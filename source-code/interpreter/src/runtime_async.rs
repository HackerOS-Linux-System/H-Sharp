use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, Condvar};
use std::sync::atomic::{AtomicU64, Ordering};

static TASK_ID: AtomicU64 = AtomicU64::new(1);

/// A unique task ID
pub type TaskId = u64;

/// State of a task's future
#[derive(Debug, Clone)]
pub enum Poll<T> {
    Ready(T),
    Pending,
}

/// A task in the async runtime
pub struct Task {
    pub id:       TaskId,
    pub name:     String,       // fn name for debug
    pub kind:     TaskKind,
    pub result:   Option<crate::Value>,
}

/// What kind of async work this task is doing
pub enum TaskKind {
    /// Pure compute — runs synchronously, already done
    Compute(crate::Value),
    /// I/O-bound — running in a background thread
    Io {
        handle: std::thread::JoinHandle<crate::Value>,
    },
    /// Awaiting another task
    Awaiting(TaskId),
    /// HTTP request (non-blocking)
    Http { url: String, method: String, body: Option<String> },
    /// Shell command (non-blocking)
    Shell(String),
}

/// The async reactor — manages all live tasks.
///
/// BUG FIX (real event loop): `block_on`/`run_all` used to be a plain
/// busy/spin loop — `block_on` slept a fixed 1ms and re-polled *every*
/// live task regardless of whether any of them had actually changed
/// state, and `run_all` didn't even sleep, spinning at 100% CPU on one
/// core for as long as any task stayed pending. Neither reacted to
/// completion; they *guessed* how often to check. `wake` fixes that:
/// every background I/O thread (`spawn_io`) notifies it the instant it
/// finishes, and `block_on`/`run_all` block on it (with a short timeout
/// as a safety net for task kinds that don't yet know to notify) instead
/// of guessing — a real, condvar-driven readiness signal instead of
/// polling on a timer.
pub struct Reactor {
    pub tasks:   HashMap<TaskId, Task>,
    pub queue:   VecDeque<TaskId>,
    wake:        Arc<(Mutex<()>, Condvar)>,
}

impl Reactor {
    pub fn new() -> Self {
        Self { tasks: HashMap::new(), queue: VecDeque::new(), wake: Arc::new((Mutex::new(()), Condvar::new())) }
    }

    /// Spawn a new compute task (already-resolved value)
    pub fn spawn_ready(&mut self, name: &str, val: crate::Value) -> TaskId {
        let id = TASK_ID.fetch_add(1, Ordering::SeqCst);
        self.tasks.insert(id, Task {
            id, name: name.to_string(),
            kind: TaskKind::Compute(val.clone()),
            result: Some(val),
        });
        id
    }

    /// Spawn an I/O task — runs a closure in a background thread. The
    /// thread notifies `self.wake` the moment `f` returns, so
    /// `block_on`/`run_all` wake immediately instead of discovering
    /// completion on their next timer tick — see `Reactor`'s doc comment.
    pub fn spawn_io<F>(&mut self, name: &str, f: F) -> TaskId
    where F: FnOnce() -> crate::Value + Send + 'static {
        let id = TASK_ID.fetch_add(1, Ordering::SeqCst);
        let wake = self.wake.clone();
        let handle = std::thread::spawn(move || {
            let v = f();
            let (lock, cvar) = &*wake;
            // The lock only ever guards this notification, never any
            // shared data — `_guard`'s sole purpose is the standard
            // "lock, then notify while held" pattern that guarantees a
            // waiter blocked in `wait_timeout` can't miss this wakeup.
            let _guard = lock.lock().unwrap();
            cvar.notify_all();
            v
        });
        self.tasks.insert(id, Task {
            id, name: name.to_string(),
            kind: TaskKind::Io { handle },
            result: None,
        });
        self.queue.push_back(id);
        id
    }

    /// Spawn HTTP GET as non-blocking I/O task
    pub fn spawn_http_get(&mut self, url: String) -> TaskId {
        self.spawn_io("http_get", move || {
            let out = std::process::Command::new("curl")
                .args(["-s", "-L", "--max-time", "30", "-A", "H#/0.6", &url])
                .output();
            crate::Value::Str(match out {
                Ok(o) => String::from_utf8_lossy(&o.stdout).to_string(),
                Err(e) => format!("http error: {}", e),
            })
        })
    }

    /// Spawn shell command as non-blocking I/O task
    pub fn spawn_shell(&mut self, cmd: String) -> TaskId {
        self.spawn_io("shell", move || {
            let out = std::process::Command::new("sh")
                .args(["-c", &cmd])
                .output();
            crate::Value::Str(match out {
                Ok(o) => String::from_utf8_lossy(&o.stdout).trim_end().to_string(),
                Err(e) => format!("shell error: {}", e),
            })
        })
    }

    /// Poll a task — returns Ready(value) or Pending
    pub fn poll(&mut self, id: TaskId) -> Poll<crate::Value> {
        let task = match self.tasks.get_mut(&id) {
            Some(t) => t,
            None    => return Poll::Ready(crate::Value::Nil),
        };

        // Already resolved?
        if let Some(v) = &task.result {
            return Poll::Ready(v.clone());
        }

        match &task.kind {
            TaskKind::Compute(v) => {
                let v = v.clone();
                task.result = Some(v.clone());
                Poll::Ready(v)
            }
            TaskKind::Io { .. } => {
                // Check if the thread is done (try_join)
                // We use is_finished() (stable since 1.61)
                if let TaskKind::Io { handle } = &task.kind {
                    if handle.is_finished() {
                        // Move out the handle and join
                        if let TaskKind::Io { handle } = std::mem::replace(
                            &mut task.kind,
                            TaskKind::Compute(crate::Value::Nil)
                        ) {
                            let val = handle.join().unwrap_or(crate::Value::Nil);
                            task.result = Some(val.clone());
                            return Poll::Ready(val);
                        }
                    }
                }
                Poll::Pending
            }
            _ => Poll::Pending,
        }
    }

    /// Block until a task is ready — runs the event loop.
    ///
    /// Waits on `self.wake` (real notification from whichever background
    /// thread finishes) instead of the previous unconditional 1ms
    /// spin-sleep. The `wait_timeout` cap is a safety net, not the normal
    /// wakeup path: a `Compute` task resolves synchronously and never
    /// reaches this loop at all, so today every task kind that *can* be
    /// `Pending` here (`Io`) does notify — the timeout only matters if a
    /// future task kind is added without wiring it into `wake`.
    pub fn block_on(&mut self, id: TaskId) -> crate::Value {
        loop {
            match self.poll(id) {
                Poll::Ready(v) => return v,
                Poll::Pending  => {
                    let (lock, cvar) = &*self.wake;
                    let guard = lock.lock().unwrap();
                    let _ = cvar.wait_timeout(guard, std::time::Duration::from_millis(5));
                }
            }
        }
    }

    /// Run all queued tasks to completion.
    ///
    /// Same fix as `block_on`: previously this had *no* wait at all
    /// between sweeps of the queue — a task that stayed `Pending` for any
    /// length of time meant `run_all` spun at 100% CPU on one core the
    /// entire time. Now it waits on `self.wake` once per full sweep that
    /// found at least one still-pending task, instead of immediately
    /// looping back to re-poll everything.
    pub fn run_all(&mut self) {
        while !self.queue.is_empty() {
            let mut any_pending = false;
            for _ in 0..self.queue.len() {
                let id = match self.queue.pop_front() { Some(id) => id, None => break };
                match self.poll(id) {
                    Poll::Ready(_) => {}
                    Poll::Pending  => { self.queue.push_back(id); any_pending = true; }
                }
            }
            if any_pending {
                let (lock, cvar) = &*self.wake;
                let guard = lock.lock().unwrap();
                let _ = cvar.wait_timeout(guard, std::time::Duration::from_millis(5));
            }
        }
    }
}
