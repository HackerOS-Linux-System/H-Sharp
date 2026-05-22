use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
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

/// The async reactor — manages all live tasks
pub struct Reactor {
    pub tasks:   HashMap<TaskId, Task>,
    pub queue:   VecDeque<TaskId>,
}

impl Reactor {
    pub fn new() -> Self {
        Self { tasks: HashMap::new(), queue: VecDeque::new() }
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

    /// Spawn an I/O task — runs a closure in a background thread
    pub fn spawn_io<F>(&mut self, name: &str, f: F) -> TaskId
    where F: FnOnce() -> crate::Value + Send + 'static {
        let id = TASK_ID.fetch_add(1, Ordering::SeqCst);
        let handle = std::thread::spawn(f);
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

    /// Block until a task is ready — runs the event loop
    pub fn block_on(&mut self, id: TaskId) -> crate::Value {
        loop {
            match self.poll(id) {
                Poll::Ready(v) => return v,
                Poll::Pending  => {
                    // Yield — process other queued tasks
                    std::thread::yield_now();
                    std::thread::sleep(std::time::Duration::from_millis(1));
                }
            }
        }
    }

    /// Run all queued tasks to completion
    pub fn run_all(&mut self) {
        while let Some(id) = self.queue.pop_front() {
            match self.poll(id) {
                Poll::Ready(_) => {}
                Poll::Pending  => self.queue.push_back(id),
            }
        }
    }
}
