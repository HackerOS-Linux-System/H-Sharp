use hsharp_parser::ast::*;
use crate::runtime_async;
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Bytes(Vec<u8>),
    Nil,
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Struct { name: String, fields: HashMap<String, Value> },
    Fn { name: String, params: Vec<Param>, body: Vec<Stmt>, env: Env, is_async: bool },
    Return(Box<Value>),
    Break,
    Continue,
    /// Async task — result of calling an async fn
    /// Contains the resolved value (computed eagerly in v0.4)
    /// Real coroutine scheduling in v0.5
    AsyncTask(Box<AsyncTaskState>),
}

/// State of an async task
#[derive(Debug, Clone)]
pub enum AsyncTaskState {
    Ready(Value),
    Pending { fn_name: String, args: Vec<Value> },
}

/// Inline monomorphization for generic functions at interpreter call sites
pub fn mono_fn_inline(f: &hsharp_parser::ast::FnDef, subst: &std::collections::HashMap<String, hsharp_parser::ast::TypeExpr>) -> hsharp_parser::ast::FnDef {
    if subst.is_empty() { return f.clone(); }
    hsharp_parser::ast::FnDef {
        attrs:       f.attrs.clone(),
        type_params: vec![],  // monomorphized
        name:        {
            let mut parts: Vec<String> = subst.values().map(|t| match t {
                hsharp_parser::ast::TypeExpr::Named(n) => n.clone(),
                _ => "t".to_string(),
            }).collect();
            parts.sort();
            format!("{}__{}", f.name, parts.join("__"))
        },
        params:      f.params.iter().map(|p| hsharp_parser::ast::Param {
            name: p.name.clone(),
            ty: subst_type_inline(&p.ty, subst),
            mutable: p.mutable,
            span: p.span.clone(),
        }).collect(),
        return_type: f.return_type.as_ref().map(|t| subst_type_inline(t, subst)),
        body:        f.body.clone(),
        pub_: f.pub_, is_async: f.is_async, is_unsafe: f.is_unsafe, mem_mode: f.mem_mode, span: f.span.clone(),
    }
}

fn subst_type_inline(ty: &hsharp_parser::ast::TypeExpr, subst: &std::collections::HashMap<String, hsharp_parser::ast::TypeExpr>) -> hsharp_parser::ast::TypeExpr {
    match ty {
        hsharp_parser::ast::TypeExpr::Named(n) => subst.get(n).cloned().unwrap_or(ty.clone()),
        other => other.clone(),
    }
}


impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n)    => write!(f, "{}", n),
            Value::Float(n)  => write!(f, "{}", n),
            Value::Bool(b)   => write!(f, "{}", b),
            Value::Str(s)    => write!(f, "{}", s),
            Value::Nil       => write!(f, "nil"),
            Value::AsyncTask(t) => match t.as_ref() {
                AsyncTaskState::Ready(v) => write!(f, "{}", v),
                AsyncTaskState::Pending { fn_name, .. } => write!(f, "<async:{}>", fn_name),
            },
            Value::Array(a)  => write!(f, "[{}]", a.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")),
            Value::Tuple(t)  => write!(f, "({})", t.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(", ")),
            Value::Bytes(b)  => write!(f, "<bytes len={}>", b.len()),
            Value::Struct { name, fields } => {
                let fs: Vec<String> = fields.iter().map(|(k, v)| format!("{}: {}", k, v)).collect();
                write!(f, "{} {{ {} }}", name, fs.join(", "))
            }
            Value::Fn { name, .. } => write!(f, "<fn {}>", name),
            Value::Return(v) => write!(f, "{}", v),
            Value::Break    => write!(f, "<break>"),
            Value::Continue => write!(f, "<continue>"),
        }
    }
}

impl Value {
    pub fn to_int(&self) -> i64 {
        match self {
            Value::Int(n)   => *n,
            Value::Float(n) => *n as i64,
            Value::Bool(b)  => if *b { 1 } else { 0 },
            Value::Str(s)   => s.parse::<i64>().unwrap_or(0),
            _               => 0,
        }
    }
    pub fn to_float(&self) -> f64 {
        match self {
            Value::Int(n)   => *n as f64,
            Value::Float(n) => *n,
            Value::Str(s)   => s.parse::<f64>().unwrap_or(0.0),
            _               => 0.0,
        }
    }
    pub fn to_str_val(&self) -> String {
        match self {
            Value::Str(s)   => s.clone(),
            Value::Int(n)   => n.to_string(),
            Value::Float(n) => n.to_string(),
            Value::Bool(b)  => b.to_string(),
            Value::Nil      => String::new(),
            _               => self.to_string(),
        }
    }
}

impl Value {
    pub fn is_truthy(&self) -> bool {
        if let Value::AsyncTask(t) = self {
            if let AsyncTaskState::Ready(v) = t.as_ref() { return v.is_truthy(); }
        }
        match self {
            Value::Bool(b) => *b,
            Value::Nil => false,
            Value::Int(n) => *n != 0,
            _ => true,
        }
    }
}

/// A single variable binding. Held behind `Arc<Mutex<..>>` (see
/// `Slot` alias below) so that closures can capture the *binding
/// itself* rather than a snapshot of its value at capture time —
/// this is what makes mutable capture work: a closure and its
/// defining scope share the same `Arc`, so a write through either
/// side is visible to the other.
///
/// `Arc<Mutex<..>>` rather than the cheaper `Rc<RefCell<..>>` is
/// deliberate: `runtime_async::Reactor::spawn_io` runs real
/// `std::thread::spawn` background threads for I/O tasks (`http`,
/// `shell`, ...), which requires `Value` — and therefore `Env`, and
/// therefore this slot type — to be `Send`. `Rc`/`RefCell` are not
/// `Send`; `Arc`/`Mutex` are (as long as the contents are `Send`,
/// which `Value` is once this is the only shared-mutability
/// primitive it uses). The lock is uncontended in the vast majority
/// of cases (H# has no shared-memory threads exposed to user code
/// today — only the internal I/O task threads, which don't touch
/// closure captures), so this doesn't meaningfully change performance.
#[derive(Debug)]
pub struct Binding {
    pub value: Value,
    pub mutable: bool,
}

/// Shared, interior-mutable variable slot.
pub type Slot = Arc<Mutex<Binding>>;

#[derive(Debug, Clone)]
pub struct Env {
    pub scopes: Vec<HashMap<String, Slot>>,
}

impl Env {
    pub fn new() -> Self {
        Self { scopes: vec![HashMap::new()] }
    }

    pub fn push(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn pop(&mut self) {
        self.scopes.pop();
    }

    /// Introduce a brand-new binding (shadowing any binding of the
    /// same name in an outer scope). This always allocates a fresh
    /// `Slot`, so it deliberately does *not* alias an outer variable
    /// of the same name — that's the correct shadowing behavior for
    /// `let x = ...` inside a nested block.
    pub fn define(&mut self, name: &str, val: Value, mutable: bool) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), Arc::new(Mutex::new(Binding { value: val, mutable })));
        }
    }

    pub fn get(&self, name: &str) -> Option<Value> {
        self.get_slot(name).map(|slot| slot.lock().unwrap().value.clone())
    }

    /// Look up the raw `Slot` (shared cell) for a variable, without
    /// cloning its value. Used by closure capture so the closure
    /// shares the exact same storage as the defining scope.
    pub fn get_slot(&self, name: &str) -> Option<Slot> {
        for scope in self.scopes.iter().rev() {
            if let Some(slot) = scope.get(name) {
                return Some(Arc::clone(slot));
            }
        }
        None
    }

    /// Return all variables visible in the current scope (for profiler/introspection)
    pub fn all_vars(&self) -> Vec<(String, Value)> {
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        for scope in self.scopes.iter().rev() {
            for (k, slot) in scope {
                if seen.insert(k.clone()) {
                    result.push((k.clone(), slot.lock().unwrap().value.clone()));
                }
            }
        }
        result
    }

    pub fn set(&mut self, name: &str, val: Value) -> bool {
        for scope in self.scopes.iter().rev() {
            if let Some(slot) = scope.get(name) {
                let mut binding = slot.lock().unwrap();
                if binding.mutable {
                    binding.value = val;
                    return true;
                } else {
                    return false; // immutable
                }
            }
        }
        false
    }

    /// Flatten all scopes into one for closure capture.
    ///
    /// This shares the underlying `Slot`s (via `Arc::clone`) rather
    /// than copying values, so a closure created here and the scope
    /// it was created in point at the *same* storage: writes made
    /// through `set()` from inside the closure are visible to the
    /// enclosing scope afterwards, and vice versa. This is what makes
    /// mutable capture work — previously this cloned `Value`s
    /// directly, which silently produced read-only snapshots.
    pub fn flatten_for_capture(&self) -> Self {
        let mut flat: HashMap<String, Slot> = HashMap::new();
        for scope in self.scopes.iter() {
            for (k, slot) in scope { flat.insert(k.clone(), Arc::clone(slot)); }
        }
        Self { scopes: vec![flat] }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum RuntimeError {
    #[error("undefined variable `{0}`")]
    UndefinedVar(String),
    #[error("type error: {0}")]
    TypeError(String),
    #[error("division by zero")]
    DivisionByZero,
    #[error("index out of bounds: index {0}, len {1}")]
    IndexOutOfBounds(i64, usize),
    #[error("cannot assign to immutable variable `{0}`")]
    ImmutableAssign(String),
    #[error("panic: {0}")]
    Panic(String),
    #[error("undefined function `{0}`")]
    UndefinedFn(String),
    #[error("undefined field `{0}`")]
    UndefinedField(String),
    /// The H# program called `exit(code)`. This is a **controlled**
    /// termination request, not a failure — it's routed through the
    /// normal `Result` error channel instead of calling
    /// `std::process::exit` directly from deep inside `call_fn` for one
    /// specific, load-bearing reason: `std::process::exit` compiles to an
    /// **uncatchable WASM trap** (`unreachable`) on `wasm32-unknown-unknown`,
    /// not a normal process exit and not even a catchable Rust panic —
    /// `std::panic::catch_unwind` cannot intercept it. A H# program using
    /// the completely ordinary `if bad is exit(1) end` idiom (see e.g.
    /// `unpack.h#`'s own argument validation) would otherwise crash the
    /// WASM playground with an uncaught JS exception instead of
    /// terminating cleanly. Every caller of `run_module`/`exec_block` gets
    /// this back through the same `Result` path as any other error and
    /// decides for itself what "the program asked to exit" should mean —
    /// the native CLI (`hsharp preview`/`run`) calls the real
    /// `std::process::exit` at its own top level (a safe place: nothing
    /// is unwinding through wasm there), while the playground crate
    /// treats `Exit(0)` as a normal, successful completion and `Exit(n)`
    /// (n != 0) as "the program exited with a non-zero status" — neither
    /// is a panic or a bug.
    #[error("exit({0})")]
    Exit(i32),
    /// Any error that doesn't fit an existing variant — used for module /
    /// stdlib resolution failures (see `helpers::std_lib_missing_message`)
    /// and for the `__builtin_*` dispatch bridge's "not implemented in
    /// this runtime yet" message (`call.rs`). Kept as a single catch-all
    /// `String` variant instead of one new variant per failure mode, since
    /// none of these need to be pattern-matched on by callers (unlike
    /// `Exit`, which the native CLI's own top level specifically intercepts
    /// to call `std::process::exit`) — they only ever need to be displayed.
    #[error("{0}")]
    Custom(String),
}

pub struct Interpreter {
    /// Real async task reactor (v0.6 cooperative runtime)
    pub reactor: runtime_async::Reactor,
    pub env: Env,
    pub fns: HashMap<String, FnDef>,
    /// `impl Type is fn method(...) ... end` methods, keyed as
    /// `"TypeName_methodName"` (matches the typechecker's naming
    /// convention so both stay in sync).
    pub methods: HashMap<String, FnDef>,
    pub structs: HashMap<String, StructDef>,
    /// Enum definitions, keyed by enum type name — needed so `Type::Variant`
    /// (bare or called with args) can be recognized as a variant
    /// construction rather than falling through to the stdlib alias /
    /// builtin lookup in `call_path`, and so match arms can validate
    /// variant names.
    pub enums: HashMap<String, EnumDef>,
    pub stdout: String, // capture output
    pub captured_output: bool,
    /// Names of `@safety`/`@arena` functions we've already printed the
    /// interpreter-vs-LLVM-backend parity note for (see call_fn) — so a
    /// function called many times (e.g. in a loop or recursively) only
    /// gets the note once instead of flooding stderr.
    pub mem_mode_notes_given: std::collections::HashSet<String>,
    /// Statements executed so far, incremented once per `exec_stmt` call —
    /// i.e. once per loop iteration, once per function call's body entry,
    /// etc. Exists so an *embedder* (the WASM playground; conceivably a
    /// future `hsharp run --max-steps N` too) can bound runaway execution
    /// deterministically, in terms the interpreter itself understands,
    /// rather than only via a wall-clock timeout from the outside.
    ///
    /// Why this matters beyond "just use a JS `setTimeout`"/Worker
    /// deadline: a wall-clock-only timeout can't preempt *inside* a single
    /// synchronous `run_module()` call — if one `exec_stmt` (e.g. building
    /// a huge array literal, or a single non-looping allocation) takes
    /// long enough on its own, nothing outside gets a chance to intervene
    /// until it returns. A step limit checked *between* statements bounds
    /// the amount of interpreter work that can happen without a check,
    /// independent of how long any single statement takes to execute.
    /// It's a complement to an outer timeout, not a replacement for one —
    /// see `source-code/playground/src/lib.rs`'s `run_with_limits`.
    pub step_count: u64,
    /// `None` = unlimited (the CLI's `preview`/`run` never sets this).
    /// `Some(n)` = `exec_stmt` returns `RuntimeError::Panic("step limit
    /// exceeded")` once `step_count` would exceed `n`.
    pub step_limit: Option<u64>,
    /// Open TCP client connections, keyed by an opaque handle returned
    /// to H# code from `tcp_connect` (see `std/tcp.h#`/`std/net_tcp.h#`).
    /// A real `std::net::TcpStream` needs to stay alive *across* separate
    /// `call_fn` invocations (`connect`, then `send`, then `recv`, then
    /// `close`, each a distinct call from H# code) — unlike every other
    /// resource this interpreter deals with (files, sqlite "handles"),
    /// which are cheap to just reopen by path on every call. A live
    /// socket can't be reopened-by-address the same way without losing
    /// the connection's actual state, so it has to be kept somewhere
    /// that outlives one `call_fn` call: here.
    pub tcp_streams: HashMap<i64, std::net::TcpStream>,
    pub next_tcp_handle: i64,
    /// Named atomics for `std/sync.h#` — see that file's module doc
    /// comment for why these are real-but-uncontended in this
    /// single-native-thread interpreter.
    pub atomics: HashMap<String, i64>,
}
