pub mod runtime_async;
use hsharp_parser::ast::*;
use std::collections::HashMap;
use std::fmt;
use serde_json::Value as Json;
use sha2::{Sha256, Sha512, Digest as Sha2Digest};
use sha1::Sha1;
use md5::Md5;
use hmac::{Hmac, Mac};

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
fn mono_fn_inline(f: &hsharp_parser::ast::FnDef, subst: &std::collections::HashMap<String, hsharp_parser::ast::TypeExpr>) -> hsharp_parser::ast::FnDef {
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
        pub_: f.pub_, is_async: f.is_async, is_unsafe: f.is_unsafe, span: f.span.clone(),
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
    fn is_truthy(&self) -> bool {
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

#[derive(Debug, Clone)]
pub struct Env {
    scopes: Vec<HashMap<String, (Value, bool)>>, // (value, mutable)
}

impl Env {
    pub fn new() -> Self {
        Self { scopes: vec![HashMap::new()] }
    }

    fn push(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, name: &str, val: Value, mutable: bool) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), (val, mutable));
        }
    }

    fn get(&self, name: &str) -> Option<&Value> {
        for scope in self.scopes.iter().rev() {
            if let Some((v, _)) = scope.get(name) {
                return Some(v);
            }
        }
        None
    }

    /// Return all variables visible in the current scope (for profiler/introspection)
    pub fn all_vars(&self) -> Vec<(String, Value)> {
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        for scope in self.scopes.iter().rev() {
            for (k, (v, _)) in scope {
                if seen.insert(k.clone()) {
                    result.push((k.clone(), v.clone()));
                }
            }
        }
        result
    }

    fn set(&mut self, name: &str, val: Value) -> bool {
        for scope in self.scopes.iter_mut().rev() {
            if let Some((v, m)) = scope.get_mut(name) {
                if *m {
                    *v = val;
                    return true;
                } else {
                    return false; // immutable
                }
            }
        }
        false
    }

    /// Flatten all scopes into one for closure capture.
    pub fn flatten_for_capture(&self) -> Self {
        let mut flat = std::collections::HashMap::new();
        for scope in self.scopes.iter() {
            for (k, v) in scope { flat.insert(k.clone(), v.clone()); }
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
}

pub struct Interpreter {
    /// Real async task reactor (v0.6 cooperative runtime)
    pub reactor: runtime_async::Reactor,
    env: Env,
    fns: HashMap<String, FnDef>,
    /// `impl Type is fn method(...) ... end` methods, keyed as
    /// `"TypeName_methodName"` (matches the typechecker's naming
    /// convention so both stay in sync).
    methods: HashMap<String, FnDef>,
    structs: HashMap<String, StructDef>,
    /// Enum definitions, keyed by enum type name — needed so `Type::Variant`
    /// (bare or called with args) can be recognized as a variant
    /// construction rather than falling through to the stdlib alias /
    /// builtin lookup in `call_path`, and so match arms can validate
    /// variant names.
    enums: HashMap<String, EnumDef>,
    stdout: String, // capture output
    pub captured_output: bool,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Env::new(),
            fns: HashMap::new(),
            methods: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            stdout: String::new(),
            captured_output: false,
            reactor: runtime_async::Reactor::new(),
        }
    }

    pub fn run_module(&mut self, module: &Module) -> Result<(), RuntimeError> {
        self.run_module_register_only(module)?;

        // Call main
        if let Some(main_fn) = self.fns.get("main").cloned() {
            let stmts = main_fn.body.clone();
            self.env.push();
            self.exec_block(&stmts)?;
            self.env.pop();
        }

        Ok(())
    }

    /// Register every top-level item (functions, structs, enums, inline
    /// modules, impl blocks) without invoking `main`. Used by `run_module`
    /// internally, and exposed publicly so callers that want to invoke a
    /// *specific* function directly — e.g. a test runner calling individual
    /// `#[test]` functions one at a time — can register the module once and
    /// then drive execution themselves via whatever entry point they want.
    pub fn run_module_register_only(&mut self, module: &Module) -> Result<(), RuntimeError> {
        // Register top-level items
        for item in &module.items {
            match item {
                Item::FnDef(f) => { self.fns.insert(f.name.clone(), f.clone()); }
                Item::StructDef(s) => { self.structs.insert(s.name.clone(), s.clone()); }
                Item::EnumDef(e) => { self.enums.insert(e.name.clone(), e.clone()); }
                Item::ModDecl { name, inline: Some(items), .. } => {
                    self.register_mod_items(name, items);
                }
                Item::ImplBlock(imp) => {
                    self.register_impl_methods(&imp.type_name, &imp.methods);
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Directly invoke a top-level function by name with no arguments —
    /// the shape every `#[test] fn name() is ... end` function has. Returns
    /// the RuntimeError (e.g. a failed `assert_eq`) on failure so callers
    /// can report it, rather than propagating a process exit.
    pub fn call_test_fn(&mut self, name: &str) -> Result<Value, RuntimeError> {
        self.call_fn(name, Vec::new())
    }

    fn exec_block(&mut self, stmts: &[Stmt]) -> Result<Option<Value>, RuntimeError> {
        let len = stmts.len();
        for (i, stmt) in stmts.iter().enumerate() {
            // Implicit return: last expression in block yields its value
            if i == len - 1 {
                if let Stmt::Expr(expr, _) = stmt {
                    match expr {
                        // Control-flow exprs are executed normally
                        Expr::If { .. } | Expr::While { .. } | Expr::For { .. } |
                        Expr::Assign(..) | Expr::CompoundAssign(..) | Expr::Unsafe(..) => {
                            if let Some(v) = self.exec_stmt(stmt)? {
                                return Ok(Some(v));
                            }
                        }
                        // All other exprs: evaluate and return their value
                        _ => {
                            let v = self.eval_expr(expr)?;
                            return Ok(Some(v));
                        }
                    }
                    continue;
                }
            }
            if let Some(v) = self.exec_stmt(stmt)? {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    fn exec_stmt(&mut self, stmt: &Stmt) -> Result<Option<Value>, RuntimeError> {
        match stmt {
            Stmt::Let { name, mutable, value, .. } => {
                let val = if let Some(expr) = value {
                    self.eval_expr(expr)?
                } else {
                    Value::Nil
                };
                // The `?` operator (Expr::Try) signals an early return by
                // producing a Value::Return(Nil) sentinel instead of an
                // ordinary value. If we're binding the result of an
                // expression containing a top-level `?` that short-
                // circuited, propagate the early return immediately rather
                // than binding the sentinel itself to `name` and continuing
                // — that would silently corrupt `name`'s value and let
                // execution carry on past where it should have stopped.
                if matches!(val, Value::Return(_)) {
                    return Ok(Some(val));
                }
                self.env.define(name, val, *mutable);
                Ok(None)
            }
            Stmt::Return(expr, _) => {
                let val = if let Some(e) = expr {
                    self.eval_expr(e)?
                } else {
                    Value::Nil
                };
                Ok(Some(Value::Return(Box::new(val))))
            }
            Stmt::Break(_, _) => Ok(Some(Value::Break)),
            Stmt::Continue(_) => Ok(Some(Value::Continue)),
            Stmt::Expr(expr, _) => {
                match expr {
                    Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                        let cond_val = self.eval_expr(condition)?;
                        if cond_val.is_truthy() {
                            self.env.push();
                            let r = self.exec_block(then_body)?;
                            self.env.pop();
                            return Ok(r);
                        }
                        for (ec, eb) in elsif_branches {
                            let cv = self.eval_expr(ec)?;
                            if cv.is_truthy() {
                                self.env.push();
                                let r = self.exec_block(eb)?;
                                self.env.pop();
                                return Ok(r);
                            }
                        }
                        if let Some(else_b) = else_body {
                            self.env.push();
                            let r = self.exec_block(else_b)?;
                            self.env.pop();
                            return Ok(r);
                        }
                        Ok(None)
                    }
                    Expr::While { condition, body, .. } => {
                        loop {
                            let cond = self.eval_expr(condition)?;
                            if !cond.is_truthy() { break; }
                            self.env.push();
                            let r = self.exec_block(body)?;
                            self.env.pop();
                            match r {
                                Some(Value::Break) => break,
                                Some(Value::Continue) => continue,
                                Some(v @ Value::Return(_)) => return Ok(Some(v)),
                                _ => {}
                            }
                        }
                        Ok(None)
                    }
                    Expr::For { pattern, iterable, body, .. } => {
                        let iter_val = self.eval_expr(iterable)?;
                        let items = match &iter_val {
                            Value::Array(arr) => arr.clone(),
                            Value::Str(s) => s.chars().map(|c| Value::Str(c.to_string())).collect(),
                            _ => return Err(RuntimeError::TypeError(format!("cannot iterate over {}", iter_val))),
                        };
                        for item in items {
                            self.env.push();
                            if let Pattern::Ident(name, _) = pattern {
                                self.env.define(name, item, false);
                            }
                            let r = self.exec_block(body)?;
                            self.env.pop();
                            match r {
                                Some(Value::Break) => break,
                                Some(Value::Continue) => continue,
                                Some(v @ Value::Return(_)) => return Ok(Some(v)),
                                _ => {}
                            }
                        }
                        Ok(None)
                    }
                    Expr::Assign(lhs, rhs, _) => {
                        let val = self.eval_expr(rhs)?;
                        self.assign_lhs(lhs, val)?;
                        Ok(None)
                    }
                    Expr::CompoundAssign(lhs, op, rhs, _) => {
                        let rval = self.eval_expr(rhs)?;
                        let lval = self.eval_expr(lhs)?;
                        let result = self.eval_binop(lval, op, rval)?;
                        self.assign_lhs(lhs, result)?;
                        Ok(None)
                    }
                    Expr::Unsafe(body, arena_cfg, _) => {
                        use hsharp_parser::ast::{UnsafeMode, ArenaKind, ManualKind};
                        // Describe arena type in scope (for debug/tooling)
                        let arena_name = match arena_cfg.as_ref().map(|c| &c.mode) {
                            Some(UnsafeMode::Arena { kind, size: _ }) => {
                                let k = match kind {
                                    ArenaKind::General => "general",
                                    ArenaKind::Fixed   => "fixed",
                                    ArenaKind::Pool    => "pool",
                                    ArenaKind::Page    => "page",
                                    ArenaKind::Ring    => "ring",
                                };
                                format!("arena({})", k)
                            }
                            Some(UnsafeMode::Manual(ManualKind::Modern))  => "manual".to_string(),
                            Some(UnsafeMode::Manual(ManualKind::Classic)) => "manual(classic)".to_string(),
                            Some(UnsafeMode::Raw) | None                  => "raw".to_string(),
                        };
                        self.env.push();
                        // Expose __arena_kind in scope for introspection
                        self.env.define(&format!("__unsafe_{}", arena_name), Value::Str(arena_name.clone()), false);
                        let r = self.exec_block(body)?;
                        self.env.pop();
                        // Only propagate explicit returns, not block values
                        // (otherwise outer block exits early after arena block)
                        match r {
                            Some(Value::Return(_)) => Ok(r),
                            _ => Ok(None),
                        }
                    }
                    _ => {
                        self.eval_expr(expr)?;
                        Ok(None)
                    }
                }
            }
            Stmt::Item(Item::FnDef(f)) => {
                self.fns.insert(f.name.clone(), f.clone());
                Ok(None)
            }
            Stmt::Item(Item::ModDecl { name, inline: Some(items), .. }) => {
                self.register_mod_items(name, items);
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    #[allow(unreachable_patterns)]
fn eval_expr(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match expr {
            // String interpolation: evaluate ALL parts (text + expressions)
            Expr::Literal(Literal::Interpolated(parts), _) => {
                let mut result = String::new();
                for part in parts {
                    match part {
                        hsharp_parser::ast::InterpPart::Text(t) => result.push_str(t),
                        hsharp_parser::ast::InterpPart::Expr(e) => {
                            let v = self.eval_expr(e)?;
                            result.push_str(&v.to_string());
                        }
                    }
                }
                return Ok(Value::Str(result));
            }
            Expr::Literal(lit, _) => Ok(match lit {
                Literal::Int(n) => Value::Int(*n),
                Literal::Float(f) => Value::Float(*f),
                Literal::String(s) => Value::Str(s.clone()),
                Literal::Bool(b) => Value::Bool(*b),
                Literal::Nil => Value::Nil,
                Literal::Interpolated(parts) => {
                    let mut r = String::new();
                    for p in parts {
                        match p {
                            hsharp_parser::ast::InterpPart::Text(t) => r.push_str(t),
                            hsharp_parser::ast::InterpPart::Expr(_) => {},
                        }
                    }
                    Value::Str(r)
                }
                Literal::Bytes(b) => Value::Bytes(b.clone()),
            }),
            Expr::Ident(name, _) => {
                if let Some(v) = self.env.get(name).cloned() {
                    Ok(v)
                } else if self.fns.contains_key(name) {
                    let f = self.fns[name].clone();
                    Ok(Value::Fn {
                        name: name.clone(),
                        params: f.params.clone(),
                        body: f.body.clone(),
                        env: self.env.clone(),
                        is_async: f.is_async,
                    })
                } else {
                    Err(RuntimeError::UndefinedVar(name.clone()))
                }
            }
            Expr::BinOp(lhs, op, rhs, _) => {
                let l = self.eval_expr(lhs)?;
                let r = self.eval_expr(rhs)?;
                self.eval_binop(l, op, r)
            }
            Expr::UnOp(op, inner, _) => {
                let v = self.eval_expr(inner)?;
                match op {
                    UnOp::Neg => match v {
                        Value::Int(n) => Ok(Value::Int(-n)),
                        Value::Float(f) => Ok(Value::Float(-f)),
                        _ => Err(RuntimeError::TypeError("cannot negate".into())),
                    },
                    UnOp::Not => Ok(Value::Bool(!v.is_truthy())),
                    _ => Ok(v),
                }
            }
            Expr::Call(callee, args, _) => {
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a))
                    .collect::<Result<_, _>>()?;

                if let Expr::Ident(name, _) = callee.as_ref() {
                    return self.call_fn(name, arg_vals);
                }

                // module::function(...) call — e.g. json::parse(x), math::sqrt(x)
                if let Expr::Path(segments, _) = callee.as_ref() {
                    let result = self.call_path(segments, arg_vals)?;
                    // sort::sort_ints / sort::sort_strings document an
                    // in-place mutation API (`sort::sort_ints(arr)` sorts
                    // `arr` itself, not a copy) — the builtin returns the
                    // sorted array, and we write it back to the first
                    // argument's binding if it's a plain named variable,
                    // mirroring the MethodCall write-back mechanism used
                    // for collection mutation elsewhere.
                    let full = segments.join("::");
                    if matches!(full.as_str(), "sort::sort_ints" | "sort::sort_strings") {
                        if let Some(Expr::Ident(name, _)) = args.first() {
                            self.env.set(name, result.clone());
                        }
                    }
                    return Ok(result);
                }

                let callee_val = self.eval_expr(callee)?;
                match callee_val {
                    Value::Fn { params, body, env, .. } => {
                        self.invoke_fn_value(&params, &body, env, arg_vals)
                    }
                    _ => Err(RuntimeError::TypeError("not callable".into())),
                }
            }
            // Bare module path used as a value — e.g. passing `math::PI` around,
            // or a path that wasn't immediately called. We best-effort resolve
            // it as a zero-arg call; otherwise return Nil.
            Expr::Path(segments, _) => {
                self.call_path(segments, Vec::new())
            }
            Expr::MethodCall(obj, method, args, _) => {
                let obj_val = self.eval_expr(obj)?;
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a))
                    .collect::<Result<_, _>>()?;

                let var_name = if let Expr::Ident(n, _) = obj.as_ref() { Some(n.clone()) } else { None };

                // Case 1: receiver is a struct with a user-defined `impl`
                // method. Run it with `self` bound, then — if the receiver
                // is a plain named variable — write the (possibly mutated)
                // `self` back so field assignments like `self.x = 5` made
                // inside the method are visible to the caller.
                if matches!(obj_val, Value::Struct { .. }) {
                    if let Some(result) = self.try_user_method(&obj_val, method, &arg_vals) {
                        let (ret, mutated_self) = result?;
                        if let Some(name) = &var_name {
                            self.env.set(name, mutated_self);
                        }
                        return Ok(ret);
                    }
                }

                // Case 2: builtin mutating methods (push/pop/insert/remove)
                // on a plain named variable — compute the new container
                // value and write it back into the environment, since this
                // interpreter passes Value by clone rather than by shared
                // reference.
                if let Some(name) = &var_name {
                    if let Some(new_val) = compute_mutated_container(&obj_val, method, &arg_vals) {
                        self.env.set(name, new_val);
                    }
                }
                self.call_method(obj_val, method, arg_vals)
            }
            Expr::FieldAccess(obj, field, _) => {
                let v = self.eval_expr(obj)?;
                match v {
                    Value::Struct { fields, .. } => {
                        fields.get(field).cloned()
                            .ok_or_else(|| RuntimeError::UndefinedField(field.clone()))
                    }
                    Value::Tuple(items) => {
                        // Tuple field access: t.0, t.1, ... — `field` is the
                        // numeric index as a string (see the parser's
                        // numeric-field special case for the Dot operator).
                        field.parse::<usize>().ok()
                            .and_then(|idx| items.get(idx).cloned())
                            .ok_or_else(|| RuntimeError::UndefinedField(field.clone()))
                    }
                    _ => Err(RuntimeError::TypeError(format!("no field `{}` on {}", field, v))),
                }
            }
            Expr::IndexAccess(arr, idx, _) => {
                let a = self.eval_expr(arr)?;
                // Detect a literal Range subexpression directly, so we can
                // slice without materializing the full index array (which
                // is what a bare `Expr::Range` evaluates to — see below).
                if let Expr::Range(start_e, end_e, inclusive, _) = idx.as_ref() {
                    let start_v = self.eval_expr(start_e)?;
                    let end_v   = self.eval_expr(end_e)?;
                    if let (Value::Int(s), Value::Int(e)) = (start_v, end_v) {
                        let s = s.max(0) as usize;
                        let e_excl = if *inclusive { (e + 1).max(0) as usize } else { e.max(0) as usize };
                        return match a {
                            Value::Array(items) => {
                                let e_clamped = e_excl.min(items.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Array(items[s_clamped..e_clamped].to_vec()))
                            }
                            Value::Str(s_val) => {
                                let chars: Vec<char> = s_val.chars().collect();
                                let e_clamped = e_excl.min(chars.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Str(chars[s_clamped..e_clamped].iter().collect()))
                            }
                            Value::Bytes(b) => {
                                let e_clamped = e_excl.min(b.len());
                                let s_clamped = s.min(e_clamped);
                                Ok(Value::Bytes(b[s_clamped..e_clamped].to_vec()))
                            }
                            _ => Err(RuntimeError::TypeError("cannot slice this type".into())),
                        };
                    }
                }
                let i = self.eval_expr(idx)?;
                match (a, i) {
                    (Value::Array(arr), Value::Int(i)) => {
                        let idx = i as usize;
                        arr.get(idx).cloned()
                            .ok_or(RuntimeError::IndexOutOfBounds(i, arr.len()))
                    }
                    (Value::Str(s), Value::Int(i)) => {
                        s.chars().nth(i as usize)
                            .map(|c| Value::Str(c.to_string()))
                            .ok_or(RuntimeError::IndexOutOfBounds(i, s.len()))
                    }
                    (Value::Bytes(b), Value::Int(i)) => {
                        b.get(i as usize).copied()
                            .map(|byte| Value::Int(byte as i64))
                            .ok_or(RuntimeError::IndexOutOfBounds(i, b.len()))
                    }
                    // Index with an already-materialized Range array (e.g.
                    // produced by a `let r = 0..3; arr[r]` indirection) —
                    // treat a contiguous ascending int array as a slice.
                    (Value::Array(items), Value::Array(range_idx)) if !range_idx.is_empty() => {
                        if let (Some(Value::Int(first)), Some(Value::Int(last))) =
                            (range_idx.first(), range_idx.last())
                        {
                            let s = (*first).max(0) as usize;
                            let e_excl = ((*last) + 1).max(0) as usize;
                            let e_clamped = e_excl.min(items.len());
                            let s_clamped = s.min(e_clamped);
                            Ok(Value::Array(items[s_clamped..e_clamped].to_vec()))
                        } else {
                            Err(RuntimeError::TypeError("invalid slice index".into()))
                        }
                    }
                    (Value::Str(s_val), Value::Array(range_idx)) if !range_idx.is_empty() => {
                        if let (Some(Value::Int(first)), Some(Value::Int(last))) =
                            (range_idx.first(), range_idx.last())
                        {
                            let chars: Vec<char> = s_val.chars().collect();
                            let s = (*first).max(0) as usize;
                            let e_excl = ((*last) + 1).max(0) as usize;
                            let e_clamped = e_excl.min(chars.len());
                            let s_clamped = s.min(e_clamped);
                            Ok(Value::Str(chars[s_clamped..e_clamped].iter().collect()))
                        } else {
                            Err(RuntimeError::TypeError("invalid slice index".into()))
                        }
                    }
                    _ => Err(RuntimeError::TypeError("cannot index".into())),
                }
            }
            Expr::ArrayLit(elems, _) => {
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.eval_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Array(vals))
            }
            Expr::TupleLit(elems, _) => {
                let vals: Vec<Value> = elems.iter()
                    .map(|e| self.eval_expr(e))
                    .collect::<Result<_, _>>()?;
                Ok(Value::Tuple(vals))
            }
            Expr::StructLit(name, fields, _) => {
                let mut field_map = HashMap::new();
                for (fname, fexpr) in fields {
                    field_map.insert(fname.clone(), self.eval_expr(fexpr)?);
                }
                Ok(Value::Struct { name: name.clone(), fields: field_map })
            }
            Expr::Cast(inner, ty, _) => {
                let v = self.eval_expr(inner)?;
                match (v, ty) {
                    (Value::Int(n), TypeExpr::Named(t)) if t == "f64" || t == "f32" => Ok(Value::Float(n as f64)),
                    (Value::Float(f), TypeExpr::Named(t)) if t == "int" || t.starts_with('i') => Ok(Value::Int(f as i64)),
                    (Value::Int(n), TypeExpr::Named(t)) if t.starts_with('i') || t.starts_with('u') => Ok(Value::Int(n)),
                    (v, _) => Ok(v),
                }
            }
            Expr::Range(start, end, inclusive, _) => {
                let s = self.eval_expr(start)?;
                let e = self.eval_expr(end)?;
                match (s, e) {
                    (Value::Int(s), Value::Int(e)) => {
                        let end = if *inclusive { e + 1 } else { e };
                        Ok(Value::Array((s..end).map(Value::Int).collect()))
                    }
                    _ => Err(RuntimeError::TypeError("range requires integers".into())),
                }
            }
            Expr::Return(val, _) => {
                let v = if let Some(e) = val { self.eval_expr(e)? } else { Value::Nil };
                Ok(Value::Return(Box::new(v)))
            }
            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                let cond = self.eval_expr(condition)?;
                if cond.is_truthy() {
                    self.env.push();
                    let r = self.exec_block(then_body)?;
                    self.env.pop();
                    return Ok(r.unwrap_or(Value::Nil));
                }
                for (ec, eb) in elsif_branches {
                    let cv = self.eval_expr(ec)?;
                    if cv.is_truthy() {
                        self.env.push();
                        let r = self.exec_block(eb)?;
                        self.env.pop();
                        return Ok(r.unwrap_or(Value::Nil));
                    }
                }
                if let Some(else_b) = else_body {
                    self.env.push();
                    let r = self.exec_block(else_b)?;
                    self.env.pop();
                    return Ok(r.unwrap_or(Value::Nil));
                }
                Ok(Value::Nil)
            }
            Expr::Match { subject, arms, .. } => {
                let subj = self.eval_expr(subject)?;
                for arm in arms {
                    if self.pattern_matches(&arm.pattern, &subj) {
                        self.env.push();
                        self.bind_pattern(&arm.pattern, subj.clone());
                        // NOTE: previously this special-cased a
                        // single-statement arm by calling self.eval_expr()
                        // directly on its body, as a shortcut to get the
                        // arm's value without the Option<Value> wrapping
                        // exec_block produces. That shortcut was wrong for
                        // any arm whose single statement was an assignment
                        // (`pattern => var = value`) or compound assignment,
                        // since eval_expr has no case for Expr::Assign /
                        // Expr::CompoundAssign at all — those are only
                        // handled inside exec_block's Stmt::Expr dispatch.
                        // Going through exec_block unconditionally fixes
                        // this; for the common "last expression is the
                        // arm's value" case, exec_block's own implicit-
                        // return handling (see its Stmt::Expr branch)
                        // already does the right thing.
                        let result = self.exec_block(&arm.body)?;
                        self.env.pop();
                        return Ok(result.unwrap_or(Value::Nil));
                    }
                }
                Ok(Value::Nil)
            }
            Expr::SelfExpr(_) => {
                self.env.get("self").cloned()
                    .ok_or_else(|| RuntimeError::UndefinedVar("self".into()))
            }
            Expr::Unsafe(body, _arena_cfg, _) => {
                self.env.push();
                let r = self.exec_block(body)?;
                self.env.pop();
                Ok(match r {
                    Some(Value::Return(v)) => *v,
                    Some(v) => v,
                    None => Value::Nil,
                })
            }
            // await expr — resolve AsyncTask
            Expr::Await(inner, _) => {
                let task_val = self.eval_expr(inner)?;
                match task_val {
                    Value::AsyncTask(t) => match *t {
                        AsyncTaskState::Ready(v) => Ok(v),
                        AsyncTaskState::Pending { fn_name, ref args } => {
                            // v0.6: check if it's an I/O task registered in reactor
                            // otherwise execute synchronously
                            self.call_fn(&fn_name, args.clone())
                        }
                    },
                    other => Ok(other),
                }
            }
                        // Closure with environment capture
            Expr::Closure { params, body, .. } => {
                // Capture lexical scope — flatten all scopes so captured vars
                // are always accessible regardless of scope nesting
                Ok(Value::Fn {
                    name:     "<closure>".to_string(),
                    params:   params.clone(),
                    body:     body.clone(),
                    env:      self.env.flatten_for_capture(),
                    is_async: false,
                })
            }
            // ? (Try) operator — propagate Nil as early return
            Expr::Try(inner, _) => {
                let v = self.eval_expr(inner)?;
                match &v {
                    Value::Nil => {
                        // Early return with Nil from the enclosing function
                        return Ok(Value::Return(Box::new(Value::Nil)));
                    }
                    _ => Ok(v),
                }
            }

            _ => Ok(Value::Nil),
        }
    }

    /// Register an inline module's functions both under their namespaced
    /// key (`mod_name::fn_name`, used by `mod_name::fn_name(...)` call
    /// sites) and under their bare name (used by other functions *inside*
    /// the same module calling each other directly, e.g. `gcd` calling
    /// `gcd` recursively without the `math_utils::` prefix). Nested `mod`
    /// blocks are flattened recursively with dotted-path namespacing.
    fn register_mod_items(&mut self, mod_name: &str, items: &[Item]) {
        for item in items {
            match item {
                Item::FnDef(f) => {
                    let namespaced = format!("{}::{}", mod_name, f.name);
                    self.fns.insert(namespaced, f.clone());
                    // Also register under the bare name so sibling
                    // functions in the same module can call each other
                    // without the module prefix. If a bare name collision
                    // already exists (e.g. two modules both define
                    // `helper`), the most recently registered module wins —
                    // acceptable for v0.8; cross-module name collisions
                    // should use the qualified form anyway.
                    self.fns.insert(f.name.clone(), f.clone());
                }
                Item::StructDef(s) => {
                    self.structs.insert(s.name.clone(), s.clone());
                }
                Item::ModDecl { name: sub_name, inline: Some(sub_items), .. } => {
                    let nested = format!("{}::{}", mod_name, sub_name);
                    self.register_mod_items(&nested, sub_items);
                }
                _ => {}
            }
        }
    }

    /// Resolve and call a `module::function`-style path. Tries, in order:
    /// 1. A user-defined fn registered under the exact "module::function" name
    ///    (e.g. an inline `mod` was namespace-flattened to this key).
    /// 2. An explicit alias table mapping common stdlib paths to the actual
    ///    builtin symbol implemented in `call_fn` (since `call_fn` silently
    ///    returns `Nil` for unknown names rather than erroring, guessing via
    ///    a snake_case heuristic alone would mask typos as no-ops).
    /// 3. The snake_case convention (`module::fn` -> `module_fn`) as a
    ///    best-effort guess for builtins not yet in the alias table.
    /// 4. A user-defined fn registered under just the last segment
    ///    (covers `use "std -> x" from "x"` aliasing where only the
    ///    unqualified name was ever defined locally), or the bare last
    ///    segment as a final builtin-name attempt.
    fn call_path(&mut self, segments: &[String], args: Vec<Value>) -> Result<Value, RuntimeError> {
        // Enum variant construction: `Type::Variant` or `Type::Variant(args)`.
        // Checked first and unconditionally whenever segments[0] names a
        // known enum — this can never collide with anything else
        // meaningful, since an enum type name and a stdlib module alias
        // occupy different namespaces by construction (you can't `use` an
        // enum the way you `use "std -> x"`).
        if segments.len() == 2 {
            if let Some(edef) = self.enums.get(&segments[0]).cloned() {
                if edef.variants.iter().any(|v| v.name == segments[1]) {
                    return Ok(self.make_enum_value(&segments[0], &segments[1], args));
                }
            }
        }
        let full = segments.join("::");
        if self.fns.contains_key(&full) {
            return self.call_fn(&full, args);
        }
        // Static method call on a type with no instance, e.g. `Point::new(...)`
        // or `HashMap::new()` — these are registered in `self.methods` under
        // `TypeName_method` by `register_impl_methods`, separately from
        // `self.fns`, so they need their own lookup here. Only applies to
        // genuine 2-segment `Type::method` paths (not deeper module paths).
        if segments.len() == 2 {
            let method_key = format!("{}_{}", segments[0], segments[1]);
            if let Some(f) = self.methods.get(&method_key).cloned() {
                return self.call_static_method(&f, args);
            }
        }
        if let Some(alias) = resolve_stdlib_alias(&full) {
            return self.call_fn(alias, args);
        }
        let snake = segments.join("_");
        if self.fns.contains_key(&snake) {
            return self.call_fn(&snake, args);
        }
        if let Some(last) = segments.last() {
            if self.fns.contains_key(last) {
                return self.call_fn(last, args);
            }
            // Best-effort: try the snake_case guess, then the bare last
            // segment, in case either happens to be a real builtin name
            // not yet listed in the alias table.
            if builtin_exists(&snake) {
                return self.call_fn(&snake, args);
            }
            return self.call_fn(last, args);
        }
        Err(RuntimeError::UndefinedFn(full))
    }

    /// Run a static `impl` method (one whose first parameter isn't `self`,
    /// e.g. `Point::new(x, y)`) — no receiver to bind, just ordinary
    /// positional parameter binding.
    fn call_static_method(&mut self, f: &FnDef, args: Vec<Value>) -> Result<Value, RuntimeError> {
        self.env.push();
        for (param, val) in f.params.iter().zip(args) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(&f.body)?;
        self.env.pop();
        Ok(match result {
            Some(Value::Return(v)) => *v,
            Some(v) => v,
            None => Value::Nil,
        })
    }

    /// Construct an enum variant value as a `Value::Struct` whose `name` is
    /// the fully-qualified `"Type::Variant"` string and whose `fields` hold
    /// any tuple-variant payload under numeric string keys (`"0"`, `"1"`,
    /// ...), mirroring how plain tuples already expose `.0`/`.1` access.
    /// This reuses the existing Struct representation rather than adding a
    /// new `Value` variant, so all the generic struct machinery (field
    /// access, equality via field comparison, etc.) works for free. Unit
    /// variants (`Color::Red`) simply get empty `fields`.
    fn make_enum_value(&self, enum_name: &str, variant_name: &str, args: Vec<Value>) -> Value {
        let mut fields = HashMap::new();
        for (i, v) in args.into_iter().enumerate() {
            fields.insert(i.to_string(), v);
        }
        Value::Struct { name: format!("{}::{}", enum_name, variant_name), fields }
    }

    /// Register an `impl Type is ... end` block's methods so `value.method(...)`
    /// dispatch (in `call_method`) can find and execute real H#-defined
    /// method bodies instead of only the built-in Rust method table.
    fn register_impl_methods(&mut self, type_name: &str, methods: &[FnDef]) {
        for m in methods {
            let key = format!("{}_{}", type_name, m.name);
            self.methods.insert(key, m.clone());
        }
    }

    /// Try to find and run a user-defined `impl` method for a struct value.
    /// Returns `None` if no matching method was registered (caller should
    /// fall back to the builtin method table in that case). On success,
    /// returns `(return_value, mutated_self)` — `mutated_self` reflects any
    /// changes the method body made to `self`'s fields (e.g. `self.x = 5`),
    /// which the caller should write back to the receiver's binding since
    /// this interpreter passes `Value` by clone rather than by reference.
    fn try_user_method(&mut self, obj: &Value, method: &str, args: &[Value]) -> Option<Result<(Value, Value), RuntimeError>> {
        let type_name = match obj {
            Value::Struct { name, .. } => name.clone(),
            _ => return None,
        };
        let key = format!("{}_{}", type_name, method);
        let f = self.methods.get(&key)?.clone();

        self.env.push();
        // Bind `self` to the receiver (always mutable inside the method,
        // so `self.field = val` works regardless of how the impl declared
        // its `self` parameter).
        self.env.define("self", obj.clone(), true);
        for (param, val) in f.params.iter().filter(|p| p.name != "self").zip(args.iter().cloned()) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(&f.body);
        let mutated_self = self.env.get("self").cloned().unwrap_or_else(|| obj.clone());
        self.env.pop();

        Some(result.map(|r| {
            let ret = match r {
                Some(Value::Return(v)) => *v,
                Some(v) => v,
                None => Value::Nil,
            };
            (ret, mutated_self)
        }))
    }

    /// Invoke an already-materialized `Value::Fn` (e.g. a closure passed as
    /// an argument to a builtin like `iter::map`) with the given positional
    /// arguments. This is the same call mechanism `Expr::Call` uses when its
    /// callee evaluates to a closure value, factored out so Rust-side
    /// builtins (iter_map, iter_filter, sort_by, etc.) can invoke H#
    /// closures passed to them.
    fn invoke_fn_value(&mut self, params: &[Param], body: &[Stmt], env: Env, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let saved = self.env.clone();
        self.env = env;
        self.env.push();
        for (param, val) in params.iter().zip(args) {
            self.env.define(&param.name, val, param.mutable);
        }
        let result = self.exec_block(body);
        self.env.pop();
        self.env = saved;
        result.map(|r| match r {
            Some(Value::Return(v)) => *v,
            Some(v) => v,
            None => Value::Nil,
        })
    }

    fn call_fn(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {

                    // Check if name is a closure/fn stored in environment (e.g. let triple = |n| n*3)
        if let Some(val) = self.env.get(name).cloned() {
            match val {
                Value::Fn { params, body, env: captured_env, is_async, .. } => {
                    let saved = self.env.clone();
                    self.env = captured_env;
                    self.env.push();
                    for (param, val) in params.iter().zip(args.iter()) {
                        self.env.define(&param.name, val.clone(), param.mutable);
                    }
                    let result = self.exec_block(&body)?;
                    self.env.pop();
                    self.env = saved;
                    let resolved = match result {
                        Some(Value::Return(v)) => *v,
                        Some(v) => v,
                        None => Value::Nil,
                    };
                    if is_async {
                        return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(resolved))));
                    }
                    return Ok(resolved);
                }
                _ => {}
            }
        }

        // Builtins
        match name {
            // ── Regex (v0.6) ─────────────────────────────────────────────────
            "re_match" | "regex_match" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                // Use grep as portable regex engine
                use std::io::Write;
                let mut grep_m = std::process::Command::new("grep")
                    .args(["-qP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .spawn().unwrap_or_else(|_| panic!("grep not found"));
                if let Some(stdin) = grep_m.stdin.as_mut() {
                    let _ = stdin.write_all(text.as_bytes());
                }
                let ok = grep_m.wait().map(|s| s.success()).unwrap_or(false);
                return Ok(Value::Bool(ok));
            }
            "re_find" | "regex_find" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                let mut gf = std::process::Command::new("grep")
                    .args(["-oP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn().unwrap_or_else(|_| { eprintln!("grep not found"); std::process::exit(1); });
                if let Some(s) = gf.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let gfo = gf.wait_with_output().unwrap_or_else(|_| std::process::Command::new("true").output().unwrap());
                return Ok(Value::Str(String::from_utf8_lossy(&gfo.stdout).trim().to_string()));
            }
            "re_find_all" | "regex_find_all" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                let mut gfa = std::process::Command::new("grep")
                    .args(["-oP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn().unwrap_or_else(|_| { eprintln!("grep not found"); std::process::exit(1); });
                if let Some(s) = gfa.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let gfao = gfa.wait_with_output().unwrap_or_else(|_| std::process::Command::new("true").output().unwrap());
                let results: Vec<Value> = String::from_utf8_lossy(&gfao.stdout)
                    .lines().filter(|l| !l.is_empty())
                    .map(|l| Value::Str(l.to_string())).collect();
                return Ok(Value::Array(results));
            }
            "re_replace" | "regex_replace" => {
                let pattern = args.first().map(|v| v.to_string()).unwrap_or_default();
                let repl    = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let text    = args.get(2).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                let sed_script = format!("s|{}|{}|g", pattern, repl);
                let mut sed_c = std::process::Command::new("sed")
                    .args(["-E", &sed_script])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn().unwrap_or_else(|_| { eprintln!("sed not found"); std::process::exit(1); });
                if let Some(s) = sed_c.stdin.as_mut() { let _ = s.write_all(text.as_bytes()); }
                let sed_out = sed_c.wait_with_output().unwrap_or_else(|_| std::process::Command::new("true").output().unwrap());
                let out = Ok::<_, std::io::Error>(sed_out);
                return Ok(Value::Str(match out {
                    Ok(o) => String::from_utf8_lossy(&o.stdout).trim_end().to_string(),
                    Err(_) => text.to_string(),
                }));
            }
            // ── (text, pattern) argument-order wrappers ───────────────────────
            // std/regex.h#'s documented H# API takes the subject text first
            // (`is_match(s, pattern)`, `find(s, pattern)`, etc.), matching
            // common scripting-language convention — but the underlying
            // grep/sed-based builtins above were written expecting
            // (pattern, text)/(pattern, repl, text). These wrappers just
            // swap argument order before delegating, so `re::is_match(text,
            // pattern)` from H# code resolves correctly via the alias table.
            "re_match_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_match", vec![pat, text]);
            }
            "re_find_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_find", vec![pat, text]);
            }
            "re_find_all_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_find_all", vec![pat, text]);
            }
            "re_replace_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                let repl = args.get(2).cloned().unwrap_or(Value::Nil);
                return self.call_fn("re_replace", vec![pat, repl, text]);
            }
            "re_replace_all_ta" => {
                let text = args.first().cloned().unwrap_or(Value::Nil);
                let pat  = args.get(1).cloned().unwrap_or(Value::Nil);
                let repl = args.get(2).cloned().unwrap_or(Value::Nil);
                // "replace all" and "replace" are the same operation here
                // since the sed `g` flag already replaces every match.
                return self.call_fn("re_replace", vec![pat, repl, text]);
            }
            "re_split_ta" => {
                let text    = args.first().map(|v| v.to_string()).unwrap_or_default();
                let pattern = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut p = std::process::Command::new("grep")
                    .args(["-ozP", &pattern])
                    .stdin(std::process::Stdio::piped())
                    .stdout(std::process::Stdio::piped())
                    .spawn();
                // Simplest portable approach: use Rust's own splitting once
                // we have a way to test the pattern per-position is complex
                // without a real regex engine, so fall back to a basic
                // whitespace-pattern-aware split for the common `\s+` case
                // and a literal split otherwise.
                let _ = &mut p;
                if pattern == r"\s+" || pattern == r"\s*" {
                    let parts: Vec<Value> = text.split_whitespace().map(|s| Value::Str(s.to_string())).collect();
                    return Ok(Value::Array(parts));
                }
                // Literal-substring split fallback for simple patterns.
                let parts: Vec<Value> = text.split(pattern.as_str()).map(|s| Value::Str(s.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            // ── SQLite (v0.6) ─────────────────────────────────────────────────
            "sqlite_open" | "db_open" => {
                let path = args.first().map(|v| v.to_string()).unwrap_or_else(|| "./db.sqlite".to_string());
                // Return the path as a db handle (string-based for portability)
                return Ok(Value::Str(format!("sqlite://{}", path)));
            }
            "sqlite_exec" | "db_exec" => {
                let db   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sql  = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let path = db.strip_prefix("sqlite://").unwrap_or(&db);
                let out  = std::process::Command::new("sqlite3")
                    .arg(path).arg(&sql)
                    .output();
                return Ok(match out {
                    Ok(o) if o.status.success() => Value::Str(String::from_utf8_lossy(&o.stdout).to_string()),
                    Ok(o) => Value::Str(format!("db error: {}", String::from_utf8_lossy(&o.stderr))),
                    Err(e) => Value::Str(format!("sqlite3 not found: {}", e)),
                });
            }
            "sqlite_query" | "db_query" => {
                let db   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sql  = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let path = db.strip_prefix("sqlite://").unwrap_or(&db);
                let out  = std::process::Command::new("sqlite3")
                    .args(["-separator", ",", path, &sql])
                    .output();
                let rows: Vec<Value> = match out {
                    Ok(o) => String::from_utf8_lossy(&o.stdout)
                        .lines()
                        .filter(|l| !l.is_empty())
                        .map(|l| {
                            let cols: Vec<Value> = l.split(',')
                                .map(|c| Value::Str(c.trim().to_string()))
                                .collect();
                            Value::Array(cols)
                        })
                        .collect(),
                    Err(_) => vec![],
                };
                return Ok(Value::Array(rows));
            }
            "sqlite_close" | "db_close" => {
                return Ok(Value::Nil); // SQLite files don't need explicit close
            }
            // ── Profiler (v0.6) ───────────────────────────────────────────────
            "prof_start" | "profile_start" => {
                let label = args.first().map(|v| v.to_string()).unwrap_or_else(|| "default".to_string());
                // Store start time in a global map (use env for now)
                let start_ns = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos() as i64)
                    .unwrap_or(0);
                self.env.define(&format!("__prof_{}", label), Value::Int(start_ns), true);
                return Ok(Value::Int(start_ns));
            }
            "prof_end" | "profile_end" => {
                let label = args.first().map(|v| v.to_string()).unwrap_or_else(|| "default".to_string());
                let end_ns = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos() as i64)
                    .unwrap_or(0);
                let start_ns = self.env.get(&format!("__prof_{}", label))
                    .and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None })
                    .unwrap_or(end_ns);
                let elapsed_ms = (end_ns - start_ns) / 1_000_000;
                let msg = format!("[prof] {} = {}ms", label, elapsed_ms);
                return Ok(Value::Str(msg));
            }
            "prof_report" => {
                // Print all profiler entries
                let report: Vec<String> = self.env.all_vars()
                    .iter()
                    .filter(|(k, _)| k.starts_with("__prof_"))
                    .map(|(k, v)| format!("  {}: started at {:?}", k.trim_start_matches("__prof_"), v.to_string()))
                    .collect();
                return Ok(Value::Str(format!("[profiler report]
{}", report.join("
"))));
            }
            // ── Large project tooling ─────────────────────────────────────────
            "module_info" => {
                return Ok(Value::Str(format!("module: {} functions registered", self.fns.len())));
            }
            "heap_size" | "memory_usage" => {
                // Read /proc/self/status for VmRSS
                let mem = std::fs::read_to_string("/proc/self/status").ok()
                    .and_then(|s| s.lines()
                        .find(|l| l.starts_with("VmRSS:"))
                        .map(|l| l.split_whitespace().nth(1).unwrap_or("0").parse::<i64>().unwrap_or(0)))
                    .unwrap_or(0);
                return Ok(Value::Int(mem));
            }
            "print" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                if self.captured_output {
                    self.stdout.push_str(&s);
                } else {
                    print!("{}", s);
                }
                return Ok(Value::Nil);
            }
            // H# 0.1: write() is the primary output function
            "write" | "writeln" | "println" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                if self.captured_output {
                    self.stdout.push_str(&s);
                    self.stdout.push('\n');
                } else {
                    println!("{}", s);
                }
                return Ok(Value::Nil);
            }
            "panic" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Err(RuntimeError::Panic(s));
            }
            "exit" => {
                let code = match args.first() {
                    Some(Value::Int(n)) => *n as i32,
                    _ => 0,
                };
                std::process::exit(code);
            }
            "len" => {
                return Ok(match args.first() {
                    Some(Value::Array(a)) => Value::Int(a.len() as i64),
                    Some(Value::Str(s)) => Value::Int(s.len() as i64),
                    Some(Value::Bytes(b)) => Value::Int(b.len() as i64),
                    _ => Value::Int(0),
                });
            }
            "assert" => {
                let cond = args.first().map(|v| v.is_truthy()).unwrap_or(false);
                if !cond {
                    let msg = args.get(1).map(|v| v.to_string()).unwrap_or_else(|| "assertion failed".into());
                    return Err(RuntimeError::Panic(msg));
                }
                return Ok(Value::Nil);
            }
            "to_string" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default()));
            }
            "parse_int" => {
                let s = match args.first() {
                    Some(Value::Str(s)) => s.clone(),
                    _ => return Ok(Value::Nil),
                };
                return Ok(s.parse::<i64>().map(Value::Int).unwrap_or(Value::Nil));
            }
            // ── v0.3 Real stdlib — no stubs ────────────────────────────
            "trim" | "str_trim" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().trim().to_string()));
            }
            "to_upper" | "upper" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().to_uppercase()));
            }
            "to_lower" | "lower" => {
                return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default().to_lowercase()));
            }
            "contains" | "str_contains" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.contains(p.as_str())));
            }
            "starts_with" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.starts_with(p.as_str())));
            }
            "ends_with" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let p = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(s.ends_with(p.as_str())));
            }
            "replace" | "str_replace" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                let f = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let t = args.get(2).map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(s.replace(f.as_str(), t.as_str())));
            }
            "split" | "str_split" => {
                let s   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts = s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect();
                return Ok(Value::Array(parts));
            }
            "str_join" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts: Vec<String> = arr.iter().map(|v| v.to_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "conv_str_to_int" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Int(s.trim().parse::<i64>().unwrap_or(0)));
            }
            "conv_int_to_hex" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Str(format!("{:x}", n)));
            }
            "conv_to_bytes" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bytes(s.into_bytes()));
            }
            "now_unix" | "time_unix" => {
                use std::time::{SystemTime, UNIX_EPOCH};
                let secs = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs() as i64).unwrap_or(0);
                return Ok(Value::Int(secs));
            }
            "now_ms" | "time_ms" => {
                use std::time::{SystemTime, UNIX_EPOCH};
                let ms = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as i64).unwrap_or(0);
                return Ok(Value::Int(ms));
            }
            "sleep_ms" => {
                let ms = args.first().map(|v| v.to_int()).unwrap_or(0) as u64;
                std::thread::sleep(std::time::Duration::from_millis(ms));
                return Ok(Value::Nil);
            }
            "shell" | "cmd" => {
                let cmd = args.first().map(|v| v.to_string()).unwrap_or_default();
                let out = std::process::Command::new("sh").arg("-c").arg(cmd.as_str()).output();
                return Ok(match out {
                    Ok(o) => Value::Str(String::from_utf8_lossy(&o.stdout).trim_end().to_string()),
                    Err(e) => Value::Str(format!("shell error: {}", e)),
                });
            }
            "getpid" | "pid" => { return Ok(Value::Int(std::process::id() as i64)); }
            "random_hex" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(8).max(0) as usize;
                let mut bytes = vec![0u8; n];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut bytes);
                }
                return Ok(Value::Str(bytes.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hex_encode" => {
                let s = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(s.as_bytes().iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hex_decode" => {
                let h = args.first().map(|v| v.to_string()).unwrap_or_default();
                let bytes: Vec<u8> = (0..h.len()).step_by(2)
                    .filter_map(|i| h.get(i..i+2).and_then(|b| u8::from_str_radix(b, 16).ok()))
                    .collect();
                return Ok(Value::Str(String::from_utf8_lossy(&bytes).to_string()));
            }
            "random_int" => {
                let min = args.first().map(|v| v.to_int()).unwrap_or(0);
                let max = args.get(1).map(|v| v.to_int()).unwrap_or(100);
                let mut buf = [0u8; 8];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut buf);
                }
                let r = (i64::from_le_bytes(buf).unsigned_abs() as i64).abs();
                return Ok(Value::Int(if max > min { min + r % (max - min) } else { min }));
            }
            "random_string" => {
                let n = args.first().map(|v| v.to_int()).unwrap_or(8).max(0) as usize;
                let cs = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
                let mut bytes = vec![0u8; n];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
                    use std::io::Read; let _ = f.read_exact(&mut bytes);
                }
                return Ok(Value::Str(bytes.iter().map(|&b| cs[b as usize % cs.len()] as char).collect()));
            }
            "hostname" => {
                let h = std::fs::read_to_string("/etc/hostname").map(|s| s.trim().to_string()).unwrap_or_else(|_| "unknown".into());
                return Ok(Value::Str(h));
            }
            // ── Math (v0.8) ──────────────────────────────────────────────────
            "math_sin"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).sin())),
            "math_cos"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).cos())),
            "math_tan"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).tan())),
            "math_asin"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).asin())),
            "math_acos"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).acos())),
            "math_atan"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).atan())),
            "math_atan2" => {
                let y = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let x = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(y.atan2(x)));
            }
            "math_sqrt"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).sqrt())),
            "math_pow"   => {
                let base = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let exp  = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(base.powf(exp)));
            }
            "math_floor" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).floor())),
            "math_ceil"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).ceil())),
            "math_round" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).round())),
            "math_trunc" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).trunc())),
            "math_log"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).ln())),
            "math_log2"  => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).log2())),
            "math_log10" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).log10())),
            "math_exp"   => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).exp())),
            "math_abs" => {
                let v = args.first().cloned().unwrap_or(Value::Int(0));
                return Ok(match v {
                    Value::Int(n)   => Value::Int(n.abs()),
                    Value::Float(f) => Value::Float(f.abs()),
                    _ => v,
                });
            }
            "math_fabs" => return Ok(Value::Float(args.first().map(|v| v.to_float()).unwrap_or(0.0).abs())),
            "math_ipow" => {
                let base = args.first().map(|v| v.to_int()).unwrap_or(0);
                let exp  = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as u32;
                return Ok(Value::Int(base.pow(exp)));
            }
            "math_min" => {
                let a = args.first().cloned().unwrap_or(Value::Int(0));
                let b = args.get(1).cloned().unwrap_or(Value::Int(0));
                return Ok(match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Value::Int(*x.min(y)),
                    _ => if a.to_float() < b.to_float() { a } else { b },
                });
            }
            "math_max" => {
                let a = args.first().cloned().unwrap_or(Value::Int(0));
                let b = args.get(1).cloned().unwrap_or(Value::Int(0));
                return Ok(match (&a, &b) {
                    (Value::Int(x), Value::Int(y)) => Value::Int(*x.max(y)),
                    _ => if a.to_float() > b.to_float() { a } else { b },
                });
            }
            "math_fmin" => {
                let a = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(a.min(b)));
            }
            "math_fmax" => {
                let a = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(a.max(b)));
            }
            "math_clamp" => {
                let v  = args.first().map(|v| v.to_int()).unwrap_or(0);
                let lo = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let hi = args.get(2).map(|v| v.to_int()).unwrap_or(0);
                return Ok(Value::Int(v.max(lo).min(hi)));
            }
            "math_fclamp" => {
                let v  = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let lo = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                let hi = args.get(2).map(|v| v.to_float()).unwrap_or(0.0);
                return Ok(Value::Float(v.max(lo).min(hi)));
            }
            "math_gcd" => {
                let mut a = args.first().map(|v| v.to_int()).unwrap_or(0).abs();
                let mut b = args.get(1).map(|v| v.to_int()).unwrap_or(0).abs();
                while b != 0 { let t = b; b = a % b; a = t; }
                return Ok(Value::Int(a));
            }
            "math_lcm" => {
                let a = args.first().map(|v| v.to_int()).unwrap_or(0);
                let b = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                if a == 0 || b == 0 { return Ok(Value::Int(0)); }
                let mut x = a.abs();
                let mut y = b.abs();
                while y != 0 { let t = y; y = x % y; x = t; }
                return Ok(Value::Int((a / x * b).abs()));
            }
            "math_pi"  => return Ok(Value::Float(std::f64::consts::PI)),
            "math_e"   => return Ok(Value::Float(std::f64::consts::E)),
            "math_tau" => return Ok(Value::Float(std::f64::consts::TAU)),
            // ── JSON (v0.8) ──────────────────────────────────────────────────
            "json_parse" => {
                let raw = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(match serde_json::from_str::<Json>(&raw) {
                    Ok(j)  => json_to_value(&j),
                    Err(_) => Value::Nil,
                });
            }
            "json_parse_array" => {
                let raw = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(match serde_json::from_str::<Json>(&raw) {
                    Ok(Json::Array(items)) => Value::Array(items.iter().map(json_to_value).collect()),
                    _ => Value::Array(Vec::new()),
                });
            }
            "json_stringify" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                let j = value_to_json(&v);
                return Ok(Value::Str(serde_json::to_string(&j).unwrap_or_default()));
            }
            "json_stringify_pretty" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                let j = value_to_json(&v);
                return Ok(Value::Str(serde_json::to_string_pretty(&j).unwrap_or_default()));
            }
            "json_empty_object" => {
                return Ok(Value::Struct { name: "__json".to_string(), fields: HashMap::new() });
            }
            "json_get_str" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).map(|v| Value::Str(v.to_string())).unwrap_or(Value::Str(String::new())));
                }
                return Ok(Value::Str(String::new()));
            }
            "json_get_int" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Int(fields.get(&key).map(|v| v.to_int()).unwrap_or(0)));
                }
                return Ok(Value::Int(0));
            }
            "json_get_float" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Float(fields.get(&key).map(|v| v.to_float()).unwrap_or(0.0)));
                }
                return Ok(Value::Float(0.0));
            }
            "json_get_bool" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(matches!(fields.get(&key), Some(Value::Bool(true)))));
                }
                return Ok(Value::Bool(false));
            }
            "json_get_obj" | "json_get_arr" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "json_has_key" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(fields.contains_key(&key)));
                }
                return Ok(Value::Bool(false));
            }
            "json_is_null" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(matches!(fields.get(&key), Some(Value::Nil) | None)));
                }
                return Ok(Value::Bool(true));
            }
            "json_set" => {
                // NOTE: H# values are passed by value in this interpreter
                // (no shared mutable references), so `json::set_str(obj, ...)`
                // cannot mutate the caller's `obj` binding in place the way
                // a reference-based runtime could. This builtin returns the
                // *updated* struct; H# code must re-bind it, e.g.:
                //   obj = json::set_str(obj, "key", "val")
                // The fluent `json::object([...])` constructor is the
                // recommended way to build objects instead.
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let val = args.get(2).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.insert(key, val);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "json_as_int" => return Ok(Value::Int(args.first().map(|v| v.to_int()).unwrap_or(0))),
            "json_as_str" => return Ok(Value::Str(args.first().map(|v| v.to_string()).unwrap_or_default())),
            "json_object" => {
                // Build an object from an array of (key, value) tuples, e.g.
                // json::object([("lang", "H#"), ("version", "0.6")]).
                let mut fields = HashMap::new();
                if let Some(Value::Array(pairs)) = args.first() {
                    for pair in pairs {
                        if let Value::Tuple(items) = pair {
                            if items.len() == 2 {
                                let key = items[0].to_string();
                                fields.insert(key, items[1].clone());
                            }
                        }
                    }
                }
                return Ok(Value::Struct { name: "__json".to_string(), fields });
            }
            "json_int_at" => {
                let idx = args.get(1).map(|v| v.to_int()).unwrap_or(0) as usize;
                if let Some(Value::Array(arr)) = args.first() {
                    return Ok(Value::Int(arr.get(idx).map(|v| v.to_int()).unwrap_or(0)));
                }
                return Ok(Value::Int(0));
            }
            "json_obj_at" => {
                let idx = args.get(1).map(|v| v.to_int()).unwrap_or(0) as usize;
                if let Some(Value::Array(arr)) = args.first() {
                    return Ok(arr.get(idx).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "json_query" => {
                let path = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut current = args.first().cloned().unwrap_or(Value::Nil);
                for segment in path.split('.') {
                    current = match current {
                        Value::Struct { fields, .. } => fields.get(segment).cloned().unwrap_or(Value::Nil),
                        _ => Value::Nil,
                    };
                }
                return Ok(current);
            }
            // ── HashMap (v0.8) — backed by Value::Struct{name:"__hashmap"} ────
            // Keys are encoded via Value::to_string() since the underlying
            // storage is a plain string-keyed map; this is sufficient for
            // the common case of string/int keys used throughout the stdlib.
            "hashmap_new" => return Ok(Value::Struct { name: "__hashmap".into(), fields: HashMap::new() }),
            "hashmap_insert" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let val = args.get(2).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.insert(key, val);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "hashmap_get" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get(&key).cloned().unwrap_or(Value::Nil));
                }
                return Ok(Value::Nil);
            }
            "hashmap_contains" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Bool(fields.contains_key(&key)));
                }
                return Ok(Value::Bool(false));
            }
            "hashmap_remove" => {
                let key = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if let Some(Value::Struct { name, mut fields }) = args.first().cloned() {
                    fields.remove(&key);
                    return Ok(Value::Struct { name, fields });
                }
                return Ok(Value::Nil);
            }
            "hashmap_len" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Int(fields.len() as i64));
                }
                return Ok(Value::Int(0));
            }
            "hashmap_keys" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Array(fields.keys().map(|k| Value::Str(k.clone())).collect()));
                }
                return Ok(Value::Array(Vec::new()));
            }
            "hashmap_values" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(Value::Array(fields.values().cloned().collect()));
                }
                return Ok(Value::Array(Vec::new()));
            }
            // ── HashSet (v0.8) — wraps a Value::Array of unique values ────────
            "hashset_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__hashset".into(), fields });
            }
            "hashset_insert" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, fields }) = args.first().cloned() {
                    let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                    let mut new_items = items;
                    if !new_items.iter().any(|v| values_equal(v, &val)) {
                        new_items.push(val);
                    }
                    let mut new_fields = fields;
                    new_fields.insert("items".to_string(), Value::Array(new_items));
                    return Ok(Value::Struct { name, fields: new_fields });
                }
                return Ok(Value::Nil);
            }
            "hashset_contains" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    if let Some(Value::Array(items)) = fields.get("items") {
                        return Ok(Value::Bool(items.iter().any(|v| values_equal(v, &val))));
                    }
                }
                return Ok(Value::Bool(false));
            }
            "hashset_remove" => {
                let val = args.get(1).cloned().unwrap_or(Value::Nil);
                if let Some(Value::Struct { name, fields }) = args.first().cloned() {
                    let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                    let new_items: Vec<Value> = items.into_iter().filter(|v| !values_equal(v, &val)).collect();
                    let mut new_fields = fields;
                    new_fields.insert("items".to_string(), Value::Array(new_items));
                    return Ok(Value::Struct { name, fields: new_fields });
                }
                return Ok(Value::Nil);
            }
            "hashset_len" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    if let Some(Value::Array(items)) = fields.get("items") {
                        return Ok(Value::Int(items.len() as i64));
                    }
                }
                return Ok(Value::Int(0));
            }
            "hashset_to_array" => {
                if let Some(Value::Struct { fields, .. }) = args.first() {
                    return Ok(fields.get("items").cloned().unwrap_or(Value::Array(Vec::new())));
                }
                return Ok(Value::Array(Vec::new()));
            }
            // ── Queue / Stack (v0.8) — each wraps a Value::Array under a
            // distinct struct name so call_method/compute_mutated_container
            // can give them FIFO vs LIFO pop semantics that differ from a
            // plain array's (and from each other).
            "queue_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__queue".into(), fields });
            }
            "stack_new" => {
                let mut fields = HashMap::new();
                fields.insert("items".to_string(), Value::Array(Vec::new()));
                return Ok(Value::Struct { name: "__stack".into(), fields });
            }
            "fs_read" | "read_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(std::fs::read_to_string(p.as_str()).map(Value::Str).unwrap_or(Value::Nil));
            }
            "fs_write" | "write_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let c = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::write(p.as_str(), c.as_str());
                return Ok(Value::Nil);
            }
            "fs_exists" | "file_exists" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).exists()));
            }
            "fs_mkdir_all" | "mkdir_all" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::create_dir_all(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_remove" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_file(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_append" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let c = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                use std::io::Write;
                if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(p.as_str()) {
                    let _ = f.write_all(c.as_bytes());
                }
                return Ok(Value::Nil);
            }
            "fs_is_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_dir()));
            }
            "fs_is_file" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_file()));
            }
            "fs_rmdir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_dir(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_rmdir_all" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::remove_dir_all(p.as_str());
                return Ok(Value::Nil);
            }
            "fs_read_lines" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let content = std::fs::read_to_string(p.as_str()).unwrap_or_default();
                let lines: Vec<Value> = content.lines().map(|l| Value::Str(l.to_string())).collect();
                return Ok(Value::Array(lines));
            }
            "fs_size" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sz = std::fs::metadata(p.as_str()).map(|m| m.len()).unwrap_or(0);
                return Ok(Value::Int(sz as i64));
            }
            "fs_copy" => {
                let src = args.first().map(|v| v.to_string()).unwrap_or_default();
                let dst = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::copy(src.as_str(), dst.as_str());
                return Ok(Value::Nil);
            }
            "fs_rename" => {
                let src = args.first().map(|v| v.to_string()).unwrap_or_default();
                let dst = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let _ = std::fs::rename(src.as_str(), dst.as_str());
                return Ok(Value::Nil);
            }
            "fs_cwd" => {
                let cwd = std::env::current_dir().map(|p| p.display().to_string()).unwrap_or_default();
                return Ok(Value::Str(cwd));
            }
            "fs_list_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let entries: Vec<Value> = std::fs::read_dir(p.as_str())
                    .map(|rd| rd.filter_map(|e| e.ok())
                        .map(|e| Value::Str(e.file_name().to_string_lossy().to_string()))
                        .collect())
                    .unwrap_or_default();
                return Ok(Value::Array(entries));
            }
            // ── path (v0.8) ──────────────────────────────────────────────────
            "path_join" => {
                let a = args.first().map(|v| v.to_string()).unwrap_or_default();
                let b = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let joined = std::path::Path::new(&a).join(&b);
                return Ok(Value::Str(joined.to_string_lossy().to_string()));
            }
            "path_stem" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let stem = std::path::Path::new(&p).file_stem()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(stem));
            }
            "path_extension" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let ext = std::path::Path::new(&p).extension()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(ext));
            }
            "path_parent" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                let parent = std::path::Path::new(&p).parent()
                    .map(|s| s.to_string_lossy().to_string())
                    .unwrap_or_default();
                return Ok(Value::Str(parent));
            }
            // ── env (v0.8) ───────────────────────────────────────────────────
            "env_temp_dir" => {
                return Ok(Value::Str(std::env::temp_dir().to_string_lossy().to_string()));
            }
            "env_get" => {
                let k = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(std::env::var(&k).map(Value::Str).unwrap_or(Value::Nil));
            }
            "env_args" => {
                let a: Vec<Value> = std::env::args().map(Value::Str).collect();
                return Ok(Value::Array(a));
            }
            "env_home" => {
                return Ok(std::env::var("HOME").map(Value::Str).unwrap_or(Value::Str(String::new())));
            }
            // ── iter (v0.8) — higher-order array operations that invoke
            // H# closures passed as Value::Fn arguments via invoke_fn_value.
            "iter_map" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                let mut result = Vec::with_capacity(arr.len());
                for x in arr {
                    let v = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            self.invoke_fn_value(params, body, env.clone(), vec![x])?,
                        _ => Value::Nil,
                    };
                    result.push(v);
                }
                return Ok(Value::Array(result));
            }
            "iter_filter" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                let mut result = Vec::new();
                for x in arr {
                    let keep = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            matches!(self.invoke_fn_value(params, body, env.clone(), vec![x.clone()])?, Value::Bool(true)),
                        _ => false,
                    };
                    if keep { result.push(x); }
                }
                return Ok(Value::Array(result));
            }
            "iter_reduce" => {
                let arr  = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let init = args.get(1).cloned().unwrap_or(Value::Nil);
                let f    = args.get(2).cloned();
                let mut acc = init;
                for x in arr {
                    acc = match &f {
                        Some(Value::Fn { params, body, env, .. }) =>
                            self.invoke_fn_value(params, body, env.clone(), vec![acc, x])?,
                        _ => acc,
                    };
                }
                return Ok(acc);
            }
            "iter_zip" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                let len = a.len().min(b.len());
                let zipped: Vec<Value> = (0..len).map(|i| Value::Tuple(vec![a[i].clone(), b[i].clone()])).collect();
                return Ok(Value::Array(zipped));
            }
            "iter_chain" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                a.extend(b);
                return Ok(Value::Array(a));
            }
            "iter_take" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let n = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(a.into_iter().take(n).collect()));
            }
            "iter_skip" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let n = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(a.into_iter().skip(n).collect()));
            }
            "iter_any" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                for x in arr {
                    if let Some(Value::Fn { params, body, env, .. }) = &f {
                        if matches!(self.invoke_fn_value(params, body, env.clone(), vec![x])?, Value::Bool(true)) {
                            return Ok(Value::Bool(true));
                        }
                    }
                }
                return Ok(Value::Bool(false));
            }
            "iter_all" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let f = args.get(1).cloned();
                for x in arr {
                    if let Some(Value::Fn { params, body, env, .. }) = &f {
                        if !matches!(self.invoke_fn_value(params, body, env.clone(), vec![x])?, Value::Bool(true)) {
                            return Ok(Value::Bool(false));
                        }
                    }
                }
                return Ok(Value::Bool(true));
            }
            "iter_sum" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sum: i64 = arr.iter().map(|v| v.to_int()).sum();
                return Ok(Value::Int(sum));
            }
            "iter_product" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let prod: i64 = arr.iter().map(|v| v.to_int()).product();
                return Ok(Value::Int(prod));
            }
            "iter_reverse" => {
                let mut a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                a.reverse();
                return Ok(Value::Array(a));
            }
            "iter_join" => {
                let a   = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let sep = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
                return Ok(Value::Str(parts.join(&sep)));
            }
            "iter_repeat" => {
                let val = args.first().cloned().unwrap_or(Value::Nil);
                let n   = args.get(1).map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
                return Ok(Value::Array(vec![val; n]));
            }
            "iter_unique" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let mut result: Vec<Value> = Vec::new();
                for x in arr {
                    if !result.iter().any(|v| values_equal(v, &x)) {
                        result.push(x);
                    }
                }
                return Ok(Value::Array(result));
            }
            // ── sort (v0.8) ──────────────────────────────────────────────────
            "sort_ints" => {
                let mut arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                arr.sort_by_key(|v| v.to_int());
                return Ok(Value::Array(arr));
            }
            "sort_strings" => {
                let mut arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                arr.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
                return Ok(Value::Array(arr));
            }
            "binary_search" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let target = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let mut lo: i64 = 0;
                let mut hi: i64 = arr.len() as i64 - 1;
                while lo <= hi {
                    let mid = lo + (hi - lo) / 2;
                    let mid_val = arr[mid as usize].to_int();
                    if mid_val == target { return Ok(Value::Int(mid)); }
                    if mid_val < target { lo = mid + 1; } else { hi = mid - 1; }
                }
                return Ok(Value::Int(-1));
            }
            "binary_search_left" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let target = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                let mut lo: i64 = 0;
                let mut hi: i64 = arr.len() as i64;
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    if arr[mid as usize].to_int() < target { lo = mid + 1; } else { hi = mid; }
                }
                return Ok(Value::Int(lo));
            }
            "min_int" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                return Ok(arr.iter().map(|v| v.to_int()).min().map(Value::Int).unwrap_or(Value::Nil));
            }
            "max_int" => {
                let arr = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                return Ok(arr.iter().map(|v| v.to_int()).max().map(Value::Int).unwrap_or(Value::Nil));
            }
            "merge_sorted" => {
                let a = match args.first() { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
                let b = match args.get(1) { Some(Value::Array(b)) => b.clone(), _ => Vec::new() };
                let mut result: Vec<Value> = Vec::with_capacity(a.len() + b.len());
                let (mut i, mut j) = (0usize, 0usize);
                while i < a.len() && j < b.len() {
                    if a[i].to_int() <= b[j].to_int() { result.push(a[i].clone()); i += 1; }
                    else { result.push(b[j].clone()); j += 1; }
                }
                result.extend_from_slice(&a[i..]);
                result.extend_from_slice(&b[j..]);
                return Ok(Value::Array(result));
            }
            // ── async (v0.8) — this interpreter's async model runs eagerly
            // (no real cooperative scheduling), so `async::spawn(closure)`
            // simply invokes the closure immediately and wraps its result
            // as a Ready task; `await` on it is then a transparent unwrap.
            // This matches the existing Expr::Await behavior, which already
            // passes non-AsyncTask values through unchanged.
            "async_spawn" => {
                if let Some(Value::Fn { params, body, env, .. }) = args.first().cloned() {
                    let result = self.invoke_fn_value(&params, &body, env, Vec::new())?;
                    return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(result))));
                }
                return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(Value::Nil))));
            }
            "async_timeout" => {
                // args: (timeout_ms, closure) — the timeout itself isn't
                // enforced (no real scheduler/clock-based cancellation in
                // this interpreter); the closure just runs to completion.
                if let Some(Value::Fn { params, body, env, .. }) = args.get(1).cloned() {
                    return self.invoke_fn_value(&params, &body, env, Vec::new());
                }
                return Ok(Value::Nil);
            }
            // ── test / assert (v0.8) — CRITICAL: these were entirely
            // missing before. `assert_eq` etc. fell through to call_fn's
            // catch-all `Ok(Value::Nil)`, meaning every test in the entire
            // suite "passed" unconditionally regardless of whether its
            // assertions were true — the test runner only checks the
            // process exit code, and a silently-ignored assertion never
            // produces a nonzero exit. These builtins raise a real
            // RuntimeError::Panic on failure so a failing assertion
            // actually fails the test (and fails `bytes test`'s
            // `hsharp preview` subprocess check).
            "assert_eq" => {
                let a = args.first().cloned().unwrap_or(Value::Nil);
                let b = args.get(1).cloned().unwrap_or(Value::Nil);
                if !values_equal(&a, &b) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_eq failed:\n  expected: {}\n  actual:   {}", b, a
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_ne" => {
                let a = args.first().cloned().unwrap_or(Value::Nil);
                let b = args.get(1).cloned().unwrap_or(Value::Nil);
                if values_equal(&a, &b) {
                    return Err(RuntimeError::Panic(format!("assert_ne failed: both equal {}", a)));
                }
                return Ok(Value::Nil);
            }
            "assert_true" => {
                let cond = args.first().cloned().unwrap_or(Value::Bool(false));
                if !matches!(cond, Value::Bool(true)) {
                    return Err(RuntimeError::Panic("assert_true failed: condition was false".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_false" => {
                let cond = args.first().cloned().unwrap_or(Value::Bool(true));
                if matches!(cond, Value::Bool(true)) {
                    return Err(RuntimeError::Panic("assert_false failed: condition was true".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_nil" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if !matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic(format!("assert_nil failed: got {}", v)));
                }
                return Ok(Value::Nil);
            }
            "assert_not_nil" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic("assert_not_nil failed: value was nil".into()));
                }
                return Ok(Value::Nil);
            }
            "assert_err" => {
                let v = args.first().cloned().unwrap_or(Value::Nil);
                if !matches!(v, Value::Nil) {
                    return Err(RuntimeError::Panic(format!("assert_err failed: expected error but got {}", v)));
                }
                return Ok(Value::Nil);
            }
            "assert_approx" => {
                let a     = args.first().map(|v| v.to_float()).unwrap_or(0.0);
                let b     = args.get(1).map(|v| v.to_float()).unwrap_or(0.0);
                let delta = args.get(2).map(|v| v.to_float()).unwrap_or(0.0);
                if (a - b).abs() > delta {
                    return Err(RuntimeError::Panic(format!(
                        "assert_approx failed: |{} - {}| = {} > {}", a, b, (a - b).abs(), delta
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_contains" => {
                let s   = args.first().map(|v| v.to_string()).unwrap_or_default();
                let sub = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if !s.contains(&sub) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_contains failed:\n  string:    {}\n  substring: {}", s, sub
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_starts_with" => {
                let s      = args.first().map(|v| v.to_string()).unwrap_or_default();
                let prefix = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                if !s.starts_with(&prefix) {
                    return Err(RuntimeError::Panic(format!(
                        "assert_starts_with failed:\n  string: {}\n  prefix: {}", s, prefix
                    )));
                }
                return Ok(Value::Nil);
            }
            "assert_len" => {
                let actual = match args.first() {
                    Some(Value::Array(a)) => a.len() as i64,
                    Some(Value::Str(s))   => s.chars().count() as i64,
                    _ => 0,
                };
                let expected = args.get(1).map(|v| v.to_int()).unwrap_or(0);
                if actual != expected {
                    return Err(RuntimeError::Panic(format!(
                        "assert_len failed: expected {}, got {}", expected, actual
                    )));
                }
                return Ok(Value::Nil);
            }
            "fail" => {
                let msg = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Err(RuntimeError::Panic(format!("test failed: {}", msg)));
            }
            "skip" => {
                // Skipping isn't distinguished from passing at this layer
                // (no separate "skipped" exit-code channel) — treat as a
                // no-op success. A real skip-tracking mechanism belongs in
                // the bytes test_runner, which already has its own
                // per-function subprocess invocation it could extend.
                return Ok(Value::Nil);
            }
            "file_size_bytes" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Int(std::fs::metadata(p.as_str()).map(|m| m.len() as i64).unwrap_or(0)));
            }
            "is_dir" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Bool(std::path::Path::new(p.as_str()).is_dir()));
            }
            "file_stem" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).file_stem().and_then(|s| s.to_str()).unwrap_or("").to_string()));
            }
            "file_ext" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).extension().and_then(|s| s.to_str()).unwrap_or("").to_string()));
            }
            "file_parent" => {
                let p = args.first().map(|v| v.to_string()).unwrap_or_default();
                return Ok(Value::Str(std::path::Path::new(p.as_str()).parent().and_then(|p| p.to_str()).unwrap_or("").to_string()));
            }
            "new_uuid" => {
                let mut b = [0u8; 16];
                if let Ok(mut f) = std::fs::File::open("/dev/urandom") { use std::io::Read; let _ = f.read_exact(&mut b); }
                b[6] = (b[6] & 0x0f) | 0x40;
                b[8] = (b[8] & 0x3f) | 0x80;
                return Ok(Value::Str(format!(
                    "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                    b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]
                )));
            }
            "bold"        => { return Ok(Value::Str(format!("\x1b[1m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "green_text"  => { return Ok(Value::Str(format!("\x1b[32m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "red_text"    => { return Ok(Value::Str(format!("\x1b[31m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "yellow_text" => { return Ok(Value::Str(format!("\x1b[33m{}\x1b[0m", args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "dim_text"    => { return Ok(Value::Str(format!("\x1b[2m{}\x1b[0m",  args.first().map(|v| v.to_string()).unwrap_or_default()))); }
            "dns_resolve" => {
                let host = args.first().map(|v| v.to_string()).unwrap_or_default();
                use std::net::ToSocketAddrs;
                let ip = format!("{}:0", host).to_socket_addrs().ok().and_then(|mut a| a.next()).map(|a| a.ip().to_string()).unwrap_or_default();
                return Ok(Value::Str(ip));
            }
            "scan_port_net" | "scan_port" => {
                let host    = args.first().map(|v| v.to_string()).unwrap_or_default();
                let port    = args.get(1).map(|v| v.to_int()).unwrap_or(80) as u16;
                let timeout = args.get(2).map(|v| v.to_int()).unwrap_or(500) as u64;
                use std::net::TcpStream;
                let addr = format!("{}:{}", host, port);
                let open = addr.parse::<std::net::SocketAddr>()
                    .map(|a| TcpStream::connect_timeout(&a, std::time::Duration::from_millis(timeout)).is_ok())
                    .unwrap_or(false);
                return Ok(Value::Bool(open));
            }
            "sha256" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha256::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "sha512" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha512::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "md5" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Md5::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "sha1" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let mut hasher = Sha1::new();
                Sha2Digest::update(&mut hasher, data.as_bytes());
                let result = hasher.finalize();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hmac_sha256" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let msg = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut mac = <Hmac<Sha256> as Mac>::new_from_slice(key.as_bytes())
                    .expect("HMAC accepts any key length");
                Mac::update(&mut mac, msg.as_bytes());
                let result = mac.finalize().into_bytes();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "hmac_sha512" => {
                let key = args.first().map(|v| v.to_string()).unwrap_or_default();
                let msg = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let mut mac = <Hmac<Sha512> as Mac>::new_from_slice(key.as_bytes())
                    .expect("HMAC accepts any key length");
                Mac::update(&mut mac, msg.as_bytes());
                let result = mac.finalize().into_bytes();
                return Ok(Value::Str(result.iter().map(|b| format!("{:02x}", b)).collect()));
            }
            "rot13" => {
                let data = args.first().map(|v| v.to_string()).unwrap_or_default();
                let rotated: String = data.chars().map(|c| {
                    if c.is_ascii_lowercase() {
                        (((c as u8 - b'a' + 13) % 26) + b'a') as char
                    } else if c.is_ascii_uppercase() {
                        (((c as u8 - b'A' + 13) % 26) + b'A') as char
                    } else {
                        c
                    }
                }).collect();
                return Ok(Value::Str(rotated));
            }
            "xor_hex" => {
                let a = args.first().map(|v| v.to_string()).unwrap_or_default();
                let b_s = args.get(1).map(|v| v.to_string()).unwrap_or_default();
                let ab: Vec<u8> = (0..a.len()).step_by(2).filter_map(|i| u8::from_str_radix(a.get(i..i+2).unwrap_or(""), 16).ok()).collect();
                let bb: Vec<u8> = (0..b_s.len()).step_by(2).filter_map(|i| u8::from_str_radix(b_s.get(i..i+2).unwrap_or(""), 16).ok()).collect();
                let r: String = ab.iter().zip(bb.iter().cycle()).map(|(x,y)| format!("{:02x}", x^y)).collect();
                return Ok(Value::Str(r));
            }
            // ── end real stdlib ─────────────────────────────────────────
            _ => {}
        }

        // User-defined functions
        if let Some(f) = self.fns.get(name).cloned() {
            // Monomorphize generic functions at call site
            let f = if !f.type_params.is_empty() {
                // Build type substitution from actual argument types
                let mut subst = std::collections::HashMap::new();
                for (tp, val) in f.type_params.iter().zip(args.iter()) {
                    let concrete_ty = match val {
                        Value::Int(_)   => hsharp_parser::ast::TypeExpr::Named("int".into()),
                        Value::Float(_) => hsharp_parser::ast::TypeExpr::Named("float".into()),
                        Value::Str(_)   => hsharp_parser::ast::TypeExpr::Named("string".into()),
                        Value::Bool(_)  => hsharp_parser::ast::TypeExpr::Named("bool".into()),
                        Value::Array(_) => hsharp_parser::ast::TypeExpr::Array(Box::new(hsharp_parser::ast::TypeExpr::Named("any".into()))),
                        _               => hsharp_parser::ast::TypeExpr::Named("any".into()),
                    };
                    subst.insert(tp.name.clone(), concrete_ty);
                }
                mono_fn_inline(&f, &subst)
            } else {
                f
            };
            self.env.push();
            for (param, val) in f.params.iter().zip(args) {
                self.env.define(&param.name, val, param.mutable);
            }
            let result = self.exec_block(&f.body)?;
            self.env.pop();
            let resolved = match result {
                Some(Value::Return(v)) => *v,
                Some(v) => v,
                None => Value::Nil,
            };
            // If function is async, wrap in AsyncTask::Ready
            if f.is_async {
                return Ok(Value::AsyncTask(Box::new(AsyncTaskState::Ready(resolved))));
            }
            return Ok(resolved);
        }
        // Unknown function — return Nil (or could return error)
        Ok(Value::Nil)


    }

    fn call_method(&mut self, obj: Value, method: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        // User-defined `impl Type is fn method(self, ...) ... end` methods
        // take priority over the builtin method table below — this is what
        // makes `point.distance_to(other)`, custom `HashMap`-style structs,
        // etc. actually execute real H# code instead of always falling
        // through to the generic struct-field lookup. Mutation of `self`
        // inside the method is discarded here (no receiver binding to write
        // back to) — see `Expr::MethodCall` in `eval_expr` for the path
        // that *does* propagate self-mutation back to a named variable.
        if matches!(obj, Value::Struct { .. }) {
            if let Some(result) = self.try_user_method(&obj, method, &args) {
                return result.map(|(ret, _mutated_self)| ret);
            }
        }

        let arg0_str = || args.first().and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
        let arg0_int = || args.first().and_then(|v| if let Value::Int(n) = v { Some(*n) } else { None }).unwrap_or(0);

        match (&obj, method) {
            // ── String methods ────────────────────────────────────────────────
            (Value::Str(s), "len")          => Ok(Value::Int(s.len() as i64)),
            (Value::Str(s), "to_upper")     => Ok(Value::Str(s.to_uppercase())),
            (Value::Str(s), "to_uppercase") => Ok(Value::Str(s.to_uppercase())),
            (Value::Str(s), "to_lower")     => Ok(Value::Str(s.to_lowercase())),
            (Value::Str(s), "to_lowercase") => Ok(Value::Str(s.to_lowercase())),
            (Value::Str(s), "trim")         => Ok(Value::Str(s.trim().to_string())),
            (Value::Str(s), "trim_start")   => Ok(Value::Str(s.trim_start().to_string())),
            (Value::Str(s), "trim_end")     => Ok(Value::Str(s.trim_end().to_string())),
            (Value::Str(s), "to_string")    => Ok(Value::Str(s.clone())),
            (Value::Str(s), "is_empty")     => Ok(Value::Bool(s.is_empty())),
            (Value::Str(s), "reverse") => {
                Ok(Value::Str(s.chars().rev().collect()))
            }
            (Value::Str(s), "contains") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.contains(pat.as_str())))
            }
            (Value::Str(s), "starts_with") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.starts_with(pat.as_str())))
            }
            (Value::Str(s), "ends_with") => {
                let pat = arg0_str();
                Ok(Value::Bool(s.ends_with(pat.as_str())))
            }
            (Value::Str(s), "split") => {
                let sep = arg0_str();
                Ok(Value::Array(s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect()))
            }
            (Value::Str(s), "replace") => {
                let from = arg0_str();
                let to = args.get(1).and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                Ok(Value::Str(s.replace(from.as_str(), to.as_str())))
            }
            (Value::Str(s), "replace_all") => {
                let from = arg0_str();
                let to = args.get(1).and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                Ok(Value::Str(s.replace(from.as_str(), to.as_str())))
            }
            (Value::Str(s), "index_of") => {
                let sub = arg0_str();
                match s.find(sub.as_str()) {
                    Some(i) => Ok(Value::Int(i as i64)),
                    None => Ok(Value::Int(-1)),
                }
            }
            (Value::Str(s), "count") => {
                let sub = arg0_str();
                Ok(Value::Int(s.matches(sub.as_str()).count() as i64))
            }
            (Value::Str(s), "chars") => {
                Ok(Value::Array(s.chars().map(|c| Value::Str(c.to_string())).collect()))
            }
            (Value::Str(s), "bytes") => {
                Ok(Value::Bytes(s.as_bytes().to_vec()))
            }
            (Value::Str(s), "parse_int") => {
                s.trim().parse::<i64>()
                    .map(Value::Int)
                    .map_err(|_| RuntimeError::TypeError(format!("cannot parse int from '{}'", s)))
            }
            (Value::Str(s), "parse_float") => {
                s.trim().parse::<f64>()
                    .map(Value::Float)
                    .map_err(|_| RuntimeError::TypeError(format!("cannot parse float from '{}'", s)))
            }
            (Value::Str(s), "repeat") => {
                let n = arg0_int() as usize;
                Ok(Value::Str(s.repeat(n)))
            }
            // ── Array methods ─────────────────────────────────────────────────
            (Value::Array(arr), "len")     => Ok(Value::Int(arr.len() as i64)),
            (Value::Array(arr), "first")   => Ok(arr.first().cloned().unwrap_or(Value::Nil)),
            (Value::Array(arr), "last")    => Ok(arr.last().cloned().unwrap_or(Value::Nil)),
            (Value::Array(arr), "is_empty") => Ok(Value::Bool(arr.is_empty())),
            (Value::Array(arr), "contains") => {
                let target = args.first().cloned().unwrap_or(Value::Nil);
                Ok(Value::Bool(arr.iter().any(|v| values_equal(v, &target))))
            }
            (Value::Array(arr), "reverse") => {
                let mut rev = arr.clone();
                rev.reverse();
                Ok(Value::Array(rev))
            }
            (Value::Array(arr), "join") => {
                let sep = arg0_str();
                let parts: Vec<String> = arr.iter().map(|v| v.to_str_val()).collect();
                Ok(Value::Str(parts.join(sep.as_str())))
            }
            (Value::Array(_), "push") => {
                // push mutates — handled by caller via assign; here we just
                // return the value pushed (the interpreter special-cases mutations)
                Ok(args.first().cloned().unwrap_or(Value::Nil))
            }
            // ── Bytes methods ─────────────────────────────────────────────────
            (Value::Bytes(b), "len") => Ok(Value::Int(b.len() as i64)),
            (Value::Bytes(b), "to_hex") => {
                Ok(Value::Str(b.iter().map(|byte| format!("{:02x}", byte)).collect()))
            }
            (Value::Bytes(b), "to_string") => {
                Ok(Value::Str(String::from_utf8_lossy(b).to_string()))
            }
            (Value::Bytes(b), "is_empty") => Ok(Value::Bool(b.is_empty())),
            // ── Primitive to_string ───────────────────────────────────────────
            (Value::Int(n), "to_string")   => Ok(Value::Str(n.to_string())),
            (Value::Float(f), "to_string") => Ok(Value::Str(f.to_string())),
            (Value::Bool(b), "to_string")  => Ok(Value::Str(b.to_string())),
            (Value::Nil, "to_string")      => Ok(Value::Str("nil".to_string())),
            // ── HashMap (v0.8) — read-only methods (mutation handled via
            // compute_mutated_container in the MethodCall write-back path) ──
            (Value::Struct { name, fields }, "get") if name == "__hashmap" => {
                let key = arg0_str();
                Ok(fields.get(&key).cloned().unwrap_or(Value::Nil))
            }
            (Value::Struct { name, fields }, "contains_key") if name == "__hashmap" => {
                let key = arg0_str();
                Ok(Value::Bool(fields.contains_key(&key)))
            }
            (Value::Struct { name, fields }, "len") if name == "__hashmap" => {
                Ok(Value::Int(fields.len() as i64))
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__hashmap" => {
                Ok(Value::Bool(fields.is_empty()))
            }
            (Value::Struct { name, fields }, "keys") if name == "__hashmap" => {
                Ok(Value::Array(fields.keys().map(|k| Value::Str(k.clone())).collect()))
            }
            (Value::Struct { name, fields }, "values") if name == "__hashmap" => {
                Ok(Value::Array(fields.values().cloned().collect()))
            }
            (Value::Struct { name, .. }, "insert") if name == "__hashmap" => {
                // Mutation is applied via compute_mutated_container's
                // write-back; `insert` itself doesn't return a useful value.
                Ok(Value::Nil)
            }
            (Value::Struct { name, .. }, "remove") if name == "__hashmap" => {
                Ok(Value::Nil)
            }
            // ── HashSet (v0.8) ─────────────────────────────────────────────────
            (Value::Struct { name, .. }, "insert") if name == "__hashset" => {
                Ok(Value::Nil)
            }
            (Value::Struct { name, .. }, "remove") if name == "__hashset" => {
                Ok(Value::Nil)
            }
            (Value::Struct { name, fields }, "contains") if name == "__hashset" => {
                let target = args.first().cloned().unwrap_or(Value::Nil);
                let items = match fields.get("items") { Some(Value::Array(a)) => a, _ => return Ok(Value::Bool(false)) };
                Ok(Value::Bool(items.iter().any(|v| values_equal(v, &target))))
            }
            (Value::Struct { name, fields }, "len") if name == "__hashset" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Int(a.len() as i64)),
                    _ => Ok(Value::Int(0)),
                }
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__hashset" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Bool(a.is_empty())),
                    _ => Ok(Value::Bool(true)),
                }
            }
            (Value::Struct { name, fields }, "to_array") if name == "__hashset" => {
                Ok(fields.get("items").cloned().unwrap_or(Value::Array(Vec::new())))
            }
            // ── Queue / Stack (v0.8) — shared read-only methods ─────────────────
            (Value::Struct { name, fields }, "len") if name == "__queue" || name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Int(a.len() as i64)),
                    _ => Ok(Value::Int(0)),
                }
            }
            (Value::Struct { name, fields }, "is_empty") if name == "__queue" || name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(Value::Bool(a.is_empty())),
                    _ => Ok(Value::Bool(true)),
                }
            }
            (Value::Struct { name, fields }, "peek") if name == "__queue" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.first().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, fields }, "peek") if name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.last().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            // `pop`'s *return value* for queue/stack: the write-back of the
            // shrunk container happens separately in compute_mutated_container;
            // here we just report what *would be / was* removed.
            (Value::Struct { name, fields }, "pop") if name == "__queue" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.first().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, fields }, "pop") if name == "__stack" => {
                match fields.get("items") {
                    Some(Value::Array(a)) => Ok(a.last().cloned().unwrap_or(Value::Nil)),
                    _ => Ok(Value::Nil),
                }
            }
            (Value::Struct { name, .. }, "push") if name == "__queue" || name == "__stack" => {
                // The pushed value is the expression's result, matching
                // Array's push semantics; the actual mutation/write-back
                // happens in compute_mutated_container.
                Ok(args.first().cloned().unwrap_or(Value::Nil))
            }
            // ── Struct field dispatch ─────────────────────────────────────────
            (Value::Struct { fields, .. }, _) => {
                if let Some(v) = fields.get(method) {
                    Ok(v.clone())
                } else {
                    Err(RuntimeError::TypeError(format!("no method or field `{}` on struct", method)))
                }
            }
            _ => Err(RuntimeError::TypeError(format!("no method `{}` on {}", method, obj))),
        }
    }

    fn eval_binop(&self, l: Value, op: &BinOp, r: Value) -> Result<Value, RuntimeError> {
        match op {
            BinOp::Add => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_add(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a + b)),
                (Value::Int(a), Value::Float(b)) => Ok(Value::Float(a as f64 + b)),
                (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a + b as f64)),
                (Value::Str(a), Value::Str(b)) => Ok(Value::Str(a + &b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot add {} and {}", l, r))),
            },
            BinOp::Sub => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_sub(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a - b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot subtract {} and {}", l, r))),
            },
            BinOp::Mul => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_mul(b))),
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot multiply {} and {}", l, r))),
            },
            BinOp::Div => match (l, r) {
                (Value::Int(a), Value::Int(b)) => {
                    if b == 0 { Err(RuntimeError::DivisionByZero) }
                    else { Ok(Value::Int(a / b)) }
                },
                (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a / b)),
                (l, r) => Err(RuntimeError::TypeError(format!("cannot divide {} and {}", l, r))),
            },
            BinOp::Mod => match (l, r) {
                (Value::Int(a), Value::Int(b)) => {
                    if b == 0 { Err(RuntimeError::DivisionByZero) }
                    else { Ok(Value::Int(a % b)) }
                },
                (l, r) => Err(RuntimeError::TypeError(format!("cannot mod {} and {}", l, r))),
            },
            BinOp::Eq => Ok(Value::Bool(values_equal(&l, &r))),
            BinOp::NotEq => Ok(Value::Bool(!values_equal(&l, &r))),
            BinOp::Lt => compare_values(l, r, |a, b| a < b),
            BinOp::Gt => compare_values(l, r, |a, b| a > b),
            BinOp::LtEq => compare_values(l, r, |a, b| a <= b),
            BinOp::GtEq => compare_values(l, r, |a, b| a >= b),
            BinOp::And => Ok(Value::Bool(l.is_truthy() && r.is_truthy())),
            BinOp::Or => Ok(if l.is_truthy() { l } else { r }),
            BinOp::BitAnd => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a & b)),
                _ => Err(RuntimeError::TypeError("bitwise & requires integers".into())),
            },
            BinOp::BitOr => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a | b)),
                _ => Err(RuntimeError::TypeError("bitwise | requires integers".into())),
            },
            BinOp::BitXor => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a ^ b)),
                _ => Err(RuntimeError::TypeError("bitwise ^ requires integers".into())),
            },
            BinOp::Shl => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a << b)),
                _ => Err(RuntimeError::TypeError("<< requires integers".into())),
            },
            BinOp::Shr => match (l, r) {
                (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a >> b)),
                _ => Err(RuntimeError::TypeError(">> requires integers".into())),
            },
        }
    }

    fn pattern_matches(&self, pat: &Pattern, val: &Value) -> bool {
        match pat {
            Pattern::Wildcard(_) => true,
            // A bare identifier pattern always matches (and binds) UNLESS
            // it happens to name a known unit variant of an enum the
            // value belongs to — this supports the common style of
            // writing unit variants without `Type::` qualification or
            // parens, e.g. `match status is Ok => ... Error(msg) => ... end`.
            // Most of the time `name` is just a binding, so the variant
            // check only applies when the value is actually a
            // `Type::Variant`-shaped struct and `name` matches its bare
            // variant name.
            Pattern::Ident(name, _) => {
                if let Value::Struct { name: type_variant, .. } = val {
                    if let Some((_, variant)) = type_variant.split_once("::") {
                        if variant == name { return true; }
                        // A different variant of (presumably) the same
                        // enum — an Ident pattern shouldn't blanket-match
                        // every enum value, only ones whose variant name
                        // it doesn't otherwise look like it's trying to
                        // exclude. Since Ident patterns are also plain
                        // bindings, fall through to true here too — H#
                        // doesn't track enum exhaustiveness strictly
                        // enough at the interpreter level to disambiguate
                        // "binding to any value" vs "matching a wrong
                        // variant name that happens to look like one";
                        // the typechecker's exhaustiveness pass is the
                        // proper place for that warning.
                    }
                }
                true
            }
            Pattern::Literal(lit, _) => match (lit, val) {
                (Literal::Int(a), Value::Int(b)) => a == b,
                (Literal::Float(a), Value::Float(b)) => (a - b).abs() < f64::EPSILON,
                (Literal::Bool(a), Value::Bool(b)) => a == b,
                (Literal::String(a), Value::Str(b)) => a == b,
                (Literal::Nil, Value::Nil) => true,
                _ => false,
            },
            Pattern::Or(pats, _) => pats.iter().any(|p| self.pattern_matches(p, val)),
            Pattern::Enum { qualified_type, variant, inner, .. } => {
                let Value::Struct { name: type_variant, fields } = val else { return false; };
                let actual_variant = type_variant.split_once("::").map(|(_, v)| v).unwrap_or(type_variant.as_str());
                let actual_type    = type_variant.split_once("::").map(|(t, _)| t);
                if actual_variant != variant { return false; }
                if let Some(qt) = qualified_type {
                    if actual_type != Some(qt.as_str()) { return false; }
                }
                if inner.is_empty() { return true; }
                inner.iter().enumerate().all(|(i, p)| {
                    match fields.get(&i.to_string()) {
                        Some(v) => self.pattern_matches(p, v),
                        None => false,
                    }
                })
            }
            Pattern::Tuple(pats, _) => {
                let Value::Tuple(items) = val else { return false; };
                if pats.len() != items.len() { return false; }
                pats.iter().zip(items.iter()).all(|(p, v)| self.pattern_matches(p, v))
            }
            Pattern::Struct { fields: pat_fields, .. } => {
                let Value::Struct { fields, .. } = val else { return false; };
                pat_fields.iter().all(|(fname, fpat)| {
                    match fields.get(fname) {
                        Some(v) => self.pattern_matches(fpat, v),
                        None => false,
                    }
                })
            }
            Pattern::Range(lo, hi, inclusive, _) => {
                let (Pattern::Literal(Literal::Int(lo), _), Pattern::Literal(Literal::Int(hi), _)) = (lo.as_ref(), hi.as_ref()) else {
                    return false;
                };
                match val {
                    Value::Int(n) => if *inclusive { *n >= *lo && *n <= *hi } else { *n >= *lo && *n < *hi },
                    _ => false,
                }
            }
        }
    }

    fn bind_pattern(&mut self, pat: &Pattern, val: Value) {
        match pat {
            Pattern::Ident(name, _) => {
                if name != "_" {
                    self.env.define(name, val, false);
                }
            }
            Pattern::Enum { inner, .. } => {
                if let Value::Struct { fields, .. } = &val {
                    for (i, p) in inner.iter().enumerate() {
                        if let Some(v) = fields.get(&i.to_string()) {
                            self.bind_pattern(p, v.clone());
                        }
                    }
                }
            }
            Pattern::Tuple(pats, _) => {
                if let Value::Tuple(items) = &val {
                    for (p, v) in pats.iter().zip(items.iter()) {
                        self.bind_pattern(p, v.clone());
                    }
                }
            }
            Pattern::Struct { fields: pat_fields, .. } => {
                if let Value::Struct { fields, .. } = &val {
                    for (fname, fpat) in pat_fields {
                        if let Some(v) = fields.get(fname) {
                            self.bind_pattern(fpat, v.clone());
                        }
                    }
                }
            }
            Pattern::Or(pats, _) => {
                // Bind using whichever alternative actually matched.
                if let Some(p) = pats.iter().find(|p| self.pattern_matches(p, &val)) {
                    self.bind_pattern(p, val);
                }
            }
            Pattern::Wildcard(_) | Pattern::Literal(_, _) | Pattern::Range(_, _, _, _) => {}
        }
    }

    pub fn get_stdout(&self) -> &str {
        &self.stdout
    }

    fn assign_lhs(&mut self, lhs: &Expr, val: Value) -> Result<(), RuntimeError> {
        match lhs {
            Expr::Ident(name, _) => {
                if !self.env.set(name, val) {
                    return Err(RuntimeError::ImmutableAssign(name.clone()));
                }
                Ok(())
            }
            Expr::IndexAccess(arr_expr, idx_expr, _) => {
                let idx = match self.eval_expr(idx_expr)? {
                    Value::Int(i) => i as usize,
                    _ => return Err(RuntimeError::TypeError("index must be int".into())),
                };
                if let Expr::Ident(name, _) = arr_expr.as_ref() {
                    if let Some(v) = self.env.get(name).cloned() {
                        if let Value::Array(mut arr) = v {
                            if idx < arr.len() {
                                arr[idx] = val;
                                self.env.set(name, Value::Array(arr));
                                return Ok(());
                            }
                            return Err(RuntimeError::IndexOutOfBounds(idx as i64, arr.len()));
                        }
                    }
                }
                Err(RuntimeError::TypeError("cannot index-assign".into()))
            }
            Expr::FieldAccess(obj_expr, field, _) => {
                if let Expr::Ident(name, _) = obj_expr.as_ref() {
                    if let Some(v) = self.env.get(name).cloned() {
                        if let Value::Struct { name: sname, mut fields } = v {
                            fields.insert(field.clone(), val);
                            self.env.set(name, Value::Struct { name: sname, fields });
                            return Ok(());
                        }
                    }
                }
                Err(RuntimeError::TypeError("cannot field-assign".into()))
            }
            _ => Err(RuntimeError::TypeError("invalid assignment target".into())),
        }
    }
}

/// Explicit alias table for `module::function` paths that don't follow the
/// plain snake_case convention, or whose target builtin has a different
/// bare name than `module_function` would suggest (e.g. `crypto::sha256`
/// must resolve to the existing `sha256` builtin, not a nonexistent
/// `crypto_sha256`). Returns the real builtin symbol name implemented in
/// `call_fn`, or None if `full_path` isn't a known special case (callers
/// should then fall back to the snake_case guess or the bare last segment).
fn resolve_stdlib_alias(full_path: &str) -> Option<&'static str> {
    Some(match full_path {
        // crypto — bridge to the differently-named existing builtins
        "crypto::sha256"        => "sha256",
        "crypto::sha512"        => "sha512",
        "crypto::md5"            => "md5",
        "crypto::sha1"           => "sha1",
        "crypto::hmac_sha256"   => "hmac_sha256",
        "crypto::hmac_sha512"   => "hmac_sha512",
        "crypto::random_bytes"  => "random_string",
        "crypto::random_int"    => "random_int",
        "sec::xor"               => "xor_hex",
        "sec::rot13"             => "rot13",
        "sec::scan_port"         => "scan_port",
        // hex
        "hex::encode"            => "hex_encode",
        "hex::decode"            => "hex_decode",
        // regex — std/regex.h#'s H# API takes (text, pattern, ...) i.e.
        // subject-first; bridge to the _ta ("text-argument-first") wrapper
        // builtins, which swap order before delegating to the underlying
        // grep/sed-based (pattern, text) implementations.
        "regex::is_match"        => "re_match_ta",
        "re::is_match"           => "re_match_ta",
        "regex::find"            => "re_find_ta",
        "re::find"                => "re_find_ta",
        "regex::find_all"        => "re_find_all_ta",
        "re::find_all"            => "re_find_all_ta",
        "regex::replace"         => "re_replace_ta",
        "re::replace"             => "re_replace_ta",
        "regex::replace_all"     => "re_replace_all_ta",
        "re::replace_all"         => "re_replace_all_ta",
        "regex::split"            => "re_split_ta",
        "re::split"                => "re_split_ta",
        // fs
        "fs::read"                => "fs_read",
        "fs::write"               => "fs_write",
        "fs::exists"              => "fs_exists",
        "fs::mkdir"               => "fs_mkdir_all",
        "fs::remove"              => "fs_remove",
        "fs::append"              => "fs_append",
        "fs::is_dir"              => "fs_is_dir",
        "fs::is_file"             => "fs_is_file",
        "fs::rmdir"               => "fs_rmdir",
        "fs::rmdir_all"           => "fs_rmdir_all",
        "fs::read_lines"          => "fs_read_lines",
        "fs::size"                => "fs_size",
        "fs::copy"                => "fs_copy",
        "fs::rename"              => "fs_rename",
        "fs::cwd"                 => "fs_cwd",
        "fs::chdir"               => "fs_cwd", // no-op placeholder until chdir lands
        "fs::list_dir"            => "fs_list_dir",
        // path
        "path::join"              => "path_join",
        "path::stem"              => "path_stem",
        "path::extension"         => "path_extension",
        "path::parent"            => "path_parent",
        // env
        "env::temp_dir"           => "env_temp_dir",
        "env::get"                => "env_get",
        "env::args"               => "env_args",
        "env::home"               => "env_home",
        // iter
        "iter::map"                => "iter_map",
        "iter::filter"             => "iter_filter",
        "iter::reduce"             => "iter_reduce",
        "iter::zip"                => "iter_zip",
        "iter::chain"              => "iter_chain",
        "iter::take"                => "iter_take",
        "iter::skip"                => "iter_skip",
        "iter::any"                 => "iter_any",
        "iter::all"                 => "iter_all",
        "iter::sum"                 => "iter_sum",
        "iter::product"             => "iter_product",
        "iter::reverse"             => "iter_reverse",
        "iter::join"                => "iter_join",
        "iter::repeat"              => "iter_repeat",
        "iter::unique"              => "iter_unique",
        // sort
        "sort::sort_ints"           => "sort_ints",
        "sort::sort_strings"        => "sort_strings",
        "sort::binary_search"       => "binary_search",
        "sort::binary_search_left"  => "binary_search_left",
        "sort::min_int"             => "min_int",
        "sort::max_int"             => "max_int",
        "sort::merge_sorted"        => "merge_sorted",
        // async
        "async::spawn"               => "async_spawn",
        "async::timeout"             => "async_timeout",
        // str
        "str::trim"               => "str_trim",
        "str::split"              => "str_split",
        "str::replace"            => "str_replace",
        "str::join"               => "str_join",
        // conv
        "conv::str_to_int"        => "conv_str_to_int",
        "conv::int_to_hex"        => "conv_int_to_hex",
        "conv::to_bytes"          => "conv_to_bytes",
        // db
        "db::open"                => "db_open",
        "db::query"               => "db_query",
        "db::exec"                => "db_exec",
        "db::close"               => "db_close",
        // dns
        "dns::resolve"            => "dns_resolve",
        // uuid
        "uuid::v4"                 => "new_uuid",
        // time
        "t::now_unix"             => "now_unix",
        "t::now_ms"               => "now_ms",
        "t::sleep_ms"             => "sleep_ms",
        "time::now_unix"          => "time_unix",
        "time::now_ms"            => "time_ms",
        // collections — native HashMap/HashSet/Queue/Stack constructors
        "col::HashMap::new"        => "hashmap_new",
        "col::HashSet::new"        => "hashset_new",
        "col::Queue::new"          => "queue_new",
        "col::Stack::new"          => "stack_new",
        // json — set_str/set_int/set_bool all bridge to the same generic
        // json_set builtin (the value's runtime type is preserved either way)
        "json::set_str"            => "json_set",
        "json::set_int"            => "json_set",
        "json::set_bool"           => "json_set",
        // The rest of the json:: API — each maps 1:1 to its json_* builtin.
        // These were missing entirely before (only the three set_* aliases
        // existed), meaning json::parse, json::get_str, json::stringify,
        // etc. all silently fell through call_path's snake_case/
        // builtin_exists fallback to a nonexistent bare-last-segment
        // function name and returned Nil instead of ever reaching their
        // real implementations — every JSON test failed because of this.
        "json::parse"               => "json_parse",
        "json::parse_array"         => "json_parse_array",
        "json::stringify"           => "json_stringify",
        "json::stringify_pretty"    => "json_stringify_pretty",
        "json::empty_object"        => "json_empty_object",
        "json::object"              => "json_object",
        "json::get_str"             => "json_get_str",
        "json::get_int"             => "json_get_int",
        "json::get_float"           => "json_get_float",
        "json::get_bool"            => "json_get_bool",
        "json::get_obj"             => "json_get_obj",
        "json::get_arr"             => "json_get_arr",
        "json::has_key"             => "json_has_key",
        "json::is_null"             => "json_is_null",
        "json::obj_at"              => "json_obj_at",
        "json::int_at"              => "json_int_at",
        "json::str_at"              => "json_as_str",
        "json::as_int"              => "json_as_int",
        "json::as_str"              => "json_as_str",
        "json::query"               => "json_query",
        _ => return None,
    })
}

/// Returns true for snake_case names known to be handled by the builtin
/// match arm inside `call_fn` (the stdlib bridge). Used by `call_path` as a
/// best-effort guess only *after* the explicit alias table has already been
/// checked — this heuristic can produce a name that looks plausible but
/// isn't actually implemented, in which case `call_fn` silently returns
/// `Nil` rather than erroring. Prefer adding new mappings to
/// `resolve_stdlib_alias` over relying on this fallback.
fn builtin_exists(snake_name: &str) -> bool {
    const KNOWN: &[&str] = &[
        "math_sin", "math_cos", "math_tan", "math_asin", "math_acos", "math_atan",
        "math_atan2", "math_sqrt", "math_pow", "math_floor", "math_ceil", "math_round",
        "math_trunc", "math_log", "math_log2", "math_log10", "math_exp", "math_abs",
        "math_fabs", "math_ipow", "math_min", "math_max", "math_fmin", "math_fmax",
        "math_clamp", "math_fclamp", "math_gcd", "math_lcm", "math_pi", "math_e", "math_tau",
        "fs_read", "fs_write", "fs_exists", "fs_mkdir_all", "fs_remove", "fs_append",
        "fs_is_dir", "fs_rmdir", "fs_rmdir_all", "fs_read_lines", "fs_size",
        "fs_copy", "fs_rename", "fs_cwd", "fs_list_dir",
        "path_join", "path_stem", "path_extension", "path_parent",
        "env_temp_dir", "env_get", "env_args", "env_home",
        "str_trim", "str_split", "str_replace", "str_contains",
        "db_open", "db_query", "db_exec", "db_close",
        "sqlite_open", "sqlite_query", "sqlite_exec", "sqlite_close",
        "regex_match", "regex_find", "regex_find_all", "regex_replace",
        "re_match", "re_find", "re_find_all", "re_replace",
        "re_match_ta", "re_find_ta", "re_find_all_ta", "re_replace_ta",
        "re_replace_all_ta", "re_split_ta",
        "dns_resolve",
    ];
    KNOWN.contains(&snake_name)
}

/// Convert a parsed `serde_json::Value` into H#'s runtime `Value`.
/// JSON objects become `Value::Struct` (name `"__json"`) so they can be
/// passed around as opaque handles; JSON arrays become `Value::Array`.
fn json_to_value(j: &Json) -> Value {
    match j {
        Json::Null            => Value::Nil,
        Json::Bool(b)          => Value::Bool(*b),
        Json::Number(n) => {
            if let Some(i) = n.as_i64() { Value::Int(i) }
            else { Value::Float(n.as_f64().unwrap_or(0.0)) }
        }
        Json::String(s)        => Value::Str(s.clone()),
        Json::Array(items)     => Value::Array(items.iter().map(json_to_value).collect()),
        Json::Object(map) => {
            let mut fields = HashMap::new();
            for (k, v) in map {
                fields.insert(k.clone(), json_to_value(v));
            }
            Value::Struct { name: "__json".to_string(), fields }
        }
    }
}

/// Convert an H# runtime `Value` back into a `serde_json::Value` for
/// stringification.
fn value_to_json(v: &Value) -> Json {
    match v {
        Value::Nil          => Json::Null,
        Value::Bool(b)       => Json::Bool(*b),
        Value::Int(n)        => Json::Number((*n).into()),
        Value::Float(f)      => serde_json::Number::from_f64(*f).map(Json::Number).unwrap_or(Json::Null),
        Value::Str(s)        => Json::String(s.clone()),
        Value::Array(items)  => Json::Array(items.iter().map(value_to_json).collect()),
        Value::Struct { fields, .. } => {
            let mut map = serde_json::Map::new();
            for (k, v) in fields {
                map.insert(k.clone(), value_to_json(v));
            }
            Json::Object(map)
        }
        _ => Json::Null,
    }
}

/// Compute the new value of a container after a builtin mutating method
/// call, for receivers that are plain `Value::Array` (not user-defined
/// structs — those go through `try_user_method`'s `self`-mutation path
/// instead). Returns `None` for non-mutating methods, in which case the
/// caller should leave the original binding untouched.
fn compute_mutated_container(obj: &Value, method: &str, args: &[Value]) -> Option<Value> {
    match (obj, method) {
        (Value::Array(arr), "push") => {
            let mut new_arr = arr.clone();
            new_arr.push(args.first().cloned().unwrap_or(Value::Nil));
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "pop") => {
            let mut new_arr = arr.clone();
            new_arr.pop();
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "insert") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_arr = arr.clone();
            let idx = idx.min(new_arr.len());
            new_arr.insert(idx, val);
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "remove") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let mut new_arr = arr.clone();
            if idx < new_arr.len() { new_arr.remove(idx); }
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "clear") => {
            let _ = arr;
            Some(Value::Array(Vec::new()))
        }
        (Value::Array(arr), "sort") => {
            let mut new_arr = arr.clone();
            new_arr.sort_by(|a, b| {
                a.to_float().partial_cmp(&b.to_float()).unwrap_or(std::cmp::Ordering::Equal)
            });
            Some(Value::Array(new_arr))
        }
        // ── HashMap ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_fields = fields.clone();
            new_fields.insert(key, val);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let mut new_fields = fields.clone();
            new_fields.remove(&key);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── HashSet ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let mut new_items = items;
            if !new_items.iter().any(|v| values_equal(v, &val)) {
                new_items.push(val);
            }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let new_items: Vec<Value> = items.into_iter().filter(|v| !values_equal(v, &val)).collect();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Queue (FIFO: push appends, pop removes from the front) ────────
        (Value::Struct { name, fields }, "push") if name == "__queue" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__queue" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            if !items.is_empty() { items.remove(0); }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Stack (LIFO: push appends, pop removes from the back) ─────────
        (Value::Struct { name, fields }, "push") if name == "__stack" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__stack" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.pop();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        _ => None,
    }
}

fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => (*a as f64) == *b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Bytes(a), Value::Bytes(b)) => a == b,
        (Value::Nil, Value::Nil) => true,
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Tuple(a), Value::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Struct { name: na, fields: fa }, Value::Struct { name: nb, fields: fb }) => {
            na == nb && fa.len() == fb.len()
                && fa.iter().all(|(k, v)| fb.get(k).map(|v2| values_equal(v, v2)).unwrap_or(false))
        }
        _ => false,
    }
}

fn compare_values(a: Value, b: Value, f: impl Fn(f64, f64) -> bool) -> Result<Value, RuntimeError> {
    let result = match (a, b) {
        (Value::Int(a), Value::Int(b)) => f(a as f64, b as f64),
        (Value::Float(a), Value::Float(b)) => f(a, b),
        (Value::Int(a), Value::Float(b)) => f(a as f64, b),
        (Value::Float(a), Value::Int(b)) => f(a, b as f64),
        (a, b) => return Err(RuntimeError::TypeError(format!("cannot compare {} and {}", a, b))),
    };
    Ok(Value::Bool(result))
}
