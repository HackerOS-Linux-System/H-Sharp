use hsharp_parser::ast::*;
use std::collections::HashMap;
use std::fmt;

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
    Fn { name: String, params: Vec<Param>, body: Vec<Stmt>, env: Env },
    Return(Box<Value>),
    Break,
    Continue,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(n)    => write!(f, "{}", n),
            Value::Float(n)  => write!(f, "{}", n),
            Value::Bool(b)   => write!(f, "{}", b),
            Value::Str(s)    => write!(f, "{}", s),
            Value::Nil       => write!(f, "nil"),
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
    env: Env,
    fns: HashMap<String, FnDef>,
    structs: HashMap<String, StructDef>,
    stdout: String, // capture output
    pub captured_output: bool,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: Env::new(),
            fns: HashMap::new(),
            structs: HashMap::new(),
            stdout: String::new(),
            captured_output: false,
        }
    }

    pub fn run_module(&mut self, module: &Module) -> Result<(), RuntimeError> {
        // Register top-level items
        for item in &module.items {
            match item {
                Item::FnDef(f) => { self.fns.insert(f.name.clone(), f.clone()); }
                Item::StructDef(s) => { self.structs.insert(s.name.clone(), s.clone()); }
                _ => {}
            }
        }

        // Call main
        if let Some(main_fn) = self.fns.get("main").cloned() {
            let stmts = main_fn.body.clone();
            self.env.push();
            self.exec_block(&stmts)?;
            self.env.pop();
        }

        Ok(())
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
                    Expr::Unsafe(body, _, _) => {
                        self.env.push();
                        let r = self.exec_block(body)?;
                        self.env.pop();
                        Ok(r)
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
            _ => Ok(None),
        }
    }

    #[allow(unreachable_patterns)]
fn eval_expr(&mut self, expr: &Expr) -> Result<Value, RuntimeError> {
        match expr {
            Expr::Literal(lit, _) => Ok(match lit {
                Literal::Int(n) => Value::Int(*n),
                Literal::Float(f) => Value::Float(*f),
                Literal::String(s) => Value::Str(s.clone()),
                Literal::Bool(b) => Value::Bool(*b),
                Literal::Nil => Value::Nil,
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
                let callee_val = self.eval_expr(callee)?;
                match callee_val {
                    Value::Fn { params, body, env, .. } => {
                        let saved = self.env.clone();
                        self.env = env;
                        self.env.push();
                        for (param, val) in params.iter().zip(arg_vals) {
                            self.env.define(&param.name, val, param.mutable);
                        }
                        let result = self.exec_block(&body)?;
                        self.env.pop();
                        self.env = saved;
                        Ok(match result {
                            Some(Value::Return(v)) => *v,
                            Some(v) => v,
                            None => Value::Nil,
                        })
                    }
                    _ => Err(RuntimeError::TypeError("not callable".into())),
                }
            }
            Expr::MethodCall(obj, method, args, _) => {
                let obj_val = self.eval_expr(obj)?;
                let arg_vals: Vec<Value> = args.iter()
                    .map(|a| self.eval_expr(a))
                    .collect::<Result<_, _>>()?;
                self.call_method(obj_val, method, arg_vals)
            }
            Expr::FieldAccess(obj, field, _) => {
                let v = self.eval_expr(obj)?;
                match v {
                    Value::Struct { fields, .. } => {
                        fields.get(field).cloned()
                            .ok_or_else(|| RuntimeError::UndefinedField(field.clone()))
                    }
                    _ => Err(RuntimeError::TypeError(format!("no field `{}` on {}", field, v))),
                }
            }
            Expr::IndexAccess(arr, idx, _) => {
                let a = self.eval_expr(arr)?;
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
                        // Single-expression arm: evaluate as expression, not block
                        let result = if arm.body.len() == 1 {
                            match &arm.body[0] {
                                Stmt::Expr(e, _) => {
                                    let v = self.eval_expr(e)?;
                                    self.env.pop();
                                    return Ok(v);
                                }
                                _ => self.exec_block(&arm.body)?
                            }
                        } else {
                            self.exec_block(&arm.body)?
                        };
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
            _ => Ok(Value::Nil),
        }
    }

    fn call_fn(&mut self, name: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        // Builtins
        match name {
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
            "write" | "writeln" | "println" | "print" => {
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
                let out = std::process::Command::new("sh").arg("-c")
                    .arg(format!("printf '%s' '{}' | sha256sum | cut -d' ' -f1", data.replace('\'', "'\\''")))
                    .output();
                return Ok(Value::Str(out.map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default()));
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
            self.env.push();
            for (param, val) in f.params.iter().zip(args) {
                self.env.define(&param.name, val, param.mutable);
            }
            let result = self.exec_block(&f.body)?;
            self.env.pop();
            return Ok(match result {
                Some(Value::Return(v)) => *v,
                Some(v) => v,
                None => Value::Nil,
            });
        }
        // Unknown function — return Nil (or could return error)
        Ok(Value::Nil)


    }

    fn call_method(&mut self, obj: Value, method: &str, args: Vec<Value>) -> Result<Value, RuntimeError> {
        match (&obj, method) {
            (Value::Str(s), "len") => Ok(Value::Int(s.len() as i64)),
            (Value::Str(s), "to_uppercase") => Ok(Value::Str(s.to_uppercase())),
            (Value::Str(s), "to_lowercase") => Ok(Value::Str(s.to_lowercase())),
            (Value::Str(s), "trim") => Ok(Value::Str(s.trim().to_string())),
            (Value::Str(s), "contains") => {
                let pat = args.first().and_then(|v| if let Value::Str(s) = v { Some(s.as_str()) } else { None }).unwrap_or("");
                Ok(Value::Bool(s.contains(pat)))
            }
            (Value::Str(s), "split") => {
                let sep = args.first().and_then(|v| if let Value::Str(s) = v { Some(s.clone()) } else { None }).unwrap_or_default();
                Ok(Value::Array(s.split(sep.as_str()).map(|p| Value::Str(p.to_string())).collect()))
            }
            (Value::Array(arr), "len") => Ok(Value::Int(arr.len() as i64)),
            (Value::Array(arr), "first") => Ok(arr.first().cloned().unwrap_or(Value::Nil)),
            (Value::Array(arr), "last") => Ok(arr.last().cloned().unwrap_or(Value::Nil)),
            (Value::Bytes(b), "len") => Ok(Value::Int(b.len() as i64)),
            (Value::Bytes(b), "to_hex") => {
                Ok(Value::Str(b.iter().map(|byte| format!("{:02x}", byte)).collect()))
            }
            // Array of ints can act as bytes
            (Value::Array(arr), "to_hex") => {
                let hex: String = arr.iter().map(|v| match v {
                    Value::Int(n) => format!("{:02x}", n & 0xFF),
                    _ => "??".to_string(),
                }).collect();
                Ok(Value::Str(hex))
            }
            (Value::Array(arr), "len") => Ok(Value::Int(arr.len() as i64)),
            (Value::Int(n), "to_string") => Ok(Value::Str(n.to_string())),
            (Value::Float(f), "to_string") => Ok(Value::Str(f.to_string())),
            (Value::Bool(b), "to_string") => Ok(Value::Str(b.to_string())),
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
            Pattern::Wildcard(_) | Pattern::Ident(_, _) => true,
            Pattern::Literal(lit, _) => match (lit, val) {
                (Literal::Int(a), Value::Int(b)) => a == b,
                (Literal::Bool(a), Value::Bool(b)) => a == b,
                (Literal::String(a), Value::Str(b)) => a == b,
                (Literal::Nil, Value::Nil) => true,
                _ => false,
            },
            Pattern::Or(pats, _) => pats.iter().any(|p| self.pattern_matches(p, val)),
            _ => false,
        }
    }

    fn bind_pattern(&mut self, pat: &Pattern, val: Value) {
        if let Pattern::Ident(name, _) = pat {
            if name != "_" {
                self.env.define(name, val, false);
            }
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

fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Nil, Value::Nil) => true,
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
