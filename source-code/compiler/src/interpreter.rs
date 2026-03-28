use hsharp_parser::ast::*;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use thiserror::Error;

// ─── Błędy runtime ────────────────────────────────────────────────────────────

#[derive(Error, Debug, Clone)]
pub enum RuntimeError {
    #[error("Niezdefiniowana zmienna: `{0}`")]
    UndefinedVar(String),
    #[error("Niezdefiniowana funkcja: `{0}`")]
    UndefinedFn(String),
    #[error("Błąd typów: {0}")]
    TypeError(String),
    #[error("Dzielenie przez zero")]
    DivisionByZero,
    #[error("Indeks poza zakresem: {0}")]
    IndexOutOfBounds(usize),
    #[error("Wyjątek: {0}")]
    Exception(String),
    #[error("IO: {0}")]
    Io(String),
    #[error("{0}")]
    Other(String),
}

impl From<std::io::Error> for RuntimeError {
    fn from(e: std::io::Error) -> Self { RuntimeError::Io(e.to_string()) }
}

// ─── Wartości runtime ─────────────────────────────────────────────────────────

/// Używamy Arc<str> dla stringów żeby unikać klonowania w hot path
#[derive(Debug, Clone)]
pub enum HValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Arc<str>),
    Char(char),
    Nil,
    List(Arc<Vec<HValue>>),
    Map(Arc<Vec<(HValue, HValue)>>),
    Fn {
        name: Arc<str>,
        params: Vec<Param>,
        body: Vec<Stmt>,
        closure: EnvFrame,
    },
    Object {
        class: Arc<str>,
        fields: Arc<HashMap<String, HValue>>,
    },
    ArcVal(Arc<HValue>),
    Builtin(BuiltinId),
}

/// Wbudowane funkcje jako enum zamiast String — O(1) dispatch
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinId {
    Write, Writeln, Read,
    Len, Push, Pop, Contains,
    ToInt, ToFloat, ToStr, ToBool,
    TypeOf, Assert, Panic, Exit,
    Rand, Sleep, Min, Max, Abs,
}

impl BuiltinId {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "write"    => Some(Self::Write),
            "writeln"  => Some(Self::Writeln),
            "read"     => Some(Self::Read),
            "len"      => Some(Self::Len),
            "push"     => Some(Self::Push),
            "pop"      => Some(Self::Pop),
            "contains" => Some(Self::Contains),
            "to_int"   => Some(Self::ToInt),
            "to_float" => Some(Self::ToFloat),
            "to_str"   => Some(Self::ToStr),
            "to_bool"  => Some(Self::ToBool),
            "typeof"   => Some(Self::TypeOf),
            "assert"   => Some(Self::Assert),
            "panic"    => Some(Self::Panic),
            "exit"     => Some(Self::Exit),
            "rand"     => Some(Self::Rand),
            "sleep"    => Some(Self::Sleep),
            "min"      => Some(Self::Min),
            "max"      => Some(Self::Max),
            "abs"      => Some(Self::Abs),
            _          => None,
        }
    }
}

impl fmt::Display for HValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HValue::Int(n)       => write!(f, "{}", n),
            HValue::Float(n)     => {
                if n.fract() == 0.0 { write!(f, "{:.1}", n) }
                else { write!(f, "{}", n) }
            }
            HValue::Bool(b)      => write!(f, "{}", b),
            HValue::Str(s)       => write!(f, "{}", s),
            HValue::Char(c)      => write!(f, "{}", c),
            HValue::Nil          => write!(f, "nil"),
            HValue::List(v)      => {
                write!(f, "[")?;
                for (i, x) in v.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", x)?;
                }
                write!(f, "]")
            }
            HValue::Map(m)       => {
                write!(f, "{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            HValue::Fn { name, .. }   => write!(f, "<fn {}>", name),
            HValue::Object { class, .. } => write!(f, "<{}>", class),
            HValue::ArcVal(v)    => write!(f, "Arc({})", v),
            HValue::Builtin(id)  => write!(f, "<builtin {:?}>", id),
        }
    }
}

impl HValue {
    #[inline]
    fn is_truthy(&self) -> bool {
        match self {
            HValue::Bool(b)   => *b,
            HValue::Nil       => false,
            HValue::Int(0)    => false,
            HValue::Str(s)    => !s.is_empty(),
            HValue::List(v)   => !v.is_empty(),
            _                 => true,
        }
    }

    #[inline]
    fn type_name(&self) -> &'static str {
        match self {
            HValue::Int(_)     => "Int",
            HValue::Float(_)   => "Float",
            HValue::Bool(_)    => "Bool",
            HValue::Str(_)     => "Str",
            HValue::Char(_)    => "Char",
            HValue::Nil        => "Nil",
            HValue::List(_)    => "List",
            HValue::Map(_)     => "Map",
            HValue::Fn { .. }  => "Fn",
            HValue::Object { class, .. } => "Object",
            HValue::ArcVal(_)  => "Arc",
            HValue::Builtin(_) => "Builtin",
        }
    }
}

// ─── Env stack (optymalizacja: Vec zamiast Box<Scope>) ───────────────────────

pub type EnvFrame = HashMap<String, HValue>;

pub struct Env {
    /// Stack ramek — push = nowy scope, pop = wyjście ze scope
    stack: Vec<EnvFrame>,
}

impl Env {
    pub fn new() -> Self {
        // Pre-alokacja dla typowego programu
        let mut global = HashMap::with_capacity(64);
        // Wbudowane funkcje w global scope
        for name in &[
            "write", "writeln", "read", "len", "push", "pop", "contains",
            "to_int", "to_float", "to_str", "to_bool", "typeof",
            "assert", "panic", "exit", "rand", "sleep", "min", "max", "abs",
        ] {
            if let Some(id) = BuiltinId::from_name(name) {
                global.insert(name.to_string(), HValue::Builtin(id));
            }
        }
        Self { stack: vec![global] }
    }

    #[inline]
    pub fn push(&mut self) {
        self.stack.push(HashMap::with_capacity(16));
    }

    #[inline]
    pub fn pop(&mut self) {
        if self.stack.len() > 1 { self.stack.pop(); }
    }

    #[inline]
    pub fn set(&mut self, name: String, val: HValue) {
        if let Some(frame) = self.stack.last_mut() {
            frame.insert(name, val);
        }
    }

    /// Przypisanie do istniejącej zmiennej (szuka w górę stosu)
    #[inline]
    pub fn assign(&mut self, name: &str, val: HValue) -> bool {
        for frame in self.stack.iter_mut().rev() {
            if let Some(slot) = frame.get_mut(name) {
                *slot = val;
                return true;
            }
        }
        false
    }

    /// Lookup — zaczyna od wierzchołka stosu
    #[inline]
    pub fn get(&self, name: &str) -> Option<&HValue> {
        for frame in self.stack.iter().rev() {
            if let Some(v) = frame.get(name) { return Some(v); }
        }
        None
    }

    pub fn current_frame(&self) -> EnvFrame {
        self.stack.last().cloned().unwrap_or_default()
    }
}

impl Default for Env { fn default() -> Self { Self::new() } }

// ─── Sygnały kontrolne ────────────────────────────────────────────────────────

enum Signal {
    Return(HValue),
    Break(Option<HValue>),
    Next,
    Raise(HValue),
}

// ─── Definicje klas ───────────────────────────────────────────────────────────

#[derive(Clone)]
struct ClassDef {
    fields:  Vec<Field>,
    methods: HashMap<String, (Vec<Param>, Vec<Stmt>)>,
}

// ─── Interpreter ─────────────────────────────────────────────────────────────

pub struct Interpreter {
    env:     Env,
    classes: HashMap<String, ClassDef>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env:     Env::new(),
            classes: HashMap::new(),
        }
    }

    pub fn run_module(&mut self, module: &Module) -> Result<(), RuntimeError> {
        // Faza 1: rejestruj wszystkie deklaracje (dwuprzebiegowe)
        for decl in &module.decls { self.register_decl(decl)?; }

        // Faza 2: szukaj main/glowna
        let main = self.env.get("main").cloned()
        .or_else(|| self.env.get("glowna").cloned());

        if let Some(HValue::Fn { params, body, .. }) = main {
            self.env.push();
            self.exec_body(&body)?;
            self.env.pop();
        } else {
            // Skrypt bez main — wykonaj top-level wyrażenia
            for decl in &module.decls {
                if let Decl::Function { name, .. } = decl {
                    // Pomiń definicje funkcji — już zarejestrowane
                    continue;
                }
            }
        }
        Ok(())
    }

    fn register_decl(&mut self, decl: &Decl) -> Result<(), RuntimeError> {
        match decl {
            Decl::Function { name, params, body, .. } => {
                let closure = self.env.current_frame();
                self.env.set(name.clone(), HValue::Fn {
                    name: Arc::from(name.as_str()),
                             params: params.clone(),
                             body: body.clone(),
                             closure,
                });
            }
            Decl::Class { name, fields, methods, .. } => {
                let mut method_map = HashMap::new();
                for m in methods {
                    if let Decl::Function { name: mn, params, body, .. } = m {
                        method_map.insert(mn.clone(), (params.clone(), body.clone()));
                    }
                }
                self.classes.insert(name.clone(), ClassDef {
                    fields: fields.clone(),
                                    methods: method_map,
                });
            }
            Decl::Const { name, value, .. } => {
                let v = self.eval_expr(value)?;
                self.env.set(name.clone(), v);
            }
            _ => {}
        }
        Ok(())
    }

    // ─── Ciało ───────────────────────────────────────────────────────────────

    fn exec_body(&mut self, stmts: &[Stmt]) -> Result<Option<Signal>, RuntimeError> {
        for stmt in stmts {
            if let Some(sig) = self.exec_stmt(stmt)? { return Ok(Some(sig)); }
        }
        Ok(None)
    }

    fn exec_stmt(&mut self, stmt: &Stmt) -> Result<Option<Signal>, RuntimeError> {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let v = match value {
                    Some(e) => self.eval_expr(e)?,
                    None    => HValue::Nil,
                };
                self.env.set(name.clone(), v);
            }

            Stmt::Expr(e) => { self.eval_expr(e)?; }

            Stmt::Return(val) => {
                let v = match val {
                    Some(e) => self.eval_expr(e)?,
                    None    => HValue::Nil,
                };
                return Ok(Some(Signal::Return(v)));
            }

            Stmt::Break(val) => {
                let v = match val {
                    Some(e) => Some(self.eval_expr(e)?),
                    None    => None,
                };
                return Ok(Some(Signal::Break(v)));
            }

            Stmt::Next => return Ok(Some(Signal::Next)),

            Stmt::Raise(e) => {
                let v = self.eval_expr(e)?;
                return Ok(Some(Signal::Raise(v)));
            }

            Stmt::Assign { target, value, .. } => {
                let v = self.eval_expr(value)?;
                match target.as_ref() {
                    Expr::Var(name) => {
                        if !self.env.assign(name, v.clone()) {
                            self.env.set(name.clone(), v);
                        }
                    }
                    Expr::FieldAccess { object, field, .. } => {
                        // Uproszczone - TODO: pełna mutacja pól
                    }
                    Expr::IndexAccess { object, index, .. } => {
                        // TODO: mutacja elementów listy
                    }
                    _ => {}
                }
            }

            Stmt::While { cond, body, .. } => {
                loop {
                    let cv = self.eval_expr(cond)?;
                    if !cv.is_truthy() { break; }
                    self.env.push();
                    let sig = self.exec_body(body)?;
                    self.env.pop();
                    match sig {
                        Some(Signal::Break(_)) => break,
                        Some(Signal::Return(v)) => return Ok(Some(Signal::Return(v))),
                        Some(Signal::Raise(v))  => return Ok(Some(Signal::Raise(v))),
                        _ => {}
                    }
                }
            }

            Stmt::For { var, iterable, body, .. } => {
                let iter_val = self.eval_expr(iterable)?;
                let items = self.to_iter(iter_val)?;
                for item in items {
                    self.env.push();
                    self.env.set(var.clone(), item);
                    let sig = self.exec_body(body)?;
                    self.env.pop();
                    match sig {
                        Some(Signal::Break(_)) => break,
                        Some(Signal::Next)     => continue,
                        Some(Signal::Return(v)) => return Ok(Some(Signal::Return(v))),
                        Some(Signal::Raise(v))  => return Ok(Some(Signal::Raise(v))),
                        _ => {}
                    }
                }
            }

            Stmt::Rescue { body, handlers, ensure, .. } => {
                self.env.push();
                let result = self.exec_body(body);
                self.env.pop();

                let raised = match result {
                    Err(RuntimeError::Exception(msg)) => Some(HValue::Str(Arc::from(msg.as_str()))),
                    Ok(Some(Signal::Raise(v)))        => Some(v),
                    Err(e) => return Err(e),
                    Ok(sig) => {
                        // ensure
                        if !ensure.is_empty() {
                            self.env.push();
                            self.exec_body(ensure)?;
                            self.env.pop();
                        }
                        if let Some(s) = sig { return Ok(Some(s)); }
                        None
                    }
                };

                if let Some(exc) = raised {
                    let mut handled = false;
                    for h in handlers {
                        self.env.push();
                        if let Some(b) = &h.binding {
                            self.env.set(b.clone(), exc.clone());
                        }
                        self.exec_body(&h.body)?;
                        self.env.pop();
                        handled = true;
                        break;
                    }
                    if !handled {
                        return Err(RuntimeError::Exception(exc.to_string()));
                    }
                }

                if !ensure.is_empty() {
                    self.env.push();
                    self.exec_body(ensure)?;
                    self.env.pop();
                }
            }
        }
        Ok(None)
    }

    // ─── Wyrażenia ────────────────────────────────────────────────────────────

    #[inline]
    pub fn eval_expr(&mut self, expr: &Expr) -> Result<HValue, RuntimeError> {
        match expr {
            // Literały - bez alokacji
            Expr::Int(n)   => Ok(HValue::Int(*n)),
            Expr::Float(f) => Ok(HValue::Float(*f)),
            Expr::Bool(b)  => Ok(HValue::Bool(*b)),
            Expr::Char(c)  => Ok(HValue::Char(*c)),
            Expr::Nil      => Ok(HValue::Nil),
            Expr::SelfExpr => self.env.get("self").cloned()
            .ok_or_else(|| RuntimeError::UndefinedVar("self".to_string())),

            // Str - Arc żeby unikać klonowania
            Expr::Str(s) => Ok(HValue::Str(Arc::from(s.as_str()))),

            // write
            Expr::Write { args, newline, .. } => {
                let mut out = String::with_capacity(64);
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push(' '); }
                    let v = self.eval_expr(a)?;
                    use fmt::Write as _;
                    let _ = write!(out, "{}", v);
                }
                if *newline { println!("{}", out); } else { print!("{}", out); }
                Ok(HValue::Nil)
            }

            Expr::Var(name) => {
                self.env.get(name).cloned()
                .ok_or_else(|| RuntimeError::UndefinedVar(name.clone()))
            }

            Expr::BinOp { op, lhs, rhs, .. } => {
                // Short-circuit dla && i ||
                match op {
                    BinOp::And => {
                        let l = self.eval_expr(lhs)?;
                        if !l.is_truthy() { return Ok(HValue::Bool(false)); }
                        let r = self.eval_expr(rhs)?;
                        return Ok(HValue::Bool(r.is_truthy()));
                    }
                    BinOp::Or => {
                        let l = self.eval_expr(lhs)?;
                        if l.is_truthy() { return Ok(HValue::Bool(true)); }
                        let r = self.eval_expr(rhs)?;
                        return Ok(HValue::Bool(r.is_truthy()));
                    }
                    _ => {}
                }
                let l = self.eval_expr(lhs)?;
                let r = self.eval_expr(rhs)?;
                self.eval_binop(op, l, r)
            }

            Expr::UnaryOp { op, expr, .. } => {
                let v = self.eval_expr(expr)?;
                match op {
                    UnaryOp::Neg => match v {
                        HValue::Int(n)   => Ok(HValue::Int(-n)),
                        HValue::Float(f) => Ok(HValue::Float(-f)),
                        _ => Err(RuntimeError::TypeError("- działa tylko na liczbach".to_string())),
                    },
                    UnaryOp::Not    => Ok(HValue::Bool(!v.is_truthy())),
                    UnaryOp::BitNot => match v {
                        HValue::Int(n) => Ok(HValue::Int(!n)),
                        _ => Err(RuntimeError::TypeError("~ działa tylko na Int".to_string())),
                    },
                }
            }

            Expr::If { cond, then, elsif, otherwise, .. } => {
                if self.eval_expr(cond)?.is_truthy() {
                    return self.eval_expr(then);
                }
                for (ec, eb) in elsif {
                    if self.eval_expr(ec)?.is_truthy() {
                        return self.eval_expr(eb);
                    }
                }
                match otherwise {
                    Some(e) => self.eval_expr(e),
                    None    => Ok(HValue::Nil),
                }
            }

            Expr::Block(stmts) => {
                self.env.push();
                let mut result = HValue::Nil;
                let last = stmts.len().saturating_sub(1);
                for (i, stmt) in stmts.iter().enumerate() {
                    if i == last {
                        if let Stmt::Expr(e) = stmt {
                            result = self.eval_expr(e)?;
                        } else {
                            self.exec_stmt(stmt)?;
                        }
                    } else {
                        self.exec_stmt(stmt)?;
                    }
                }
                self.env.pop();
                Ok(result)
            }

            Expr::Call { callee, args, .. } => {
                let func = self.eval_expr(callee)?;
                let mut vals = Vec::with_capacity(args.len());
                for a in args { vals.push(self.eval_expr(a)?); }
                self.call_value(func, vals)
            }

            Expr::MethodCall { object, method, args, .. } => {
                let obj = self.eval_expr(object)?;
                let mut vals = Vec::with_capacity(args.len());
                for a in args { vals.push(self.eval_expr(a)?); }
                self.call_method(obj, method, vals)
            }

            Expr::FieldAccess { object, field, .. } => {
                match self.eval_expr(object)? {
                    HValue::Object { fields, .. } => {
                        fields.get(field).cloned()
                        .ok_or_else(|| RuntimeError::UndefinedVar(field.clone()))
                    }
                    _ => Err(RuntimeError::TypeError(format!("Nie można uzyskać pola `{}`", field))),
                }
            }

            Expr::IndexAccess { object, index, .. } => {
                let obj = self.eval_expr(object)?;
                let idx = self.eval_expr(index)?;
                match (obj, idx) {
                    (HValue::List(v), HValue::Int(i)) => {
                        let i = if i < 0 { v.len() as i64 + i } else { i } as usize;
                        v.get(i).cloned().ok_or(RuntimeError::IndexOutOfBounds(i))
                    }
                    (HValue::Str(s), HValue::Int(i)) => {
                        let i = if i < 0 { s.len() as i64 + i } else { i } as usize;
                        s.chars().nth(i).map(HValue::Char)
                        .ok_or(RuntimeError::IndexOutOfBounds(i))
                    }
                    (HValue::Map(m), key) => {
                        let ks = key.to_string();
                        m.iter().find(|(k, _)| k.to_string() == ks)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| RuntimeError::Other(format!("Klucz `{}` nie istnieje", ks)))
                    }
                    _ => Err(RuntimeError::TypeError("Indeksowanie działa na List i Map".to_string())),
                }
            }

            Expr::New { class, args, .. } => {
                let cdef = self.classes.get(class).cloned()
                .ok_or_else(|| RuntimeError::UndefinedVar(class.clone()))?;
                let mut fields: HashMap<String, HValue> = HashMap::with_capacity(cdef.fields.len());
                for f in &cdef.fields {
                    let v = match &f.default {
                        Some(e) => self.eval_expr(e)?,
                        None    => HValue::Nil,
                    };
                    fields.insert(f.name.clone(), v);
                }
                for (i, (name, val_expr)) in args.iter().enumerate() {
                    let v = self.eval_expr(val_expr)?;
                    if let Some(n) = name {
                        fields.insert(n.clone(), v);
                    } else if let Some(f) = cdef.fields.get(i) {
                        fields.insert(f.name.clone(), v);
                    }
                }
                Ok(HValue::Object {
                    class: Arc::from(class.as_str()),
                   fields: Arc::new(fields),
                })
            }

            Expr::List(items) => {
                let mut v = Vec::with_capacity(items.len());
                for i in items { v.push(self.eval_expr(i)?); }
                Ok(HValue::List(Arc::new(v)))
            }

            Expr::Map(pairs) => {
                let mut m = Vec::with_capacity(pairs.len());
                for (k, v) in pairs { m.push((self.eval_expr(k)?, self.eval_expr(v)?)); }
                Ok(HValue::Map(Arc::new(m)))
            }

            Expr::Match { value, arms, .. } => {
                let v = self.eval_expr(value)?;
                for arm in arms {
                    if self.match_pattern(&arm.pattern, &v) {
                        if let Some(g) = &arm.guard {
                            if !self.eval_expr(g)?.is_truthy() { continue; }
                        }
                        return self.eval_expr(&arm.body);
                    }
                }
                Ok(HValue::Nil)
            }

            Expr::Range { from, to, inclusive, .. } => {
                match (self.eval_expr(from)?, self.eval_expr(to)?) {
                    (HValue::Int(a), HValue::Int(b)) => {
                        let end = if *inclusive { b + 1 } else { b };
                        Ok(HValue::List(Arc::new((a..end).map(HValue::Int).collect())))
                    }
                    _ => Err(RuntimeError::TypeError("Range działa tylko na Int".to_string())),
                }
            }

            Expr::ArcNew(inner) => {
                let v = self.eval_expr(inner)?;
                Ok(HValue::ArcVal(Arc::new(v)))
            }

            Expr::Cast { expr, ty, .. } => {
                let v = self.eval_expr(expr)?;
                self.cast_value(v, ty)
            }

            Expr::TypeCheck { expr, ty, .. } => {
                let v = self.eval_expr(expr)?;
                let ok = match (ty, &v) {
                    (Ty::Int,   HValue::Int(_))   => true,
                    (Ty::Float, HValue::Float(_)) => true,
                    (Ty::Bool,  HValue::Bool(_))  => true,
                    (Ty::Str,   HValue::Str(_))   => true,
                    (Ty::Char,  HValue::Char(_))  => true,
                    (Ty::List(_), HValue::List(_)) => true,
                    (Ty::Named(n), HValue::Object { class, .. }) => n == class.as_ref(),
                    _ => false,
                };
                Ok(HValue::Bool(ok))
            }

            Expr::Try(e) => self.eval_expr(e),

            Expr::ArenaBlock { body, .. } => {
                self.env.push();
                self.exec_body(body)?;
                self.env.pop();
                Ok(HValue::Nil)
            }

            _ => Ok(HValue::Nil),
        }
    }

    // ─── BinOp hot path ───────────────────────────────────────────────────────

    #[inline]
    fn eval_binop(&self, op: &BinOp, l: HValue, r: HValue) -> Result<HValue, RuntimeError> {
        match op {
            BinOp::Add => match (l, r) {
                (HValue::Int(a),   HValue::Int(b))   => Ok(HValue::Int(a + b)),
                (HValue::Float(a), HValue::Float(b)) => Ok(HValue::Float(a + b)),
                (HValue::Int(a),   HValue::Float(b)) => Ok(HValue::Float(a as f64 + b)),
                (HValue::Float(a), HValue::Int(b))   => Ok(HValue::Float(a + b as f64)),
                // String concat — tworzymy nowy Arc<str>
                (HValue::Str(a), HValue::Str(b)) => {
                    let mut s = String::with_capacity(a.len() + b.len());
                    s.push_str(&a); s.push_str(&b);
                    Ok(HValue::Str(Arc::from(s.as_str())))
                }
                (HValue::Str(a), b) => {
                    let bs = b.to_string();
                    let mut s = String::with_capacity(a.len() + bs.len());
                    s.push_str(&a); s.push_str(&bs);
                    Ok(HValue::Str(Arc::from(s.as_str())))
                }
                (HValue::List(a), HValue::List(b)) => {
                    let mut v: Vec<HValue> = (*a).clone();
                    v.extend((*b).iter().cloned());
                    Ok(HValue::List(Arc::new(v)))
                }
                (l, r) => Err(RuntimeError::TypeError(
                    format!("Nie można dodać {} i {}", l.type_name(), r.type_name())
                )),
            },
            BinOp::Sub => match (l, r) {
                (HValue::Int(a),   HValue::Int(b))   => Ok(HValue::Int(a - b)),
                (HValue::Float(a), HValue::Float(b)) => Ok(HValue::Float(a - b)),
                (HValue::Int(a),   HValue::Float(b)) => Ok(HValue::Float(a as f64 - b)),
                (HValue::Float(a), HValue::Int(b))   => Ok(HValue::Float(a - b as f64)),
                (l, r) => Err(RuntimeError::TypeError(format!("- : {} i {}", l.type_name(), r.type_name()))),
            },
            BinOp::Mul => match (l, r) {
                (HValue::Int(a),   HValue::Int(b))   => Ok(HValue::Int(a * b)),
                (HValue::Float(a), HValue::Float(b)) => Ok(HValue::Float(a * b)),
                (HValue::Int(a),   HValue::Float(b)) => Ok(HValue::Float(a as f64 * b)),
                (HValue::Float(a), HValue::Int(b))   => Ok(HValue::Float(a * b as f64)),
                (HValue::Str(s),   HValue::Int(n))   => Ok(HValue::Str(Arc::from(s.repeat(n.max(0) as usize).as_str()))),
                (l, r) => Err(RuntimeError::TypeError(format!("* : {} i {}", l.type_name(), r.type_name()))),
            },
            BinOp::Div => match (l, r) {
                (HValue::Int(a),   HValue::Int(0))   => Err(RuntimeError::DivisionByZero),
                (HValue::Int(a),   HValue::Int(b))   => Ok(HValue::Int(a / b)),
                (HValue::Float(a), HValue::Float(b)) => Ok(HValue::Float(a / b)),
                (HValue::Int(a),   HValue::Float(b)) => Ok(HValue::Float(a as f64 / b)),
                (HValue::Float(a), HValue::Int(b))   => Ok(HValue::Float(a / b as f64)),
                (l, r) => Err(RuntimeError::TypeError(format!("/ : {} i {}", l.type_name(), r.type_name()))),
            },
            BinOp::Mod => match (l, r) {
                (HValue::Int(a), HValue::Int(0)) => Err(RuntimeError::DivisionByZero),
                (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a % b)),
                _ => Err(RuntimeError::TypeError("% działa tylko na Int".to_string())),
            },
            BinOp::Pow => match (l, r) {
                (HValue::Int(a),   HValue::Int(b))   => Ok(HValue::Int(a.pow(b.max(0) as u32))),
                (HValue::Float(a), HValue::Float(b)) => Ok(HValue::Float(a.powf(b))),
                (HValue::Int(a),   HValue::Float(b)) => Ok(HValue::Float((a as f64).powf(b))),
                _ => Err(RuntimeError::TypeError("** działa na Int i Float".to_string())),
            },
            BinOp::Eq    => Ok(HValue::Bool(self.vals_eq(&l, &r))),
            BinOp::NotEq => Ok(HValue::Bool(!self.vals_eq(&l, &r))),
            BinOp::Lt    => self.cmp(&l, &r).map(|c| HValue::Bool(c < 0)),
            BinOp::Gt    => self.cmp(&l, &r).map(|c| HValue::Bool(c > 0)),
            BinOp::LtEq  => self.cmp(&l, &r).map(|c| HValue::Bool(c <= 0)),
            BinOp::GtEq  => self.cmp(&l, &r).map(|c| HValue::Bool(c >= 0)),
            BinOp::And   => Ok(HValue::Bool(l.is_truthy() && r.is_truthy())),
            BinOp::Or    => Ok(HValue::Bool(l.is_truthy() || r.is_truthy())),
            BinOp::BitAnd => match (l, r) { (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a & b)), _ => Err(RuntimeError::TypeError("& tylko Int".to_string())) },
            BinOp::BitOr  => match (l, r) { (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a | b)), _ => Err(RuntimeError::TypeError("| tylko Int".to_string())) },
            BinOp::BitXor => match (l, r) { (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a ^ b)), _ => Err(RuntimeError::TypeError("^ tylko Int".to_string())) },
            BinOp::LShift => match (l, r) { (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a << b)), _ => Err(RuntimeError::TypeError("<< tylko Int".to_string())) },
            BinOp::RShift => match (l, r) { (HValue::Int(a), HValue::Int(b)) => Ok(HValue::Int(a >> b)), _ => Err(RuntimeError::TypeError(">> tylko Int".to_string())) },
            _ => Ok(HValue::Nil),
        }
    }

    #[inline]
    fn vals_eq(&self, a: &HValue, b: &HValue) -> bool {
        match (a, b) {
            (HValue::Int(x),   HValue::Int(y))   => x == y,
            (HValue::Float(x), HValue::Float(y)) => x == y,
            (HValue::Bool(x),  HValue::Bool(y))  => x == y,
            (HValue::Str(x),   HValue::Str(y))   => x == y,
            (HValue::Char(x),  HValue::Char(y))  => x == y,
            (HValue::Nil,      HValue::Nil)       => true,
            _ => false,
        }
    }

    #[inline]
    fn cmp(&self, a: &HValue, b: &HValue) -> Result<i64, RuntimeError> {
        match (a, b) {
            (HValue::Int(x),   HValue::Int(y))   => Ok(x.cmp(y) as i64),
            (HValue::Float(x), HValue::Float(y)) => Ok(x.partial_cmp(y).map(|o| o as i64).unwrap_or(0)),
            (HValue::Str(x),   HValue::Str(y))   => Ok(x.cmp(y) as i64),
            _ => Err(RuntimeError::TypeError(format!("Nie można porównać {} i {}", a.type_name(), b.type_name()))),
        }
    }

    // ─── Wywołania ────────────────────────────────────────────────────────────

    fn call_value(&mut self, func: HValue, args: Vec<HValue>) -> Result<HValue, RuntimeError> {
        match func {
            HValue::Builtin(id) => self.call_builtin(id, args),

            HValue::Fn { params, body, closure, .. } => {
                self.env.push();
                // Wczytaj closure (zmienne zewnętrzne)
                for (k, v) in closure { self.env.set(k, v); }
                // Parametry
                for (i, p) in params.iter().enumerate() {
                    self.env.set(p.name.clone(), args.get(i).cloned().unwrap_or(HValue::Nil));
                }
                let result = match self.exec_body(&body)? {
                    Some(Signal::Return(v)) => v,
                    Some(Signal::Raise(v))  => {
                        self.env.pop();
                        return Err(RuntimeError::Exception(v.to_string()));
                    }
                    _ => HValue::Nil,
                };
                self.env.pop();
                Ok(result)
            }

            _ => Err(RuntimeError::TypeError(format!("Nie można wywołać wartości typu {}", func.type_name()))),
        }
    }

    fn call_builtin(&mut self, id: BuiltinId, args: Vec<HValue>) -> Result<HValue, RuntimeError> {
        match id {
            BuiltinId::Write | BuiltinId::Writeln => {
                let out = args.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ");
                println!("{}", out);
                Ok(HValue::Nil)
            }
            BuiltinId::Read => {
                if let Some(prompt) = args.first() { print!("{}", prompt); }
                use std::io::Write as _;
                let _ = std::io::stdout().flush();
                let mut line = String::new();
                std::io::stdin().read_line(&mut line)?;
                Ok(HValue::Str(Arc::from(line.trim_end_matches('\n'))))
            }
            BuiltinId::Len => match args.first() {
                Some(HValue::List(v)) => Ok(HValue::Int(v.len() as i64)),
                Some(HValue::Str(s))  => Ok(HValue::Int(s.chars().count() as i64)),
                Some(HValue::Map(m))  => Ok(HValue::Int(m.len() as i64)),
                _ => Err(RuntimeError::TypeError("len: oczekiwano List, Str lub Map".to_string())),
            },
            BuiltinId::ToInt => match args.first() {
                Some(HValue::Int(n))   => Ok(HValue::Int(*n)),
                Some(HValue::Float(f)) => Ok(HValue::Int(*f as i64)),
                Some(HValue::Str(s))   => s.trim().parse::<i64>().map(HValue::Int)
                .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Int", s))),
                Some(HValue::Bool(b))  => Ok(HValue::Int(if *b { 1 } else { 0 })),
                _                      => Ok(HValue::Int(0)),
            },
            BuiltinId::ToFloat => match args.first() {
                Some(HValue::Float(f)) => Ok(HValue::Float(*f)),
                Some(HValue::Int(n))   => Ok(HValue::Float(*n as f64)),
                Some(HValue::Str(s))   => s.trim().parse::<f64>().map(HValue::Float)
                .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Float", s))),
                _                      => Ok(HValue::Float(0.0)),
            },
            BuiltinId::ToStr   => Ok(HValue::Str(Arc::from(args.first().map(|v| v.to_string()).unwrap_or_default().as_str()))),
            BuiltinId::ToBool  => Ok(HValue::Bool(args.first().map(|v| v.is_truthy()).unwrap_or(false))),
            BuiltinId::TypeOf  => Ok(HValue::Str(Arc::from(args.first().map(|v| v.type_name()).unwrap_or("Nil")))),
            BuiltinId::Assert  => {
                let ok = args.first().map(|v| v.is_truthy()).unwrap_or(false);
                if !ok {
                    let msg = args.get(1).map(|v| v.to_string()).unwrap_or_else(|| "Assertion failed".to_string());
                    return Err(RuntimeError::Exception(msg));
                }
                Ok(HValue::Nil)
            }
            BuiltinId::Panic => {
                let msg = args.first().map(|v| v.to_string()).unwrap_or_else(|| "panic!".to_string());
                eprintln!("PANIC: {}", msg);
                std::process::exit(1);
            }
            BuiltinId::Exit => {
                let code = match args.first() { Some(HValue::Int(n)) => *n as i32, _ => 0 };
                std::process::exit(code);
            }
            BuiltinId::Min => match (args.first(), args.get(1)) {
                (Some(HValue::Int(a)), Some(HValue::Int(b)))     => Ok(HValue::Int(*a.min(b))),
                (Some(HValue::Float(a)), Some(HValue::Float(b))) => Ok(HValue::Float(a.min(*b))),
                _ => Err(RuntimeError::TypeError("min: oczekiwano dwóch liczb".to_string())),
            },
            BuiltinId::Max => match (args.first(), args.get(1)) {
                (Some(HValue::Int(a)), Some(HValue::Int(b)))     => Ok(HValue::Int(*a.max(b))),
                (Some(HValue::Float(a)), Some(HValue::Float(b))) => Ok(HValue::Float(a.max(*b))),
                _ => Err(RuntimeError::TypeError("max: oczekiwano dwóch liczb".to_string())),
            },
            BuiltinId::Abs => match args.first() {
                Some(HValue::Int(n))   => Ok(HValue::Int(n.abs())),
                Some(HValue::Float(f)) => Ok(HValue::Float(f.abs())),
                _ => Err(RuntimeError::TypeError("abs: oczekiwano liczby".to_string())),
            },
            BuiltinId::Rand => {
                let max = match args.first() { Some(HValue::Int(n)) => *n, _ => 100 };
                let seed = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH).unwrap_or_default()
                .subsec_nanos() as i64;
                Ok(HValue::Int(seed.abs() % max.max(1)))
            }
            BuiltinId::Sleep => {
                let ms = match args.first() { Some(HValue::Int(n)) => *n as u64, _ => 0 };
                std::thread::sleep(std::time::Duration::from_millis(ms));
                Ok(HValue::Nil)
            }
            _ => Ok(HValue::Nil),
        }
    }

    fn call_method(&mut self, obj: HValue, method: &str, args: Vec<HValue>) -> Result<HValue, RuntimeError> {
        match &obj {
            HValue::Str(s) => {
                let s = s.clone();
                match method {
                    "len"         => Ok(HValue::Int(s.chars().count() as i64)),
                    "upper"       => Ok(HValue::Str(Arc::from(s.to_uppercase().as_str()))),
                    "lower"       => Ok(HValue::Str(Arc::from(s.to_lowercase().as_str()))),
                    "trim"        => Ok(HValue::Str(Arc::from(s.trim()))),
                    "trim_start"  => Ok(HValue::Str(Arc::from(s.trim_start()))),
                    "trim_end"    => Ok(HValue::Str(Arc::from(s.trim_end()))),
                    "is_empty"    => Ok(HValue::Bool(s.is_empty())),
                    "to_int"      => s.trim().parse::<i64>().map(HValue::Int)
                    .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Int", s))),
                    "to_float"    => s.trim().parse::<f64>().map(HValue::Float)
                    .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Float", s))),
                    "to_str"      => Ok(obj.clone()),
                    "chars"       => Ok(HValue::List(Arc::new(s.chars().map(HValue::Char).collect()))),
                    "bytes"       => Ok(HValue::List(Arc::new(s.bytes().map(|b| HValue::Int(b as i64)).collect()))),
                    "split"       => {
                        let sep = args.first().and_then(|v| if let HValue::Str(s) = v { Some(s.clone()) } else { None });
                        let result = match sep {
                            Some(ref sep_s) => s.split(sep_s.as_ref()).map(|p| HValue::Str(Arc::from(p))).collect(),
                            None            => s.split_whitespace().map(|p| HValue::Str(Arc::from(p))).collect(),
                        };
                        Ok(HValue::List(Arc::new(result)))
                    }
                    "contains"    => {
                        let pat = args.first().and_then(|v| if let HValue::Str(p) = v { Some(p.clone()) } else { None }).unwrap_or_default();
                        Ok(HValue::Bool(s.contains(pat.as_ref())))
                    }
                    "starts_with" => {
                        let pat = args.first().and_then(|v| if let HValue::Str(p) = v { Some(p.clone()) } else { None }).unwrap_or_default();
                        Ok(HValue::Bool(s.starts_with(pat.as_ref())))
                    }
                    "ends_with"   => {
                        let pat = args.first().and_then(|v| if let HValue::Str(p) = v { Some(p.clone()) } else { None }).unwrap_or_default();
                        Ok(HValue::Bool(s.ends_with(pat.as_ref())))
                    }
                    "replace"     => {
                        let from = args.first().and_then(|v| if let HValue::Str(p) = v { Some(p.clone()) } else { None }).unwrap_or_default();
                        let to   = args.get(1).and_then(|v| if let HValue::Str(p) = v { Some(p.clone()) } else { None }).unwrap_or_default();
                        Ok(HValue::Str(Arc::from(s.replace(from.as_ref(), to.as_ref()).as_str())))
                    }
                    "repeat"      => {
                        let n = args.first().and_then(|v| if let HValue::Int(n) = v { Some(*n) } else { None }).unwrap_or(1);
                        Ok(HValue::Str(Arc::from(s.repeat(n.max(0) as usize).as_str())))
                    }
                    _ => Err(RuntimeError::UndefinedFn(format!("Str.{}", method))),
                }
            }

            HValue::Int(n) => {
                let n = *n;
                match method {
                    "to_str"   => Ok(HValue::Str(Arc::from(n.to_string().as_str()))),
                    "to_float" => Ok(HValue::Float(n as f64)),
                    "abs"      => Ok(HValue::Int(n.abs())),
                    "pow"      => {
                        let exp = args.first().and_then(|v| if let HValue::Int(e) = v { Some(*e) } else { None }).unwrap_or(1);
                        Ok(HValue::Int(n.pow(exp.max(0) as u32)))
                    }
                    _ => Err(RuntimeError::UndefinedFn(format!("Int.{}", method))),
                }
            }

            HValue::Float(f) => {
                let f = *f;
                match method {
                    "to_str"   => Ok(HValue::Str(Arc::from(f.to_string().as_str()))),
                    "to_int"   => Ok(HValue::Int(f as i64)),
                    "floor"    => Ok(HValue::Float(f.floor())),
                    "ceil"     => Ok(HValue::Float(f.ceil())),
                    "round"    => Ok(HValue::Float(f.round())),
                    "abs"      => Ok(HValue::Float(f.abs())),
                    "sqrt"     => Ok(HValue::Float(f.sqrt())),
                    "sin"      => Ok(HValue::Float(f.sin())),
                    "cos"      => Ok(HValue::Float(f.cos())),
                    "ln"       => Ok(HValue::Float(f.ln())),
                    "log2"     => Ok(HValue::Float(f.log2())),
                    _ => Err(RuntimeError::UndefinedFn(format!("Float.{}", method))),
                }
            }

            HValue::List(v) => {
                let v = v.clone();
                match method {
                    "len"      => Ok(HValue::Int(v.len() as i64)),
                    "first"    => Ok(v.first().cloned().unwrap_or(HValue::Nil)),
                    "last"     => Ok(v.last().cloned().unwrap_or(HValue::Nil)),
                    "is_empty" => Ok(HValue::Bool(v.is_empty())),
                    "reverse"  => { let mut v2 = (*v).clone(); v2.reverse(); Ok(HValue::List(Arc::new(v2))) }
                    "sort"     => {
                        let mut v2 = (*v).clone();
                        v2.sort_by(|a, b| match (a, b) {
                            (HValue::Int(x), HValue::Int(y))     => x.cmp(y),
                                   (HValue::Float(x), HValue::Float(y)) => x.partial_cmp(y).unwrap_or(std::cmp::Ordering::Equal),
                                   (HValue::Str(x), HValue::Str(y))     => x.cmp(y),
                                   _ => std::cmp::Ordering::Equal,
                        });
                        Ok(HValue::List(Arc::new(v2)))
                    }
                    "join"     => {
                        let sep = args.first().and_then(|v| if let HValue::Str(s) = v { Some(s.as_ref()) } else { None }).unwrap_or("");
                        Ok(HValue::Str(Arc::from(v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(sep).as_str())))
                    }
                    "contains" => {
                        let target = args.first().cloned().unwrap_or(HValue::Nil);
                        Ok(HValue::Bool(v.iter().any(|item| self.vals_eq(item, &target))))
                    }
                    "push"     => {
                        let val = args.first().cloned().unwrap_or(HValue::Nil);
                        let mut v2 = (*v).clone(); v2.push(val);
                        Ok(HValue::List(Arc::new(v2)))
                    }
                    "pop"      => {
                        if v.is_empty() { return Ok(HValue::Nil); }
                        let last = v.last().cloned().unwrap_or(HValue::Nil);
                        Ok(last)
                    }
                    "slice"    => {
                        let from = args.first().and_then(|v| if let HValue::Int(n) = v { Some(*n as usize) } else { None }).unwrap_or(0);
                        let to   = args.get(1).and_then(|v| if let HValue::Int(n) = v { Some(*n as usize) } else { None }).unwrap_or(v.len());
                        Ok(HValue::List(Arc::new(v.get(from..to.min(v.len())).unwrap_or(&[]).to_vec())))
                    }
                    _ => Err(RuntimeError::UndefinedFn(format!("List.{}", method))),
                }
            }

            HValue::Object { class, fields } => {
                let class = class.clone();
                let fields = fields.clone();

                if let Some(cdef) = self.classes.get(class.as_ref()).cloned() {
                    if let Some((params, body)) = cdef.methods.get(method).cloned() {
                        self.env.push();
                        self.env.set("self".to_string(), HValue::Object {
                            class: class.clone(),
                                     fields: fields.clone(),
                        });
                        for (i, p) in params.iter().enumerate() {
                            self.env.set(p.name.clone(), args.get(i).cloned().unwrap_or(HValue::Nil));
                        }
                        let result = match self.exec_body(&body)? {
                            Some(Signal::Return(v)) => v,
                            _ => HValue::Nil,
                        };
                        self.env.pop();
                        return Ok(result);
                    }
                }
                Err(RuntimeError::UndefinedFn(format!("{}.{}", class, method)))
            }

            _ => Err(RuntimeError::TypeError(format!("Typ {} nie ma metody `{}`", obj.type_name(), method))),
        }
    }

    fn cast_value(&self, v: HValue, ty: &Ty) -> Result<HValue, RuntimeError> {
        match ty {
            Ty::Int => match v {
                HValue::Float(f) => Ok(HValue::Int(f as i64)),
                HValue::Str(s)   => s.trim().parse::<i64>().map(HValue::Int)
                .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Int", s))),
                HValue::Bool(b)  => Ok(HValue::Int(if b { 1 } else { 0 })),
                other => Ok(other),
            },
            Ty::Float => match v {
                HValue::Int(n)  => Ok(HValue::Float(n as f64)),
                HValue::Str(s)  => s.trim().parse::<f64>().map(HValue::Float)
                .map_err(|_| RuntimeError::TypeError(format!("Nie można zamienić '{}' na Float", s))),
                other => Ok(other),
            },
            Ty::Str  => Ok(HValue::Str(Arc::from(v.to_string().as_str()))),
            Ty::Bool => Ok(HValue::Bool(v.is_truthy())),
            _ => Ok(v),
        }
    }

    fn to_iter(&self, val: HValue) -> Result<Vec<HValue>, RuntimeError> {
        match val {
            HValue::List(v)  => Ok((*v).clone()),
            HValue::Str(s)   => Ok(s.chars().map(HValue::Char).collect()),
            HValue::Int(n)   => Ok((0..n).map(HValue::Int).collect()),
            HValue::ArcVal(v) => self.to_iter((*v).clone()),
            _ => Err(RuntimeError::TypeError(format!("Nie można iterować po {}", val.type_name()))),
        }
    }

    fn match_pattern(&self, pat: &Pattern, val: &HValue) -> bool {
        match (pat, val) {
            (Pattern::Wildcard,  _)                 => true,
            (Pattern::Nil,       HValue::Nil)       => true,
            (Pattern::Bool(pb),  HValue::Bool(vb))  => pb == vb,
            (Pattern::Int(pi),   HValue::Int(vi))   => pi == vi,
            (Pattern::Float(pf), HValue::Float(vf)) => (pf - vf).abs() < f64::EPSILON,
            (Pattern::Str(ps),   HValue::Str(vs))   => ps.as_str() == vs.as_ref(),
            (Pattern::Var(_),    _)                 => true,
            (Pattern::Or(pats),  v)                 => pats.iter().any(|p| self.match_pattern(p, v)),
            (Pattern::List(pats), HValue::List(vals)) => {
                pats.len() == vals.len() &&
                pats.iter().zip(vals.iter()).all(|(p, v)| self.match_pattern(p, v))
            }
            _ => false,
        }
    }
}

impl Default for Interpreter { fn default() -> Self { Self::new() } }

// ─── Publiczne API ────────────────────────────────────────────────────────────

pub fn run_script(source: &str, file_name: &str) -> Result<(), RuntimeError> {
    let module = hsharp_parser::parse(source, file_name)
    .map_err(|e| RuntimeError::Other(e))?;
    let mut interp = Interpreter::new();
    interp.run_module(&module)
}

pub fn run_file(path: &std::path::Path) -> Result<(), RuntimeError> {
    let source = std::fs::read_to_string(path)?;
    let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("script");
    run_script(&source, name)
}
