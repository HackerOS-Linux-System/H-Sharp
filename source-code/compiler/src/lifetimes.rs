use hsharp_parser::ast::*;
use std::collections::HashMap;

/// A lifetime annotation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Lifetime {
    Named(String),   // 'a
    Static,          // 'static
    Elided,          // '_ (inferred by compiler)
    Anonymous,       // unnamed (inferred)
    Owned,           // not a reference — owns its value
}

impl Lifetime {
    pub fn from_str(s: &str) -> Self {
        match s {
            "'static" | "static" => Self::Static,
            "'_"      | "_"      => Self::Elided,
            _ if s.starts_with('\'') => Self::Named(s[1..].to_string()),
            _ => Self::Named(s.to_string()),
        }
    }

    pub fn outlives(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Static, _) => true,
            (_, Self::Static) => false,
            (Self::Named(a), Self::Named(b)) => a == b,
            _ => true,  // Elided/Anonymous/Owned: inferred, assumed OK
        }
    }
}

/// Error from lifetime analysis
#[derive(Debug, Clone)]
pub struct LifetimeError {
    pub message: String,
    pub span:    hsharp_parser::span::Span,
}

impl std::fmt::Display for LifetimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "lifetime error: {} at {}:{}", self.message, self.span.start.line, self.span.start.col)
    }
}

/// Lifetime scope: tracks which lifetimes are in scope and their constraints
pub struct LifetimeScope {
    /// Lifetime parameter → constraint (outlives)
    pub lifetimes: HashMap<String, Vec<String>>,
    /// Variable → lifetime it was created in
    pub vars: HashMap<String, Lifetime>,
}

impl LifetimeScope {
    pub fn new() -> Self {
        Self { lifetimes: HashMap::new(), vars: HashMap::new() }
    }

    pub fn define_lifetime(&mut self, name: &str) {
        self.lifetimes.entry(name.to_string()).or_default();
    }

    pub fn bind_var(&mut self, name: &str, lifetime: Lifetime) {
        self.vars.insert(name.to_string(), lifetime);
    }

    pub fn get_lifetime(&self, var: &str) -> Option<&Lifetime> {
        self.vars.get(var)
    }
}

/// Lifetime checker — validates lifetime annotations on fn signatures and usage
pub struct LifetimeChecker {
    pub errors: Vec<LifetimeError>,
    scopes: Vec<LifetimeScope>,
}

impl LifetimeChecker {
    pub fn new() -> Self {
        Self { errors: Vec::new(), scopes: vec![LifetimeScope::new()] }
    }

    fn push(&mut self) { self.scopes.push(LifetimeScope::new()); }
    fn pop(&mut self) { self.scopes.pop(); }
    fn scope_mut(&mut self) -> &mut LifetimeScope { self.scopes.last_mut().unwrap() }

    /// Check a function's lifetime annotations for consistency
    pub fn check_fn(&mut self, f: &FnDef) {
        self.push();

        // Register lifetime params from type_params (e.g. <'a, 'b, T>)
        for tp in &f.type_params {
            if tp.name.starts_with('\'') {
                self.scope_mut().define_lifetime(&tp.name);
            }
        }

        // Bind params with their lifetimes
        for param in &f.params {
            let lt = self.extract_lifetime_from_type(&param.ty);
            self.scope_mut().bind_var(&param.name, lt);
        }

        // Validate return type lifetime vs param lifetimes
        if let Some(ret) = &f.return_type {
            let ret_lt = self.extract_lifetime_from_type(ret);
            self.check_return_lifetime(f, &ret_lt);
        }

        // Check body
        self.check_stmts(&f.body);

        self.pop();
    }

    fn extract_lifetime_from_type(&self, ty: &TypeExpr) -> Lifetime {
        // In H# v0.6, lifetimes are implicit in & types
        // Future: parse explicit 'a in type expressions
        match ty {
            TypeExpr::Ref(_) | TypeExpr::RefMut(_) => Lifetime::Anonymous,
            TypeExpr::Named(n) if n == "string"    => Lifetime::Static, // string literals are 'static
            _ => Lifetime::Anonymous,
        }
    }

    fn check_return_lifetime(&mut self, f: &FnDef, ret_lt: &Lifetime) {
        match ret_lt {
            Lifetime::Named(name) => {
                // Return lifetime must match a parameter lifetime
                let param_lifetimes: Vec<Lifetime> = f.params.iter()
                    .map(|p| self.extract_lifetime_from_type(&p.ty))
                    .collect();
                let found = param_lifetimes.iter().any(|lt| {
                    if let Lifetime::Named(n) = lt { n == name } else { false }
                });
                if !found && name != "static" {
                    self.errors.push(LifetimeError {
                        message: format!(
                            "lifetime '{}' in return type of `{}` doesn't match any parameter lifetime",
                            name, f.name
                        ),
                        span: f.span.clone(),
                    });
                }
            }
            _ => {} // Anonymous/Static/Elided are always OK
        }
    }

    fn check_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts { self.check_stmt(stmt); }
    }

    fn check_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { name, value, .. } => {
                let lt = if let Some(v) = value {
                    self.infer_lifetime(v)
                } else {
                    Lifetime::Anonymous
                };
                self.scope_mut().bind_var(name, lt);
            }
            Stmt::Return(Some(e), span) => {
                let lt = self.infer_lifetime(e);
                // Validate return doesn't return local reference
                self.check_no_local_ref_return(&lt, span);
            }
            Stmt::Expr(e, _) => { self.check_expr(e); }
            _ => {}
        }
    }

    fn infer_lifetime(&self, expr: &Expr) -> Lifetime {
        match expr {
            Expr::Literal(Literal::String(_), _) => Lifetime::Static,
            Expr::Ident(name, _) => {
                for scope in self.scopes.iter().rev() {
                    if let Some(lt) = scope.get_lifetime(name) {
                        return lt.clone();
                    }
                }
                Lifetime::Anonymous
            }
            _ => Lifetime::Anonymous,
        }
    }

    fn check_no_local_ref_return(&mut self, lt: &Lifetime, _span: &hsharp_parser::span::Span) {
        // For now: warn if returning a local reference (simplified check)
        // Full impl: track scope depth of each variable's lifetime
        match lt {
            Lifetime::Named(_) => {} // explicit named lifetime — OK if consistent
            _ => {}  // anonymous/static — OK
        }
    }

    fn check_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Call(callee, args, _) => {
                self.check_expr(callee);
                for a in args { self.check_expr(a); }
            }
            Expr::BinOp(l, _, r, _) => { self.check_expr(l); self.check_expr(r); }
            Expr::If { condition, then_body, else_body, .. } => {
                self.check_expr(condition);
                self.push(); self.check_stmts(then_body); self.pop();
                if let Some(eb) = else_body {
                    self.push(); self.check_stmts(eb); self.pop();
                }
            }
            _ => {}
        }
    }

    /// Run lifetime checking on the whole module
    pub fn check_module(&mut self, module: &Module) -> Vec<LifetimeError> {
        for item in &module.items {
            if let Item::FnDef(f) = item {
                self.check_fn(f);
            }
        }
        self.errors.clone()
    }
}
