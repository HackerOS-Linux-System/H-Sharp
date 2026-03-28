use hsharp_parser::ast::*;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug, Clone)]
pub enum TypeError {
    #[error("Niezdefiniowana zmienna: `{name}` w linii {line}")]
    UndefinedVar { name: String, line: u32 },

    #[error("Niezdefiniowana funkcja: `{name}`")]
    UndefinedFn { name: String },

    #[error("Niezdefiniowana klasa: `{name}`")]
    UndefinedClass { name: String },

    #[error("Niezgodność typów: oczekiwano `{expected}`, znaleziono `{found}`")]
    TypeMismatch { expected: String, found: String },

    #[error("Zła liczba argumentów: oczekiwano {expected}, znaleziono {found}")]
    ArgCount { expected: usize, found: usize },

    #[error("Duplikat definicji: `{name}`")]
    Duplicate { name: String },

    #[error("Powrót poza funkcją")]
    ReturnOutsideFn,

    #[error("Break poza pętlą")]
    BreakOutsideLoop,

    #[error("Błąd: {0}")]
    Other(String),
}

/// Wpis w tablicy symboli
#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable { ty: Ty, mutable: bool },
    Function { params: Vec<Ty>, return_ty: Ty },
    Class { fields: Vec<(String, Ty)>, methods: Vec<String> },
    Enum { variants: Vec<String> },
    Trait { methods: Vec<String> },
    Const { ty: Ty },
    TypeAlias { ty: Ty },
    Import { source: ImportSource, name: String },
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub span: Span,
}

/// Zakres (scope) dla zmiennych lokalnych
#[derive(Debug, Default)]
pub struct Scope {
    symbols: HashMap<String, Symbol>,
    parent: Option<Box<Scope>>,
}

impl Scope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_parent(parent: Scope) -> Self {
        Self {
            symbols: HashMap::new(),
            parent: Some(Box::new(parent)),
        }
    }

    pub fn define(&mut self, name: String, symbol: Symbol) {
        self.symbols.insert(name, symbol);
    }

    pub fn lookup(&self, name: &str) -> Option<&Symbol> {
        if let Some(sym) = self.symbols.get(name) {
            return Some(sym);
        }
        self.parent.as_ref().and_then(|p| p.lookup(name))
    }

    pub fn lookup_mut(&mut self, name: &str) -> Option<&mut Symbol> {
        if self.symbols.contains_key(name) {
            return self.symbols.get_mut(name);
        }
        self.parent.as_mut().and_then(|p| p.lookup_mut(name))
    }
}

/// Główny type checker
pub struct TypeChecker {
    pub global_scope: Scope,
    pub errors: Vec<TypeError>,
    in_function: Option<Ty>, // Aktualny typ powrotu
    in_loop: bool,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut global = Scope::new();
        // Wbudowane typy / funkcje
        Self::register_builtins(&mut global);
        Self {
            global_scope: global,
            errors: Vec::new(),
            in_function: None,
            in_loop: false,
        }
    }

    fn register_builtins(scope: &mut Scope) {
        // write(args...) -> Void
        scope.define("write".to_string(), Symbol {
            name: "write".to_string(),
                     kind: SymbolKind::Function {
                         params: vec![Ty::Str],
                         return_ty: Ty::Void,
                     },
                     span: Span::dummy(),
        });

        // Wbudowane konwersje
        for (name, from, to) in &[
            ("to_int", Ty::Str, Ty::Int),
            ("to_float", Ty::Str, Ty::Float),
            ("to_str", Ty::Int, Ty::Str),
            ("to_bool", Ty::Int, Ty::Bool),
        ] {
            scope.define(name.to_string(), Symbol {
                name: name.to_string(),
                         kind: SymbolKind::Function {
                             params: vec![from.clone()],
                         return_ty: to.clone(),
                         },
                         span: Span::dummy(),
            });
        }
    }

    pub fn check_module(&mut self, module: &Module) -> bool {
        // Pierwsza runda: zarejestruj wszystkie deklaracje najwyższego poziomu
        for decl in &module.decls {
            self.register_decl(decl);
        }

        // Druga runda: sprawdź ciała
        for decl in &module.decls {
            self.check_decl(decl);
        }

        self.errors.is_empty()
    }

    fn register_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Function { name, params, return_ty, .. } => {
                let param_tys = params.iter().map(|p| p.ty.clone()).collect();
                self.global_scope.define(name.clone(), Symbol {
                    name: name.clone(),
                                         kind: SymbolKind::Function { params: param_tys, return_ty: return_ty.clone() },
                                         span: Span::dummy(),
                });
            }
            Decl::Class { name, fields, methods, .. } => {
                let field_list = fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect();
                let method_names = methods.iter().filter_map(|m| {
                    if let Decl::Function { name, .. } = m { Some(name.clone()) } else { None }
                }).collect();
                self.global_scope.define(name.clone(), Symbol {
                    name: name.clone(),
                                         kind: SymbolKind::Class { fields: field_list, methods: method_names },
                                         span: Span::dummy(),
                });
            }
            Decl::Enum { name, variants, .. } => {
                let variant_names = variants.iter().map(|v| v.name.clone()).collect();
                self.global_scope.define(name.clone(), Symbol {
                    name: name.clone(),
                                         kind: SymbolKind::Enum { variants: variant_names },
                                         span: Span::dummy(),
                });
            }
            Decl::Const { name, ty, .. } => {
                self.global_scope.define(name.clone(), Symbol {
                    name: name.clone(),
                                         kind: SymbolKind::Const { ty: ty.clone() },
                                         span: Span::dummy(),
                });
            }
            Decl::TypeAlias { name, ty, .. } => {
                self.global_scope.define(name.clone(), Symbol {
                    name: name.clone(),
                                         kind: SymbolKind::TypeAlias { ty: ty.clone() },
                                         span: Span::dummy(),
                });
            }
            Decl::Import(imp) => {
                self.global_scope.define(imp.name.clone(), Symbol {
                    name: imp.name.clone(),
                                         kind: SymbolKind::Import {
                                             source: imp.source.clone(),
                                         name: imp.name.clone(),
                                         },
                                         span: imp.span.clone(),
                });
            }
            _ => {}
        }
    }

    fn check_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Function { name, params, return_ty, body, .. } => {
                let mut scope = Scope::new();
                for p in params {
                    scope.define(p.name.clone(), Symbol {
                        name: p.name.clone(),
                                 kind: SymbolKind::Variable { ty: p.ty.clone(), mutable: p.mutable },
                                 span: p.span.clone(),
                    });
                }
                let prev = self.in_function.replace(return_ty.clone());
                self.check_body(body, &mut scope);
                self.in_function = prev;
            }
            Decl::Class { methods, .. } => {
                for method in methods {
                    self.check_decl(method);
                }
            }
            _ => {}
        }
    }

    fn check_body(&mut self, stmts: &[Stmt], scope: &mut Scope) {
        for stmt in stmts {
            self.check_stmt(stmt, scope);
        }
    }

    fn check_stmt(&mut self, stmt: &Stmt, scope: &mut Scope) {
        match stmt {
            Stmt::Let { name, ty, mutable, value, span } => {
                let inferred_ty = if let Some(val) = value {
                    self.infer_expr(val, scope)
                } else {
                    ty.clone().unwrap_or(Ty::Infer)
                };

                let actual_ty = if let Some(declared) = ty {
                    if !self.types_compatible(declared, &inferred_ty) {
                        self.errors.push(TypeError::TypeMismatch {
                            expected: format!("{}", declared),
                                         found: format!("{}", inferred_ty),
                        });
                    }
                    declared.clone()
                } else {
                    inferred_ty
                };

                scope.define(name.clone(), Symbol {
                    name: name.clone(),
                             kind: SymbolKind::Variable { ty: actual_ty, mutable: *mutable },
                             span: span.clone(),
                });
            }
            Stmt::Return(val) => {
                if self.in_function.is_none() {
                    self.errors.push(TypeError::ReturnOutsideFn);
                }
                if let Some(v) = val {
                    self.infer_expr(v, scope);
                }
            }
            Stmt::While { cond, body, .. } => {
                self.infer_expr(cond, scope);
                let mut inner = Scope::with_parent(std::mem::take(scope));
                let prev_loop = std::mem::replace(&mut self.in_loop, true);
                self.check_body(body, &mut inner);
                self.in_loop = prev_loop;
                *scope = *inner.parent.take().unwrap();
            }
            Stmt::For { var, iterable, body, span } => {
                let iter_ty = self.infer_expr(iterable, scope);
                let elem_ty = match &iter_ty {
                    Ty::List(inner) => *inner.clone(),
                    _ => Ty::Infer,
                };
                let mut inner = Scope::with_parent(std::mem::take(scope));
                inner.define(var.clone(), Symbol {
                    name: var.clone(),
                             kind: SymbolKind::Variable { ty: elem_ty, mutable: false },
                             span: span.clone(),
                });
                let prev_loop = std::mem::replace(&mut self.in_loop, true);
                self.check_body(body, &mut inner);
                self.in_loop = prev_loop;
                *scope = *inner.parent.take().unwrap();
            }
            Stmt::Break(_) => {
                if !self.in_loop {
                    self.errors.push(TypeError::BreakOutsideLoop);
                }
            }
            Stmt::Expr(e) => { self.infer_expr(e, scope); }
            Stmt::Assign { target, value, .. } => {
                let _ty_target = self.infer_expr(target, scope);
                let _ty_value = self.infer_expr(value, scope);
            }
            Stmt::Raise(e) => { self.infer_expr(e, scope); }
            Stmt::Next => {
                if !self.in_loop {
                    self.errors.push(TypeError::BreakOutsideLoop);
                }
            }
            Stmt::Rescue { body, handlers, ensure, .. } => {
                let mut inner = Scope::with_parent(std::mem::take(scope));
                self.check_body(body, &mut inner);
                for h in handlers {
                    self.check_body(&h.body, &mut inner);
                }
                self.check_body(ensure, &mut inner);
                *scope = *inner.parent.take().unwrap();
            }
        }
    }

    fn infer_expr(&mut self, expr: &Expr, scope: &mut Scope) -> Ty {
        match expr {
            Expr::Int(_) => Ty::Int,
            Expr::Float(_) => Ty::Float,
            Expr::Bool(_) => Ty::Bool,
            Expr::Str(_) => Ty::Str,
            Expr::Char(_) => Ty::Char,
            Expr::Nil => Ty::Option(Box::new(Ty::Infer)),
            Expr::SelfExpr => Ty::Named("Self".to_string()),

            Expr::Var(name) => {
                if let Some(sym) = scope.lookup(name).or_else(|| self.global_scope.lookup(name)) {
                    match &sym.kind {
                        SymbolKind::Variable { ty, .. } => ty.clone(),
                        SymbolKind::Const { ty } => ty.clone(),
                        SymbolKind::Function { return_ty, .. } => return_ty.clone(),
                        _ => Ty::Infer,
                    }
                } else {
                    self.errors.push(TypeError::UndefinedVar {
                        name: name.clone(),
                                     line: 0,
                    });
                    Ty::Infer
                }
            }

            Expr::BinOp { op, lhs, rhs, .. } => {
                let lty = self.infer_expr(lhs, scope);
                let rty = self.infer_expr(rhs, scope);
                match op {
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq
                    | BinOp::And | BinOp::Or => Ty::Bool,
                    BinOp::Add if matches!(lty, Ty::Str) => Ty::Str,
                    _ => lty,
                }
            }

            Expr::UnaryOp { op, expr, .. } => {
                let ty = self.infer_expr(expr, scope);
                match op {
                    UnaryOp::Not => Ty::Bool,
                    _ => ty,
                }
            }

            Expr::Call { callee, args, .. } => {
                if let Expr::Var(name) = callee.as_ref() {
                    if let Some(sym) = self.global_scope.lookup(name).cloned() {
                        if let SymbolKind::Function { params, return_ty } = sym.kind {
                            if args.len() != params.len() {
                                self.errors.push(TypeError::ArgCount {
                                    expected: params.len(),
                                                 found: args.len(),
                                });
                            }
                            for arg in args {
                                self.infer_expr(arg, scope);
                            }
                            return return_ty;
                        }
                    }
                }
                for arg in args {
                    self.infer_expr(arg, scope);
                }
                Ty::Infer
            }

            Expr::Write { args, .. } => {
                for a in args { self.infer_expr(a, scope); }
                Ty::Void
            }

            Expr::If { cond, then, elsif, otherwise, .. } => {
                self.infer_expr(cond, scope);
                let then_ty = self.infer_expr(then, scope);
                for (ec, eb) in elsif {
                    self.infer_expr(ec, scope);
                    self.infer_expr(eb, scope);
                }
                if let Some(e) = otherwise {
                    self.infer_expr(e, scope);
                }
                then_ty
            }

            Expr::Block(stmts) => {
                let mut inner = Scope::with_parent(std::mem::take(scope));
                let mut last_ty = Ty::Void;
                for (i, s) in stmts.iter().enumerate() {
                    if i == stmts.len() - 1 {
                        if let Stmt::Expr(e) = s {
                            last_ty = self.infer_expr(e, &mut inner);
                        } else {
                            self.check_stmt(s, &mut inner);
                        }
                    } else {
                        self.check_stmt(s, &mut inner);
                    }
                }
                *scope = *inner.parent.take().unwrap();
                last_ty
            }

            Expr::List(items) => {
                let elem_ty = items.first()
                .map(|e| self.infer_expr(e, scope))
                .unwrap_or(Ty::Infer);
                for item in items.iter().skip(1) {
                    self.infer_expr(item, scope);
                }
                Ty::List(Box::new(elem_ty))
            }

            Expr::New { class, args, .. } => {
                if self.global_scope.lookup(class).is_none() {
                    self.errors.push(TypeError::UndefinedClass { name: class.clone() });
                }
                for (_, a) in args { self.infer_expr(a, scope); }
                Ty::Named(class.clone())
            }

            Expr::Cast { ty, .. } => ty.clone(),
            Expr::TypeCheck { .. } => Ty::Bool,
            Expr::Try(e) => {
                let ty = self.infer_expr(e, scope);
                match ty {
                    Ty::Result(ok, _) => *ok,
                    Ty::Option(inner) => *inner,
                    other => other,
                }
            }

            Expr::ArcNew(inner) => {
                let ty = self.infer_expr(inner, scope);
                Ty::Arc(Box::new(ty))
            }

            Expr::Match { value, arms, .. } => {
                self.infer_expr(value, scope);
                let mut result_ty = Ty::Void;
                for arm in arms {
                    result_ty = self.infer_expr(&arm.body, scope);
                }
                result_ty
            }

            Expr::ArenaBlock { body, .. } => {
                let mut inner = Scope::with_parent(std::mem::take(scope));
                self.check_body(body, &mut inner);
                *scope = *inner.parent.take().unwrap();
                Ty::Void
            }

            _ => Ty::Infer,
        }
    }

    fn types_compatible(&self, expected: &Ty, found: &Ty) -> bool {
        if matches!(expected, Ty::Infer) || matches!(found, Ty::Infer) {
            return true;
        }
        expected == found
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hsharp_parser::parse;

    #[test]
    fn test_type_check_ok() {
        let src = r#"
        fn dodaj(a: Int, b: Int) -> Int [
        return a + b
        ]
        "#;
        let module = parse(src, "test").expect("parse");
        let mut tc = TypeChecker::new();
        let ok = tc.check_module(&module);
        assert!(ok, "Błędy: {:?}", tc.errors);
    }

    #[test]
    fn test_undefined_var() {
        let src = r#"
        fn test() [
        write niezdefiniowana
        ]
        "#;
        let module = parse(src, "test").expect("parse");
        let mut tc = TypeChecker::new();
        tc.check_module(&module);
        assert!(!tc.errors.is_empty());
    }
}
