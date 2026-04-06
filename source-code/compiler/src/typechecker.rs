use hsharp_parser::ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("undefined variable `{0}`")]
    UndefinedVar(String),
    #[error("type mismatch: expected `{expected}`, found `{found}`")]
    TypeMismatch { expected: String, found: String },
    #[error("undefined function `{0}`")]
    UndefinedFn(String),
    #[error("undefined type `{0}`")]
    UndefinedType(String),
    #[error("wrong number of arguments to `{name}`: expected {expected}, found {found}")]
    ArgCount { name: String, expected: usize, found: usize },
    #[error("cannot assign to immutable variable `{0}`")]
    ImmutableAssign(String),
    #[error("return type mismatch in `{fn_name}`: expected `{expected}`, found `{found}`")]
    ReturnMismatch { fn_name: String, expected: String, found: String },
}

#[derive(Debug, Clone, PartialEq)]
pub enum HType {
    Int, Uint,
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    F32, F64,
    Bool,
    Str,
    Bytes,
    Void,
    Any,
    Optional(Box<HType>),
    Array(Box<HType>),
    Tuple(Vec<HType>),
    Named(String),
    Fn(Vec<HType>, Box<HType>),
    Ref(Box<HType>),
    RefMut(Box<HType>),
}

impl HType {
    pub fn from_type_expr(te: &TypeExpr) -> Self {
        match te {
            TypeExpr::Named(n) => match n.as_str() {
                "int" => HType::Int,
                "uint" => HType::Uint,
                "i8" => HType::I8, "i16" => HType::I16,
                "i32" => HType::I32, "i64" => HType::I64,
                "i128" => HType::I128,
                "u8" => HType::U8, "u16" => HType::U16,
                "u32" => HType::U32, "u64" => HType::U64,
                "u128" => HType::U128,
                "f32" => HType::F32, "f64" => HType::F64,
                "bool" => HType::Bool,
                "string" => HType::Str,
                "bytes" => HType::Bytes,
                "any" => HType::Any,
                _ => HType::Named(n.clone()),
            },
            TypeExpr::Void => HType::Void,
            TypeExpr::Optional(inner) => HType::Optional(Box::new(Self::from_type_expr(inner))),
            TypeExpr::Array(inner) => HType::Array(Box::new(Self::from_type_expr(inner))),
            TypeExpr::Tuple(ts) => HType::Tuple(ts.iter().map(Self::from_type_expr).collect()),
            TypeExpr::Ref(inner) => HType::Ref(Box::new(Self::from_type_expr(inner))),
            TypeExpr::RefMut(inner) => HType::RefMut(Box::new(Self::from_type_expr(inner))),
            TypeExpr::Fn(params, ret) => HType::Fn(
                params.iter().map(Self::from_type_expr).collect(),
                Box::new(Self::from_type_expr(ret)),
            ),
            TypeExpr::Generic(name, _args) => HType::Named(name.clone()),
            TypeExpr::Slice(inner, _) => HType::Array(Box::new(Self::from_type_expr(inner))),
            // Explicit numeric type aliases added to AST
            TypeExpr::I8          => HType::I8,
            TypeExpr::I16         => HType::I16,
            TypeExpr::I32         => HType::I32,
            TypeExpr::I64         => HType::I64,
            TypeExpr::I128        => HType::I128,
            TypeExpr::U8          => HType::U8,
            TypeExpr::U16         => HType::U16,
            TypeExpr::U32         => HType::U32,
            TypeExpr::U64         => HType::U64,
            TypeExpr::U128        => HType::U128,
            TypeExpr::F32         => HType::F32,
            TypeExpr::F64         => HType::F64,
            TypeExpr::Bool        => HType::Bool,
            TypeExpr::String      => HType::Str,
            TypeExpr::Bytes       => HType::Bytes,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self,
            HType::Int | HType::Uint |
            HType::I8 | HType::I16 | HType::I32 | HType::I64 | HType::I128 |
            HType::U8 | HType::U16 | HType::U32 | HType::U64 | HType::U128 |
            HType::F32 | HType::F64)
    }

    pub fn compatible_with(&self, other: &HType) -> bool {
        if self == other { return true; }
        if matches!(self, HType::Any) || matches!(other, HType::Any) { return true; }
        if self.is_numeric() && other.is_numeric() { return true; }
        false
    }

    pub fn display(&self) -> String {
        match self {
            HType::Int => "int".into(),
            HType::Uint => "uint".into(),
            HType::I8 => "i8".into(), HType::I16 => "i16".into(),
            HType::I32 => "i32".into(), HType::I64 => "i64".into(),
            HType::I128 => "i128".into(),
            HType::U8 => "u8".into(), HType::U16 => "u16".into(),
            HType::U32 => "u32".into(), HType::U64 => "u64".into(),
            HType::U128 => "u128".into(),
            HType::F32 => "f32".into(), HType::F64 => "f64".into(),
            HType::Bool => "bool".into(),
            HType::Str => "string".into(),
            HType::Bytes => "bytes".into(),
            HType::Void => "void".into(),
            HType::Any => "any".into(),
            HType::Optional(inner) => format!("{}?", inner.display()),
            HType::Array(inner) => format!("[{}]", inner.display()),
            HType::Tuple(ts) => format!("({})", ts.iter().map(|t| t.display()).collect::<Vec<_>>().join(", ")),
            HType::Named(n) => n.clone(),
            HType::Fn(params, ret) => format!("fn({}) -> {}", params.iter().map(|t| t.display()).collect::<Vec<_>>().join(", "), ret.display()),
            HType::Ref(inner) => format!("&{}", inner.display()),
            HType::RefMut(inner) => format!("&mut {}", inner.display()),
        }
    }
}

#[derive(Debug, Clone)]
struct VarInfo {
    ty: HType,
    mutable: bool,
}

#[derive(Debug, Clone)]
struct FnSig {
    params: Vec<HType>,
    return_type: HType,
}

pub struct TypeChecker {
    scopes: Vec<HashMap<String, VarInfo>>,
    fns: HashMap<String, FnSig>,
    structs: HashMap<String, Vec<(String, HType)>>,
    current_fn_return: Option<HType>,
    errors: Vec<TypeError>,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut tc = Self {
            scopes: vec![HashMap::new()],
            fns: HashMap::new(),
            structs: HashMap::new(),
            current_fn_return: None,
            errors: Vec::new(),
        };
        tc.register_builtins();
        tc
    }

    fn register_builtins(&mut self) {
        // std builtins
        self.fns.insert("print".into(), FnSig {
            params: vec![HType::Any],
            return_type: HType::Void,
        });
        self.fns.insert("println".into(), FnSig {
            params: vec![HType::Any],
            return_type: HType::Void,
        });
        self.fns.insert("input".into(), FnSig {
            params: vec![HType::Str],
            return_type: HType::Str,
        });
        self.fns.insert("len".into(), FnSig {
            params: vec![HType::Any],
            return_type: HType::Int,
        });
        self.fns.insert("exit".into(), FnSig {
            params: vec![HType::Int],
            return_type: HType::Void,
        });
        self.fns.insert("panic".into(), FnSig {
            params: vec![HType::Str],
            return_type: HType::Void,
        });
        self.fns.insert("assert".into(), FnSig {
            params: vec![HType::Bool, HType::Str],
            return_type: HType::Void,
        });
        self.fns.insert("to_string".into(), FnSig {
            params: vec![HType::Any],
            return_type: HType::Str,
        });
        self.fns.insert("parse_int".into(), FnSig {
            params: vec![HType::Str],
            return_type: HType::Optional(Box::new(HType::Int)),
        });
    }

    pub fn check_module(&mut self, module: &Module) -> Result<(), TypeError> {
        // First pass: collect fn signatures
        for item in &module.items {
            self.collect_signatures(item);
        }
        // Second pass: check bodies
        for item in &module.items {
            self.check_item(item);
        }
        if let Some(e) = self.errors.first() {
            return Err(e.clone());
        }
        Ok(())
    }

    fn collect_signatures(&mut self, item: &Item) {
        match item {
            Item::FnDef(f) => {
                let params = f.params.iter().map(|p| HType::from_type_expr(&p.ty)).collect();
                let ret = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
                self.fns.insert(f.name.clone(), FnSig { params, return_type: ret });
            }
            Item::StructDef(s) => {
                let fields = s.fields.iter()
                    .map(|f| (f.name.clone(), HType::from_type_expr(&f.ty)))
                    .collect();
                self.structs.insert(s.name.clone(), fields);
            }
            _ => {}
        }
    }

    fn check_item(&mut self, item: &Item) {
        match item {
            Item::FnDef(f) => self.check_fn(f),
            Item::ImplBlock(impl_) => {
                for method in &impl_.methods {
                    self.check_fn(method);
                }
            }
            _ => {}
        }
    }

    fn check_fn(&mut self, f: &FnDef) {
        self.push_scope();
        let ret_ty = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
        self.current_fn_return = Some(ret_ty.clone());

        for param in &f.params {
            let ty = HType::from_type_expr(&param.ty);
            self.define(&param.name, ty, param.mutable);
        }

        for stmt in &f.body {
            self.check_stmt(stmt, &f.name);
        }

        self.pop_scope();
        self.current_fn_return = None;
    }

    fn check_stmt(&mut self, stmt: &Stmt, fn_name: &str) {
        match stmt {
            Stmt::Let { name, ty, mutable, value, .. } => {
                let inferred = value.as_ref().map(|e| self.infer_expr(e));
                let declared = ty.as_ref().map(HType::from_type_expr);
                let final_ty = declared.or(inferred).unwrap_or(HType::Any);
                self.define(name, final_ty, *mutable);
            }
            Stmt::Return(expr, _) => {
                if let Some(ret_ty) = &self.current_fn_return.clone() {
                    let expr_ty = expr.as_ref().map(|e| self.infer_expr(e)).unwrap_or(HType::Void);
                    if !expr_ty.compatible_with(ret_ty) {
                        self.errors.push(TypeError::ReturnMismatch {
                            fn_name: fn_name.to_string(),
                            expected: ret_ty.display(),
                            found: expr_ty.display(),
                        });
                    }
                }
            }
            Stmt::Expr(e, _) => { self.infer_expr(e); }
            Stmt::Item(item) => self.check_item(item),
            _ => {}
        }
    }

    fn infer_expr(&mut self, expr: &Expr) -> HType {
        match expr {
            Expr::Literal(lit, _) => match lit {
                Literal::Int(_) => HType::Int,
                Literal::Float(_) => HType::F64,
                Literal::String(_) => HType::Str,
                Literal::Bool(_) => HType::Bool,
                Literal::Nil => HType::Optional(Box::new(HType::Any)),
                Literal::Bytes(_) => HType::Bytes,
            },
            Expr::Ident(name, _) => {
                if let Some(v) = self.lookup(name) {
                    v.ty.clone()
                } else {
                    self.errors.push(TypeError::UndefinedVar(name.clone()));
                    HType::Any
                }
            }
            Expr::BinOp(lhs, op, rhs, _) => {
                let lt = self.infer_expr(lhs);
                let rt = self.infer_expr(rhs);
                match op {
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt |
                    BinOp::LtEq | BinOp::GtEq | BinOp::And | BinOp::Or => HType::Bool,
                    _ => if lt.is_numeric() && rt.is_numeric() { lt } else { HType::Any },
                }
            }
            Expr::UnOp(op, inner, _) => {
                let ty = self.infer_expr(inner);
                match op {
                    UnOp::Not => HType::Bool,
                    UnOp::Neg => ty,
                    UnOp::Ref => HType::Ref(Box::new(ty)),
                    UnOp::RefMut => HType::RefMut(Box::new(ty)),
                    _ => ty,
                }
            }
            Expr::Call(callee, args, _) => {
                if let Expr::Ident(name, _) = callee.as_ref() {
                    if let Some(sig) = self.fns.get(name).cloned() {
                        return sig.return_type.clone();
                    }
                    // unknown function — warning but not hard error
                    HType::Any
                } else {
                    HType::Any
                }
            }
            Expr::MethodCall(_, _, _, _) => HType::Any,
            Expr::FieldAccess(_, _, _) => HType::Any,
            Expr::IndexAccess(arr, _, _) => {
                if let HType::Array(inner) = self.infer_expr(arr) {
                    *inner
                } else {
                    HType::Any
                }
            }
            Expr::ArrayLit(elems, _) => {
                let inner = elems.first().map(|e| self.infer_expr(e)).unwrap_or(HType::Any);
                HType::Array(Box::new(inner))
            }
            Expr::TupleLit(elems, _) => {
                HType::Tuple(elems.iter().map(|e| self.infer_expr(e)).collect())
            }
            Expr::If { then_body, .. } => {
                // Return type of last statement in then body
                then_body.last().map(|s| match s {
                    Stmt::Expr(e, _) => self.infer_expr(e),
                    _ => HType::Void,
                }).unwrap_or(HType::Void)
            }
            Expr::Cast(_, ty, _) => HType::from_type_expr(ty),
            Expr::Return(_, _) => HType::Void,
            Expr::SelfExpr(_) => HType::Named("Self".into()),
            Expr::Try(inner, _) => {
                let ty = self.infer_expr(inner);
                if let HType::Optional(inner) = ty { *inner } else { ty }
            }
            _ => HType::Any,
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, name: &str, ty: HType, mutable: bool) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), VarInfo { ty, mutable });
        }
    }

    fn lookup(&self, name: &str) -> Option<&VarInfo> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v);
            }
        }
        None
    }
}
