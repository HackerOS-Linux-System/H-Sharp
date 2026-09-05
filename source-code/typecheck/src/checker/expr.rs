use hsharp_parser::ast::*;
use std::collections::HashMap;
use super::{TypeChecker, VarInfo};
use crate::htype::HType;
use crate::helpers::cast_allowed;

impl TypeChecker {
    /// Public wrapper around `infer_expr`, used by `monomorphize.rs` (§2)
    /// to determine call-site type arguments for generic functions. Takes
    /// `&mut self` because `infer_expr` may push diagnostics for nested
    /// sub-expressions (e.g. a generic call's arguments might themselves
    /// contain a struct-field-access error) — those diagnostics are still
    /// useful and are retained in `self.diagnostics`.
    pub fn infer_expr_pub(&mut self, expr: &Expr) -> HType {
        self.infer_expr(expr)
    }

    pub(super) fn infer_expr(&mut self, expr: &Expr) -> HType {
        match expr {
            Expr::Literal(lit, _) => match lit {
                Literal::Int(_)           => HType::Int,
                Literal::Float(_)         => HType::F64,
                Literal::String(_)        => HType::Str,
                Literal::Interpolated(_)  => HType::Str,
                Literal::Bool(_)          => HType::Bool,
                Literal::Nil              => HType::Optional(Box::new(HType::Any)),
                Literal::Bytes(_)         => HType::Bytes,
            },
            Expr::Ident(name, _) => {
                if name.starts_with("__bind:") || name.starts_with("__closure_") { return HType::Any; }
                if let Some(v) = self.lookup(name) { v.ty.clone() }
                else if let Some(t) = self.consts.get(name) { t.clone() }
                else if self.fns.contains_key(name) { HType::Any }
                else { HType::Any } // lenient — don't error on unknown idents
            }
            // BUG FIX: `infer_expr` had no arm for `Expr::StructLit` at
            // all, so `Foo { field: val, ... }` fell through to the
            // catch-all `_ => HType::Any` far below — even though a
            // struct literal's type is unambiguous, right there as its
            // own first field. Found while testing generics: this
            // starves any *other* code that calls `infer_expr`/
            // `infer_expr_pub` outside of `check_module`'s own live
            // traversal — most concretely `monomorphize.rs`, whose
            // whole job is re-inferring call-site argument types in a
            // second pass, of ever getting a real struct type back for
            // `let x = Foo { ... }`. That in turn caused every generic
            // function called with a struct-typed local variable to
            // silently monomorphize against `Any` instead of the real
            // struct — see `monomorphize.rs`'s `collect_generic_uses`
            // doc comment for the full chain and a confirmed repro
            // (`identity(some_box)` was instantiating `identity__any`,
            // not `identity__Box`).
            Expr::StructLit(name, _, _) => HType::Named(name.clone()),
            Expr::BinOp(lhs, op, rhs, _) => {
                let lt = self.infer_expr(lhs);
                let rt = self.infer_expr(rhs);
                match op {
                    BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Gt |
                    BinOp::LtEq | BinOp::GtEq | BinOp::And | BinOp::Or => HType::Bool,
                    BinOp::Add if matches!(lt, HType::Str) || matches!(rt, HType::Str) => HType::Str,
                    _ => if lt.is_numeric() && rt.is_numeric() { lt } else { HType::Any },
                }
            }
            Expr::UnOp(op, inner, _) => {
                let ty = self.infer_expr(inner);
                match op {
                    UnOp::Not    => HType::Bool,
                    UnOp::Neg    => ty,
                    UnOp::Ref    => HType::Ref(Box::new(ty)),
                    UnOp::RefMut => HType::RefMut(Box::new(ty)),
                    _            => ty,
                }
            }
            Expr::Call(callee, _args, _) => {
                if let Expr::Ident(name, _) = callee.as_ref() {
                    if let Some(sig) = self.fns.get(name).cloned() {
                        return sig.return_type.clone();
                    }
                }
                if let Expr::Path(segments, _) = callee.as_ref() {
                    // Try the fully-qualified name first ("json::parse"),
                    // then fall back to just the last segment (for modules
                    // that were namespace-flattened at expansion time).
                    let full = segments.join("::");
                    if let Some(sig) = self.fns.get(&full).cloned() {
                        return sig.return_type.clone();
                    }
                    if let Some(last) = segments.last() {
                        if let Some(sig) = self.fns.get(last).cloned() {
                            return sig.return_type.clone();
                        }
                    }
                }
                HType::Any
            }
            Expr::Path(_, _) => HType::Any,
            Expr::MethodCall(_, _, _, _) => HType::Any,
            Expr::FieldAccess(base, field, span) => {
                let base_ty = self.infer_expr(base);
                // Unwrap references — `&Foo` / `&mut Foo` field access works
                // the same as `Foo` field access.
                let named = match &base_ty {
                    HType::Named(n) => Some(n.clone()),
                    HType::Ref(inner) | HType::RefMut(inner) => {
                        if let HType::Named(n) = inner.as_ref() { Some(n.clone()) } else { None }
                    }
                    _ => None,
                };
                match named.and_then(|n| self.structs.get(&n).map(|f| (n, f.clone()))) {
                    Some((struct_name, fields)) => {
                        match fields.iter().find(|(fname, _)| fname == field) {
                            Some((_, fty)) => fty.clone(),
                            None => {
                                let available: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                                self.err_hint(
                                    span.clone(),
                                              format!("struct `{}` has no field `{}`", struct_name, field),
                                                  if available.is_empty() {
                                                      format!("`{}` has no fields", struct_name)
                                                  } else {
                                                      format!("available fields: {}", available.join(", "))
                                                  },
                                );
                                HType::Any
                            }
                        }
                    }
                    // Unknown / builtin / non-struct type — stay lenient.
                    None => HType::Any,
                }
            }
            Expr::IndexAccess(arr, _, _) => {
                if let HType::Array(inner) = self.infer_expr(arr) { *inner }
                else { HType::Any }
            }
            Expr::ArrayLit(elems, _) => {
                let inner = elems.first().map(|e| self.infer_expr(e)).unwrap_or(HType::Any);
                HType::Array(Box::new(inner))
            }
            Expr::TupleLit(elems, _) => {
                HType::Tuple(elems.iter().map(|e| self.infer_expr(e)).collect())
            }
            Expr::If { then_body, .. } => {
                then_body.last().map(|s| match s {
                    Stmt::Expr(e, _) => self.infer_expr(e),
                                     _ => HType::Void,
                }).unwrap_or(HType::Void)
            }
            Expr::Cast(inner, ty, span) => {
                let from = self.infer_expr(inner);
                let to   = HType::from_type_expr(ty);
                if !cast_allowed(&from, &to) {
                    self.err_hint(
                        span.clone(),
                                  format!("invalid cast: cannot cast `{}` as `{}`", from.display(), to.display()),
                                      "valid casts: numeric<->numeric, numeric<->bool, any<->concrete type".to_string(),
                    );
                }
                to
            }
            Expr::Return(_, _)    => HType::Void,
            Expr::SelfExpr(_)     => HType::Named("Self".into()),
            Expr::Try(inner, _)   => {
                let ty = self.infer_expr(inner);
                if let HType::Optional(i) = ty { *i } else { ty }
            }
            Expr::Assign(_, rhs, _) => self.infer_expr(rhs),
            Expr::CompoundAssign(lhs, _, _rhs, _) => self.infer_expr(lhs),
            Expr::Range(_, _, _, _) => HType::Array(Box::new(HType::Int)),
            Expr::Closure { params, return_type, body, .. } => {
                // BUG FIX: this used to return just the closure *body's*
                // inferred/declared return type (e.g. `int` for `|b: int|
                // -> int is a + b end`) — the type of what the closure
                // computes, not the type of the closure *value itself*
                // (`fn(int) -> int`). That's correct when checking the
                // body's last expression, but wrong everywhere the closure
                // literal is used as a value — most visibly `return |b|
                // -> int is ... end` from a function declared `-> fn(int)
                // -> int`, which always failed with "expected
                // fn(int)->int, found int" no matter what. A closure
                // literal's type is a function type built from its own
                // parameter types and return type, matching how `Expr::Fn`
                // /named functions are typed everywhere else in this file.
                let param_tys: Vec<HType> = params.iter().map(|p| HType::from_type_expr(&p.ty)).collect();
                let ret_ty = return_type.as_ref().map(HType::from_type_expr)
                    .or_else(|| body.last().map(|s| match s {
                        Stmt::Expr(e, _) => self.infer_expr(e),
                        _ => HType::Any,
                    }))
                    .unwrap_or(HType::Void);
                HType::Fn(param_tys, Box::new(ret_ty))
            }
            Expr::Match { subject, arms, span } => {
                let subj_ty = self.infer_expr(subject);
                self.check_match_exhaustive(&subj_ty, arms, span);
                arms.first().and_then(|arm| arm.body.last()).map(|s| match s {
                    Stmt::Expr(e, _) => self.infer_expr(e),
                                                                 _ => HType::Any,
                }).unwrap_or(HType::Any)
            }
            _ => HType::Any,
        }
    }

    pub(super) fn push_scope(&mut self) { self.scopes.push(HashMap::new()); }
    pub(super) fn pop_scope(&mut self)  { self.scopes.pop(); }

    pub(super) fn define(&mut self, name: &str, ty: HType, mutable: bool) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), VarInfo { ty, mutable });
        }
    }

    fn lookup(&self, name: &str) -> Option<&VarInfo> {
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) { return Some(v); }
        }
        None
    }
}
