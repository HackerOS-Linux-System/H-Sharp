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
                    // then the snake_case mangled name ("json_parse") —
                    // BUG FIX: this is the spelling `modules.rs`'s
                    // `mangle_module_items` actually renames a `mod X is
                    // ... end` block's functions to (`X_fn_name`), and
                    // the one `codegen.rs`'s own call-resolution path
                    // tries (`segments.join("_")`) when compiling a
                    // `module::function(...)` call — so it's the name
                    // that's actually registered in `self.fns` for any
                    // module that isn't purely namespace-flattened. Only
                    // trying `"::"` and the bare last segment meant a
                    // real cross-module call (e.g. `util::scan_ident_end`)
                    // silently inferred as `HType::Any` here even though
                    // codegen resolved and typed it correctly — and that
                    // `Any` could then trip an otherwise-spurious "return
                    // type mismatch" for any tuple built around the
                    // result (see the matching fix in `htype.rs`'s
                    // `compatible_with`, which was the second half of the
                    // same failure mode for callers who don't have this
                    // exact fix applied to their toolchain yet).
                    // Finally fall back to just the last segment (for
                    // modules that were namespace-flattened at expansion
                    // time instead of snake_case-mangled).
                    let full = segments.join("::");
                    if let Some(sig) = self.fns.get(&full).cloned() {
                        return sig.return_type.clone();
                    }
                    let snake = segments.join("_");
                    if let Some(sig) = self.fns.get(&snake).cloned() {
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
                // [FIXED] Tuple positional access (`.0`, `.1`, ...) had no
                // arm here at all — a `HType::Tuple` base always fell
                // through the struct-field lookup below (which only knows
                // `HType::Named`) straight to the final `None => HType::Any`
                // catch-all, so `x.0`/`x.1` on ANY tuple, anywhere,
                // inferred as `Any` regardless of the tuple's actual
                // element types. That's what made every `let (a, b) =
                // some_call()` — which the parser desugars to a hidden
                // `let __destructure = some_call(); let a = __destructure.0;
                // let b = __destructure.1;` (see parser.rs's `parse_let`)
                // — silently lose both `a`'s and `b`'s real types, and made
                // an explicitly-annotated `let t: (A, B) = ...; t.0; t.1;`
                // just as broken. Handling it here, symmetrically with the
                // struct-field case, fixes both call sites at once since
                // they desugar to the exact same `FieldAccess` node.
                if let HType::Tuple(elems) = &base_ty {
                    return match field.parse::<usize>() {
                        Ok(idx) if idx < elems.len() => elems[idx].clone(),
                        _ => {
                            self.err_hint(
                                span.clone(),
                                format!("tuple of {} element(s) has no field `.{}`", elems.len(), field),
                                "tuple fields are accessed positionally as `.0`, `.1`, ... up to (len - 1)".to_string(),
                            );
                            HType::Any
                        }
                    };
                }
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
            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                self.infer_expr(condition);
                let then_val = self.check_block_value(then_body);
                for (cond, body) in elsif_branches {
                    self.infer_expr(cond);
                    self.check_block_value(body);
                }
                if let Some(else_body) = else_body {
                    self.check_block_value(else_body);
                }
                then_val
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
            Expr::SelfExpr(_)     => match &self.current_impl {
                Some(t) => HType::Named(t.clone()),
                None => HType::Named("Self".into()),
            },
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
                let mut result = HType::Any;
                for (i, arm) in arms.iter().enumerate() {
                    if let Some(g) = &arm.guard { self.infer_expr(g); }
                    let val = self.check_block_value(&arm.body);
                    if i == 0 { result = val; }
                }
                result
            }
            // `while`/`for`/`do` don't produce a value the way `if`/`match`
            // do (nothing reads "the value of a while loop"), but their
            // bodies still need every statement checked — previously these
            // fell to the catch-all `_ => HType::Any` below, meaning a
            // `return` (or a nested `if`'s `return`s) inside a loop body
            // was never checked against the enclosing function's declared
            // return type at all. `check_block_value`'s result is
            // discarded here on purpose; only the checking side effects
            // (diagnostics) matter for these three.
            Expr::While { condition, body, .. } => {
                self.infer_expr(condition);
                self.check_block_value(body);
                HType::Void
            }
            Expr::For { iterable, body, .. } => {
                self.infer_expr(iterable);
                self.check_block_value(body);
                HType::Void
            }
            Expr::Do { body, .. } => self.check_block_value(body),
            _ => HType::Any,
        }
    }

    /// Run `check_stmt` over every statement in a nested block (an
    /// `if`/`match`/`while`/`for`/`do` body), returning the last
    /// statement's value for tail-expression position — the same "value
    /// of a block = value of its last statement" rule `Expr::If`/
    /// `Expr::Match` always used, kept intact here.
    ///
    /// BUG FIX: previously `Expr::If`'s value came from peeking at
    /// `then_body.last()` directly with a tiny local match (and
    /// `Expr::Match`/`Expr::While`/`Expr::For`/`Expr::Do` didn't recurse
    /// into their bodies for checking *at all* — they fell through to the
    /// catch-all `_ => HType::Any` at the bottom of `infer_expr`). That
    /// meant `check_stmt`'s per-statement checks — most importantly the
    /// return-type-mismatch check in its `Stmt::Return` arm — only ever
    /// ran on a function's *top-level* statements (the ones `check_fn`
    /// iterates directly). A `return` nested inside an `if`, `while`,
    /// `for`, `match` arm, or `do` block was silently never checked
    /// against the function's declared return type, no matter how wrong
    /// it was. Routing every nested block through this one function
    /// (instead of ad hoc last-statement peeking) fixes that uniformly.
    pub(super) fn check_block_value(&mut self, body: &[Stmt]) -> HType {
        let mut result = HType::Void;
        for stmt in body {
            result = self.check_stmt(stmt);
        }
        result
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
