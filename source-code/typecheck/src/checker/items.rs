use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use super::TypeChecker;
use crate::htype::HType;
use crate::helpers::{block_always_returns, stmt_span};

impl TypeChecker {
    pub(super) fn check_item(&mut self, item: &Item) {
        match item {
            Item::FnDef(f) => self.check_fn(f),
            Item::ImplBlock(imp) => {
                for method in &imp.methods { self.check_fn(method); }
            }
            Item::ModDecl { inline: Some(items), .. } => {
                for sub_item in items { self.check_item(sub_item); }
            }
            _ => {}
        }
    }

    fn check_fn(&mut self, f: &FnDef) {
        // Collect #[test] functions
        if f.attrs.iter().any(|a| a.name == "test") {
            self.test_fns.push(f.name.clone());
        }
        // Collect #[inline] functions
        if f.attrs.iter().any(|a| a.name == "inline" || a.name == "always_inline") {
            self.inline_fns.insert(f.name.clone());
        }
        // Collect #[must_use] functions
        if f.attrs.iter().any(|a| a.name == "must_use") {
            self.must_use_fns.insert(f.name.clone());
        }
        // Collect #[deprecated]
        if let Some(attr) = f.attrs.iter().find(|a| a.name == "deprecated") {
            let msg = attr.args.iter().find_map(|a| {
                if let AttrArg::KeyValue(k, v) = a { if k == "since" || k == "note" { return Some(v.clone()); } }
                None
            }).unwrap_or_default();
            self.deprecated_items.insert(f.name.clone(), msg);
        }

        self.push_scope();
        let ret_ty = f.return_type.as_ref().map(HType::from_type_expr).unwrap_or(HType::Void);
        self.current_fn_return = Some(ret_ty.clone());

        for param in &f.params {
            let ty = HType::from_type_expr(&param.ty);
            self.define(&param.name, ty, param.mutable);
        }

        for stmt in &f.body { self.check_stmt(stmt, &f.name); }

        // §13: `@pointers`/`@arc` builtin gating — see check_mem_mode_block.
        self.check_mem_mode_block(&f.body, f.mem_mode, false, &f.name);

        // §3: return-path reachability. If `f` declares a non-void return
        // type, every path through its body must end in a `return <expr>`
        // (or, for the common "implicit tail expression" style, the last
        // statement of the body — and of every nested if/match branch —
        // must itself be a `return`). A function that can "fall off the
        // end" without returning is a silent bug: at runtime it currently
        // returns a zero-initialized value of the declared type with no
        // warning at all.
        if !matches!(ret_ty, HType::Void) && !block_always_returns(&f.body) {
            let span = f.body.last().map(|s| stmt_span(s)).unwrap_or_else(|| f.span.clone());
            self.err_hint(
                span,
                format!("function `{}` has return type `{}` but does not return on all paths", f.name, ret_ty.display()),
                    format!("add a `return <{}>` at the end of the function, or in every branch of the final if/match", ret_ty.display()),
            );
        }

        self.pop_scope();
        self.current_fn_return = None;
    }

    // ── §13: MemoryMode enforcement ─────────────────────────────────────────
    // `@pointers`/`@arc` gate their respective raw/manual-memory builtins so
    // the annotations become a real, checked boundary instead of docs-only
    // hints — previously *any* function, regardless of its `@` annotation,
    // could call `ptr_read_i64`/`arc_retain`/etc with zero enforcement (see
    // codegen.rs's history: these builtins were "usable in any function").
    // This is a static, lexical check, the same spirit as Rust's `unsafe`:
    // it doesn't re-derive control flow, it just asks "is this call
    // textually inside the right function/mode, or inside an
    // `unsafe ... end` block?" — enough to give the annotations real teeth
    // without a full effect system. A separate, self-contained recursive
    // walker (rather than folding into `infer_expr`) so it can't interact
    // with — or regress — the existing type-inference logic.
    const PTR_RESTRICTED_BUILTINS: &'static [&'static str] = &[
        "ptr_read_i64", "ptr_write_i64", "ptr_add", "ptr_is_null",
        "ptr_read_i32", "ptr_write_i32", "ptr_read_i16", "ptr_write_i16",
        "ptr_read_i8",  "ptr_write_i8",  "ptr_read_f64", "ptr_write_f64",
        "ptr_read_f32", "ptr_write_f32", "ptr_read_ptr", "ptr_write_ptr",
        "ptr_alloc_size", "ptr_copy", "ptr_compare", "ptr_field_offset",
        "ptr_read_checked", "ptr_write_checked", "ptr_fill", "ptr_zero",
    ];
    const ARC_RESTRICTED_BUILTINS: &'static [&'static str] =
        &["arc_alloc", "arc_retain", "arc_release", "arc_count",
          "arc_downgrade", "arc_upgrade", "arc_weak_release", "arc_weak_count"];
    const ARENA_RESTRICTED_BUILTINS: &'static [&'static str] =
        &["arena_checkpoint", "arena_rewind", "arena_used", "arena_capacity"];

    /// Walks every statement in `body`, recursing into every nested block
    /// (`if`/`match`/`while`/`for`/`do`/`unsafe`/closures — unlike
    /// `infer_expr`, which today only looks at top-level statements), and
    /// errors on any restricted-builtin call not permitted by `mode` or
    /// `in_unsafe`.
    fn check_mem_mode_block(&mut self, body: &[Stmt], mode: MemoryMode, in_unsafe: bool, fn_name: &str) {
        for stmt in body {
            self.check_mem_mode_stmt(stmt, mode, in_unsafe, fn_name);
        }
    }

    fn check_mem_mode_stmt(&mut self, stmt: &Stmt, mode: MemoryMode, in_unsafe: bool, fn_name: &str) {
        match stmt {
            Stmt::Let { value: Some(e), .. } => self.check_mem_mode_expr(e, mode, in_unsafe, fn_name),
            Stmt::Expr(e, _) => self.check_mem_mode_expr(e, mode, in_unsafe, fn_name),
            Stmt::Return(Some(e), _) | Stmt::Break(Some(e), _) => {
                self.check_mem_mode_expr(e, mode, in_unsafe, fn_name);
            }
            // A nested/local fn def is its own lexical scope — it does not
            // inherit the enclosing function's `@` mode or an enclosing
            // `unsafe` block, same as a nested `fn` in Rust isn't implicitly
            // `unsafe` just because it's textually defined inside one.
            Stmt::Item(Item::FnDef(nested)) => {
                self.check_mem_mode_block(&nested.body, nested.mem_mode, false, &nested.name);
            }
            _ => {}
        }
    }

    fn check_mem_mode_expr(&mut self, e: &Expr, mode: MemoryMode, in_unsafe: bool, fn_name: &str) {
        match e {
            Expr::Call(callee, args, span) => {
                if let Expr::Ident(name, _) = callee.as_ref() {
                    self.check_mem_mode_call(name, mode, in_unsafe, fn_name, span);
                }
                self.check_mem_mode_expr(callee, mode, in_unsafe, fn_name);
                for a in args { self.check_mem_mode_expr(a, mode, in_unsafe, fn_name); }
            }
            Expr::MethodCall(recv, _, args, _) => {
                self.check_mem_mode_expr(recv, mode, in_unsafe, fn_name);
                for a in args { self.check_mem_mode_expr(a, mode, in_unsafe, fn_name); }
            }
            Expr::BinOp(l, _, r, _) | Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => {
                self.check_mem_mode_expr(l, mode, in_unsafe, fn_name);
                self.check_mem_mode_expr(r, mode, in_unsafe, fn_name);
            }
            Expr::UnOp(_, inner, _) | Expr::FieldAccess(inner, _, _) | Expr::Cast(inner, _, _) |
            Expr::Try(inner, _) | Expr::Await(inner, _) => self.check_mem_mode_expr(inner, mode, in_unsafe, fn_name),
            Expr::IndexAccess(a, b, _) => {
                self.check_mem_mode_expr(a, mode, in_unsafe, fn_name);
                self.check_mem_mode_expr(b, mode, in_unsafe, fn_name);
            }
            Expr::ArrayLit(items, _) | Expr::TupleLit(items, _) => {
                for i in items { self.check_mem_mode_expr(i, mode, in_unsafe, fn_name); }
            }
            Expr::StructLit(_, fields, _) => {
                for (_, v) in fields { self.check_mem_mode_expr(v, mode, in_unsafe, fn_name); }
            }
            Expr::Return(Some(inner), _) => self.check_mem_mode_expr(inner, mode, in_unsafe, fn_name),
            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                self.check_mem_mode_expr(condition, mode, in_unsafe, fn_name);
                self.check_mem_mode_block(then_body, mode, in_unsafe, fn_name);
                for (cond, b) in elsif_branches {
                    self.check_mem_mode_expr(cond, mode, in_unsafe, fn_name);
                    self.check_mem_mode_block(b, mode, in_unsafe, fn_name);
                }
                if let Some(else_body) = else_body {
                    self.check_mem_mode_block(else_body, mode, in_unsafe, fn_name);
                }
            }
            Expr::Match { subject, arms, .. } => {
                self.check_mem_mode_expr(subject, mode, in_unsafe, fn_name);
                for arm in arms {
                    if let Some(g) = &arm.guard { self.check_mem_mode_expr(g, mode, in_unsafe, fn_name); }
                    self.check_mem_mode_block(&arm.body, mode, in_unsafe, fn_name);
                }
            }
            Expr::While { condition, body, .. } => {
                self.check_mem_mode_expr(condition, mode, in_unsafe, fn_name);
                self.check_mem_mode_block(body, mode, in_unsafe, fn_name);
            }
            Expr::For { iterable, body, .. } => {
                self.check_mem_mode_expr(iterable, mode, in_unsafe, fn_name);
                self.check_mem_mode_block(body, mode, in_unsafe, fn_name);
            }
            Expr::Do { body, .. } => self.check_mem_mode_block(body, mode, in_unsafe, fn_name),
            // Any `unsafe ... end` block — arena/manual/raw/bare — permits
            // raw/manual memory ops inside it, same "trust me" umbrella.
            Expr::Unsafe(body, _, _) => self.check_mem_mode_block(body, mode, true, fn_name),
            // Closures don't have their own `@` mode; conservatively they
            // inherit the enclosing function's mode/unsafe-ness.
            Expr::Closure { body, .. } => self.check_mem_mode_block(body, mode, in_unsafe, fn_name),
            _ => {}
        }
    }

    fn check_mem_mode_call(&mut self, name: &str, mode: MemoryMode, in_unsafe: bool, fn_name: &str, span: &Span) {
        if in_unsafe { return; }
        if Self::PTR_RESTRICTED_BUILTINS.contains(&name) && mode != MemoryMode::Pointers {
            self.err_hint(
                span.clone(),
                format!("`{}` used in `{}`, which is not `@pointers`", name, fn_name),
                format!("mark `{}` as `@pointers`, or wrap this call in `unsafe is ... end`", fn_name),
            );
        }
        if Self::ARC_RESTRICTED_BUILTINS.contains(&name) && mode != MemoryMode::Arc {
            self.err_hint(
                span.clone(),
                format!("`{}` used in `{}`, which is not `@arc`", name, fn_name),
                format!("mark `{}` as `@arc`, or wrap this call in `unsafe is ... end`", fn_name),
            );
        }
        if Self::ARENA_RESTRICTED_BUILTINS.contains(&name) && mode != MemoryMode::Arena {
            self.err_hint(
                span.clone(),
                format!("`{}` used in `{}`, which is not `@arena`", name, fn_name),
                format!("mark `{}` as `@arena`, or wrap this call in `unsafe arena ... end`", fn_name),
            );
        }
    }

    fn check_stmt(&mut self, stmt: &Stmt, fn_name: &str) {
        match stmt {
            Stmt::Let { name, ty, mutable, value, .. } => {
                let inferred = value.as_ref().map(|e| self.infer_expr(e));
                let declared = ty.as_ref().map(HType::from_type_expr);
                let final_ty = declared.or(inferred).unwrap_or(HType::Any);
                self.define(name, final_ty, *mutable);
            }
            Stmt::Return(expr, span) => {
                if let Some(ret_ty) = &self.current_fn_return.clone() {
                    let expr_ty = expr.as_ref().map(|e| self.infer_expr(e)).unwrap_or(HType::Void);
                    if !expr_ty.compatible_with(ret_ty) {
                        self.err_hint(
                            span.clone(),
                                      format!("return type mismatch in `{}`: expected `{}`, found `{}`", fn_name, ret_ty.display(), expr_ty.display()),
                                          format!("convert the value to `{}` before returning, or change the function's declared return type", ret_ty.display()),
                        );
                    }
                }
            }
            Stmt::Expr(e, _) => { self.infer_expr(e); }
            Stmt::Item(item) => self.check_item(item),
            _ => {}
        }
    }
}
