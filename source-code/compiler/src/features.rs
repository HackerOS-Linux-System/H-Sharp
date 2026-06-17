use hsharp_parser::ast::*;
use crate::typechecker::Diagnostic;
use crate::builtins_registry::{self, Backend};

/// A language feature that not all backends support yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LangFeature {
    /// `await <expr>` — async runtime required.
    Await,
    /// `async fn` — async runtime required.
    AsyncFn,
    /// `unsafe arena(...) is ... end` — arena allocator modes.
    UnsafeArena,
    /// `unsafe manual(...) is ... end` — manual memory management modes.
    UnsafeManual,
    /// Closures capturing more than 2 outer variables (current
    /// `hsh_closure_call1/2` trampolines only forward up to 2 captures —
    /// see roadmap §4).
    ClosureManyCaptures,
    /// Generic functions/structs/impls (`fn f<T>(...)`) — requires
    /// monomorphization (§2) to have run first; if it hasn't (or a call
    /// site couldn't be resolved to a concrete instantiation), codegen
    /// would otherwise see an unresolved `TypeExpr::Named("T")`.
    UnresolvedGeneric,
}

impl LangFeature {
    fn supported_on(&self, backend: Backend) -> bool {
        match self {
            LangFeature::Await | LangFeature::AsyncFn =>
            backend == Backend::Interpreter,
            LangFeature::UnsafeArena | LangFeature::UnsafeManual =>
            backend == Backend::Llvm,
            LangFeature::ClosureManyCaptures =>
            false, // not supported by ANY backend yet (hard 2-capture limit)
            LangFeature::UnresolvedGeneric =>
            false, // never valid post-monomorphization; always an error
        }
    }

    fn message(&self, backend: Backend) -> String {
        match self {
            LangFeature::Await =>
            format!("`await` is not supported by the {} backend", backend.name()),
                LangFeature::AsyncFn =>
                format!("`async fn` is not supported by the {} backend", backend.name()),
                    LangFeature::UnsafeArena =>
                    format!("`unsafe arena(...)` is not supported by the {} backend", backend.name()),
                        LangFeature::UnsafeManual =>
                        format!("`unsafe manual(...)` is not supported by the {} backend", backend.name()),
                            LangFeature::ClosureManyCaptures =>
                            "closures capturing more than 2 outer variables are not yet supported by any backend".to_string(),
                            LangFeature::UnresolvedGeneric =>
                            "generic function/type left unresolved after monomorphization".to_string(),
        }
    }

    fn hint(&self, _backend: Backend) -> &'static str {
        match self {
            LangFeature::Await | LangFeature::AsyncFn =>
            "run without --release (uses the interpreter), or restructure without `await`/`async` for compiled builds",
            LangFeature::UnsafeArena =>
            "arena allocation requires a compiled backend; this code path is interpreter-only here",
            LangFeature::UnsafeManual =>
            "manual memory management requires a compiled backend; this code path is interpreter-only here",
            LangFeature::ClosureManyCaptures =>
            "reduce the closure to <= 2 captured variables (e.g. bundle extras into a small struct and capture that one value instead)",
            LangFeature::UnresolvedGeneric =>
            "ensure every call site provides enough type information to infer the type parameter (e.g. via the let binding's declared type)",
        }
    }
}

/// Walk `module` and return a diagnostic for every AST node using a feature
/// unsupported on `backend`. Also checks every `Expr::Call`/`Expr::Ident`
/// against `builtins_registry::supported_on`.
pub fn check_module_features(module: &Module, backend: Backend) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for item in &module.items {
        check_item(item, backend, &mut out);
    }
    out
}

fn check_item(item: &Item, backend: Backend, out: &mut Vec<Diagnostic>) {
    match item {
        Item::FnDef(f) => {
            if f.is_async && !LangFeature::AsyncFn.supported_on(backend) {
                push(out, LangFeature::AsyncFn, backend, f.span.clone());
            }
            check_block(&f.body, backend, out);
        }
        Item::ImplBlock(imp) => for m in &imp.methods { check_item(&Item::FnDef(m.clone()), backend, out); },
        Item::ModDecl { inline: Some(items), .. } => for it in items { check_item(it, backend, out); },
        _ => {}
    }
}

fn check_block(stmts: &[Stmt], backend: Backend, out: &mut Vec<Diagnostic>) {
    for stmt in stmts { check_stmt(stmt, backend, out); }
}

fn check_stmt(stmt: &Stmt, backend: Backend, out: &mut Vec<Diagnostic>) {
    match stmt {
        Stmt::Let { value: Some(e), .. } => check_expr(e, backend, out),
        Stmt::Return(Some(e), _) | Stmt::Expr(e, _) | Stmt::Break(Some(e), _) => check_expr(e, backend, out),
        Stmt::Item(item) => check_item(item, backend, out),
        _ => {}
    }
}

fn check_expr(expr: &Expr, backend: Backend, out: &mut Vec<Diagnostic>) {
    match expr {
        Expr::Await(inner, span) => {
            if !LangFeature::Await.supported_on(backend) {
                push(out, LangFeature::Await, backend, span.clone());
            }
            check_expr(inner, backend, out);
        }
        Expr::Unsafe(body, arena_cfg, span) => {
            if let Some(cfg) = arena_cfg {
                let feature = match &cfg.mode {
                    UnsafeMode::Arena { .. } => Some(LangFeature::UnsafeArena),
                    UnsafeMode::Manual(_)    => Some(LangFeature::UnsafeManual),
                    UnsafeMode::Raw          => None,
                };
                if let Some(f) = feature {
                    if !f.supported_on(backend) {
                        push(out, f, backend, span.clone());
                    }
                }
            }
            check_block(body, backend, out);
        }
        Expr::Closure { params, body, span, .. } => {
            // §4 closure capture check: count free variables referenced in
            // `body` that are NOT among `params` and aren't calls to
            // top-level functions (heuristic: any bare Ident not in
            // `params` and not immediately followed by a call is treated
            // as a potential capture). This is intentionally conservative
            // (may over-count), matching the "loud false positive is
            // better than silent truncation" philosophy of this checker.
            let param_names: std::collections::HashSet<&str> =
            params.iter().map(|p| p.name.as_str()).collect();
            let mut captures = std::collections::HashSet::new();
            collect_free_idents(body, &param_names, &mut captures);
            if captures.len() > 2 && !LangFeature::ClosureManyCaptures.supported_on(backend) {
                push(out, LangFeature::ClosureManyCaptures, backend, span.clone());
            }
            check_block(body, backend, out);
        }
        Expr::Call(callee, args, span) => {
            if let Expr::Ident(name, _) = callee.as_ref() {
                if !builtins_registry::supported_on(name, backend) {
                    let spec = builtins_registry::find(name);
                    let doc = spec.map(|s| s.doc).unwrap_or("");
                    out.push(
                        Diagnostic::error(
                            span.clone(),
                                          format!("`{}` is not supported by the {} backend", name, backend.name()),
                        ).with_hint(doc.to_string())
                        .with_hint(format!(
                            "implemented on: {}",
                            spec.map(|s| s.backends.iter().map(|b| b.name()).collect::<Vec<_>>().join(", "))
                            .unwrap_or_default()
                        ))
                    );
                }
            }
            check_expr(callee, backend, out);
            for a in args { check_expr(a, backend, out); }
        }
        // Generic recursion into all other expression kinds:
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { check_expr(l, backend, out); check_expr(r, backend, out); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) => check_expr(e, backend, out),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { check_expr(l, backend, out); check_expr(r, backend, out); }
        Expr::FieldAccess(e, _, _) => check_expr(e, backend, out),
        Expr::IndexAccess(e, i, _) => { check_expr(e, backend, out); check_expr(i, backend, out); }
        Expr::MethodCall(recv, _, args, _) => {
            check_expr(recv, backend, out);
            for a in args { check_expr(a, backend, out); }
        }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => for e in elems { check_expr(e, backend, out); },
        Expr::StructLit(_, fields, _) => for (_, e) in fields { check_expr(e, backend, out); },
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            check_expr(condition, backend, out);
            check_block(then_body, backend, out);
            for (c, b) in elsif_branches { check_expr(c, backend, out); check_block(b, backend, out); }
            if let Some(b) = else_body { check_block(b, backend, out); }
        }
        Expr::While { condition, body, .. } => { check_expr(condition, backend, out); check_block(body, backend, out); }
        Expr::For { iterable, body, .. } => { check_expr(iterable, backend, out); check_block(body, backend, out); }
        Expr::Do { body, .. } => check_block(body, backend, out),
        Expr::Match { subject, arms, .. } => {
            check_expr(subject, backend, out);
            for arm in arms {
                if let Some(g) = &arm.guard { check_expr(g, backend, out); }
                check_block(&arm.body, backend, out);
            }
        }
        Expr::Return(Some(e), _) => check_expr(e, backend, out),
        _ => {}
    }
}

fn push(out: &mut Vec<Diagnostic>, feature: LangFeature, backend: Backend, span: hsharp_parser::span::Span) {
    out.push(Diagnostic::error(span, feature.message(backend)).with_hint(feature.hint(backend).to_string()));
}

/// Collect identifiers referenced inside `body` that are not in `bound`
/// (parameters) and are not themselves the callee of a `Call` (a plain
/// function call `foo()` references a top-level fn, not a capture).
fn collect_free_idents(stmts: &[Stmt], bound: &std::collections::HashSet<&str>, out: &mut std::collections::HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value: Some(e), .. } => collect_free_idents_expr(e, bound, out),
            Stmt::Return(Some(e), _) | Stmt::Expr(e, _) => collect_free_idents_expr(e, bound, out),
            _ => {}
        }
    }
}

fn collect_free_idents_expr(expr: &Expr, bound: &std::collections::HashSet<&str>, out: &mut std::collections::HashSet<String>) {
    match expr {
        Expr::Ident(name, _) => {
            if !bound.contains(name.as_str()) {
                out.insert(name.clone());
            }
        }
        Expr::Call(callee, args, _) => {
            // The callee of a direct call is a function reference, not a
            // capture — skip it; recurse into args only.
            let _ = callee;
            for a in args { collect_free_idents_expr(a, bound, out); }
        }
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { collect_free_idents_expr(l, bound, out); collect_free_idents_expr(r, bound, out); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => collect_free_idents_expr(e, bound, out),
        Expr::FieldAccess(e, _, _) => collect_free_idents_expr(e, bound, out),
        Expr::IndexAccess(e, i, _) => { collect_free_idents_expr(e, bound, out); collect_free_idents_expr(i, bound, out); }
        Expr::MethodCall(recv, _, args, _) => {
            collect_free_idents_expr(recv, bound, out);
            for a in args { collect_free_idents_expr(a, bound, out); }
        }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => for e in elems { collect_free_idents_expr(e, bound, out); },
        Expr::StructLit(_, fields, _) => for (_, e) in fields { collect_free_idents_expr(e, bound, out); },
        _ => {}
    }
}
