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
    /// A closure literal (`|params| is ... end` / `\|params\| expr`)
    /// anywhere on the **LLVM** backend.
    ///
    /// BUG FIX: this used to be `ClosureManyCaptures`, gating only
    /// closures capturing *more than 2* outer variables, on the stated
    /// assumption that closures capturing 0-2 variables had real codegen
    /// support via `hsh_closure_call1/2` trampolines in
    /// `compiler/runtime/core.c`. They don't: `Expr::Closure` has **no
    /// codegen arm at all** in `FnCx::expr()` (`codegen.rs`) — the two
    /// places `Expr::Closure` appears in that file are an AST move-checker
    /// and an AST feature-scanner, neither of which emits any LLVM IR for
    /// it. A closure literal compiled with `--release` silently fell
    /// through to `expr()`'s generic fallback (a placeholder zero value)
    /// instead of erroring, meaning *every* closure — 0 captures or 20 —
    /// silently miscompiled into garbage on the LLVM backend, not just
    /// ones with "too many" captures. `hsh_closure_create`/
    /// `hsh_closure_call1/2` are real, callable C runtime functions, but
    /// nothing in codegen.rs ever calls them; they're dead code today,
    /// not a working 0-2-capture fast path with a gap above it. Gating
    /// unconditionally (any closure, any capture count) turns that silent
    /// miscompilation into the loud, correct compile error this project's
    /// other backend gaps already get (`await`, `unsafe arena(...)`, …)
    /// until real closure codegen (heap-allocated capture environment +
    /// a genuine function-pointer/env-pointer closure value + call sites
    /// that dispatch through it) is built.
    Closures,
    /// A user-defined H# struct type passed *by value* (not `&`/`&mut`)
    /// as a parameter or return type of an `extern [c/c++/rust]` function
    /// — on **any** backend (the interpreter has no `extern` support at
    /// all yet, so this isn't backend-specific the way the others are).
    ///
    /// H# gives every struct field a uniform `int64_t` slot, with no
    /// per-field width/type at all (`compiler/runtime/core.c`'s
    /// `hsh_struct_new`/`get`/`set` — see `ffi.rs`'s `struct_c_def` doc
    /// comment for the full story). `build_extern_fn_type` (codegen.rs)
    /// has no case for "H# struct passed by value" at all: it falls
    /// through `llvm_types.rs`'s `htype_to_llvm` catch-all, which returns
    /// a bare `i64` — meaning a call like `extern_fn(my_struct)` would
    /// silently pass my_struct's raw *heap-handle integer* as if it were
    /// the struct's real, C-ABI-classified byte layout. That's not a
    /// pointer-vs-value mixup a reader could spot in the generated code
    /// either: it's a single `i64` argument either way, so the call
    /// "looks" fine right up until the C side reads garbage or the
    /// process segfaults. Gating this converts that silent miscompile
    /// into the same loud, actionable error this project already gives
    /// `await`/`unsafe arena(...)`/bare closures. Passing `&MyStruct`/
    /// `&mut MyStruct` (a real pointer to the int64-slot layout
    /// `struct_c_def` describes) already works correctly today and isn't
    /// gated.
    StructByValueFfi,
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
            LangFeature::Closures =>
            backend == Backend::Interpreter,
            LangFeature::StructByValueFfi =>
            false, // not implemented on any backend yet — see doc comment
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
                            LangFeature::Closures =>
                            format!("closures are not implemented by the {} backend yet (works fine with `hsharp preview` / the interpreter)", backend.name()),
                            LangFeature::StructByValueFfi =>
                            "passing a struct by value across an `extern` FFI boundary is not implemented yet (on any backend)".to_string(),
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
            LangFeature::Closures =>
            "closures need a compiled backend that can build a heap-allocated capture environment and a real function-pointer/env-pointer closure value — not implemented in this LLVM backend yet; run without --release (uses the interpreter) instead, or rewrite as a named top-level `fn` taking any 'captured' state as explicit parameters",
            LangFeature::StructByValueFfi =>
            "pass a pointer instead: change the parameter/return type to `&MyStruct` (or `&mut MyStruct` if the C side writes to it) — every H# struct field is already a plain int64 slot in declaration order (see `hsharp ffi-header`'s generated `typedef struct { int64_t ...; }`), so the C/Rust side can read/write it correctly through a pointer today",
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
    // Needed by the `StructByValueFfi` check below (`check_extern_block`) —
    // collected once here rather than threaded in from `codegen.rs`'s own
    // copy, since this runs as an independent pre-codegen diagnostic pass
    // (see `cli/src/compile.rs`) and may run without codegen ever
    // starting at all (e.g. `hsharp check`).
    let mut structs: std::collections::HashMap<String, Vec<StructField>> = std::collections::HashMap::new();
    for item in &module.items {
        if let Item::StructDef(sd) = item {
            structs.insert(sd.name.clone(), sd.fields.clone());
        }
    }
    for item in &module.items {
        check_item(item, backend, &structs, &mut out);
    }
    out
}

fn check_item(item: &Item, backend: Backend, structs: &std::collections::HashMap<String, Vec<StructField>>, out: &mut Vec<Diagnostic>) {
    match item {
        Item::FnDef(f) => {
            if f.is_async && !LangFeature::AsyncFn.supported_on(backend) {
                push(out, LangFeature::AsyncFn, backend, f.span.clone());
            }
            check_block(&f.body, backend, structs, out);
        }
        Item::ImplBlock(imp) => for m in &imp.methods { check_item(&Item::FnDef(m.clone()), backend, structs, out); },
        Item::ModDecl { inline: Some(items), .. } => for it in items { check_item(it, backend, structs, out); },
        Item::Extern(ext) => check_extern_block(ext, backend, structs, out),
        _ => {}
    }
}

/// The `StructByValueFfi` check (see that variant's doc comment):
/// every extern function's params and return type, looking for a bare
/// (non-`&`/`&mut`) `TypeExpr::Named(n)` where `n` is a known H# struct.
fn check_extern_block(ext: &ExternBlock, backend: Backend, structs: &std::collections::HashMap<String, Vec<StructField>>, out: &mut Vec<Diagnostic>) {
    if !ext.lang.is_c_abi() {
        return; // Python bridge marshals through strings, not a C ABI struct layout at all.
    }
    let is_by_value_struct = |ty: &TypeExpr| -> bool {
        matches!(ty, TypeExpr::Named(n) if structs.contains_key(n))
    };
    for f in &ext.functions {
        for p in &f.params {
            if is_by_value_struct(&p.ty) {
                push(out, LangFeature::StructByValueFfi, backend, f.span.clone());
            }
        }
        if let Some(r) = &f.return_type {
            if is_by_value_struct(r) {
                push(out, LangFeature::StructByValueFfi, backend, f.span.clone());
            }
        }
    }
}

fn check_block(stmts: &[Stmt], backend: Backend, structs: &std::collections::HashMap<String, Vec<StructField>>, out: &mut Vec<Diagnostic>) {
    for stmt in stmts { check_stmt(stmt, backend, structs, out); }
}

fn check_stmt(stmt: &Stmt, backend: Backend, structs: &std::collections::HashMap<String, Vec<StructField>>, out: &mut Vec<Diagnostic>) {
    match stmt {
        Stmt::Let { value: Some(e), .. } => check_expr(e, backend, structs, out),
        Stmt::Return(Some(e), _) | Stmt::Expr(e, _) | Stmt::Break(Some(e), _) => check_expr(e, backend, structs, out),
        Stmt::Item(item) => check_item(item, backend, structs, out),
        _ => {}
    }
}

fn check_expr(expr: &Expr, backend: Backend, structs: &std::collections::HashMap<String, Vec<StructField>>, out: &mut Vec<Diagnostic>) {
    match expr {
        Expr::Await(inner, span) => {
            if !LangFeature::Await.supported_on(backend) {
                push(out, LangFeature::Await, backend, span.clone());
            }
            check_expr(inner, backend, structs, out);
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
            check_block(body, backend, structs, out);
        }
        Expr::Closure { params, body, span, .. } => {
            // BUG FIX: see `LangFeature::Closures`'s doc comment — every
            // closure literal is unimplemented on the LLVM backend, not
            // just ones with "too many" captures, so this now gates
            // unconditionally instead of only past a free-variable count
            // threshold. (The free-variable counting below is no longer
            // needed for the gate itself, but stays removed rather than
            // kept-around-unused — see git history if it's ever needed
            // again once real closure codegen lands and *does* have a
            // genuine capture-count limit to check.)
            if !LangFeature::Closures.supported_on(backend) {
                push(out, LangFeature::Closures, backend, span.clone());
            }
            let _ = params;
            check_block(body, backend, structs, out);
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
            check_expr(callee, backend, structs, out);
            for a in args { check_expr(a, backend, structs, out); }
        }
        // Generic recursion into all other expression kinds:
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { check_expr(l, backend, structs, out); check_expr(r, backend, structs, out); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) => check_expr(e, backend, structs, out),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { check_expr(l, backend, structs, out); check_expr(r, backend, structs, out); }
        Expr::FieldAccess(e, _, _) => check_expr(e, backend, structs, out),
        Expr::IndexAccess(e, i, _) => { check_expr(e, backend, structs, out); check_expr(i, backend, structs, out); }
        Expr::MethodCall(recv, _, args, _) => {
            check_expr(recv, backend, structs, out);
            for a in args { check_expr(a, backend, structs, out); }
        }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => for e in elems { check_expr(e, backend, structs, out); },
        Expr::StructLit(_, fields, _) => for (_, e) in fields { check_expr(e, backend, structs, out); },
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            check_expr(condition, backend, structs, out);
            check_block(then_body, backend, structs, out);
            for (c, b) in elsif_branches { check_expr(c, backend, structs, out); check_block(b, backend, structs, out); }
            if let Some(b) = else_body { check_block(b, backend, structs, out); }
        }
        Expr::While { condition, body, .. } => { check_expr(condition, backend, structs, out); check_block(body, backend, structs, out); }
        Expr::For { iterable, body, .. } => { check_expr(iterable, backend, structs, out); check_block(body, backend, structs, out); }
        Expr::Do { body, .. } => check_block(body, backend, structs, out),
        Expr::Match { subject, arms, .. } => {
            check_expr(subject, backend, structs, out);
            for arm in arms {
                if let Some(g) = &arm.guard { check_expr(g, backend, structs, out); }
                check_block(&arm.body, backend, structs, out);
            }
        }
        Expr::Return(Some(e), _) => check_expr(e, backend, structs, out),
        _ => {}
    }
}

fn push(out: &mut Vec<Diagnostic>, feature: LangFeature, backend: Backend, span: hsharp_parser::span::Span) {
    out.push(Diagnostic::error(span, feature.message(backend)).with_hint(feature.hint(backend).to_string()));
}

/// Collect identifiers referenced inside `body` that are not in `bound`
/// (parameters) and are not themselves the callee of a `Call` (a plain
/// function call `foo()` references a top-level fn, not a capture).
///
/// No longer called from `check_expr`'s `Expr::Closure` arm (see
/// `LangFeature::Closures`'s doc comment for why the gate is now
/// unconditional rather than count-based) — kept, not deleted, for when
/// real LLVM closure codegen lands and needs an actual capture-count
/// limit to check again (e.g. a fixed-arity trampoline convention that
/// genuinely does cap at N captures, unlike today's dead
/// `hsh_closure_call1/2`).
#[allow(dead_code)]
fn collect_free_idents(stmts: &[Stmt], bound: &std::collections::HashSet<&str>, out: &mut std::collections::HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value: Some(e), .. } => collect_free_idents_expr(e, bound, out),
            Stmt::Return(Some(e), _) | Stmt::Expr(e, _) => collect_free_idents_expr(e, bound, out),
            _ => {}
        }
    }
}

#[allow(dead_code)]
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
