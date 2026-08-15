use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::typechecker::{HType, TypeChecker};

pub struct MonoStats {
    pub instances_generated: usize,
    pub call_sites_rewritten: usize,
    pub unresolved: Vec<(String, Span)>,
    /// A generic call site where a concrete type argument was
    /// successfully inferred, but that type doesn't actually implement
    /// one of the type parameter's declared bounds (`fn f<T: Trait>`).
    /// Previously this went completely unchecked — see this module's
    /// doc comment on `check_bounds` for why that matters — so a
    /// mismatched call typechecked cleanly and only surfaced as a
    /// confusing "undefined fn" deep in LLVM codegen (the mangled
    /// method-call target, e.g. `NotAVisitor_visit_num`, simply doesn't
    /// exist because no such `impl` was ever written).
    pub bound_violations: Vec<BoundViolation>,
}

pub struct BoundViolation {
    pub fn_name:    String,
    pub type_param: String,
    pub trait_name: String,
    pub concrete_ty: String,
    pub span: Span,
}

/// type name -> set of trait names it has an `impl Type : Trait is ... end`
/// block for. Built once per `monomorphize()` call from the module's own
/// `Item::ImplBlock`s — the only source of truth for "does X implement
/// Y" in this compiler (there's no separate trait-registry anywhere
/// else; `typecheck`'s lib.rs doesn't track this at all, per the
/// `check_bounds` doc comment below).
fn build_impls_table(module: &Module) -> HashMap<String, HashSet<String>> {
    let mut table: HashMap<String, HashSet<String>> = HashMap::new();
    for item in &module.items {
        if let Item::ImplBlock(imp) = item {
            if let Some(trait_name) = &imp.trait_name {
                table.entry(imp.type_name.clone()).or_default().insert(trait_name.clone());
            }
        }
    }
    table
}

/// Checks `generic_fn`'s declared bounds (`fn f<T: Trait1 + Trait2>`)
/// against the concrete `type_args` inferred at a call site, pushing a
/// `BoundViolation` into `stats` for anything unsatisfied.
///
/// This is deliberately *name-based* (checks `impls_table` for an exact
/// `Item::ImplBlock` match), not a full trait-coherence system — no
/// blanket impls, no supertraits, no associated types. That's enough to
/// catch the concrete failure mode this exists for (passing a type that
/// plainly never implemented the required trait at all — the
/// `NotAVisitor` case) without trying to build a complete trait solver
/// in one pass. A type that *does* implement the trait but only found
/// via some mechanism this table doesn't model would incorrectly be
/// flagged — there's no such mechanism in this compiler today (single,
/// flat `impl Type : Trait` blocks are the only way to implement
/// anything — see `ast.rs`'s `ImplBlock`), so that gap is currently
/// theoretical, not real.
fn check_bounds(
    generic_fn: &FnDef,
    type_args: &[HType],
    impls_table: &HashMap<String, HashSet<String>>,
    span: &Span,
    stats: &mut MonoStats,
) {
    for (tp, ty) in generic_fn.type_params.iter().zip(type_args.iter()) {
        if tp.bounds.is_empty() { continue; }
        // Fail-open on `Any`/unresolved types — see this module's
        // `check_bounds` doc comment update below: `infer_type_args`
        // calls `checker.infer_expr_pub(arg_expr)` on each call-site
        // argument, but by the time monomorphization runs (a separate
        // pass, after `check_module` has already finished and unwound
        // its scope stack), a plain local-variable argument like `ev`
        // often can't be resolved anymore and falls back to `HType::Any`
        // — not because the call is actually wrong, but because this
        // second pass has less context than the first one did. Treating
        // `Any` as "violates every bound" produced false positives on
        // completely correct programs (confirmed: a real, working
        // `eval_with(ev, tree)` call was flagged here during testing).
        // Better a missed violation (falls through to today's status
        // quo: an opaque codegen error) than rejecting correct code —
        // matches the "lenient — don't error on unknown idents"
        // philosophy `typecheck`'s own `infer_expr` already documents
        // for the exact same reason.
        let concrete_name = match htype_to_type_expr(ty) {
            TypeExpr::Named(n) if n != "any" => n,
            _ => continue,
        };
        let implemented = impls_table.get(&concrete_name).cloned().unwrap_or_default();
        for bound in &tp.bounds {
            if !implemented.contains(bound) {
                stats.bound_violations.push(BoundViolation {
                    fn_name: generic_fn.name.clone(),
                    type_param: tp.name.clone(),
                    trait_name: bound.clone(),
                    concrete_ty: concrete_name.clone(),
                    span: span.clone(),
                });
            }
        }
    }
}

/// Entry point: monomorphize `module` in place, returning stats.
///
/// `checker` should be a `TypeChecker` that has ALREADY run
/// `check_module` on this module (so its `fns`/`structs` maps are
/// populated) — monomorphization reuses the typechecker's type inference
/// to determine call-site type arguments.
pub fn monomorphize(module: &mut Module, checker: &mut TypeChecker) -> MonoStats {
    // 1. COLLECTION: split items into generic vs. concrete.
    let mut generic_fns: HashMap<String, FnDef> = HashMap::new();
    let mut generic_structs: HashMap<String, StructDef> = HashMap::new();
    let mut concrete_items: Vec<Item> = Vec::new();

    // Built once, up front, from the module as originally written — impl
    // blocks are always concrete items (an `impl` itself never has type
    // params of its own in this language), so draining generic fns/
    // structs out of `module.items` below doesn't affect this table.
    let impls_table = build_impls_table(module);

    for item in module.items.drain(..) {
        match item {
            Item::FnDef(f) if !f.type_params.is_empty() => {
                generic_fns.insert(f.name.clone(), f);
            }
            Item::StructDef(s) if !s.type_params.is_empty() => {
                generic_structs.insert(s.name.clone(), s);
            }
            other => concrete_items.push(other),
        }
    }

    // 2. INSTANCE SET: find every call site (in concrete items, including
    // bodies of concrete functions) referencing a generic_fns/generic_structs
    // name, infer concrete type arguments, and build a worklist. The
    // worklist is processed breadth-first because instantiating
    // `Wrapper<int>` might itself contain a call to another generic
    // function — that call site lives in the INSTANCE we're about to
    // generate, so we discover it only after generating the instance.
    let mut worklist: VecDeque<(String, Vec<HType>)> = VecDeque::new();
    let mut seen: HashSet<(String, String)> = HashSet::new(); // (name, mangled-suffix)
    let mut stats = MonoStats { instances_generated: 0, call_sites_rewritten: 0, unresolved: Vec::new(), bound_violations: Vec::new() };

    // Seed the worklist from concrete items.
    for item in &concrete_items {
        collect_generic_uses(item, &generic_fns, &impls_table, checker, &mut worklist, &mut stats);
    }

    // 3 & 4. SUBSTITUTION + emission, processing the worklist. Generated
    // instances are appended to `concrete_items`; their bodies are also
    // scanned for further generic uses (chained generics).
    while let Some((name, type_args)) = worklist.pop_front() {
        let suffix = mangle_suffix(&type_args);
        let key = (name.clone(), suffix.clone());
        if !seen.insert(key) { continue; } // already generated

        if let Some(generic_fn) = generic_fns.get(&name) {
            let mangled_name = format!("{}__{}", name, suffix);
            let instance = instantiate_fn(generic_fn, &mangled_name, &type_args);
            stats.instances_generated += 1;

            // Scan the new instance's body for further generic calls
            // (e.g. it calls another generic fn with a now-concrete type).
            let inst_item = Item::FnDef(instance);
            collect_generic_uses(&inst_item, &generic_fns, &impls_table, checker, &mut worklist, &mut stats);
            concrete_items.push(inst_item);
        } else if let Some(generic_struct) = generic_structs.get(&name) {
            let mangled_name = format!("{}__{}", name, suffix);
            let instance = instantiate_struct(generic_struct, &mangled_name, &type_args);
            stats.instances_generated += 1;
            concrete_items.push(Item::StructDef(instance));
        }
        // else: name wasn't actually generic (shouldn't happen — guarded
        // by collect_generic_uses only enqueueing known generic names).
    }

    // 5. REWRITE CALL SITES in concrete_items (including the newly
    // generated instances, whose bodies may themselves call other generic
    // instances that are now also concrete).
    for item in concrete_items.iter_mut() {
        rewrite_item_calls(item, &generic_fns, checker, &mut stats);
    }

    module.items = concrete_items;
    stats
}

// ── 2. Collection: find generic call sites, infer type args ────────────────

fn collect_generic_uses(
    item: &Item,
    generic_fns: &HashMap<String, FnDef>,
    impls_table: &HashMap<String, HashSet<String>>,
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                        stats: &mut MonoStats,
) {
    match item {
        Item::FnDef(f) => {
            // BUG FIX (found while testing trait-bounded generics):
            // `collect_in_block`/`collect_in_expr` run as a *second*
            // pass over the AST, after `check_module` has already
            // finished and popped every local scope it pushed while
            // typechecking this same function body — so a plain
            // `checker.infer_expr_pub(&Expr::Ident("x"))` call for a
            // local variable `x` finds nothing and silently falls back
            // to `HType::Any`. Confirmed via direct testing: a call like
            // `identity(some_box_value)` was monomorphizing into
            // `identity__any` instead of `identity__Box` — a real
            // *correctness* bug (the wrong specialization gets
            // generated), not just a missing diagnostic, for what is
            // the single most common way to call a generic function.
            //
            // Fix: track local `let` types ourselves in a flat map as
            // we walk each function body (seeded with parameter types
            // here, extended on every `Stmt::Let` in `collect_in_block`)
            // and consult it before falling back to the checker. Not a
            // full scope stack (a `let` inside a nested block that
            // shadows an outer binding will incorrectly "leak" its type
            // to the same name after the block ends) — a real but minor
            // imprecision, hugely preferable to every local variable
            // resolving to `Any` unconditionally.
            let mut local_types: HashMap<String, HType> = HashMap::new();
            for p in &f.params {
                local_types.insert(p.name.clone(), HType::from_type_expr(&p.ty));
            }
            collect_in_block(&f.body, generic_fns, impls_table, checker, worklist, stats, &mut local_types);
        }
        Item::ImplBlock(imp) => for m in &imp.methods {
            let mut local_types: HashMap<String, HType> = HashMap::new();
            local_types.insert("self".to_string(), HType::Named(imp.type_name.clone()));
            for p in &m.params {
                local_types.insert(p.name.clone(), HType::from_type_expr(&p.ty));
            }
            collect_in_block(&m.body, generic_fns, impls_table, checker, worklist, stats, &mut local_types);
        },
        Item::ModDecl { inline: Some(items), .. } => for it in items { collect_generic_uses(it, generic_fns, impls_table, checker, worklist, stats); },
        _ => {}
    }
}

fn collect_in_block(
    stmts: &[Stmt],
    generic_fns: &HashMap<String, FnDef>,
    impls_table: &HashMap<String, HashSet<String>>,
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                    stats: &mut MonoStats,
    local_types: &mut HashMap<String, HType>,
) {
    for stmt in stmts {
        if let Stmt::Let { name, ty, value, .. } = stmt {
            // Explicit annotation wins outright; otherwise infer from
            // the RHS. `infer_expr_pub` is reliable here even though
            // it's "cold" (see the doc comment above): a struct
            // literal's type is syntactically apparent, a call's type
            // comes from the callee's own declared return type, a
            // literal's type is its own — none of those need scope
            // context, only a bare `Ident` reference does, and that's
            // exactly the case this whole `local_types` map exists to
            // shortcut around instead.
            let inferred = ty.as_ref().map(HType::from_type_expr)
                .or_else(|| value.as_ref().map(|e| checker.infer_expr_pub(e)));
            if let Some(t) = inferred {
                local_types.insert(name.clone(), t);
            }
        }
        match stmt {
            Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) | Stmt::Expr(e, _) =>
            collect_in_expr(e, generic_fns, impls_table, checker, worklist, stats, local_types),
            _ => {}
        }
    }
}

fn collect_in_expr(
    expr: &Expr,
    generic_fns: &HashMap<String, FnDef>,
    impls_table: &HashMap<String, HashSet<String>>,
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                   stats: &mut MonoStats,
    local_types: &HashMap<String, HType>,
) {
    if let Expr::Call(callee, args, span) = expr {
        if let Expr::Ident(name, _) = callee.as_ref() {
            if let Some(generic_fn) = generic_fns.get(name) {
                match infer_type_args(generic_fn, args, checker, local_types) {
                    Some(type_args) => {
                        // See `check_bounds`'s doc comment: this is the
                        // point where a concrete type argument is known
                        // for every one of `generic_fn`'s type params —
                        // the natural place to also verify it actually
                        // satisfies any `T: Trait` bound declared on
                        // that param, instead of silently accepting any
                        // type and letting a mismatch surface later as
                        // an opaque "undefined fn" in LLVM codegen.
                        check_bounds(generic_fn, &type_args, impls_table, span, stats);
                        worklist.push_back((name.clone(), type_args));
                    }
                    None => stats.unresolved.push((name.clone(), span.clone())),
                }
            }
        }
    }
    // Recurse into all sub-expressions (best-effort generic coverage,
    // including nested blocks). `local_types` is read-only from here
    // down (nested blocks can only ever *add* more local bindings on
    // top of what's already known — see the shadowing caveat on
    // `collect_generic_uses`'s doc comment — so a plain shared
    // reference is enough; no need to thread a fresh mutable copy per
    // nested scope for this best-effort pass).
    let mut local_types_owned = local_types.clone();
    walk_sub_exprs(expr, &mut |e| collect_in_expr(e, generic_fns, impls_table, checker, worklist, stats, &local_types_owned));
    walk_sub_blocks(expr, &mut |b| collect_in_block(b, generic_fns, impls_table, checker, worklist, stats, &mut local_types_owned));
}

/// Infer concrete `HType`s for each of `generic_fn.type_params`, by matching
/// each parameter's declared type (`TypeExpr::Named(param_name)`) against
/// the inferred type of the corresponding *argument expression* at the call
/// site.
///
/// Returns `None` if any type parameter couldn't be pinned down from the
/// arguments (e.g. it only appears in the return type) — the caller records
/// this as `unresolved` for `features.rs` to report.
fn infer_type_args(generic_fn: &FnDef, call_args: &[Expr], checker: &mut TypeChecker, local_types: &HashMap<String, HType>) -> Option<Vec<HType>> {
    let mut resolved: HashMap<String, HType> = HashMap::new();

    for (param, arg_expr) in generic_fn.params.iter().zip(call_args.iter()) {
        // `local_types` first — see `collect_generic_uses`'s doc comment
        // on why `checker.infer_expr_pub` alone gives the wrong answer
        // (`Any`) for a bare local-variable argument.
        let arg_ty = match arg_expr {
            Expr::Ident(n, _) if local_types.contains_key(n) => local_types[n].clone(),
            _ => checker.infer_expr_pub(arg_expr),
        };
        bind_type_param(&param.ty, &arg_ty, &mut resolved);
    }

    let mut out = Vec::with_capacity(generic_fn.type_params.len());
    for tp in &generic_fn.type_params {
        out.push(resolved.get(&tp.name).cloned()?);
    }
    Some(out)
}

/// Walk `param_ty` (which may reference a type parameter, e.g.
/// `&mut T`, `[T]`, `Option<T>`, or bare `T`) alongside the concrete
/// `arg_ty` inferred at the call site, recording any type-parameter
/// bindings discovered (`T -> arg_ty`'s corresponding sub-type).
fn bind_type_param(param_ty: &TypeExpr, arg_ty: &HType, out: &mut HashMap<String, HType>) {
    match (param_ty, arg_ty) {
        (TypeExpr::Named(n), t) => {
            // Heuristic: a single uppercase-ish identifier that isn't a
            // known primitive type name is treated as a type parameter.
            // (A more rigorous version would check against
            // `generic_fn.type_params` directly — left to the caller via
            // the final `resolved.get(&tp.name)` lookup, which simply
            // won't find anything for non-type-parameter names, so this
            // over-approximation is harmless.)
            out.entry(n.clone()).or_insert_with(|| t.clone());
        }
        (TypeExpr::Ref(inner), HType::Ref(arg_inner)) |
        (TypeExpr::RefMut(inner), HType::RefMut(arg_inner)) |
        (TypeExpr::RefMut(inner), HType::Ref(arg_inner)) | // &mut T param, &T arg — still binds T
        (TypeExpr::Ref(inner), HType::RefMut(arg_inner)) => {
            bind_type_param(inner, arg_inner, out);
        }
        (TypeExpr::Array(inner), HType::Array(arg_inner)) => {
            bind_type_param(inner, arg_inner, out);
        }
        (TypeExpr::Optional(inner), HType::Optional(arg_inner)) => {
            bind_type_param(inner, arg_inner, out);
        }
        (TypeExpr::Generic(_, inner_params), arg_t) => {
            // e.g. param `Option<T>` vs arg type `HType::Optional(Box<HType>)`
            // or `HType::Named("Option")` with no sub-type info — best
            // effort: if arg_t is itself a single-level wrapper, recurse.
            if let Some(first) = inner_params.first() {
                match arg_t {
                    HType::Optional(inner) | HType::Array(inner) | HType::Ref(inner) | HType::RefMut(inner) =>
                    bind_type_param(first, inner, out),
                    _ => {}
                }
            }
        }
        _ => {}
    }
}

// ── 3. Substitution: clone + specialize generic items ────────────────────

fn instantiate_fn(generic_fn: &FnDef, mangled_name: &str, type_args: &[HType]) -> FnDef {
    let subst = build_subst_map(&generic_fn.type_params, type_args);
    let mut instance = generic_fn.clone();
    instance.name = mangled_name.to_string();
    instance.type_params = Vec::new(); // fully concrete now

    for param in instance.params.iter_mut() {
        substitute_type(&mut param.ty, &subst);
    }
    if let Some(ret) = instance.return_type.as_mut() {
        substitute_type(ret, &subst);
    }
    substitute_block_types(&mut instance.body, &subst);

    instance
}

fn instantiate_struct(generic_struct: &StructDef, mangled_name: &str, type_args: &[HType]) -> StructDef {
    let subst = build_subst_map(&generic_struct.type_params, type_args);
    let mut instance = generic_struct.clone();
    instance.name = mangled_name.to_string();
    instance.type_params = Vec::new();

    for field in instance.fields.iter_mut() {
        substitute_type(&mut field.ty, &subst);
    }

    instance
}

fn build_subst_map(type_params: &[TypeParam], type_args: &[HType]) -> HashMap<String, TypeExpr> {
    type_params.iter().zip(type_args.iter())
    .map(|(tp, ty)| (tp.name.clone(), htype_to_type_expr(ty)))
    .collect()
}

/// Convert an inferred `HType` back into a `TypeExpr` for splicing into the
/// instantiated AST (parameter types, return types, field types).
fn htype_to_type_expr(ty: &HType) -> TypeExpr {
    match ty {
        HType::Int => TypeExpr::Named("int".into()),
        HType::Uint => TypeExpr::Named("uint".into()),
        HType::I8 => TypeExpr::I8, HType::I16 => TypeExpr::I16,
        HType::I32 => TypeExpr::I32, HType::I64 => TypeExpr::I64, HType::I128 => TypeExpr::I128,
        HType::U8 => TypeExpr::U8, HType::U16 => TypeExpr::U16,
        HType::U32 => TypeExpr::U32, HType::U64 => TypeExpr::U64, HType::U128 => TypeExpr::U128,
        HType::F32 => TypeExpr::F32, HType::F64 => TypeExpr::F64,
        HType::Bool => TypeExpr::Bool,
        HType::Str => TypeExpr::String,
        HType::Bytes => TypeExpr::Bytes,
        HType::Void => TypeExpr::Void,
        HType::Any => TypeExpr::Named("any".into()),
        HType::Optional(inner) => TypeExpr::Optional(Box::new(htype_to_type_expr(inner))),
        HType::Array(inner)    => TypeExpr::Array(Box::new(htype_to_type_expr(inner))),
        HType::Tuple(items)    => TypeExpr::Tuple(items.iter().map(htype_to_type_expr).collect()),
        HType::Named(n)        => TypeExpr::Named(n.clone()),
        HType::Fn(p, r)        => TypeExpr::Fn(p.iter().map(htype_to_type_expr).collect(), Box::new(htype_to_type_expr(r))),
        HType::Ref(inner)      => TypeExpr::Ref(Box::new(htype_to_type_expr(inner))),
        HType::RefMut(inner)   => TypeExpr::RefMut(Box::new(htype_to_type_expr(inner))),
    }
}

/// Recursively replace `TypeExpr::Named(param_name)` (and nested
/// occurrences inside `Array`/`Optional`/`Ref`/etc.) per `subst`.
fn substitute_type(ty: &mut TypeExpr, subst: &HashMap<String, TypeExpr>) {
    match ty {
        TypeExpr::Named(n) => {
            if let Some(replacement) = subst.get(n) {
                *ty = replacement.clone();
            }
        }
        TypeExpr::Array(inner) | TypeExpr::Optional(inner) |
        TypeExpr::Ref(inner)   | TypeExpr::RefMut(inner) => substitute_type(inner, subst),
        TypeExpr::Tuple(items) => for i in items { substitute_type(i, subst); },
        TypeExpr::Generic(_, args) => for a in args { substitute_type(a, subst); },
        TypeExpr::Fn(params, ret) => {
            for p in params { substitute_type(p, subst); }
            substitute_type(ret, subst);
        }
        TypeExpr::Slice(inner, _) => substitute_type(inner, subst),
        _ => {}
    }
}

/// Substitute type-parameter references in every `let x: T = ...` and
/// `... as T` occurring within a function body being instantiated.
fn substitute_block_types(stmts: &mut [Stmt], subst: &HashMap<String, TypeExpr>) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::Let { ty: Some(t), value, .. } => {
                substitute_type(t, subst);
                if let Some(e) = value { substitute_expr_types(e, subst); }
            }
            Stmt::Let { value: Some(e), .. } => substitute_expr_types(e, subst),
            Stmt::Return(Some(e), _) | Stmt::Expr(e, _) | Stmt::Break(Some(e), _) =>
            substitute_expr_types(e, subst),
            _ => {}
        }
    }
}

fn substitute_expr_types(expr: &mut Expr, subst: &HashMap<String, TypeExpr>) {
    if let Expr::Cast(_, ty, _) = expr {
        substitute_type(ty, subst);
    }
    if let Expr::Closure { return_type: Some(rt), .. } = expr {
        substitute_type(rt, subst);
    }
    walk_sub_exprs_mut(expr, &mut |e| substitute_expr_types(e, subst));
    walk_sub_blocks_mut(expr, &mut |b| substitute_block_types(b, subst));
}

// ── Mangling ────────────────────────────────────────────────────────────

/// `[int, string]` -> `"int_string"`. Non-identifier characters (`&`, `[`,
/// `]`, spaces, `?`) in `HType::display()` are replaced with `_` to keep
/// the mangled name a valid identifier.
fn mangle_suffix(type_args: &[HType]) -> String {
    type_args.iter()
    .map(|t| sanitize_ident(&t.display()))
    .collect::<Vec<_>>()
    .join("_")
}

fn sanitize_ident(s: &str) -> String {
    s.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect()
}

// ── 5. Call-site rewriting ─────────────────────────────────────────────────

fn rewrite_item_calls(item: &mut Item, generic_fns: &HashMap<String, FnDef>, checker: &mut TypeChecker, stats: &mut MonoStats) {
    match item {
        // Same `local_types` tracking as `collect_generic_uses` above,
        // for the same reason: `infer_type_args` needs to agree with
        // what the collection pass already decided, or a call site gets
        // renamed to a specialization (e.g. `identity__Box`) that
        // collection never actually generated (it generated
        // `identity__any` instead, from the same cold-checker miss) —
        // turning a silent wrong-specialization bug into a hard
        // "undefined fn" one. Both passes must resolve the exact same
        // way, so this mirrors `collect_generic_uses` line for line.
        Item::FnDef(f) => {
            let mut local_types: HashMap<String, HType> = HashMap::new();
            for p in &f.params {
                local_types.insert(p.name.clone(), HType::from_type_expr(&p.ty));
            }
            rewrite_block_calls(&mut f.body, generic_fns, checker, stats, &mut local_types);
        }
        Item::ImplBlock(imp) => for m in &mut imp.methods {
            let mut local_types: HashMap<String, HType> = HashMap::new();
            local_types.insert("self".to_string(), HType::Named(imp.type_name.clone()));
            for p in &m.params {
                local_types.insert(p.name.clone(), HType::from_type_expr(&p.ty));
            }
            rewrite_block_calls(&mut m.body, generic_fns, checker, stats, &mut local_types);
        },
        Item::ModDecl { inline: Some(items), .. } => for it in items { rewrite_item_calls(it, generic_fns, checker, stats); },
        _ => {}
    }
}

fn rewrite_block_calls(stmts: &mut [Stmt], generic_fns: &HashMap<String, FnDef>, checker: &mut TypeChecker, stats: &mut MonoStats, local_types: &mut HashMap<String, HType>) {
    for stmt in stmts.iter_mut() {
        if let Stmt::Let { name, ty, value, .. } = stmt {
            let inferred = ty.as_ref().map(HType::from_type_expr)
                .or_else(|| value.as_ref().map(|e| checker.infer_expr_pub(e)));
            if let Some(t) = inferred {
                local_types.insert(name.clone(), t);
            }
        }
        match stmt {
            Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) |
            Stmt::Expr(e, _) | Stmt::Break(Some(e), _) =>
            rewrite_expr_calls(e, generic_fns, checker, stats, local_types),
            _ => {}
        }
    }
}

fn rewrite_expr_calls(expr: &mut Expr, generic_fns: &HashMap<String, FnDef>, checker: &mut TypeChecker, stats: &mut MonoStats, local_types: &mut HashMap<String, HType>) {
    if let Expr::Call(callee, args, _) = expr {
        if let Expr::Ident(name, ident_span) = callee.as_mut() {
            if let Some(generic_fn) = generic_fns.get(name.as_str()) {
                if let Some(type_args) = infer_type_args(generic_fn, args, checker, local_types) {
                    let suffix = mangle_suffix(&type_args);
                    *name = format!("{}__{}", name, suffix);
                    let _ = ident_span; // span preserved as-is
                    stats.call_sites_rewritten += 1;
                }
                // If inference failed here too, it was already recorded as
                // `unresolved` during collection — leave the call as-is;
                // features.rs will report it.
            }
        }
    }
    let mut local_types_owned = local_types.clone();
    walk_sub_exprs_mut(expr, &mut |e| rewrite_expr_calls(e, generic_fns, checker, stats, &mut local_types_owned));
    walk_sub_blocks_mut(expr, &mut |b| rewrite_block_calls(b, generic_fns, checker, stats, &mut local_types_owned));
}

// ── Generic AST walkers (shared) ────────────────────────────────────────────

/// Visit every direct sub-expression of `expr` (one level; recursion is the
/// caller's responsibility via repeated calls). Does NOT descend into
/// nested statement blocks — see `walk_sub_blocks`.
fn walk_sub_exprs(expr: &Expr, f: &mut impl FnMut(&Expr)) {
    match expr {
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { f(l); f(r); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => f(e),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { f(l); f(r); }
        Expr::FieldAccess(e, _, _) => f(e),
        Expr::IndexAccess(e, i, _) => { f(e); f(i); }
        Expr::MethodCall(recv, _, args, _) => { f(recv); for a in args { f(a); } }
        Expr::Call(callee, args, _) => { f(callee); for a in args { f(a); } }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => for e in elems { f(e); },
        Expr::StructLit(_, fields, _) => for (_, e) in fields { f(e); },
        Expr::Return(Some(e), _) => f(e),
        Expr::If { condition, .. } => f(condition),
        Expr::While { condition, .. } => f(condition),
        Expr::For { iterable, .. } => f(iterable),
        Expr::Match { subject, .. } => f(subject),
        _ => {}
    }
}

fn walk_sub_exprs_mut(expr: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
    match expr {
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) => { f(l); f(r); }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => f(e),
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => { f(l); f(r); }
        Expr::FieldAccess(e, _, _) => f(e),
        Expr::IndexAccess(e, i, _) => { f(e); f(i); }
        Expr::MethodCall(recv, _, args, _) => { f(recv); for a in args { f(a); } }
        Expr::Call(callee, args, _) => { f(callee); for a in args { f(a); } }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => for e in elems { f(e); },
        Expr::StructLit(_, fields, _) => for (_, e) in fields { f(e); },
        Expr::Return(Some(e), _) => f(e),
        Expr::If { condition, .. } => f(condition),
        Expr::While { condition, .. } => f(condition),
        Expr::For { iterable, .. } => f(iterable),
        Expr::Match { subject, .. } => f(subject),
        _ => {}
    }
}

/// Visit every nested STATEMENT BLOCK directly owned by `expr` (if/while/
/// for/match arms/closures/do/unsafe bodies). Used so block-level passes
/// (collect_in_block / rewrite_block_calls / substitute_block_types) reach
/// nested control flow without re-implementing the traversal.
fn walk_sub_blocks(expr: &Expr, f: &mut impl FnMut(&[Stmt])) {
    match expr {
        Expr::If { then_body, elsif_branches, else_body, .. } => {
            f(then_body);
            for (_, b) in elsif_branches { f(b); }
            if let Some(b) = else_body { f(b); }
        }
        Expr::While { body, .. } | Expr::For { body, .. } | Expr::Do { body, .. } => f(body),
        Expr::Match { arms, .. } => for arm in arms { f(&arm.body); },
        Expr::Closure { body, .. } => f(body),
        Expr::Unsafe(body, _, _) => f(body),
        _ => {}
    }
}

fn walk_sub_blocks_mut(expr: &mut Expr, f: &mut impl FnMut(&mut [Stmt])) {
    match expr {
        Expr::If { then_body, elsif_branches, else_body, .. } => {
            f(then_body);
            for (_, b) in elsif_branches { f(b); }
            if let Some(b) = else_body { f(b); }
        }
        Expr::While { body, .. } | Expr::For { body, .. } | Expr::Do { body, .. } => f(body),
        Expr::Match { arms, .. } => for arm in arms { f(&mut arm.body); },
        Expr::Closure { body, .. } => f(body),
        Expr::Unsafe(body, _, _) => f(body),
        _ => {}
    }
}
