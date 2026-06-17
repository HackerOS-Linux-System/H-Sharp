use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::typechecker::{HType, TypeChecker};

pub struct MonoStats {
    pub instances_generated: usize,
    pub call_sites_rewritten: usize,
    pub unresolved: Vec<(String, Span)>,
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
    let mut stats = MonoStats { instances_generated: 0, call_sites_rewritten: 0, unresolved: Vec::new() };

    // Seed the worklist from concrete items.
    for item in &concrete_items {
        collect_generic_uses(item, &generic_fns, checker, &mut worklist, &mut stats);
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
            collect_generic_uses(&inst_item, &generic_fns, checker, &mut worklist, &mut stats);
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
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                        stats: &mut MonoStats,
) {
    match item {
        Item::FnDef(f) => collect_in_block(&f.body, generic_fns, checker, worklist, stats),
        Item::ImplBlock(imp) => for m in &imp.methods { collect_in_block(&m.body, generic_fns, checker, worklist, stats); },
        Item::ModDecl { inline: Some(items), .. } => for it in items { collect_generic_uses(it, generic_fns, checker, worklist, stats); },
        _ => {}
    }
}

fn collect_in_block(
    stmts: &[Stmt],
    generic_fns: &HashMap<String, FnDef>,
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                    stats: &mut MonoStats,
) {
    for stmt in stmts {
        match stmt {
            Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) | Stmt::Expr(e, _) =>
            collect_in_expr(e, generic_fns, checker, worklist, stats),
            _ => {}
        }
    }
}

fn collect_in_expr(
    expr: &Expr,
    generic_fns: &HashMap<String, FnDef>,
    checker: &mut TypeChecker,
    worklist: &mut VecDeque<(String, Vec<HType>)>,
                   stats: &mut MonoStats,
) {
    if let Expr::Call(callee, args, span) = expr {
        if let Expr::Ident(name, _) = callee.as_ref() {
            if let Some(generic_fn) = generic_fns.get(name) {
                match infer_type_args(generic_fn, args, checker) {
                    Some(type_args) => worklist.push_back((name.clone(), type_args)),
                    None => stats.unresolved.push((name.clone(), span.clone())),
                }
            }
        }
    }
    // Recurse into all sub-expressions (best-effort generic coverage,
    // including nested blocks).
    walk_sub_exprs(expr, &mut |e| collect_in_expr(e, generic_fns, checker, worklist, stats));
    walk_sub_blocks(expr, &mut |b| collect_in_block(b, generic_fns, checker, worklist, stats));
}

/// Infer concrete `HType`s for each of `generic_fn.type_params`, by matching
/// each parameter's declared type (`TypeExpr::Named(param_name)`) against
/// the inferred type of the corresponding *argument expression* at the call
/// site.
///
/// Returns `None` if any type parameter couldn't be pinned down from the
/// arguments (e.g. it only appears in the return type) — the caller records
/// this as `unresolved` for `features.rs` to report.
fn infer_type_args(generic_fn: &FnDef, call_args: &[Expr], checker: &mut TypeChecker) -> Option<Vec<HType>> {
    let mut resolved: HashMap<String, HType> = HashMap::new();

    for (param, arg_expr) in generic_fn.params.iter().zip(call_args.iter()) {
        let arg_ty = checker.infer_expr_pub(arg_expr);
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
        Item::FnDef(f) => rewrite_block_calls(&mut f.body, generic_fns, checker, stats),
        Item::ImplBlock(imp) => for m in &mut imp.methods { rewrite_block_calls(&mut m.body, generic_fns, checker, stats); },
        Item::ModDecl { inline: Some(items), .. } => for it in items { rewrite_item_calls(it, generic_fns, checker, stats); },
        _ => {}
    }
}

fn rewrite_block_calls(stmts: &mut [Stmt], generic_fns: &HashMap<String, FnDef>, checker: &mut TypeChecker, stats: &mut MonoStats) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::Let { value: Some(e), .. } | Stmt::Return(Some(e), _) |
            Stmt::Expr(e, _) | Stmt::Break(Some(e), _) =>
            rewrite_expr_calls(e, generic_fns, checker, stats),
            _ => {}
        }
    }
}

fn rewrite_expr_calls(expr: &mut Expr, generic_fns: &HashMap<String, FnDef>, checker: &mut TypeChecker, stats: &mut MonoStats) {
    if let Expr::Call(callee, args, _) = expr {
        if let Expr::Ident(name, ident_span) = callee.as_mut() {
            if let Some(generic_fn) = generic_fns.get(name.as_str()) {
                if let Some(type_args) = infer_type_args(generic_fn, args, checker) {
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
    walk_sub_exprs_mut(expr, &mut |e| rewrite_expr_calls(e, generic_fns, checker, stats));
    walk_sub_blocks_mut(expr, &mut |b| rewrite_block_calls(b, generic_fns, checker, stats));
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
