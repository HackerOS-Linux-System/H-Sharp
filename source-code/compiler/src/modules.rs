use std::path::{Path, PathBuf};
use std::collections::{HashMap, HashSet};
use hsharp_parser::ast::*;

/// Resolved module: parsed AST + source path
pub struct ResolvedModule {
    pub path:  PathBuf,
    pub items: Vec<Item>,
}

/// Module resolver: loads and caches H# source files
pub struct ModuleResolver {
    /// Fallback search paths (entry file's directory, then cwd) — used when
    /// a `mod X` can't be found relative to the directory of the file that
    /// declared it.
    pub search_paths: Vec<PathBuf>,
    /// Cache of already-attempted resolutions, keyed by
    /// `(declaring file's directory, mod name)` so the *same* failed or
    /// successful lookup from the *same* directory isn't redone (and, for
    /// failures, re-warned about) every time another file also declares
    /// `mod X`. Different directories intentionally get separate cache
    /// entries — `mod helpers` from two different subdirectories can
    /// legitimately resolve to two different files.
    cache: HashMap<(PathBuf, String), Result<(Vec<Item>, PathBuf), String>>,
    /// Absolute paths of files that have already been fully expanded and
    /// inlined into the output *once*, program-wide. A module commonly gets
    /// `mod`-declared from several different files (e.g. `mod registry`
    /// from both `cli.h#` and `deps.h#`) — its definitions must still only
    /// end up in the compiled program a single time. Without this, each
    /// `mod registry` re-inlines a full copy of registry.h#'s functions,
    /// giving the LLVM module several functions with the identical
    /// (mangled) name — which corrupts codegen (duplicate/stale
    /// `FunctionValue` bindings) badly enough to crash the compiler itself.
    inlined_files: HashSet<PathBuf>,
}

impl ModuleResolver {
    pub fn new(source_file: &Path) -> Self {
        let mut search_paths = Vec::new();
        // 1. Directory of the source file
        if let Some(parent) = source_file.parent() {
            search_paths.push(parent.to_path_buf());
        }
        // 2. Current working directory
        if let Ok(cwd) = std::env::current_dir() {
            search_paths.push(cwd);
        }
        Self { search_paths, cache: HashMap::new(), inlined_files: HashSet::new() }
    }

    /// Resolve `mod name` → find and parse name.h#, name/mod.h#, or
    /// name/main.h#, searching `from_dir` (the directory of the file that
    /// declared this `mod`) first, then falling back to the entry file's
    /// directory and the cwd. Returns the parsed items and the *file*
    /// they came from (its directory is what the caller should recurse
    /// with as the new `from_dir` for any `mod` declarations inside it).
    fn resolve(&mut self, mod_name: &str, from_dir: &Path) -> Result<(Vec<Item>, PathBuf), String> {
        let key = (from_dir.to_path_buf(), mod_name.to_string());
        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }
        let result = self.load(mod_name, from_dir);
        self.cache.insert(key, result.clone());
        result
    }

    /// Returns the parsed items and the resolved *file path* (not its
    /// directory — callers that need the directory call `.parent()`).
    fn load(&self, mod_name: &str, from_dir: &Path) -> Result<(Vec<Item>, PathBuf), String> {
        // Try: name.h#, name/mod.h#, name/main.h#
        let candidates = [
            format!("{}.h#", mod_name),
            format!("{}/mod.h#", mod_name),
            format!("{}/main.h#", mod_name),
        ];
        // Search the declaring file's own directory first — this is what
        // makes nested directory modules work (e.g. `translations/main.h#`
        // declaring `mod pl` must find `translations/pl.h#`, not go looking
        // relative to the *entry* file's directory). Fall back to the
        // entry-file directory / cwd for the common case of every module
        // living flat alongside the entry point.
        let mut dirs: Vec<&Path> = vec![from_dir];
        for p in &self.search_paths {
            if p.as_path() != from_dir {
                dirs.push(p.as_path());
            }
        }
        for dir in dirs {
            for candidate in &candidates {
                let path = dir.join(candidate);
                if path.exists() {
                    let src = std::fs::read_to_string(&path)
                        .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
                    let result = hsharp_parser::parse(&src, path.to_str().unwrap_or("?"));
                    if result.has_errors() {
                        return Err(format!("parse errors in {}: {}", path.display(), result.render_errors()));
                    }
                    let mut sub_module = result.module;
                    // Each resolved file gets its *own* `@: mode` directive
                    // applied here, before its items get merged into the
                    // caller's item list — `lib.rs::compile`'s top-level
                    // `apply_file_mem_mode` call only ever sees the *entry*
                    // file's directive (this function returns bare `Vec<Item>`,
                    // discarding `sub_module.file_mem_mode` otherwise), so
                    // without this, `use`d files' own `@:` lines would be
                    // silently ignored — the directive would only ever work
                    // for the one file `hsharp compile`/`build` was pointed
                    // at directly, not for anything it pulls in.
                    if let Some(mode) = sub_module.file_mem_mode {
                        for item in &mut sub_module.items {
                            hsharp_parser::ast::apply_file_mem_mode_item(item, mode);
                        }
                    }
                    // Canonicalize so the same file reached via different
                    // relative paths (e.g. from two different declaring
                    // directories) is recognized as the same file by
                    // `inlined_files`. Falls back to the plain joined path
                    // if canonicalization fails for some reason.
                    let resolved_path = std::fs::canonicalize(&path).unwrap_or(path);
                    return Ok((sub_module.items, resolved_path));
                }
            }
        }
        let mut searched: Vec<String> = vec![from_dir.display().to_string()];
        searched.extend(self.search_paths.iter().map(|p| p.display().to_string()));
        Err(format!(
            "module '{}' not found\n  Searched: {}\n  Expected: {}.h#",
            mod_name,
            searched.join(", "),
            mod_name
        ))
    }

    /// Expand all ModDecl items in a module, inlining external modules.
    /// `current_dir` is the directory of the file `items` came from — any
    /// `mod X` found in `items` is resolved relative to it first.
    pub fn expand_module(&mut self, items: Vec<Item>, current_dir: &Path) -> Result<Vec<Item>, String> {
        let mut expanded = Vec::new();
        for item in items {
            match item {
                Item::ModDecl { name, pub_: _, inline: Some(inline_items), .. } => {
                    // Inline module: mangle this file-level item set's own
                    // function names *before* recursing, so any further
                    // nested `mod` inside it gets mangled independently
                    // with its own name (no double-prefixing).
                    let mangled = mangle_module_items(inline_items, &name);
                    let sub = self.expand_module(mangled, current_dir)?;
                    expanded.extend(sub);
                }
                Item::ModDecl { name, pub_: _mod_pub, inline: None, .. } => {
                    // External module: load file. Every item is inlined
                    // regardless of its own `pub` marker — codegen needs the
                    // full item set to compile the program either way, and
                    // there's no cross-module privacy *enforcement* (that
                    // would be a typechecker diagnostic: "field/fn `x` is
                    // private to module `y`") implemented yet.
                    match self.resolve(&name, current_dir) {
                        Ok((raw_items, resolved_file)) => {
                            // A module can be (and commonly is) `mod`-
                            // declared from several different files. Its
                            // contents must still only end up in the
                            // compiled program once — otherwise every
                            // extra `mod registry` (say) inlines another
                            // full copy of registry.h#'s functions under
                            // the *same* mangled names, giving the LLVM
                            // module duplicate function definitions that
                            // corrupt codegen. `resolve()`'s cache already
                            // avoids re-parsing the file, but a cache hit
                            // still returned a fresh copy of the items
                            // here, which we'd then merrily re-inline —
                            // this check is what actually stops that.
                            if !self.inlined_files.insert(resolved_file.clone()) {
                                continue;
                            }
                            let resolved_dir = resolved_file.parent()
                                .map(|p| p.to_path_buf())
                                .unwrap_or_else(|| current_dir.to_path_buf());
                            // Mangle *before* recursing (see comment above).
                            let mangled = mangle_module_items(raw_items, &name);
                            let sub = self.expand_module(mangled, &resolved_dir)?;
                            expanded.extend(sub);
                        }
                        Err(e) => {
                            // Non-fatal: emit warning but continue. Cached
                            // in `resolve()`, so this only prints once per
                            // (directory, name) pair no matter how many
                            // different files declare the same missing/
                            // broken `mod X`.
                            eprintln!("warn: {}", e);
                        }
                    }
                }
                other => expanded.push(other),
            }
        }
        Ok(expanded)
    }
}

/// Find and hoist any locally-declared functions (`fn foo() is ... end`
/// written inside another function's body) out to top level, renaming them
/// `{enclosing_name}_{foo}` and rewriting call sites within `body` to
/// match — the same trick `mangle_module_items` uses for same-named
/// functions across different files. Recurses so a nested fn that itself
/// contains a further-nested fn gets hoisted correctly too (with a fully
/// qualified name like `outer_middle_inner`).
///
/// This only handles the *lambda-lifting-safe* case: a nested function
/// that doesn't reference any of the enclosing function's locals/params —
/// only its own params/locals and module-level names. We don't check for
/// that here; a nested fn that *does* capture an outer variable will just
/// fail to resolve that identifier once hoisted (a codegen "undefined
/// var" error), since hoisting to top level removes access to the
/// enclosing scope. Real closures (capturing an environment) are a
/// separate, larger feature.
pub fn hoist_nested_fns(body: &mut Vec<Stmt>, enclosing_name: &str) -> Vec<FnDef> {
    let mut hoisted = Vec::new();

    // Pull nested `Item::FnDef` statements out of the body, in order,
    // leaving every other statement (including non-FnDef items) in place.
    let mut nested_defs: Vec<FnDef> = Vec::new();
    body.retain(|s| {
        if let Stmt::Item(Item::FnDef(f)) = s {
            nested_defs.push(f.clone());
            false
        } else {
            true
        }
    });

    if nested_defs.is_empty() {
        return hoisted;
    }

    let local_names: HashSet<String> = nested_defs.iter().map(|f| f.name.clone()).collect();

    // Rewrite call sites in the (now nested-fn-stripped) enclosing body.
    rename_calls_in_stmts(body, &local_names, enclosing_name);

    for mut f in nested_defs {
        // Nested fns can call their *siblings* (also declared in the same
        // enclosing body) by original bare name too — rewrite those.
        rename_calls_in_stmts(&mut f.body, &local_names, enclosing_name);
        let new_name = format!("{}_{}", enclosing_name, f.name);
        // Recurse for doubly-nested functions, using this fn's own new
        // (already mangled) name as the next prefix.
        let deeper = hoist_nested_fns(&mut f.body, &new_name);
        f.name = new_name;
        hoisted.push(f);
        hoisted.extend(deeper);
    }

    hoisted
}
/// and rewrite every unqualified call site *within this same item set* to
/// use the new mangled name, so intra-module calls keep resolving.
///
/// Without this, two files each defining a same-named helper (very common:
/// `find_hsh`, `capture`, `cmd_add`, `collect_hsharp_files` all collided in
/// one real project) silently overwrite each other in `func_vals` — and
/// when they don't even share a signature, `compile_fn` ends up binding one
/// function's body against a *different* function's LLVM parameter list,
/// which panics (`get_nth_param` out of range) or silently miscompiles.
/// Mangling gives every module-level function a name that's unique across
/// the whole program, matching the mangled name our call dispatch
/// (`module::function` -> `module_function`) already tries first.
fn mangle_module_items(items: Vec<Item>, prefix: &str) -> Vec<Item> {
    let local_fns: HashSet<String> = items.iter().filter_map(|i| match i {
        Item::FnDef(f) => Some(f.name.clone()),
        _ => None,
    }).collect();

    if local_fns.is_empty() {
        return items;
    }

    items.into_iter().map(|item| match item {
        Item::FnDef(mut f) => {
            rename_calls_in_stmts(&mut f.body, &local_fns, prefix);
            f.name = format!("{}_{}", prefix, f.name);
            Item::FnDef(f)
        }
        other => other,
    }).collect()
}

fn rename_calls_in_stmts(stmts: &mut [Stmt], local_fns: &HashSet<String>, prefix: &str) {
    for s in stmts.iter_mut() {
        rename_calls_in_stmt(s, local_fns, prefix);
    }
}

fn rename_calls_in_stmt(stmt: &mut Stmt, local_fns: &HashSet<String>, prefix: &str) {
    match stmt {
        Stmt::Let { value: Some(e), .. }   => rename_calls_in_expr(e, local_fns, prefix),
        Stmt::Expr(e, _)                   => rename_calls_in_expr(e, local_fns, prefix),
        Stmt::Return(Some(e), _)           => rename_calls_in_expr(e, local_fns, prefix),
        Stmt::Break(Some(e), _)           => rename_calls_in_expr(e, local_fns, prefix),
        Stmt::Item(Item::FnDef(f)) => {
            // Nested/local function def: its body can still call the
            // enclosing module's top-level functions unqualified, but the
            // nested fn itself isn't a top-level module symbol, so it's
            // not renamed here.
            rename_calls_in_stmts(&mut f.body, local_fns, prefix);
        }
        Stmt::Let { value: None, .. } | Stmt::Return(None, _) | Stmt::Break(None, _) |
        Stmt::Continue(_) | Stmt::Import(..) | Stmt::Item(_) => {}
    }
}

fn rename_calls_in_expr(expr: &mut Expr, local_fns: &HashSet<String>, prefix: &str) {
    match expr {
        Expr::Call(callee, args, _) => {
            match &mut **callee {
                Expr::Ident(name, _) if local_fns.contains(name.as_str()) => {
                    *name = format!("{}_{}", prefix, name);
                }
                other => rename_calls_in_expr(other, local_fns, prefix),
            }
            for a in args.iter_mut() { rename_calls_in_expr(a, local_fns, prefix); }
        }
        Expr::MethodCall(recv, _, args, _) => {
            rename_calls_in_expr(recv, local_fns, prefix);
            for a in args.iter_mut() { rename_calls_in_expr(a, local_fns, prefix); }
        }
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) |
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => {
            rename_calls_in_expr(l, local_fns, prefix);
            rename_calls_in_expr(r, local_fns, prefix);
        }
        Expr::UnOp(_, e, _) | Expr::Cast(e, _, _) | Expr::Try(e, _) | Expr::Await(e, _) => {
            rename_calls_in_expr(e, local_fns, prefix);
        }
        Expr::FieldAccess(e, _, _) => rename_calls_in_expr(e, local_fns, prefix),
        Expr::IndexAccess(e, i, _) => {
            rename_calls_in_expr(e, local_fns, prefix);
            rename_calls_in_expr(i, local_fns, prefix);
        }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => {
            for e in elems.iter_mut() { rename_calls_in_expr(e, local_fns, prefix); }
        }
        Expr::StructLit(_, fields, _) => {
            for (_, e) in fields.iter_mut() { rename_calls_in_expr(e, local_fns, prefix); }
        }
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            rename_calls_in_expr(condition, local_fns, prefix);
            rename_calls_in_stmts(then_body, local_fns, prefix);
            for (cond, body) in elsif_branches.iter_mut() {
                rename_calls_in_expr(cond, local_fns, prefix);
                rename_calls_in_stmts(body, local_fns, prefix);
            }
            if let Some(body) = else_body {
                rename_calls_in_stmts(body, local_fns, prefix);
            }
        }
        Expr::Match { subject, arms, .. } => {
            rename_calls_in_expr(subject, local_fns, prefix);
            for arm in arms.iter_mut() {
                if let Some(g) = &mut arm.guard { rename_calls_in_expr(g, local_fns, prefix); }
                rename_calls_in_stmts(&mut arm.body, local_fns, prefix);
            }
        }
        Expr::While { condition, body, .. } => {
            rename_calls_in_expr(condition, local_fns, prefix);
            rename_calls_in_stmts(body, local_fns, prefix);
        }
        Expr::For { iterable, body, .. } => {
            rename_calls_in_expr(iterable, local_fns, prefix);
            rename_calls_in_stmts(body, local_fns, prefix);
        }
        Expr::Do { body, .. }      => rename_calls_in_stmts(body, local_fns, prefix),
        Expr::Closure { body, .. } => rename_calls_in_stmts(body, local_fns, prefix),
        Expr::Unsafe(body, _, _)   => rename_calls_in_stmts(body, local_fns, prefix),
        Expr::Return(Some(e), _)   => rename_calls_in_expr(e, local_fns, prefix),
        Expr::Literal(..) | Expr::Ident(..) | Expr::SelfExpr(_) |
        Expr::Path(..) | Expr::Return(None, _) => {}
    }
}
