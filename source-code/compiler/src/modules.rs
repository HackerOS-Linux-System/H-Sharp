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
        Self::with_extra_search_paths(source_file, Vec::new())
    }

    /// Same as `new`, but with additional directories inserted into the
    /// search path between "the declaring file's own directory" (always
    /// checked first) and "the current working directory" (always the
    /// last resort). This is what lets a `mod X` in one project resolve
    /// into *another* project's source tree — e.g. `isolated`'s
    /// `Bytes.hk` declaring `-> include => ../source-code/src`, so
    /// `isolated/src/main.h#`'s `mod config` (etc.) can resolve straight
    /// into `source-code/src/config.h#` without a physical copy ever
    /// existing under `isolated/`. See `hsharp-cli`'s `--include`/`-I`
    /// flag (`compile.rs`) for how a caller actually populates `extra`.
    pub fn with_extra_search_paths(source_file: &Path, extra: Vec<PathBuf>) -> Self {
        let mut search_paths = Vec::new();
        // 1. Directory of the source file
        if let Some(parent) = source_file.parent() {
            search_paths.push(parent.to_path_buf());
        }
        // 2. Explicit extra include directories (project-local shared
        //    source trees), in the order given.
        search_paths.extend(extra);
        // 3. Current working directory
        if let Ok(cwd) = std::env::current_dir() {
            search_paths.push(cwd);
        }
        Self { search_paths, cache: HashMap::new(), inlined_files: HashSet::new() }
    }

    /// Resolve one `use "std -> lib"` import: find and parse
    /// `/usr/lib/HackerOS/H#/std/{lib}.h#`, recursively resolve *its own*
    /// `use "std -> other"` imports and `mod` declarations, mangle its
    /// functions under `alias` (exactly like an external `mod alias`
    /// would be — see `mangle_module_items`), and return the resulting
    /// flat item list ready to append to the compiling program.
    ///
    /// This is the fix for the interpreter/AOT divergence documented at
    /// length elsewhere (see this crate's `lib.rs` and
    /// `hsharp-interpreter`'s `helpers.rs` module doc comments): before
    /// this existed, `use "std -> x"` was resolved *twice*, by two
    /// independent, hand-maintained mechanisms that could (and did)
    /// disagree — `hsharp-interpreter::interp::load_std_module` for the
    /// tree-walking interpreter, and a separate `segments.join("_")` ->
    /// `builtins_registry` lookup for the LLVM/AOT backend, which never
    /// looked at `std/*.h#` at all. Routing `std ->` through the exact
    /// same `ModuleResolver`/`mangle_module_items` machinery `mod`
    /// already used means both `hsharp preview` and `hsharp build` now
    /// compile the *same* inlined, mangled function bodies from the
    /// *same* `.h#` source file — one resolution path, not two.
    ///
    /// A missing std file is a hard `Err` (not a warning) with the exact
    /// "please install h# utils" wording — matching the policy already
    /// enforced by the typechecker's own `module.imports` check in
    /// `hsharp-typecheck`'s `checker/mod.rs` (which still runs too, as a
    /// defensive second check — see its doc comment — but by the time
    /// it runs, a genuinely missing std file will already have failed
    /// here first).
    pub fn resolve_std_import(&mut self, lib: &str, alias: &str) -> Result<Vec<Item>, String> {
        // NOTE: this literal must stay in sync with the identical
        // constants in `hsharp-interpreter::helpers::STD_LIB_ROOT` and
        // `hsharp-typecheck`'s `checker/mod.rs` — there's no single
        // shared crate all three live in to hold one real constant
        // instead, so this comment is the enforcement mechanism.
        let path = PathBuf::from("/usr/lib/HackerOS/H#/std").join(format!("{lib}.h#"));
        if !path.exists() {
            return Err(format!(
                "std module '{lib}' not found at {path}\n\n\
please install h# utils for HackerOS use:\n\
  linux:   hacker unpack h#-utils\n\
  windows: (not available yet — no install path is defined for Windows yet)\n",
                lib = lib, path = path.display(),
            ));
        }

        // Same "only inline once, program-wide" dedup `mod` resolution
        // already needs (see `inlined_files`'s doc comment) — a std lib
        // commonly gets `use`d from several different files (e.g. both
        // `cli.h#` and the user's own `main.h#` importing `std -> env`),
        // and its functions must still only end up in the compiled
        // program a single time.
        let canonical = std::fs::canonicalize(&path).unwrap_or_else(|_| path.clone());
        if !self.inlined_files.insert(canonical) {
            return Ok(Vec::new());
        }

        let src = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
        let result = hsharp_parser::parse(&src, path.to_str().unwrap_or(lib));
        if result.has_errors() {
            return Err(format!(
                "parse errors in std module '{}' ({}):\n{}",
                lib, path.display(), result.render_errors()
            ));
        }
        let sub_module = result.module;
        let sub_dir = path.parent().map(|p| p.to_path_buf()).unwrap_or_else(|| PathBuf::from("."));

        // This std file's own `use "std -> other"` imports, resolved
        // before its own functions are mangled/appended — so its
        // internal calls into another std module (e.g. `cli.h#` calling
        // into `env::args()`) see that other module already inlined.
        let mut out = Vec::new();
        for (kind, sub_alias, _span) in &sub_module.imports {
            if let ImportKind::Std { path: sub_path, .. } = kind {
                let sub_lib = sub_path.last().cloned().unwrap_or_default();
                if sub_lib.is_empty() { continue; }
                let ns = sub_alias.clone().unwrap_or_else(|| sub_lib.clone());
                out.extend(self.resolve_std_import(&sub_lib, &ns)?);
            }
        }

        // Mangle under this import's alias *before* recursing into any
        // `mod X` the std file itself declares (same ordering
        // `expand_module` uses for external `mod` files, for the same
        // reason: a nested `mod` needs to see its own name applied
        // independently, not double-prefixed).
        let mangled = mangle_module_items(sub_module.items, alias);
        let expanded = self.expand_module(mangled, &sub_dir)?;
        out.extend(expanded);
        Ok(out)
    }

    /// The single front-end entry point every caller (`hsharp preview`,
    /// `hsharp build`/`compile`, `hsharp check`) should use instead of
    /// calling `expand_module` directly: resolves this module's
    /// `use "std -> x"` imports (via `resolve_std_import`, above) *and*
    /// its `mod X` declarations (via `expand_module`), producing one
    /// flat, fully-inlined item list — the same one, regardless of which
    /// backend eventually compiles or interprets it.
    pub fn expand_program(&mut self, module: &Module, entry_dir: &Path) -> Result<Vec<Item>, String> {
        let mut items = Vec::new();
        for (kind, alias, _span) in &module.imports {
            if let ImportKind::Std { path, .. } = kind {
                let lib = path.last().cloned().unwrap_or_default();
                if lib.is_empty() { continue; }
                let ns = alias.clone().unwrap_or_else(|| lib.clone());
                items.extend(self.resolve_std_import(&lib, &ns)?);
            }
        }
        items.extend(self.expand_module(module.items.clone(), entry_dir)?);
        Ok(items)
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
    // Nested-fn hoisting only ever renames *function* references — a
    // nested `fn` can't itself declare a struct/enum type at that scope
    // (H#'s grammar only allows nested `fn`, not nested `struct`/`enum`),
    // so there's no local-types set to build here; pass an empty one
    // through to `rename_calls_in_stmts`'s now-shared signature (see
    // `mangle_module_items`'s doc comment for why that function grew a
    // `local_types` parameter in the first place).
    let no_types: HashSet<String> = HashSet::new();

    // Rewrite call sites in the (now nested-fn-stripped) enclosing body.
    rename_calls_in_stmts(body, &local_names, &no_types, enclosing_name);

    for mut f in nested_defs {
        // Nested fns can call their *siblings* (also declared in the same
        // enclosing body) by original bare name too — rewrite those.
        rename_calls_in_stmts(&mut f.body, &local_names, &no_types, enclosing_name);
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
/// Renames every top-level `fn`, `struct`, and `enum` in this batch of
/// items to `{prefix}_{name}` (matching the AOT backend's
/// `segments.join("_")` call-dispatch convention — see `codegen.rs`),
/// and rewrites every reference to one of them *within this same batch*
/// (calls, struct-literal construction, type annotations) to match.
///
/// Struct/enum renaming was added after a real bug surfaced in
/// practice: two different `std/*.h#` files (or the same file imported
/// under two different aliases) declaring a same-named struct — e.g.
/// `tcp.h#` and its now-former literal duplicate `net_tcp.h#` both
/// declaring `struct TcpStream` — would inline as two distinct
/// `Item::StructDef`s with the identical name `"TcpStream"`, since only
/// *functions* used to get mangled here. That specific duplication was
/// fixed at the source (`net_tcp.h#`/`net_http.h#` now delegate instead
/// of duplicating — see those files' module doc comments), but the
/// underlying capability gap remained: nothing stopped the *next*
/// two std files (or two unrelated third-party H# packages) from
/// declaring the same struct/enum name and colliding the same way.
/// Namespacing struct/enum names the same way functions already were
/// closes that gap generally, not just for the one collision that
/// happened to be found by hand.
///
/// Known remaining limitation: this does NOT rewrite `Pattern::Struct`/
/// `Pattern::Enum` (destructuring a struct or matching an enum variant
/// in a `match` arm) — those still reference the *original* type name.
/// This is safe-but-incomplete rather than silently wrong: a local
/// struct/enum that's only ever constructed and field-accessed (which
/// covers every struct in this stdlib today — plain data records, no
/// pattern-matched enums) mangles correctly; one that's pattern-matched
/// would need that additional rewrite too, and will currently fail to
/// typecheck/resolve loudly (a clear "unknown type" error) rather than
/// silently binding to the wrong type, if that gap is ever hit.
fn mangle_module_items(items: Vec<Item>, prefix: &str) -> Vec<Item> {
    let local_fns: HashSet<String> = items.iter().filter_map(|i| match i {
        Item::FnDef(f) => Some(f.name.clone()),
        _ => None,
    }).collect();
    let local_types: HashSet<String> = items.iter().filter_map(|i| match i {
        Item::StructDef(s) => Some(s.name.clone()),
        Item::EnumDef(e) => Some(e.name.clone()),
        _ => None,
    }).collect();

    if local_fns.is_empty() && local_types.is_empty() {
        return items;
    }

    items.into_iter().map(|item| match item {
        Item::FnDef(mut f) => {
            rename_calls_in_stmts(&mut f.body, &local_fns, &local_types, prefix);
            for p in f.params.iter_mut() {
                rename_type_expr(&mut p.ty, &local_types, prefix);
            }
            if let Some(rt) = f.return_type.as_mut() {
                rename_type_expr(rt, &local_types, prefix);
            }
            f.name = format!("{}_{}", prefix, f.name);
            Item::FnDef(f)
        }
        Item::StructDef(mut s) => {
            s.name = format!("{}_{}", prefix, s.name);
            // A field whose type is *another* locally-defined struct/enum
            // (e.g. `struct Cache { ..., entries: [Entry] }` where `Entry`
            // is declared in the same file) needs that reference renamed
            // too, or it'll point at the pre-mangling name.
            for field in s.fields.iter_mut() {
                rename_type_expr(&mut field.ty, &local_types, prefix);
            }
            Item::StructDef(s)
        }
        Item::EnumDef(mut e) => {
            e.name = format!("{}_{}", prefix, e.name);
            for variant in e.variants.iter_mut() {
                match &mut variant.fields {
                    EnumVariantFields::Unit => {}
                    EnumVariantFields::Tuple(tys) => {
                        for ty in tys.iter_mut() { rename_type_expr(ty, &local_types, prefix); }
                    }
                    EnumVariantFields::Struct(fields) => {
                        for f in fields.iter_mut() { rename_type_expr(&mut f.ty, &local_types, prefix); }
                    }
                }
            }
            Item::EnumDef(e)
        }
        Item::ImplBlock(mut imp) => {
            if local_types.contains(&imp.type_name) {
                imp.type_name = format!("{}_{}", prefix, imp.type_name);
            }
            for m in imp.methods.iter_mut() {
                rename_calls_in_stmts(&mut m.body, &local_fns, &local_types, prefix);
                for p in m.params.iter_mut() {
                    rename_type_expr(&mut p.ty, &local_types, prefix);
                }
                if let Some(rt) = m.return_type.as_mut() {
                    rename_type_expr(rt, &local_types, prefix);
                }
            }
            Item::ImplBlock(imp)
        }
        other => other,
    }).collect()
}

/// Recursively rewrites any `TypeExpr::Named(name)` matching a local
/// struct/enum, anywhere inside `ty` (through arrays, slices, tuples,
/// optionals, refs, fn types, and generic type arguments).
fn rename_type_expr(ty: &mut TypeExpr, local_types: &HashSet<String>, prefix: &str) {
    match ty {
        TypeExpr::Named(n) => {
            if local_types.contains(n.as_str()) {
                *n = format!("{}_{}", prefix, n);
            }
        }
        TypeExpr::Generic(n, args) => {
            if local_types.contains(n.as_str()) {
                *n = format!("{}_{}", prefix, n);
            }
            for a in args.iter_mut() { rename_type_expr(a, local_types, prefix); }
        }
        TypeExpr::Array(inner) | TypeExpr::Slice(inner, _) | TypeExpr::Optional(inner) |
        TypeExpr::Ref(inner) | TypeExpr::RefMut(inner) => {
            rename_type_expr(inner, local_types, prefix);
        }
        TypeExpr::Tuple(elems) => {
            for e in elems.iter_mut() { rename_type_expr(e, local_types, prefix); }
        }
        TypeExpr::Fn(params, ret) => {
            for p in params.iter_mut() { rename_type_expr(p, local_types, prefix); }
            rename_type_expr(ret, local_types, prefix);
        }
        TypeExpr::Void | TypeExpr::I8 | TypeExpr::I16 | TypeExpr::I32 | TypeExpr::I64 | TypeExpr::I128 |
        TypeExpr::U8 | TypeExpr::U16 | TypeExpr::U32 | TypeExpr::U64 | TypeExpr::U128 |
        TypeExpr::F32 | TypeExpr::F64 | TypeExpr::Bool | TypeExpr::String | TypeExpr::Bytes => {}
    }
}

fn rename_calls_in_stmts(stmts: &mut [Stmt], local_fns: &HashSet<String>, local_types: &HashSet<String>, prefix: &str) {
    for s in stmts.iter_mut() {
        rename_calls_in_stmt(s, local_fns, local_types, prefix);
    }
}

fn rename_calls_in_stmt(stmt: &mut Stmt, local_fns: &HashSet<String>, local_types: &HashSet<String>, prefix: &str) {
    match stmt {
        Stmt::Let { value: Some(e), ty, .. } => {
            rename_calls_in_expr(e, local_fns, local_types, prefix);
            if let Some(t) = ty { rename_type_expr(t, local_types, prefix); }
        }
        Stmt::Let { value: None, ty: Some(t), .. } => rename_type_expr(t, local_types, prefix),
        Stmt::Expr(e, _)                   => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Stmt::Return(Some(e), _)           => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Stmt::Break(Some(e), _)           => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Stmt::Item(Item::FnDef(f)) => {
            // Nested/local function def: its body can still call the
            // enclosing module's top-level functions unqualified, but the
            // nested fn itself isn't a top-level module symbol, so it's
            // not renamed here.
            rename_calls_in_stmts(&mut f.body, local_fns, local_types, prefix);
            for p in f.params.iter_mut() { rename_type_expr(&mut p.ty, local_types, prefix); }
            if let Some(rt) = f.return_type.as_mut() { rename_type_expr(rt, local_types, prefix); }
        }
        Stmt::Let { value: None, ty: None, .. } | Stmt::Return(None, _) | Stmt::Break(None, _) |
        Stmt::Continue(_) | Stmt::Import(..) | Stmt::Item(_) => {}
    }
}

fn rename_calls_in_expr(expr: &mut Expr, local_fns: &HashSet<String>, local_types: &HashSet<String>, prefix: &str) {
    match expr {
        Expr::Call(callee, args, _) => {
            match &mut **callee {
                Expr::Ident(name, _) if local_fns.contains(name.as_str()) => {
                    *name = format!("{}_{}", prefix, name);
                }
                other => rename_calls_in_expr(other, local_fns, local_types, prefix),
            }
            for a in args.iter_mut() { rename_calls_in_expr(a, local_fns, local_types, prefix); }
        }
        Expr::MethodCall(recv, _, args, _) => {
            rename_calls_in_expr(recv, local_fns, local_types, prefix);
            for a in args.iter_mut() { rename_calls_in_expr(a, local_fns, local_types, prefix); }
        }
        Expr::BinOp(l, _, r, _) | Expr::Range(l, r, _, _) |
        Expr::Assign(l, r, _) | Expr::CompoundAssign(l, _, r, _) => {
            rename_calls_in_expr(l, local_fns, local_types, prefix);
            rename_calls_in_expr(r, local_fns, local_types, prefix);
        }
        Expr::UnOp(_, e, _) => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Expr::Cast(e, t, _) => {
            rename_calls_in_expr(e, local_fns, local_types, prefix);
            rename_type_expr(t, local_types, prefix);
        }
        Expr::Try(e, _) | Expr::Await(e, _) => {
            rename_calls_in_expr(e, local_fns, local_types, prefix);
        }
        Expr::FieldAccess(e, _, _) => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Expr::IndexAccess(e, i, _) => {
            rename_calls_in_expr(e, local_fns, local_types, prefix);
            rename_calls_in_expr(i, local_fns, local_types, prefix);
        }
        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => {
            for e in elems.iter_mut() { rename_calls_in_expr(e, local_fns, local_types, prefix); }
        }
        // The one genuinely new rewrite this whole pass exists for:
        // `Config { path: ..., values: ... }` constructing a *local*
        // struct needs to become `alias_Config { ... }` to match its
        // now-mangled `Item::StructDef`, or codegen/typecheck would look
        // up a struct definition that no longer exists under that name.
        Expr::StructLit(name, fields, _) => {
            if local_types.contains(name.as_str()) {
                *name = format!("{}_{}", prefix, name);
            }
            for (_, e) in fields.iter_mut() { rename_calls_in_expr(e, local_fns, local_types, prefix); }
        }
        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            rename_calls_in_expr(condition, local_fns, local_types, prefix);
            rename_calls_in_stmts(then_body, local_fns, local_types, prefix);
            for (cond, body) in elsif_branches.iter_mut() {
                rename_calls_in_expr(cond, local_fns, local_types, prefix);
                rename_calls_in_stmts(body, local_fns, local_types, prefix);
            }
            if let Some(body) = else_body {
                rename_calls_in_stmts(body, local_fns, local_types, prefix);
            }
        }
        Expr::Match { subject, arms, .. } => {
            rename_calls_in_expr(subject, local_fns, local_types, prefix);
            for arm in arms.iter_mut() {
                if let Some(g) = &mut arm.guard { rename_calls_in_expr(g, local_fns, local_types, prefix); }
                rename_calls_in_stmts(&mut arm.body, local_fns, local_types, prefix);
            }
        }
        Expr::While { condition, body, .. } => {
            rename_calls_in_expr(condition, local_fns, local_types, prefix);
            rename_calls_in_stmts(body, local_fns, local_types, prefix);
        }
        Expr::For { iterable, body, .. } => {
            rename_calls_in_expr(iterable, local_fns, local_types, prefix);
            rename_calls_in_stmts(body, local_fns, local_types, prefix);
        }
        Expr::Do { body, .. }      => rename_calls_in_stmts(body, local_fns, local_types, prefix),
        Expr::Closure { body, .. } => rename_calls_in_stmts(body, local_fns, local_types, prefix),
        Expr::Unsafe(body, _, _)   => rename_calls_in_stmts(body, local_fns, local_types, prefix),
        Expr::Return(Some(e), _)   => rename_calls_in_expr(e, local_fns, local_types, prefix),
        Expr::Literal(..) | Expr::Ident(..) | Expr::SelfExpr(_) |
        Expr::Path(..) | Expr::Return(None, _) => {}
    }
}
