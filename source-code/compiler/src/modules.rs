use std::path::{Path, PathBuf};
use std::collections::{HashMap, HashSet};
use hsharp_parser::ast::*;
use hsharp_parser::span::Span;
use crate::bytes_resolve;

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
    cache: HashMap<(PathBuf, String), Result<(Vec<Item>, Vec<(ImportKind, Option<String>, Span)>, PathBuf), String>>,
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

    /// Resolve one `use "bytes -> name[/version]"` (or `dynamic use
    /// "bytes -> name[/version]"`) import: find the package in the
    /// on-disk cache(s) the `bytes` package manager fills in, parse its
    /// entry file, recursively resolve *its* own `use`/`mod` declarations,
    /// mangle its items under `alias` (exactly like `resolve_std_import`
    /// does for a std file), and return the resulting flat item list.
    ///
    /// Static and Dynamic links diverge here in a way they don't for the
    /// tree-walking interpreter (see `hsharp-interpreter::interp`'s
    /// `load_bytes_module` doc comment): a `Static` (the default) import
    /// genuinely gets its code baked into the compiled binary, so it's
    /// resolved and inlined exactly like a std/`mod` file. A `Dynamic`
    /// import's whole contract (`ast.rs`'s `ImportLinkKind` doc comment)
    /// is "the code stays on the host machine, not in the binary" — doing
    /// that properly means emitting a runtime loader/dlopen-style stub in
    /// the generated code, which this LLVM backend does not implement yet
    /// (only `extern dynamic [c]` FFI blocks get real dynamic dispatch,
    /// via `ffi_linker`/libc `dlopen`, not arbitrary `.h#` packages). So a
    /// `dynamic use "bytes -> x"` is a **hard compile error** here, with
    /// an actionable way out, rather than silently degrading to a static
    /// inline (which would contradict what the programmer asked for) or
    /// silently doing nothing (which would produce "undefined fn" errors
    /// with no indication why). The interpreter (`hsharp run`/`preview`)
    /// has no such limitation and supports `dynamic use` fully.
    pub fn resolve_bytes_import(
        &mut self,
        name: &str,
        version: Option<&str>,
        alias: &str,
        link: ImportLinkKind,
        start_dir: &Path,
    ) -> Result<Vec<Item>, String> {
        if matches!(link, ImportLinkKind::Dynamic) {
            return Err(format!(
                "dynamic use \"bytes -> {name}\" cannot be compiled to a native binary yet: \
the LLVM/AOT backend has no runtime package loader (unlike `extern dynamic [c]` \
FFI blocks, which do dispatch through libc `dlopen`).\n\n\
fix one of:\n\
  - drop `dynamic`: `use \"bytes -> {name}\"` links it statically into the binary\n\
  - run it through the interpreter instead: `hsharp run <file>` / `hsharp preview <file>`\n",
                name = name,
            ));
        }

        let project_root = bytes_resolve::find_bytes_project_root(start_dir);
        let lock = bytes_resolve::read_bytes_lockfile(&project_root);
        if let Some(wanted) = version {
            if let Some(locked) = lock.get(name) {
                if !locked.version.is_empty() && locked.version != wanted {
                    return Err(bytes_resolve::version_mismatch_message(name, wanted, &locked.version));
                }
            }
        }

        let path = match bytes_resolve::find_pkg_entry(name, start_dir) {
            Ok(p) => p,
            Err(bytes_resolve::BytesResolveError::NotFound(tried)) => {
                return Err(bytes_resolve::missing_message(name, &tried));
            }
            Err(bytes_resolve::BytesResolveError::NoEntry(dir)) => {
                return Err(bytes_resolve::no_entry_message(name, &dir));
            }
        };

        // Same "only inline once, program-wide" dedup `mod`/`std ->`
        // resolution already needs — a `bytes ->` package commonly gets
        // `use`d from more than one file in the same program.
        let canonical = std::fs::canonicalize(&path).unwrap_or_else(|_| path.clone());
        if !self.inlined_files.insert(canonical) {
            return Ok(Vec::new());
        }

        let src = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read bytes package '{}' at {}: {}", name, path.display(), e))?;
        let result = hsharp_parser::parse(&src, path.to_str().unwrap_or(name));
        if result.has_errors() {
            return Err(format!(
                "parse errors in bytes package '{}' ({}):\n{}",
                name, path.display(), result.render_errors()
            ));
        }
        let sub_module = result.module;
        let sub_dir = path.parent().map(|p| p.to_path_buf()).unwrap_or_else(|| PathBuf::from("."));

        // This package's own `use "std -> x"` / `use "bytes -> y"`
        // imports, resolved before its own functions are mangled/
        // appended — mirrors `resolve_std_import`'s identical recursion,
        // one level down. A nested `bytes ->` is resolved starting from
        // *this* package's own directory — `find_bytes_project_root`
        // walks back up from there and lands on the same top-level
        // project manifest either way, since `bytes` flat-installs every
        // dependency into one shared cache rather than nesting caches per
        // package (see that function's doc comment for the full story).
        let mut out = Vec::new();
        for (kind, sub_alias, _span) in &sub_module.imports {
            match kind {
                ImportKind::Std { path: sub_path, .. } => {
                    let sub_lib = sub_path.last().cloned().unwrap_or_default();
                    if sub_lib.is_empty() { continue; }
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_lib.clone());
                    out.extend(self.resolve_std_import(&sub_lib, &ns)?);
                }
                ImportKind::BytesRepo { name: sub_name, version: sub_version, link: sub_link, .. } => {
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_name.clone());
                    out.extend(self.resolve_bytes_import(sub_name, sub_version.as_deref(), &ns, *sub_link, &sub_dir)?);
                }
                ImportKind::Hlib { name: sub_name, version: sub_version, .. } => {
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_name.clone());
                    out.extend(self.resolve_hlib_import(sub_name, sub_version.as_deref(), &ns, &sub_dir)?);
                }
                _ => {}
            }
        }

        let mangled = mangle_module_items(sub_module.items, alias);
        let expanded = self.expand_module(mangled, &sub_dir)?;
        out.extend(expanded);
        Ok(out)
    }

    /// Resolve one `use "hlib -> name[/version]"` import: locate a
    /// `.hlib` (HackerOS Lib) archive, verify its internal checksums,
    /// and turn it into a flat `Vec<Item>` — **without** requiring the
    /// programmer to write a single `extern` block.
    ///
    /// Two paths, tried in order:
    ///
    ///   1. **AST splice** (the common case — every `h# lib build`
    ///      output has this unless the source module had zero `pub`
    ///      items): the archive's `ast` artifact is exactly a
    ///      `serde_json`-serialized `Vec<Item>` — the *same* `Item` type
    ///      this compiler already works with — so it's deserialized and
    ///      mangled/inlined exactly like a `mod` file or a `bytes ->`
    ///      package. Generics, structs, everything just works, because
    ///      by the time typecheck sees it, it *is* normal H# source.
    ///      This is what lets `.hlib` consumption skip `extern` entirely
    ///      for H#-to-H# libraries.
    ///   2. **Synthesized `extern`** (fallback — only used when the
    ///      archive has no `ast` artifact at all, e.g. a closed-source
    ///      `.hlib` or one produced by Hacker Lang/HackerScript with no
    ///      H#-shaped AST to give): a single `extern dynamic [rust, ...]`
    ///      block is built in memory straight from the archive's
    ///      language-agnostic header (`manifest.exports`), pointing at
    ///      the `.so` extracted into `~/.hackeros/H#/hlib-cache/`. The
    ///      programmer still never writes `extern` themselves — the
    ///      compiler does, internally, from `use "hlib -> x"` alone.
    ///      Any *generic* export is silently skipped here (there is no
    ///      AST to expand it from) with a note on stderr.
    pub fn resolve_hlib_import(
        &mut self,
        name: &str,
        version: Option<&str>,
        alias: &str,
        start_dir: &Path,
    ) -> Result<Vec<Item>, String> {
        let hlib_path = find_hlib_file(name, version, start_dir)?;

        // Same "only inline once, program-wide" dedup every other import
        // kind needs (see `inlined_files`'s doc comment).
        let canonical = std::fs::canonicalize(&hlib_path).unwrap_or_else(|_| hlib_path.clone());
        if !self.inlined_files.insert(canonical) {
            return Ok(Vec::new());
        }

        let archive = hsharp_hlib::HlibArchive::open(&hlib_path)
            .map_err(|e| format!("cannot open .hlib '{}' at {}: {}", name, hlib_path.display(), e))?;
        archive
            .verify_checksums()
            .map_err(|e| format!(".hlib '{}' failed its internal integrity check: {}", name, e))?;

        // ── Path 1: splice the ast artifact directly ────────────────────
        if let Some(ast_artifact) = archive.manifest.artifacts_of_kind(hsharp_hlib::ArtifactKind::Ast).next() {
            let ast_bytes = archive.entry_bytes(&ast_artifact.path).ok_or_else(|| {
                format!(".hlib '{}': ast artifact listed in manifest but missing from the archive", name)
            })?;
            let items: Vec<Item> = serde_json::from_slice(ast_bytes)
                .map_err(|e| format!(".hlib '{}': cannot parse its ast artifact: {}", name, e))?;

            let sub_dir = hlib_path.parent().map(|p| p.to_path_buf()).unwrap_or_else(|| PathBuf::from("."));
            let mangled = mangle_module_items(items, alias);
            return self.expand_module(mangled, &sub_dir);
        }

        // ── Path 2: synthesize `extern` from the header ─────────────────
        let host_triple = crate::target::TargetTriple::host().llvm_triple;
        let so_artifact = archive.manifest.shared_object_for(&host_triple).ok_or_else(|| {
            format!(
                ".hlib '{name}' has neither an `ast` artifact nor a `.so` built for this host \
                 ({host_triple}) — nothing here can be linked. Available native targets: {targets}",
                name = name,
                host_triple = host_triple,
                targets = archive
                    .manifest
                    .artifacts_of_kind(hsharp_hlib::ArtifactKind::SharedObject)
                    .filter_map(|a| a.target.as_deref())
                    .collect::<Vec<_>>()
                    .join(", "),
            )
        })?;
        let so_bytes = archive.entry_bytes(&so_artifact.path).ok_or_else(|| {
            format!(".hlib '{}': shared object listed in manifest but missing from the archive", name)
        })?;

        let cache_dir = hlib_cache_dir()?.join(format!("{}-{}", name, archive.manifest.version));
        std::fs::create_dir_all(&cache_dir)
            .map_err(|e| format!("cannot create hlib cache dir {}: {}", cache_dir.display(), e))?;
        let so_path = cache_dir.join(format!("lib{}.so", name));
        if !so_path.exists() {
            std::fs::write(&so_path, so_bytes).map_err(|e| format!("cannot extract .so from '{}': {}", name, e))?;
        }

        let functions: Vec<ExternFnDecl> = archive
            .manifest
            .exports
            .iter()
            .filter(|e| !e.generic && matches!(e.kind, hsharp_hlib::ExportedSymbolKind::Function))
            .map(|e| ExternFnDecl {
                name: e.name.clone(),
                params: e
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, t)| Param {
                        name: format!("arg{i}"),
                        ty: abi_type_to_type_expr(t),
                        mutable: false,
                        span: Span::dummy(),
                    })
                    .collect(),
                return_type: e.returns.as_ref().map(abi_type_to_type_expr),
                variadic: false,
                span: Span::dummy(),
            })
            .collect();

        let skipped: Vec<&str> = archive.manifest.exports.iter().filter(|e| e.generic).map(|e| e.name.as_str()).collect();
        if !skipped.is_empty() {
            eprintln!(
                "  note: .hlib '{}' — {} generic export(s) skipped (no ast artifact to expand \
                 them from, only a compiled .so): {}",
                name,
                skipped.len(),
                skipped.join(", ")
            );
        }
        if functions.is_empty() {
            return Err(format!(
                ".hlib '{}' has no `ast` artifact and no non-generic function export to bind — nothing to link.",
                name
            ));
        }

        Ok(vec![Item::Extern(ExternBlock {
            lang: ExternLang::Rust,
            link_kind: ExternLinkKind::Dynamic,
            library: Some(so_path.to_string_lossy().to_string()),
            functions,
            span: Span::dummy(),
        })])
    }

    /// Resolve one `use "workspace -> member"` import (optionally with
    /// `from "module -> item_or_*"`): find the named member inside the
    /// current project's `[workspace] -> members` list (root
    /// `Bytes.hk`/`bytes.hk` — see `bytes_resolve::read_workspace_members`),
    /// parse either that member's own build entry (`module: None`, e.g.
    /// `use "workspace -> parser"` alone) or one specific module file
    /// inside it (`module: Some("ast")`, from `from "ast -> *"`),
    /// recursively resolve *that* file's own imports, mangle its items
    /// under `alias` — same as every other `resolve_*_import` here — and
    /// return the resulting flat item list.
    ///
    /// This is what makes `use "workspace -> parser" from "ast -> *"`
    /// H#'s equivalent of Rust's `use hsharp_parser::ast::*;`: `parser`
    /// is resolved as a workspace member (like a Cargo workspace crate),
    /// `ast` as a module file inside it, and `*` as "bring in everything
    /// `pub` or otherwise defined there", matching how a `mod`/`std ->`
    /// import already inlines a whole file's item list.
    ///
    /// `item: Some(name)` (a *specific* name after the arrow, not `*`)
    /// is a best-effort single-item import: only the one item whose own
    /// name matches is kept after mangling. This is intentionally
    /// simplistic — it does **not** trace that item's own dependencies
    /// within the same file, so a single-item import of something that
    /// calls a private helper defined alongside it in the same module
    /// will fail to link. Prefer `from "module -> *"` for anything with
    /// in-module dependencies; single-item imports are best suited to
    /// standalone leaf functions, structs, or enums.
    pub fn resolve_workspace_import(
        &mut self,
        member: &str,
        module: Option<&str>,
        item: Option<&str>,
        alias: &str,
        start_dir: &Path,
    ) -> Result<Vec<Item>, String> {
        let project_root = bytes_resolve::find_bytes_project_root(start_dir);
        let member_dir = bytes_resolve::find_workspace_member_dir(&project_root, member)
            .ok_or_else(|| format!(
                "workspace member '{member}' not found under {root}.\n\n\
hint: `use \"workspace -> {member}\"` looks for `{member}` in the root \
`Bytes.hk`'s `[workspace] -> members => [...]` list (either listed exactly \
as \"{member}\", or as a path ending in \"/{member}\", e.g. \"source-code/{member}\") \
— check {root}/Bytes.hk (or bytes.hk).\n",
                member = member, root = project_root.display(),
            ))?;

        // Resolve the file to parse: either the member's own build entry
        // (`[build] -> entry`, default `src/main.h#` — same manifest field
        // `bytes` itself uses to drive a build), or one module file inside
        // that entry's directory, found the exact same way a plain `mod
        // <name>` would be (`name.h#` / `name/mod.h#` / `name/main.h#`).
        let entry = bytes_resolve::workspace_member_entry(&member_dir);
        let src_dir = entry.parent().map(|p| p.to_path_buf()).unwrap_or_else(|| member_dir.clone());

        let path: PathBuf = match module {
            None => {
                if !entry.exists() {
                    return Err(format!(
                        "workspace member '{member}''s build entry {entry} does not exist \
(checked `[build] -> entry` in {member_dir}/Bytes.hk).",
                        member = member, entry = entry.display(), member_dir = member_dir.display(),
                    ));
                }
                entry.clone()
            }
            Some(m) => {
                let candidates = [format!("{m}.h#"), format!("{m}/mod.h#"), format!("{m}/main.h#")];
                candidates
                    .iter()
                    .map(|c| src_dir.join(c))
                    .find(|p| p.is_file())
                    .ok_or_else(|| format!(
                        "workspace member '{member}': module '{m}' not found \
(expected {m}.h#, {m}/mod.h#, or {m}/main.h# under {dir})",
                        member = member, m = m, dir = src_dir.display(),
                    ))?
            }
        };

        // Same "only inline once, program-wide" dedup every other import
        // kind here needs (see `inlined_files`'s doc comment) — a
        // workspace member/module commonly gets `use`d from more than one
        // file in the same program.
        let canonical = std::fs::canonicalize(&path).unwrap_or_else(|_| path.clone());
        if !self.inlined_files.insert(canonical) {
            return Ok(Vec::new());
        }

        let src = std::fs::read_to_string(&path)
            .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
        let result = hsharp_parser::parse(&src, path.to_str().unwrap_or(member));
        if result.has_errors() {
            return Err(format!(
                "parse errors in workspace member '{}' ({}):\n{}",
                member, path.display(), result.render_errors()
            ));
        }
        let sub_module = result.module;
        let sub_dir = path.parent().map(|p| p.to_path_buf()).unwrap_or(src_dir);

        // This module file's own `use "std -> x"` / `use "bytes -> y"` /
        // `use "hlib -> z"` / `use "workspace -> other"` imports, resolved
        // before its own items are filtered/mangled/appended — mirrors
        // `resolve_bytes_import`'s identical recursion, one level down,
        // so a workspace member's module can freely depend on std, on
        // another bytes package, on a `.hlib`, or on *another* workspace
        // member, exactly like its own top-level entry file could.
        let mut out = Vec::new();
        for (kind, sub_alias, _span) in &sub_module.imports {
            match kind {
                ImportKind::Std { path: sub_path, .. } => {
                    let sub_lib = sub_path.last().cloned().unwrap_or_default();
                    if sub_lib.is_empty() { continue; }
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_lib.clone());
                    out.extend(self.resolve_std_import(&sub_lib, &ns)?);
                }
                ImportKind::BytesRepo { name: sub_name, version: sub_version, link: sub_link, .. } => {
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_name.clone());
                    out.extend(self.resolve_bytes_import(sub_name, sub_version.as_deref(), &ns, *sub_link, &sub_dir)?);
                }
                ImportKind::Hlib { name: sub_name, version: sub_version, .. } => {
                    let ns = sub_alias.clone().unwrap_or_else(|| sub_name.clone());
                    out.extend(self.resolve_hlib_import(sub_name, sub_version.as_deref(), &ns, &sub_dir)?);
                }
                ImportKind::Workspace { member: sub_member, module: sub_mod, item: sub_item } => {
                    out.extend(self.resolve_workspace_import(sub_member, sub_mod.as_deref(), sub_item.as_deref(), sub_member, &sub_dir)?);
                }
                _ => {}
            }
        }

        // Best-effort single-item filter (see doc comment above): keep
        // only the item whose own name matches, dropping everything else
        // from this file before mangling/appending. `item == Some("*")`
        // (or no `from` at all) keeps every item, same as a `mod`/`std ->`
        // import always has.
        let raw_items = match item {
            Some(name) if name != "*" => sub_module.items
                .into_iter()
                .filter(|it| item_name(it) == Some(name))
                .collect::<Vec<_>>(),
            _ => sub_module.items,
        };
        if raw_items.is_empty() {
            if let Some(name) = item {
                if name != "*" {
                    return Err(format!(
                        "workspace member '{member}', module '{m}': no item named '{name}' found",
                        member = member, m = module.unwrap_or(""), name = name,
                    ));
                }
            }
        }

        let mangled = mangle_module_items(raw_items, alias);
        let expanded = self.expand_module(mangled, &sub_dir)?;
        out.extend(expanded);
        Ok(out)
    }

    /// The single front-end entry point every caller (`hsharp preview`,
    /// `hsharp build`/`compile`, `hsharp check`) should use instead of
    /// calling `expand_module` directly: resolves this module's
    /// `use "std -> x"` imports (via `resolve_std_import`, above), its
    /// `use "bytes -> x"` imports (via `resolve_bytes_import`, above),
    /// *and* its `mod X` declarations (via `expand_module`), producing one
    /// flat, fully-inlined item list — the same one, regardless of which
    /// backend eventually compiles or interprets it.
    pub fn expand_program(&mut self, module: &Module, entry_dir: &Path) -> Result<Vec<Item>, String> {
        let mut items = Vec::new();
        for (kind, alias, _span) in &module.imports {
            match kind {
                ImportKind::Std { path, .. } => {
                    let lib = path.last().cloned().unwrap_or_default();
                    if lib.is_empty() { continue; }
                    let ns = alias.clone().unwrap_or_else(|| lib.clone());
                    items.extend(self.resolve_std_import(&lib, &ns)?);
                }
                ImportKind::BytesRepo { name, version, link, .. } => {
                    let ns = alias.clone().unwrap_or_else(|| name.clone());
                    items.extend(self.resolve_bytes_import(name, version.as_deref(), &ns, *link, entry_dir)?);
                }
                ImportKind::Hlib { name, version, .. } => {
                    let ns = alias.clone().unwrap_or_else(|| name.clone());
                    items.extend(self.resolve_hlib_import(name, version.as_deref(), &ns, entry_dir)?);
                }
                ImportKind::Workspace { member, module: sub_module, item } => {
                    // NOTE: unlike every other `ImportKind` here, the
                    // generic `alias` tuple field is *not* usable as a
                    // namespace override for `Workspace` — it's the raw,
                    // unparsed `from "..."` string (e.g. `"ast -> *"`),
                    // already fully consumed above into `sub_module`/
                    // `item` by `parse_use_path`. There is currently no
                    // surviving syntax slot left to *also* specify a
                    // custom namespace, so the member's own name is
                    // always the namespace: `use "workspace -> parser"
                    // from "ast -> *"` imports as `parser::foo(...)`.
                    items.extend(self.resolve_workspace_import(
                        member, sub_module.as_deref(), item.as_deref(), member, entry_dir,
                    )?);
                }
                _ => {}
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
    // BUG FIX: this used to return (and cache/pass through) only
    // `sub_module.items`, silently discarding `sub_module.imports` —
    // see `expand_module`'s `ModDecl{inline: None}` arm below for the
    // full story on why that was a real bug (a `mod`-included local
    // file's own `use "std -> x"`/`use "bytes -> x"`/etc. imports were
    // never resolved at all, so e.g. `env::remove(...)` called from a
    // `mod vars`-included `vars.h#` failed with a raw `codegen:
    // undefined fn: remove` — `env.h#` was simply never loaded, since
    // nothing about `vars.h#` being `mod`-included from `main.h#` ever
    // triggered processing `vars.h#`'s *own* imports; only the entry
    // file's top-level imports ever went through `expand_program`'s
    // import loop). Now returns the imports too, so the caller can
    // resolve them exactly like `expand_program` already does for the
    // entry file.
    fn resolve(&mut self, mod_name: &str, from_dir: &Path) -> Result<(Vec<Item>, Vec<(ImportKind, Option<String>, Span)>, PathBuf), String> {
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
    fn load(&self, mod_name: &str, from_dir: &Path) -> Result<(Vec<Item>, Vec<(ImportKind, Option<String>, Span)>, PathBuf), String> {
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
                    return Ok((sub_module.items, sub_module.imports, resolved_path));
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
                        Ok((raw_items, raw_imports, resolved_file)) => {
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
                            // BUG FIX: this file's *own* `use "std -> x"`/
                            // `use "bytes -> x"`/`use "hlib -> x"`/
                            // `use "workspace -> x"` imports used to be
                            // silently dropped here — `resolve()` only
                            // ever returned `raw_items`
                            // (`sub_module.items`), never
                            // `sub_module.imports`, and nothing else in
                            // this function (or anywhere else reachable
                            // from a `mod X`-inclusion, as opposed to the
                            // top-level entry file) ever processed them.
                            // `expand_program` — called exactly once, only
                            // for the entry file — is the *only* place
                            // that loop existed. So a `use` import in any
                            // file reached via `mod` (rather than being
                            // re-declared, redundantly, at the entry file
                            // too) was simply never resolved: the imported
                            // module's functions never made it into the
                            // compiled item list at all, and any call to
                            // one produced a confusing `codegen: undefined
                            // fn: <bare name>` — e.g. `vars.h#` (`mod
                            // vars`-included from `hsh`'s `main.h#`) has
                            // its own `use "std -> env" from "env"`, and
                            // `env::remove(...)` failed this way, even
                            // though `env::set(...)`/`env::get(...)` from
                            // the *same* import happened to keep working
                            // anyway — purely because those two also
                            // happen to have their own hard-coded,
                            // import-independent dispatch arms in
                            // `codegen.rs`'s `call_fn`, which `remove`
                            // doesn't.
                            //
                            // Fix: resolve this file's own imports here,
                            // exactly the way `expand_program` already
                            // does for the entry file — added *unmangled*
                            // by this `mod`'s own name (each import kind's
                            // resolver already mangles under its own
                            // alias internally), same as
                            // `expand_program`'s two separate `items.extend(...)`
                            // calls keep the entry file's own items and
                            // its imports' items distinct.
                            let mut sub_expanded = Vec::new();
                            for (kind, alias, _span) in &raw_imports {
                                match kind {
                                    ImportKind::Std { path, .. } => {
                                        let lib = path.last().cloned().unwrap_or_default();
                                        if lib.is_empty() { continue; }
                                        let ns = alias.clone().unwrap_or_else(|| lib.clone());
                                        sub_expanded.extend(self.resolve_std_import(&lib, &ns)?);
                                    }
                                    ImportKind::BytesRepo { name: pkg_name, version, link, .. } => {
                                        let ns = alias.clone().unwrap_or_else(|| pkg_name.clone());
                                        sub_expanded.extend(self.resolve_bytes_import(
                                            pkg_name, version.as_deref(), &ns, *link, &resolved_dir,
                                        )?);
                                    }
                                    ImportKind::Hlib { name: pkg_name, version, .. } => {
                                        let ns = alias.clone().unwrap_or_else(|| pkg_name.clone());
                                        sub_expanded.extend(self.resolve_hlib_import(
                                            pkg_name, version.as_deref(), &ns, &resolved_dir,
                                        )?);
                                    }
                                    ImportKind::Workspace { member, module: sub_mod, item } => {
                                        sub_expanded.extend(self.resolve_workspace_import(
                                            member, sub_mod.as_deref(), item.as_deref(), member, &resolved_dir,
                                        )?);
                                    }
                                    _ => {}
                                }
                            }
                            // Mangle *before* recursing (see comment above).
                            let mangled = mangle_module_items(raw_items, &name);
                            let sub = self.expand_module(mangled, &resolved_dir)?;
                            sub_expanded.extend(sub);
                            expanded.extend(sub_expanded);
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
/// Locates a `.hlib` archive by logical name (and optional version),
/// searching — in order — the declaring file's own `hlibs/` directory,
/// that directory itself, the enclosing `bytes` project's `hlibs/`
/// directory (`find_bytes_project_root` walks up to find it, same as
/// `bytes ->` imports do), the user's personal cache
/// (`~/.hackeros/H#/hlibs/`), and finally the system-wide location
/// (`/usr/lib/HackerOS/H#/hlibs/`, alongside the std library — see
/// `resolve_std_import`'s path constant).
fn find_hlib_file(name: &str, version: Option<&str>, start_dir: &Path) -> Result<PathBuf, String> {
    let project_root = bytes_resolve::find_bytes_project_root(start_dir);
    let mut dirs: Vec<PathBuf> = vec![start_dir.join("hlibs"), start_dir.to_path_buf(), project_root.join("hlibs")];
    if let Ok(home) = std::env::var("HOME") {
        dirs.push(PathBuf::from(home).join(".hackeros").join("H#").join("hlibs"));
    }
    dirs.push(PathBuf::from("/usr/lib/HackerOS/H#/hlibs"));

    let filenames: Vec<String> = match version {
        Some(v) => vec![format!("{name}-{v}.hlib"), format!("{name}.hlib")],
        None => vec![format!("{name}.hlib")],
    };

    let mut tried = Vec::new();
    for dir in &dirs {
        for fname in &filenames {
            let p = dir.join(fname);
            if p.exists() {
                return Ok(p);
            }
            tried.push(p);
        }
    }
    Err(format!(
        "hlib '{name}' not found. Tried:\n{}\n\n\
         build one with `h# lib build <file.h#> -o hlibs/{name}.hlib`, \
         or place a prebuilt archive at one of the paths above.",
        tried.iter().map(|p| format!("  {}", p.display())).collect::<Vec<_>>().join("\n"),
        name = name,
    ))
}

/// Where extracted `.so` files from header-only (no-`ast`) `.hlib`s are
/// cached, keyed by `<name>-<version>` so two different libraries (or
/// two versions of the same one) never collide on disk.
fn hlib_cache_dir() -> Result<PathBuf, String> {
    let base = std::env::var("HOME")
        .map(PathBuf::from)
        .map_err(|_| "cannot locate a cache directory: $HOME is not set".to_string())?;
    Ok(base.join(".hackeros").join("H#").join("hlib-cache"))
}

/// Inverse of `hsharp-cli`'s `hlib_export::lower_type_expr` — turns an
/// ABI-stable `hsharp_hlib::AbiType` back into a `TypeExpr` suitable for
/// a synthesized `extern` block's parameter/return types. Structs
/// (`Opaque`) come back as `&Name` (a reference), not `Name` by value —
/// H#'s FFI layer requires structs to be passed by pointer (see
/// `ffi_header.rs`'s `StructByValueFfi` diagnostic), and a `.hlib`'s
/// header-only fallback path has no other way to know a struct's true
/// layout anyway, so a borrowed opaque handle is the only sound choice.
fn abi_type_to_type_expr(t: &hsharp_hlib::AbiType) -> TypeExpr {
    use hsharp_hlib::AbiType;
    match t {
        AbiType::I8 => TypeExpr::I8, AbiType::I16 => TypeExpr::I16,
        AbiType::I32 => TypeExpr::I32, AbiType::I64 => TypeExpr::I64,
        AbiType::U8 => TypeExpr::U8, AbiType::U16 => TypeExpr::U16,
        AbiType::U32 => TypeExpr::U32, AbiType::U64 => TypeExpr::U64,
        AbiType::F32 => TypeExpr::F32, AbiType::F64 => TypeExpr::F64,
        AbiType::Bool => TypeExpr::Bool,
        AbiType::Void => TypeExpr::Void,
        AbiType::Ptr => TypeExpr::Bytes,
        AbiType::Opaque { struct_name } => TypeExpr::Ref(Box::new(TypeExpr::Named(struct_name.clone()))),
    }
}

/// Best-effort item name extractor for `use "workspace -> x" from "mod ->
/// SomeItem"` single-item imports (see `resolve_workspace_import`) — the
/// only `Item` variants worth importing by name on their own. `ImplBlock`,
/// `ModDecl`, and type aliases have no single obviously-right "name" to
/// match a bare item request against, so they're not selectable this way
/// (use `from "mod -> *"` instead, which takes every item regardless).
fn item_name(item: &Item) -> Option<&str> {
    match item {
        Item::FnDef(f) => Some(f.name.as_str()),
        Item::StructDef(s) => Some(s.name.as_str()),
        Item::EnumDef(e) => Some(e.name.as_str()),
        Item::TraitDef(t) => Some(t.name.as_str()),
        Item::TypeAlias { name, .. } => Some(name.as_str()),
        Item::ConstDef { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

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
