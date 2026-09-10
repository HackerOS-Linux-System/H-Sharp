use serde_json::Value as Json;
use std::collections::HashMap;
use crate::value::{Value, RuntimeError};

// ─── std/*.h# resolution (HackerOS layout) ─────────────────────────────────
//
// From today onward, `use "std -> X"` is a REAL file lookup, not a name
// shortcut into a Rust/C builtin table. When a program (or the H# runtime
// itself, at REPL/preview/build time) declares `use "std -> env"`, the
// runtime looks for the actual library source at:
//
//   /usr/lib/HackerOS/H#/std/env.h#
//
// and parses + registers it exactly like a `mod` (see `interp.rs`'s
// `load_std_module` and `register_mod_items`). There is no silent
// "built-in fallback" anymore — a missing file is a hard error, since a
// program that imports a stdlib module and gets a silently-different
// (and possibly less complete) embedded implementation instead is a much
// worse failure mode than a loud, actionable one.
//
// `use "core -> X"` is unaffected by any of this — `core` is, by design,
// the one layer that *does* ship statically compiled into the H# runtime
// itself (this crate + `runtime/core.c` on the LLVM side), the same way a
// C program always has libc linked in without needing to `apt install`
// anything. `std` is everything built on top of that core, and now lives
// exclusively as real, inspectable, editable `.h#` source under `std/`.
pub const STD_LIB_ROOT: &str = "/usr/lib/HackerOS/H#/std";

/// The on-disk path a `use "std -> ...-> lib"` import resolves to.
pub fn std_lib_path(lib: &str) -> std::path::PathBuf {
    std::path::PathBuf::from(STD_LIB_ROOT).join(format!("{}.h#", lib))
}

/// The message shown when a `std -> lib` import can't find its file.
/// Exact wording/format is intentional — this is user-facing product
/// copy, not an internal diagnostic, and should stay stable so scripts/
/// docs that grep for it keep working. The Windows line is a known,
/// deliberate placeholder: HackerOS' `h#-utils` package currently only
/// ships a Linux path (`hacker unpack h#-utils`); there is no Windows
/// install path defined yet.
pub fn std_lib_missing_message(lib: &str) -> String {
    format!(
        "std module '{lib}' not found at {path}\n\n\
please install h# utils for HackerOS use:\n\
  linux:   hacker unpack h#-utils\n\
  windows: (not available yet — no install path is defined for Windows yet)\n",
        lib = lib,
        path = std_lib_path(lib).display(),
    )
}

// ─── bytes package resolution (`use "bytes -> pkg"`) ───────────────────────
//
// Mirrors the `std -> lib` machinery above, but resolves against packages
// installed by the `bytes` package manager (a separate H#-written project;
// see its `installer.h#`/`lockfile.h#`/`isolation.h#`) instead of the fixed
// HackerOS std layout. `bytes install` fetches a dependency into one of two
// caches:
//
//   <project>/build/cache/packages/<name>       (project-local, per
//                                                 `installer.h#::pkg_cache_dir`)
//   ~/.hackeros/H#/build/cache/packages/<name>   (global, per
//                                                 `isolation.h#::hackeros_cache_base`)
//
// and records exactly what got installed (name/version/url/checksum) in a
// `bytes.lock` JSON file next to the project's `Bytes.hk` (see
// `lockfile.h#`). A `use "bytes -> name[/version]"` import (optionally
// `dynamic use ...`, see `ImportLinkKind`) resolves against those two
// caches, in that order, cross-checked against the lockfile when one
// exists — a missing package, a broken/entry-less one, or a version that
// doesn't match what's locked is a hard, actionable error, never a silent
// stub, exactly like `std -> lib` above.
//
// NOTE ON DUPLICATION: same story as `STD_LIB_ROOT` above — this is
// intentionally re-implemented, not shared via a common crate, in
// `hsharp-compiler`'s `modules.rs` (`resolve_bytes_import`) and
// `hsharp-typecheck`'s `checker/mod.rs` (`check_module`'s import pass), so
// the tree-walking interpreter, the LLVM/AOT backend, and the typechecker
// all agree on where a `bytes ->` package lives and what counts as
// "installed". Any change to the search order or lockfile format here
// must be mirrored in both of those.

/// One entry out of `bytes.lock`'s `"packages"` object.
#[derive(Debug, Clone)]
pub struct LockedBytesPkg {
    pub version: String,
    #[allow(dead_code)]
    pub url: String,
    #[allow(dead_code)]
    pub checksum: String,
}

/// Why `find_bytes_pkg_entry` couldn't resolve a package to a usable entry
/// file — kept distinct from a plain `String` so callers (interpreter vs.
/// compiler) can format the two very different situations ("nothing here
/// at all" vs. "something's here, but it's not a valid H# package") with
/// their own wording while sharing the same search logic.
pub enum BytesResolveError {
    /// No directory or flat `<name>.h#` file exists in any searched cache.
    NotFound(Vec<std::path::PathBuf>),
    /// A package directory exists (so `bytes install` clearly ran) but it
    /// has neither a manifest `[build] -> entry` nor any of the
    /// conventional entry file names.
    NoEntry(std::path::PathBuf),
}

/// `~/.hackeros/H#/build/cache/packages` — the global package cache
/// `bytes`'s `isolation.h#::hackeros_cache_base()` writes into. Falls back
/// to `/tmp/.hackeros/H#/build/cache/packages` if `$HOME` isn't set, the
/// same fallback that H# function itself uses.
pub fn bytes_global_cache_dir() -> std::path::PathBuf {
    let base = std::env::var("HOME")
        .map(|h| std::path::PathBuf::from(h).join(".hackeros/H#/build/cache"))
        .unwrap_or_else(|_| std::path::PathBuf::from("/tmp/.hackeros/H#/build/cache"));
    base.join("packages")
}

/// Walk upward from `start_dir` looking for `Bytes.hk`/`bytes.hk` (the
/// project manifest `bytes` itself reads — see `config.h#::find_hk`), so a
/// `use "bytes -> x"` resolves against *that* project's local package
/// cache even when the file declaring the import isn't at the project
/// root (e.g. `src/foo.h#` still finds the same `build/cache/packages`
/// as `src/main.h#` would — and, just as importantly, so a nested
/// `use "bytes -> y"` *inside* an already-fetched package `x` walks back
/// up through `build/cache/packages/x/...` and finds the same top-level
/// project manifest, since `bytes` flat-installs every dependency into one
/// shared cache rather than giving each package its own nested one).
/// Capped at 8 parent directories, mirroring `config.h#::find_hk_upward`'s
/// own depth limit. Returns `start_dir` itself if no manifest is found
/// anywhere above it (the lookup then simply won't find anything under
/// `<start_dir>/build/cache/...`, which is correct for a standalone
/// script with no project at all).
pub fn find_bytes_project_root(start_dir: &std::path::Path) -> std::path::PathBuf {
    let mut dir = start_dir.to_path_buf();
    for _ in 0..8 {
        if dir.join("Bytes.hk").is_file() || dir.join("bytes.hk").is_file() {
            return dir;
        }
        match dir.parent() {
            Some(p) => dir = p.to_path_buf(),
            None => break,
        }
    }
    start_dir.to_path_buf()
}

/// The two package-cache roots a `bytes -> name` import is searched
/// against, project-local first (so a project-pinned version wins over
/// whatever happens to be globally installed).
pub fn bytes_pkg_cache_roots(start_dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    let project_root = find_bytes_project_root(start_dir);
    vec![project_root.join("build/cache/packages"), bytes_global_cache_dir()]
}

/// Very small, dependency-free `bytes.lock` reader. The real format
/// (written by `lockfile.h#::lockfile_write`) is plain JSON:
/// `{"version":1,"packages":{"name":{"version":"..","url":"..","checksum":".."}}}`
/// — parsed here with `serde_json` (already a dependency of this crate)
/// rather than the hand-rolled string-splitting `lockfile.h#` itself has
/// to use (H# has no JSON library of its own to lean on). A missing or
/// unparseable lockfile is treated as "nothing locked yet", not an error
/// — plenty of valid `bytes ->` lookups happen before `bytes install` has
/// ever run once (e.g. a fresh `hsharp check` right after `bytes add`).
pub fn read_bytes_lockfile(project_root: &std::path::Path) -> HashMap<String, LockedBytesPkg> {
    let mut out = HashMap::new();
    let path = project_root.join("bytes.lock");
    let content = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return out,
    };
    let json: Json = match serde_json::from_str(&content) {
        Ok(j) => j,
        Err(_) => return out,
    };
    let pkgs = match json.get("packages").and_then(|p| p.as_object()) {
        Some(p) => p,
        None => return out,
    };
    for (name, entry) in pkgs {
        let version = entry.get("version").and_then(|v| v.as_str()).unwrap_or("").to_string();
        let url = entry.get("url").and_then(|v| v.as_str()).unwrap_or("").to_string();
        let checksum = entry.get("checksum").and_then(|v| v.as_str()).unwrap_or("").to_string();
        out.insert(name.clone(), LockedBytesPkg { version, url, checksum });
    }
    out
}

/// Pull `-> entry => ...` out of a package's own `Bytes.hk`/`bytes.hk`
/// `[build]` section (falling back to `[package]`) — the same key
/// `config.h#::build_entry` reads project-side. Returns `None` if the
/// package has no manifest at all (e.g. the bare single-file stub `bytes`
/// creates when a name isn't in the registry yet — see
/// `installer.h#::install_bytes_dep`) or its declared entry doesn't
/// actually exist on disk, in which case the caller falls back to the
/// fixed candidate list.
fn bytes_pkg_manifest_entry(pkg_dir: &std::path::Path) -> Option<std::path::PathBuf> {
    let manifest = ["Bytes.hk", "bytes.hk"]
        .iter()
        .map(|n| pkg_dir.join(n))
        .find(|p| p.is_file())?;
    let content = std::fs::read_to_string(&manifest).ok()?;
    let mut section = String::new();
    let mut build_entry: Option<String> = None;
    let mut package_entry: Option<String> = None;
    for raw_line in content.lines() {
        let line = raw_line.trim();
        if line.starts_with('[') && line.ends_with(']') {
            section = line[1..line.len() - 1].to_string();
            continue;
        }
        if let Some(rest) = line.strip_prefix("->") {
            if let Some((key, val)) = rest.split_once("=>") {
                let key = key.trim();
                let val = val.trim().trim_matches('"');
                if key == "entry" {
                    match section.as_str() {
                        "build" => build_entry = Some(val.to_string()),
                        "package" => package_entry = Some(val.to_string()),
                        _ => {}
                    }
                }
            }
        }
    }
    let entry = build_entry.or(package_entry)?;
    let candidate = pkg_dir.join(&entry);
    if candidate.is_file() { Some(candidate) } else { None }
}

/// Resolve one `use "bytes -> name[/version]"` import to an on-disk entry
/// file. Tries, per cache root (project-local, then global — see
/// `bytes_pkg_cache_roots`): the manifest-declared entry point
/// (`Bytes.hk`'s `[build] -> entry`) inside `<cache>/<name>/`; then the
/// conventional fallback candidates a bare `bytes new`-scaffolded package
/// would have (`src/lib.h#`, `src/main.h#`, `lib.h#`, `main.h#`,
/// `<name>.h#`); then finally the flat `<cache>/<name>.h#` single-file
/// layout `install_bytes_dep`'s registry-miss stub writes when a name
/// isn't in the registry index yet.
pub fn find_bytes_pkg_entry(name: &str, start_dir: &std::path::Path) -> Result<std::path::PathBuf, BytesResolveError> {
    let mut tried = Vec::new();
    let mut broken: Option<std::path::PathBuf> = None;
    for cache in bytes_pkg_cache_roots(start_dir) {
        let pkg_dir = cache.join(name);
        if pkg_dir.is_dir() {
            tried.push(pkg_dir.clone());
            if let Some(entry) = bytes_pkg_manifest_entry(&pkg_dir) {
                return Ok(entry);
            }
            for candidate in ["src/lib.h#", "src/main.h#", "lib.h#", "main.h#"] {
                let p = pkg_dir.join(candidate);
                if p.is_file() { return Ok(p); }
            }
            let named = pkg_dir.join(format!("{}.h#", name));
            if named.is_file() { return Ok(named); }
            broken.get_or_insert(pkg_dir);
        } else {
            tried.push(pkg_dir);
        }
        let flat = cache.join(format!("{}.h#", name));
        tried.push(flat.clone());
        if flat.is_file() { return Ok(flat); }
    }
    match broken {
        Some(dir) => Err(BytesResolveError::NoEntry(dir)),
        None => Err(BytesResolveError::NotFound(tried)),
    }
}

/// The message shown when `use "bytes -> name"` can't find the package
/// anywhere on disk at all — mirrors `std_lib_missing_message`'s "loud,
/// actionable error, not a silent stub" policy, but points at `bytes
/// add`/`bytes install` (the package manager) rather than `hacker unpack`,
/// since a `bytes ->` dependency is per-project, not part of the fixed
/// HackerOS layout.
pub fn bytes_pkg_missing_message(name: &str, tried: &[std::path::PathBuf]) -> String {
    let locations = tried.iter().map(|p| format!("  - {}", p.display())).collect::<Vec<_>>().join("\n");
    format!(
        "bytes package '{name}' not found. Looked in:\n{locations}\n\n\
install it first:\n\
  bytes add {name}\n\
  bytes install\n",
        name = name, locations = locations,
    )
}

/// The message shown when a `bytes ->` package's directory exists but has
/// no resolvable entry point — distinct from "not found" because the
/// install clearly happened, but the fetched tree isn't a valid H#
/// package (or its `Bytes.hk` points at an entry file that doesn't exist).
pub fn bytes_pkg_no_entry_message(name: &str, pkg_dir: &std::path::Path) -> String {
    format!(
        "bytes package '{name}' was found at {dir} but has no usable entry point.\n\n\
expected one of (relative to that directory):\n\
  a `Bytes.hk`/`bytes.hk` with `[build] -> entry => ...`\n\
  src/lib.h#, src/main.h#, lib.h#, main.h#, or {name}.h#\n",
        name = name, dir = pkg_dir.display(),
    )
}

/// The message for `dynamic use "bytes -> name"` when the package isn't
/// recorded in `bytes.lock`. A `dynamic` import's whole contract (see
/// `ast.rs`'s `ImportLinkKind` doc comment) is "the host machine already
/// ran `bytes install`" — a package with no lockfile entry hasn't, even
/// if a stray directory with the right name happens to exist in the cache
/// (e.g. left over from a `bytes remove` that only edited
/// `Bytes.hk`/`bytes.lock` and never touched the on-disk cache).
pub fn bytes_pkg_not_locked_message(name: &str) -> String {
    format!(
        "dynamic bytes package '{name}' is not recorded in bytes.lock.\n\n\
`dynamic use \"bytes -> {name}\"` requires it to have already been installed\n\
by the bytes package manager on this machine:\n\
  bytes add {name}\n\
  bytes install\n",
        name = name,
    )
}

/// The message for a version mismatch between what the source code
/// requests (`use "bytes -> name/1.2.3"`) and what `bytes.lock` actually
/// has installed. A mismatch is worth a loud error rather than quietly
/// building/running against the wrong version.
pub fn bytes_pkg_version_mismatch_message(name: &str, wanted: &str, locked: &str) -> String {
    format!(
        "bytes package '{name}' version mismatch: code requests '{wanted}', but \
bytes.lock has '{locked}' installed.\n\n\
run one of:\n\
  bytes update {name}          ;; re-lock to the latest matching version\n\
  bytes add {name}/{wanted}    ;; explicitly re-pin and reinstall\n",
        name = name, wanted = wanted, locked = locked,
    )
}

/// Full resolution for one `use`/`dynamic use "bytes -> name[/version]"`
/// import: checks the lockfile contract for `dynamic` imports, checks a
/// requested version against what's locked, then finds the on-disk entry
/// file — folding `find_bytes_pkg_entry`'s two-shaped error and the
/// lockfile checks above into the single `Result<PathBuf, String>` shape
/// `load_bytes_module` (interpreter) wants to hand straight to
/// `RuntimeError::Custom`.
pub fn resolve_bytes_use(
    name: &str,
    version: Option<&str>,
    link: hsharp_parser::ast::ImportLinkKind,
    start_dir: &std::path::Path,
) -> Result<std::path::PathBuf, String> {
    let project_root = find_bytes_project_root(start_dir);
    let lock = read_bytes_lockfile(&project_root);

    if matches!(link, hsharp_parser::ast::ImportLinkKind::Dynamic) && !lock.contains_key(name) {
        return Err(bytes_pkg_not_locked_message(name));
    }

    if let Some(wanted) = version {
        if let Some(locked) = lock.get(name) {
            if !locked.version.is_empty() && locked.version != wanted {
                return Err(bytes_pkg_version_mismatch_message(name, wanted, &locked.version));
            }
        }
    }

    match find_bytes_pkg_entry(name, start_dir) {
        Ok(entry) => Ok(entry),
        Err(BytesResolveError::NotFound(tried)) => Err(bytes_pkg_missing_message(name, &tried)),
        Err(BytesResolveError::NoEntry(dir)) => Err(bytes_pkg_no_entry_message(name, &dir)),
    }
}

/// Bridge for the `__builtin_*` names that `std/*.h#` wrapper functions
/// call internally (e.g. `strings.h#`'s `trim()` calling
/// `__builtin_str_trim(s)`). These are NOT stdlib aliases (see
/// `resolve_stdlib_alias` below, which is now core-only) — they're the
/// std library's own private bridge down into the actual native runtime
/// primitive, the same way libc's `fopen()` is a thin wrapper over the
/// `open`/`read` syscalls. A std file can only reach these by being
/// loaded (i.e. only after a successful `use "std -> x"`), never
/// directly from user code, since `__builtin_` names aren't part of any
/// public `std ->` API.
///
/// Returns the real dispatch name to retry `call_fn` with, or `None` if
/// the primitive genuinely doesn't exist yet in this runtime (in which
/// case the caller should surface `unimplemented_builtin_message`).
pub fn resolve_builtin_dunder(name: &str) -> Option<&'static str> {
    let stripped = name.strip_prefix("__builtin_")?;
    Some(match stripped {
        // ── strings ──────────────────────────────────────────────────
        "str_trim"             => "str_trim",
        "str_trim_start"       => "str_trim_start",
        "str_trim_end"         => "str_trim_end",
        "str_split"            => "str_split",
        "str_split_whitespace" => "str_split_whitespace",
        "str_join"             => "str_join",
        "str_replace"          => "str_replace",
        "str_replace_all"      => "str_replace_all",
        "str_to_upper"         => "str_to_upper",
        "str_to_lower"         => "str_to_lower",
        "str_reverse"          => "str_reverse",
        "str_count"            => "str_count",
        "str_index_of"         => "str_index_of",
        "str_is_numeric"       => "str_is_numeric",
        // ── fs (only the subset with a real native implementation —
        // see `call.rs`'s "fs_*" match arms) ─────────────────────────
        "fs_read"        => "fs_read",
        "fs_read_bytes"  => "fs_read_bytes",
        "fs_read_lines"  => "fs_read_lines",
        "fs_write"       => "fs_write",
        "fs_write_bytes" => "fs_write_bytes",
        "fs_append"      => "fs_append",
        "fs_exists"      => "fs_exists",
        "fs_remove"      => "fs_remove",
        "fs_copy"        => "fs_copy",
        "fs_rename"      => "fs_rename",
        "fs_is_dir"      => "fs_is_dir",
        "fs_is_file"     => "fs_is_file",
        "fs_mkdir"       => "fs_mkdir_all",
        "fs_rmdir"       => "fs_rmdir",
        "fs_rmdir_all"   => "fs_rmdir_all",
        "fs_size"        => "fs_size",
        "fs_cwd"         => "fs_cwd",
        "fs_chdir"       => "fs_chdir",
        "fs_list_dir"    => "fs_list_dir",
        "fs_walk"          => "fs_walk",
        "fs_modified_time" => "fs_modified_time",
        "fs_temp_file"     => "fs_temp_file",
        "bytes_from_ints"  => "bytes_from_ints",
        "bytes_to_ints"    => "bytes_to_ints",
        "bytes_concat"     => "bytes_concat",
        "bytes_len"        => "bytes_len",
        "bytes_to_string"  => "bytes_to_string",
        // ── json ─────────────────────────────────────────────────────
        "json_parse"             => "json_parse",
        "json_parse_array"       => "json_parse_array",
        "json_stringify"         => "json_stringify",
        "json_stringify_pretty"  => "json_stringify_pretty",
        "json_empty_object"      => "json_empty_object",
        "json_set"               => "json_set",
        "json_get_str"           => "json_get_str",
        "json_get_int"           => "json_get_int",
        "json_get_float"         => "json_get_float",
        "json_get_bool"          => "json_get_bool",
        "json_get_obj"           => "json_get_obj",
        "json_get_arr"           => "json_get_arr",
        "json_has_key"           => "json_has_key",
        "json_is_null"           => "json_is_null",
        "json_query"             => "json_query",
        "json_as_int"            => "json_as_int",
        "json_as_str"            => "json_as_str",
        // ── math ─────────────────────────────────────────────────────
        // Each arm returns its own `&'static str` literal rather than
        // reusing `stripped` (the `name.strip_prefix(...)` result,
        // borrowed from the caller's `&str` — that's what actually
        // caused the E0521 "borrowed data escapes outside of function"
        // build error: `stripped`'s lifetime is tied to `name`'s, which
        // this function's signature can't promise is `'static`, even
        // though every *value* it could hold in these arms happens to
        // already be a real `'static` literal too).
        "math_sin"   => "math_sin",
        "math_cos"   => "math_cos",
        "math_tan"   => "math_tan",
        "math_asin"  => "math_asin",
        "math_acos"  => "math_acos",
        "math_atan"  => "math_atan",
        "math_atan2" => "math_atan2",
        "math_sqrt"  => "math_sqrt",
        "math_pow"   => "math_pow",
        "math_floor" => "math_floor",
        "math_ceil"  => "math_ceil",
        "math_round" => "math_round",
        "math_trunc" => "math_trunc",
        "math_log"   => "math_log",
        "math_log2"  => "math_log2",
        "math_log10" => "math_log10",
        "math_exp"   => "math_exp",
        "conv_float_to_int" => "conv_float_to_int",
        // ── regex (real grep/sed backend — see call.rs) ─────────────────
        "regex_match"      => "regex_match",
        "regex_find"       => "regex_find",
        "regex_find_all"   => "regex_find_all",
        "regex_replace"        => "regex_replace",
        "regex_replace_all"    => "regex_replace",
        "regex_split"          => "re_split_ta",
        // ── sort ─────────────────────────────────────────────────────
        "sort_ints"    => "sort_ints",
        "sort_strings" => "sort_strings",
        "sort_by"      => "sort_by",
        // ── path ─────────────────────────────────────────────────────
        "path_join"          => "path_join",
        "path_stem"          => "path_stem",
        "path_extension"     => "path_extension",
        "path_parent"        => "path_parent",
        "path_filename"      => "path_filename",
        "path_is_absolute"   => "path_is_absolute",
        "path_normalize"     => "path_normalize",
        "path_with_extension"=> "path_with_extension",
        "path_exists"        => "fs_exists",
        // ── env ──────────────────────────────────────────────────────
        "env_get"       => "env_get",
        "env_set"       => "env_set",
        "env_remove"    => "env_remove",
        "env_args"      => "env_args",
        "env_vars"      => "env_vars",
        "env_temp_dir"  => "env_temp_dir",
        "env_home"      => "env_home",
        // ── os ───────────────────────────────────────────────────────
        "os_platform"       => "os_platform",
        "os_arch"           => "os_arch",
        "os_hostname"       => "hostname",
        "os_username"       => "os_username",
        "os_home_dir"       => "os_home_dir",
        "os_temp_dir"       => "env_temp_dir",
        "os_pid"            => "getpid",
        "os_is_root"        => "os_is_root",
        "os_kernel_version" => "os_kernel_version",
        // ── process ──────────────────────────────────────────────────
        "process_run"      => "proc_run",
        "process_run_args" => "proc_run_args",
        "process_spawn"    => "proc_spawn",
        "process_kill"     => "proc_kill",
        "process_which"    => "proc_which",
        "process_shell"    => "shell",
        // ── term ─────────────────────────────────────────────────────
        "term_width"   => "term_width",
        "term_height"  => "term_height",
        "term_is_tty"  => "term_is_tty",
        // ── uuid ─────────────────────────────────────────────────────
        "uuid_v4"       => "uuid_v4",
        "uuid_is_valid" => "uuid_is_valid",
        // ── base64 / url encoding ────────────────────────────────────
        "base64_encode" => "base64_encode",
        "base64_decode" => "base64_decode",
        "base64_decode_bytes" => "base64_decode_bytes",
        "base64url_encode" => "base64url_encode",
        "base64url_decode" => "base64url_decode",
        "hmac_sha256_b64url" => "hmac_sha256_b64url",
        "url_encode"    => "url_encode",
        "url_decode"    => "url_decode",
        // ── hex (already-existing text-hex codec + hex-string XOR) ────
        "hex_encode" => "hex_encode",
        "hex_encode_bytes" => "hex_encode_bytes",
        "hex_decode" => "hex_decode",
        "hex_xor"    => "xor_hex",
        // ── conv ─────────────────────────────────────────────────────
        "conv_str_to_int"   => "conv_str_to_int",
        "conv_str_to_float" => "parse_float",
        "conv_int_to_hex"   => "conv_int_to_hex",
        "str_to_char_code"  => "str_to_char_code",
        "char_code_to_str"  => "char_code_to_str",
        // ── date / time (Howard-Hinnant civil calendar — see call.rs) ─
        "date_year"      => "date_year",
        "date_month"     => "date_month",
        "date_day"       => "date_day",
        "date_weekday"   => "date_weekday",
        "date_add_days"  => "date_add_days",
        "date_add_hours" => "date_add_hours",
        "date_diff_days" => "date_diff_days",
        "date_format"    => "date_format",
        "date_parse"     => "date_parse",
        "time_now_unix"  => "now_unix",
        "time_now_ms"    => "now_ms",
        "time_sleep_ms"  => "sleep_ms",
        // ── crypto (real hashes only — see crypto.h# doc comments for
        // which functions still have no native backend) ───────────────
        "crypto_sha256"        => "sha256",
        "crypto_sha256_bytes"  => "sha256_bytes",
        "crypto_sha512"        => "sha512",
        "crypto_sha1"          => "sha1",
        "crypto_md5"           => "md5",
        "crypto_hmac_sha256"   => "hmac_sha256",
        "crypto_hmac_sha512"   => "hmac_sha512",
        "crypto_random_bytes"  => "crypto_random_bytes",
        "crypto_random_int"    => "random_int",
        "crypto_bytes_eq"      => "crypto_bytes_eq",
        "crypto_xor_bytes"     => "crypto_xor_bytes",
        // ── db (shells out to the `sqlite3` CLI — see call.rs) ─────────
        "db_open"  => "db_open",
        "db_exec"  => "db_exec",
        "db_query" => "db_query",
        "db_close" => "db_close",
        // ── test ─────────────────────────────────────────────────────
        "test_fail" => "fail",
        "test_skip" => "skip",
        // ── collections ──────────────────────────────────────────────
        "hashmap_new"        => "hashmap_new",
        "hashmap_insert"     => "hashmap_insert",
        "hashmap_get"        => "hashmap_get",
        "hashmap_remove"     => "hashmap_remove",
        "hashmap_contains"   => "hashmap_contains",
        "hashmap_keys"       => "hashmap_keys",
        "hashmap_values"     => "hashmap_values",
        "hashmap_len"        => "hashmap_len",
        "hashset_new"        => "hashset_new",
        "hashset_insert"     => "hashset_insert",
        "hashset_remove"     => "hashset_remove",
        "hashset_contains"   => "hashset_contains",
        "hashset_len"        => "hashset_len",
        "hashset_to_array"   => "hashset_to_array",
        // ── tcp ──────────────────────────────────────────────────────
        "tcp_connect"   => "tcp_connect",
        "tcp_send"      => "tcp_send",
        "tcp_recv"      => "tcp_recv",
        "tcp_close"     => "tcp_close",
        "tcp_scan_port" => "tcp_scan_port",
        // ── http (plain HTTP/1.1, no TLS — see call.rs's http_request) ──
        "http_request" => "http_request",
        // ── sync ─────────────────────────────────────────────────────
        "atomic_add"   => "atomic_add",
        "atomic_load"  => "atomic_load",
        "atomic_store" => "atomic_store",
        // ── io ───────────────────────────────────────────────────────
        "io_read_line"    => "io_read_line",
        "io_read_char"    => "io_read_char",
        "io_write_no_nl"  => "io_write_no_nl",
        "io_flush"        => "io_flush",
        // ── sys ──────────────────────────────────────────────────────
        "sys_cpu_count"    => "sys_cpu_count",
        "sys_memory_total" => "sys_memory_total",
        "sys_memory_free"  => "sys_memory_free",
        "sys_uptime"       => "sys_uptime",
        "sys_load_avg"     => "sys_load_avg",
        "sys_disk_total"   => "sys_disk_total",
        "sys_disk_free"    => "sys_disk_free",
        "sys_page_size"    => "sys_page_size",
        "sys_is_64bit"         => "sys_is_64bit",
        "sys_is_little_endian" => "sys_is_little_endian",
        "sys_get_uid"      => "sys_get_uid",
        "sys_get_gid"      => "sys_get_gid",
        "sys_get_ppid"     => "sys_get_ppid",
        "sys_get_pid"      => "getpid",
        "sys_hostname"     => "hostname",
        "sys_sysname"      => "sys_sysname",
        "sys_machine"      => "sys_machine",
        "sys_kernel_version" => "os_kernel_version",
        _ => return None,
    })
}

/// `__builtin_*` names with no native implementation *anywhere* in this
/// runtime yet (not a resolution failure — the primitive itself hasn't
/// been written). Kept as an explicit list rather than "anything
/// `resolve_builtin_dunder` didn't match" so the error message can name
/// concretely what's missing instead of a generic "undefined function".
pub fn unimplemented_builtin_message(name: &str) -> String {
    let stripped = name.strip_prefix("__builtin_").unwrap_or(name);
    format!(
        "std library primitive '{stripped}' has no native implementation in this H# runtime yet.\n\
This isn't a missing `use` or a typo — the underlying `__builtin_{stripped}` intrinsic itself \
hasn't been implemented in the interpreter (see source-code/interpreter/src/call.rs) or the \
LLVM runtime (source-code/compiler/runtime/core.c). The std/*.h# wrapper that calls it is real, \
but has nothing to call into on this backend."
    )
}

/// **Deprecated / disabled by design.** This used to be a table mapping
/// fully-qualified `module::function` paths (e.g. `"fs::read"`,
/// `"crypto::sha256"`, `"json::parse"`) straight onto native Rust
/// builtins — which meant a program could call `fs::read(...)` and get a
/// real answer *without ever writing* `use "std -> fs"`, silently
/// bypassing the std library entirely and reaching a second, hidden
/// implementation embedded in this crate instead.
///
/// That's exactly the "embedded std lib" behavior HackerOS' H# no longer
/// wants: every `std -> X` capability must come from the real
/// `/usr/lib/HackerOS/H#/std/X.h#` file (see `std_lib_path` above), which
/// `interp.rs`'s `load_std_module` now actually loads and registers into
/// `self.fns` under `X::function` — so `call_path`'s very first lookup
/// (`self.fns.contains_key(&full)`) already finds it, before this
/// function would ever be consulted. Keeping this function return `None`
/// unconditionally (rather than deleting every call site) means: if a
/// program calls `fs::read(...)` *without* a working `use "std -> fs"`,
/// it now fails loudly with `UndefinedFn("fs::read")` — exactly what
/// should happen — instead of quietly succeeding via a shortcut the user
/// never asked for.
///
/// `use "core -> X"` is unaffected: `core` is intentionally still
/// statically embedded (see the module-level doc comment above), and its
/// resolution never went through this table in the first place.
pub fn resolve_stdlib_alias(_full_path: &str) -> Option<&'static str> {
    None
}

/// Returns true for snake_case names known to be handled by the builtin
/// match arm inside `call_fn` (the stdlib bridge). Used by `call_path` as a
/// best-effort guess only *after* the explicit alias table has already been
/// checked — this heuristic can produce a name that looks plausible but
/// isn't actually implemented, in which case `call_fn` silently returns
/// `Nil` rather than erroring. Prefer adding new mappings to
/// `resolve_stdlib_alias` over relying on this fallback.
/// **Deprecated / disabled by design** — same reasoning as
/// `resolve_stdlib_alias` above. This used to let a bare `module_function`
/// snake_case guess (e.g. `fs::read` → `fs_read`) reach a native builtin
/// even when the corresponding `std -> module` was never `use`d. Now
/// returns `false` unconditionally so that path is closed: the only way
/// to reach a std capability is a successful `use "std -> module"`, which
/// registers the real function under `module::name` and satisfies
/// `call_path`'s lookup *before* this function is ever consulted.
pub fn builtin_exists(_snake_name: &str) -> bool {
    false
}

/// Convert a parsed `serde_json::Value` into H#'s runtime `Value`.
/// JSON objects become `Value::Struct` (name `"__json"`) so they can be
/// passed around as opaque handles; JSON arrays become `Value::Array`.
pub fn json_to_value(j: &Json) -> Value {
    match j {
        Json::Null            => Value::Nil,
        Json::Bool(b)          => Value::Bool(*b),
        Json::Number(n) => {
            if let Some(i) = n.as_i64() { Value::Int(i) }
            else { Value::Float(n.as_f64().unwrap_or(0.0)) }
        }
        Json::String(s)        => Value::Str(s.clone()),
        Json::Array(items)     => Value::Array(items.iter().map(json_to_value).collect()),
        Json::Object(map) => {
            let mut fields = HashMap::new();
            for (k, v) in map {
                fields.insert(k.clone(), json_to_value(v));
            }
            Value::Struct { name: "__json".to_string(), fields }
        }
    }
}

/// Convert an H# runtime `Value` back into a `serde_json::Value` for
/// stringification.
pub fn value_to_json(v: &Value) -> Json {
    match v {
        Value::Nil          => Json::Null,
        Value::Bool(b)       => Json::Bool(*b),
        Value::Int(n)        => Json::Number((*n).into()),
        Value::Float(f)      => serde_json::Number::from_f64(*f).map(Json::Number).unwrap_or(Json::Null),
        Value::Str(s)        => Json::String(s.clone()),
        Value::Array(items)  => Json::Array(items.iter().map(value_to_json).collect()),
        Value::Struct { fields, .. } => {
            let mut map = serde_json::Map::new();
            for (k, v) in fields {
                map.insert(k.clone(), value_to_json(v));
            }
            Json::Object(map)
        }
        _ => Json::Null,
    }
}

/// Compute the new value of a container after a builtin mutating method
/// call, for receivers that are plain `Value::Array` (not user-defined
/// structs — those go through `try_user_method`'s `self`-mutation path
/// instead). Returns `None` for non-mutating methods, in which case the
/// caller should leave the original binding untouched.
pub fn compute_mutated_container(obj: &Value, method: &str, args: &[Value]) -> Option<Value> {
    match (obj, method) {
        (Value::Array(arr), "push") => {
            let mut new_arr = arr.clone();
            new_arr.push(args.first().cloned().unwrap_or(Value::Nil));
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "pop") => {
            let mut new_arr = arr.clone();
            new_arr.pop();
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "insert") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_arr = arr.clone();
            let idx = idx.min(new_arr.len());
            new_arr.insert(idx, val);
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "remove") => {
            let idx = args.first().map(|v| v.to_int()).unwrap_or(0).max(0) as usize;
            let mut new_arr = arr.clone();
            if idx < new_arr.len() { new_arr.remove(idx); }
            Some(Value::Array(new_arr))
        }
        (Value::Array(arr), "clear") => {
            let _ = arr;
            Some(Value::Array(Vec::new()))
        }
        (Value::Array(arr), "sort") => {
            let mut new_arr = arr.clone();
            new_arr.sort_by(|a, b| {
                a.to_float().partial_cmp(&b.to_float()).unwrap_or(std::cmp::Ordering::Equal)
            });
            Some(Value::Array(new_arr))
        }
        // ── HashMap ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let val = args.get(1).cloned().unwrap_or(Value::Nil);
            let mut new_fields = fields.clone();
            new_fields.insert(key, val);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashmap" => {
            let key = args.first().map(|v| v.to_string()).unwrap_or_default();
            let mut new_fields = fields.clone();
            new_fields.remove(&key);
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── HashSet ──────────────────────────────────────────────────────
        (Value::Struct { name, fields }, "insert") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let mut new_items = items;
            if !new_items.iter().any(|v| values_equal(v, &val)) {
                new_items.push(val);
            }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "remove") if name == "__hashset" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            let new_items: Vec<Value> = items.into_iter().filter(|v| !values_equal(v, &val)).collect();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(new_items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Queue (FIFO: push appends, pop removes from the front) ────────
        (Value::Struct { name, fields }, "push") if name == "__queue" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__queue" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            if !items.is_empty() { items.remove(0); }
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        // ── Stack (LIFO: push appends, pop removes from the back) ─────────
        (Value::Struct { name, fields }, "push") if name == "__stack" => {
            let val = args.first().cloned().unwrap_or(Value::Nil);
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.push(val);
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        (Value::Struct { name, fields }, "pop") if name == "__stack" => {
            let mut items = match fields.get("items") { Some(Value::Array(a)) => a.clone(), _ => Vec::new() };
            items.pop();
            let mut new_fields = fields.clone();
            new_fields.insert("items".to_string(), Value::Array(items));
            Some(Value::Struct { name: name.clone(), fields: new_fields })
        }
        _ => None,
    }
}

pub fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Float(a), Value::Float(b)) => a == b,
        (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => (*a as f64) == *b,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Bytes(a), Value::Bytes(b)) => a == b,
        (Value::Nil, Value::Nil) => true,
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Tuple(a), Value::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Struct { name: na, fields: fa }, Value::Struct { name: nb, fields: fb }) => {
            na == nb && fa.len() == fb.len()
                && fa.iter().all(|(k, v)| fb.get(k).map(|v2| values_equal(v, v2)).unwrap_or(false))
        }
        _ => false,
    }
}

pub fn compare_values(a: Value, b: Value, f: impl Fn(std::cmp::Ordering) -> bool) -> Result<Value, RuntimeError> {
    // Extended to cover `(Value::Str, Value::Str)` — plain lexicographic
    // byte-wise comparison, same ordering `String`'s own `Ord` impl
    // gives — since `std/semver.h#`'s prerelease-tag comparison (and
    // any future std code doing the same) needs `a < b` to work on
    // strings, not just numbers. Reworked to compare via
    // `std::cmp::Ordering` rather than a `Fn(f64, f64) -> bool` closure,
    // since there's no sensible way to project a string comparison
    // through "cast both sides to f64" the way the old signature
    // required.
    let ord = match (a, b) {
        (Value::Int(a), Value::Int(b)) => a.cmp(&b),
        (Value::Float(a), Value::Float(b)) => a.partial_cmp(&b).unwrap_or(std::cmp::Ordering::Equal),
        (Value::Int(a), Value::Float(b)) => (a as f64).partial_cmp(&b).unwrap_or(std::cmp::Ordering::Equal),
        (Value::Float(a), Value::Int(b)) => a.partial_cmp(&(b as f64)).unwrap_or(std::cmp::Ordering::Equal),
        (Value::Str(a), Value::Str(b)) => a.cmp(&b),
        (a, b) => return Err(RuntimeError::TypeError(format!("cannot compare {} and {}", a, b))),
    };
    Ok(Value::Bool(f(ord)))
}
