#![allow(dead_code)]

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use hsharp_parser::ast::ImportLinkKind;

/// How many parent directories are inspected while looking for a `Bit.hk`.
const ROOT_SEARCH_DEPTH: usize = 12;

/// Manifest file names, in order of preference.
const MANIFESTS: [&str; 2] = ["Bit.hk", "bit.hk"];

// ─── Lock file ───────────────────────────────────────────────────────────

/// One line of `bit.lock` (JSON Lines).
#[derive(Debug, Clone, Default)]
pub struct LockedBitLib {
    pub name: String,
    /// Short commit id (12 chars) — the directory name of the installed copy.
    pub version: String,
    pub commit: String,
    pub url: String,
    pub checksum: String,
    /// `hsharp` | `hackerlang` | `hackerscript` | ``
    pub lang: String,
    /// `hlib` | `so` | `a` | `obj` | `source`
    pub output: String,
    pub installed_at: String,
}

/// Why a `bit -> name` import couldn't be resolved to a usable entry file.
#[derive(Debug)]
pub enum BitResolveError {
    /// No library directory / flat `<name>.h#` file exists anywhere.
    NotFound(Vec<PathBuf>),
    /// A library directory exists but has no usable entry file.
    NoEntry(PathBuf),
}

// ─── Directories ─────────────────────────────────────────────────────────

fn home_dir() -> PathBuf {
    std::env::var_os("HOME")
        .filter(|h| !h.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/tmp"))
}

/// `~/.hackeros/libs` — where `bit install` puts libraries.
pub fn bit_default_libs_dir() -> PathBuf {
    home_dir().join(".hackeros/libs")
}

/// Every libraries directory that is searched, most specific first, without
/// duplicates: `BIT_HOME`, `BIT_LIBS`, each entry of `HLIB_PATH`, and the
/// default `~/.hackeros/libs`.
pub fn bit_libs_roots() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    let push = |p: PathBuf, out: &mut Vec<PathBuf>| {
        if !p.as_os_str().is_empty() && !out.contains(&p) {
            out.push(p);
        }
    };
    for var in ["BIT_HOME", "BIT_LIBS"] {
        if let Some(v) = std::env::var_os(var) {
            push(PathBuf::from(v), &mut out);
        }
    }
    if let Some(v) = std::env::var_os("HLIB_PATH") {
        for p in std::env::split_paths(&v) {
            push(p, &mut out);
        }
    }
    push(bit_default_libs_dir(), &mut out);
    out
}

/// `~/.hackeros/bit` (or `$BIT_DIR`) — bit's state directory.
pub fn bit_state_dir() -> PathBuf {
    match std::env::var_os("BIT_DIR") {
        Some(v) if !v.is_empty() => PathBuf::from(v),
        _ => home_dir().join(".hackeros/bit"),
    }
}

/// Path of the global `bit.lock`.
pub fn bit_lock_path() -> PathBuf {
    bit_state_dir().join("bit.lock")
}

/// First 12 characters of a commit id (bit's directory name for a version).
pub fn short_hash(h: &str) -> &str {
    if h.len() <= 12 || !h.is_char_boundary(12) { h } else { &h[..12] }
}

/// Library names: letters, digits, `-`, `_`, `.`; must start with a letter
/// or digit; at most 64 characters (bit's `util::valid_name`). This also
/// keeps `..` and path separators out of the directory lookup.
pub fn valid_lib_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphanumeric() => {}
        _ => return false,
    }
    name.len() <= 64 && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'))
}

// ─── Lock file reading ───────────────────────────────────────────────────

fn json_str(v: &serde_json::Value, key: &str) -> String {
    v.get(key).and_then(|x| x.as_str()).unwrap_or("").to_string()
}

/// Reads a `bit.lock` (JSON Lines). A missing or unreadable file, and any
/// malformed line, is treated as "nothing locked" — plenty of valid lookups
/// happen with no lock at all (hand-copied libraries, path dependencies).
pub fn read_bit_lock_from(path: &Path) -> HashMap<String, LockedBitLib> {
    let mut out = HashMap::new();
    let content = match std::fs::read_to_string(path) {
        Ok(c) => c,
        Err(_) => return out,
    };
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let json: serde_json::Value = match serde_json::from_str(line) {
            Ok(j) => j,
            Err(_) => continue,
        };
        let name = json_str(&json, "name");
        if name.is_empty() {
            continue;
        }
        out.insert(
            name.clone(),
            LockedBitLib {
                name,
                version: json_str(&json, "version"),
                commit: json_str(&json, "commit"),
                url: json_str(&json, "url"),
                checksum: json_str(&json, "checksum"),
                lang: json_str(&json, "lang"),
                output: json_str(&json, "output"),
                installed_at: json_str(&json, "installed_at"),
            },
        );
    }
    out
}

/// The global `bit.lock`.
pub fn read_bit_lock() -> HashMap<String, LockedBitLib> {
    read_bit_lock_from(&bit_lock_path())
}

// ─── Bit.hk (just enough of the hk-parser grammar) ───────────────────────
//
//   [section]
//   -> key => value          ! `!` starts a comment (whole lines only)
//   -> map                   ! a key without a value opens a map …
//   --> child => value       ! … one more dash per nesting level
//   -> list => [a, b, c]
//
// Nested keys are flattened to `map.child`, like bit's own `hk_get`.

#[derive(Debug, Clone)]
struct HkEntry {
    section: String,
    key: String,
    value: String,
}

fn unquote(s: &str) -> String {
    let s = s.trim();
    let bytes = s.as_bytes();
    if bytes.len() >= 2 && (bytes[0] == b'"' || bytes[0] == b'\'') && bytes[bytes.len() - 1] == bytes[0] {
        return s[1..s.len() - 1].to_string();
    }
    s.to_string()
}

fn parse_hk(content: &str) -> Vec<HkEntry> {
    let mut out = Vec::new();
    let mut section = String::new();
    let mut stack: Vec<String> = Vec::new();
    for raw in content.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('!') || line.starts_with(";;") {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            section = line[1..line.len() - 1].trim().to_lowercase();
            stack.clear();
            continue;
        }
        let dashes = line.bytes().take_while(|b| *b == b'-').count();
        if dashes == 0 || !line[dashes..].starts_with('>') {
            continue;
        }
        let rest = line[dashes + 1..].trim();
        let (key, value, has_value) = match rest.split_once("=>") {
            Some((k, v)) => (k.trim(), unquote(v), true),
            None => (rest, String::new(), false),
        };
        if key.is_empty() {
            continue;
        }
        stack.truncate(dashes - 1);
        let dotted = if stack.is_empty() { key.to_string() } else { format!("{}.{}", stack.join("."), key) };
        stack.push(key.to_string());
        if has_value {
            out.push(HkEntry { section: section.clone(), key: dotted, value });
        }
    }
    out
}

fn hk_get<'a>(hk: &'a [HkEntry], section: &str, key: &str) -> Option<&'a str> {
    hk.iter()
        .find(|e| e.section == section && e.key == key)
        .map(|e| e.value.as_str())
        .filter(|v| !v.is_empty())
}

/// `[a, "b", c]` → `["a", "b", "c"]` (a bare `a` is a one-element list).
fn hk_list(v: &str) -> Vec<String> {
    v.trim()
        .trim_start_matches('[')
        .trim_end_matches(']')
        .split(',')
        .map(unquote)
        .filter(|s| !s.is_empty())
        .collect()
}

/// `Bit.hk` / `bit.hk` in `dir`, if any.
pub fn manifest_in(dir: &Path) -> Option<PathBuf> {
    MANIFESTS.iter().map(|n| dir.join(n)).find(|p| p.is_file())
}

fn load_hk(dir: &Path) -> Vec<HkEntry> {
    manifest_in(dir)
        .and_then(|m| std::fs::read_to_string(m).ok())
        .map(|c| parse_hk(&c))
        .unwrap_or_default()
}

// ─── Project / workspace root ────────────────────────────────────────────

/// Nearest directory (walking up from `start_dir`) that has a `Bit.hk`.
/// Returns `start_dir` itself when there is none (a standalone script).
pub fn find_bit_project_root(start_dir: &Path) -> PathBuf {
    nearest_manifest_dir(start_dir).unwrap_or_else(|| start_dir.to_path_buf())
}

fn nearest_manifest_dir(start_dir: &Path) -> Option<PathBuf> {
    // Absolute path first: a relative `src` would otherwise stop at the
    // current directory instead of walking up past it.
    let start_dir = if start_dir.as_os_str().is_empty() { Path::new(".") } else { start_dir };
    let mut dir = start_dir.canonicalize().unwrap_or_else(|_| start_dir.to_path_buf());
    for _ in 0..ROOT_SEARCH_DEPTH {
        if manifest_in(&dir).is_some() {
            return Some(dir);
        }
        match dir.parent() {
            Some(p) if p != dir => dir = p.to_path_buf(),
            _ => break,
        }
    }
    None
}

/// Does the workspace at `ws_dir` list `member_dir` in `[workspace] -> members`?
fn workspace_lists_member(ws_dir: &Path, member_dir: &Path) -> bool {
    let members = read_workspace_members(ws_dir);
    if members.is_empty() {
        return false;
    }
    let rel = member_dir.strip_prefix(ws_dir).ok().map(|p| p.to_path_buf());
    let base = member_dir.file_name().map(|s| s.to_string_lossy().to_string());
    members.iter().any(|m| {
        let m = m.trim_start_matches("./").trim_end_matches('/');
        rel.as_ref().map(|r| r == Path::new(m)).unwrap_or(false) || base.as_deref() == Some(m)
    })
}

/// Like bit's `project::find_root`: the nearest `Bit.hk` directory,
/// promoted to the enclosing workspace when that directory is one of its
/// members. Falls back to `start_dir` when there is no manifest at all.
pub fn find_bit_workspace_root(start_dir: &Path) -> PathBuf {
    let near = match nearest_manifest_dir(start_dir) {
        Some(n) => n,
        None => return start_dir.to_path_buf(),
    };
    let mut up = near.parent().map(|p| p.to_path_buf());
    for _ in 0..ROOT_SEARCH_DEPTH {
        let dir = match up {
            Some(d) => d,
            None => break,
        };
        if manifest_in(&dir).is_some() && workspace_lists_member(&dir, &near) {
            return dir;
        }
        up = dir.parent().map(|p| p.to_path_buf());
    }
    near
}

/// The project directories whose `cache/` and `[dependencies]` apply to a
/// file living in `start_dir`: the nearest project and its workspace root.
fn project_roots(start_dir: &Path) -> Vec<PathBuf> {
    let near = find_bit_project_root(start_dir);
    let ws = find_bit_workspace_root(start_dir);
    if ws == near { vec![near] } else { vec![near, ws] }
}

// ─── Workspace manifests ─────────────────────────────────────────────────

/// `[workspace] -> members => [...]` of the manifest in `project_root`.
pub fn read_workspace_members(project_root: &Path) -> Vec<String> {
    let hk = load_hk(project_root);
    hk_get(&hk, "workspace", "members").map(hk_list).unwrap_or_default()
}

/// Resolve one workspace member name (as written in `use "workspace ->
/// NAME"`) to its directory, matching either the full listed path
/// (`"source-code/parser"`) or just its last component (`"parser"`), and
/// falling back to a same-named subdirectory of the workspace root.
pub fn find_workspace_member_dir(project_root: &Path, member: &str) -> Option<PathBuf> {
    for m in &read_workspace_members(project_root) {
        let m = m.trim_start_matches("./").trim_end_matches('/');
        let base = m.rsplit('/').next().unwrap_or(m);
        if m == member || base == member {
            let dir = project_root.join(m);
            if dir.is_dir() {
                return Some(dir);
            }
        }
    }
    let guess = project_root.join(member);
    if guess.is_dir() { Some(guess) } else { None }
}

/// A workspace member's entry file: the library entry when it has one,
/// else its binary entry, defaulting to `<src>/main.h#`.
pub fn workspace_member_entry(member_dir: &Path) -> PathBuf {
    lib_dir_entry(member_dir, "").unwrap_or_else(|| {
        let hk = load_hk(member_dir);
        member_dir.join(hk_get(&hk, "layout", "src").unwrap_or("src")).join("main.h#")
    })
}

// ─── Entry file of a library directory ───────────────────────────────────

fn existing(dir: &Path, rel: &str) -> Option<PathBuf> {
    if rel.is_empty() {
        return None;
    }
    let p = dir.join(rel);
    if p.is_file() { Some(p) } else { None }
}

/// The entry file of the library in `dir` (see the module docs for the
/// order). `name` may be empty (workspace members are looked up by path).
pub fn lib_dir_entry(dir: &Path, name: &str) -> Option<PathBuf> {
    lib_dir_entry_depth(dir, name, 0)
}

fn lib_dir_entry_depth(dir: &Path, name: &str, depth: usize) -> Option<PathBuf> {
    let hk = load_hk(dir);
    let src = hk_get(&hk, "layout", "src").unwrap_or("src").to_string();
    let get = |section: &str, key: &str| hk_get(&hk, section, key);

    // library entry
    for key in ["hsharp-lib-entry", "lib-entry"] {
        if let Some(p) = get("layout", key).and_then(|v| existing(dir, v)) {
            return Some(p);
        }
    }
    if let Some(p) = existing(dir, &format!("{}/lib.h#", src)) {
        return Some(p);
    }
    // legacy `[build]/[package] -> entry`, then the binary entry
    for section in ["build", "package"] {
        if let Some(p) = get(section, "entry").and_then(|v| existing(dir, v)) {
            return Some(p);
        }
    }
    for key in ["hsharp-entry", "entry"] {
        if let Some(p) = get("layout", key).and_then(|v| existing(dir, v)) {
            return Some(p);
        }
    }
    if let Some(p) = existing(dir, &format!("{}/main.h#", src)) {
        return Some(p);
    }
    // conventional file names
    for rel in ["src/lib.h#", "src/main.h#", "lib.h#", "main.h#"] {
        if let Some(p) = existing(dir, rel) {
            return Some(p);
        }
    }
    if !name.is_empty() {
        for rel in [format!("{}.h#", name), format!("src/{}.h#", name)] {
            if let Some(p) = existing(dir, &rel) {
                return Some(p);
            }
        }
    }
    // a library that is a workspace: the member named like it, else the first
    // member that has an entry
    if depth < 2 {
        if let Some(members) = hk_get(&hk, "workspace", "members").map(hk_list) {
            let matches_name = |m: &String| m.trim_end_matches('/').rsplit('/').next() == Some(name);
            for m in members.iter().filter(|m| !name.is_empty() && matches_name(m)) {
                if let Some(p) = lib_dir_entry_depth(&dir.join(m), name, depth + 1) {
                    return Some(p);
                }
            }
            for m in members.iter() {
                if let Some(p) = lib_dir_entry_depth(&dir.join(m), name, depth + 1) {
                    return Some(p);
                }
            }
        }
    }
    None
}

/// `[package] -> version` of the library in `dir`.
pub fn manifest_version(dir: &Path) -> Option<String> {
    let hk = load_hk(dir);
    hk_get(&hk, "package", "version").map(|s| s.to_string())
}

// ─── Finding the library directory ───────────────────────────────────────

/// `path` dependencies declared in `[dependencies]` of the project's Bit.hk
/// for `name`: `-> name` + `--> path => ../x`, `-> name.path => ../x`, or
/// `-> name => path ../x`. Relative paths are relative to the project.
fn path_dependency_dirs(project_root: &Path, name: &str) -> Vec<PathBuf> {
    let hk = load_hk(project_root);
    let mut out = Vec::new();
    let mut add = |raw: &str| {
        let raw = raw.trim();
        if raw.is_empty() {
            return;
        }
        let p = PathBuf::from(raw);
        let p = if p.is_absolute() { p } else { project_root.join(p) };
        if !out.contains(&p) {
            out.push(p);
        }
    };
    if let Some(v) = hk_get(&hk, "dependencies", &format!("{}.path", name)) {
        add(v);
    }
    if let Some(v) = hk_get(&hk, "dependencies", name) {
        let mut it = v.trim().splitn(2, char::is_whitespace);
        if it.next().map(|w| w.eq_ignore_ascii_case("path")).unwrap_or(false) {
            add(it.next().unwrap_or(""));
        }
    }
    out
}

/// Newest (by modification time) version directory of `<libs>/<name>/`,
/// ignoring `current` and hidden entries.
fn newest_version_dir(base: &Path) -> Option<PathBuf> {
    let mut best: Option<(std::time::SystemTime, PathBuf)> = None;
    for entry in std::fs::read_dir(base).ok()?.flatten() {
        let path = entry.path();
        let fname = entry.file_name().to_string_lossy().to_string();
        if fname == "current" || fname.starts_with('.') || !path.is_dir() {
            continue;
        }
        let mtime = entry.metadata().and_then(|m| m.modified()).unwrap_or(std::time::UNIX_EPOCH);
        if best.as_ref().map(|(t, _)| mtime > *t).unwrap_or(true) {
            best = Some((mtime, path));
        }
    }
    best.map(|(_, p)| p)
}

/// Does `dir` look like a library that holds its sources directly (as
/// opposed to a `<name>/` directory that only holds version directories)?
fn holds_sources(dir: &Path) -> bool {
    manifest_in(dir).is_some()
        || dir.join("src").is_dir()
        || std::fs::read_dir(dir)
            .map(|rd| rd.flatten().any(|e| e.file_name().to_string_lossy().ends_with(".h#")))
            .unwrap_or(false)
}

/// All directories where library `name` may live, in search order.
pub fn bit_lib_candidates(name: &str, start_dir: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    let push = |p: PathBuf, out: &mut Vec<PathBuf>| {
        if !out.contains(&p) {
            out.push(p);
        }
    };
    let roots = project_roots(start_dir);
    for root in &roots {
        push(root.join("cache/libs").join(name), &mut out);
        push(root.join("cache/source").join(name), &mut out);
    }
    for root in &roots {
        for p in path_dependency_dirs(root, name) {
            push(p, &mut out);
        }
    }
    let lock = read_bit_lock();
    for libs in bit_libs_roots() {
        let base = libs.join(name);
        if let Some(l) = lock.get(name) {
            if !l.commit.is_empty() {
                push(base.join(short_hash(&l.commit)), &mut out);
                push(base.join(&l.commit), &mut out);
            }
            if !l.version.is_empty() {
                push(base.join(&l.version), &mut out);
            }
        }
        push(base.join("current"), &mut out);
        if let Some(newest) = newest_version_dir(&base) {
            push(newest, &mut out);
        }
        if holds_sources(&base) {
            push(base, &mut out);
        }
    }
    out
}

/// Resolve `name` to `(library directory, entry file)`.
pub fn find_bit_lib(name: &str, start_dir: &Path) -> Result<(PathBuf, PathBuf), BitResolveError> {
    let mut tried: Vec<PathBuf> = Vec::new();
    let mut broken: Option<PathBuf> = None;
    for dir in bit_lib_candidates(name, start_dir) {
        tried.push(dir.clone());
        if !dir.is_dir() {
            continue;
        }
        if let Some(entry) = lib_dir_entry(&dir, name) {
            return Ok((dir, entry));
        }
        broken.get_or_insert(dir);
    }
    // flat single-file library: `<libs>/<name>.h#`
    for libs in bit_libs_roots() {
        let flat = libs.join(format!("{}.h#", name));
        tried.push(flat.clone());
        if flat.is_file() {
            let dir = libs.clone();
            return Ok((dir, flat));
        }
    }
    match broken {
        Some(dir) => Err(BitResolveError::NoEntry(dir)),
        None => Err(BitResolveError::NotFound(tried)),
    }
}

/// Entry file of library `name` (see `find_bit_lib`).
pub fn find_bit_lib_entry(name: &str, start_dir: &Path) -> Result<PathBuf, BitResolveError> {
    find_bit_lib(name, start_dir).map(|(_, entry)| entry)
}

// ─── Versions ────────────────────────────────────────────────────────────

fn strip_v(s: &str) -> &str {
    s.strip_prefix('v').or_else(|| s.strip_prefix('V')).unwrap_or(s)
}

/// Does the requested `use "bit -> name/<wanted>"` version match `have`?
/// Matches: `*`/empty/`latest`, equal strings (a leading `v` is ignored),
/// or a hex commit prefix (at least 7 hex digits) of the locked commit.
pub fn version_matches(wanted: &str, lock: &LockedBitLib) -> bool {
    let w = wanted.trim();
    if w.is_empty() || w == "*" || w.eq_ignore_ascii_case("latest") {
        return true;
    }
    if lock.version.is_empty() && lock.commit.is_empty() {
        return true;
    }
    if strip_v(w) == strip_v(&lock.version) {
        return true;
    }
    w.len() >= 7
        && w.chars().all(|c| c.is_ascii_hexdigit())
        && (lock.commit.starts_with(w) || lock.version.starts_with(w))
}

fn manifest_version_matches(wanted: &str, have: &str) -> bool {
    let w = wanted.trim();
    w.is_empty() || w == "*" || w.eq_ignore_ascii_case("latest") || strip_v(w) == strip_v(have)
}

/// Is `dir` inside one of bit's libraries directories (an `install`ed copy,
/// as opposed to a project-local or hand-placed directory)?
fn is_global_install(dir: &Path) -> bool {
    bit_libs_roots().iter().any(|r| dir.starts_with(r))
}

// ─── Messages ────────────────────────────────────────────────────────────

/// Where a hand-copied library can go, for the "can't install it" case.
fn manual_placement_help(name: &str) -> String {
    let libs = bit_libs_roots()
        .into_iter()
        .next()
        .unwrap_or_else(bit_default_libs_dir);
    format!(
        "if it cannot be installed, put its sources in one of these places:\n\
  {libs}/{name}/<version>/     (+ a symlink `current` -> <version>; sources, Bit.hk, src/)\n\
  {libs}/{name}/               (sources directly inside)\n\
  <project>/cache/libs/{name}/\n\
or point to it from Bit.hk:\n\
  [dependencies]\n\
  -> {name}\n\
  --> path => ../{name}\n\
(override the libraries directory with BIT_HOME, or HLIB_PATH=dir1:dir2)\n",
        libs = libs.display(),
        name = name,
    )
}

pub fn missing_message(name: &str, tried: &[PathBuf]) -> String {
    let locations = tried.iter().map(|p| format!("  - {}", p.display())).collect::<Vec<_>>().join("\n");
    format!(
        "bit library '{name}' not found. Looked in:\n{locations}\n\n\
install it first:\n\
  bit install {name}\n\
  bit search {name}      (find the exact name in the index)\n\
or add it to [dependencies] in Bit.hk and run: bit install\n\n\
{help}",
        name = name,
        locations = locations,
        help = manual_placement_help(name),
    )
}

pub fn no_entry_message(name: &str, dir: &Path) -> String {
    format!(
        "bit library '{name}' was found at {dir} but has no usable entry point.\n\n\
expected one of (relative to that directory):\n\
  a Bit.hk with `[layout] -> hsharp-lib-entry => ...` (or `lib-entry`)\n\
  src/lib.h#, src/main.h#, lib.h#, main.h#, {name}.h# or src/{name}.h#\n\n\
the library may be written in another language (Hacker Lang / HackerScript) — \
those cannot be imported from H# with `use \"bit -> ...\"`.\n\
if the copy is damaged, reinstall it:  bit install {name} --force\n",
        name = name,
        dir = dir.display(),
    )
}

pub fn not_locked_message(name: &str) -> String {
    format!(
        "dynamic bit library '{name}' is not recorded in bit.lock ({lock}).\n\n\
`dynamic use \"bit -> {name}\"` requires it to have already been installed\n\
by bit on this machine:\n\
  bit install {name}\n",
        name = name,
        lock = bit_lock_path().display(),
    )
}

pub fn version_mismatch_message(name: &str, wanted: &str, have: &str, source: &str) -> String {
    format!(
        "bit library '{name}' version mismatch: code requests '{wanted}', but \
{source} has '{have}' installed.\n\n\
run one of:\n\
  bit upgrade {name}              re-fetch the newest version\n\
  bit install {name} --force      reinstall (pin a revision with `bit add {name} <rev>`)\n\
or change the import to `use \"bit -> {name}/{have}\"`\n",
        name = name,
        wanted = wanted,
        have = have,
        source = source,
    )
}

pub fn invalid_name_message(name: &str) -> String {
    format!(
        "invalid bit library name '{name}' in `use \"bit -> {name}\"`: \
names contain letters, digits, `-`, `_` and `.`, start with a letter or digit, \
and are at most 64 characters long\n",
        name = name,
    )
}

// ─── Full resolution ─────────────────────────────────────────────────────

/// Full resolution of one `use`/`dynamic use "bit -> name[/version]"`:
/// validates the name, checks the `dynamic` contract against `bit.lock`,
/// finds the library and its entry file, and checks a requested version
/// against `bit.lock` (installed copies) or the library's own `Bit.hk`
/// (project-local / hand-placed copies).
pub fn resolve_bit_use(
    name: &str,
    version: Option<&str>,
    link: ImportLinkKind,
    start_dir: &Path,
) -> Result<PathBuf, String> {
    if !valid_lib_name(name) {
        return Err(invalid_name_message(name));
    }
    let lock = read_bit_lock();

    if matches!(link, ImportLinkKind::Dynamic) && !lock.contains_key(name) {
        return Err(not_locked_message(name));
    }

    let (dir, entry) = match find_bit_lib(name, start_dir) {
        Ok(found) => found,
        Err(BitResolveError::NotFound(tried)) => return Err(missing_message(name, &tried)),
        Err(BitResolveError::NoEntry(dir)) => return Err(no_entry_message(name, &dir)),
    };

    if let Some(wanted) = version {
        let locked = lock.get(name).filter(|_| is_global_install(&dir));
        match locked {
            Some(l) => {
                if !version_matches(wanted, l) {
                    let have = if l.version.is_empty() { &l.commit } else { &l.version };
                    return Err(version_mismatch_message(name, wanted, have, "bit.lock"));
                }
            }
            None => {
                if let Some(have) = manifest_version(&dir) {
                    if !manifest_version_matches(wanted, &have) {
                        let source = format!("the Bit.hk in {}", dir.display());
                        return Err(version_mismatch_message(name, wanted, &have, &source));
                    }
                }
            }
        }
    }
    Ok(entry)
}

// ─── `[edition]` (H# only) ───────────────────────────────────────────────
//
//   [package]
//   -> lang => h#                 ! the section is honoured ONLY when `lang` names H#
//
//   [edition]
//   -> edition => 2026            ! default edition for files without `using "<year>"`
//
// Precedence for a file with no `using` of its own (highest first):
//   `--edition` flag  >  `HSHARP_EDITION`  >  the project's `[edition]`  >  newest.
// A *dependency's* files (another Bit.hk root) use that dependency's own
// `[edition]` instead of the importing project's default — see `edition_for_file`.

/// Does the manifest's `lang` explicitly include H#? (`h#`, `hsharp`,
/// `h-sharp`, `hsh`, `hs#`; case/space/dash/underscore/quote insensitive —
/// the same spellings `bit` accepts. Note `hs` alone means HackerScript.)
fn hk_lang_includes_hsharp(hk: &[HkEntry]) -> bool {
    let raw = hk_get(hk, "package", "lang")
        .or_else(|| hk_get(hk, "project", "lang"))
        .or_else(|| hk_get(hk, "build", "lang"));
    let Some(raw) = raw else { return false };
    hk_list(raw).iter().any(|l| {
        let t: String = l
            .to_lowercase()
            .chars()
            .filter(|c| !matches!(c, ' ' | '-' | '_' | '"' | '\'' | '[' | ']'))
            .collect();
        matches!(t.as_str(), "h#" | "hsharp" | "hsh" | "hs#")
    })
}

/// The `[edition] -> edition` of the `Bit.hk` in `dir`.
///
/// * `Ok(None)`   — no manifest, no `[edition]` section, or `lang` isn't H#
///                  (the section is deliberately ignored for other languages);
/// * `Ok(Some(e))` — a valid, supported edition;
/// * `Err(msg)`   — the section is present for an H# project but its value is
///                  not a supported edition (message names the file).
pub fn manifest_edition(dir: &Path) -> Result<Option<hsharp_parser::edition::Edition>, String> {
    let Some(manifest) = manifest_in(dir) else { return Ok(None) };
    let Ok(content) = std::fs::read_to_string(&manifest) else { return Ok(None) };
    let hk = parse_hk(&content);
    if !hk_lang_includes_hsharp(&hk) {
        return Ok(None);
    }
    let Some(raw) = hk_get(&hk, "edition", "edition") else { return Ok(None) };
    hsharp_parser::edition::Edition::parse(raw).map(Some).map_err(|e| {
        format!("{}: [edition] -> edition => {}: {}\n  hint: {}", manifest.display(), raw, e.message(), e.hints().join("; "))
    })
}

/// Root of the `Bit.hk` project that owns `dir` (nearest manifest walking
/// up), canonicalized; `None` if there is none.
pub fn manifest_dir_of(dir: &Path) -> Option<PathBuf> {
    nearest_manifest_dir(dir).map(|d| std::fs::canonicalize(&d).unwrap_or(d))
}

/// Edition declared by the project governing `start_dir` (nearest `Bit.hk`
/// walking up), if any. Used by the CLI to seed the default edition.
pub fn project_edition(start_dir: &Path) -> Result<Option<hsharp_parser::edition::Edition>, String> {
    match nearest_manifest_dir(start_dir) {
        Some(dir) => manifest_edition(&dir),
        None => Ok(None),
    }
}

/// Default edition for `file` when it has no `using` of its own, decided by
/// *which project owns the file*:
///
/// * the file belongs to the entry project (`entry_root`) → `None`, i.e. the
///   process-wide default the CLI already resolved (flag > env > `[edition]`
///   > newest), so a `--edition` flag really does win for your own code;
/// * the file belongs to another `Bit.hk` root (a `bit` library, a path
///   dependency, `-I` include) → that project's own `[edition]`, so a
///   library written for another edition keeps compiling as itself;
/// * no manifest, or no `[edition]` → `None`.
///
/// An unreadable/invalid `[edition]` in a dependency yields `None` here; the
/// CLI surfaces invalid editions of the *entry* project up front.
pub fn edition_for_file(file: &Path, entry_root: Option<&Path>) -> Option<hsharp_parser::edition::Edition> {
    let dir = file.parent()?;
    let owner = nearest_manifest_dir(dir)?;
    if let Some(root) = entry_root {
        let same = |a: &Path, b: &Path| match (std::fs::canonicalize(a), std::fs::canonicalize(b)) {
            (Ok(x), Ok(y)) => x == y,
            _ => a == b,
        };
        if same(&owner, root) {
            return None;
        }
    }
    manifest_edition(&owner).ok().flatten()
}

// ─── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::Mutex;

    // Tests touch process-wide environment variables.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn tmp(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("bit_resolve_test_{}_{}", tag, std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d).unwrap();
        d
    }

    fn write(p: &Path, s: &str) {
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, s).unwrap();
    }

    fn isolated_env(root: &Path) {
        std::env::set_var("HOME", root.join("home"));
        std::env::set_var("BIT_HOME", root.join("libs"));
        std::env::set_var("BIT_DIR", root.join("state"));
        std::env::remove_var("BIT_LIBS");
        std::env::remove_var("HLIB_PATH");
    }

    #[test]
    fn hk_parses_nested_keys_and_comments() {
        let hk = parse_hk(
            "! comment\n[package]\n-> name => \"x\"\n[dependencies]\n-> mine\n--> path => ../mine\n--> output => a\n-> tui => rev v1.0\n[workspace]\n-> members => [core, \"cli\"]\n",
        );
        assert_eq!(hk_get(&hk, "package", "name"), Some("x"));
        assert_eq!(hk_get(&hk, "dependencies", "mine.path"), Some("../mine"));
        assert_eq!(hk_get(&hk, "dependencies", "mine.output"), Some("a"));
        assert_eq!(hk_get(&hk, "dependencies", "tui"), Some("rev v1.0"));
        assert_eq!(hk_list(hk_get(&hk, "workspace", "members").unwrap()), vec!["core", "cli"]);
    }

    #[test]
    fn lock_is_json_lines() {
        let d = tmp("lock");
        write(
            &d.join("bit.lock"),
            "{\"name\":\"mold\",\"version\":\"a1b2c3d4e5f6\",\"commit\":\"a1b2c3d4e5f6aaaaaaaa\",\"lang\":\"hsharp\"}\n\nnot json\n{\"name\":\"tui\",\"version\":\"111111111111\"}\n",
        );
        let l = read_bit_lock_from(&d.join("bit.lock"));
        assert_eq!(l.len(), 2);
        assert_eq!(l["mold"].lang, "hsharp");
        assert!(version_matches("a1b2c3d4e5f6", &l["mold"]));
        assert!(version_matches("a1b2c3d", &l["mold"]));
        assert!(version_matches("*", &l["mold"]));
        assert!(!version_matches("1.0", &l["mold"]));
    }

    #[test]
    fn names_are_validated() {
        assert!(valid_lib_name("mold"));
        assert!(valid_lib_name("H2D"));
        assert!(valid_lib_name("a.b-c_d"));
        assert!(!valid_lib_name(""));
        assert!(!valid_lib_name(".."));
        assert!(!valid_lib_name("../x"));
        assert!(!valid_lib_name("-x"));
    }

    #[test]
    fn resolves_installed_current_and_flat_and_path_dep() {
        let _g = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let root = tmp("resolve");
        isolated_env(&root);

        // installed copy: libs/mold/aaaaaaaaaaaa/{Bit.hk,src/lib.h#} + current
        let v = root.join("libs/mold/aaaaaaaaaaaa");
        write(&v.join("Bit.hk"), "[package]\n-> name => mold\n-> version => 0.3.0\n[layout]\n-> src => src\n");
        write(&v.join("src/lib.h#"), "pub fn a() is end\n");
        #[cfg(unix)]
        std::os::unix::fs::symlink("aaaaaaaaaaaa", root.join("libs/mold/current")).unwrap();
        write(
            &root.join("state/bit.lock"),
            "{\"name\":\"mold\",\"version\":\"aaaaaaaaaaaa\",\"commit\":\"aaaaaaaaaaaa1111\",\"lang\":\"hsharp\"}\n",
        );

        // a project
        let proj = root.join("proj");
        write(&proj.join("Bit.hk"), "[package]\n-> name => proj\n[dependencies]\n-> mine\n--> path => ../mine\n");
        write(&proj.join("src/main.h#"), "fn main() is end\n");
        let start = proj.join("src");

        let e = resolve_bit_use("mold", None, ImportLinkKind::Static, &start).unwrap();
        assert!(e.ends_with("src/lib.h#"), "{}", e.display());
        // version by lock
        assert!(resolve_bit_use("mold", Some("aaaaaaaaaaaa"), ImportLinkKind::Static, &start).is_ok());
        assert!(resolve_bit_use("mold", Some("9.9.9"), ImportLinkKind::Static, &start).is_err());
        // dynamic needs a lock entry
        assert!(resolve_bit_use("mold", None, ImportLinkKind::Dynamic, &start).is_ok());

        // hand-copied, flat layout — no lock, no install
        write(&root.join("libs/flat/lib.h#"), "pub fn f() is end\n");
        write(&root.join("libs/flat/Bit.hk"), "[package]\n-> version => 1.2.0\n");
        assert!(resolve_bit_use("flat", None, ImportLinkKind::Static, &start).is_ok());
        assert!(resolve_bit_use("flat", Some("1.2.0"), ImportLinkKind::Static, &start).is_ok());
        assert!(resolve_bit_use("flat", Some("v1.2.0"), ImportLinkKind::Static, &start).is_ok());
        assert!(resolve_bit_use("flat", Some("2.0"), ImportLinkKind::Static, &start).is_err());
        assert!(resolve_bit_use("flat", None, ImportLinkKind::Dynamic, &start).is_err());

        // flat single file
        write(&root.join("libs/single.h#"), "pub fn s() is end\n");
        assert!(resolve_bit_use("single", None, ImportLinkKind::Static, &start).is_ok());

        // project-local cache/libs and a path dependency
        write(&proj.join("cache/libs/loc/src/lib.h#"), "pub fn l() is end\n");
        assert!(resolve_bit_use("loc", None, ImportLinkKind::Static, &start).is_ok());
        write(&root.join("mine/src/lib.h#"), "pub fn m() is end\n");
        assert!(resolve_bit_use("mine", None, ImportLinkKind::Static, &start).is_ok());

        // missing + bad names
        let err = resolve_bit_use("nope", None, ImportLinkKind::Static, &start).unwrap_err();
        assert!(err.contains("bit install nope") && err.contains("cache/libs/nope"), "{}", err);
        assert!(resolve_bit_use("../etc", None, ImportLinkKind::Static, &start).is_err());

        // directory without an entry
        write(&root.join("libs/hollow/README"), "x");
        write(&root.join("libs/hollow/Bit.hk"), "[package]\n-> name => hollow\n");
        assert!(matches!(find_bit_lib("hollow", &start), Err(BitResolveError::NoEntry(_))));
    }

    #[test]
    fn workspace_root_promotion_and_members() {
        let root = tmp("ws");
        write(&root.join("Bit.hk"), "[workspace]\n-> members => [core, tools/cli]\n");
        write(&root.join("core/Bit.hk"), "[package]\n-> name => core\n");
        write(&root.join("core/src/lib.h#"), "");
        write(&root.join("tools/cli/Bit.hk"), "[package]\n-> name => cli\n");
        write(&root.join("tools/cli/src/main.h#"), "");
        assert_eq!(find_bit_project_root(&root.join("core/src")), root.join("core"));
        assert_eq!(find_bit_workspace_root(&root.join("core/src")), root);
        assert_eq!(find_workspace_member_dir(&root, "cli"), Some(root.join("tools/cli")));
        assert!(workspace_member_entry(&root.join("core")).ends_with("src/lib.h#"));
        assert!(workspace_member_entry(&root.join("tools/cli")).ends_with("src/main.h#"));
    }

    #[test]
    fn edition_section_is_read_only_for_hsharp_projects() {
        let root = tmp("edition_lang");
        let w = |dir: &str, body: &str| write(&root.join(dir).join("Bit.hk"), body);
        w("a", "[package]\n-> name => a\n-> lang => h#\n[edition]\n-> edition => 2026\n");
        w("b", "[package]\n-> name => b\n-> lang => hs\n[edition]\n-> edition => 2026\n");
        w("c", "[package]\n-> name => c\n[edition]\n-> edition => 2026\n");
        w("d", "[package]\n-> name => d\n-> lang => h#\n");
        w("e", "[package]\n-> name => e\n-> lang => [\"HackerScript\", \"H-Sharp\"]\n[edition]\n-> edition => \"2026\"\n");
        w("f", "[package]\n-> name => f\n-> lang => h#\n[edition]\n-> edition => 2099\n");
        w("g", "[package]\n-> name => g\n-> lang => h#\n[edition]\n-> edition => soon\n");
        let e = hsharp_parser::edition::Edition::E2026;
        assert_eq!(manifest_edition(&root.join("a")), Ok(Some(e)));
        assert_eq!(manifest_edition(&root.join("b")), Ok(None), "hs = HackerScript -> ignored");
        assert_eq!(manifest_edition(&root.join("c")), Ok(None), "no lang -> ignored");
        assert_eq!(manifest_edition(&root.join("d")), Ok(None), "no section");
        assert_eq!(manifest_edition(&root.join("e")), Ok(Some(e)), "h# among several langs");
        let err = manifest_edition(&root.join("f")).unwrap_err();
        assert!(err.contains("newer") && err.contains("Bit.hk"), "{err}");
        assert!(manifest_edition(&root.join("g")).unwrap_err().contains("four-digit"));
        assert_eq!(manifest_edition(&root.join("nowhere")), Ok(None));
    }

    #[test]
    fn edition_for_file_prefers_the_owning_project() {
        let root = tmp("edition_owner");
        let hk = "[package]\n-> name => x\n-> lang => h#\n[edition]\n-> edition => 2026\n";
        write(&root.join("app/Bit.hk"), hk);
        write(&root.join("app/src/main.h#"), "fn main() is end\n");
        write(&root.join("dep/Bit.hk"), hk);
        write(&root.join("dep/src/lib.h#"), "pub fn f() is end\n");
        write(&root.join("loose/x.h#"), "fn x() is end\n");
        let app = root.join("app");
        let e = hsharp_parser::edition::Edition::E2026;
        // entry project's own files -> process-wide default (None here)
        assert_eq!(edition_for_file(&app.join("src/main.h#"), Some(&app)), None);
        // a dependency's files -> that dependency's own [edition]
        assert_eq!(edition_for_file(&root.join("dep/src/lib.h#"), Some(&app)), Some(e));
        // no Bit.hk anywhere above -> None
        assert_eq!(edition_for_file(&root.join("loose/x.h#"), Some(&app)), None);
        assert_eq!(project_edition(&app.join("src")), Ok(Some(e)));
    }
}
