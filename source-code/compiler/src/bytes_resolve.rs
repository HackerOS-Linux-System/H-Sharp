use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// One entry out of `bytes.lock`'s `"packages"` object.
pub struct LockedBytesPkg {
    pub version: String,
}

/// Why a `bytes -> name` import couldn't be resolved to a usable entry
/// file — see the identical type in `hsharp-interpreter::helpers` /
/// `hsharp-typecheck::bytes_resolve`.
pub enum BytesResolveError {
    NotFound(Vec<PathBuf>),
    NoEntry(PathBuf),
}

/// `~/.hackeros/H#/build/cache/packages` — see
/// `hsharp-interpreter::helpers::bytes_global_cache_dir`.
pub fn bytes_global_cache_dir() -> PathBuf {
    let base = std::env::var("HOME")
        .map(|h| PathBuf::from(h).join(".hackeros/H#/build/cache"))
        .unwrap_or_else(|_| PathBuf::from("/tmp/.hackeros/H#/build/cache"));
    base.join("packages")
}

/// See `hsharp-interpreter::helpers::find_bytes_project_root`.
pub fn find_bytes_project_root(start_dir: &Path) -> PathBuf {
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

/// See `hsharp-interpreter::helpers::bytes_pkg_cache_roots`.
fn pkg_cache_roots(start_dir: &Path) -> Vec<PathBuf> {
    let project_root = find_bytes_project_root(start_dir);
    vec![project_root.join("build/cache/packages"), bytes_global_cache_dir()]
}

/// See `hsharp-interpreter::helpers::read_bytes_lockfile`. Uses
/// `serde_json` (already a dependency of this crate) exactly like the
/// interpreter's version does.
pub fn read_bytes_lockfile(project_root: &Path) -> HashMap<String, LockedBytesPkg> {
    let mut out = HashMap::new();
    let path = project_root.join("bytes.lock");
    let content = match std::fs::read_to_string(&path) {
        Ok(c) => c,
        Err(_) => return out,
    };
    let json: serde_json::Value = match serde_json::from_str(&content) {
        Ok(j) => j,
        Err(_) => return out,
    };
    let pkgs = match json.get("packages").and_then(|p| p.as_object()) {
        Some(p) => p,
        None => return out,
    };
    for (name, entry) in pkgs {
        let version = entry.get("version").and_then(|v| v.as_str()).unwrap_or("").to_string();
        out.insert(name.clone(), LockedBytesPkg { version });
    }
    out
}

/// See `hsharp-interpreter::helpers::bytes_pkg_manifest_entry`.
fn manifest_entry(pkg_dir: &Path) -> Option<PathBuf> {
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

/// See `hsharp-interpreter::helpers::find_bytes_pkg_entry`.
pub fn find_pkg_entry(name: &str, start_dir: &Path) -> Result<PathBuf, BytesResolveError> {
    let mut tried = Vec::new();
    let mut broken: Option<PathBuf> = None;
    for cache in pkg_cache_roots(start_dir) {
        let pkg_dir = cache.join(name);
        if pkg_dir.is_dir() {
            tried.push(pkg_dir.clone());
            if let Some(entry) = manifest_entry(&pkg_dir) {
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

/// See `hsharp-interpreter::helpers::bytes_pkg_missing_message`.
pub fn missing_message(name: &str, tried: &[PathBuf]) -> String {
    let locations = tried.iter().map(|p| format!("  - {}", p.display())).collect::<Vec<_>>().join("\n");
    format!(
        "bytes package '{name}' not found. Looked in:\n{locations}\n\n\
install it first:\n\
  bytes add {name}\n\
  bytes install\n",
        name = name, locations = locations,
    )
}

/// See `hsharp-interpreter::helpers::bytes_pkg_no_entry_message`.
pub fn no_entry_message(name: &str, pkg_dir: &Path) -> String {
    format!(
        "bytes package '{name}' was found at {dir} but has no usable entry point.\n\n\
expected one of (relative to that directory):\n\
  a `Bytes.hk`/`bytes.hk` with `[build] -> entry => ...`\n\
  src/lib.h#, src/main.h#, lib.h#, main.h#, or {name}.h#\n",
        name = name, dir = pkg_dir.display(),
    )
}

/// See `hsharp-interpreter::helpers::bytes_pkg_version_mismatch_message`.
pub fn version_mismatch_message(name: &str, wanted: &str, locked: &str) -> String {
    format!(
        "bytes package '{name}' version mismatch: code requests '{wanted}', but \
bytes.lock has '{locked}' installed.\n\n\
run one of:\n\
  bytes update {name}          ;; re-lock to the latest matching version\n\
  bytes add {name}/{wanted}    ;; explicitly re-pin and reinstall\n",
        name = name, wanted = wanted, locked = locked,
    )
}
