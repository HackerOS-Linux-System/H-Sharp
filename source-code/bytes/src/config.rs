use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BytesProject {
    pub package:      PackageMeta,
    pub run:          Option<RunConfig>,
    pub dependencies: HashMap<String, String>,
    pub python:       Option<PythonConfig>,
    pub jit:          Option<JitConfig>,
    pub workspace:    Option<WorkspaceConfig>,
    pub release:      Option<ReleaseConfig>,
    pub registry:     Option<RegistryConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ReleaseConfig {
    /// "h#" (LLVM, statically linked, detailed errors — v0.8 default) or
    /// "hsharp" (internal Cranelift-era typechecker, terse errors).
    /// "hhc"/"llvm" are accepted as legacy aliases for "h#".
    pub backend:  Option<String>,
    pub optimize: Option<String>, // "O0".."O3"
    pub lto:      Option<bool>,
    pub strip:    Option<bool>,
}

/// §13: per-project registry configuration.
///
/// ```text
/// [dependencies]
/// -> mold     => latest        ! latest tag (default)
/// -> obsidian => 1.2.0          ! pin to git tag v1.2.0 / 1.2.0
/// -> nidus    => source         ! always build from HEAD of default branch
///
/// [registry]
/// -> mode    => release   ! global default: "release" (latest tag) | "source" (HEAD)
/// -> mirror  => https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.json
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    /// "release" (default: resolve latest git tag) or "source" (always
    /// clone HEAD of the default branch — like `cargo install --git`
    /// without a tag).
    pub mode: String,
    /// Override the index.json URL (defaults to the Bytes-Repository one).
    pub mirror: Option<String>,
}

impl Default for RegistryConfig {
    fn default() -> Self {
        Self { mode: "release".to_string(), mirror: None }
    }
}

/// Per-dependency version spec, parsed from the `[dependencies]` value.
#[derive(Debug, Clone, PartialEq)]
pub enum DepSpec {
    /// `latest` — resolve the newest git tag (cargo-style).
    Latest,
    /// `1.2.0` (or any string starting with a digit) — pin to that git tag
    /// (with or without a leading `v`, both are tried).
    Version(String),
    /// `source` — always clone HEAD of the default branch, ignoring tags.
    Source,
}

impl DepSpec {
    pub fn parse(s: &str) -> Self {
        match s.trim() {
            "latest" | "" => DepSpec::Latest,
            "source"      => DepSpec::Source,
            v             => DepSpec::Version(v.to_string()),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PackageMeta {
    pub name:        String,
    pub version:     String,
    pub description: Option<String>,
    pub entry:       Option<String>,
    pub authors:     Vec<String>,
    pub license:     Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RunConfig {
    pub args:    Vec<String>,
    pub env:     HashMap<String, String>,
    pub timeout: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PythonConfig {
    pub version:  String,
    pub venv:     Option<String>,
    pub packages: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct JitConfig {
    pub cache_dir:  Option<String>,
    pub warmup:     Option<bool>,
    pub tier:       Option<String>,
    pub hot_thresh: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct WorkspaceConfig {
    pub members:   Vec<String>,
    pub languages: HashMap<String, String>,
    pub mode:      Option<String>,
}

pub const SUPPORTED_LANGUAGES: &[(&str, &str)] = &[
    ("h#",         "H# (hsharp)"),
    ("rust",       "Rust (cargo)"),
    ("c",          "C (gcc/clang)"),
    ("cpp",        "C++ (g++/clang++)"),
    ("zig",        "Zig"),
    ("odin",       "Odin"),
    ("crystal",    "Crystal"),
    ("typescript", "TypeScript (tsc/deno)"),
    ("javascript", "JavaScript (node)"),
    ("golang",     "Go"),
    ("kotlin",     "Kotlin (kotlinc)"),
    ("lua",        "Lua"),
    ("dart",       "Dart"),
    ("vala",       "Vala"),
    ("python",     "Python"),
    ("swift",      "Swift"),
    ("nim",        "Nim"),
    ("d",          "D (dmd/ldc)"),
    ("julia",      "Julia"),
    ("elixir",     "Elixir"),
];

impl BytesProject {
    pub fn load(path: &str) -> anyhow::Result<Self> {
        let s = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;
        if path.ends_with(".toml") || path.ends_with("bytes.toml") {
            toml::from_str(&s).map_err(|e| anyhow::anyhow!("parse bytes.toml: {}", e))
        } else if path.ends_with(".hk") || path.ends_with("bytes.hk") {
            Self::from_hk(&s)
        } else {
            toml::from_str(&s).or_else(|_| Self::from_hk(&s))
            .map_err(|e| anyhow::anyhow!("parse config: {}", e))
        }
    }

    /// Parse bytes.hk using hk-parser 0.3.0
    fn from_hk(content: &str) -> anyhow::Result<Self> {
        use hk_parser::parse_hk;

        let config = parse_hk(content)
        .map_err(|e| anyhow::anyhow!("parse bytes.hk: {:?}", e))?;

        let mut proj = BytesProject::default();

        // bytes.hk uses [project] in some templates (chker, eic) and
        // [package] in others (bytes new). Accept both — [project] wins
        // if both happen to be present, since it's the more common
        // convention in hand-written manifests.
        let pkg_section = config.get("project").or_else(|| config.get("package"));
        if let Some(pkg_section) = pkg_section {
            if let Ok(map) = pkg_section.as_map() {
                if let Some(v) = map.get("name")    { proj.package.name    = v.as_string().unwrap_or_default(); }
                if let Some(v) = map.get("version") { proj.package.version = v.as_string().unwrap_or_default(); }
                if let Some(v) = map.get("description") { proj.package.description = Some(v.as_string().unwrap_or_default()); }
                if let Some(v) = map.get("entry")   { proj.package.entry   = Some(v.as_string().unwrap_or_default()); }
            }
        }

        // Entry can also live under [build] -> entry (chker/eic convention)
        if proj.package.entry.is_none() {
            if let Some(build_section) = config.get("build") {
                if let Ok(map) = build_section.as_map() {
                    if let Some(v) = map.get("entry") {
                        proj.package.entry = Some(v.as_string().unwrap_or_default());
                    }
                }
            }
        }

        // Safety net: never allow an empty package name (it would produce
        // an output path of just "build/", which is a directory, not a
        // file — causing the linker error
        // "cannot open output file build/: Jest katalogiem").
        if proj.package.name.trim().is_empty() {
            proj.package.name = std::env::current_dir()
            .ok()
            .and_then(|d| d.file_name().map(|n| n.to_string_lossy().to_string()))
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "out".to_string());
        }

        if let Some(deps_section) = config.get("dependencies") {
            if let Ok(map) = deps_section.as_map() {
                for (k, v) in map {
                    proj.dependencies.insert(k.clone(), v.as_string().unwrap_or_else(|_| "latest".to_string()));
                }
            }
        }

        if let Some(jit_section) = config.get("jit") {
            if let Ok(map) = jit_section.as_map() {
                let mut jit = JitConfig::default();
                if let Some(v) = map.get("tier")       { jit.tier       = Some(v.as_string().unwrap_or_default()); }
                if let Some(v) = map.get("hot_thresh")  { jit.hot_thresh = v.as_number().ok().map(|n| n as u64); }
                if let Some(v) = map.get("cache_dir")   { jit.cache_dir  = Some(v.as_string().unwrap_or_default()); }
                proj.jit = Some(jit);
            }
        }

        if let Some(py_section) = config.get("python") {
            if let Ok(map) = py_section.as_map() {
                let mut py = PythonConfig::default();
                if let Some(v) = map.get("version") { py.version = v.as_string().unwrap_or_else(|_| "3".to_string()); }
                if let Some(v) = map.get("packages") {
                    if let Ok(arr) = v.as_array() {
                        py.packages = arr.iter().filter_map(|i| i.as_string().ok()).collect();
                    }
                }
                proj.python = Some(py);
            }
        }

        if let Some(rel_section) = config.get("release") {
            if let Ok(map) = rel_section.as_map() {
                let mut rel = ReleaseConfig::default();
                if let Some(v) = map.get("backend")  { rel.backend  = Some(v.as_string().unwrap_or_default()); }
                if let Some(v) = map.get("optimize") { rel.optimize = Some(v.as_string().unwrap_or_default()); }
                if let Some(v) = map.get("lto")   { rel.lto   = v.as_string().ok().map(|s| s == "true"); }
                if let Some(v) = map.get("strip") { rel.strip = v.as_string().ok().map(|s| s == "true"); }
                proj.release = Some(rel);
            }
        }

        if let Some(reg_section) = config.get("registry") {
            if let Ok(map) = reg_section.as_map() {
                let mut reg = RegistryConfig::default();
                if let Some(v) = map.get("mode")   { reg.mode = v.as_string().unwrap_or_else(|_| "release".to_string()); }
                if let Some(v) = map.get("mirror") { reg.mirror = Some(v.as_string().unwrap_or_default()); }
                proj.registry = Some(reg);
            }
        }

        if let Some(ws_section) = config.get("workspace") {
            if let Ok(map) = ws_section.as_map() {
                let mut ws = WorkspaceConfig::default();
                if let Some(v) = map.get("members") {
                    if let Ok(arr) = v.as_array() {
                        ws.members = arr.iter().filter_map(|i| i.as_string().ok()).collect();
                    }
                }
                if let Some(lang_map) = map.get("languages") {
                    if let Ok(lm) = lang_map.as_map() {
                        for (k, v) in lm {
                            ws.languages.insert(k.clone(), v.as_string().unwrap_or_default());
                        }
                    }
                }
                if let Some(v) = map.get("mode") { ws.mode = Some(v.as_string().unwrap_or_default()); }
                proj.workspace = Some(ws);
            }
        }

        Ok(proj)
    }

    pub fn find() -> Option<String> {
        for name in &["bytes.toml", "Bytes.toml", "bytes.hk", "Bytes.hk"] {
            if Path::new(name).exists() { return Some(name.to_string()); }
        }
        None
    }

    pub fn entry_file(&self) -> String {
        self.package.entry.clone().unwrap_or_else(|| "src/main.h#".to_string())
    }

    pub fn is_workspace(&self) -> bool {
        self.workspace.as_ref().map(|w| !w.members.is_empty()).unwrap_or(false)
    }
}

pub fn ram_cache_dir() -> PathBuf {
    let base = dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(format!(".hackeros/H#/libs/session-{}", std::process::id()));
    std::fs::create_dir_all(&base).ok();
    base
}

pub fn project_cache_dir(project_root: &Path) -> PathBuf {
    let dir = project_root.join(".cache");
    std::fs::create_dir_all(&dir).ok();
    dir
}

pub fn default_bytes_toml(name: &str) -> String {
    format!(r#"[package]
        name        = "{name}"
        version     = "0.1.0"
        description = "H# project"
        entry       = "src/main.h#"

        [jit]
        tier       = "jit"
        hot_thresh = 100

        [run]
        # args    = ["--verbose"]
        # timeout = 30

        [dependencies]
        # scanner = "latest"
        # tui     = "latest"
        "#, name = name)
}

pub fn default_bytes_hk(name: &str) -> String {
    format!(r#"! H# project — bytes.hk

        [package]
        -> name        => {name}
        -> version     => 0.1.0
        -> description => H# script project
        -> entry       => src/main.h#

        [jit]
        -> tier       => jit
        -> hot_thresh => 100

        [run]
        ! -> args => ["--verbose"]

        [dependencies]
        ! scanner => latest

        [workspace]
        -> members => []
        -> mode    => standard
        "#, name = name)
}

pub fn workspace_bytes_hk(name: &str, members: &[(&str, &str)]) -> String {
    let member_list: Vec<String> = members.iter().map(|(m, _)| format!("\"{}\"", m)).collect();
    let lang_entries: String = members.iter()
    .map(|(m, lang)| format!("--> {} => {}", m, lang))
    .collect::<Vec<_>>().join("\n");
    format!(r#"! H# SPECIAL workspace — bytes.hk

        [workspace]
        -> name    => {name}
        -> version => 0.1.0
        -> mode    => special
        -> members => [{members}]
        -> languages
        {langs}

        [build]
        -> parallel => true
        -> cache    => .cache/
        "#, name = name, members = member_list.join(", "), langs = lang_entries)
}

pub fn cleanup_stale_sessions() {
    let libs_base = dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(".hackeros/H#/libs");
    if !libs_base.exists() { return; }
    if let Ok(entries) = std::fs::read_dir(&libs_base) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if let Some(pid_str) = name.strip_prefix("session-") {
                if let Ok(pid) = pid_str.parse::<u32>() {
                    if !std::path::Path::new(&format!("/proc/{}", pid)).exists() {
                        let _ = std::fs::remove_dir_all(entry.path());
                    }
                }
            }
        }
    }
}
