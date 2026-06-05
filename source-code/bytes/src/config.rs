use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// bytes.toml project manifest
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BytesProject {
    pub package:      PackageMeta,
    pub run:          Option<RunConfig>,
    pub dependencies: HashMap<String, String>,
    pub python:       Option<PythonConfig>,
    pub jit:          Option<JitConfig>,
    /// Multi-language workspace settings (v0.7)
    pub workspace:    Option<WorkspaceConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PackageMeta {
    pub name:        String,
    pub version:     String,
    pub description: Option<String>,
    pub entry:       Option<String>,  // default: src/main.h#
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
    pub tier:       Option<String>,   // "interpreter" | "bytecode" | "jit"
    pub hot_thresh: Option<u64>,
}

/// v0.7 multi-language workspace
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct WorkspaceConfig {
    /// Member directories
    pub members: Vec<String>,
    /// Language per member: { "app": "h#", "lib": "rust", ... }
    pub languages: HashMap<String, String>,
    /// Build mode: "standard" | "special" (BAZEL-like)
    pub mode: Option<String>,
}

// ── Supported workspace languages ─────────────────────────────────────────────

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

// ── Load / find ───────────────────────────────────────────────────────────────

impl BytesProject {
    pub fn load(path: &str) -> anyhow::Result<Self> {
        let s = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;

        // Try TOML first, then HK format
        if path.ends_with(".toml") || path.ends_with("bytes.toml") {
            toml::from_str(&s).map_err(|e| anyhow::anyhow!("parse bytes.toml: {}", e))
        } else if path.ends_with(".hk") || path.ends_with("bytes.hk") {
            Self::from_hk(&s)
        } else {
            // Auto-detect
            toml::from_str(&s)
            .or_else(|_| Self::from_hk(&s))
            .map_err(|e| anyhow::anyhow!("parse config: {}", e))
        }
    }

    /// Parse bytes.hk using hk-parser 0.3.0
    fn from_hk(content: &str) -> anyhow::Result<Self> {
        use hk_parser::{parse_hk, HkValue};

        let config = parse_hk(content)
        .map_err(|e| anyhow::anyhow!("parse bytes.hk: {:?}", e))?;

        let mut proj = BytesProject::default();

        // [package] section
        if let Some(pkg_section) = config.get("package") {
            if let Ok(map) = pkg_section.as_map() {
                if let Some(v) = map.get("name") {
                    proj.package.name = v.as_string().unwrap_or_default();
                }
                if let Some(v) = map.get("version") {
                    proj.package.version = v.as_string().unwrap_or_default();
                }
                if let Some(v) = map.get("description") {
                    proj.package.description = Some(v.as_string().unwrap_or_default());
                }
                if let Some(v) = map.get("entry") {
                    proj.package.entry = Some(v.as_string().unwrap_or_default());
                }
            }
        }

        // [dependencies]
        if let Some(deps_section) = config.get("dependencies") {
            if let Ok(map) = deps_section.as_map() {
                for (k, v) in map {
                    proj.dependencies.insert(k.clone(), v.as_string().unwrap_or_else(|_| "latest".to_string()));
                }
            }
        }

        // [jit]
        if let Some(jit_section) = config.get("jit") {
            if let Ok(map) = jit_section.as_map() {
                let mut jit = JitConfig::default();
                if let Some(v) = map.get("tier") {
                    jit.tier = Some(v.as_string().unwrap_or_default());
                }
                if let Some(v) = map.get("hot_thresh") {
                    jit.hot_thresh = v.as_number().ok().map(|n| n as u64);
                }
                if let Some(v) = map.get("cache_dir") {
                    jit.cache_dir = Some(v.as_string().unwrap_or_default());
                }
                proj.jit = Some(jit);
            }
        }

        // [python]
        if let Some(py_section) = config.get("python") {
            if let Ok(map) = py_section.as_map() {
                let mut py = PythonConfig::default();
                if let Some(v) = map.get("version") {
                    py.version = v.as_string().unwrap_or_else(|_| "3".to_string());
                }
                if let Some(v) = map.get("packages") {
                    if let Ok(arr) = v.as_array() {
                        py.packages = arr.iter()
                        .filter_map(|i| i.as_string().ok())
                        .collect();
                    }
                }
                proj.python = Some(py);
            }
        }

        // [workspace]
        if let Some(ws_section) = config.get("workspace") {
            if let Ok(map) = ws_section.as_map() {
                let mut ws = WorkspaceConfig::default();
                if let Some(v) = map.get("members") {
                    if let Ok(arr) = v.as_array() {
                        ws.members = arr.iter()
                        .filter_map(|i| i.as_string().ok())
                        .collect();
                    }
                }
                if let Some(lang_map) = map.get("languages") {
                    if let Ok(lm) = lang_map.as_map() {
                        for (k, v) in lm {
                            ws.languages.insert(k.clone(), v.as_string().unwrap_or_default());
                        }
                    }
                }
                if let Some(v) = map.get("mode") {
                    ws.mode = Some(v.as_string().unwrap_or_default());
                }
                proj.workspace = Some(ws);
            }
        }

        Ok(proj)
    }

    /// Find bytes.toml or bytes.hk in current dir
    pub fn find() -> Option<String> {
        for name in &["bytes.toml", "Bytes.toml", "bytes.hk", "Bytes.hk"] {
            if Path::new(name).exists() {
                return Some(name.to_string());
            }
        }
        None
    }

    pub fn entry_file(&self) -> String {
        self.package.entry.clone()
        .unwrap_or_else(|| "src/main.h#".to_string())
    }

    pub fn is_workspace(&self) -> bool {
        self.workspace.as_ref().map(|w| !w.members.is_empty()).unwrap_or(false)
    }
}

// ── RAM cache directory ───────────────────────────────────────────────────────

/// Session-scoped RAM cache: ~/.hackeros/H#/libs/session-{PID}/
/// Stored in tmpfs (RAM) when available — auto-cleaned on reboot.
pub fn ram_cache_dir() -> PathBuf {
    let base = dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(format!(".hackeros/H#/libs/session-{}", std::process::id()));
    std::fs::create_dir_all(&base).ok();
    base
}

/// Persistent cache for `bytes build --release`: {project}/.cache/
pub fn project_cache_dir(project_root: &Path) -> PathBuf {
    let dir = project_root.join(".cache");
    std::fs::create_dir_all(&dir).ok();
    dir
}

// ── Default manifests ─────────────────────────────────────────────────────────

pub fn default_bytes_toml(name: &str) -> String {
    format!(
        r#"[package]
        name        = "{name}"
        version     = "0.1.0"
        description = "H# project"
        entry       = "src/main.h#"

        [jit]
        # RAM cache cleared on reboot (/dev/shm / tmpfs)
        tier       = "jit"      # interpreter | bytecode | jit
        hot_thresh = 100        # JIT-compile after N calls

        [run]
        # args    = ["--verbose"]
        # timeout = 30

        [dependencies]
        # Add H# packages from Bytes-Repository:
        # scanner   = "latest"
        # tui       = "latest"
        # mold      = "latest"

        # [python]
        # version  = "3.13"
        # packages = ["numpy", "requests"]
        "#,
        name = name
    )
}

pub fn default_bytes_hk(name: &str) -> String {
    format!(
        r#"! H# project — bytes.hk
        ! Full docs: https://hackeros-linux-system.github.io/HackerOS-Website/tools-docs/hk.html

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
        ! tui     => latest

        [workspace]
        -> members   => []
        -> mode      => standard
        "#,
        name = name
    )
}

/// Workspace bytes.hk for SPECIAL (BAZEL-like) multi-language workspaces
pub fn workspace_bytes_hk(name: &str, members: &[(&str, &str)]) -> String {
    let member_list: Vec<String> = members.iter().map(|(m, _)| format!("\"{}\"", m)).collect();
    let lang_entries: String = members
    .iter()
    .map(|(m, lang)| format!("--> {} => {}", m, lang))
    .collect::<Vec<_>>()
    .join("\n");

    format!(
        r#"! H# SPECIAL workspace — bytes.hk
        ! Multi-language build workspace (H#, Rust, C, C++, Zig, Go, ...)
        ! Inspired by Bazel but simpler — one config rules them all

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

        [release]
        -> optimize => true
        -> lto      => true
        -> strip    => true
        "#,
        name    = name,
        members = member_list.join(", "),
            langs   = lang_entries,
    )
}

/// Cleanup stale sessions from dead processes
pub fn cleanup_stale_sessions() {
    let libs_base = dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(".hackeros/H#/libs");

    if !libs_base.exists() {
        return;
    }

    if let Ok(entries) = std::fs::read_dir(&libs_base) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_string();
            if let Some(pid_str) = name.strip_prefix("session-") {
                if let Ok(pid) = pid_str.parse::<u32>() {
                    let proc_path = PathBuf::from(format!("/proc/{}", pid));
                    if !proc_path.exists() {
                        let _ = std::fs::remove_dir_all(entry.path());
                    }
                }
            }
        }
    }
}
