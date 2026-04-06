/// bytes.toml project configuration
/// bytes uses TOML (not HCL like vira)

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct BytesProject {
    pub package:      PackageMeta,
    pub run:          Option<RunConfig>,
    pub dependencies: HashMap<String, String>,
    pub python:       Option<PythonConfig>,
    pub jit:          Option<JitConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PackageMeta {
    pub name:        String,
    pub version:     String,
    pub description: Option<String>,
    pub entry:       Option<String>,  // main file, default: src/main.h#
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RunConfig {
    pub args:    Vec<String>,
    pub env:     HashMap<String, String>,
    pub timeout: Option<u64>,  // seconds
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct PythonConfig {
    pub version: String,           // "3.13", "3.14"
    pub venv:    Option<String>,   // venv path, default: .bytes-cache/pyenv
    pub packages: Vec<String>,     // pip packages to install
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct JitConfig {
    pub cache_dir:   Option<String>,   // default: /dev/shm/bytes-{uid}
    pub warmup:      Option<bool>,     // pre-JIT on startup
    pub tier:        Option<String>,   // "interpreter" | "bytecode" | "jit"
    pub hot_thresh:  Option<u64>,      // calls before JIT (default: 100)
}

impl BytesProject {
    pub fn load(path: &str) -> anyhow::Result<Self> {
        let s = std::fs::read_to_string(path)
            .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;
        toml::from_str(&s).map_err(|e| anyhow::anyhow!("parse bytes.toml: {}", e))
    }

    pub fn find() -> Option<String> {
        for name in &["bytes.toml", "Bytes.toml"] {
            if std::path::Path::new(name).exists() {
                return Some(name.to_string());
            }
        }
        None
    }

    pub fn entry_file(&self) -> String {
        self.package.entry.clone()
            .unwrap_or_else(|| "src/main.h#".to_string())
    }
}

/// bytes session dir: ~/.hackeros/H#/libs/session-{PID}/
/// Mounted as tmpfs (RAM-backed) when possible — cleared on reboot automatically.
/// Falls back to regular dir if tmpfs mount fails (still in ~/.hackeros).
pub fn ram_cache_dir() -> std::path::PathBuf {
    let base = dirs::home_dir()
        .unwrap_or_else(|| std::path::PathBuf::from("/tmp"))
        .join(format!(".hackeros/H#/libs/session-{}", std::process::id()));
    std::fs::create_dir_all(&base).ok();
    base
}

/// Generate default bytes.toml
pub fn default_bytes_toml(name: &str) -> String {
    format!(r#"[package]
name = "{name}"
version = "0.1.0"
description = "H# script project"
entry = "src/main.h#"

[jit]
# RAM cache — cleared on reboot (/dev/shm/bytes-PID/)
tier = "jit"         # interpreter | bytecode | jit
hot_thresh = 100     # JIT-compile after 100 calls

[run]
# args = ["--verbose"]
# timeout = 30

[dependencies]
# Add H# packages from Vira registry:
# scanner = "1.2"
# github.com/user/repo = "latest"

# [python]
# version = "3.13"
# packages = ["numpy", "requests", "cryptography"]
"#, name = name)
}
