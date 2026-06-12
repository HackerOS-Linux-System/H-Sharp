#![allow(dead_code)]
use colored::*;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::config::{BytesProject, JitConfig, ram_cache_dir};

/// Execution tier
#[derive(Debug, Clone, PartialEq)]
pub enum ExecTier {
    Interpreter,
    Bytecode,
    Jit,
}

impl ExecTier {
    pub fn from_str(s: &str) -> Self {
        match s {
            "interpreter" => Self::Interpreter,
            "bytecode"    => Self::Bytecode,
            _             => Self::Jit,
        }
    }
    pub fn name(&self) -> &'static str {
        match self {
            Self::Interpreter => "interpreter",
            Self::Bytecode    => "bytecode",
            Self::Jit         => "jit",
        }
    }
}

/// In-RAM JIT cache for compiled function objects
pub struct JitCache {
    pub cache_dir:   PathBuf,
    pub call_counts: HashMap<String, u64>,
    pub hot_thresh:  u64,
    pub compiled:    HashMap<String, Vec<u8>>,
}

impl JitCache {
    pub fn new(config: &JitConfig) -> Self {
        let cache_dir = config.cache_dir.as_ref()
        .map(PathBuf::from)
        .unwrap_or_else(ram_cache_dir);
        std::fs::create_dir_all(&cache_dir).ok();
        Self {
            cache_dir,
            call_counts: HashMap::new(),
            hot_thresh:  config.hot_thresh.unwrap_or(100),
            compiled:    HashMap::new(),
        }
    }

    pub fn should_jit(&self, fn_name: &str) -> bool {
        self.call_counts.get(fn_name).copied().unwrap_or(0) >= self.hot_thresh
    }

    pub fn record_call(&mut self, fn_name: &str) {
        *self.call_counts.entry(fn_name.to_string()).or_insert(0) += 1;
    }

    pub fn is_compiled(&self, fn_name: &str) -> bool {
        self.compiled.contains_key(fn_name)
    }

    pub fn cache_native(&mut self, fn_name: &str, bytes: Vec<u8>) {
        let path = self.cache_dir.join(format!("{}.jit.o", fn_name));
        std::fs::write(&path, &bytes).ok();
        self.compiled.insert(fn_name.to_string(), bytes);
    }

    pub fn cleanup(&self) {
        if let Ok(entries) = std::fs::read_dir(&self.cache_dir) {
            for entry in entries.flatten() {
                if entry.path().extension().map(|e| e == "o").unwrap_or(false) {
                    std::fs::remove_file(entry.path()).ok();
                }
            }
        }
    }
}

/// Main JIT runner
pub struct BytesRunner {
    pub project: BytesProject,
    pub tier:    ExecTier,
    pub cache:   Option<JitCache>,
    pub verbose: bool,
}

impl BytesRunner {
    pub fn new(project: BytesProject, verbose: bool) -> Self {
        let tier = project.jit.as_ref()
        .and_then(|j| j.tier.as_deref())
        .map(ExecTier::from_str)
        .unwrap_or(ExecTier::Jit);

        let cache = project.jit.as_ref().map(JitCache::new);

        Self { project, tier, cache, verbose }
    }

    pub fn run(&mut self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let t0 = Instant::now();

        if self.verbose {
            let tier_name = match &self.tier {
                ExecTier::Interpreter => "interpreter".yellow(),
                ExecTier::Bytecode    => "bytecode".cyan(),
                ExecTier::Jit         => "JIT".green().bold(),
            };
            eprintln!("  {} {} [{}]", "bytes".cyan().bold(), file.dimmed(), tier_name);
        }

        let exit_code = match &self.tier {
            ExecTier::Interpreter => self.run_interpreter(file, args)?,
            ExecTier::Bytecode    => self.run_bytecode(file, args)?,
            ExecTier::Jit         => self.run_jit(file, args)?,
        };

        if self.verbose {
            eprintln!(
                "  {} {:.2}ms",
                "elapsed:".dimmed(),
                      t0.elapsed().as_secs_f64() * 1000.0
            );
        }

        Ok(exit_code)
    }

    /// Tier 1: pure interpreter via `hsharp preview`
    fn run_interpreter(&self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let hsharp = find_hsharp()?;
        let mut cmd = std::process::Command::new(&hsharp);
        cmd.arg("preview").arg(file).args(args);
        if let Some(run) = &self.project.run {
            for (k, v) in &run.env { cmd.env(k, v); }
        }
        Ok(cmd.status()?.code().unwrap_or(1))
    }

    /// Tier 2: bytecode VM
    fn run_bytecode(&mut self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let bc_path = self.cache.as_ref()
        .map(|c| {
            c.cache_dir.join(format!(
                "{}.h#bc",
                Path::new(file).file_stem().unwrap_or_default().to_string_lossy()
            ))
        })
        .unwrap_or_else(|| PathBuf::from("/tmp/bytes_temp.h#bc"));

        let needs_compile = !bc_path.exists() || {
            let src_mtime = std::fs::metadata(file).ok().and_then(|m| m.modified().ok());
            let bc_mtime  = std::fs::metadata(&bc_path).ok().and_then(|m| m.modified().ok());
            src_mtime.zip(bc_mtime).map(|(s, b)| s > b).unwrap_or(true)
        };

        if needs_compile {
            if self.verbose { eprintln!("  {} bytecode...", "compiling".dimmed()); }
            if let Ok(hsharp) = find_hsharp() {
                let ok = std::process::Command::new(&hsharp)
                .args(["build", file, "-o", &bc_path.display().to_string(), "--cranelift"])
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
                if !ok {
                    return self.run_interpreter(file, args);
                }
            } else {
                return self.run_interpreter(file, args);
            }
        }

        if bc_path.exists() {
            let status = std::process::Command::new(&bc_path).args(args).status()?;
            Ok(status.code().unwrap_or(1))
        } else {
            self.run_interpreter(file, args)
        }
    }

    /// Tier 3: Cranelift JIT — compile to RAM, run from RAM
    fn run_jit(&mut self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let bin_path = self.cache.as_ref()
        .map(|c| {
            c.cache_dir.join(format!(
                "{}.jit",
                Path::new(file).file_stem().unwrap_or_default().to_string_lossy()
            ))
        })
        .unwrap_or_else(|| PathBuf::from("/tmp/bytes_jit_temp"));

        let needs_compile = !bin_path.exists() || {
            let src_mtime = std::fs::metadata(file).ok().and_then(|m| m.modified().ok());
            let bin_mtime = std::fs::metadata(&bin_path).ok().and_then(|m| m.modified().ok());
            src_mtime.zip(bin_mtime).map(|(s, b)| s > b).unwrap_or(true)
        };

        if needs_compile {
            if self.verbose { eprintln!("  {} JIT binary → RAM...", "compiling".dimmed()); }
            let compiled = if let Ok(hsharp) = find_hsharp() {
                std::process::Command::new(&hsharp)
                .args(["build", file, "-o", &bin_path.display().to_string()])
                .status()
                .map(|s| s.success())
                .unwrap_or(false)
            } else {
                false
            };

            if !compiled {
                if self.verbose {
                    eprintln!("  {} JIT compile failed, falling back to interpreter", "warn:".yellow());
                }
                return self.run_interpreter(file, args);
            }

            // Make executable
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&bin_path, std::fs::Permissions::from_mode(0o755)).ok();
            }
        }

        let mut cmd = std::process::Command::new(&bin_path);
        cmd.args(args);
        if let Some(run) = &self.project.run {
            for (k, v) in &run.env { cmd.env(k, v); }
        }
        Ok(cmd.status()?.code().unwrap_or(1))
    }
}

pub fn find_hsharp() -> anyhow::Result<String> {
    // HackerOS standard location
    if let Some(h) = dirs::home_dir() {
        let p = h.join(".hackeros/H#/bins/hsharp");
        if p.exists() { return Ok(p.display().to_string()); }
        let p2 = h.join(".hackeros/H#/bins/h#");
        if p2.exists() { return Ok(p2.display().to_string()); }
    }

    // System locations
    for name in &["/usr/bin/hsharp", "/usr/bin/h#", "/usr/local/bin/hsharp", "/usr/local/bin/h#"] {
        if std::path::Path::new(name).exists() {
            return Ok(name.to_string());
        }
    }

    // PATH lookup
    if let Ok(o) = std::process::Command::new("which").arg("hsharp").output() {
        if o.status.success() {
            let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
            if !s.is_empty() { return Ok(s); }
        }
    }

    Err(anyhow::anyhow!("h# not found. Install from: hacker unpack h#"))
}
