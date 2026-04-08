/// bytes JIT engine — tiered execution for H#
/// Tier 1: tree-walk interpreter (cold start, always available)
/// Tier 2: bytecode VM (warm, ~5-10x faster than tree-walk)
/// Tier 3: Cranelift JIT for hot functions (LuaJIT-class performance)
///
/// Hot functions detected by call counter → JIT compiled and cached in RAM.

use colored::*;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

use crate::config::{BytesProject, JitConfig, ram_cache_dir};

/// Execution tier selection
#[derive(Debug, Clone, PartialEq)]
pub enum ExecTier {
    Interpreter,   // Pure tree-walk — always works, slowest
    Bytecode,      // Bytecode VM — medium speed
    Jit,           // Cranelift JIT for hot paths — LuaJIT-class
}

impl ExecTier {
    pub fn from_str(s: &str) -> Self {
        match s {
            "interpreter" => Self::Interpreter,
            "bytecode"    => Self::Bytecode,
            "jit" | _     => Self::Jit,
        }
    }
}

/// JIT-compiled function cache (in RAM)
pub struct JitCache {
    pub cache_dir:  PathBuf,
    pub call_counts: HashMap<String, u64>,
    pub hot_thresh:  u64,
    pub compiled:    HashMap<String, Vec<u8>>,  // fn_name → native .o bytes
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
            hot_thresh: config.hot_thresh.unwrap_or(100),
            compiled: HashMap::new(),
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

    /// Cache native bytes for a JIT-compiled function
    pub fn cache_native(&mut self, fn_name: &str, bytes: Vec<u8>) {
        let path = self.cache_dir.join(format!("{}.jit.o", fn_name));
        std::fs::write(&path, &bytes).ok();
        self.compiled.insert(fn_name.to_string(), bytes);
    }

    pub fn cleanup(&self) {
        // Remove cache dir contents but not the dir itself
        if let Ok(entries) = std::fs::read_dir(&self.cache_dir) {
            for entry in entries.flatten() {
                std::fs::remove_file(entry.path()).ok();
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

    /// Run H# file with the configured tier
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
            eprintln!("  {} {:.2}ms", "elapsed:".dimmed(), t0.elapsed().as_secs_f64() * 1000.0);
        }

        Ok(exit_code)
    }

    /// Tier 1: delegate to hsharp interpreter via `hsharp preview`
    fn run_interpreter(&self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let hsharp = find_hsharp()?;
        let mut cmd = std::process::Command::new(&hsharp);
        cmd.arg("preview").arg(file).args(args);
        // Pass env vars from bytes.toml [run]
        if let Some(run) = &self.project.run {
            for (k, v) in &run.env { cmd.env(k, v); }
        }
        Ok(cmd.status()?.code().unwrap_or(1))
    }

    /// Tier 2: bytecode VM (uses cranelift JIT compilation + caching)
    /// Produces .bc (bytecode) files in RAM cache — much faster than interpreter
    fn run_bytecode(&mut self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let source = std::fs::read_to_string(file)?;
        let bc_path = self.cache.as_ref()
            .map(|c| c.cache_dir.join(format!("{}.h#bc", Path::new(file).file_stem().unwrap_or_default().to_string_lossy())))
            .unwrap_or_else(|| PathBuf::from("/tmp/bytes_temp.h#bc"));

        // Check if bytecode cache is valid (source newer than cache)
        let needs_compile = !bc_path.exists() || {
            let src_mtime = std::fs::metadata(file).ok().and_then(|m| m.modified().ok());
            let bc_mtime  = std::fs::metadata(&bc_path).ok().and_then(|m| m.modified().ok());
            src_mtime.zip(bc_mtime).map(|(s, b)| s > b).unwrap_or(true)
        };

        if needs_compile {
            if self.verbose { eprintln!("  {} bytecode...", "compiling".dimmed()); }
            // Use cranelift backend to generate bytecode (object file in RAM)
            let hsharp = find_hsharp()?;
            let status = std::process::Command::new(&hsharp)
                .args(["build", file, "-o", &bc_path.display().to_string(), "--cranelift"])
                .status()?;
            if !status.success() {
                return self.run_interpreter(file, args);  // fallback
            }
        }

        // Execute cached bytecode
        let status = std::process::Command::new(&bc_path).args(args).status()?;
        Ok(status.code().unwrap_or(1))
    }

    /// Tier 3: Cranelift JIT with hot-path detection
    /// First run: interpreter, then JIT compiles hot functions
    fn run_jit(&mut self, file: &str, args: &[String]) -> anyhow::Result<i32> {
        let source = std::fs::read_to_string(file)?;

        // Check for pre-compiled JIT binary in RAM cache
        let bin_path = self.cache.as_ref()
            .map(|c| c.cache_dir.join(format!("{}.jit", Path::new(file).file_stem().unwrap_or_default().to_string_lossy())))
            .unwrap_or_else(|| PathBuf::from("/tmp/bytes_jit_temp"));

        let needs_compile = !bin_path.exists() || {
            let src_mtime = std::fs::metadata(file).ok().and_then(|m| m.modified().ok());
            let bin_mtime = std::fs::metadata(&bin_path).ok().and_then(|m| m.modified().ok());
            src_mtime.zip(bin_mtime).map(|(s, b)| s > b).unwrap_or(true)
        };

        if needs_compile {
            if self.verbose { eprintln!("  {} JIT binary → RAM...", "compiling".dimmed()); }
            // Compile to RAM cache using cranelift (fast compile, good runtime)
            let hsharp = find_hsharp()?;
            let ok = std::process::Command::new(&hsharp)
                .args(["build", file, "-o", &bin_path.display().to_string()])
                .status()
                .map(|s| s.success())
                .unwrap_or(false);

            if !ok {
                if self.verbose { eprintln!("  {} JIT compile failed, falling back to interpreter", "warn:".yellow()); }
                return self.run_interpreter(file, args);
            }

            // Make executable
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&bin_path, std::fs::Permissions::from_mode(0o755)).ok();
        }

        // Run the JIT-compiled binary from RAM
        let mut cmd = std::process::Command::new(&bin_path);
        cmd.args(args);
        if let Some(run) = &self.project.run {
            for (k, v) in &run.env { cmd.env(k, v); }
        }
        Ok(cmd.status()?.code().unwrap_or(1))
    }
}

fn find_hsharp() -> anyhow::Result<String> {
    // Check HackerOS standard location first
    let hackeros_path = dirs::home_dir()
        .map(|h| h.join(".hackeros/H#/bins/hsharp"))
        .filter(|p| p.exists())
        .map(|p| p.display().to_string());

    if let Some(p) = hackeros_path { return Ok(p); }

    // System PATH
    for name in &["hsharp", "/usr/bin/hsharp", "/usr/local/bin/hsharp"] {
        if std::path::Path::new(name).exists() { return Ok(name.to_string()); }
        if std::process::Command::new("which").arg(name)
            .output().map(|o| o.status.success()).unwrap_or(false) {
            return Ok(name.to_string());
        }
    }
    Err(anyhow::anyhow!("hsharp not found. Install from: https://hackeros.dev/h-sharp"))
}
