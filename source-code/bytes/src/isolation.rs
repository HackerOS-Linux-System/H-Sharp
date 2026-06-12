#![allow(dead_code)]
use colored::*;
use std::path::{Path, PathBuf};

pub fn hackeros_libs_base() -> PathBuf {
    dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(".hackeros/H#/libs")
}

pub fn hackeros_cache_base() -> PathBuf {
    dirs::home_dir()
    .unwrap_or_else(|| PathBuf::from("/tmp"))
    .join(".hackeros/H#/.cache")
}

pub fn create_session_dir() -> anyhow::Result<PathBuf> {
    let base        = hackeros_libs_base();
    let session_id  = format!("session-{}", std::process::id());
    let session_dir = base.join(&session_id);
    std::fs::create_dir_all(&session_dir)?;
    // Try tmpfs mount; fall back silently
    let mounted = try_mount_tmpfs(&session_dir);
    if !mounted {
        let marker = session_dir.join(".bytes-session");
        std::fs::write(&marker, format!("{}", std::process::id()))?;
    }
    Ok(session_dir)
}

/// Mount tmpfs using CLI tools only — no `nix` crate needed.
fn try_mount_tmpfs(path: &Path) -> bool {
    #[cfg(target_os = "linux")]
    {
        // Direct mount (needs root)
        if std::process::Command::new("mount")
            .args(["-t", "tmpfs", "-o", "size=512m,mode=0700",
                  "tmpfs", &path.display().to_string()])
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status().map(|s| s.success()).unwrap_or(false)
            { return true; }

            // Unprivileged via unshare
            if std::process::Command::new("unshare")
                .args(["--user", "--mount", "mount", "-t", "tmpfs",
                      "-o", "size=512m", "tmpfs", &path.display().to_string()])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status().map(|s| s.success()).unwrap_or(false)
                { return true; }
    }
    false
}

fn cleanup_session(dir: &Path) {
    #[cfg(target_os = "linux")]
    {
        let _ = std::process::Command::new("umount")
        .arg(&dir.display().to_string())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();
    }
    let _ = std::fs::remove_dir_all(dir);
}

// ── IsolatedEnv ───────────────────────────────────────────────────────────────

pub struct IsolatedEnv {
    pub session_dir:  PathBuf,
    pub pkg_dir:      PathBuf,
    pub sys_deps_dir: PathBuf,
}

impl IsolatedEnv {
    pub fn new() -> anyhow::Result<Self> {
        let session_dir  = create_session_dir()?;
        let pkg_dir      = session_dir.join("packages");
        let sys_deps_dir = session_dir.join("sys-deps");
        std::fs::create_dir_all(&pkg_dir)?;
        std::fs::create_dir_all(&sys_deps_dir)?;
        Ok(Self { session_dir, pkg_dir, sys_deps_dir })
    }

    pub fn install_hsharp_pkg(&self, name: &str, version: &str, source_url: &str) -> anyhow::Result<PathBuf> {
        let pkg_path = self.pkg_dir.join(format!("{}-{}", name, version));
        std::fs::create_dir_all(&pkg_path)?;
        std::fs::write(
            pkg_path.join(format!("{}.h#", name)),
                       format!(";; pkg: {} v{}\n;; source: {}\n", name, version, source_url),
        )?;
        Ok(pkg_path)
    }

    pub fn install_sys_dep(&self, deb_name: &str) -> anyhow::Result<()> {
        let extract_dir = self.sys_deps_dir.join(deb_name);
        std::fs::create_dir_all(&extract_dir)?;
        eprintln!("  {} system dep {} -> isolated env", "fetching".cyan(), deb_name.yellow());

        let deb_tmp    = tempfile::NamedTempFile::new()?;
        let downloaded = std::process::Command::new("apt-get")
        .args(["download", deb_name])
        .current_dir(deb_tmp.path().parent().unwrap_or(Path::new("/tmp")))
        .status().map(|s| s.success()).unwrap_or(false);

        if !downloaded {
            eprintln!("  {} could not download {}, skipping", "warn:".yellow(), deb_name);
            return Ok(());
        }

        let deb_parent = deb_tmp.path().parent().unwrap_or(Path::new("/tmp"));
        let deb_files: Vec<_> = std::fs::read_dir(deb_parent)
        .into_iter().flatten().flatten()
        .filter(|e| {
            let n = e.file_name().to_string_lossy().to_string();
            n.starts_with(deb_name) && n.ends_with(".deb")
        })
        .collect();

        for deb in &deb_files {
            let ok = std::process::Command::new("dpkg-deb")
            .args(["--extract", &deb.path().display().to_string(),
                  &extract_dir.display().to_string()])
            .status().map(|s| s.success()).unwrap_or(false);
            if ok {
                eprintln!("  {} {} extracted", "checkmark".green(), deb_name.cyan());
            }
        }
        Ok(())
    }

    pub fn ld_library_path(&self) -> String {
        let mut paths = Vec::new();
        if let Ok(entries) = std::fs::read_dir(&self.sys_deps_dir) {
            for pkg in entries.flatten() {
                for lib_dir in &[
                    "usr/lib", "usr/lib/x86_64-linux-gnu",
                    "lib",     "lib/x86_64-linux-gnu",
                ] {
                    let p = pkg.path().join(lib_dir);
                    if p.exists() { paths.push(p.display().to_string()); }
                }
            }
        }
        paths.join(":")
    }

    pub fn size(&self)    -> u64 { dir_size(&self.session_dir) }
    pub fn cleanup(&self)        { cleanup_session(&self.session_dir); }
}

fn dir_size(path: &Path) -> u64 {
    let mut total = 0u64;
    if let Ok(entries) = std::fs::read_dir(path) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() { total += dir_size(&p); }
            else if let Ok(m) = p.metadata() { total += m.len(); }
        }
    }
    total
}

// ── ViraCache ─────────────────────────────────────────────────────────────────

pub struct ViraCache { pub base: PathBuf }

impl ViraCache {
    pub fn open() -> Self {
        let base = hackeros_cache_base();
        std::fs::create_dir_all(&base).ok();
        Self { base }
    }

    pub fn pkg_path(&self, name: &str, version: &str) -> PathBuf {
        self.base.join("packages").join(format!("{}-{}", name, version))
    }

    pub fn is_cached(&self, name: &str, version: &str) -> bool {
        self.pkg_path(name, version).exists()
    }

    pub fn cache_pkg(&self, name: &str, version: &str, content: &str) -> anyhow::Result<PathBuf> {
        let path = self.pkg_path(name, version);
        std::fs::create_dir_all(&path)?;
        std::fs::write(path.join(format!("{}.h#", name)), content)?;
        Ok(path)
    }

    pub fn total_size_mb(&self) -> f64 {
        dir_size(&self.base) as f64 / (1024.0 * 1024.0)
    }

    pub fn list(&self) -> Vec<(String, String)> {
        let pkg_dir = self.base.join("packages");
        if !pkg_dir.exists() { return vec![]; }
        std::fs::read_dir(&pkg_dir).into_iter().flatten().flatten()
        .filter_map(|e| {
            let name  = e.file_name().to_string_lossy().to_string();
            let parts: Vec<&str> = name.rsplitn(2, '-').collect();
            if parts.len() == 2 {
                Some((parts[1].to_string(), parts[0].to_string()))
            } else {
                Some((name, "?".into()))
            }
        })
        .collect()
    }
}
