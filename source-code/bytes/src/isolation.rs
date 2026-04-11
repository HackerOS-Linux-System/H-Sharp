use std::path::{Path, PathBuf};
use colored::*;

/// Returns the base libs directory: ~/.hackeros/H#/libs/
pub fn hackeros_libs_base() -> PathBuf {
    dirs::home_dir()
        .unwrap_or_else(|| PathBuf::from("/tmp"))
        .join(".hackeros/H#/libs")
}

/// Returns the vira cache base: ~/.hackeros/H#/.cache/
pub fn hackeros_cache_base() -> PathBuf {
    dirs::home_dir()
        .unwrap_or_else(|| PathBuf::from("/tmp"))
        .join(".hackeros/H#/.cache")
}

/// Create an isolated session directory for bytes
/// Returns the path to the session directory
pub fn create_session_dir() -> anyhow::Result<PathBuf> {
    let base = hackeros_libs_base();
    let session_id = format!("session-{}", std::process::id());
    let session_dir = base.join(&session_id);

    std::fs::create_dir_all(&session_dir)?;

    // Try to mount as tmpfs for RAM-backed storage (requires root or user namespaces)
    // If mounting fails, we fall back to regular directory (still in ~/.hackeros/H#/libs/)
    let mounted = try_mount_tmpfs(&session_dir);
    if !mounted {
        // Register for cleanup on exit via a marker file
        let marker = session_dir.join(".bytes-session");
        std::fs::write(&marker, format!("{}", std::process::id()))?;
    }

    Ok(session_dir)
}

/// Attempt to mount tmpfs at path (works on Linux with user namespaces or as root)
fn try_mount_tmpfs(path: &Path) -> bool {
    // Try mount(2) via nix
    #[cfg(target_os = "linux")]
    {
        use nix::mount::{mount, MsFlags};
        let result = mount(
            Some("tmpfs"),
            path,
            Some("tmpfs"),
            MsFlags::empty(),
            Some("size=512m,mode=0700"),
        );
        if result.is_ok() { return true; }

        // Try unshare+mount via subprocess (user namespace)
        let ok = std::process::Command::new("unshare")
            .args(["--user", "--mount", "mount", "-t", "tmpfs",
                   "-o", "size=512m", "tmpfs", &path.display().to_string()])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        if ok { return true; }
    }
    false
}

/// Register cleanup of session dir on process exit
pub fn register_cleanup(session_dir: PathBuf) {
    // Use tempfile drop semantics via a background thread that waits on parent exit
    std::thread::spawn(move || {
        // Wait for parent process to finish (check via /proc/PID)
        let pid = std::process::id();
        loop {
            std::thread::sleep(std::time::Duration::from_secs(2));
            if !Path::new(&format!("/proc/{}", pid)).exists() {
                cleanup_session(&session_dir);
                break;
            }
        }
    });
}

fn cleanup_session(dir: &Path) {
    // Unmount if mounted
    #[cfg(target_os = "linux")]
    {
        let _ = nix::mount::umount(dir);
    }
    let _ = std::fs::remove_dir_all(dir);
}

/// Install a package into the isolated environment
/// Handles system deps via dpkg-deb extraction
pub struct IsolatedEnv {
    pub session_dir: PathBuf,
    pub pkg_dir:     PathBuf,
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

    /// Install H# package into isolated env
    pub fn install_hsharp_pkg(&self, name: &str, version: &str, source_url: &str) -> anyhow::Result<PathBuf> {
        let pkg_path = self.pkg_dir.join(format!("{}-{}", name, version));
        std::fs::create_dir_all(&pkg_path)?;
        // Write package stub (real impl would download + extract)
        std::fs::write(pkg_path.join(format!("{}.h#", name)),
            format!(";; pkg: {} v{}\n;; source: {}\n", name, version, source_url)
        )?;
        Ok(pkg_path)
    }

    /// Install a Debian system dependency into isolated env (no system pollution)
    /// Uses dpkg-deb to extract .deb into sys_deps_dir WITHOUT installing system-wide
    pub fn install_sys_dep(&self, deb_name: &str) -> anyhow::Result<()> {
        let extract_dir = self.sys_deps_dir.join(deb_name);
        std::fs::create_dir_all(&extract_dir)?;

        eprintln!("  {} system dep {} → isolated env", "fetching".cyan(), deb_name.yellow());

        // Download .deb to temp location
        let deb_tmp = tempfile::NamedTempFile::new()?;
        let downloaded = std::process::Command::new("apt-get")
            .args(["download", deb_name])
            .current_dir(deb_tmp.path().parent().unwrap_or(Path::new("/tmp")))
            .status()
            .map(|s| s.success())
            .unwrap_or(false);

        if !downloaded {
            eprintln!("  {} could not download {}, skipping", "warn:".yellow(), deb_name);
            return Ok(());
        }

        // Extract .deb into isolated dir (dpkg-deb --extract)
        let deb_files: Vec<_> = std::fs::read_dir(deb_tmp.path().parent().unwrap_or(Path::new("/tmp")))
            .into_iter().flatten().flatten()
            .filter(|e| e.file_name().to_string_lossy().starts_with(deb_name) && e.file_name().to_string_lossy().ends_with(".deb"))
            .collect();

        for deb in &deb_files {
            let ok = std::process::Command::new("dpkg-deb")
                .args(["--extract", &deb.path().display().to_string(), &extract_dir.display().to_string()])
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
            if ok {
                eprintln!("  {} {} extracted to isolated env", "✓".green(), deb_name.cyan());
            }
        }

        Ok(())
    }

    /// Get LD_LIBRARY_PATH for running binaries with isolated system deps
    pub fn ld_library_path(&self) -> String {
        let mut paths = Vec::new();
        // Walk sys_deps_dir for lib directories
        if let Ok(entries) = std::fs::read_dir(&self.sys_deps_dir) {
            for pkg in entries.flatten() {
                for lib_dir in &["usr/lib", "usr/lib/x86_64-linux-gnu", "lib", "lib/x86_64-linux-gnu"] {
                    let p = pkg.path().join(lib_dir);
                    if p.exists() { paths.push(p.display().to_string()); }
                }
            }
        }
        paths.join(":")
    }

    /// Total session size in bytes
    pub fn size(&self) -> u64 {
        dir_size(&self.session_dir)
    }

    pub fn cleanup(&self) {
        cleanup_session(&self.session_dir);
    }
}

impl Drop for IsolatedEnv {
    fn drop(&mut self) {
        // Session cleanup is deferred — only clean up on process exit
        // because multiple parts of the process may use the same env
    }
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

/// Vira persistent cache: ~/.hackeros/H#/.cache/
/// NOT cleaned on reboot — persists between sessions
/// Isolated: each package gets its own extracted tree
pub struct ViraCache {
    pub base: PathBuf,
}

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
                let name = e.file_name().to_string_lossy().to_string();
                let parts: Vec<&str> = name.rsplitn(2, '-').collect();
                if parts.len() == 2 { Some((parts[1].to_string(), parts[0].to_string())) }
                else { Some((name, "?".into())) }
            })
            .collect()
    }
}
