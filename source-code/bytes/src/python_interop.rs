#![allow(dead_code)]
use std::path::{Path, PathBuf};
use crate::config::PythonConfig;

pub struct PythonEnv {
    pub version:  String,
    pub venv_dir: PathBuf,
}

impl PythonEnv {
    pub fn setup(version: &str, cache: &Path) -> anyhow::Result<Self> {
        let venv_dir = cache.join("venv");
        if !venv_dir.exists() {
            let python = find_python(version)?;
            let ok = std::process::Command::new(&python)
            .args(["-m", "venv", &venv_dir.display().to_string()])
            .status().map(|s| s.success()).unwrap_or(false);
            if !ok {
                anyhow::bail!("failed to create venv at {}", venv_dir.display());
            }
        }
        Ok(Self { version: version.to_string(), venv_dir })
    }

    pub fn install_package(&self, pkg: &str, ver: Option<&str>) -> anyhow::Result<()> {
        let pip  = self.venv_dir.join("bin/pip");
        let spec = if let Some(v) = ver {
            if v == "latest" { pkg.to_string() } else { format!("{}=={}", pkg, v) }
        } else { pkg.to_string() };

        let ok = std::process::Command::new(&pip)
        .args(["install", "-q", &spec])
        .status().map(|s| s.success()).unwrap_or(false);

        if !ok {
            let _ = std::process::Command::new("pip3")
            .args(["install", "-q", "--user", &spec])
            .status();
        }
        Ok(())
    }
}

pub fn setup_python_deps(config: &PythonConfig, cache: &Path) -> anyhow::Result<()> {
    if config.packages.is_empty() { return Ok(()); }
    let env = PythonEnv::setup(&config.version, cache)?;
    for pkg in &config.packages { env.install_package(pkg, None)?; }
    Ok(())
}

pub fn resolve_python_import(pkg: &str, venv_dir: &Path) -> Option<PathBuf> {
    let site_packages = venv_dir.join("lib");
    if let Ok(entries) = std::fs::read_dir(&site_packages) {
        for e in entries.flatten() {
            let sp = e.path().join("site-packages").join(pkg);
            if sp.exists() { return Some(sp); }
        }
    }
    None
}

fn find_python(version: &str) -> anyhow::Result<String> {
    let candidates = vec![
        format!("python{}", version),
            format!("python{}", &version[..1]),
                "python3".to_string(),
                "python".to_string(),
    ];
    for py in &candidates {
        if let Ok(o) = std::process::Command::new("which").arg(py).output() {
            if o.status.success() {
                let s = String::from_utf8_lossy(&o.stdout).trim().to_string();
                if !s.is_empty() { return Ok(s); }
            }
        }
    }
    for p in &["/usr/bin/python3", "/usr/local/bin/python3"] {
        if std::path::Path::new(p).exists() { return Ok(p.to_string()); }
    }
    Err(anyhow::anyhow!("Python {} not found", version))
}
