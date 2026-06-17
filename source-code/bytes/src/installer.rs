#![allow(dead_code)]
use colored::*;
use std::path::PathBuf;

use crate::config::BytesProject;
use crate::lockfile::LockFile;
use crate::progress::{BytesBar, BarTheme};
use crate::registry::{download_package, Registry};

pub struct Installer {
    pub project:   BytesProject,
    pub cache_dir: PathBuf,
    pub release:   bool,
    pub verbose:   bool,
}

impl Installer {
    pub fn new(project: BytesProject, cache_dir: PathBuf, release: bool, verbose: bool) -> Self {
        Self { project, cache_dir, release, verbose }
    }

    pub fn install_all(&self) -> anyhow::Result<()> {
        if self.project.dependencies.is_empty() && self.project.python.is_none() {
            return Ok(());
        }
        self.install_hsharp_deps()?;
        self.install_python_deps()?;
        Ok(())
    }

    fn install_hsharp_deps(&self) -> anyhow::Result<()> {
        if self.project.dependencies.is_empty() { return Ok(()); }

        let pkg_cache = self.cache_dir.join("packages");
        std::fs::create_dir_all(&pkg_cache)?;

        let total    = self.project.dependencies.len() as u64;
        let mut bar  = BytesBar::new(total, BarTheme::Default);
        let registry = Registry::fetch();
        let mut lock = LockFile::read();

        for (pkg, ver) in &self.project.dependencies {
            bar.set_status(format!("fetching {}", pkg));

            if let Some(locked) = lock.get(pkg) {
                if locked.version == *ver && pkg_cache.join(pkg).exists() {
                    bar.set_status(format!("{} (cached)", pkg));
                    bar.inc(1);
                    continue;
                }
            }

            if let Some(entry) = registry.find(pkg) {
                let spec = crate::config::DepSpec::parse(ver);
                let mode = self.project.registry.as_ref().map(|r| r.mode.clone()).unwrap_or_else(|| "release".to_string());
                if let Err(e) = download_package(entry, &pkg_cache, &spec, &mode) {
                    eprintln!("  {} {}: {}", "warn:".yellow(), pkg, e);
                } else {
                    lock.lock(pkg, ver, entry.git.clone(), None);
                }
            } else {
                std::fs::write(
                    pkg_cache.join(format!("{}.h#", pkg)),
                               format!(";; bytes stub: {} v{}\n", pkg, ver),
                ).ok();
                lock.lock(pkg, ver, None, None);
            }
            bar.inc(1);
        }
        lock.write();
        bar.finish(&format!("{} H# package(s) ready", self.project.dependencies.len()));
        Ok(())
    }

    fn install_python_deps(&self) -> anyhow::Result<()> {
        if let Some(py) = &self.project.python {
            if py.packages.is_empty() { return Ok(()); }
            let py_cache = self.cache_dir.join("pyenv");
            std::fs::create_dir_all(&py_cache)?;
            crate::python_interop::setup_python_deps(py, &py_cache)?;
        }
        Ok(())
    }
}
