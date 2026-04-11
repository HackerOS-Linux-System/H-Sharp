use std::path::{Path, PathBuf};
use colored::*;
use crate::config::ViraProject;
use crate::registry::{Registry, ResolvedDep, resolve_dep};

pub struct Installer {
    cache_dir: PathBuf,
}

impl Installer {
    pub fn new() -> Self {
        let cache_dir = ViraProject::cache_dir();
        std::fs::create_dir_all(&cache_dir).ok();
        Self { cache_dir }
    }

    /// Install all dependencies from vira.hcl
    pub fn install_all(&self, project: &ViraProject, registry: &Registry) -> anyhow::Result<()> {
        if project.dependencies.is_empty() {
            println!("  {}", "Nothing to install.".dimmed());
            return Ok(());
        }

        println!("  {} {} package(s)...", "Installing".cyan().bold(), project.dependencies.len());
        println!("  {} {}", "Cache:".dimmed(), self.cache_dir.display().to_string().cyan());
        println!();

        let mut errors = 0;
        for (name, version_spec) in &project.dependencies {
            // Parse "name/version" or "name" = "version"
            let (pkg_name, pkg_ver) = if version_spec == "latest" || version_spec.is_empty() {
                (name.as_str(), None)
            } else {
                (name.as_str(), Some(version_spec.as_str()))
            };

            match self.install_package(pkg_name, pkg_ver, registry) {
                Ok(path) => println!("  {} {} → {}", "✓".green(), name.cyan(), path.display().to_string().dimmed()),
                Err(e)   => {
                    eprintln!("  {} {}: {}", "✗".red(), name.red(), e);
                    errors += 1;
                }
            }
        }

        if errors > 0 {
            anyhow::bail!("{} package(s) failed to install", errors);
        }
        Ok(())
    }

    /// Install a single package, returns path to cached artifact
    pub fn install_package(&self, name: &str, version: Option<&str>, registry: &Registry)
        -> anyhow::Result<PathBuf>
    {
        let resolved = resolve_dep(name, version, registry)?;

        match resolved {
            ResolvedDep::Archive { name, version, download_url } => {
                self.download_archive(&name, &version, &download_url)
            }
            ResolvedDep::Git { url, alias, version } => {
                self.clone_git(&alias, &url, &version)
            }
            ResolvedDep::Python { package, .. } => {
                println!("  {} Python package {} — use `bytes python {}`",
                    "info:".cyan(), package.yellow(), package);
                Ok(self.cache_dir.join(format!("py_{}.placeholder", package)))
            }
        }
    }

    /// Download a pre-built .a archive
    fn download_archive(&self, name: &str, version: &str, url: &str)
        -> anyhow::Result<PathBuf>
    {
        let pkg_dir = self.cache_dir.join(format!("{}-{}", name, version));
        let archive = pkg_dir.join(format!("{}.a", name));

        if archive.exists() {
            return Ok(archive); // already cached
        }
        std::fs::create_dir_all(&pkg_dir)?;

        // Download .a with progress
        print!("  {} {} v{}...", "Downloading".cyan(), name, version);
        let ok = std::process::Command::new("curl")
            .args(["-s", "-L", "--max-time", "60", "--fail", url,
                   "-o", &archive.display().to_string()])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);

        if !ok {
            // Try wget fallback
            let ok2 = std::process::Command::new("wget")
                .args(["-q", "--timeout=60", "-O", &archive.display().to_string(), url])
                .status()
                .map(|s| s.success())
                .unwrap_or(false);
            if !ok2 {
                std::fs::remove_dir_all(&pkg_dir).ok();
                anyhow::bail!("download failed from {}", url);
            }
        }

        // Write metadata
        let meta = serde_json::json!({ "name": name, "version": version, "url": url });
        std::fs::write(pkg_dir.join("meta.json"), meta.to_string())?;

        println!(" {}", "done".green());
        Ok(archive)
    }

    /// Clone a git repository into cache
    fn clone_git(&self, name: &str, url: &str, version: &str)
        -> anyhow::Result<PathBuf>
    {
        let pkg_dir = self.cache_dir.join(format!("{}-git", name));

        if pkg_dir.exists() {
            // Already cloned — pull
            print!("  {} {} (git)...", "Updating".cyan(), name);
            std::process::Command::new("git")
                .args(["-C", &pkg_dir.display().to_string(), "pull", "--ff-only"])
                .output().ok();
            println!(" {}", "done".green());
            return Ok(pkg_dir);
        }

        print!("  {} {} from {}...", "Cloning".cyan(), name, url);
        let ok = std::process::Command::new("git")
            .args(["clone", "--depth=1", url, &pkg_dir.display().to_string()])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);

        if !ok {
            anyhow::bail!("git clone failed: {}", url);
        }
        println!(" {}", "done".green());
        Ok(pkg_dir)
    }

    /// Clean the cache directory
    pub fn clean(&self) -> anyhow::Result<()> {
        if self.cache_dir.exists() {
            std::fs::remove_dir_all(&self.cache_dir)?;
            println!("  {} cleaned {}", "✓".green().bold(), self.cache_dir.display().to_string().cyan());
        } else {
            println!("  {}", "Cache already empty.".dimmed());
        }
        Ok(())
    }

    /// List all cached packages
    pub fn list(&self) -> Vec<(String, String)> {
        if !self.cache_dir.exists() { return vec![]; }
        std::fs::read_dir(&self.cache_dir)
            .into_iter().flatten().flatten()
            .filter_map(|e| {
                let name = e.file_name().to_string_lossy().to_string();
                // name-version format
                let parts: Vec<&str> = name.rsplitn(2, '-').collect();
                if parts.len() == 2 {
                    Some((parts[1].to_string(), parts[0].to_string()))
                } else {
                    None
                }
            })
            .collect()
    }
}
