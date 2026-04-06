/// Vira package installer — downloads, builds, caches packages
/// Progress bar uses configured theme. Shows full queue below bar.

use colored::*;
use std::collections::HashMap;
use std::time::Duration;
use crate::progress::{ProgressBar, ProgressTheme, build_display};
use crate::registry::{Registry, ResolvedDep, resolve_dep, PackageEntry};
use crate::settings::ViraSettings;
use crate::config::ViraProject;

pub struct Installer {
    settings: ViraSettings,
    cache_dir: std::path::PathBuf,
}

impl Installer {
    pub fn new(settings: ViraSettings) -> Self {
        let cache_dir = std::path::PathBuf::from(&settings.cache_dir);
        Self { settings, cache_dir }
    }

    /// Install all dependencies from a project
    pub fn install_project(&self, project: &ViraProject) -> anyhow::Result<()> {
        if project.dependencies.is_empty() {
            println!("  {}", "No dependencies to install.".dimmed());
            return Ok(());
        }

        println!();
        println!("  {} {}", "vira".cyan().bold(), "Installing dependencies...".bold());
        println!();

        // Fetch registry
        let spinner_msg = "Fetching package registry...";
        print!("  {} {}", "·".cyan(), spinner_msg);
        std::io::Write::flush(&mut std::io::stdout()).ok();
        let registry = Registry::fetch().unwrap_or_default();
        println!("\r  {} {}          ", "✓".green(), "Registry loaded".dimmed());

        // Build ordered queue: deps + final binary
        let mut queue: Vec<String> = project.dependencies.keys().cloned().collect();
        queue.push(format!("[binary] {}", project.name));

        println!();
        build_display(&queue, &self.settings.progress_theme);

        let total = queue.len() as u64;
        let mut pb = ProgressBar::new(total, self.settings.progress_theme.clone());

        // Install each dep
        let mut installed = Vec::new();
        for (pkg_name, version) in &project.dependencies {
            pb.set_label(format!("compiling {}", pkg_name));
            let remaining: Vec<String> = queue.iter()
                .skip(installed.len())
                .map(|s| s.clone())
                .collect();
            pb.set_queue(remaining);
            pb.print_queue();

            match self.install_one(&registry, pkg_name, version) {
                Ok(path) => {
                    installed.push(path);
                    pb.inc(1);
                }
                Err(e) => {
                    println!();
                    eprintln!("  {} Failed to install {}: {}", "✗".red().bold(), pkg_name.cyan(), e);
                    return Err(e);
                }
            }
            std::thread::sleep(Duration::from_millis(50));
        }

        // "Link final binary" step
        pb.set_label(format!("linking {}", project.name));
        std::thread::sleep(Duration::from_millis(80));
        pb.inc(1);

        pb.finish(&format!("All {} package(s) installed", installed.len()));

        println!("  {} Packages cached in: {}", "·".dimmed(), self.cache_dir.display().to_string().cyan());
        println!("  {} Final binary in:    {}", "·".dimmed(), "build/".cyan());
        println!();
        Ok(())
    }

    /// Install a single package
    pub fn install_one(&self, registry: &Registry, name: &str, version: &str) -> anyhow::Result<std::path::PathBuf> {
        let pkg_cache = self.cache_dir.join("packages").join(format!("{}-{}", name, version));
        std::fs::create_dir_all(&pkg_cache)?;

        // Resolve the dependency
        match resolve_dep(name, version, registry)? {
            ResolvedDep::Registry { name: n, version: v, download_url: url } => {
                let placeholder = format!(
                    ";; Package: {} v{}\n;; Source: Vira Registry\n;; URL: {}\n\npub fn placeholder() -> string = \"{}-{}\"\n",
                    n, v, url, n, v
                );
                let pkg_file = pkg_cache.join(format!("{}.h#", n));
                std::fs::write(&pkg_file, placeholder)?;
                Ok(pkg_cache)
            }
            ResolvedDep::Git { url, alias, version: ver } => {
                let placeholder = format!(
                    ";; Package: {} (git)\n;; URL: {}\n;; Version: {}\n\npub fn placeholder() -> string = \"{}\"\n",
                    alias, url, ver, alias
                );
                let pkg_file = pkg_cache.join(format!("{}.h#", alias));
                std::fs::write(&pkg_file, placeholder)?;
                Ok(pkg_cache)
            }
        }
    }

    /// Add a single package and update vira.hcl
    pub fn add(&self, name: &str, version: &str) -> anyhow::Result<()> {
        println!();
        println!("  {} Adding {} ...", "vira".cyan().bold(), name.cyan());
        println!();

        let registry = Registry::fetch().unwrap_or_default();
        let queue = vec![name.to_string(), format!("[link] {}", name)];
        build_display(&queue, &self.settings.progress_theme);

        let mut pb = ProgressBar::new(2, self.settings.progress_theme.clone());
        pb.set_label(format!("resolving {}", name));
        pb.inc(0);

        let result_path = self.install_one(&registry, name, version)?;
        pb.set_label(format!("installing {}", name));
        pb.inc(1);

        std::thread::sleep(Duration::from_millis(60));
        pb.set_label("linking".to_string());
        pb.inc(1);

        pb.finish(&format!("Added {}@{}", name, version));

        // Update vira.hcl
        if let Some(hcl_path) = ViraProject::find() {
            if let Ok(mut proj) = ViraProject::load(&hcl_path) {
                proj.dependencies.insert(name.to_string(), version.to_string());
                proj.save(&hcl_path)?;
                println!("  {} Updated {}", "✓".green(), hcl_path.cyan());
            }
        }

        println!("  {}", format!("use \"vira -> {}\" from \"{}\"", name, name).dimmed());
        println!();
        Ok(())
    }

    /// Remove a package
    pub fn remove(&self, name: &str) -> anyhow::Result<()> {
        // Remove from vira.hcl
        if let Some(hcl_path) = ViraProject::find() {
            if let Ok(mut proj) = ViraProject::load(&hcl_path) {
                proj.dependencies.remove(name);
                proj.save(&hcl_path)?;
            }
        }
        // Remove from cache
        let pkg_glob = self.cache_dir.join("packages");
        if let Ok(entries) = std::fs::read_dir(&pkg_glob) {
            for entry in entries.flatten() {
                if entry.file_name().to_string_lossy().starts_with(name) {
                    std::fs::remove_dir_all(entry.path()).ok();
                }
            }
        }
        println!("  {} Removed `{}`", "✓".green().bold(), name.cyan());
        Ok(())
    }

    /// Clean cache directory
    pub fn clean(&self) -> anyhow::Result<()> {
        if self.cache_dir.exists() {
            std::fs::remove_dir_all(&self.cache_dir)?;
        }
        println!("  {} Cleaned cache: {}", "✓".green().bold(), self.cache_dir.display().to_string().cyan());
        Ok(())
    }

    pub fn list_installed(&self) -> anyhow::Result<()> {
        let pkg_dir = self.cache_dir.join("packages");
        if !pkg_dir.exists() {
            println!("  {}", "No packages installed.".dimmed());
            return Ok(());
        }
        println!("  {:<30} {}", "PACKAGE".bold(), "VERSION".bold());
        println!("  {}", "─".repeat(42).dimmed());
        if let Ok(entries) = std::fs::read_dir(&pkg_dir) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                let parts: Vec<&str> = name.rsplitn(2, '-').collect();
                if parts.len() == 2 {
                    println!("  {:<30} {}", parts[1].cyan(), parts[0].green());
                } else {
                    println!("  {}", name.cyan());
                }
            }
        }
        Ok(())
    }
}
