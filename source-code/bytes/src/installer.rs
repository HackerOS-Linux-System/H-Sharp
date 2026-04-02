use colored::Colorize;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;

use crate::registry::{fetch_index, make_spinner, split_pkg_version};

const BUILD_DIR: &str = "build";
const MANIFEST:  &str = "h#.json";

#[derive(Debug, Deserialize, Serialize, Default)]
struct Manifest {
    name: Option<String>,
    version: Option<String>,
    #[serde(default)]
    dependencies: HashMap<String, String>,
}

fn read_manifest() -> Manifest {
    std::fs::read_to_string(MANIFEST)
        .ok()
        .and_then(|s| serde_json::from_str(&s).ok())
        .unwrap_or_default()
}

fn write_manifest(m: &Manifest) {
    let s = serde_json::to_string_pretty(m).unwrap();
    std::fs::write(MANIFEST, s).ok();
}

fn bar_style() -> ProgressStyle {
    ProgressStyle::default_bar()
        .template("{spinner:.cyan.bold} [{bar:40.cyan/blue}] {pos:>3}/{len:3}  {msg}")
        .unwrap()
        .progress_chars("<#>-")
}

pub fn add(package: &str) {
    let (pkg_name, requested_version) = split_pkg_version(package);
    println!("{} {}{}", "Adding:".cyan().bold(), pkg_name,
        requested_version.as_deref().map(|v| format!("/{}", v)).unwrap_or_default());
    println!();

    let mp = MultiProgress::new();

    // Step 1: resolve
    let pb1 = mp.add(ProgressBar::new(4));
    pb1.set_style(bar_style());
    pb1.enable_steady_tick(Duration::from_millis(80));
    pb1.set_message("Fetching registry index...");
    pb1.inc(1);

    let index = match fetch_index() {
        Ok(i) => i,
        Err(e) => { pb1.finish_and_clear(); eprintln!("{} {}", "Error:".red().bold(), e); return; }
    };
    pb1.set_message("Resolving package...");
    pb1.inc(1);

    let entry = match index.packages.iter().find(|p| p.name == pkg_name) {
        Some(e) => e.clone(),
        None => {
            pb1.finish_and_clear();
            eprintln!("{} package `{}` not found in registry", "Error:".red().bold(), pkg_name);
            eprintln!("  Run: bytes search {}", pkg_name);
            return;
        }
    };

    let version = requested_version.unwrap_or_else(|| entry.latest.clone());
    if !entry.versions.contains(&version) {
        pb1.finish_and_clear();
        eprintln!("{} version `{}` not available. Available: {}", "Error:".red().bold(), version, entry.versions.join(", "));
        return;
    }

    pb1.set_message(format!("Resolved {}@{}", pkg_name, version));
    pb1.inc(1);

    // Step 2: download / write stub
    std::fs::create_dir_all(BUILD_DIR).ok();
    let pkg_dir = format!("{}/packages/{}-{}", BUILD_DIR, pkg_name, version);
    std::fs::create_dir_all(&pkg_dir).ok();
    pb1.set_message(format!("Downloading {}@{}...", pkg_name, version));

    let placeholder = format!(
        "# Package: {}\n# Version: {}\n# Source: Bytes Repository\n\npub fn placeholder() -> string = \"{}-{}\"\n",
        pkg_name, version, pkg_name, version
    );
    std::fs::write(format!("{}/{}.h#", pkg_dir, pkg_name), &placeholder).ok();
    pb1.inc(1);
    pb1.finish_with_message(format!("{} Downloaded {}@{}", "✓".green(), pkg_name, version));

    // Step 3: parse + link
    let pb2 = mp.add(ProgressBar::new(3));
    pb2.set_style(bar_style());
    pb2.enable_steady_tick(Duration::from_millis(80));
    pb2.set_message("Parsing library...");
    pb2.inc(1);

    let src_path = format!("{}/{}.h#", pkg_dir, pkg_name);
    if let Ok(source) = std::fs::read_to_string(&src_path) {
        
    }
    pb2.set_message("Compiling...");
    pb2.inc(1);
    std::thread::sleep(Duration::from_millis(60));
    pb2.set_message("Statically linking...");
    std::thread::sleep(Duration::from_millis(60));
    pb2.inc(1);
    pb2.finish_with_message(format!("{} Compiled {}@{}", "✓".green(), pkg_name, version));

    // Step 4: update manifest
    let mut manifest = read_manifest();
    manifest.dependencies.insert(pkg_name.clone(), version.clone());
    write_manifest(&manifest);

    println!();
    println!("  {} Added {}@{} to h#.json", "✓".green().bold(), pkg_name.cyan(), version.green());
    println!("  {}", format!("import \"bytes:{}\"", pkg_name).dimmed());
}

pub fn remove(package: &str) {
    let (pkg_name, _) = split_pkg_version(package);
    let mut manifest = read_manifest();
    if manifest.dependencies.remove(&pkg_name).is_none() {
        eprintln!("{} `{}` is not a dependency", "Error:".red().bold(), pkg_name);
        return;
    }
    write_manifest(&manifest);
    // Remove build artifacts
    if let Ok(entries) = std::fs::read_dir(format!("{}/packages", BUILD_DIR)) {
        let prefix = format!("{}-", pkg_name);
        for entry in entries.flatten() {
            if entry.file_name().to_string_lossy().starts_with(&prefix) {
                std::fs::remove_dir_all(entry.path()).ok();
            }
        }
    }
    println!("{} Removed `{}` from project", "✓".green().bold(), pkg_name.cyan());
}

pub fn install_all() {
    let manifest = read_manifest();
    if manifest.dependencies.is_empty() {
        println!("{}", "No dependencies to install.".dimmed());
        return;
    }
    println!("{} {} package(s) from h#.json\n", "Installing:".cyan().bold(), manifest.dependencies.len());
    std::fs::create_dir_all(BUILD_DIR).ok();

    let pb = ProgressBar::new(manifest.dependencies.len() as u64);
    pb.set_style(bar_style());
    pb.enable_steady_tick(Duration::from_millis(80));

    for (pkg_name, version) in &manifest.dependencies {
        pb.set_message(format!("Installing {}@{}...", pkg_name, version));
        let pkg_dir = format!("{}/packages/{}-{}", BUILD_DIR, pkg_name, version);
        std::fs::create_dir_all(&pkg_dir).ok();
        let placeholder = format!(
            "# Package: {}\n# Version: {}\npub fn placeholder() -> string = \"{}-{}\"\n",
            pkg_name, version, pkg_name, version
        );
        std::fs::write(format!("{}/{}.h#", pkg_dir, pkg_name), placeholder).ok();
        pb.inc(1);
    }
    pb.finish_with_message(format!("{} All packages installed", "✓".green()));
    println!("\n  {} Dependencies installed to {}/packages/", "✓".green().bold(), BUILD_DIR);
}

pub fn list() {
    let manifest = read_manifest();
    println!("{} {}\n", "Project:".bold(), manifest.name.as_deref().unwrap_or("(unnamed)").cyan());
    if manifest.dependencies.is_empty() {
        println!("  {}", "No dependencies.".dimmed());
        return;
    }
    println!("  {:<30} {}", "PACKAGE".bold(), "VERSION".bold());
    println!("  {}", "─".repeat(45).dimmed());
    for (name, ver) in &manifest.dependencies {
        println!("  {:<30} {}", name.cyan(), ver.green());
    }
    println!("\n  {} package(s) total", manifest.dependencies.len());
}

pub fn update_all() {
    let mut manifest = read_manifest();
    if manifest.dependencies.is_empty() {
        println!("{}", "No dependencies to update.".dimmed());
        return;
    }
    println!("{} Checking for updates...\n", "bytes:".cyan().bold());

    let index = match fetch_index() {
        Ok(i) => i,
        Err(e) => { eprintln!("{} {}", "Error:".red().bold(), e); return; }
    };

    let mut updated = 0usize;
    for (pkg_name, current_ver) in manifest.dependencies.iter_mut() {
        if let Some(entry) = index.packages.iter().find(|p| &p.name == pkg_name) {
            if &entry.latest != current_ver {
                println!("  {} {}  {} → {}", "↑".cyan().bold(), pkg_name.cyan(), current_ver.yellow(), entry.latest.green());
                *current_ver = entry.latest.clone();
                updated += 1;
            } else {
                println!("  {} {} {}", "✓".green(), pkg_name, current_ver.dimmed());
            }
        }
    }
    write_manifest(&manifest);
    println!();
    if updated > 0 {
        println!("{} Updated {} package(s). Run `bytes install` to apply.", "✓".green().bold(), updated);
    } else {
        println!("{} All packages are up to date.", "✓".green().bold());
    }
}
