/// Vira registry — vira-io/repository + Bytes-Repository
/// use "vira -> pkgname" from "alias"   → vira registry
/// use "bytes -> pkgname" from "alias"  → bytes repository

use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

const VIRA_INDEX: &str = "https://raw.githubusercontent.com/vira-io/repository/main/repo-list.json";
const BYTES_INDEX: &str = "https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.json";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageEntry {
    pub name:        String,
    pub latest:      String,
    pub versions:    Option<Vec<String>>,
    pub git:         Option<String>,
    pub description: Option<String>,
    pub keywords:    Option<Vec<String>>,
    pub author:      Option<String>,
    pub license:     Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Default)]
pub struct Registry {
    pub packages: Vec<PackageEntry>,
    pub source:   String,
}

impl Registry {
    /// Fetch from Vira registry (default)
    pub fn fetch() -> Self { Self::fetch_vira() }

    pub fn fetch_vira() -> Self {
        let mut r = Self::fetch_url(VIRA_INDEX);
        r.source = "vira".into();
        r
    }

    pub fn fetch_bytes() -> Self {
        let mut r = Self::fetch_url(BYTES_INDEX);
        r.source = "bytes".into();
        r
    }

    fn fetch_url(url: &str) -> Self {
        let result: Option<Self> = (|| {
            let (host, path) = parse_url(url)?;
            let body = http_get(&host, &path).ok()?;
            serde_json::from_str(&body).ok()
        })();
        result.unwrap_or_default()
    }

    pub fn find(&self, name: &str) -> Option<&PackageEntry> {
        self.packages.iter().find(|p| p.name == name)
    }

    pub fn search(&self, query: &str) -> Vec<&PackageEntry> {
        let q = query.to_lowercase();
        self.packages.iter().filter(|p|
            p.name.to_lowercase().contains(&q)
            || p.description.as_deref().unwrap_or("").to_lowercase().contains(&q)
        ).collect()
    }
}

/// Resolve import kind to download URL
pub enum ResolvedDep {
    Registry { name: String, version: String, download_url: String },
    Git      { url: String, alias: String, version: String },
    Python   { package: String, version: Option<String> },
}

/// Resolve a dependency name to download URL
pub fn resolve_dep(name: &str, version: &str, registry: &Registry) -> anyhow::Result<ResolvedDep> {
    // GitHub/GitLab direct
    if name.starts_with("github.com/") || name.starts_with("gitlab.com/") {
        let alias = name.split('/').last().unwrap_or(name).to_string();
        return Ok(ResolvedDep::Git { url: format!("https://{}", name), alias, version: version.to_string() });
    }
    // Vira registry
    let ver = if version == "latest" || version.is_empty() {
        registry.find(name).map(|e| e.latest.clone()).unwrap_or_else(|| "latest".into())
    } else { version.to_string() };
    let url = registry.find(name)
        .and_then(|e| e.git.as_deref())
        .map(|g| g.to_string())
        .unwrap_or_else(|| format!("https://github.com/vira-io/{}", name));
    Ok(ResolvedDep::Registry { name: name.to_string(), version: ver, download_url: url })
}

fn parse_url(url: &str) -> Option<(String, String)> {
    let u = url.trim_start_matches("https://").trim_start_matches("http://");
    let (host, path) = u.split_once('/')?;
    Some((host.to_string(), format!("/{}", path)))
}

fn http_get(host: &str, path: &str) -> anyhow::Result<String> {
    let addr = format!("{}:443", host);
    // Try HTTPS via HTTP/1.0 (simple approach)
    // Fall back to HTTP on port 80
    let addr80 = format!("{}:80", host.replace("raw.githubusercontent.com", "raw.githubusercontent.com"));

    // Use raw.githubusercontent.com via HTTPS would need TLS...
    // For now use HTTP redirect via curl/wget as fallback
    let output = std::process::Command::new("curl")
        .args(["-s", "--max-time", "8", &format!("https://{}{}", host, path)])
        .output();

    if let Ok(out) = output {
        if out.status.success() {
            return Ok(String::from_utf8_lossy(&out.stdout).to_string());
        }
    }

    // Try wget
    let output = std::process::Command::new("wget")
        .args(["-q", "-O", "-", "--timeout=8", &format!("https://{}{}", host, path)])
        .output();

    if let Ok(out) = output {
        if out.status.success() {
            return Ok(String::from_utf8_lossy(&out.stdout).to_string());
        }
    }

    Err(anyhow::anyhow!("cannot fetch {}{}", host, path))
}

pub fn print_results(results: &[&PackageEntry], source: &str) {
    use colored::*;
    if results.is_empty() {
        println!("  {}", "No packages found.".dimmed());
        return;
    }
    println!("  {} {:<25} {:<12} {}", "SRC".bold(), "PACKAGE".bold(), "LATEST".bold(), "DESCRIPTION".bold());
    println!("  {}", "─".repeat(70).dimmed());
    for p in results {
        let desc = p.description.as_deref().unwrap_or("—");
        let desc = if desc.len() > 38 { &desc[..38] } else { desc };
        println!("  {} {:<25} {:<12} {}",
            source.cyan().dimmed(),
            p.name.cyan(),
            p.latest.green(),
            desc.dimmed());
    }
}

pub fn print_search_results(results: &[&PackageEntry]) {
    print_results(results, "vira");
}
