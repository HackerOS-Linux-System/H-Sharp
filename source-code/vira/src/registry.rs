use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;

pub const VIRA_INDEX_URL: &str =
    "https://raw.githubusercontent.com/vira-io/repository/main/repo-list.json";
pub const BYTES_INDEX_URL: &str =
    "https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.json";

// ── Real JSON structure from vira-io/repository ──────────────────────────────

#[derive(Debug, Clone, Deserialize)]
pub struct RepoListJson {
    pub libraries: Vec<LibraryEntry>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LibraryEntry {
    pub name:        String,
    pub description: Option<String>,
    /// versions map: "0.1.0" -> "https://github.com/.../lib.a"
    pub versions:    Option<HashMap<String, String>>,
    /// git repo url (for community libraries without prebuilt .a)
    pub git:         Option<String>,
}

impl LibraryEntry {
    /// Latest version string (semver-highest or last in map)
    pub fn latest_version(&self) -> Option<String> {
        let versions = self.versions.as_ref()?;
        if versions.is_empty() { return None; }
        // Parse as semver and pick highest; fall back to last key
        let mut keys: Vec<&String> = versions.keys().collect();
        keys.sort_by(|a, b| semver_cmp(a, b));
        keys.last().map(|s| s.to_string())
    }

    /// Download URL for a specific version, or latest if None
    pub fn url_for(&self, version: Option<&str>) -> Option<String> {
        let versions = self.versions.as_ref()?;
        match version {
            Some(v) => versions.get(v).cloned(),
            None    => {
                let latest = self.latest_version()?;
                versions.get(&latest).cloned()
            }
        }
    }
}

/// Simple semver comparison (handles "0.1.0", "0.2", "0.3.1" etc.)
fn semver_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    let parse = |s: &str| -> Vec<u64> {
        s.split('.').map(|p| p.parse().unwrap_or(0)).collect()
    };
    let av = parse(a);
    let bv = parse(b);
    let len = av.len().max(bv.len());
    for i in 0..len {
        let ai = av.get(i).copied().unwrap_or(0);
        let bi = bv.get(i).copied().unwrap_or(0);
        match ai.cmp(&bi) {
            std::cmp::Ordering::Equal => continue,
            other => return other,
        }
    }
    std::cmp::Ordering::Equal
}

// ── Registry ─────────────────────────────────────────────────────────────────

#[derive(Debug, Default)]
pub struct Registry {
    pub libraries: Vec<LibraryEntry>,
    pub source:    String,
}

impl Registry {
    /// Load from local cache file
    pub fn load_cache(cache_path: &PathBuf) -> Option<Self> {
        let data = std::fs::read_to_string(cache_path).ok()?;
        let parsed: RepoListJson = serde_json::from_str(&data).ok()?;
        Some(Self { libraries: parsed.libraries, source: "cache".into() })
    }

    /// Fetch from remote URL, save to cache
    pub fn fetch_and_cache(url: &str, cache_path: &PathBuf) -> Self {
        match http_get(url) {
            Ok(body) => {
                // Save to cache
                if let Some(parent) = cache_path.parent() {
                    std::fs::create_dir_all(parent).ok();
                }
                std::fs::write(cache_path, &body).ok();
                match serde_json::from_str::<RepoListJson>(&body) {
                    Ok(parsed) => Self { libraries: parsed.libraries, source: "remote".into() },
                    Err(e) => {
                        eprintln!("  warn: failed to parse registry: {}", e);
                        Self::load_cache(cache_path).unwrap_or_default()
                    }
                }
            }
            Err(_) => {
                // Offline — use cache
                Self::load_cache(cache_path).unwrap_or_default()
            }
        }
    }

    /// Fetch vira registry (.cache/vira-registry.json in project dir)
    pub fn fetch_vira() -> Self {
        let cache = PathBuf::from(".cache/vira-registry.json");
        Self::fetch_and_cache(VIRA_INDEX_URL, &cache)
    }

    /// Fetch bytes registry (~/.hackeros/H#/.cache/bytes-registry.json)
    pub fn fetch_bytes() -> Self {
        let cache = dirs::home_dir()
            .unwrap_or_else(|| PathBuf::from("/tmp"))
            .join(".hackeros/H#/.cache/bytes-registry.json");
        Self::fetch_and_cache(BYTES_INDEX_URL, &cache)
    }

    /// Compatibility: default fetch = vira registry
    pub fn fetch() -> Self { Self::fetch_vira() }

    pub fn find(&self, name: &str) -> Option<&LibraryEntry> {
        self.libraries.iter().find(|l| l.name == name)
    }

    pub fn search(&self, query: &str) -> Vec<&LibraryEntry> {
        let q = query.to_lowercase();
        self.libraries.iter().filter(|l| {
            l.name.to_lowercase().contains(&q)
            || l.description.as_deref().unwrap_or("").to_lowercase().contains(&q)
        }).collect()
    }
}

// ── Resolved dependency ───────────────────────────────────────────────────────

#[derive(Debug)]
pub enum ResolvedDep {
    /// Pre-built static archive (.a) from vira registry
    Archive { name: String, version: String, download_url: String },
    /// Git repository (clone + build)
    Git     { url: String, alias: String, version: String },
    /// Python package (handled by bytes)
    Python  { package: String, version: Option<String> },
}

/// Resolve a dependency name+version to a download URL
pub fn resolve_dep(name: &str, version: Option<&str>, registry: &Registry)
    -> anyhow::Result<ResolvedDep>
{
    // GitHub/GitLab direct URL
    if name.starts_with("github.com/") || name.starts_with("gitlab.com/") {
        let alias = name.split('/').last().unwrap_or(name).to_string();
        return Ok(ResolvedDep::Git {
            url:     format!("https://{}", name),
            alias,
            version: version.unwrap_or("latest").to_string(),
        });
    }

    // Registry lookup
    match registry.find(name) {
        None => {
            // Not in registry — try as git
            Ok(ResolvedDep::Git {
                url:     format!("https://github.com/vira-io/{}", name),
                alias:   name.to_string(),
                version: version.unwrap_or("latest").to_string(),
            })
        }
        Some(entry) => {
            // Has git-only (community library)
            if entry.versions.is_none() || entry.versions.as_ref().unwrap().is_empty() {
                if let Some(git) = &entry.git {
                    return Ok(ResolvedDep::Git {
                        url:     git.clone(),
                        alias:   name.to_string(),
                        version: version.unwrap_or("latest").to_string(),
                    });
                }
            }

            // Resolve version
            let ver_str = match version {
                Some(v) => v.to_string(),
                None    => entry.latest_version()
                    .ok_or_else(|| anyhow::anyhow!("no versions available for {}", name))?,
            };

            let url = entry.url_for(Some(&ver_str))
                .or_else(|| entry.url_for(None))
                .ok_or_else(|| anyhow::anyhow!(
                    "version {} not found for {}. Available: {:?}",
                    ver_str, name,
                    entry.versions.as_ref().map(|v| v.keys().collect::<Vec<_>>())
                ))?;

            Ok(ResolvedDep::Archive {
                name:         name.to_string(),
                version:      ver_str,
                download_url: url,
            })
        }
    }
}

/// Print search results
pub fn print_search_results(results: &[&LibraryEntry]) {
    use colored::*;
    if results.is_empty() {
        println!("  {}", "No packages found.".dimmed());
        return;
    }
    println!("  {:<25} {:<10} {}", "PACKAGE".bold(), "LATEST".bold(), "DESCRIPTION".bold());
    println!("  {}", "─".repeat(65).dimmed());
    for l in results {
        let latest = l.latest_version().unwrap_or_else(|| "git".into());
        let desc   = l.description.as_deref().unwrap_or("—");
        let desc   = if desc.len() > 38 { &desc[..38] } else { desc };
        println!("  {:<25} {:<10} {}", l.name.cyan(), latest.green(), desc.dimmed());
    }
}

// ── HTTP helper ───────────────────────────────────────────────────────────────

fn http_get(url: &str) -> anyhow::Result<String> {
    // Try curl first (most reliable)
    let curl = std::process::Command::new("curl")
        .args(["-s", "-L", "--max-time", "10", "--fail", url])
        .output();
    if let Ok(out) = curl {
        if out.status.success() {
            return Ok(String::from_utf8_lossy(&out.stdout).to_string());
        }
    }
    // Fallback: wget
    let wget = std::process::Command::new("wget")
        .args(["-q", "-O", "-", "--timeout=10", url])
        .output();
    if let Ok(out) = wget {
        if out.status.success() {
            return Ok(String::from_utf8_lossy(&out.stdout).to_string());
        }
    }
    anyhow::bail!("failed to fetch {}", url)
}
