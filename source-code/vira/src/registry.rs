/// Vira package registry client
/// Fetches from: https://github.com/vira-io/repository/blob/main/repo-list.json
/// Also supports direct git repo URLs: github.com/user/repo

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::TcpStream;
use colored::*;

const REGISTRY_URL: &str = "https://raw.githubusercontent.com/vira-io/repository/main/repo-list.json";
const REGISTRY_HOST: &str = "raw.githubusercontent.com";
const REGISTRY_PATH: &str = "/vira-io/repository/main/repo-list.json";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageEntry {
    pub name:        String,
    pub description: Option<String>,
    pub versions:    Vec<String>,
    pub latest:      String,
    pub url:         Option<String>,
    pub keywords:    Option<Vec<String>>,
    pub author:      Option<String>,
    pub license:     Option<String>,
    pub git:         Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Default)]
pub struct Registry {
    pub packages: Vec<PackageEntry>,
}

impl Registry {
    /// Fetch index from vira-io/repository or cache
    pub fn fetch() -> anyhow::Result<Self> {
        let cache = cache_path();
        match http_get(REGISTRY_HOST, REGISTRY_PATH) {
            Ok(body) => {
                if let Some(p) = &cache {
                    let _ = std::fs::create_dir_all(p.parent().unwrap_or(std::path::Path::new(".")));
                    let _ = std::fs::write(p, &body);
                }
                Ok(serde_json::from_str(&body).unwrap_or_default())
            }
            Err(_) => {
                // Try cache
                if let Some(p) = &cache {
                    if let Ok(s) = std::fs::read_to_string(p) {
                        return Ok(serde_json::from_str(&s).unwrap_or_default());
                    }
                }
                Ok(Registry::default())
            }
        }
    }

    pub fn find(&self, name: &str) -> Option<&PackageEntry> {
        self.packages.iter().find(|p| p.name == name)
    }

    pub fn search(&self, query: &str) -> Vec<&PackageEntry> {
        let q = query.to_lowercase();
        self.packages.iter().filter(|p| {
            p.name.to_lowercase().contains(&q)
            || p.description.as_deref().unwrap_or("").to_lowercase().contains(&q)
            || p.keywords.as_ref().map(|ks| ks.iter().any(|k| k.to_lowercase().contains(&q))).unwrap_or(false)
        }).collect()
    }
}

/// Resolve a dependency string to (name, version, source_url)
pub enum ResolvedDep {
    /// From vira registry
    Registry { name: String, version: String, download_url: String },
    /// Direct git repo
    Git { url: String, alias: String, version: String },
}

pub fn resolve_dep(name: &str, version: &str, registry: &Registry) -> anyhow::Result<ResolvedDep> {
    // GitHub/GitLab style
    if name.starts_with("github.com/") || name.starts_with("gitlab.com/") || name.starts_with("git.sr.ht/") {
        let alias = name.split('/').last().unwrap_or(name).to_string();
        return Ok(ResolvedDep::Git {
            url: format!("https://{}", name),
            alias,
            version: version.to_string(),
        });
    }

    // Vira registry lookup
    if let Some(entry) = registry.find(name) {
        let ver = if version == "latest" || version.is_empty() {
            entry.latest.clone()
        } else {
            version.to_string()
        };
        let url = entry.git.as_deref()
            .map(|g| g.to_string())
            .unwrap_or_else(|| format!("https://github.com/vira-io/{}", name));
        Ok(ResolvedDep::Registry {
            name: name.to_string(),
            version: ver,
            download_url: url,
        })
    } else {
        Err(anyhow::anyhow!("package `{}` not found in registry", name))
    }
}

/// Minimal HTTP GET (plain HTTP to raw.githubusercontent.com port 80)
pub fn http_get(host: &str, path: &str) -> anyhow::Result<String> {
    let addr = format!("{}:80", host).parse::<std::net::SocketAddr>()?;
    let mut stream = TcpStream::connect_timeout(&addr, std::time::Duration::from_secs(8))?;
    write!(stream, "GET {} HTTP/1.0\r\nHost: {}\r\nUser-Agent: vira/0.1\r\nConnection: close\r\n\r\n", path, host)?;
    stream.set_read_timeout(Some(std::time::Duration::from_secs(15)))?;
    let mut resp = String::new();
    stream.read_to_string(&mut resp)?;
    let body = resp.split_once("\r\n\r\n").map(|(_, b)| b).unwrap_or(&resp);
    if body.is_empty() { anyhow::bail!("empty response"); }
    Ok(body.to_string())
}

fn cache_path() -> Option<std::path::PathBuf> {
    dirs::cache_dir().map(|d| d.join("vira").join("registry.json"))
}

pub fn print_search_results(results: &[&PackageEntry]) {
    if results.is_empty() {
        println!("  {}", "No packages found.".dimmed());
        return;
    }
    println!("  {:<25} {:<12} {}", "PACKAGE".bold(), "LATEST".bold(), "DESCRIPTION".bold());
    println!("  {}", "─".repeat(68).dimmed());
    for p in results {
        let desc = p.description.as_deref().unwrap_or("—");
        let desc = if desc.len() > 40 { &desc[..40] } else { desc };
        println!("  {:<25} {:<12} {}",
            p.name.cyan(),
            p.latest.green(),
            desc.dimmed());
    }
}
