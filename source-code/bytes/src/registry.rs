use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::time::Duration;

/// Raw entry from index.json — each object is { "pkgname": "https://github.com/..." }
type RawIndex = Vec<HashMap<String, String>>;

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Registry {
    pub packages: Vec<PackageEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageEntry {
    pub name:        String,
    pub latest:      String,
    pub git:         Option<String>,
    pub description: Option<String>,
    pub versions:    Vec<String>,
}

impl Registry {
    /// Fetch the Bytes-Repository index from GitHub.
    /// Falls back to an empty registry on network errors.
    pub fn fetch() -> Self {
        // Primary: raw GitHub
        let urls = [
            "https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.json",
            "https://raw.githubusercontent.com/Bytes-Repository/repository/refs/heads/main/index.json",
        ];
        for url in &urls {
            if let Ok(body) = http_get_url(url) {
                if let Ok(raw) = serde_json::from_str::<RawIndex>(&body) {
                    return Self::from_raw(raw);
                }
            }
        }
        Self::default()
    }

    fn from_raw(raw: RawIndex) -> Self {
        let packages = raw
        .into_iter()
        .flat_map(|map| {
            map.into_iter().map(|(name, url)| PackageEntry {
                name:        name.clone(),
                                latest:      "latest".to_string(),
                                git:         Some(url),
                                description: None,
                                versions:    vec!["latest".to_string()],
            })
        })
        .collect();
        Self { packages }
    }

    pub fn find(&self, name: &str) -> Option<&PackageEntry> {
        self.packages.iter().find(|p| p.name == name)
    }
}

/// Minimal raw-TCP HTTP GET (no external deps).
/// For HTTPS urls on hosts that support it via curl fallback.
pub fn http_get_url(url: &str) -> anyhow::Result<String> {
    // Try curl first (available on most HackerOS systems)
    let out = std::process::Command::new("curl")
    .args(["-s", "-L", "--max-time", "10", "-A", "bytes/0.7 H#-PM", url])
    .output();
    if let Ok(o) = out {
        if o.status.success() {
            let body = String::from_utf8_lossy(&o.stdout).to_string();
            if !body.is_empty() {
                return Ok(body);
            }
        }
    }
    // Fallback: raw TCP for http://
    if url.starts_with("http://") {
        let rest = &url[7..];
        let (host, path) = rest.split_once('/').unwrap_or((rest, ""));
        return http_get_tcp(host, &format!("/{}", path));
    }
    anyhow::bail!("cannot fetch {}", url)
}

fn http_get_tcp(host: &str, path: &str) -> anyhow::Result<String> {
    let addr = format!("{}:80", host);
    let mut s = std::net::TcpStream::connect_timeout(
        &addr.parse::<std::net::SocketAddr>()
        .or_else(|_| format!("{}:80", host).parse())?,
                                                     Duration::from_secs(8),
    )?;
    write!(
        s,
        "GET {} HTTP/1.0\r\nHost: {}\r\nUser-Agent: bytes/0.7\r\nConnection: close\r\n\r\n",
        path, host
    )?;
    s.set_read_timeout(Some(Duration::from_secs(10))).ok();
    let mut r = String::new();
    s.read_to_string(&mut r)?;
    Ok(r.split_once("\r\n\r\n").map(|(_, b)| b).unwrap_or(&r).to_string())
}

/// Split "pkg@1.2" or "pkg/1.2" into (name, Some(version))
pub fn split_pkg_version(spec: &str) -> (String, Option<String>) {
    if let Some((n, v)) = spec.split_once('@') {
        return (n.to_string(), Some(v.to_string()));
    }
    if let Some((n, v)) = spec.split_once('/') {
        // Only treat as version if v looks like a semver digit
        if v.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            return (n.to_string(), Some(v.to_string()));
        }
    }
    (spec.to_string(), None)
}

/// Download a package from its git URL into `dest_dir`.
/// Uses `git clone --depth 1` if available, otherwise curl-downloads a tarball.
pub fn download_package(entry: &PackageEntry, dest_dir: &std::path::Path) -> anyhow::Result<()> {
    let url = entry
    .git
    .as_deref()
    .ok_or_else(|| anyhow::anyhow!("no URL for package {}", entry.name))?;

    std::fs::create_dir_all(dest_dir)?;
    let pkg_dir = dest_dir.join(&entry.name);

    if pkg_dir.exists() {
        return Ok(()); // already cached
    }

    // Try git clone --depth 1
    let git_ok = std::process::Command::new("git")
    .args(["clone", "--depth", "1", url, &pkg_dir.display().to_string()])
    .stdout(std::process::Stdio::null())
    .stderr(std::process::Stdio::null())
    .status()
    .map(|s| s.success())
    .unwrap_or(false);

    if git_ok {
        return Ok(());
    }

    // Fallback: download zip archive from GitHub
    let zip_url = format!("{}/archive/refs/heads/main.tar.gz", url.trim_end_matches(".git"));
    let tarball = dest_dir.join(format!("{}.tar.gz", entry.name));
    let dl_ok = std::process::Command::new("curl")
    .args(["-s", "-L", "-o", &tarball.display().to_string(), &zip_url])
    .status()
    .map(|s| s.success())
    .unwrap_or(false);

    if dl_ok && tarball.exists() {
        std::fs::create_dir_all(&pkg_dir)?;
        std::process::Command::new("tar")
        .args(["-xzf", &tarball.display().to_string(), "-C", &pkg_dir.display().to_string(), "--strip-components=1"])
        .status()
        .ok();
        std::fs::remove_file(&tarball).ok();
    } else {
        // Write a stub so the cache isn't empty
        std::fs::create_dir_all(&pkg_dir)?;
        std::fs::write(
            pkg_dir.join(format!("{}.h#", entry.name)),
                       format!(";; bytes pkg stub: {}\n;; source: {}\n", entry.name, url),
        )?;
    }
    Ok(())
}
