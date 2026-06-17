#![allow(dead_code)]
use colored::*;
use serde::Deserialize;
use std::path::{Path, PathBuf};

/// One entry in the Bytes-Repository index.
///
/// Real format (as published at
/// https://github.com/Bytes-Repository/repository/blob/main/index.json):
///
/// ```json
/// [
///   { "mold": "https://github.com/Bytes-Repository/mold" },
///   { "obsidian": "https://github.com/Bytes-Repository/obsidian" }
/// ]
/// ```
///
/// Each element is a single-key object: package name -> git repository URL.
/// There is no version/description metadata in the index itself — version
/// resolution happens via git tags (cargo-style) at install time.
#[derive(Debug, Clone)]
pub struct RegistryEntry {
    pub name:        String,
    /// "latest" unless a specific tag was resolved
    pub latest:      String,
    pub description: Option<String>,
    pub git:         Option<String>,
}

/// Raw index.json shape: array of single-key maps.
type RawIndex = Vec<std::collections::HashMap<String, String>>;

pub struct Registry {
    pub packages: Vec<RegistryEntry>,
}

const INDEX_URL: &str =
"https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.json";

    impl Registry {
        /// Fetch and parse the registry index. On any network/parse failure,
        /// returns an empty registry (callers fall back to stub packages).
        pub fn fetch() -> Self {
            match Self::try_fetch() {
                Ok(reg) => reg,
                Err(e) => {
                    eprintln!("  {} could not fetch package registry: {}", "warn:".yellow(), e);
                    Self { packages: Vec::new() }
                }
            }
        }

        fn try_fetch() -> anyhow::Result<Self> {
            // Use curl (always available on HackerOS) instead of pulling in a
            // full HTTP client crate just for one JSON file.
            let output = std::process::Command::new("curl")
            .args(["-fsSL", "--max-time", "10", INDEX_URL])
            .output()?;

            if !output.status.success() {
                anyhow::bail!("curl exit code {}", output.status.code().unwrap_or(-1));
            }

            let body: String = String::from_utf8_lossy(&output.stdout).to_string();
            let raw: RawIndex = serde_json::from_str(&body)
            .map_err(|e| anyhow::anyhow!("invalid index.json: {}", e))?;

            let packages = raw.into_iter()
            .filter_map(|map| {
                // Each element should have exactly one key: name -> git url
                map.into_iter().next().map(|(name, git)| RegistryEntry {
                    name,
                    latest: "latest".to_string(),
                                           description: None,
                                           git: Some(git),
                })
            })
            .collect();

            Ok(Self { packages })
        }

        pub fn find(&self, name: &str) -> Option<&RegistryEntry> {
            self.packages.iter().find(|p| p.name == name)
        }
    }

    /// Split "pkg/1.2.3" or "pkg@1.2.3" into (name, Some(version)).
    /// Plain "pkg" returns (name, None).
    pub fn split_pkg_version(spec: &str) -> (String, Option<String>) {
        for sep in ['@', '/'] {
            if let Some(idx) = spec.rfind(sep) {
                let name = &spec[..idx];
                let ver  = &spec[idx + 1..];
                if ver.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                    return (name.to_string(), Some(ver.to_string()));
                }
            }
        }
        (spec.to_string(), None)
    }

    /// Resolve the latest git tag for a repository (cargo-style version
    /// resolution). Falls back to the default branch HEAD if no tags exist.
    ///
    /// Returns `None` if the resolution fails entirely (offline, repo missing).
    pub fn resolve_latest_tag(git_url: &str) -> Option<String> {
        let output = std::process::Command::new("git")
        .args(["ls-remote", "--tags", "--sort=-v:refname", git_url])
        .output()
        .ok()?;
        if !output.status.success() { return None; }

        let text = String::from_utf8_lossy(&output.stdout);
        // First line looks like: <sha>\trefs/tags/v1.2.3
        for line in text.lines() {
            if let Some(tag_ref) = line.split('\t').nth(1) {
                if let Some(tag) = tag_ref.strip_prefix("refs/tags/") {
                    // Skip dereferenced annotated-tag markers (^{})
                    if !tag.ends_with("^{}") {
                        return Some(tag.to_string());
                    }
                }
            }
        }
        None
    }

    /// Download (clone) a package from its registry entry into `dest_dir`.
    ///
    /// `spec` (from `bytes.hk` `[dependencies]`, parsed via `DepSpec::parse`)
    /// and `default_mode` (from `[registry] -> mode`, "release" or "source")
    /// together decide what gets cloned:
    ///
    ///   - `DepSpec::Source`, or `default_mode == "source"` with
    ///     `DepSpec::Latest` — always clone HEAD of the default branch
    ///     (`git clone --depth 1 <url>`, no `--branch`).
    ///   - `DepSpec::Version(v)` — clone tag `v` (trying both `v` and `v{v}`,
    ///     e.g. `1.2.0` and `v1.2.0`, since repos are inconsistent about the
    ///     `v` prefix).
    ///   - `DepSpec::Latest` with `default_mode == "release"` (the overall
    ///     default) — resolve and clone the newest tag via
    ///     `resolve_latest_tag`, falling back to HEAD if the repo has no tags.
    pub fn download_package(
        entry: &RegistryEntry,
        dest_dir: &Path,
        spec: &crate::config::DepSpec,
        default_mode: &str,
    ) -> anyhow::Result<PathBuf> {
        use crate::config::DepSpec;

        let git_url = entry.git.as_ref()
        .ok_or_else(|| anyhow::anyhow!("package `{}` has no git source", entry.name))?;

        let pkg_dir = dest_dir.join(&entry.name);
        if pkg_dir.exists() {
            std::fs::remove_dir_all(&pkg_dir).ok();
        }
        std::fs::create_dir_all(dest_dir)?;

        let tag: Option<String> = match spec {
            DepSpec::Source => None,
            DepSpec::Version(v) => {
                // Try the version string as-is, then with a `v` prefix —
                // repos are inconsistent about tagging `1.2.0` vs `v1.2.0`.
                let candidates = [v.clone(), format!("v{}", v)];
                candidates.into_iter()
                .find(|t| tag_exists(git_url, t))
                .or_else(|| Some(v.clone())) // fall back: let git clone --branch error clearly if truly missing
            }
            DepSpec::Latest => {
                if default_mode == "source" {
                    None
                } else {
                    resolve_latest_tag(git_url)
                }
            }
        };

        clone_or_tarball(git_url, tag.as_deref(), &pkg_dir, &entry.name)?;
        Ok(pkg_dir)
    }

    /// Does `tag` exist as a tag in `git_url`? (used to disambiguate `1.2.0` vs
    /// `v1.2.0` for `DepSpec::Version`)
    fn tag_exists(git_url: &str, tag: &str) -> bool {
        std::process::Command::new("git")
        .args(["ls-remote", "--exit-code", "--tags", git_url, tag])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
    }

    fn clone_or_tarball(git_url: &str, tag: Option<&str>, pkg_dir: &Path, pkg_name: &str) -> anyhow::Result<()> {
        let dest_dir = pkg_dir.parent().unwrap_or(Path::new("."));

        let mut cmd = std::process::Command::new("git");
        cmd.arg("clone").arg("--depth").arg("1");
        if let Some(t) = tag {
            cmd.arg("--branch").arg(t);
        }
        cmd.arg(git_url).arg(pkg_dir);
        cmd.stdout(std::process::Stdio::null());
        cmd.stderr(std::process::Stdio::null());

        let ok = cmd.status().map(|s| s.success()).unwrap_or(false);
        if ok { return Ok(()); }

        // Fallback: tarball download via GitHub codeload (no tag, HEAD of default branch)
        if let Some(tarball_url) = github_tarball_url(git_url, tag) {
            let tmp_tar = dest_dir.join(format!("{}.tar.gz", pkg_name));
            let dl_ok = std::process::Command::new("curl")
            .args(["-fsSL", "-o", tmp_tar.to_str().unwrap_or(""), &tarball_url])
            .status().map(|s| s.success()).unwrap_or(false);
            if dl_ok {
                std::fs::create_dir_all(pkg_dir)?;
                std::process::Command::new("tar")
                .args(["-xzf", tmp_tar.to_str().unwrap_or(""),
                      "-C", pkg_dir.to_str().unwrap_or(""),
                      "--strip-components=1"])
                .status().ok();
                std::fs::remove_file(&tmp_tar).ok();
                return Ok(());
            }
        }
        anyhow::bail!("could not fetch `{}` from {} (tag: {:?})", pkg_name, git_url, tag)
    }

    /// Build a GitHub codeload tarball URL from a repo URL + optional ref.
    /// e.g. https://github.com/Bytes-Repository/mold ->
    ///      https://codeload.github.com/Bytes-Repository/mold/tar.gz/refs/heads/main
    fn github_tarball_url(git_url: &str, tag: Option<&str>) -> Option<String> {
        let trimmed = git_url.trim_end_matches(".git").trim_end_matches('/');
        let path = trimmed.strip_prefix("https://github.com/")?;
        let r#ref = tag.unwrap_or("HEAD");
        let ref_path = if tag.is_some() {
            format!("refs/tags/{}", r#ref)
        } else {
            "refs/heads/main".to_string()
        };
        Some(format!("https://codeload.github.com/{}/tar.gz/{}", path, ref_path))
    }
