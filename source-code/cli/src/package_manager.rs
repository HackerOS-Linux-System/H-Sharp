
use anyhow::{anyhow, Context, Result};
use colored::Colorize;
use hk_parser::{load_hk_file, parse_hk, HkValue};
use indicatif::{ProgressBar, ProgressStyle};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

const BYTES_INDEX_URL: &str =
"https://raw.githubusercontent.com/Bytes-Repository/repository/main/index.hk";

const CORE_LIBS_PATH: &str = "/usr/lib/HackerOS/H#/";

/// Metadane biblioteki z index.hk
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LibMeta {
    pub name: String,
    pub version: String,
    pub description: String,
    pub authors: Vec<String>,
    pub so_download: Option<String>,
    pub hl_download: Option<String>,
}

/// Manager pakietów H#
pub struct PackageManager {
    bytes_dir: PathBuf,
    index_cache: Option<HashMap<String, LibMeta>>,
}

impl PackageManager {
    pub fn new() -> Result<Self> {
        let home = std::env::var("HOME").unwrap_or_else(|_| "/root".to_string());
        let bytes_dir = PathBuf::from(home)
        .join(".hackeros")
        .join("H#")
        .join("bytes");
        std::fs::create_dir_all(&bytes_dir)
        .context("Nie można utworzyć katalogu bytes")?;
        Ok(Self { bytes_dir, index_cache: None })
    }

    /// Pobiera i parsuje index bibliotek z Bytes
    pub fn fetch_index(&mut self) -> Result<HashMap<String, LibMeta>> {
        if let Some(cache) = &self.index_cache {
            return Ok(cache.clone());
        }

        let pb = ProgressBar::new_spinner();
        pb.set_style(
            ProgressStyle::default_spinner()
            .template("{spinner:.cyan} {msg}")
            .unwrap(),
        );
        pb.set_message("Pobieranie indeksu Bytes...");
        pb.enable_steady_tick(Duration::from_millis(80));

        let response = reqwest::blocking::get(BYTES_INDEX_URL)
        .context("Nie można pobrać indeksu Bytes")?;
        let content = response.text().context("Nie można odczytać indeksu")?;

        pb.finish_with_message(format!("{} Indeks pobrany", "✓".green()));

        let config = parse_hk(&content).map_err(|e| anyhow!("Błąd parsowania index.hk: {}", e))?;
        let mut libs = HashMap::new();

        if let Some(HkValue::Map(libraries)) = config.get("libraries") {
            for (name, val) in libraries {
                if let HkValue::Map(meta) = val {
                    let lib = LibMeta {
                        name: name.clone(),
                        version: meta.get("version")
                        .and_then(|v| v.as_string().ok())
                        .unwrap_or_else(|| "0.1".to_string()),
                        description: meta.get("description")
                        .and_then(|v| v.as_string().ok())
                        .unwrap_or_default(),
                        authors: meta.get("authors")
                        .and_then(|v| v.as_array().ok())
                        .map(|arr| arr.iter().filter_map(|v| v.as_string().ok()).collect())
                        .unwrap_or_default(),
                        so_download: meta.get("so-download")
                        .and_then(|v| v.as_string().ok()),
                        hl_download: meta.get(".hl-download")
                        .and_then(|v| v.as_string().ok()),
                    };
                    libs.insert(name.clone(), lib);
                }
            }
        }

        self.index_cache = Some(libs.clone());
        Ok(libs)
    }

    /// Instaluje bibliotekę bytes do ~/.hackeros/H#/bytes/
    pub fn install(&mut self, name: &str) -> Result<()> {
        let index = self.fetch_index()?;

        let lib = index.get(name)
        .ok_or_else(|| anyhow!("Biblioteka `{}` nie istnieje w indeksie Bytes.\nSpróbuj: h# search {}", name, name))?;

        println!(
            "{} Instaluję {} v{} - {}",
            "→".cyan(),
                 lib.name.bold(),
                 lib.version,
                 lib.description
        );

        let lib_dir = self.bytes_dir.join(&lib.name);
        std::fs::create_dir_all(&lib_dir)?;

        // Preferujemy .hl, następnie .so / .a
        if let Some(hl_url) = &lib.hl_download.clone() {
            self.download_file(hl_url, &lib_dir.join(format!("{}.hl", lib.name)))?;
        } else if let Some(so_url) = &lib.so_download.clone() {
            let ext = if so_url.ends_with(".a") { "a" } else { "so" };
            self.download_file(so_url, &lib_dir.join(format!("lib{}.{}", lib.name, ext)))?;
        } else {
            return Err(anyhow!("Brak plików do pobrania dla `{}`", name));
        }

        // Zapisz metadane
        let meta_path = lib_dir.join("meta.json");
        let meta_json = serde_json::to_string_pretty(lib)?;
        std::fs::write(meta_path, meta_json)?;

        println!("{} Zainstalowano {}", "✓".green().bold(), lib.name.bold());
        Ok(())
    }

    fn download_file(&self, url: &str, dest: &Path) -> Result<()> {
        let pb = ProgressBar::new_spinner();
        pb.set_style(
            ProgressStyle::default_spinner()
            .template("{spinner:.green} {msg}")
            .unwrap(),
        );
        pb.set_message(format!("Pobieranie {}...", dest.file_name().unwrap_or_default().to_string_lossy()));
        pb.enable_steady_tick(Duration::from_millis(80));

        let response = reqwest::blocking::get(url)
        .with_context(|| format!("Nie można pobrać: {}", url))?;
        let bytes = response.bytes().context("Błąd odczytu danych")?;
        std::fs::write(dest, &bytes)?;

        pb.finish_with_message(format!("{} {}", "✓".green(), dest.display()));
        Ok(())
    }

    /// Usuwa bibliotekę
    pub fn remove(&self, name: &str) -> Result<()> {
        let lib_dir = self.bytes_dir.join(name);
        if !lib_dir.exists() {
            return Err(anyhow!("Biblioteka `{}` nie jest zainstalowana", name));
        }
        std::fs::remove_dir_all(&lib_dir)?;
        println!("{} Usunięto {}", "✓".green().bold(), name.bold());
        Ok(())
    }

    /// Wyszukuje biblioteki w indeksie
    pub fn search(&mut self, query: &str) -> Result<Vec<LibMeta>> {
        let index = self.fetch_index()?;
        let q = query.to_lowercase();
        let results: Vec<LibMeta> = index.values()
        .filter(|lib| {
            lib.name.to_lowercase().contains(&q)
            || lib.description.to_lowercase().contains(&q)
        })
        .cloned()
        .collect();
        Ok(results)
    }

    /// Wyświetla zainstalowane biblioteki
    pub fn list_installed(&self) -> Result<Vec<String>> {
        let mut libs = Vec::new();
        if self.bytes_dir.exists() {
            for entry in std::fs::read_dir(&self.bytes_dir)? {
                let entry = entry?;
                if entry.path().is_dir() {
                    libs.push(entry.file_name().to_string_lossy().to_string());
                }
            }
        }
        Ok(libs)
    }

    /// Czyści cache bibliotek
    pub fn clean(&self) -> Result<()> {
        if self.bytes_dir.exists() {
            std::fs::remove_dir_all(&self.bytes_dir)?;
            std::fs::create_dir_all(&self.bytes_dir)?;
        }
        println!("{} Cache wyczyszczone", "✓".green().bold());
        Ok(())
    }

    /// Aktualizuje zainstalowane biblioteki
    pub fn update(&mut self) -> Result<()> {
        let installed = self.list_installed()?;
        if installed.is_empty() {
            println!("Brak zainstalowanych bibliotek.");
            return Ok(());
        }
        println!("{} Aktualizuję {} bibliotek(i)...", "→".cyan(), installed.len());
        let index = self.fetch_index()?;
        for name in &installed {
            let meta_path = self.bytes_dir.join(name).join("meta.json");
            if let Ok(content) = std::fs::read_to_string(&meta_path) {
                if let Ok(local_meta) = serde_json::from_str::<LibMeta>(&content) {
                    if let Some(remote) = index.get(name) {
                        if remote.version != local_meta.version {
                            println!(
                                "  {} {} {} → {}",
                                "↑".yellow(), name, local_meta.version, remote.version
                            );
                            self.install(name)?;
                        } else {
                            println!("  {} {} (aktualne {})", "✓".green(), name, local_meta.version);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Sprawdza czy lib jest zainstalowany i zwraca ścieżkę
    pub fn resolve_lib(&self, name: &str) -> Option<PathBuf> {
        // Najpierw sprawdź bytes
        let bytes_path = self.bytes_dir.join(name);
        if bytes_path.exists() {
            return Some(bytes_path);
        }

        // Następnie core
        let core_path = PathBuf::from(CORE_LIBS_PATH).join(name);
        if core_path.exists() {
            return Some(core_path);
        }

        None
    }
}

impl Default for PackageManager {
    fn default() -> Self {
        Self::new().expect("Nie można zainicjalizować Package Managera")
    }
}
