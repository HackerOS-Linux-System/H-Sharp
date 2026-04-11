use colored::*;
use serde::{Deserialize, Serialize};
use std::io::{self, BufRead, Write};
use crate::progress::ProgressTheme;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ViraSettings {
    pub progress_theme:  ProgressTheme,
    pub parallel_jobs:   usize,
    pub cache_dir:       String,
    pub registry_url:    String,
    pub auto_update:     bool,
    pub color:           bool,
}

impl Default for ViraSettings {
    fn default() -> Self {
        Self {
            progress_theme: ProgressTheme::Default,
            parallel_jobs:  4,
            cache_dir:      ".cache".to_string(),
            registry_url:   "https://raw.githubusercontent.com/vira-io/repository/main/repo-list.json".to_string(),
            auto_update:    true,
            color:          true,
        }
    }
}

impl ViraSettings {
    pub fn load() -> Self {
        let path = settings_path();
        if let Ok(s) = std::fs::read_to_string(&path) {
            serde_json::from_str(&s).unwrap_or_default()
        } else {
            Self::default()
        }
    }

    pub fn save(&self) -> anyhow::Result<()> {
        let path = settings_path();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, serde_json::to_string_pretty(self)?)?;
        Ok(())
    }
}

fn settings_path() -> std::path::PathBuf {
    dirs::config_dir()
        .unwrap_or_else(|| std::path::PathBuf::from("."))
        .join("vira")
        .join("settings.json")
}

/// Interactive TUI settings editor (terminal-based, no external deps)
pub fn run_settings_tui() -> anyhow::Result<()> {
    let mut settings = ViraSettings::load();

    loop {
        // Clear screen
        print!("\x1b[2J\x1b[H");
        io::stdout().flush().ok();

        // Header
        println!("{}", "╔══════════════════════════════════════════╗".cyan());
        println!("{}", "║           VIRA  SETTINGS                 ║".cyan());
        println!("{}", "╚══════════════════════════════════════════╝".cyan());
        println!();

        // Menu items
        let items = [
            ("1", "Progress theme",  format!("{}", settings.progress_theme).yellow().to_string()),
            ("2", "Parallel jobs",   settings.parallel_jobs.to_string().yellow().to_string()),
            ("3", "Cache directory", settings.cache_dir.yellow().to_string()),
            ("4", "Registry URL",    truncate(&settings.registry_url, 40).yellow().to_string()),
            ("5", "Auto-update",     bool_str(settings.auto_update).yellow().to_string()),
            ("6", "Color output",    bool_str(settings.color).yellow().to_string()),
        ];

        for (key, label, value) in &items {
            println!("  {}  {:<22} {}", format!("[{}]", key).cyan().bold(), label, value);
        }
        println!();
        println!("  {}  Save & exit", "[s]".green().bold());
        println!("  {}  Exit without saving", "[q]".red().bold());
        println!();
        print!("  → ");
        io::stdout().flush().ok();

        let stdin = io::stdin();
        let mut line = String::new();
        stdin.lock().read_line(&mut line).ok();
        let choice = line.trim();

        match choice {
            "1" => {
                println!("\n  Themes: {} | {} | {}",
                    "default".cyan(), "arrow".cyan(), "cargo".cyan());
                print!("  Enter theme: ");
                io::stdout().flush().ok();
                let mut t = String::new();
                io::stdin().lock().read_line(&mut t).ok();
                if let Ok(theme) = t.trim().parse::<ProgressTheme>() {
                    settings.progress_theme = theme;
                    println!("  {} Theme set to: {}", "✓".green(), settings.progress_theme);
                } else {
                    println!("  {} Unknown theme", "✗".red());
                }
                std::thread::sleep(std::time::Duration::from_millis(600));
            }
            "2" => {
                print!("\n  Enter parallel jobs (1-16): ");
                io::stdout().flush().ok();
                let mut n = String::new();
                io::stdin().lock().read_line(&mut n).ok();
                if let Ok(v) = n.trim().parse::<usize>() {
                    settings.parallel_jobs = v.clamp(1, 16);
                    println!("  {} Set to {}", "✓".green(), settings.parallel_jobs);
                }
                std::thread::sleep(std::time::Duration::from_millis(600));
            }
            "3" => {
                print!("\n  Enter cache directory path: ");
                io::stdout().flush().ok();
                let mut p = String::new();
                io::stdin().lock().read_line(&mut p).ok();
                settings.cache_dir = p.trim().to_string();
                println!("  {} Set to: {}", "✓".green(), settings.cache_dir);
                std::thread::sleep(std::time::Duration::from_millis(600));
            }
            "4" => {
                print!("\n  Enter registry URL: ");
                io::stdout().flush().ok();
                let mut u = String::new();
                io::stdin().lock().read_line(&mut u).ok();
                settings.registry_url = u.trim().to_string();
                println!("  {} Updated", "✓".green());
                std::thread::sleep(std::time::Duration::from_millis(600));
            }
            "5" => { settings.auto_update = !settings.auto_update; }
            "6" => { settings.color = !settings.color; }
            "s" | "S" => {
                settings.save()?;
                println!("\n  {} Settings saved to: {}", "✓".green().bold(),
                    settings_path().display().to_string().cyan());
                std::thread::sleep(std::time::Duration::from_millis(800));
                break;
            }
            "q" | "Q" => {
                println!("\n  {} Exiting without save", "·".dimmed());
                break;
            }
            _ => {}
        }
    }
    Ok(())
}

fn bool_str(b: bool) -> &'static str { if b { "enabled" } else { "disabled" } }
fn truncate(s: &str, n: usize) -> String {
    if s.len() <= n { s.to_string() } else { format!("{}…", &s[..n-1]) }
}
