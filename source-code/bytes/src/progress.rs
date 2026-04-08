/// bytes progress bar — [#------] style with theme switcher
/// Default: [#------] [42%] [status]
/// Arrow:   [>-------] [42%] [status]
/// Cargo:   [===>    ] [42%] [status]

use colored::*;
use std::io::Write;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum BarTheme { Default, Arrow, Cargo }

impl Default for BarTheme { fn default() -> Self { Self::Default } }

impl std::fmt::Display for BarTheme {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self { Self::Default => write!(f, "default"), Self::Arrow => write!(f, "arrow"), Self::Cargo => write!(f, "cargo") }
    }
}
impl std::str::FromStr for BarTheme {
    type Err = ();
    fn from_str(s: &str) -> Result<Self,()> {
        match s { "arrow" => Ok(Self::Arrow), "cargo" => Ok(Self::Cargo), _ => Ok(Self::Default) }
    }
}

pub struct BytesBar {
    pub total:   u64,
    pub current: u64,
    pub width:   usize,
    pub theme:   BarTheme,
    pub status:  String,
}

impl BytesBar {
    pub fn new(total: u64, theme: BarTheme) -> Self {
        Self { total, current: 0, width: 20, theme, status: String::new() }
    }

    pub fn set_status(&mut self, s: impl Into<String>) { self.status = s.into(); }

    pub fn inc(&mut self, n: u64) {
        self.current = (self.current + n).min(self.total);
        self.render();
    }

    pub fn finish(&mut self, msg: &str) {
        self.current = self.total;
        self.render();
        println!();
        println!("  {} {}", "✓".green().bold(), msg.bold());
    }

    fn render(&self) {
        let pct = if self.total == 0 { 100.0 } else { self.current as f64 / self.total as f64 * 100.0 };
        let filled = ((pct / 100.0) * self.width as f64) as usize;
        let empty  = self.width.saturating_sub(filled);

        // Bar rendering per theme
        // Default: [#------]   (filled=# empty=-)
        // Arrow:   [>-------]  (leading > then -)
        // Cargo:   [===>    ]  (filled== then > then spaces)
        let bar = match &self.theme {
            BarTheme::Default => {
                let f: String = "#".repeat(filled);
                let e: String = "-".repeat(empty);
                format!("{}{}{}{}", "[".cyan(), f.cyan().bold(), e.dimmed(), "]".cyan())
            }
            BarTheme::Arrow => {
                if filled == 0 {
                    format!("{}{}{}", "[".cyan(), "-".repeat(self.width).dimmed(), "]".cyan())
                } else {
                    let lead = ">".repeat(1);
                    let dashes: String = "-".repeat(empty);
                    let fill_part = if filled > 1 { "#".repeat(filled - 1) } else { String::new() };
                    format!("{}{}{}{}{}", "[".cyan(), fill_part.cyan().bold(), lead.cyan().bold(), dashes.dimmed(), "]".cyan())
                }
            }
            BarTheme::Cargo => {
                if filled == 0 {
                    format!("{}{}{}", "[".cyan(), " ".repeat(self.width), "]".cyan())
                } else {
                    let eq_part: String = "=".repeat(filled.saturating_sub(1));
                    let spaces: String  = " ".repeat(empty);
                    format!("{}{}{}{}{}", "[".cyan(), eq_part.cyan().bold(), ">".cyan().bold(), spaces, "]".cyan())
                }
            }
        };

        // ETA: rough estimate
        let pct_str = format!("{:.0}%", pct);
        let eta_str = if pct > 0.0 && pct < 100.0 {
            let remaining = self.total.saturating_sub(self.current);
            let rate = self.current.max(1);
            format!(" ~{}s", remaining / rate)
        } else { String::new() };

        let status = if self.status.len() > 32 { &self.status[..32] } else { &self.status };

        print!("\r{} {} {}{}  {}", bar, pct_str.yellow().bold(), eta_str.dimmed(), " ".repeat(10), status.cyan());
        std::io::stdout().flush().ok();
    }
}

/// Multi-item queue display below progress bar
pub fn print_queue(items: &[String], current_idx: usize) {
    let shown: Vec<_> = items.iter().skip(current_idx).take(5).collect();
    if shown.is_empty() { return; }
    println!(); // newline after bar
    for (i, item) in shown.iter().enumerate() {
        let prefix = if i == 0 { "  →".cyan().bold().to_string() } else { "  ·".dimmed().to_string() };
        println!("{} {}", prefix, item.dimmed());
    }
    // Move cursor back up
    print!("\x1b[{}A", shown.len() + 1);
    std::io::stdout().flush().ok();
}

/// Settings TUI for bytes (same style as vira settings)
pub fn bytes_settings_tui(theme: &mut BarTheme) -> anyhow::Result<()> {
    use std::io::{BufRead};

    loop {
        print!("\x1b[2J\x1b[H");
        std::io::stdout().flush().ok();

        println!("{}", "╔═══════════════════════════════════╗".cyan());
        println!("{}", "║         BYTES  SETTINGS           ║".cyan());
        println!("{}", "╚═══════════════════════════════════╝".cyan());
        println!();
        println!("  {} Progress bar theme: {}", "[1]".cyan().bold(), theme.to_string().yellow());
        println!("  {}   default  [#------] [%]", " ".dimmed());
        println!("  {}   arrow    [#>-----] [%]", " ".dimmed());
        println!("  {}   cargo    [===>   ] [%]", " ".dimmed());
        println!();
        println!("  {} Save & exit", "[s]".green().bold());
        println!("  {} Exit without saving", "[q]".red().bold());
        println!();
        print!("  → ");
        std::io::stdout().flush().ok();

        let stdin = std::io::stdin();
        let mut line = String::new();
        stdin.lock().read_line(&mut line).ok();

        match line.trim() {
            "1" => {
                print!("\n  Theme (default/arrow/cargo): ");
                std::io::stdout().flush().ok();
                let mut t = String::new();
                std::io::stdin().lock().read_line(&mut t).ok();
                *theme = t.trim().parse().unwrap_or(BarTheme::Default);
                println!("  {} set to: {}", "✓".green(), theme);
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
            "s" | "S" => { println!("\n  {} saved", "✓".green().bold()); break; }
            "q" | "Q" => { println!("\n  {} cancelled", "·".dimmed()); break; }
            _ => {}
        }
    }
    Ok(())
}
