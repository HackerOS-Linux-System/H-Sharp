/// bytes progress bar — same themes as vira
use colored::*;
use std::io::Write;

pub enum Theme { Default, Arrow, Cargo }

pub struct Bar { pub n: u64, pub total: u64, pub width: usize, pub theme: Theme, pub label: String }

impl Bar {
    pub fn new(total: u64) -> Self { Self { n: 0, total, width: 38, theme: Theme::Default, label: String::new() } }
    pub fn set_label(&mut self, s: impl Into<String>) { self.label = s.into(); }
    pub fn inc(&mut self, n: u64) { self.n = (self.n + n).min(self.total); self.render(); }
    pub fn finish(&mut self, msg: &str) { self.n = self.total; self.render(); println!(); println!("  {} {}", "✓".green().bold(), msg.bold()); }

    fn render(&self) {
        let pct = if self.total == 0 { 100.0 } else { self.n as f64 / self.total as f64 * 100.0 };
        let filled = ((pct / 100.0) * self.width as f64) as usize;
        let empty  = self.width.saturating_sub(filled);
        let bar = match self.theme {
            Theme::Default => format!("{}{}{}{}", "<".cyan(), "#".repeat(filled).cyan().bold(), "-".repeat(empty).dimmed(), ">".cyan()),
            Theme::Arrow   => {
                if filled == 0 { format!("{}{}{}", "[".cyan(), ".".repeat(self.width).dimmed(), "]".cyan()) }
                else { format!("{}{}{}{}{}", "[".cyan(), "-".repeat(filled.saturating_sub(1)).cyan().bold(), ">".cyan().bold(), ".".repeat(empty).dimmed(), "]".cyan()) }
            }
            Theme::Cargo   => {
                if filled == 0 { format!("{}{}{}", "[".cyan(), " ".repeat(self.width), "]".cyan()) }
                else { format!("{}{}{}{}{}", "[".cyan(), "=".repeat(filled.saturating_sub(1)).cyan().bold(), ">".cyan().bold(), " ".repeat(empty), "]".cyan()) }
            }
        };
        let label = if self.label.len() > 28 { &self.label[..28] } else { &self.label };
        print!("\r{} {:5.1}% {}", bar, pct, label.cyan());
        std::io::stdout().flush().ok();
    }
}
