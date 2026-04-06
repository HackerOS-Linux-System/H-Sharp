/// Vira progress bar — three themes: default (H# style), arrow, cargo-like
use colored::*;
use std::io::{self, Write};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ProgressTheme {
    /// Default H# / Vira theme: <####----------> 42% [pkg]
    Default,
    /// Arrow theme: [-------->........] 42% [pkg]
    Arrow,
    /// Cargo-like: [====>            ] 42% [pkg]
    Cargo,
}

impl Default for ProgressTheme { fn default() -> Self { Self::Default } }

impl std::fmt::Display for ProgressTheme {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Default => write!(f, "default"),
            Self::Arrow   => write!(f, "arrow"),
            Self::Cargo   => write!(f, "cargo"),
        }
    }
}

impl std::str::FromStr for ProgressTheme {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "default" => Ok(Self::Default),
            "arrow"   => Ok(Self::Arrow),
            "cargo"   => Ok(Self::Cargo),
            _         => Err(format!("unknown theme: {}", s)),
        }
    }
}

pub struct ProgressBar {
    theme:   ProgressTheme,
    width:   usize,
    current: u64,
    total:   u64,
    label:   String,
    queue:   Vec<String>,
    started: Instant,
}

impl ProgressBar {
    pub fn new(total: u64, theme: ProgressTheme) -> Self {
        Self {
            theme,
            width:   40,
            current: 0,
            total,
            label:   String::new(),
            queue:   Vec::new(),
            started: Instant::now(),
        }
    }

    pub fn set_label(&mut self, s: impl Into<String>) { self.label = s.into(); }
    pub fn set_queue(&mut self, q: Vec<String>)       { self.queue = q; }

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
        let pct = if self.total == 0 { 100.0 } else { (self.current as f64 / self.total as f64) * 100.0 };
        let filled = ((pct / 100.0) * self.width as f64) as usize;
        let empty  = self.width.saturating_sub(filled);

        let bar = match self.theme {
            ProgressTheme::Default => {
                // <####----------->
                let f: String = "#".repeat(filled);
                let e: String = "-".repeat(empty);
                format!("{}{}{}{}", "<".cyan(), f.cyan().bold(), e.dimmed(), ">".cyan())
            }
            ProgressTheme::Arrow => {
                // [-------->........]
                if filled == 0 {
                    let dots: String = ".".repeat(self.width);
                    format!("{}{}{}", "[".cyan(), dots.dimmed(), "]".cyan())
                } else {
                    let dashes: String = "-".repeat(filled.saturating_sub(1));
                    let dots: String   = ".".repeat(empty);
                    format!("{}{}{}{}{}", "[".cyan(), dashes.cyan().bold(), ">".cyan().bold(), dots.dimmed(), "]".cyan())
                }
            }
            ProgressTheme::Cargo => {
                // [====>           ]
                if filled == 0 {
                    let spaces: String = " ".repeat(self.width);
                    format!("{}{}{}", "[".cyan(), spaces, "]".cyan())
                } else {
                    let eq: String    = "=".repeat(filled.saturating_sub(1));
                    let spaces: String = " ".repeat(empty);
                    format!("{}{}{}{}{}", "[".cyan(), eq.cyan().bold(), ">".cyan().bold(), spaces, "]".cyan())
                }
            }
        };

        let pct_str = format!("{:5.1}%", pct);
        let label   = if self.label.len() > 30 { &self.label[..30] } else { &self.label };

        // Clear line + print
        print!("\r{} {} {}", bar, pct_str.yellow(), label.cyan());
        io::stdout().flush().ok();
    }

    /// Print the waiting queue below the progress bar
    pub fn print_queue(&self) {
        if self.queue.is_empty() { return; }
        let remaining: Vec<&String> = self.queue.iter()
            .skip(self.current as usize)
            .take(6)
            .collect();
        if remaining.is_empty() { return; }
        print!("\x1b[{}A", remaining.len() + 1); // move cursor up
        for (i, item) in remaining.iter().enumerate() {
            let prefix = if i == 0 { "  ▸".cyan().bold().to_string() } else { "  ·".dimmed().to_string() };
            println!("{} {}", prefix, item.dimmed());
        }
        print!("\x1b[{}B", remaining.len() + 1); // move cursor back down
    }
}

/// Multi-step build display showing all pending items
pub fn build_display(items: &[String], theme: &ProgressTheme) {
    println!();
    println!("  {} Build queue:", "▸".cyan().bold());
    for (i, item) in items.iter().enumerate() {
        let prefix = if i == 0 { "  →".cyan().bold().to_string() } else { "  ·".dimmed().to_string() };
        println!("{} {}", prefix, item);
    }
    println!();
}
