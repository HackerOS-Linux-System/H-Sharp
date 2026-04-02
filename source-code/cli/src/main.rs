use clap::{Parser, Subcommand};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

mod build;
mod check;
mod new;
mod preview;

#[derive(Parser)]
#[command(
    name = "hsharp",
    bin_name = "hsharp",
    version = env!("CARGO_PKG_VERSION"),
    about = "H# — the cybersecurity-first compiled language",
)]
pub struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Build the project to a native binary
    Build {
        #[arg(short, long)]
        output: Option<String>,
        /// Target (linux-x86_64, windows-x86_64, macos-aarch64, ...)
        #[arg(short, long)]
        target: Option<String>,
        #[arg(long)]
        debug: bool,
        #[arg(long = "no-opt")]
        no_opt: bool,
    },
    /// Preview / interpret without compiling
    Preview {
        file: Option<std::path::PathBuf>,
    },
    /// Check syntax and types only
    Check {
        file: Option<std::path::PathBuf>,
    },
    /// Create a new H# project
    New {
        name: String,
        #[arg(short, long, default_value = "app")]
        template: String,
    },
    /// List cross-compilation targets
    Targets,
}

fn main() {
    print_banner();
    let cli = Cli::parse();
    match cli.command {
        Command::Build { output, target, debug, no_opt } => build::run(output, target, debug, no_opt),
        Command::Preview { file }  => preview::run(file),
        Command::Check { file }    => check::run(file),
        Command::New { name, template } => new::run(name, template),
        Command::Targets => {
            println!("{}\n", "Available cross-compilation targets:".bold());
            for (name, desc) in hsharp_compiler::TargetTriple::all_named() {
                println!("  {}  {}", format!("{:<25}", name).cyan(), desc);
            }
            println!("\n{}", "Usage: hsharp build --target linux-aarch64".dimmed());
        }
    }
}

fn print_banner() {
    println!("{}", "  H# Language 0.1.0  —  cybersecurity-first compiled language".cyan().bold());
    println!();
}

pub fn make_bar(total: u64, prefix: &str) -> ProgressBar {
    let pb = ProgressBar::new(total);
    pb.set_style(
        ProgressStyle::default_bar()
            .template(&format!("{{spinner:.cyan}} {} [{{bar:40.cyan/blue}}] {{pos}}/{{len}}  {{msg}}", prefix))
            .unwrap()
            .progress_chars("<#>-"),
    );
    pb.enable_steady_tick(Duration::from_millis(80));
    pb
}

pub fn make_spinner(msg: &str) -> ProgressBar {
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.cyan} {msg}").unwrap());
    pb.set_message(msg.to_string());
    pb.enable_steady_tick(Duration::from_millis(80));
    pb
}
