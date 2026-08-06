use clap::{Parser, Subcommand};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

mod compile;
mod check;
mod new;
mod preview;

#[derive(Parser)]
#[command(
name = "h#",
bin_name = "h#",
version = env!("CARGO_PKG_VERSION"),
          about = "h# — HackerOS-first compiled language",
          long_about = None,
)]
pub struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Compile a H# source file to a native binary
    ///
    /// Examples:
    ///   h# compile src/main.h#
    ///   h# compile src/main.h# -o build/myapp --release
    ///   h# compile src/main.h# --target linux-aarch64 --emit-ir
    Compile {
        #[arg(help = "Source file to compile (e.g. src/main.h#)")]
        file: std::path::PathBuf,

        /// Output binary path (default: build/<stem>)
        #[arg(short, long)]
        output: Option<String>,

        /// Cross-compilation target (linux-x86_64, windows-x86_64, macos-aarch64, …)
        #[arg(short, long)]
        target: Option<String>,

        /// Enable LLVM O3 + native CPU codegen, LTO, strip
        #[arg(long)]
        release: bool,

        /// Disable optimisations (O0, no LTO)
        #[arg(long = "no-opt")]
        no_opt: bool,

        /// Keep DWARF debug info in the binary
        #[arg(long)]
        debug: bool,

        /// Dynamically link output (default: static)
        #[arg(long = "dynamic")]
        dynamic: bool,

        /// Dump optimised LLVM IR to stdout instead of emitting a binary
        #[arg(long = "emit-ir")]
        emit_ir: bool,

        /// Emit kind: bin (default), obj (.o), so (.so/.dylib/.dll), lib (.a)
        /// Example: h# compile src/main.h# --emit so
        #[arg(long = "emit", value_name = "KIND")]
        emit_kind: Option<String>,

        /// Print every compilation step
        #[arg(short, long)]
        verbose: bool,

        /// Project-wide default MemoryMode fallback (weaker than a
        /// function's own @mode and weaker than its file's `@: mode`
        /// directive — see CompileOptions::default_mem_mode). Mainly set
        /// by the `bytes` package manager from `bytes.hk`'s `mem_mode`
        /// key, not typed by hand.
        /// Valid: default, safety, arc, arena, pointers
        #[arg(long = "mem-mode", value_name = "MODE")]
        mem_mode: Option<String>,
    },

    /// Preview / interpret a file without compiling
    Preview {
        #[arg(required = true)]
        file: std::path::PathBuf,
    },

    /// Check syntax and types only (no binary emitted)
    Check {
        files: Vec<std::path::PathBuf>,
    },

    /// Create a new H# project from a template
    New {
        name: String,
        #[arg(short, long, default_value = "app")]
        template: String,
    },

    /// List available cross-compilation targets
    Targets,

    /// Open the H# documentation in your browser
    Docs,
}

fn main() {
    print_banner();
    let cli = Cli::parse();
    match cli.command {
        Command::Compile { file, output, target, release, no_opt, debug, dynamic, emit_ir, emit_kind, verbose, mem_mode } =>
        compile::run(file, output, target, release, no_opt, debug, dynamic, emit_ir, emit_kind, verbose, mem_mode),
        Command::Preview { file }  => preview::run(Some(file)),
        Command::Check { files }   => check::run_multi(files),
        Command::New { name, template } => new::run(name, template),
        Command::Targets => {
            println!("{}\n", "Available cross-compilation targets:".bold());
            for (name, desc) in hsharp_compiler::TargetTriple::all_named() {
                println!("  {}  {}", format!("{:<25}", name).cyan(), desc);
            }
            println!("\n{}", "Usage: h# compile --target linux-aarch64 src/main.h#".dimmed());
        }
        Command::Docs => open_docs(),
    }
}

/// Open the H# documentation site in the user's default browser. Tries,
/// in order: `termux-open-url` (Termux has no real desktop/xdg session —
/// this is its own opener that hands the URL to whatever browser app is
/// installed on the phone), `xdg-open` (Linux desktop), `open` (macOS),
/// `cmd /c start` (Windows). Falls back to just printing the URL if none
/// of those exist or the launch fails, so the person can still get there.
fn open_docs() {
    const DOCS_URL: &str = "https://hackeros-linux-system.github.io/HackerOS-Website/h-sharp/docs.html";

    let opened = if cfg!(target_os = "windows") {
        std::process::Command::new("cmd").args(["/c", "start", DOCS_URL]).status()
    } else if cfg!(target_os = "macos") {
        std::process::Command::new("open").arg(DOCS_URL).status()
    } else if std::env::var_os("TERMUX_VERSION").is_some() {
        std::process::Command::new("termux-open-url").arg(DOCS_URL).status()
    } else {
        std::process::Command::new("xdg-open").arg(DOCS_URL).status()
    };

    match opened {
        Ok(status) if status.success() => {
            println!("{} {}", "Opened docs:".green().bold(), DOCS_URL.dimmed());
        }
        _ => {
            println!("{}", "Couldn't open a browser automatically. Docs are here:".yellow());
            println!("  {}", DOCS_URL.cyan().underline());
        }
    }
}

fn print_banner() {
    println!("{}", "  H# v0.8  LLVM backend".cyan().bold());
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
