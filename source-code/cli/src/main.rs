use clap::{Parser, Subcommand};
use colored::Colorize;
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

mod compile;
mod check;
mod new;
mod preview;
mod repl;
mod fmt;
mod lsp_cmd;
mod ffi_header;
mod hlib_export;
mod hlib_cmd;
mod edition_cmd;

#[derive(Parser)]
#[command(
name = "h#",
bin_name = "h#",
version = env!("CARGO_PKG_VERSION"),
          about = "h# — HackerOS-first compiled language",
          long_about = None,
)]
pub struct Cli {
    /// H# edition assumed for files without `using "<year>"` (default: the
    /// project's `Bit.hk` `[edition]` when `lang => h#`, else the newest
    /// edition). Also settable via HSHARP_EDITION. A file's own `using`
    /// always wins for that file. Run `h# editions` to list them.
    #[arg(long, global = true, value_name = "YEAR")]
    edition: Option<String>,

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
        /// by the `bit` package manager from the `mem-mode` key of
        /// `[build]` in `Bit.hk`, not typed by hand.
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

    /// Start an interactive H# REPL (read-eval-print loop)
    Repl,

    /// Reformat H# source file(s) (indentation only — see fmt.rs)
    Fmt {
        /// Files to format. If none given, formats every .h#/.hsp/.h-sharp
        /// file found under the current directory (like `hsharp check`).
        files: Vec<std::path::PathBuf>,

        /// Report which files would change, without writing them (exits
        /// non-zero if any would) — for CI, mirrors `rustfmt --check`.
        #[arg(long)]
        check: bool,
    },

    /// Run the H# language server over stdio (for editor integration)
    ///
    /// Not a separate binary — statically linked into this one. Point
    /// your editor's LSP client at `hsharp lsp` (or `h# lsp`).
    Lsp,

    /// Open the H# documentation in your browser
    Docs,

    /// List the H# editions this toolchain supports and show which one is
    /// the default for files without `using "<year>"` (and why)
    Editions,

    /// Generate a companion C or Rust header for a file's `extern`
    /// blocks — including a real `typedef struct { int64_t ...; }` /
    /// `#[repr(C)] struct { ... i64 }` for every H# struct type an
    /// extern function references by pointer (`&`/`&mut`), matching
    /// H#'s actual field layout (see `compiler::ffi::struct_c_def`'s doc
    /// comment). This is the concrete tool the `StructByValueFfi`
    /// compile-error's hint points to: it's how you find out what layout
    /// your struct actually has on the H# side before hand-writing (or
    /// generating) the matching C/Rust definition.
    FfiHeader {
        #[arg(help = "Source file whose extern blocks to generate a header for")]
        file: std::path::PathBuf,

        /// Header language: c (default) or rust
        #[arg(short, long, default_value = "c")]
        lang: String,
    },

    /// Build, inspect, verify and sign `.hlib` (HackerOS Lib) archives —
    /// H#'s native library format, natively readable by Hacker Lang and
    /// HackerScript too. See /HLIB_FORMAT.md at the repo root.
    #[command(subcommand)]
    Lib(LibCommand),
}

#[derive(Subcommand)]
pub enum LibCommand {
    /// Compile a H# source file to a shared object and package it, its
    /// interface header, and (for any generic/macro export) its AST,
    /// into a single `.hlib` archive.
    ///
    /// Examples:
    ///   h# lib build src/mylib.h# -o mylib.hlib
    ///   h# lib build src/mylib.h# -o mylib.hlib --sign keys/publisher.key
    Build {
        #[arg(help = "H# source file to package (e.g. src/mylib.h#)")]
        file: std::path::PathBuf,

        /// Output .hlib path (default: build/<stem>.hlib)
        #[arg(short, long)]
        output: Option<String>,

        /// Library version string embedded in manifest.json (default: 0.1.0)
        #[arg(long, default_value = "0.1.0")]
        lib_version: String,

        /// Cross-compilation target for the embedded .so (default: host)
        #[arg(short, long)]
        target: Option<String>,

        /// Path to a hex-encoded Ed25519 signing key (see `h# lib keygen`).
        /// Unsigned if omitted.
        #[arg(long)]
        sign: Option<std::path::PathBuf>,

        /// Enable LLVM O3 + native CPU codegen for the embedded .so
        #[arg(long)]
        release: bool,
    },

    /// Print a `.hlib` archive's manifest and entry listing without
    /// verifying checksums or signature (fast — just parses `manifest.json`).
    Inspect {
        #[arg(help = ".hlib file to inspect")]
        file: std::path::PathBuf,
    },

    /// Verify a `.hlib` archive's internal SHA-256 checksums, and
    /// optionally its Ed25519 signature against a known public key.
    Verify {
        #[arg(help = ".hlib file to verify")]
        file: std::path::PathBuf,

        /// Lowercase-hex Ed25519 public key to verify the signature
        /// against. If omitted, only checksums are verified.
        #[arg(long)]
        pubkey: Option<String>,
    },

    /// Generate a fresh Ed25519 keypair for signing `.hlib` archives.
    /// Prints the public key; writes the secret key to `--out` (hex, 0600).
    Keygen {
        /// Where to write the secret signing key (hex-encoded)
        #[arg(short, long, default_value = "hlib_signing.key")]
        out: std::path::PathBuf,
    },

    /// Extract a `.hlib`'s native artifacts to `--into`, and generate a
    /// ready-to-`mod`-include `.h#` stub declaring an `extern` block for
    /// every non-generic export in its header — so consuming a `.hlib`
    /// from H# is just `mod <name>_hlib_bind;` once this has run.
    Bind {
        #[arg(help = ".hlib file to bind")]
        file: std::path::PathBuf,

        /// Directory to extract native artifacts and write the stub into
        #[arg(short, long, default_value = "hlibs")]
        into: std::path::PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();
    // `hsharp lsp` speaks JSON-RPC over stdout — any stray print (the
    // banner included) corrupts the protocol stream and breaks every
    // editor client. `hsharp repl` prints its own banner instead (see
    // repl.rs) so it isn't duplicated. Every other command gets the
    // normal banner.
    // Default edition for files that don't say `using "<year>"` — resolved
    // once, up front (flag > HSHARP_EDITION > Bit.hk [edition] > newest), so
    // the compiler, the interpreter (`preview`/`repl`), `check`, `fmt` and
    // `lib build` all agree. An invalid value exits here with a clear error.
    let anchor: std::path::PathBuf = match &cli.command {
        Command::Compile { file, .. } | Command::Preview { file } | Command::FfiHeader { file, .. } => file.clone(),
        Command::Lib(LibCommand::Build { file, .. }) => file.clone(),
        Command::Check { files } | Command::Fmt { files, .. } if !files.is_empty() => files[0].clone(),
        _ => std::path::PathBuf::from("."),
    };
    let edition_info = edition_cmd::init(cli.edition.clone(), &anchor);
    // Build-like commands print their own report (compile shows backend,
    // edition and toolchain in its summary), so they get no banner above it.
    if !matches!(
        cli.command,
        Command::Lsp | Command::Repl | Command::Compile { .. } | Command::Preview { .. } | Command::Check { .. }
    ) {
        print_banner(edition_info.0);
    }
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
        Command::Editions => edition_cmd::list(edition_info),
        Command::FfiHeader { file, lang } => ffi_header::run(file, lang),
        Command::Repl => repl::run(),
        Command::Fmt { files, check } => fmt::run(files, check),
        Command::Lsp => lsp_cmd::run(),
        Command::Lib(lib_cmd) => hlib_cmd::run(lib_cmd),
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

fn print_banner(edition: hsharp_parser::edition::Edition) {
    println!("{}", format!("  H# v{}  LLVM backend  (default edition {})", env!("CARGO_PKG_VERSION"), edition).cyan().bold());
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
