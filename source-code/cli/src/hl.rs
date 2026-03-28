use clap::{Parser, Subcommand};
use colored::Colorize;
use std::path::PathBuf;

#[derive(Parser)]
#[command(
name = "hl",
about = "hl - nakładka H# dla skryptów .hl",
version = "0.1.0",
author = "HackerOS Team <hackeros068@gmail.com>",
long_about = "
hl to nakładka dla skryptów H# (.hl).
Pod spodem wywołuje interpreter h#.
Pliki .hl są traktowane jako pełnoprawne skrypty H#
i uruchamiane bez konieczności osobnego etapu kompilacji.
"
)]
struct Cli {
    #[command(subcommand)]
    command: HlCmd,
}

#[derive(Subcommand)]
enum HlCmd {
    /// Uruchamia skrypt .hl
    #[command(name = "run")]
    Run {
        /// Plik skryptu .hl
        file: PathBuf,
        /// Argumenty przekazywane do skryptu
        #[arg(trailing_var_arg = true)]
        args: Vec<String>,
    },

    /// Kompiluje skrypt .hl do binarki
    #[command(name = "compile")]
    Compile {
        /// Plik skryptu .hl
        file: PathBuf,
        /// Plik wyjściowy
        #[arg(short, long)]
        output: Option<String>,
    },

    /// Sprawdza składnię skryptu .hl
    #[command(name = "check")]
    Check {
        /// Plik skryptu .hl
        file: PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        HlCmd::Run { file, args } => cmd_run(&file, &args),
        HlCmd::Compile { file, output } => cmd_compile(&file, output),
        HlCmd::Check { file } => cmd_check(&file),
    };

    if let Err(e) = result {
        eprintln!("{} {}", "[hl błąd]".red().bold(), e);
        std::process::exit(1);
    }
}

fn cmd_run(file: &std::path::Path, _args: &[String]) -> anyhow::Result<()> {
    // Sprawdź rozszerzenie - .hl jest wymagane
    let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
    if ext != "hl" {
        eprintln!(
            "{} hl obsługuje tylko pliki .hl (dostałem .{})",
                  "⚠".yellow(),
                  ext
        );
        eprintln!("  Użyj: {} dla plików .h#", "h# exec".bold());
    }

    if !file.exists() {
        return Err(anyhow::anyhow!("Plik nie istnieje: {}", file.display()));
    }

    // Przekaż do interpretera
    match hsharp_scripting::run_hl_file(file) {
        Ok(()) => Ok(()),
        Err(e) => {
            eprintln!("{} {}", "[runtime błąd]".red().bold(), e);
            Err(anyhow::anyhow!("Błąd wykonania"))
        }
    }
}

fn cmd_compile(file: &std::path::Path, output: Option<String>) -> anyhow::Result<()> {
    let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
    if ext != "hl" {
        eprintln!("{} hl compile: oczekiwano pliku .hl", "⚠".yellow());
    }

    let opts = hsharp_compiler::CompileOptions {
        target: None,
        optimize: false,
        debug: true,
        static_link: true,
        output: output.or_else(|| {
            Some(
                file.file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("output")
                .to_string(),
            )
        }),
    };

    match hsharp_compiler::compile_file(file, &opts) {
        Ok(()) => {
            println!(
                "{} Skompilowano {} → {}",
                "✓".green().bold(),
                     file.display(),
                     opts.output.as_deref().unwrap_or("output")
            );
            Ok(())
        }
        Err(e) => {
            eprintln!("{} Błąd kompilacji: {}", "[błąd]".red().bold(), e);
            Err(anyhow::anyhow!("Kompilacja nieudana"))
        }
    }
}

fn cmd_check(file: &std::path::Path) -> anyhow::Result<()> {
    match hsharp_scripting::check_hl_file(file) {
        Ok(()) => Ok(()),
        Err(e) => {
            eprintln!("{} {}", "[błąd składni]".red().bold(), e);
            Err(anyhow::anyhow!("Błąd składni"))
        }
    }
}
