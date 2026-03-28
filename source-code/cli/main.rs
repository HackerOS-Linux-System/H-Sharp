mod diagnostics;
mod package_manager;

use clap::{Parser, Subcommand};
use colored::Colorize;
use diagnostics::*;
use hsharp_compiler::{compile_file, CompileOptions};
use package_manager::PackageManager;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Parser)]
#[command(
name = "h-sharp",
about = "H# — język programowania HackerOS",
version = "0.1.0",
author = "HackerOS Team <hackeros068@gmail.com>",
)]
struct Cli {
    #[command(subcommand)]
    command: HsharpCmd,
}

#[derive(Subcommand)]
enum HsharpCmd {
    /// Kompiluje plik .h# / .ja / .hsp / .hl do binarki (bez pobierania libów)
    #[command(name = "compile")]
    Compile {
        file: PathBuf,
        #[arg(short, long)] output: Option<String>,
        #[arg(long)] target: Option<String>,
    },

    /// Kompiluje projekt z zarządzaniem zależnościami
    #[command(name = "build")]
    Build {
        #[arg(long)] release: bool,
        #[arg(long)] production: bool,
        #[arg(short, long)] output: Option<String>,
    },

    /// Instaluje bibliotekę z Bytes
    #[command(name = "install")]
    Install { lib: String },

    /// Usuwa bibliotekę
    #[command(name = "remove")]
    Remove { lib: String },

    /// Wyszukuje bibliotekę w Bytes
    #[command(name = "search")]
    Search { query: String },

    /// Czyści cache bytes
    #[command(name = "clean")]
    Clean,

    /// Aktualizuje zainstalowane biblioteki
    #[command(name = "update")]
    Update,

    /// Sprawdza składnię i typy pliku H#
    #[command(name = "check")]
    Check { file: PathBuf },

    /// Uruchamia skrypt .hl (szybki interpreter)
    #[command(name = "run")]
    Run {
        file: PathBuf,
        #[arg(trailing_var_arg = true)] args: Vec<String>,
    },

    /// Interpretuje plik .h# (wolniejszy interpreter)
    #[command(name = "exec")]
    Exec {
        file: PathBuf,
        #[arg(trailing_var_arg = true)] args: Vec<String>,
    },

    /// Uruchamia projekt H# w trybie prerelease
    #[command(name = "start")]
    Start { file: Option<PathBuf> },
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        HsharpCmd::Compile { file, output, target } => cmd_compile(&file, output, target),
        HsharpCmd::Build { release, production, output } => cmd_build(release || production, output),
        HsharpCmd::Install { lib } => cmd_install(&lib),
        HsharpCmd::Remove { lib } => cmd_remove(&lib),
        HsharpCmd::Search { query } => cmd_search(&query),
        HsharpCmd::Clean => cmd_clean(),
        HsharpCmd::Update => cmd_update(),
        HsharpCmd::Check { file } => cmd_check(&file),
        HsharpCmd::Run { file, args } => cmd_run(&file, &args),
        HsharpCmd::Exec { file, args } => cmd_exec(&file, &args),
        HsharpCmd::Start { file } => cmd_start(file.as_deref()),
    };

    if let Err(e) = result {
        eprintln!("{} {}", "✗".red().bold(), e);
        std::process::exit(1);
    }
}

// ─── Komendy ──────────────────────────────────────────────────────────────────

fn cmd_compile(file: &Path, output: Option<String>, target: Option<String>) -> anyhow::Result<()> {
    check_extension(file)?;
    let source = std::fs::read_to_string(file)?;
    print_info(&format!("Kompiluję {}", file.display()));

    let opts = CompileOptions {
        target,
        optimize: false,
        debug: true,
        static_link: true,
        output: output.or_else(|| Some(stem(file))),
    };

    if let Err(e) = compile_file(file, &opts) {
        print_compile_error(&e, &file.display().to_string(), &source);
        return Err(anyhow::anyhow!("Kompilacja nieudana"));
    }

    let out = opts.output.as_deref().unwrap_or("a.out");
    let obj = format!("{}.o", out);
    link_binary(&obj, out, false)?;
    print_success(&format!("Skompilowano → {}", out));
    Ok(())
}

fn cmd_build(release: bool, output: Option<String>) -> anyhow::Result<()> {
    let main_file = find_main()?;
    let source = std::fs::read_to_string(&main_file)?;
    print_info(&format!("Build {} {}", main_file.display(),
                        if release { "(release)" } else { "(debug)" }));

    install_project_deps()?;

    let opts = CompileOptions {
        target: None,
        optimize: release,
        debug: !release,
        static_link: true,
        output: output.or_else(|| Some(stem(&main_file))),
    };

    if let Err(e) = compile_file(&main_file, &opts) {
        print_compile_error(&e, &main_file.display().to_string(), &source);
        return Err(anyhow::anyhow!("Build nieudany"));
    }

    let out = opts.output.as_deref().unwrap_or("a.out");
    link_binary(&format!("{}.o", out), out, release)?;
    print_success(&format!("Build {} → {}", if release { "release" } else { "debug" }, out));
    Ok(())
}

fn cmd_install(lib: &str) -> anyhow::Result<()> {
    PackageManager::new()?.install(lib)?;
    Ok(())
}

fn cmd_remove(lib: &str) -> anyhow::Result<()> {
    PackageManager::new()?.remove(lib)?;
    Ok(())
}

fn cmd_search(query: &str) -> anyhow::Result<()> {
    let mut pm = PackageManager::new()?;
    let results = pm.search(query)?;
    if results.is_empty() {
        println!("Brak wyników dla '{}'", query.bold());
        return Ok(());
    }
    println!("\n{} Wyniki dla '{}':\n", "→".cyan(), query.bold());
    for lib in &results {
        println!("  {} {} {} — {}",
                 "■".cyan(), lib.name.bold().green(),
                 format!("v{}", lib.version).dimmed(),
                     lib.description);
    }
    println!("\n{} wyników\n", results.len());
    Ok(())
}

fn cmd_clean() -> anyhow::Result<()> { PackageManager::new()?.clean()?; Ok(()) }
fn cmd_update() -> anyhow::Result<()> { PackageManager::new()?.update()?; Ok(()) }

fn cmd_check(file: &Path) -> anyhow::Result<()> {
    let source = std::fs::read_to_string(file)
    .map_err(|e| anyhow::anyhow!("Nie można otworzyć '{}': {}", file.display(), e))?;
    let name = file.file_stem().and_then(|s| s.to_str()).unwrap_or("file");
    let fname = file.display().to_string();

    match hsharp_parser::parse(&source, name) {
        Err(e) => {
            Diagnostic::error(friendly_parse_msg_pub(&e))
            .file(&fname)
            .source(&source)
            .explain(&e)
            .suggest("Sprawdź nawiasy kwadratowe [ ] — każdy blok musi być zamknięty")
            .print();
            return Err(anyhow::anyhow!("Błąd składni"));
        }
        Ok(module) => {
            let mut tc = hsharp_compiler::TypeChecker::new();
            tc.check_module(&module);
            if !tc.errors.is_empty() {
                for err in &tc.errors {
                    let msg = err.to_string();
                    Diagnostic::error(friendly_type_msg_pub(&msg))
                    .file(&fname)
                    .source(&source)
                    .explain(&msg)
                    .suggest(&type_suggestion_pub(&msg))
                    .print();
                }
                return Err(anyhow::anyhow!("{} błędów typów", tc.errors.len()));
            }
            print_success(&format!("{} — składnia i typy OK  ({} deklaracji)",
                                   fname, module.decls.len()));
        }
    }
    Ok(())
}

fn cmd_run(file: &Path, _args: &[String]) -> anyhow::Result<()> {
    if !file.exists() {
        return Err(anyhow::anyhow!("Plik nie istnieje: {}", file.display()));
    }
    let source = std::fs::read_to_string(file)?;
    let fname = file.display().to_string();

    match hsharp_scripting::run_hl_file(file) {
        Ok(()) => Ok(()),
        Err(e) => {
            print_script_error(&e.to_string(), &fname, &source, None);
            Err(anyhow::anyhow!("Błąd wykonania skryptu"))
        }
    }
}

fn cmd_exec(file: &Path, _args: &[String]) -> anyhow::Result<()> {
    if !file.exists() {
        return Err(anyhow::anyhow!("Plik nie istnieje: {}", file.display()));
    }
    let source = std::fs::read_to_string(file)?;
    let name = file.file_stem().and_then(|s| s.to_str()).unwrap_or("exec");
    let fname = file.display().to_string();

    match hsharp_compiler::interpreter::run_script(&source, name) {
        Ok(()) => Ok(()),
        Err(e) => {
            print_script_error(&e.to_string(), &fname, &source, None);
            Err(anyhow::anyhow!("Błąd wykonania"))
        }
    }
}

fn cmd_start(file: Option<&Path>) -> anyhow::Result<()> {
    let f = match file {
        Some(f) => f.to_path_buf(),
        None    => find_main()?,
    };
    print_info(&format!("Start (prerelease interpreter): {}", f.display()));
    cmd_exec(&f, &[])
}

// ─── Pomocnicze ───────────────────────────────────────────────────────────────

fn check_extension(file: &Path) -> anyhow::Result<()> {
    let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
    match ext {
        "h#" | "ja" | "hsp" | "hl" => Ok(()),
        _ => Err(anyhow::anyhow!(
            "Nieobsługiwane rozszerzenie '.{}'\nObsługiwane: .h# .ja .hsp .hl", ext
        )),
    }
}

fn stem(file: &Path) -> String {
    file.file_stem().and_then(|s| s.to_str()).unwrap_or("output").to_string()
}

fn find_main() -> anyhow::Result<PathBuf> {
    for c in &["main.h#", "src/main.h#", "Main.h#", "main.ja", "src/main.ja"] {
        let p = PathBuf::from(c);
        if p.exists() { return Ok(p); }
    }
    if let Ok(rd) = std::fs::read_dir(".") {
        for e in rd.flatten() {
            let p = e.path();
            if matches!(p.extension().and_then(|e| e.to_str()), Some("h#" | "ja")) {
                return Ok(p);
            }
        }
    }
    Err(anyhow::anyhow!("Nie znaleziono main.h# — utwórz go lub podaj plik jako argument"))
}

fn link_binary(obj: &str, output: &str, release: bool) -> anyhow::Result<()> {
    let mut args = vec![obj.to_string(), "-o".to_string(), output.to_string(), "-lm".to_string()];
    if release { args.extend(["-O2".to_string(), "-s".to_string()]); }
    args.push("-static".to_string());

    let status = Command::new("gcc").args(&args).status()
    .map_err(|_| anyhow::anyhow!("gcc nie znaleziony — zainstaluj: sudo apt install gcc"))?;

    let _ = std::fs::remove_file(obj);
    if !status.success() {
        return Err(anyhow::anyhow!("Linkowanie nieudane (exit {})", status.code().unwrap_or(-1)));
    }
    Ok(())
}

fn install_project_deps() -> anyhow::Result<()> {
    let p = PathBuf::from("project.hk");
    if !p.exists() { return Ok(()); }
    // project.hk parsing obsługuje PackageManager
    Ok(())
}

// Wrappers publiczne dla diagnostics (żeby nie eksportować prywatnych fn)
fn friendly_parse_msg_pub(e: &str) -> String {
    if e.contains('[') || e.contains(']') {
        "Brakuje nawiasu kwadratowego — bloki H# otwieramy [ i zamykamy ]".to_string()
    } else if e.contains("EOF") {
        "Plik urwał się w połowie — prawdopodobnie brakuje zamykającego ]".to_string()
    } else {
        "Nie rozumiem tej linii — sprawdź składnię H#".to_string()
    }
}

fn friendly_type_msg_pub(msg: &str) -> String {
    if msg.contains("Int") && msg.contains("Str") {
        "Próbujesz połączyć liczbę z tekstem".to_string()
    } else if msg.contains("Niezdefiniowana zmienna") {
        "Ta zmienna nie istnieje w tym miejscu".to_string()
    } else {
        "Problem z typami danych".to_string()
    }
}

fn type_suggestion_pub(msg: &str) -> String {
    if msg.contains("Int") && msg.contains("Str") {
        "Zamień liczbę na tekst: liczba as Str".to_string()
    } else if msg.contains("Niezdefiniowana zmienna") {
        "Zadeklaruj zmienną: let nazwa: Typ = wartość".to_string()
    } else {
        "Sprawdź typy zmiennych — użyj `h# check plik`".to_string()
    }
}
