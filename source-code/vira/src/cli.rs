/// Vira CLI — H# package manager and build tool
/// Uses lexopt for argument parsing, colored + indicatif for output.
///
/// Usage:
///   vira new <name> [--template T]   Create new H# project
///   vira build [--release]           Build project (calls h#)
///   vira run [args...]               Build + run
///   vira add <pkg> [version]         Add dependency
///   vira remove <pkg>                Remove dependency
///   vira install                     Install all deps from vira.hcl
///   vira update                      Update all packages
///   vira list                        List installed packages
///   vira search <query>              Search registry
///   vira info <pkg>                  Show package info
///   vira clean                       Remove .cache/
///   vira settings                    TUI settings editor
///   vira --version / -V              Print version
///   vira --help / -h                 Print help

use colored::*;
use crate::config::{ViraProject, default_vira_hcl};
use crate::installer::Installer;
use crate::registry::{Registry, print_search_results};
use crate::settings::{ViraSettings, run_settings_tui};

const VERSION: &str = "0.1.0";

pub fn run() -> anyhow::Result<()> {
    let mut parser = lexopt::Parser::from_env();
    let mut args: Vec<String> = Vec::new();

    // Collect positional + flags
    let mut show_version = false;
    let mut show_help    = false;
    let mut release      = false;
    let mut template     = "app".to_string();

    loop {
        match parser.next()? {
            Some(lexopt::Arg::Long("version")) | Some(lexopt::Arg::Short('V')) => show_version = true,
            Some(lexopt::Arg::Long("help"))    | Some(lexopt::Arg::Short('h')) => show_help = true,
            Some(lexopt::Arg::Long("release"))                                  => release = true,
            Some(lexopt::Arg::Long("template")) | Some(lexopt::Arg::Short('t')) => {
                template = parser.value()?.to_str().unwrap_or("app").to_string();
            }
            Some(lexopt::Arg::Value(v)) => args.push(v.to_str().unwrap_or("").to_string()),
            Some(lexopt::Arg::Long(u))  => args.push(format!("--{}", u)),
            Some(lexopt::Arg::Short(c)) => args.push(format!("-{}", c)),
            None => break,
        }
    }

    if show_version {
        print_header();
        println!("  vira {}", VERSION.cyan().bold());
        return Ok(());
    }
    if show_help || args.is_empty() {
        print_help();
        return Ok(());
    }

    let settings = ViraSettings::load();
    let installer = Installer::new(settings.clone());

    let cmd = args[0].as_str();
    match cmd {
        "new" => {
            let name = args.get(1).ok_or_else(|| anyhow::anyhow!("Usage: vira new <name>"))?;
            cmd_new(name, &template)?;
        }
        "build" => {
            print_header();
            cmd_build(release)?;
        }
        "run" => {
            print_header();
            cmd_build(release)?;
            cmd_run(&args[1..])?;
        }
        "add" => {
            let pkg  = args.get(1).ok_or_else(|| anyhow::anyhow!("Usage: vira add <package> [version]"))?;
            let ver  = args.get(2).map(|s| s.as_str()).unwrap_or("latest");
            // Split pkg/version if given as pkg/1.2
            let (name, ver2) = if pkg.contains('/') {
                let parts: Vec<&str> = pkg.splitn(2, '/').collect();
                (parts[0].to_string(), parts.get(1).copied().unwrap_or(ver).to_string())
            } else {
                (pkg.clone(), ver.to_string())
            };
            installer.add(&name, &ver2)?;
        }
        "remove" | "rm" => {
            let pkg = args.get(1).ok_or_else(|| anyhow::anyhow!("Usage: vira remove <package>"))?;
            installer.remove(pkg)?;
        }
        "install" => {
            print_header();
            let hcl = ViraProject::find()
                .ok_or_else(|| anyhow::anyhow!("No vira.hcl found in current directory"))?;
            let project = ViraProject::load(&hcl)?;
            installer.install_project(&project)?;
        }
        "update" => {
            print_header();
            let hcl = ViraProject::find()
                .ok_or_else(|| anyhow::anyhow!("No vira.hcl found in current directory"))?;
            let project = ViraProject::load(&hcl)?;
            println!("  {} Updating packages...", "vira".cyan().bold());
            let registry = Registry::fetch().unwrap_or_default();
            for (name, _ver) in &project.dependencies {
                if let Some(entry) = registry.find(name) {
                    println!("  {} {} → {}", "↑".cyan(), name.cyan(), entry.latest.green());
                }
            }
            installer.install_project(&project)?;
        }
        "list" | "ls" => {
            print_header();
            installer.list_installed()?;
        }
        "search" => {
            let query = args.get(1).ok_or_else(|| anyhow::anyhow!("Usage: vira search <query>"))?;
            print_header();
            println!("  {} `{}`\n", "Searching Vira Registry for:".cyan().bold(), query);
            let spinner = indicatif::ProgressBar::new_spinner();
            spinner.enable_steady_tick(std::time::Duration::from_millis(80));
            spinner.set_message("Fetching registry...");
            let registry = Registry::fetch().unwrap_or_default();
            spinner.finish_and_clear();
            let results = registry.search(query);
            println!("  Found {} result(s)\n", results.len());
            print_search_results(&results);
        }
        "info" => {
            let pkg = args.get(1).ok_or_else(|| anyhow::anyhow!("Usage: vira info <package>"))?;
            let registry = Registry::fetch().unwrap_or_default();
            match registry.find(pkg) {
                None => eprintln!("  {} `{}` not found in registry", "✗".red(), pkg),
                Some(e) => {
                    println!("  {} {}", "Package:".bold(), e.name.cyan().bold());
                    println!("  {} {}", "Latest: ".bold(), e.latest.green());
                    println!("  {} {}", "Versions:".bold(), e.versions.join(", "));
                    if let Some(d) = &e.description { println!("  {} {}", "Desc:   ".bold(), d); }
                    if let Some(a) = &e.author      { println!("  {} {}", "Author: ".bold(), a); }
                    if let Some(l) = &e.license     { println!("  {} {}", "License:".bold(), l); }
                    println!("\n  {}", format!("vira add {}", e.name).dimmed());
                }
            }
        }
        "clean" => {
            installer.clean()?;
        }
        "settings" => {
            run_settings_tui()?;
        }
        _ => {
            eprintln!("  {} Unknown command: `{}`", "error:".red().bold(), cmd);
            eprintln!("  Run `vira --help` for usage.");
            std::process::exit(1);
        }
    }
    Ok(())
}

// ── Sub-commands ──────────────────────────────────────────────────────────────

fn cmd_new(name: &str, template: &str) -> anyhow::Result<()> {
    println!("{}", "  vira".cyan().bold());
    println!("  {} project `{}`\n", "Creating".green().bold(), name.cyan().bold());

    let root = std::path::Path::new(name);
    if root.exists() {
        anyhow::bail!("directory `{}` already exists", name);
    }

    // Choose source dir based on template
    let src_dir = match template { "lib" => "lib", "cmd" => "cmd", _ => "src" };
    std::fs::create_dir_all(root.join(src_dir))?;
    std::fs::create_dir_all(root.join("build"))?;

    // vira.hcl
    std::fs::write(root.join("vira.hcl"), default_vira_hcl(name, template))?;

    // .gitignore
    std::fs::write(root.join(".gitignore"), ".cache/\nbuild/\n*.h#.o\n")?;

    // h#.json (optional metadata)
    let meta = format!(r#"{{"name":"{}","version":"0.1.0","template":"{}"}}"#, name, template);
    std::fs::write(root.join("h#.json"), meta)?;

    // Main source file
    let main_src = template_source(name, template);
    std::fs::write(root.join(src_dir).join("main.h#"), main_src)?;

    println!("  {} {}/", "Created:".green(), name);
    println!("  {} {}/vira.hcl", "Created:".green(), name);
    println!("  {} {}/{}/main.h#\n", "Created:".green(), name, src_dir);
    println!("  {} {}", "Next steps:".bold(), format!("cd {}", name).dimmed());
    println!("  {}", "vira install     # install dependencies".dimmed());
    println!("  {}", "vira build       # compile to binary".dimmed());
    println!("  {}", "h# preview src/main.h#  # quick interpreter preview".dimmed());
    println!();
    Ok(())
}

fn cmd_build(release: bool) -> anyhow::Result<()> {
    let mode = if release { "release" } else { "debug" };
    println!("  {} Building ({})...", "vira".cyan().bold(), mode);

    // Invoke h# compiler
    let hsharp = find_hsharp()?;
    let mut cmd = std::process::Command::new(&hsharp);
    cmd.arg("build");
    if release { cmd.arg("--no-debug"); }

    let status = cmd.status()?;
    if !status.success() {
        anyhow::bail!("h# build failed");
    }
    Ok(())
}

fn cmd_run(extra_args: &[String]) -> anyhow::Result<()> {
    // Find binary in build/
    let entries: Vec<_> = std::fs::read_dir("build")
        .unwrap_or_else(|_| panic!("build/ not found"))
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().ok().map(|t| t.is_file()).unwrap_or(false))
        .collect();

    if entries.is_empty() {
        anyhow::bail!("No binary found in build/. Run `vira build` first.");
    }
    let bin = entries[0].path();
    println!("  {} {}", "Running:".green().bold(), bin.display().to_string().cyan());
    println!();

    let status = std::process::Command::new(&bin)
        .args(extra_args)
        .status()?;
    std::process::exit(status.code().unwrap_or(0));
}

fn find_hsharp() -> anyhow::Result<String> {
    for name in &["hsharp", "h#"] {
        if std::process::Command::new("which").arg(name)
            .output().map(|o| o.status.success()).unwrap_or(false)
        {
            return Ok(name.to_string());
        }
    }
    // Try local: ./hsharp
    if std::path::Path::new("./hsharp").exists() { return Ok("./hsharp".into()); }
    Err(anyhow::anyhow!("h# compiler not found in PATH. Install hsharp first."))
}

// ── UI helpers ────────────────────────────────────────────────────────────────

fn print_header() {
    println!();
    println!("  {}  H# Package Manager & Build Tool", "vira".cyan().bold());
    println!("  {}  {}", "v0.1.0".dimmed(), "https://github.com/vira-io/vira".dimmed());
    println!();
}

fn print_help() {
    print_header();
    println!("  {}", "USAGE:".bold());
    println!("    {} <command> [options]", "vira".cyan());
    println!();
    println!("  {}", "PROJECT:".bold());
    println!("    {}  Create new H# project", "new <name> [--template T]".cyan());
    println!("    {}  Build project (invokes h#)", "build [--release]".cyan());
    println!("    {}  Build + run", "run [args]".cyan());
    println!();
    println!("  {}", "PACKAGES:".bold());
    println!("    {}  Add a dependency", "add <pkg> [ver]".cyan());
    println!("    {}  Remove a dependency", "remove <pkg>".cyan());
    println!("    {}  Install all deps from vira.hcl", "install".cyan());
    println!("    {}  Update all packages", "update".cyan());
    println!("    {}  List installed packages", "list".cyan());
    println!("    {}  Search Vira registry", "search <query>".cyan());
    println!("    {}  Show package info", "info <pkg>".cyan());
    println!("    {}  Clean .cache/ directory", "clean".cyan());
    println!();
    println!("  {}", "OTHER:".bold());
    println!("    {}  TUI settings editor", "settings".cyan());
    println!("    {}  Print version", "--version, -V".cyan());
    println!();
    println!("  {}", "EXAMPLES:".bold());
    println!("    {}", "vira new myapp --template cybersec".dimmed());
    println!("    {}", "vira add scanner/1.2".dimmed());
    println!("    {}", r#"vira add github.com/user/mylib"#.dimmed());
    println!("    {}", "vira build --release".dimmed());
    println!("    {}", "vira settings".dimmed());
    println!();
    println!("  {}", "TEMPLATES:".bold());
    println!("    {}", "app (default), cybersec, network, lib, cmd".dimmed());
    println!();
}

fn template_source(name: &str, template: &str) -> String {
    match template {
        "cybersec" | "security" => format!(r#";;  H# CyberSec Tool — {name}
;;  Run:   vira build && ./build/{name}
;;  Preview: h# preview src/main.h#

use "std -> io -> keyboard" from "kb"
use "std -> crypto -> hex"  from "hex"
use "std -> net -> tcp"     from "tcp"

fn banner() is
    write("╔══════════════════════════════╗")
    write("║  H# CyberSec Tool v0.1       ║")
    write("╚══════════════════════════════╝")
end

fn scan_port(host: string, port: int) -> bool is
    return false  ;; impl: tcp::connect(host, port).is_ok()
end

fn main() is
    banner()
    let target: string = "127.0.0.1"
    write("Target: " + target)

    for port in 1..=1024 is
        let open: bool = scan_port(target, port)
        if open is
            write("[OPEN] " + to_string(port) + "/tcp")
        end
    end
end
"#, name = name),
        "lib" => format!(r#";;  H# Library — {name}

/// Main library entry point
/// Use: use "vira -> {name}" from "{name}"

pub fn add(a: int, b: int) -> int = a + b

pub fn greet(name: string) -> string is
    return "Hello, " + name + " from {name}!"
end
"#, name = name),
        "network" | "net" => format!(r#";;  H# Network Tool — {name}

use "std -> net -> tcp" from "tcp"

fn main() is
    write("H# Network Tool")
    let host: string = "localhost"
    let port: int = 8080
    write("Listening on " + host + ":" + to_string(port))
end
"#, name = name),
        _ => format!(r#";;  H# Application — {name}
;;  Run:   vira build && ./build/{name}
;;  Preview: h# preview src/main.h#

fn greet(name: string) -> string is
    return "Hello, " + name + "!"
end

fn factorial(n: int) -> int is
    if n <= 1 is
        return 1
    end
    return n * factorial(n - 1)
end

fn main() is
    write(greet("H#"))

    let result: int = factorial(10)
    write("10! = " + to_string(result))

    let mut sum: int = 0
    for i in 1..=5 is
        sum += i
    end
    write("Sum 1..=5 = " + to_string(sum))
end
"#, name = name),
    }
}
