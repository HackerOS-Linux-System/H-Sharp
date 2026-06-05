use colored::*;

use crate::config::{
    default_bytes_hk, default_bytes_toml, ram_cache_dir, BytesProject,
    cleanup_stale_sessions, project_cache_dir, SUPPORTED_LANGUAGES,
};
use crate::installer::Installer;
use crate::isolation::{hackeros_libs_base, hackeros_cache_base, ViraCache};
use crate::jit::{BytesRunner, ExecTier};
use crate::lockfile::LockFile;
use crate::progress::{BytesBar, BarTheme};
use crate::python_interop::{setup_python_deps, PythonEnv};
use crate::registry::{download_package, Registry, split_pkg_version};
use crate::workspace::{build_workspace, print_summary, scaffold_workspace};

const VERSION: &str = "0.7.0";

pub fn run() -> anyhow::Result<()> {
    cleanup_stale_sessions();

    let mut parser = lexopt::Parser::from_env();

    let mut cmd     = String::new();
    let mut extra   = Vec::<String>::new();
    let mut verbose = false;
    let mut tier    = String::new();
    let mut release = false;
    let mut file    = String::new();

    loop {
        use lexopt::Arg;
        match parser.next()? {
            Some(Arg::Long("version")) | Some(Arg::Short('V')) => {
                print_version();
                return Ok(());
            }
            Some(Arg::Long("help")) | Some(Arg::Short('h')) => {
                print_help();
                return Ok(());
            }
            Some(Arg::Long("verbose")) | Some(Arg::Short('v')) => verbose = true,
            Some(Arg::Long("release")) | Some(Arg::Short('r'))  => release = true,
            Some(Arg::Long("tier")) | Some(Arg::Short('t')) => {
                tier = parser.value()?.to_str().unwrap_or("jit").to_string();
            }
            Some(Arg::Long("file")) | Some(Arg::Short('f')) => {
                file = parser.value()?.to_str().unwrap_or("").to_string();
            }
            Some(Arg::Value(v)) => {
                let s = v.to_str().unwrap_or("").to_string();
                if cmd.is_empty() {
                    cmd = s;
                } else {
                    extra.push(s);
                }
            }
            Some(Arg::Long(u))  => extra.push(format!("--{}", u)),
            Some(Arg::Short(c)) => extra.push(format!("-{}", c)),
            None => break,
        }
    }

    if cmd.is_empty() {
        print_help();
        return Ok(());
    }

    match cmd.as_str() {
        // ── Project management ──────────────────────────────────────────────
        "new" => {
            let name = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes new <name>"))?;
            let fmt  = extra.get(1).map(|s| s.as_str()).unwrap_or("hk");
            cmd_new(name, fmt)?;
        }
        "new-workspace" | "new-ws" => {
            let name = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes new-workspace <name> [members...]"))?;
            let mode = if extra.iter().any(|s| s == "--special") { "special" } else { "standard" };
            cmd_new_workspace(name, mode, &extra[1..])?;
        }

        // ── Build / run ─────────────────────────────────────────────────────
        "run" => {
            let entry = if !file.is_empty() {
                file.clone()
            } else {
                extra.first().cloned().unwrap_or_else(|| {
                    BytesProject::find()
                    .and_then(|p| BytesProject::load(&p).ok())
                    .map(|proj| proj.entry_file())
                    .unwrap_or_else(|| "src/main.h#".into())
                })
            };
            let run_args: Vec<String> = if file.is_empty() {
                extra.iter().skip(1).cloned().collect()
            } else {
                extra.clone()
            };
            cmd_run(&entry, &run_args, verbose, &tier)?;
        }
        "build" => {
            cmd_build(&extra, release, verbose)?;
        }

        // ── Package management ──────────────────────────────────────────────
        "add" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes add <package>"))?;
            let ver = extra.get(1).map(|s| s.as_str()).unwrap_or("latest");
            // Detect python: prefix
            if pkg.starts_with("python:") || pkg.starts_with("py:") {
                let name = pkg.trim_start_matches("python:").trim_start_matches("py:");
                cmd_python(name, Some(ver))?;
            } else {
                cmd_add(pkg, ver, release)?;
            }
        }
        "remove" | "rm" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes remove <package>"))?;
            cmd_remove(pkg)?;
        }
        "install" => {
            cmd_install(verbose, release)?;
        }
        "update" => {
            cmd_update(verbose)?;
        }
        "list" | "ls" => {
            cmd_list()?;
        }

        // ── Workspace ───────────────────────────────────────────────────────
        "workspace" | "ws" => {
            let sub = extra.first().map(|s| s.as_str()).unwrap_or("info");
            cmd_workspace(sub, &extra[1.min(extra.len())..], release, verbose)?;
        }

        // ── Tooling ─────────────────────────────────────────────────────────
        "test" => {
            cmd_test(&extra, verbose)?;
        }
        "fmt" | "format" => {
            cmd_fmt(&extra, verbose)?;
        }
        "doc" => {
            cmd_doc(&extra, verbose)?;
        }
        "check" => {
            cmd_check(&extra, verbose)?;
        }

        // ── Utility ─────────────────────────────────────────────────────────
        "clean" => {
            let everything = extra.iter().any(|s| s == "--everything");
            cmd_clean(everything)?;
        }
        "info" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes info <package>"))?;
            cmd_info(pkg)?;
        }
        "search" => {
            let q = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes search <query>"))?;
            cmd_search(q)?;
        }
        "python" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes python <package>"))?;
            let ver = extra.get(1).map(|s| s.as_str());
            cmd_python(pkg, ver)?;
        }
        "cache" => {
            cmd_cache_info()?;
        }
        "langs" | "languages" => {
            cmd_langs()?;
        }
        _ => {
            // Treat unknown as a file to run directly
            if extra.is_empty()
                && (cmd.ends_with(".h#") || cmd.ends_with(".hsp") || cmd.ends_with(".hsharp"))
                {
                    cmd_run(&cmd, &[], verbose, &tier)?;
                } else {
                    eprintln!(
                        "  {} unknown command `{}`. Try `bytes --help`",
                        "error:".red().bold(),
                              cmd
                    );
                    std::process::exit(1);
                }
        }
    }

    Ok(())
}

// ── Commands ──────────────────────────────────────────────────────────────────

fn cmd_new(name: &str, fmt: &str) -> anyhow::Result<()> {
    print_header();
    let root = std::path::Path::new(name);
    anyhow::ensure!(!root.exists(), "directory `{}` already exists", name);

    std::fs::create_dir_all(root.join("src"))?;
    std::fs::create_dir_all(root.join("build"))?;
    std::fs::create_dir_all(root.join("tests"))?;
    std::fs::create_dir_all(root.join("docs"))?;

    // Use HK format by default (cleaner)
    let config_file = if fmt == "toml" {
        std::fs::write(root.join("bytes.toml"), default_bytes_toml(name))?;
        "bytes.toml"
    } else {
        std::fs::write(root.join("bytes.hk"), default_bytes_hk(name))?;
        "bytes.hk"
    };

    std::fs::write(root.join(".gitignore"), ".bytes-cache/\n*.jit\n*.h#bc\nbuild/\n.cache/\n")?;
    std::fs::write(root.join("src").join("main.h#"), default_main(name))?;

    println!("  {} {} (H# project)", "Created:".green().bold(), name.cyan());
    println!("  {} {}", "Entry:  ".dimmed(), "src/main.h#".cyan());
    println!("  {} {}", "Config: ".dimmed(), config_file.cyan());
    println!();
    println!(
        "  {} {}",
        "Next:".bold(),
             format!("cd {} && bytes run", name).dimmed()
    );
    println!(
        "  {}",
        "      bytes add scanner          # H# package".dimmed()
    );
    println!(
        "  {}",
        "      bytes python numpy         # Python package".dimmed()
    );
    Ok(())
}

fn cmd_new_workspace(name: &str, mode: &str, extra: &[String]) -> anyhow::Result<()> {
    print_header();

    // Parse members from extra: "app:h#" "lib:rust" etc.
    let mut members: Vec<(&str, &str)> = Vec::new();
    let parsed: Vec<(String, String)> = extra
    .iter()
    .filter(|s| !s.starts_with("--"))
    .map(|s| {
        if let Some((n, l)) = s.split_once(':') {
            (n.to_string(), l.to_string())
        } else {
            (s.clone(), "h#".to_string())
        }
    })
    .collect();

    let pairs: Vec<(&str, &str)> = if parsed.is_empty() {
        vec![("app", "h#"), ("lib", "h#")]
    } else {
        parsed.iter().map(|(n, l)| (n.as_str(), l.as_str())).collect()
    };

    scaffold_workspace(name, mode, &pairs)?;
    Ok(())
}

fn cmd_run(file: &str, run_args: &[String], verbose: bool, tier: &str) -> anyhow::Result<()> {
    if !std::path::Path::new(file).exists() {
        anyhow::bail!("file not found: {}", file);
    }

    let mut project = BytesProject::find()
    .and_then(|p| BytesProject::load(&p).ok())
    .unwrap_or_default();

    if !tier.is_empty() {
        project
        .jit
        .get_or_insert_with(Default::default)
        .tier = Some(tier.to_string());
    }

    // Setup Python deps
    if let Some(py_config) = &project.python {
        let cache = ram_cache_dir().join("pyenv");
        std::fs::create_dir_all(&cache)?;
        setup_python_deps(py_config, &cache)?;
    }

    let mut runner = BytesRunner::new(project, verbose);
    let exit_code  = runner.run(file, run_args)?;

    // Clean up RAM session on exit
    let session = ram_cache_dir();
    if session.exists() {
        std::fs::remove_dir_all(&session).ok();
    }

    std::process::exit(exit_code);
}

fn cmd_build(extra: &[String], release: bool, verbose: bool) -> anyhow::Result<()> {
    print_header();

    let project = BytesProject::find()
    .and_then(|p| BytesProject::load(&p).ok())
    .unwrap_or_default();

    // Workspace build
    if project.is_workspace() {
        let ws = project.workspace.as_ref().unwrap();
        let results = build_workspace(ws, release, verbose)?;
        print_summary(&results);
        let any_fail = results.iter().any(|r| !r.success);
        if any_fail {
            std::process::exit(1);
        }
        return Ok(());
    }

    // Single project build
    let entry = extra.first().cloned().unwrap_or_else(|| project.entry_file());
    let cache  = if release {
        project_cache_dir(std::path::Path::new("."))
    } else {
        ram_cache_dir()
    };
    std::fs::create_dir_all(&cache)?;
    std::fs::create_dir_all("build")?;

    let mode = if release { "release (JIT → native)" } else { "dev (JIT)" };
    println!(
        "  {} {} [{}]",
        "Building:".cyan().bold(),
             entry.dimmed(),
             mode
    );

    // Install deps first
    if !project.dependencies.is_empty() {
        cmd_install(verbose, release)?;
    }

    // Run h# build
    let out = format!("build/{}", project.package.name.trim_start_matches('/'));
    let mut args = vec!["hsharp".to_string(), "build".to_string(), entry.clone(), "-o".to_string(), out.clone()];
    if release {
        args.push("--release".to_string());
    }

    let status = std::process::Command::new(&args[0])
    .args(&args[1..])
    .status();

    match status {
        Ok(s) if s.success() => {
            println!("  {} binary: {}", "✓".green().bold(), out.cyan());
        }
        _ => {
            eprintln!("  {} build failed", "✗".red().bold());
            std::process::exit(1);
        }
    }
    Ok(())
}

fn cmd_add(pkg: &str, ver: &str, release: bool) -> anyhow::Result<()> {
    print_header();
    println!(
        "  {} {} to project...",
        "Adding".cyan().bold(),
             pkg.yellow()
    );

    // Update bytes.toml / bytes.hk
    if let Some(toml_path) = BytesProject::find() {
        let mut src = std::fs::read_to_string(&toml_path)?;
        let dep_line = if toml_path.ends_with(".hk") {
            format!("-> {} => {}", pkg, ver)
        } else {
            format!("{} = \"{}\"", pkg, ver)
        };
        if src.contains("[dependencies]") {
            if let Some(idx) = src.find("[dependencies]") {
                let section_end = src[idx + 14..]
                .find("\n[")
                .map(|i| i + idx + 14)
                .unwrap_or(src.len());
                src.insert_str(section_end, &format!("\n{}", dep_line));
            }
        } else {
            src.push_str(&format!("\n[dependencies]\n{}\n", dep_line));
        }
        std::fs::write(&toml_path, src)?;
    }

    // Download to appropriate cache
    let cache = if release {
        project_cache_dir(std::path::Path::new(".")).join("packages")
    } else {
        ram_cache_dir().join("packages")
    };
    std::fs::create_dir_all(&cache)?;

    let mut bar = BytesBar::new(3, BarTheme::Default);
    bar.set_status(format!("resolving {}", pkg));
    bar.inc(1);

    let registry = Registry::fetch();
    let (pkg_name, _) = split_pkg_version(pkg);

    if let Some(entry) = registry.find(&pkg_name) {
        bar.set_status(format!("downloading {}", pkg));
        bar.inc(1);
        download_package(entry, &cache)?;

        // Update lockfile
        let mut lock = LockFile::read();
        lock.lock(&pkg_name, ver, entry.git.clone(), None);
        lock.write();

        bar.set_status("done".to_string());
        bar.inc(1);
        bar.finish(&format!(
            "added {}@{} → {}",
            pkg.cyan(),
                            ver.green(),
                            if release { ".cache/packages" } else { "~/.hackeros/H#/libs/ (RAM)" }
        ));
    } else {
        bar.set_status(format!("{} (stub)", pkg));
        bar.inc(2);
        // Write stub even if not in registry
        std::fs::write(
            cache.join(format!("{}.h#", pkg)),
                       format!(";; bytes pkg stub: {} v{}\n", pkg, ver),
        )?;
        bar.finish(&format!("added {}@{} (stub — not in registry)", pkg.cyan(), ver.yellow()));
    }

    println!(
        "  {} {}: use \"bytes -> {}\" from \"{}\"",
        "import".dimmed(),
             pkg,
             pkg,
             pkg
    );
    Ok(())
}

fn cmd_remove(pkg: &str) -> anyhow::Result<()> {
    print_header();

    if let Some(toml_path) = BytesProject::find() {
        let src = std::fs::read_to_string(&toml_path)?;
        let (prefix, end) = if toml_path.ends_with(".hk") {
            (format!("-> {} =>", pkg), "")
        } else {
            (format!("{} =", pkg), "")
        };
        let new_src: String = src
        .lines()
        .filter(|l| !l.trim_start().starts_with(&prefix))
        .map(|l| format!("{}\n", l))
        .collect();
        std::fs::write(&toml_path, new_src)?;
    }

    let mut lock = LockFile::read();
    lock.unlock(pkg);
    lock.write();

    // Remove from caches
    for cache_dir in &[
        ram_cache_dir().join("packages"),
        project_cache_dir(std::path::Path::new(".")).join("packages"),
    ] {
        let pkg_dir = cache_dir.join(pkg);
        if pkg_dir.exists() {
            std::fs::remove_dir_all(&pkg_dir).ok();
        }
    }

    println!("  {} removed `{}`", "✓".green().bold(), pkg.cyan());
    Ok(())
}

fn cmd_install(verbose: bool, release: bool) -> anyhow::Result<()> {
    print_header();
    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project = BytesProject::load(&toml_path)?;

    if project.dependencies.is_empty() && project.python.is_none() {
        println!("  {}", "Nothing to install.".dimmed());
        return Ok(());
    }

    println!(
        "  {} {}",
        "Installing for:".cyan().bold(),
             project.package.name.yellow()
    );

    let cache = if release {
        project_cache_dir(std::path::Path::new("."))
    } else {
        ram_cache_dir()
    };
    std::fs::create_dir_all(&cache)?;

    // H# deps
    if !project.dependencies.is_empty() {
        let total = project.dependencies.len() as u64;
        let mut bar = BytesBar::new(total, BarTheme::Default);
        let registry = Registry::fetch();
        let pkg_cache = cache.join("packages");
        std::fs::create_dir_all(&pkg_cache)?;

        let mut lock = LockFile::read();
        for (pkg, ver) in &project.dependencies {
            bar.set_status(format!("fetching {}", pkg));
            if let Some(entry) = registry.find(pkg) {
                download_package(entry, &pkg_cache).ok();
                lock.lock(pkg, ver, entry.git.clone(), None);
            } else {
                std::fs::write(
                    pkg_cache.join(format!("{}.h#", pkg)),
                               format!(";; stub: {} v{}\n", pkg, ver),
                )
                .ok();
                lock.lock(pkg, ver, None, None);
            }
            bar.inc(1);
        }
        lock.write();
        bar.finish(&format!(
            "{} H# package(s) installed",
                            project.dependencies.len()
        ));
    }

    // Python deps
    if let Some(py) = &project.python {
        println!();
        println!(
            "  {} Python {} packages...",
            "Setting up".cyan(),
                 py.version.yellow()
        );
        let py_cache = cache.join("pyenv");
        std::fs::create_dir_all(&py_cache)?;
        match setup_python_deps(py, &py_cache) {
            Ok(_)  => println!("  {} Python env ready", "✓".green().bold()),
            Err(e) => eprintln!("  {} Python setup: {}", "warn:".yellow(), e),
        }
    }

    println!();
    println!(
        "  {} packages ready: {}",
        "✓".green().bold(),
             cache.display().to_string().cyan()
    );
    Ok(())
}

fn cmd_update(verbose: bool) -> anyhow::Result<()> {
    print_header();
    println!("  {} checking for updates...", "bytes".cyan().bold());

    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project = BytesProject::load(&toml_path)?;

    let registry  = Registry::fetch();
    let mut lock  = LockFile::read();
    let mut updated = 0usize;

    for (pkg, current_ver) in &project.dependencies {
        if let Some(entry) = registry.find(pkg) {
            let latest = &entry.latest;
            if latest != current_ver && latest != "latest" {
                println!(
                    "  {} {}  {} → {}",
                    "↑".cyan().bold(),
                         pkg.cyan(),
                         current_ver.yellow(),
                         latest.green()
                );
                lock.lock(pkg, latest, entry.git.clone(), None);
                updated += 1;
            } else {
                println!("  {} {} {}", "✓".green(), pkg, current_ver.dimmed());
            }
        }
    }
    lock.write();

    if updated > 0 {
        println!(
            "\n  {} {} package(s) updated. Run `bytes install` to apply.",
                 "✓".green().bold(),
                 updated
        );
    } else {
        println!("\n  {} All packages up to date.", "✓".green().bold());
    }
    Ok(())
}

fn cmd_list() -> anyhow::Result<()> {
    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project = BytesProject::load(&toml_path)?;

    println!(
        "  {} {}",
        "Project:".bold(),
             project.package.name.cyan()
    );
    println!();

    if project.dependencies.is_empty() {
        println!("  {}", "No H# dependencies.".dimmed());
    } else {
        println!("  {:<28} {}", "PACKAGE".bold(), "VERSION".bold());
        println!("  {}", "─".repeat(42).dimmed());
        for (k, v) in &project.dependencies {
            println!("  {:<28} {}", k.cyan(), v.green());
        }
    }

    if let Some(py) = &project.python {
        println!();
        println!("  {} Python {}", "python:".bold(), py.version.yellow());
        for pkg in &py.packages {
            println!("  {:<28} {}", pkg.cyan(), "pip".dimmed());
        }
    }
    Ok(())
}

fn cmd_workspace(sub: &str, extra: &[String], release: bool, verbose: bool) -> anyhow::Result<()> {
    match sub {
        "build" => cmd_build(extra, release, verbose)?,
        "info" | "list" => {
            let toml_path = BytesProject::find()
            .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
            let project = BytesProject::load(&toml_path)?;
            if let Some(ws) = &project.workspace {
                println!("  {} {}", "Workspace:".bold(), project.package.name.cyan());
                println!("  {} {}", "Mode:     ".dimmed(), ws.mode.as_deref().unwrap_or("standard"));
                println!("  {} {}", "Members:  ".dimmed(), ws.members.len());
                println!();
                for m in &ws.members {
                    let lang = ws.languages.get(m).map(|s| s.as_str()).unwrap_or("h#");
                    println!("  {} {} ({})", "·".dimmed(), m.cyan(), lang.yellow());
                }
            } else {
                println!("  {}", "Not a workspace project.".dimmed());
            }
        }
        _ => {
            eprintln!("  {} unknown workspace subcommand `{}`", "error:".red(), sub);
        }
    }
    Ok(())
}

fn cmd_test(extra: &[String], verbose: bool) -> anyhow::Result<()> {
    crate::test_runner::run_tests(extra, verbose)
}

fn cmd_fmt(extra: &[String], verbose: bool) -> anyhow::Result<()> {
    crate::fmt_cmd::format_files(extra, verbose)
}

fn cmd_doc(extra: &[String], verbose: bool) -> anyhow::Result<()> {
    crate::doc_gen::generate_docs(extra, verbose)
}

fn cmd_check(extra: &[String], verbose: bool) -> anyhow::Result<()> {
    let files: Vec<String> = if extra.is_empty() {
        walkdir::WalkDir::new(".")
        .max_depth(5)
        .into_iter()
        .flatten()
        .filter(|e| {
            e.file_type().is_file()
            && e.path()
            .extension()
            .map(|x| x == "h#" || x == "hsp")
            .unwrap_or(false)
            && !e.path().starts_with("./build")
        })
        .map(|e| e.path().display().to_string())
        .collect()
    } else {
        extra.clone()
    };

    println!(
        "  {} {} file(s)",
             "Checking:".cyan().bold(),
             files.len()
    );

    let mut errors = 0usize;
    for f in &files {
        let ok = std::process::Command::new("hsharp")
        .args(["check", f])
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
        if ok {
            println!("  {} {}", "✓".green(), f.dimmed());
        } else {
            println!("  {} {}", "✗".red(), f);
            errors += 1;
        }
    }
    if errors > 0 {
        std::process::exit(1);
    }
    Ok(())
}

fn cmd_clean(everything: bool) -> anyhow::Result<()> {
    let session = ram_cache_dir();
    if session.exists() {
        std::fs::remove_dir_all(&session)?;
        println!(
            "  {} cleaned RAM session: {}",
            "✓".green().bold(),
                 session.display().to_string().cyan()
        );
    }

    let libs = hackeros_libs_base();
    if libs.exists() {
        let mut cleaned = 0usize;
        if let Ok(entries) = std::fs::read_dir(&libs) {
            for e in entries.flatten() {
                if e.file_name().to_string_lossy().starts_with("session-") {
                    std::fs::remove_dir_all(e.path()).ok();
                    cleaned += 1;
                }
            }
        }
        if cleaned > 0 {
            println!(
                "  {} {} session(s) cleaned from {}",
                     "✓".green().bold(),
                     cleaned,
                     libs.display().to_string().cyan()
            );
        }
    }

    if everything {
        if std::path::Path::new("build").exists() {
            std::fs::remove_dir_all("build")?;
            println!("  {} cleaned build/", "✓".green().bold());
        }
        if std::path::Path::new(".cache").exists() {
            std::fs::remove_dir_all(".cache")?;
            println!("  {} cleaned .cache/", "✓".green().bold());
        }
    }

    if std::path::Path::new(".bytes-cache").exists() {
        std::fs::remove_dir_all(".bytes-cache")?;
        println!("  {} cleaned .bytes-cache/", "✓".green().bold());
    }

    println!("  {}", "All clean.".green());
    Ok(())
}

fn cmd_info(pkg: &str) -> anyhow::Result<()> {
    let reg = Registry::fetch();
    match reg.find(pkg) {
        None => eprintln!("  {} `{}` not found in registry", "✗".red(), pkg),
        Some(e) => {
            println!("  {} {}", "Package:".bold(), e.name.cyan().bold());
            println!("  {} {}", "Latest: ".bold(), e.latest.green());
            if let Some(d) = &e.description {
                println!("  {} {}", "Desc:   ".bold(), d);
            }
            if let Some(git) = &e.git {
                println!("  {} {}", "Source: ".dimmed(), git.cyan());
            }
            println!(
                "  {} {}",
                "Install:".dimmed(),
                     format!("bytes add {}", e.name).cyan()
            );
        }
    }
    Ok(())
}

fn cmd_search(q: &str) -> anyhow::Result<()> {
    print_header();
    let reg = Registry::fetch();
    let results: Vec<_> = reg
    .packages
    .iter()
    .filter(|p| {
        p.name.contains(q)
        || p.description
        .as_deref()
        .unwrap_or("")
        .contains(q)
    })
    .collect();

    println!("  {:<25} {}", "PACKAGE".bold(), "SOURCE".bold());
    println!("  {}", "─".repeat(50).dimmed());
    for p in &results {
        let src = p.git.as_deref().unwrap_or("Bytes-Repository");
        println!("  {:<25} {}", p.name.cyan(), src.dimmed());
    }
    if results.is_empty() {
        println!("  {}", "No packages found.".dimmed());
    } else {
        println!();
        println!("  {} {} result(s)", "Found:".dimmed(), results.len());
    }
    Ok(())
}

fn cmd_python(pkg: &str, ver: Option<&str>) -> anyhow::Result<()> {
    print_header();
    println!(
        "  {} Python package: {}",
        "Installing".cyan().bold(),
             pkg.yellow()
    );
    let cache = ram_cache_dir().join("pyenv");
    std::fs::create_dir_all(&cache)?;
    let env = PythonEnv::setup("3", &cache)?;
    env.install_package(pkg, ver)?;
    println!(
        "  {} use: {}",
        "Done!".green().bold(),
             format!("use \"python -> {}\" from \"{}\"", pkg, pkg).cyan()
    );
    Ok(())
}

fn cmd_cache_info() -> anyhow::Result<()> {
    println!(
        "  {} {}",
        "bytes libs:".bold(),
             hackeros_libs_base().display().to_string().cyan()
    );
    println!(
        "  {}",
        "type: RAM-backed (tmpfs mount), auto-cleared on reboot".dimmed()
    );

    let session = ram_cache_dir();
    if session.exists() {
        let size = walkdir_size(&session);
        println!(
            "  {} {} KB (session {})",
                 "size:".dimmed(),
                 size / 1024,
                 std::process::id()
        );
    } else {
        println!("  {} (no active session)", "size:".dimmed());
    }

    println!();
    let vcache = ViraCache::open();
    println!(
        "  {} {}",
        "vira cache:".bold(),
             hackeros_cache_base().display().to_string().cyan()
    );
    println!(
        "  {}",
        "type: persistent, isolated per-package".dimmed()
    );
    println!(
        "  {} {:.1} MB",
        "size:".dimmed(),
             vcache.total_size_mb()
    );
    let pkgs = vcache.list();
    if !pkgs.is_empty() {
        println!();
        println!("  {:<28} {}", "PACKAGE".bold(), "VERSION".bold());
        println!("  {}", "─".repeat(38).dimmed());
        for (name, ver) in &pkgs {
            println!("  {:<28} {}", name.cyan(), ver.green());
        }
    }
    Ok(())
}

fn cmd_langs() -> anyhow::Result<()> {
    print_header();
    println!("  {}", "Supported workspace languages:".bold());
    println!();
    println!("  {:<15} {}", "LANG".bold(), "TOOLCHAIN".bold());
    println!("  {}", "─".repeat(40).dimmed());
    for (lang, desc) in SUPPORTED_LANGUAGES {
        println!("  {:<15} {}", lang.cyan(), desc.dimmed());
    }
    println!();
    println!(
        "  {}",
        "Usage: bytes new-workspace myws app:h# lib:rust server:go".dimmed()
    );
    Ok(())
}

// ── Utility helpers ───────────────────────────────────────────────────────────

fn walkdir_size(path: &std::path::Path) -> u64 {
    let mut total = 0u64;
    if let Ok(entries) = std::fs::read_dir(path) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                total += walkdir_size(&p);
            } else if let Ok(m) = std::fs::metadata(&p) {
                total += m.len();
            }
        }
    }
    total
}

// ── UI ────────────────────────────────────────────────────────────────────────

fn print_header() {
    println!();
    println!(
        "  {}  H# RAM-JIT Package Manager",
        "bytes".cyan().bold()
    );
    println!(
        "  {}  libs: ~/.hackeros/H#/libs/ (tmpfs, RAM-backed)",
             format!("v{}", VERSION).dimmed()
    );
    println!();
}

fn print_version() {
    println!("bytes {} (H# RAM-JIT PM + Workspace Builder)", VERSION);
}

fn print_help() {
    print_header();
    println!("  {}", "USAGE:".bold());
    println!("    {} <command> [options]", "bytes".cyan());
    println!();
    println!("  {}", "PROJECT:".bold());
    println!("    {}  Create H# project (fmt: hk|toml)", "new <name> [fmt]".cyan());
    println!("    {}  Create multi-language workspace", "new-workspace <name> [m:lang ...]".cyan());
    println!("    {}  Run with JIT (RAM cache)", "run [file.h#]".cyan());
    println!("    {}  Build project or workspace", "build [--release]".cyan());
    println!();
    println!("  {}", "PACKAGES:".bold());
    println!("    {}  Add H# dependency", "add <pkg> [ver]".cyan());
    println!("    {}  Remove dependency", "remove <pkg>".cyan());
    println!("    {}  Install all deps from manifest", "install".cyan());
    println!("    {}  Update all packages", "update".cyan());
    println!("    {}  List installed packages", "list".cyan());
    println!("    {}  Search package registry", "search <query>".cyan());
    println!("    {}  Show package info", "info <pkg>".cyan());
    println!("    {}  Install Python package into RAM venv", "python <pkg>".cyan());
    println!();
    println!("  {}", "TOOLING (v0.7):".bold());
    println!("    {}  Run #[test] functions", "test [file.h#]".cyan());
    println!("    {}  Format H# source files", "fmt [file.h#]".cyan());
    println!("    {}  Generate docs from /// comments", "doc [dir]".cyan());
    println!("    {}  Check syntax & types", "check [files...]".cyan());
    println!();
    println!("  {}", "UTILITY:".bold());
    println!("    {}  Show RAM cache info", "cache".cyan());
    println!("    {}  Clear RAM cache", "clean [--everything]".cyan());
    println!("    {}  Show supported workspace languages", "langs".cyan());
    println!();
    println!("  {}", "OPTIONS:".bold());
    println!("    {}  Execution tier: interpreter|bytecode|jit", "--tier <t>".cyan());
    println!("    {}  Release build", "--release, -r".cyan());
    println!("    {}  Verbose output", "--verbose, -v".cyan());
    println!();
    println!("  {}", "EXAMPLES:".bold());
    println!("    {}", "bytes new myapp && cd myapp && bytes run".dimmed());
    println!("    {}", "bytes add scanner                # H# package".dimmed());
    println!("    {}", "bytes python numpy               # Python package".dimmed());
    println!("    {}", "bytes run --tier bytecode        # skip JIT".dimmed());
    println!("    {}", "bytes build --release            # native binary".dimmed());
    println!("    {}", "bytes test                       # run #[test] fns".dimmed());
    println!("    {}", "bytes fmt                        # format all .h#".dimmed());
    println!("    {}", "bytes doc                        # generate docs".dimmed());
    println!();
    println!("  {}", "WORKSPACE EXAMPLES:".bold());
    println!(
        "    {}",
        "bytes new-workspace myws app:h# lib:rust server:go".dimmed()
    );
    println!(
        "    {}",
        "bytes new-workspace bigws app:h# lib:cpp ui:typescript --special".dimmed()
    );
    println!("    {}", "bytes build --release            # build all members".dimmed());
    println!();
    println!("  {}", "REGISTRY:".bold());
    println!(
        "    {}",
        "https://github.com/Bytes-Repository/repository/blob/main/index.json".dimmed()
    );
    println!();
    println!("  {}", "ISOLATION:".bold());
    println!(
        "    {}",
        "bytes run  → tmpfs ~/.hackeros/H#/libs/ (vanishes on reboot)".dimmed()
    );
    println!(
        "    {}",
        "bytes build --release → project .cache/ (persistent)".dimmed()
    );
    println!(
        "    {}",
        "vira       → persistent ~/.hackeros/H#/.cache/ (isolated per-pkg)".dimmed()
    );
    println!();
}

fn default_main(name: &str) -> String {
    format!(
        r#";;  {name} — H# project
        ;;  Run:   bytes run
        ;;  Build: bytes build --release
        ;;  Test:  bytes test
        ;;  Docs:  bytes doc

        using "2026"

        ;; v0.7: Result<T, E> and Option<T> built-in
        fn divide(a: int, b: int) -> int is
        if b == 0 is
            panic("division by zero")
        end
        return a / b
        end

        fn fib(n: int) -> int is
        if n <= 1 is
            return n
            end
            return fib(n - 1) + fib(n - 2)
        end

        fn main() is
        write(bold("Hello from H# v0.7!"))
        write("Project: {name}")

        ;; for-in loop over range
        let mut sum: int = 0
        for i in 1..=10 is
            sum += i
            end
            write("Sum 1..10 = " + to_string(sum))

        ;; match expression
        let x: int = 42
        match x is
        0  => write("zero")
        42 => write("the answer")
        _  => write("something else")
        end

        ;; JIT will compile fib() after 100 calls
        for i in 0..5 is
            write("fib(" + to_string(i) + ") = " + to_string(fib(i)))
        end
        end
        "#,
        name = name
    )
}
