use colored::*;

use crate::config::{
    default_bytes_hk, default_bytes_toml, ram_cache_dir, BytesProject,
    cleanup_stale_sessions, project_cache_dir, SUPPORTED_LANGUAGES,
};
use crate::isolation::{hackeros_libs_base, hackeros_cache_base, ViraCache};
use crate::jit::BytesRunner;
use crate::lockfile::LockFile;
use crate::progress::{BytesBar, BarTheme};
use crate::python_interop::{setup_python_deps, PythonEnv};
use crate::registry::{download_package, Registry, split_pkg_version};
use crate::workspace::{build_workspace, print_summary, scaffold_workspace};

const VERSION: &str = "0.7.0";

pub fn run() -> anyhow::Result<()> {
    cleanup_stale_sessions();

    let mut parser  = lexopt::Parser::from_env();
    let mut cmd     = String::new();
    let mut extra   = Vec::<String>::new();
    let mut verbose = false;
    let mut tier    = String::new();
    let mut release = false;
    let mut file    = String::new();

    loop {
        use lexopt::Arg;
        match parser.next()? {
            Some(Arg::Long("version")) | Some(Arg::Short('V')) => { print_version(); return Ok(()); }
            Some(Arg::Long("help"))    | Some(Arg::Short('h')) => { print_help();    return Ok(()); }
            Some(Arg::Long("verbose")) | Some(Arg::Short('v')) => verbose = true,
            Some(Arg::Long("release")) | Some(Arg::Short('r')) => release = true,
            Some(Arg::Long("tier"))    | Some(Arg::Short('t')) => {
                tier = parser.value()?.to_str().unwrap_or("jit").to_string();
            }
            Some(Arg::Long("file")) | Some(Arg::Short('f')) => {
                file = parser.value()?.to_str().unwrap_or("").to_string();
            }
            Some(Arg::Value(v)) => {
                let s = v.to_str().unwrap_or("").to_string();
                if cmd.is_empty() { cmd = s; } else { extra.push(s); }
            }
            Some(Arg::Long(u))  => extra.push(format!("--{}", u)),
            Some(Arg::Short(c)) => extra.push(format!("-{}", c)),
            None => break,
        }
    }

    if cmd.is_empty() { print_help(); return Ok(()); }

    match cmd.as_str() {
        "new" => {
            let name = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes new <name>"))?;
            let fmt  = extra.get(1).map(|s| s.as_str()).unwrap_or("hk");
            cmd_new(name, fmt)?;
        }
        "new-workspace" | "new-ws" => {
            let name = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes new-workspace <name>"))?;
            let mode = if extra.iter().any(|s| s == "--special") { "special" } else { "standard" };
            cmd_new_workspace(name, mode, &extra[1..])?;
        }
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
                extra.to_vec()
            };
            cmd_run(&entry, &run_args, verbose, &tier)?;
        }
        "build" => { cmd_build(&extra, release, verbose)?; }
        "add" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes add <package>"))?;
            let ver = extra.get(1).map(|s| s.as_str()).unwrap_or("latest");
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
        "install"          => { cmd_install(verbose, release)?; }
        "update"           => { cmd_update()?; }
        "list" | "ls"      => { cmd_list()?; }
        "workspace" | "ws" => {
            let sub = extra.first().map(|s| s.as_str()).unwrap_or("info");
            let rest = if extra.is_empty() { &extra[..] } else { &extra[1..] };
            cmd_workspace(sub, rest, release, verbose)?;
        }
        "test"             => { crate::test_runner::run_tests(&extra, verbose)?; }
        "fmt" | "format"   => { crate::fmt_cmd::format_files(&extra, verbose)?; }
        "doc"              => { crate::doc_gen::generate_docs(&extra, verbose)?; }
        "check"            => { cmd_check(&extra, verbose)?; }
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
        "cache"              => { cmd_cache_info()?; }
        "langs" | "languages"=> { cmd_langs()?; }
        _ => {
            if extra.is_empty()
                && (cmd.ends_with(".h#") || cmd.ends_with(".hsp") || cmd.ends_with(".hsharp"))
                {
                    cmd_run(&cmd, &[], verbose, &tier)?;
                } else {
                    eprintln!("  {} unknown command `{}`. Try `bytes --help`", "error:".red().bold(), cmd);
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
    println!("  {} {}", "Next:".bold(), format!("cd {} && bytes run", name).dimmed());
    println!("  {}", "      bytes add scanner".dimmed());
    println!("  {}", "      bytes python numpy".dimmed());
    Ok(())
}

fn cmd_new_workspace(name: &str, mode: &str, extra: &[String]) -> anyhow::Result<()> {
    print_header();
    let parsed: Vec<(String, String)> = extra.iter()
    .filter(|s| !s.starts_with("--"))
    .map(|s| {
        if let Some((n, l)) = s.split_once(':') { (n.to_string(), l.to_string()) }
        else { (s.clone(), "h#".to_string()) }
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
        project.jit.get_or_insert_with(Default::default).tier = Some(tier.to_string());
    }
    if let Some(py_config) = &project.python {
        let cache = ram_cache_dir().join("pyenv");
        std::fs::create_dir_all(&cache)?;
        setup_python_deps(py_config, &cache)?;
    }
    let mut runner    = BytesRunner::new(project, verbose);
    let exit_code     = runner.run(file, run_args)?;
    let session       = ram_cache_dir();
    if session.exists() { std::fs::remove_dir_all(&session).ok(); }
    std::process::exit(exit_code);
}

fn cmd_build(extra: &[String], release: bool, verbose: bool) -> anyhow::Result<()> {
    print_header();
    let project = BytesProject::find()
    .and_then(|p| BytesProject::load(&p).ok())
    .unwrap_or_default();

    if project.is_workspace() {
        let ws      = project.workspace.as_ref().unwrap();
        let results = build_workspace(ws, release, verbose)?;
        print_summary(&results);
        if results.iter().any(|r| !r.success) { std::process::exit(1); }
        return Ok(());
    }

    let entry = extra.first().cloned().unwrap_or_else(|| project.entry_file());
    let cache  = if release {
        project_cache_dir(std::path::Path::new("."))
    } else {
        ram_cache_dir()
    };
    std::fs::create_dir_all(&cache)?;
    std::fs::create_dir_all("build")?;

    if !project.dependencies.is_empty() { cmd_install(verbose, release)?; }

    // Defense-in-depth: even if config parsing somehow yields an empty
    // name, never produce "build/" as the output path — that's a
    // directory, and `ld -o build/` fails with
    // "cannot open output file build/: Jest katalogiem".
    let pkg_name = {
        let n = project.package.name.trim().trim_start_matches('/');
        if n.is_empty() {
            std::path::Path::new(".").canonicalize().ok()
            .and_then(|d| d.file_name().map(|s| s.to_string_lossy().to_string()))
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "out".to_string())
        } else {
            n.to_string()
        }
    };
    let out = format!("build/{}", pkg_name);

    // Decide which compiler to use. v0.8: Cranelift has been removed —
    // `h#` (LLVM, statically linked, merged from the former hhc/
    // hsharp-llvm-compiler crate) is the only AOT compiled backend.
    // `[release] -> backend` still accepts the legacy name "hhc" as an
    // alias for "h#" so existing bytes.hk files keep working.
    //
    // `hsharp build`'s internal typechecker prints a terse one-line
    // "✗ type check failed" with no further detail, whereas `h#` prints
    // full, line-numbered TYPE ERROR/SYNTAX ERROR diagnostics (§1) — so
    // `h#` is preferred for `--release` whenever available.
    let release_backend = project.release.as_ref()
    .and_then(|r| r.backend.as_deref())
    .unwrap_or("h#");

    let use_hsharp_compiler = release && matches!(release_backend, "h#" | "hhc" | "llvm");

    let (program, args): (&str, Vec<String>) = if use_hsharp_compiler {
        // h# compile <file> -o <out> [--release] [--verbose]
        // NOTE: the subcommand is 'compile', not a bare positional arg (v0.8)
        let mut a = vec!["compile".to_string(), entry.clone(), "-o".to_string(), out.clone()];
        if release { a.push("--release".to_string()); }
        if verbose { a.push("--verbose".to_string()); }
        ("/usr/bin/h#", a)
    } else {
        let mut a = vec!["build".to_string(), entry.clone(), "-o".to_string(), out.clone()];
        if release { a.push("--release".to_string()); }
        ("hsharp", a)
    };

    let mode = if release {
        format!("release ({})", program)
    } else {
        "dev (JIT)".to_string()
    };
    println!("  {} {} [{}]", "Building:".cyan().bold(), entry.dimmed(), mode);
    if verbose {
        println!("  {} {} {}", "exec:".dimmed(), program, args.join(" "));
    }
    println!();

    // CRITICAL: always inherit stdout/stderr (the default for Command::status)
    // so the underlying compiler's full diagnostics — parse errors, type
    // errors, link errors — are shown to the user, not swallowed.
    let run = std::process::Command::new(program)
    .args(&args)
    .stdout(std::process::Stdio::inherit())
    .stderr(std::process::Stdio::inherit())
    .status();

    match run {
        Ok(s) if s.success() => {
            println!();
            println!("  {} binary: {}", "checkmark".green().bold(), out.cyan());
        }
        Ok(s) => {
            println!();
            eprintln!(
                "  {} build failed (exit code {})",
                      "error".red().bold(),
                      s.code().unwrap_or(-1)
            );
            if !use_hsharp_compiler && release {
                eprintln!(
                    "  {} `hsharp build --release` gives terse errors. Try the LLVM backend for full diagnostics:",
                    "hint:".yellow()
                );
                eprintln!("        {}", format!("/usr/bin/h# compile --release {} -o {}", entry, out).cyan());
                eprintln!(
                    "  {} or set {} in bytes.hk under [release] to make `bytes build --release` use it by default.",
                    "hint:".yellow(), "backend => h#".cyan()
                );
            }
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("  {} could not run `{}`: {}", "error".red().bold(), program, e);
            eprintln!("  {} is `{}` installed and on PATH?", "hint:".yellow(), program);
            std::process::exit(1);
        }
    }
    Ok(())
}

fn cmd_add(pkg: &str, ver: &str, release: bool) -> anyhow::Result<()> {
    print_header();
    println!("  {} {} to project...", "Adding".cyan().bold(), pkg.yellow());

    if let Some(toml_path) = BytesProject::find() {
        let mut src = std::fs::read_to_string(&toml_path)?;
        let dep_line = if toml_path.ends_with(".hk") {
            format!("-> {} => {}", pkg, ver)
        } else {
            format!("{} = \"{}\"", pkg, ver)
        };
        if src.contains("[dependencies]") {
            if let Some(idx) = src.find("[dependencies]") {
                let section_end = src[idx + 14..].find("\n[")
                .map(|i| i + idx + 14).unwrap_or(src.len());
                src.insert_str(section_end, &format!("\n{}", dep_line));
            }
        } else {
            src.push_str(&format!("\n[dependencies]\n{}\n", dep_line));
        }
        std::fs::write(&toml_path, src)?;
    }

    let cache = if release {
        project_cache_dir(std::path::Path::new(".")).join("packages")
    } else {
        ram_cache_dir().join("packages")
    };
    std::fs::create_dir_all(&cache)?;

    let mut bar = BytesBar::new(3, BarTheme::Default);
    bar.set_status(format!("resolving {}", pkg));
    bar.inc(1);

    let registry    = Registry::fetch();
    let (pkg_name, _) = split_pkg_version(pkg);

    if let Some(entry) = registry.find(&pkg_name) {
        bar.set_status(format!("downloading {}", pkg));
        bar.inc(1);
        let spec = crate::config::DepSpec::parse(ver);
        let mode = BytesProject::find()
        .and_then(|p| BytesProject::load(&p).ok())
        .and_then(|p| p.registry)
        .map(|r| r.mode)
        .unwrap_or_else(|| "release".to_string());
        download_package(entry, &cache, &spec, &mode)?;
        let mut lock = LockFile::read();
        lock.lock(&pkg_name, ver, entry.git.clone(), None);
        lock.write();
        bar.set_status("done".to_string());
        bar.inc(1);
        bar.finish(&format!("added {}@{} -> {}", pkg.cyan(), ver.green(),
                            if release { ".cache/packages" } else { "~/.hackeros/H#/libs/ (RAM)" }));
    } else {
        bar.set_status(format!("{} (stub)", pkg));
        bar.inc(2);
        std::fs::write(cache.join(format!("{}.h#", pkg)),
                       format!(";; bytes pkg stub: {} v{}\n", pkg, ver))?;
                       bar.finish(&format!("added {}@{} (stub)", pkg.cyan(), ver.yellow()));
    }
    println!("  {} use: \"bytes -> {}\" from \"{}\"", "import".dimmed(), pkg, pkg);
    Ok(())
}

fn cmd_remove(pkg: &str) -> anyhow::Result<()> {
    print_header();
    if let Some(toml_path) = BytesProject::find() {
        let src = std::fs::read_to_string(&toml_path)?;
        let prefix = if toml_path.ends_with(".hk") {
            format!("-> {} =>", pkg)
        } else {
            format!("{} =", pkg)
        };
        let new_src: String = src.lines()
        .filter(|l| !l.trim_start().starts_with(&prefix))
        .map(|l| format!("{}\n", l))
        .collect();
        std::fs::write(&toml_path, new_src)?;
    }
    let mut lock = LockFile::read();
    lock.unlock(pkg);
    lock.write();
    for cache_dir in &[
        ram_cache_dir().join("packages"),
        project_cache_dir(std::path::Path::new(".")).join("packages"),
    ] {
        let pkg_dir = cache_dir.join(pkg);
        if pkg_dir.exists() { std::fs::remove_dir_all(&pkg_dir).ok(); }
    }
    println!("  {} removed `{}`", "checkmark".green().bold(), pkg.cyan());
    Ok(())
}

fn cmd_install(_verbose: bool, release: bool) -> anyhow::Result<()> {
    print_header();
    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project = BytesProject::load(&toml_path)?;

    if project.dependencies.is_empty() && project.python.is_none() {
        println!("  {}", "Nothing to install.".dimmed());
        return Ok(());
    }

    println!("  {} {}", "Installing for:".cyan().bold(), project.package.name.yellow());

    let cache = if release {
        project_cache_dir(std::path::Path::new("."))
    } else {
        ram_cache_dir()
    };
    std::fs::create_dir_all(&cache)?;

    if !project.dependencies.is_empty() {
        let total    = project.dependencies.len() as u64;
        let mut bar  = BytesBar::new(total, BarTheme::Default);
        let registry = Registry::fetch();
        let pkg_cache = cache.join("packages");
        std::fs::create_dir_all(&pkg_cache)?;
        let mut lock = LockFile::read();
        let registry_mode = project.registry.as_ref().map(|r| r.mode.clone()).unwrap_or_else(|| "release".to_string());
        for (pkg, ver) in &project.dependencies {
            bar.set_status(format!("fetching {}", pkg));
            if let Some(entry) = registry.find(pkg) {
                let spec = crate::config::DepSpec::parse(ver);
                download_package(entry, &pkg_cache, &spec, &registry_mode).ok();
                lock.lock(pkg, ver, entry.git.clone(), None);
            } else {
                std::fs::write(pkg_cache.join(format!("{}.h#", pkg)),
                               format!(";; stub: {} v{}\n", pkg, ver)).ok();
                               lock.lock(pkg, ver, None, None);
            }
            bar.inc(1);
        }
        lock.write();
        bar.finish(&format!("{} H# package(s) installed", project.dependencies.len()));
    }

    if let Some(py) = &project.python {
        println!();
        println!("  {} Python {} packages...", "Setting up".cyan(), py.version.yellow());
        let py_cache = cache.join("pyenv");
        std::fs::create_dir_all(&py_cache)?;
        match setup_python_deps(py, &py_cache) {
            Ok(_)  => println!("  {} Python env ready", "checkmark".green().bold()),
            Err(e) => eprintln!("  {} Python setup: {}", "warn:".yellow(), e),
        }
    }

    println!();
    println!("  {} packages ready: {}", "checkmark".green().bold(), cache.display().to_string().cyan());
    Ok(())
}

fn cmd_update() -> anyhow::Result<()> {
    print_header();
    println!("  {} checking for updates...", "bytes".cyan().bold());
    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project  = BytesProject::load(&toml_path)?;
    let registry = Registry::fetch();
    let mut lock = LockFile::read();
    let mut updated = 0usize;

    for (pkg, current_ver) in &project.dependencies {
        if let Some(entry) = registry.find(pkg) {
            let latest = &entry.latest;
            if latest != current_ver && latest != "latest" {
                println!("  {} {}  {} -> {}", "up".cyan().bold(), pkg.cyan(),
                         current_ver.yellow(), latest.green());
                lock.lock(pkg, latest, entry.git.clone(), None);
                updated += 1;
            } else {
                println!("  {} {} {}", "ok".green(), pkg, current_ver.dimmed());
            }
        }
    }
    lock.write();
    if updated > 0 {
        println!("\n  {} {} package(s) updated. Run `bytes install`.", "checkmark".green().bold(), updated);
    } else {
        println!("\n  {} All packages up to date.", "checkmark".green().bold());
    }
    Ok(())
}

fn cmd_list() -> anyhow::Result<()> {
    let toml_path = BytesProject::find()
    .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
    let project = BytesProject::load(&toml_path)?;
    println!("  {} {}", "Project:".bold(), project.package.name.cyan());
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
        for pkg in &py.packages { println!("  {:<28} {}", pkg.cyan(), "pip".dimmed()); }
    }
    Ok(())
}

fn cmd_workspace(sub: &str, extra: &[String], release: bool, verbose: bool) -> anyhow::Result<()> {
    match sub {
        "build" => cmd_build(extra, release, verbose)?,
        _ => {
            let toml_path = BytesProject::find()
            .ok_or_else(|| anyhow::anyhow!("No bytes.toml or bytes.hk found"))?;
            let project = BytesProject::load(&toml_path)?;
            if let Some(ws) = &project.workspace {
                println!("  {} {}", "Workspace:".bold(), project.package.name.cyan());
                println!("  {} {}", "Mode:    ".dimmed(), ws.mode.as_deref().unwrap_or("standard"));
                println!("  {} {}", "Members: ".dimmed(), ws.members.len());
                println!();
                for m in &ws.members {
                    let lang = ws.languages.get(m).map(|s| s.as_str()).unwrap_or("h#");
                    println!("  {} {} ({})", "dot".dimmed(), m.cyan(), lang.yellow());
                }
            } else {
                println!("  {}", "Not a workspace project.".dimmed());
            }
        }
    }
    Ok(())
}

fn cmd_check(extra: &[String], _verbose: bool) -> anyhow::Result<()> {
    let files: Vec<String> = if extra.is_empty() {
        walkdir::WalkDir::new(".").max_depth(5).into_iter().flatten()
        .filter(|e| {
            e.file_type().is_file()
            && e.path().extension().map(|x| x == "h#" || x == "hsp").unwrap_or(false)
            && !e.path().starts_with("./build")
        })
        .map(|e| e.path().display().to_string())
        .collect()
    } else { extra.to_vec() };

    println!("  {} {} file(s)", "Checking:".cyan().bold(), files.len());
    let mut errors = 0usize;
    for f in &files {
        let ok = std::process::Command::new("hsharp").args(["check", f])
        .status().map(|s| s.success()).unwrap_or(false);
        if ok { println!("  {} {}", "ok".green(), f.dimmed()); }
        else  { println!("  {} {}", "fail".red(), f); errors += 1; }
    }
    if errors > 0 { std::process::exit(1); }
    Ok(())
}

fn cmd_clean(everything: bool) -> anyhow::Result<()> {
    let session = ram_cache_dir();
    if session.exists() {
        std::fs::remove_dir_all(&session)?;
        println!("  {} cleaned RAM session: {}", "ok".green().bold(), session.display().to_string().cyan());
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
            println!("  {} {} session(s) cleaned", "ok".green().bold(), cleaned);
        }
    }
    if everything {
        if std::path::Path::new("build").exists() {
            std::fs::remove_dir_all("build")?;
            println!("  {} cleaned build/", "ok".green().bold());
        }
        if std::path::Path::new(".cache").exists() {
            std::fs::remove_dir_all(".cache")?;
            println!("  {} cleaned .cache/", "ok".green().bold());
        }
    }
    if std::path::Path::new(".bytes-cache").exists() {
        std::fs::remove_dir_all(".bytes-cache")?;
        println!("  {} cleaned .bytes-cache/", "ok".green().bold());
    }
    println!("  {}", "All clean.".green());
    Ok(())
}

fn cmd_info(pkg: &str) -> anyhow::Result<()> {
    let reg = Registry::fetch();
    match reg.find(pkg) {
        None    => eprintln!("  {} `{}` not found", "error".red(), pkg),
        Some(e) => {
            println!("  {} {}", "Package:".bold(), e.name.cyan().bold());
            println!("  {} {}", "Latest: ".bold(), e.latest.green());
            if let Some(d) = &e.description { println!("  {} {}", "Desc:  ".bold(), d); }
            if let Some(g) = &e.git         { println!("  {} {}", "Source:".dimmed(), g.cyan()); }
            println!("  {} {}", "Install:".dimmed(), format!("bytes add {}", e.name).cyan());
        }
    }
    Ok(())
}

fn cmd_search(q: &str) -> anyhow::Result<()> {
    print_header();
    let reg = Registry::fetch();
    let results: Vec<_> = reg.packages.iter()
    .filter(|p| p.name.contains(q) || p.description.as_deref().unwrap_or("").contains(q))
    .collect();
    println!("  {:<25} {}", "PACKAGE".bold(), "SOURCE".bold());
    println!("  {}", "─".repeat(50).dimmed());
    for p in &results {
        let src = p.git.as_deref().unwrap_or("Bytes-Repository");
        println!("  {:<25} {}", p.name.cyan(), src.dimmed());
    }
    if results.is_empty() { println!("  {}", "No packages found.".dimmed()); }
    else { println!("\n  {} {} result(s)", "Found:".dimmed(), results.len()); }
    Ok(())
}

fn cmd_python(pkg: &str, ver: Option<&str>) -> anyhow::Result<()> {
    print_header();
    println!("  {} Python package: {}", "Installing".cyan().bold(), pkg.yellow());
    let cache = ram_cache_dir().join("pyenv");
    std::fs::create_dir_all(&cache)?;
    let env = PythonEnv::setup("3", &cache)?;
    env.install_package(pkg, ver)?;
    println!("  {} use: {}", "Done!".green().bold(),
             format!("use \"python -> {}\" from \"{}\"", pkg, pkg).cyan());
    Ok(())
}

fn cmd_cache_info() -> anyhow::Result<()> {
    println!("  {} {}", "bytes libs:".bold(), hackeros_libs_base().display().to_string().cyan());
    println!("  {}", "type: RAM-backed (tmpfs), auto-cleared on reboot".dimmed());
    let session = ram_cache_dir();
    if session.exists() {
        let size = walkdir_size(&session);
        println!("  {} {} KB (session {})", "size:".dimmed(), size / 1024, std::process::id());
    } else {
        println!("  {} (no active session)", "size:".dimmed());
    }
    println!();
    let vcache = ViraCache::open();
    println!("  {} {}", "vira cache:".bold(), hackeros_cache_base().display().to_string().cyan());
    println!("  {} {:.1} MB", "size:".dimmed(), vcache.total_size_mb());
    let pkgs = vcache.list();
    if !pkgs.is_empty() {
        println!();
        println!("  {:<28} {}", "PACKAGE".bold(), "VERSION".bold());
        println!("  {}", "─".repeat(38).dimmed());
        for (n, v) in &pkgs { println!("  {:<28} {}", n.cyan(), v.green()); }
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
    println!("  {}", "Usage: bytes new-workspace myws app:h# lib:rust server:go".dimmed());
    Ok(())
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn walkdir_size(path: &std::path::Path) -> u64 {
    let mut total = 0u64;
    if let Ok(entries) = std::fs::read_dir(path) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir()                    { total += walkdir_size(&p); }
            else if let Ok(m) = p.metadata() { total += m.len(); }
        }
    }
    total
}

fn print_header() {
    println!();
    println!("  {}  H# Package Manager", "bytes".cyan().bold());
    println!("  {}  build • run • deps • workspaces", format!("v{}", VERSION).dimmed());
    println!();
}

fn print_version() {
    println!("bytes {} — H# Package Manager", VERSION);
}

fn print_help() {
    print_header();
    println!("  {}", "USAGE:".bold());
    println!("    {} <command> [options]", "bytes".cyan());
    println!();
    println!("  {}", "PROJECT:".bold());
    println!("    {}  Create H# project (fmt: hk|toml)", "new <name> [fmt]".cyan());
    println!("    {}  Create multi-language workspace",   "new-workspace <name> [m:lang ...]".cyan());
    println!("    {}  Run with JIT (RAM cache)",           "run [file.h#]".cyan());
    println!("    {}  Build project or workspace",         "build [--release]".cyan());
    println!();
    println!("  {}", "PACKAGES:".bold());
    println!("    {}  Add H# dependency",             "add <pkg> [ver]".cyan());
    println!("    {}  Remove dependency",             "remove <pkg>".cyan());
    println!("    {}  Install all deps from manifest","install".cyan());
    println!("    {}  Update all packages",           "update".cyan());
    println!("    {}  List installed packages",       "list".cyan());
    println!("    {}  Search package registry",       "search <query>".cyan());
    println!("    {}  Show package info",             "info <pkg>".cyan());
    println!("    {}  Install Python package",        "python <pkg>".cyan());
    println!();
    println!("  {}", "TOOLING (v0.7):".bold());
    println!("    {}  Run #[test] functions",         "test [file.h#]".cyan());
    println!("    {}  Format H# source files",        "fmt [file.h#]".cyan());
    println!("    {}  Generate docs from /// comments","doc [dir]".cyan());
    println!("    {}  Check syntax & types",          "check [files...]".cyan());
    println!();
    println!("  {}", "UTILITY:".bold());
    println!("    {}  Show RAM cache info",           "cache".cyan());
    println!("    {}  Clear RAM cache",               "clean [--everything]".cyan());
    println!("    {}  Show supported languages",      "langs".cyan());
    println!();
    println!("  {}", "OPTIONS:".bold());
    println!("    {}  Execution tier: interpreter|bytecode|jit", "--tier <t>".cyan());
    println!("    {}  Release build",   "--release, -r".cyan());
    println!("    {}  Verbose output",  "--verbose, -v".cyan());
    println!();
    println!("  {}", "REGISTRY:".bold());
    println!("    {}", "https://github.com/Bytes-Repository/repository/blob/main/index.json".dimmed());
}

fn default_main(name: &str) -> String {
    format!(r#"using "2026"
        ;;  {name} — H# project
        ;;  Run:   bytes run
        ;;  Build: bytes build --release
        ;;  Test:  bytes test
        ;;  Docs:  bytes doc

        fn fib(n: int) -> int is
        if n <= 1 is
            return n
            end
            return fib(n - 1) + fib(n - 2)
        end

        fn main() is
        write(bold("Hello from H# v0.7!"))
        write("Project: {name}")

        let mut sum: int = 0
        for i in 1..=10 is
            sum += i
            end
            write("Sum 1..10 = " + to_string(sum))

        match sum is
        55 => write("correct!")
        _  => write("unexpected")
        end
        end
        "#, name = name)
}
