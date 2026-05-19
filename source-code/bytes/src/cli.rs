use colored::*;
use crate::config::{BytesProject, default_bytes_toml, ram_cache_dir};
use crate::jit::BytesRunner;
use crate::registry::Registry;
use crate::python_interop::{resolve_python_import, setup_python_deps};
use crate::progress::{BytesBar, BarTheme};

const VERSION: &str = "0.1.0";

pub fn run() -> anyhow::Result<()> {
    let mut args_raw: Vec<String> = std::env::args().skip(1).collect();
    let mut parser = lexopt::Parser::from_env();

    let mut cmd    = String::new();
    let mut extra  = Vec::<String>::new();
    let mut verbose = false;
    let mut tier   = String::new();

    loop {
        match parser.next()? {
            Some(lexopt::Arg::Long("version")) | Some(lexopt::Arg::Short('V')) => {
                print_version(); return Ok(());
            }
            Some(lexopt::Arg::Long("help")) | Some(lexopt::Arg::Short('h')) => {
                print_help(); return Ok(());
            }
            Some(lexopt::Arg::Long("verbose")) | Some(lexopt::Arg::Short('v')) => verbose = true,
            Some(lexopt::Arg::Long("tier")) | Some(lexopt::Arg::Short('t')) => {
                tier = parser.value()?.to_str().unwrap_or("jit").to_string();
            }
            Some(lexopt::Arg::Value(v)) => {
                let s = v.to_str().unwrap_or("").to_string();
                if cmd.is_empty() { cmd = s; } else { extra.push(s); }
            }
            Some(lexopt::Arg::Long(u)) => extra.push(format!("--{}", u)),
            Some(lexopt::Arg::Short(c)) => extra.push(format!("-{}", c)),
            None => break,
        }
    }

    if cmd.is_empty() { print_help(); return Ok(()); }

    match cmd.as_str() {
        "new" => {
            let name = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes new <name>"))?;
            cmd_new(name)?;
        }
        "run" => {
            // bytes run [file.h#] [-- args...]
            let file = extra.first().cloned()
                .or_else(|| BytesProject::find().map(|_| {
                    BytesProject::load(&BytesProject::find().unwrap())
                        .ok().map(|p| p.entry_file()).unwrap_or_else(|| "src/main.h#".into())
                }))
                .unwrap_or_else(|| "src/main.h#".into());

            let run_args = extra.iter().skip(1).cloned().collect::<Vec<_>>();
            cmd_run(&file, &run_args, verbose, &tier)?;
        }
        "add" => {
            let pkg = extra.first().ok_or_else(|| anyhow::anyhow!("Usage: bytes add <package>"))?;
            let ver = extra.get(1).map(|s| s.as_str()).unwrap_or("latest");
            cmd_add(pkg, ver)?;
        }
        "install" => {
            cmd_install(verbose)?;
        }
        "clean" => {
            cmd_clean()?;
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
        _ => {
            // Treat unknown as file to run
            if extra.is_empty() && (cmd.ends_with(".h#") || cmd.ends_with(".hsp")) {
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

fn cmd_new(name: &str) -> anyhow::Result<()> {
    print_header();
    let root = std::path::Path::new(name);
    if root.exists() { anyhow::bail!("directory `{}` already exists", name); }

    std::fs::create_dir_all(root.join("src"))?;
    std::fs::write(root.join("bytes.toml"), default_bytes_toml(name))?;
    std::fs::write(root.join(".gitignore"), ".bytes-cache/\n*.jit\n*.h#bc\n")?;
    std::fs::write(root.join("src").join("main.h#"), default_main(name))?;

    println!("  {} {} (bytes project)", "Created:".green().bold(), name.cyan());
    println!("  {} {}", "Entry:  ".dimmed(), "src/main.h#".cyan());
    println!("  {} {}", "Config: ".dimmed(), "bytes.toml".cyan());
    println!();
    println!("  {} {}", "Next:".bold(), format!("cd {} && bytes run", name).dimmed());
    println!("  {} {}", "      ".dimmed(), "bytes add scanner          # H# package".dimmed());
    println!("  {} {}", "      ".dimmed(), "bytes python numpy          # Python package".dimmed());
    Ok(())
}

fn cmd_run(file: &str, run_args: &[String], verbose: bool, tier: &str) -> anyhow::Result<()> {
    // Check file exists
    if !std::path::Path::new(file).exists() {
        anyhow::bail!("file not found: {}", file);
    }

    // Load project config if bytes.toml present
    let mut project = BytesProject::find()
        .and_then(|p| BytesProject::load(&p).ok())
        .unwrap_or_default();

    // Override tier if given on CLI
    if !tier.is_empty() {
        project.jit.get_or_insert_with(Default::default).tier = Some(tier.to_string());
    }

    // Setup Python deps if configured
    if let Some(py_config) = &project.python {
        let cache = ram_cache_dir().join("pyenv");
        std::fs::create_dir_all(&cache)?;
        setup_python_deps(py_config, &cache)?;
    }

    let mut runner = BytesRunner::new(project, verbose);
    let exit_code  = runner.run(file, run_args)?;
    std::process::exit(exit_code);
}

fn cmd_add(pkg: &str, ver: &str) -> anyhow::Result<()> {
    print_header();

    // Check if it's a Python package
    if pkg.starts_with("python:") || pkg.starts_with("py:") {
        let name = pkg.trim_start_matches("python:").trim_start_matches("py:");
        return cmd_python(name, Some(ver));
    }

    println!("  {} {} to bytes.toml...", "Adding".cyan().bold(), pkg.yellow());

    // Update bytes.toml
    if let Some(toml_path) = BytesProject::find() {
        let mut src = std::fs::read_to_string(&toml_path)?;
        let dep_line = format!("\n{} = \"{}\"", pkg, ver);
        if src.contains("[dependencies]") {
            // Find end of [dependencies] section and insert
            if let Some(idx) = src.find("[dependencies]") {
                let section_end = src[idx+14..].find("\n[").map(|i| i + idx + 14).unwrap_or(src.len());
                src.insert_str(section_end, &dep_line);
            }
        } else {
            src.push_str(&format!("\n[dependencies]{}\n", dep_line));
        }
        std::fs::write(&toml_path, src)?;
    }

    // Download to RAM cache
    let cache = ram_cache_dir().join("packages");
    std::fs::create_dir_all(&cache)?;

    let mut bar = BytesBar::new(2, BarTheme::Default);
    bar.set_status(format!("resolving {}", pkg));
    bar.inc(1);

    let registry = Registry::fetch();
    let url = registry.find(pkg)
        .and_then(|e| e.git.as_deref())
        .map(|g| g.to_string())
        .unwrap_or_else(|| format!("https://github.com/vira-io/{}", pkg));

    // Write placeholder to RAM cache
    let pkg_file = cache.join(format!("{}.h#", pkg));
    std::fs::write(&pkg_file, format!(";; bytes pkg: {} v{}\n;; source: {}\n", pkg, ver, url))?;

    bar.set_status(format!("cached {}", pkg));
    bar.inc(1);
    bar.finish(&format!("added {}@{} → RAM cache", pkg.cyan(), ver.green()));
    println!("  {} {}", "use:".dimmed(), format!("use \"vira -> {}\" from \"{}\"", pkg, pkg).cyan());
    Ok(())
}

fn cmd_install(verbose: bool) -> anyhow::Result<()> {
    print_header();
    let toml_path = BytesProject::find()
        .ok_or_else(|| anyhow::anyhow!("No bytes.toml found in current directory"))?;
    let project = BytesProject::load(&toml_path)?;

    if project.dependencies.is_empty() && project.python.is_none() {
        println!("  {}", "Nothing to install.".dimmed());
        return Ok(());
    }

    println!("  {} {}", "Installing for:".cyan().bold(), project.package.name.yellow());
    println!("  {} /dev/shm (RAM — cleared on reboot)", "Cache:".dimmed());
    println!();

    let cache = ram_cache_dir();
    std::fs::create_dir_all(&cache)?;

    // Install H# deps
    if !project.dependencies.is_empty() {
        let total = project.dependencies.len() as u64;
        let mut bar = BytesBar::new(total, BarTheme::Default);
        let registry = Registry::fetch();

        for (pkg, ver) in &project.dependencies {
            bar.set_status(format!("fetching {}", pkg));
            let pkg_cache = cache.join("packages");
            std::fs::create_dir_all(&pkg_cache)?;
            let url = registry.find(pkg)
                .and_then(|e| e.git.as_deref())
                .map(|g| g.to_string())
                .unwrap_or_else(|| format!("https://github.com/vira-io/{}", pkg));
            std::fs::write(pkg_cache.join(format!("{}.h#", pkg)),
                format!(";; bytes pkg: {} v{}\n;; src: {}\n", pkg, ver, url))?;
            bar.inc(1);
        }
        bar.finish(&format!("{} H# package(s) cached in RAM", project.dependencies.len()));
    }

    // Install Python deps
    if let Some(py) = &project.python {
        println!();
        println!("  {} Python {} packages...", "Setting up".cyan(), py.version.yellow());
        let py_cache = cache.join("pyenv");
        std::fs::create_dir_all(&py_cache)?;
        match setup_python_deps(py, &py_cache) {
            Ok(_)  => println!("  {} Python env ready", "✓".green().bold()),
            Err(e) => eprintln!("  {} Python setup: {}", "warn:".yellow(), e),
        }
    }

    println!();
    println!("  {} all packages in RAM: {}", "✓".green().bold(), cache.display().to_string().cyan());
    println!("  {} bytes run", "Run:".dimmed());
    Ok(())
}

fn cmd_clean() -> anyhow::Result<()> {
    use crate::isolation::{hackeros_libs_base, ViraCache};
    // Clean session dir
    let session = ram_cache_dir();
    if session.exists() {
        std::fs::remove_dir_all(&session)?;
        println!("  {} cleaned session: {}", "✓".green().bold(), session.display().to_string().cyan());
    }
    // Clean ALL bytes sessions (libs base)
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
        println!("  {} {} session(s) cleaned from {}", "✓".green().bold(), cleaned, libs.display().to_string().cyan());
    } else {
        println!("  {}", "Nothing to clean.".dimmed());
    }
    if std::path::Path::new(".bytes-cache").exists() {
        std::fs::remove_dir_all(".bytes-cache")?;
        println!("  {} cleaned .bytes-cache/", "✓".green().bold());
    }
    Ok(())
}

fn cmd_info(pkg: &str) -> anyhow::Result<()> {
    let reg = Registry::fetch();
    match reg.find(pkg) {
        None    => eprintln!("  {} `{}` not found", "✗".red(), pkg),
        Some(e) => {
            println!("  {} {}", "Package:".bold(), e.name.cyan().bold());
            println!("  {} {}", "Latest: ".bold(), e.latest.green());
            if let Some(d) = &e.description { println!("  {} {}", "Desc:".bold(), d); }
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
    println!("  {:<25} {}", "PACKAGE".bold(), "VERSION".bold());
    println!("  {}", "─".repeat(40).dimmed());
    for p in &results {
        println!("  {:<25} {}", p.name.cyan(), p.latest.green());
    }
    if results.is_empty() { println!("  {}", "No packages found.".dimmed()); }
    Ok(())
}

fn cmd_python(pkg: &str, ver: Option<&str>) -> anyhow::Result<()> {
    use crate::python_interop::PythonEnv;
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
    use crate::isolation::{hackeros_libs_base, hackeros_cache_base, ViraCache};
    println!("  {} {}", "bytes libs:".bold(), hackeros_libs_base().display().to_string().cyan());
    println!("  {} RAM-backed (tmpfs mount), auto-cleared on reboot", "type:".dimmed());
    let session = ram_cache_dir();
    if session.exists() {
        let size: u64 = walkdir(&session);
        println!("  {} {} KB (session {})", "size:".dimmed(), size / 1024, std::process::id());
    } else {
        println!("  {} (no active session)", "size:".dimmed());
    }
    println!();
    let vcache = ViraCache::open();
    println!("  {} {}", "vira cache:".bold(), hackeros_cache_base().display().to_string().cyan());
    println!("  {} persistent, isolated per-package", "type:".dimmed());
    println!("  {} {:.1} MB", "size:".dimmed(), vcache.total_size_mb());
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

fn walkdir(path: &std::path::Path) -> u64 {
    let mut total = 0u64;
    if let Ok(entries) = std::fs::read_dir(path) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() { total += walkdir(&p); }
            else if let Ok(m) = std::fs::metadata(&p) { total += m.len(); }
        }
    }
    total
}

// ── UI ────────────────────────────────────────────────────────────────────────

fn print_header() {
    println!();
    println!("  {}  H# RAM-JIT Package Manager", "bytes".cyan().bold());
    println!("  {}  libs: ~/.hackeros/H#/libs/ (tmpfs, RAM-backed)", "v0.1.0".dimmed());
    println!();
}

fn print_version() {
    println!("bytes {} (H# RAM-JIT PM)", VERSION);
}

fn print_help() {
    print_header();
    println!("  {}", "USAGE:".bold());
    println!("    {} <command> [options]", "bytes".cyan());
    println!();
    println!("  {}", "COMMANDS:".bold());
    println!("    {}  Create new bytes project", "new <name>".cyan());
    println!("    {}  Run with JIT (RAM cache)", "run [file.h#]".cyan());
    println!("    {}  Add H# dependency", "add <pkg> [ver]".cyan());
    println!("    {}  Install all deps from bytes.toml", "install".cyan());
    println!("    {}  Clear RAM cache (/dev/shm)", "clean".cyan());
    println!("    {}  Search package registry", "search <query>".cyan());
    println!("    {}  Show package info", "info <pkg>".cyan());
    println!("    {}  Install Python package into RAM venv", "python <pkg>".cyan());
    println!("    {}  Show RAM cache info", "cache".cyan());
    println!();
    println!("  {}", "OPTIONS:".bold());
    println!("    {}  Execution tier: interpreter|bytecode|jit", "--tier <t>".cyan());
    println!("    {}  Verbose output", "--verbose, -v".cyan());
    println!();
    println!("  {}", "EXAMPLES:".bold());
    println!("    {}", "bytes new myapp && cd myapp && bytes run".dimmed());
    println!("    {}", "bytes add scanner              # H# package".dimmed());
    println!("    {}", "bytes python numpy             # Python package".dimmed());
    println!("    {}", "bytes run --tier bytecode      # skip JIT".dimmed());
    println!("    {}", "bytes run --tier interpreter   # pure interpreter".dimmed());
    println!("    {}", "bytes clean                    # clear ~/.hackeros/H#/libs/".dimmed());
    println!();
    println!("  {}", "ISOLATION:".bold());
    println!("    {}", "bytes: tmpfs in ~/.hackeros/H#/libs/ (vanishes on reboot)".dimmed());
    println!("    {}", "vira:  persistent ~/.hackeros/H#/.cache/ (isolated per-pkg)".dimmed());
    println!("    {}", "sys deps: extracted via dpkg-deb (no system pollution)".dimmed());
    println!();
    println!("  {}", "DIFFERENCES FROM vira:".bold());
    println!("    {}", "vira   → compilation → persistent binary in build/".dimmed());
    println!("    {}", "bytes  → JIT in RAM  → no persistent artifacts".dimmed());
    println!("    {}", "bytes.toml (TOML) vs vira.hcl (HCL)".dimmed());
    println!();
    println!("  {}", "PYTHON INTEROP (bytes.toml):".bold());
    println!("    {}", "[python]".cyan());
    println!("    {}", "version = \"3.13\"".dimmed());
    println!("    {}", "packages = [\"numpy\", \"cryptography\"]".dimmed());
    println!();
    println!("    {}", "Then in H#:".bold());
    println!("    {}", "use \"python -> numpy\" from \"np\"".cyan());
}

fn default_main(name: &str) -> String {
    format!(r#";;  {name} — H# bytes project
;;  Run: bytes run
;;  JIT cache: /dev/shm (RAM — cleared on reboot)

fn greet(who: string) -> string is
    return "Hello, " + who + " from H#!"
end

fn fib(n: int) -> int is
    if n <= 1 is
        return n
    end
    return fib(n - 1) + fib(n - 2)
end

fn main() is
    write(greet("HackerOS"))

    ;; bytes JIT will compile fib() after {thresh} calls
    let mut i: int = 0
    while i < 5 is
        write("fib(" + to_string(i) + ") = " + to_string(fib(i)))
        i += 1
    end
end
"#, name = name, thresh = 100)
}
