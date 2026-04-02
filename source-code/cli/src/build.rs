use colored::Colorize;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use std::path::PathBuf;
use std::time::Duration;
use walkdir::WalkDir;

use hsharp_compiler::{CompileOptions, TargetTriple};

pub fn run(output: Option<String>, target: Option<String>, debug: bool, no_opt: bool) {
    println!("{}\n", "H# Build System".cyan().bold());

    let sources = collect_sources(".");
    if sources.is_empty() {
        eprintln!("{} no .h#, .hsp, or .h-sharp files found", "Error:".red().bold());
        std::process::exit(1);
    }

    let project_name = detect_project_name();
    let out_name = output.unwrap_or_else(|| project_name.clone());

    let triple = if let Some(t) = target {
        match TargetTriple::from_str(&t) {
            Some(tt) => tt,
            None => {
                eprintln!("{} unknown target `{}`. Run `hsharp targets` to list them.", "Error:".red().bold(), t);
                std::process::exit(1);
            }
        }
    } else {
        TargetTriple::host()
    };

    println!("  {} {} → {}\n", "Building:".green().bold(), project_name, triple.llvm_triple);
    std::fs::create_dir_all("build").ok();

    let mp = MultiProgress::new();
    let bar_style = ProgressStyle::default_bar()
        .template("{spinner:.cyan.bold} [{bar:38.cyan/blue}] {pos:>3}/{len:3}  {msg}")
        .unwrap()
        .progress_chars("<#>-");

    // ── 1. Parse ─────────────────────────────────────────────────────────────
    let pb = mp.add(ProgressBar::new(sources.len() as u64));
    pb.set_style(bar_style.clone());
    pb.enable_steady_tick(Duration::from_millis(80));
    pb.set_message("Parsing source files...");

    let mut modules = Vec::new();
    let mut has_errors = false;

    for src_path in &sources {
        let source = match std::fs::read_to_string(src_path) {
            Ok(s) => s,
            Err(e) => {
                pb.finish_and_clear();
                eprintln!("{} cannot read `{}`: {}", "Error:".red().bold(), src_path.display(), e);
                std::process::exit(1);
            }
        };
        pb.set_message(format!("Parsing {}...", src_path.file_name().unwrap_or_default().to_string_lossy()));
        let result = hsharp_parser::parse(&source, &src_path.display().to_string());
        if result.has_errors() {
            pb.finish_and_clear();
            eprintln!("{}", result.render_errors());
            has_errors = true;
        } else {
            modules.push((src_path.clone(), source, result.module));
        }
        pb.inc(1);
    }
    pb.finish_with_message(format!("{} Parsed {} file(s)", "✓".green(), sources.len()));

    if has_errors {
        eprintln!("\n{} Build failed — syntax errors.", "✗".red().bold());
        std::process::exit(1);
    }

    // ── 2. Type check ─────────────────────────────────────────────────────────
    let pb2 = mp.add(ProgressBar::new(modules.len() as u64));
    pb2.set_style(bar_style.clone());
    pb2.enable_steady_tick(Duration::from_millis(80));
    pb2.set_message("Type checking...");

    for (src_path, _source, module) in &modules {
        pb2.set_message(format!("Checking {}...", src_path.file_name().unwrap_or_default().to_string_lossy()));
        let mut tc = hsharp_compiler::typechecker::TypeChecker::new();
        if let Err(e) = tc.check_module(module) {
            pb2.finish_and_clear();
            eprintln!("{} Type error in `{}`:\n  {}", "Error:".red().bold(), src_path.display(), e);
            has_errors = true;
        }
        pb2.inc(1);
    }
    pb2.finish_with_message(format!("{} Type check passed", "✓".green()));

    if has_errors {
        eprintln!("\n{} Build failed — type errors.", "✗".red().bold());
        std::process::exit(1);
    }

    // ── 3. Codegen ────────────────────────────────────────────────────────────
    let pb3 = mp.add(ProgressBar::new(modules.len() as u64));
    pb3.set_style(bar_style.clone());
    pb3.enable_steady_tick(Duration::from_millis(80));
    pb3.set_message("Generating C backend...");

    let opts = CompileOptions {
        target: triple.clone(),
        optimize: !no_opt,
        static_link: true,
        debug_info: debug,
        output: format!("build/{}", out_name),
    };

    let mut c_sources = Vec::new();
    for (src_path, _source, module) in &modules {
        pb3.set_message(format!("Compiling {}...", src_path.file_name().unwrap_or_default().to_string_lossy()));
        let mut cg = hsharp_compiler::codegen::Codegen::new(&src_path.display().to_string(), &opts);
        if let Err(e) = cg.compile_module(module) {
            pb3.finish_and_clear();
            eprintln!("{} Codegen error: {}", "Error:".red().bold(), e);
            has_errors = true;
            break;
        }
        let c_path = format!("build/{}.c", src_path.file_stem().unwrap_or_default().to_string_lossy());
        if let Err(e) = std::fs::write(&c_path, cg.get_c_source()) {
            pb3.finish_and_clear();
            eprintln!("{} Cannot write C source: {}", "Error:".red().bold(), e);
            has_errors = true;
            break;
        }
        c_sources.push(c_path);
        pb3.inc(1);
    }
    pb3.finish_with_message(format!("{} Code generation done", "✓".green()));

    if has_errors {
        std::process::exit(1);
    }

    // ── 4. Link ───────────────────────────────────────────────────────────────
    let pb4 = mp.add(ProgressBar::new_spinner());
    pb4.set_style(ProgressStyle::default_spinner().template("{spinner:.cyan.bold} {msg}").unwrap());
    pb4.enable_steady_tick(Duration::from_millis(80));
    let link_kind = if opts.static_link { "static" } else { "dynamic" };
    pb4.set_message(format!("Linking → {} binary...", link_kind));

    let out_bin = format!("{}{}", opts.output, triple.exe_suffix());
    match link_binaries(&c_sources, &out_bin, &opts) {
        Ok(()) => pb4.finish_with_message(format!("{} Linked: {}", "✓".green(), out_bin)),
        Err(e) => {
            pb4.finish_with_message(format!("{} Link failed: {}", "✗".red(), e));
            eprintln!("\n{} Build failed.", "✗".red().bold());
            for c in &c_sources { let _ = std::fs::remove_file(c); }
            std::process::exit(1);
        }
    }
    for c in &c_sources { let _ = std::fs::remove_file(c); }

    // Copy binary next to source
    let bin_name = format!("{}{}", out_name, triple.exe_suffix());
    let _ = std::fs::copy(&out_bin, &bin_name);

    println!();
    println!("{}", "─".repeat(52).dimmed());
    println!("  {} {}", "Binary: ".bold(), bin_name.cyan());
    println!("  {} {}", "Target: ".bold(), triple.llvm_triple);
    println!("  {} {}", "Linking:".bold(), link_kind);
    println!("{}", "─".repeat(52).dimmed());
    println!("\n  {} Build complete!", "✓".green().bold());
}

fn link_binaries(c_sources: &[String], output: &str, opts: &CompileOptions) -> Result<(), String> {
    let compiler = find_c_compiler().ok_or("no C compiler found (install gcc or clang)")?;
    let mut cmd = std::process::Command::new(&compiler);
    cmd.arg("-O2").args(c_sources).arg("-o").arg(output);
    if opts.static_link { cmd.arg("-static"); }
    if opts.debug_info  { cmd.arg("-g"); }
    let out = cmd.output().map_err(|e| format!("failed to run {}: {}", compiler, e))?;
    if !out.status.success() {
        return Err(format!("linker error:\n{}", String::from_utf8_lossy(&out.stderr)));
    }
    Ok(())
}

fn find_c_compiler() -> Option<&'static str> {
    for c in &["musl-gcc", "cc", "gcc", "clang"] {
        if std::process::Command::new("which").arg(c).output()
            .map(|o| o.status.success()).unwrap_or(false) {
            return Some(c);
        }
    }
    None
}

fn collect_sources(dir: &str) -> Vec<PathBuf> {
    let exts = ["h#", "hsp", "h-sharp"];
    WalkDir::new(dir).max_depth(5).into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file()
            && e.path().extension().and_then(|s| s.to_str()).map(|x| exts.contains(&x)).unwrap_or(false)
            && !e.path().starts_with("./build"))
        .map(|e| e.path().to_path_buf())
        .collect()
}

fn detect_project_name() -> String {
    if let Ok(content) = std::fs::read_to_string("h#.json") {
        if let Ok(json) = serde_json::from_str::<serde_json::Value>(&content) {
            if let Some(name) = json.get("name").and_then(|n| n.as_str()) {
                return name.to_string();
            }
        }
    }
    std::env::current_dir()
        .ok()
        .and_then(|p| p.file_name().map(|n| n.to_string_lossy().to_string()))
        .unwrap_or_else(|| "output".to_string())
}
