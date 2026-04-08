use colored::Colorize;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use std::path::PathBuf;
use std::time::Duration;
use walkdir::WalkDir;

use hsharp_compiler::{CompileOptions, TargetTriple};

pub fn run(files: Vec<std::path::PathBuf>, output: Option<String>, target: Option<String>, debug: bool, no_opt: bool) {
    println!("{}\n", "H# Build System".cyan().bold());

    let sources = if files.is_empty() {
        collect_sources(".")
    } else {
        files
    };
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

    // ── 3. Compile with Cranelift (native, no C transpilation) ─────────────
    let pb3 = mp.add(ProgressBar::new(modules.len() as u64));
    pb3.set_style(bar_style.clone());
    pb3.enable_steady_tick(Duration::from_millis(80));
    pb3.set_message("Cranelift codegen...");

    // out_name is already resolved (from output arg or project name)
    let resolved_out = format!("build/{}", out_name);
    let opts = CompileOptions {
        target: triple.clone(),
        optimize: !no_opt,
        static_link: true,
        debug_info: debug,
        output: resolved_out.clone(),
        use_cranelift: true,
    };

    // For single-file builds we compile directly
    // For multi-file projects, compile each and link together
    if modules.len() == 1 {
        let (src_path, _source, module) = &modules[0];
        pb3.set_message(format!("Compiling {} (Cranelift)...", src_path.file_name().unwrap_or_default().to_string_lossy()));

        let mut cg = hsharp_compiler::cranelift_codegen::CraneliftCodegen::new(&opts)
            .unwrap_or_else(|e| { eprintln!("{} Cranelift init: {}", "Error:".red().bold(), e); std::process::exit(1); });

        if let Err(e) = cg.declare_functions(module) {
            eprintln!("{} {}", "Error:".red().bold(), e);
            std::process::exit(1);
        }
        if let Err(e) = cg.compile_module(module) {
            eprintln!("{} {}", "Error:".red().bold(), e);
            std::process::exit(1);
        }
        pb3.finish_with_message(format!("{} Compiled (Cranelift)", "✓".green()));

        let pb4 = mp.add(ProgressBar::new_spinner());
        pb4.set_style(ProgressStyle::default_spinner().template("{spinner:.cyan.bold} {msg}").unwrap());
        pb4.enable_steady_tick(Duration::from_millis(80));
        pb4.set_message("Linking native binary...");

        match hsharp_compiler::cranelift_codegen::emit_module(cg, &resolved_out) {
            Ok(()) => pb4.finish_with_message(format!("{} Linked: {}", "✓".green(), opts.output)),
            Err(e) => {
                pb4.finish_and_clear();
                eprintln!("\n{} Link failed: {}", "✗".red().bold(), e);
                std::process::exit(1);
            }
        }
    } else {
        // Multi-file: compile each to object, then link
        let mut obj_paths = Vec::new();
        for (src_path, _source, module) in &modules {
            pb3.set_message(format!("Compiling {}...", src_path.file_name().unwrap_or_default().to_string_lossy()));
            let obj_out = format!("build/{}", src_path.file_stem().unwrap_or_default().to_string_lossy());
            let obj_opts = CompileOptions { output: obj_out.clone(), ..opts.clone() };

            let mut cg = hsharp_compiler::cranelift_codegen::CraneliftCodegen::new(&obj_opts)
                .unwrap_or_else(|e| { eprintln!("{} {}", "Error:".red().bold(), e); std::process::exit(1); });
            if let Err(e) = cg.declare_functions(module) { eprintln!("{} {}", "Error:".red().bold(), e); std::process::exit(1); }
            if let Err(e) = cg.compile_module(module)    { eprintln!("{} {}", "Error:".red().bold(), e); std::process::exit(1); }
            obj_paths.push(obj_out);
            pb3.inc(1);
        }
        pb3.finish_with_message(format!("{} Code generation done", "✓".green()));

        // Link all objects together
        let pb4 = mp.add(ProgressBar::new_spinner());
        pb4.set_style(ProgressStyle::default_spinner().template("{spinner:.cyan.bold} {msg}").unwrap());
        pb4.enable_steady_tick(Duration::from_millis(80));
        pb4.set_message("Linking...");

        let compiler = find_c_compiler().unwrap_or("cc");
        let out_bin = format!("{}{}", opts.output, triple.exe_suffix());
        let mut cmd = std::process::Command::new(compiler);
        for obj in &obj_paths { cmd.arg(format!("{}.o", obj)); }
        cmd.arg("-o").arg(&out_bin);
        if opts.static_link { cmd.arg("-static"); }

        match cmd.output() {
            Ok(o) if o.status.success() => pb4.finish_with_message(format!("{} Linked: {}", "✓".green(), out_bin)),
            Ok(o) => {
                pb4.finish_and_clear();
                eprintln!("\n{} Link failed:\n{}", "✗".red().bold(), String::from_utf8_lossy(&o.stderr));
                std::process::exit(1);
            }
            Err(e) => {
                pb4.finish_and_clear();
                eprintln!("\n{} {}", "✗".red().bold(), e);
                std::process::exit(1);
            }
        }
    }

    // Print summary
    let bin_name = format!("{}{}", resolved_out, triple.exe_suffix());

    println!();
    println!("{}", "─".repeat(52).dimmed());
    println!("  {} {}", "Binary: ".bold(), bin_name.cyan());
    println!("  {} {}", "Target: ".bold(), triple.llvm_triple);
    println!("  {} {}", "Backend:".bold(), "Cranelift (native)".green());
    println!("{}", "─".repeat(52).dimmed());
    println!("\n  {} Build complete!", "✓".green().bold());
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

