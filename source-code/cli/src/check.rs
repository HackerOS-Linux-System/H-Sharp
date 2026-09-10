use colored::Colorize;
use std::path::PathBuf;
use walkdir::WalkDir;

pub fn run(file: Option<PathBuf>) {
    let sources: Vec<PathBuf> = if let Some(f) = file {
        vec![f]
    } else {
        let exts = ["h#", "hsp", "h-sharp"];
        WalkDir::new(".").max_depth(5).into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file()
        && e.path().extension().and_then(|s| s.to_str()).map(|x| exts.contains(&x)).unwrap_or(false)
        && !e.path().starts_with("./build"))
        .map(|e| e.path().to_path_buf())
        .collect()
    };

    if sources.is_empty() {
        eprintln!("{} no .h# files found", "Error:".red().bold());
        std::process::exit(1);
    }

    println!("{} {} file(s)\n", "Checking:".cyan().bold(), sources.len());
    let mut total_errors = 0usize;

    for src_path in &sources {
        let source = match std::fs::read_to_string(src_path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{} {}: {}", "Error:".red().bold(), src_path.display(), e);
                total_errors += 1;
                continue;
            }
        };
        let result = hsharp_parser::parse(&source, &src_path.display().to_string());
        if result.has_errors() {
            total_errors += result.errors.len();
            eprint!("{}", result.render_errors());
        } else {
            let mut module = result.module;
            let mut resolver = hsharp_compiler::modules::ModuleResolver::new(src_path);
            let entry_dir = src_path.parent().unwrap_or_else(|| std::path::Path::new("."));
            match resolver.expand_program(&module, entry_dir) {
                Ok(items) => module.items = items,
                Err(e) => {
                    eprintln!("{} {}: {}", "Error:".red().bold(), src_path.display(), e);
                    total_errors += 1;
                    continue;
                }
            }
            // check_module now returns Vec<Diagnostic> (not Result) — collect all errors
            let mut tc = hsharp_compiler::typechecker::TypeChecker::new();
            let mut diags = tc.check_module(&module);
            // `hsharp check` previously only ran the plain typechecker,
            // never `features::check_module_features` — meaning it could
            // report "no errors found" for code that would then fail to
            // *build* (a closure literal, a struct passed by value across
            // `extern`, `await` outside an async runtime, ...), since
            // those are backend-capability errors, not type errors. Since
            // `check` exists specifically to catch what `build` would
            // reject before spending time on a full compile, it needs the
            // same feature-support pass `hsharp build` runs (see
            // `compiler/src/lib.rs`'s own compile pipeline).
            diags.extend(hsharp_compiler::features::check_module_features(&module, hsharp_compiler::builtins_registry::Backend::Llvm));
            let errs: Vec<_> = diags.iter().filter(|d| d.severity == hsharp_compiler::Severity::Error).collect();
            if errs.is_empty() {
                println!("  {} {}", "✓".green(), src_path.display());
            } else {
                total_errors += errs.len();
                hsharp_compiler::print_diagnostics(&diags, &source, &src_path.display().to_string());
                println!("  {} {}  ({} error(s))", "✗".red(), src_path.display(), errs.len());
            }
        }
    }

    println!();
    if total_errors == 0 {
        println!("{} No errors found.", "✓".green().bold());
    } else {
        println!("{} Found {} error(s).", "✗".red().bold(), total_errors);
        std::process::exit(1);
    }
}

/// Called when specific files are passed on CLI
pub fn run_multi(files: Vec<std::path::PathBuf>) {
    if files.is_empty() {
        run(None);
    } else if files.len() == 1 {
        run(Some(files.into_iter().next().unwrap()));
    } else {
        println!("{} {} file(s)\n", "Checking:".cyan().bold(), files.len());
        let mut total_errors = 0usize;
        for src_path in &files {
            let source = match std::fs::read_to_string(src_path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{} {}: {}", "Error:".red().bold(), src_path.display(), e);
                    total_errors += 1;
                    continue;
                }
            };
            let result = hsharp_parser::parse(&source, &src_path.display().to_string());
            if result.has_errors() {
                total_errors += result.errors.len();
                eprint!("{}", result.render_errors());
            } else {
                let mut module = result.module;
                let mut resolver = hsharp_compiler::modules::ModuleResolver::new(src_path);
                let entry_dir = src_path.parent().unwrap_or_else(|| std::path::Path::new("."));
                match resolver.expand_program(&module, entry_dir) {
                    Ok(items) => module.items = items,
                    Err(e) => {
                        eprintln!("{} {}: {}", "Error:".red().bold(), src_path.display(), e);
                        total_errors += 1;
                        continue;
                    }
                }
                let mut tc = hsharp_compiler::typechecker::TypeChecker::new();
                let mut diags = tc.check_module(&module);
                diags.extend(hsharp_compiler::features::check_module_features(&module, hsharp_compiler::builtins_registry::Backend::Llvm));
                let errs: Vec<_> = diags.iter().filter(|d| d.severity == hsharp_compiler::Severity::Error).collect();
                if errs.is_empty() {
                    println!("  {} {}", "✓".green().bold(), src_path.display().to_string().dimmed());
                } else {
                    total_errors += errs.len();
                    hsharp_compiler::print_diagnostics(&diags, &source, &src_path.display().to_string());
                }
            }
        }
        println!();
        if total_errors == 0 {
            println!("{}", "✓ No errors found.".green().bold());
        } else {
            eprintln!("{} Found {}.", "✗".red().bold(), format!("{} error(s)", total_errors).red());
            std::process::exit(1);
        }
    }
}
