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
            let mut tc = hsharp_compiler::typechecker::TypeChecker::new();
            match tc.check_module(&result.module) {
                Ok(()) => println!("  {} {}", "✓".green(), src_path.display()),
                Err(e) => {
                    total_errors += 1;
                    println!("  {} {}  →  {}", "✗".red(), src_path.display(), e);
                }
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

/// Check multiple files — called when specific files are passed on CLI
pub fn run_multi(files: Vec<std::path::PathBuf>) {
    if files.is_empty() {
        // No files specified → check all
        run(None);
    } else if files.len() == 1 {
        run(Some(files.into_iter().next().unwrap()));
    } else {
        // Multiple files
        use colored::Colorize;
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
                println!("  {} {}", "✓".green().bold(), src_path.display().to_string().dimmed());
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

fn print_header() {
    use colored::Colorize;
    println!("  {} {}  —  HackerOS-first compiled language",
        "h#".cyan().bold(), "v0.2.0".cyan());
    println!();
}
