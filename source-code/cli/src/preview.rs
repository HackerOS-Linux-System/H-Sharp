use colored::Colorize;
use std::path::PathBuf;
use walkdir::WalkDir;

pub fn run(file: Option<PathBuf>) {
    let src_path = file.unwrap_or_else(|| {
        let exts = ["h#", "hsp", "h-sharp"];
        WalkDir::new(".").max_depth(3).into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file()
                && e.path().extension().and_then(|s| s.to_str()).map(|x| exts.contains(&x)).unwrap_or(false)
                && !e.path().starts_with("./build"))
            .map(|e| e.path().to_path_buf())
            .next()
            .unwrap_or_else(|| {
                eprintln!("{} no .h# files found", "Error:".red().bold());
                std::process::exit(1);
            })
    });

    let source = match std::fs::read_to_string(&src_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{} cannot read `{}`: {}", "Error:".red().bold(), src_path.display(), e);
            std::process::exit(1);
        }
    };

    println!("{} {} (interpreter mode)", "▶ Preview:".cyan().bold(), src_path.display());
    println!("{}", "─".repeat(50).dimmed());

    let result = hsharp_parser::parse(&source, &src_path.display().to_string());
    if result.has_errors() {
        eprintln!("{}", result.render_errors());
        std::process::exit(1);
    }

    let mut interp = hsharp_interpreter::Interpreter::new();
    match interp.run_module(&result.module) {
        Ok(()) => {
            println!("{}", "─".repeat(50).dimmed());
            println!("{} Preview completed.", "✓".green().bold());
        }
        Err(e) => {
            println!("{}", "─".repeat(50).dimmed());
            eprintln!("{} Runtime error: {}", "✗".red().bold(), e);
            std::process::exit(1);
        }
    }
}
