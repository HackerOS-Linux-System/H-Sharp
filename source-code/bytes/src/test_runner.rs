use colored::*;

pub fn run_tests(extra: &[String], verbose: bool) -> anyhow::Result<()> {
    println!();
    println!("  {}  H# Test Runner", "bytes test".cyan().bold());
    println!();

    let files = collect_test_files(extra);
    if files.is_empty() {
        println!("  {}", "No .h# files found to test.".dimmed());
        return Ok(());
    }

    let mut total_passed = 0usize;
    let mut total_failed = 0usize;
    let mut total_files  = 0usize;

    for file in &files {
        let (passed, failed) = run_file_tests(file, verbose)?;
        total_passed += passed;
        total_failed += failed;
        if passed + failed > 0 { total_files += 1; }
    }

    println!();
    println!("  {}", "─".repeat(48).dimmed());
    if total_failed == 0 {
        println!(
            "  {} {} test(s) passed in {} file(s)",
                 "✓".green().bold(), total_passed, total_files,
        );
    } else {
        println!(
            "  {} {}/{} passed, {} failed",
            "✗".red().bold(),
                 total_passed, total_passed + total_failed,
                 total_failed,
        );
        std::process::exit(1);
    }
    Ok(())
}

fn collect_test_files(extra: &[String]) -> Vec<String> {
    if !extra.is_empty() {
        return extra.iter().filter(|s| !s.starts_with("--")).cloned().collect();
    }
    walkdir::WalkDir::new(".")
    .max_depth(6).into_iter().flatten()
    .filter(|e| {
        let p   = e.path();
        let ext = p.extension().and_then(|x| x.to_str());
        let is_test = p.to_string_lossy().contains("test")
        || p.to_string_lossy().contains("spec")
        || ext == Some("h#") || ext == Some("hsp");
        e.file_type().is_file()
        && is_test
        && !p.starts_with("./build")
        && !p.starts_with("./.cache")
    })
    .map(|e| e.path().display().to_string())
    .collect()
}

fn run_file_tests(file: &str, verbose: bool) -> anyhow::Result<(usize, usize)> {
    let source = match std::fs::read_to_string(file) {
        Ok(s)  => s,
        Err(e) => { eprintln!("  {} {}: {}", "warn:".yellow(), file, e); return Ok((0, 0)); }
    };

    let test_fns = collect_test_functions(&source);
    if test_fns.is_empty() { return Ok((0, 0)); }

    println!("  {} {}", "Testing:".cyan().bold(), file.dimmed());

    let mut passed = 0usize;
    let mut failed = 0usize;

    if try_hsharp_test(file, verbose) {
        passed = test_fns.len();
    } else {
        for fn_name in &test_fns {
            match run_single_test(file, fn_name, verbose) {
                Ok(true)  => { passed += 1; println!("    {} {}", "✓".green(), fn_name.dimmed()); }
                Ok(false) | Err(_) => {
                    failed += 1;
                    println!("    {} {}", "✗".red(), fn_name);
                }
            }
        }
    }

    println!(
        "  {} {}: {}/{} passed",
        if failed == 0 { "✓".green() } else { "✗".red() },
            file, passed, passed + failed,
    );
    Ok((passed, failed))
}

fn collect_test_functions(source: &str) -> Vec<String> {
    let mut fns   = Vec::new();
    let mut lines = source.lines().peekable();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        if trimmed == "#[test]" || trimmed.starts_with("#[test]") {
            while let Some(next) = lines.peek() {
                let nt = next.trim();
                if nt.is_empty() { lines.next(); continue; }
                if nt.starts_with("fn ") || nt.starts_with("pub fn ") {
                    let name = nt
                    .trim_start_matches("pub ")
                    .trim_start_matches("fn ")
                    .split('(').next().unwrap_or("").trim().to_string();
                    if !name.is_empty() { fns.push(name); }
                }
                break;
            }
        }
    }
    fns
}

fn try_hsharp_test(file: &str, _verbose: bool) -> bool {
    std::process::Command::new("hsharp")
    .args(["preview", "--test", file])
    .status()
    .map(|s| s.success())
    .unwrap_or(false)
}

fn run_single_test(file: &str, fn_name: &str, _verbose: bool) -> anyhow::Result<bool> {
    // Build a temp file: original source + a main that calls the test fn
    let orig = std::fs::read_to_string(file)?;
    let full_src = format!(
        "{}\n\nfn __bytes_test_entry__() is\n    {}()\nend\n",
                           orig, fn_name
    );

    // Write to a temp file using prefix (with_suffix not available in tempfile 3.8)
    let tmp = tempfile::Builder::new()
    .prefix("bytes_test_")
    .suffix(".h#")
    .tempfile()?;
    std::fs::write(tmp.path(), &full_src)?;

    let ok = std::process::Command::new("hsharp")
    .args(["preview", tmp.path().to_str().unwrap_or("")])
    .status()
    .map(|s| s.success())
    .unwrap_or(false);
    Ok(ok)
}
