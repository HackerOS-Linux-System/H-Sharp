use colored::*;
use std::path::Path;

/// Collect and run all #[test] functions in H# source files.
/// For each file, we invoke `hsharp preview --test` which runs test-tagged fns.
/// Falls back to scanning for `#[test]` annotations and running them via interpreter.
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
        if passed + failed > 0 {
            total_files += 1;
        }
    }

    println!();
    println!("  {}", "─".repeat(48).dimmed());
    if total_failed == 0 {
        println!(
            "  {} {} test(s) passed in {} file(s)",
                 "✓".green().bold(),
                 total_passed,
                 total_files,
        );
    } else {
        println!(
            "  {} {}/{} passed, {} failed",
            "✗".red().bold(),
                 total_passed,
                 total_passed + total_failed,
                 total_failed,
        );
        std::process::exit(1);
    }
    Ok(())
}

fn collect_test_files(extra: &[String]) -> Vec<String> {
    if !extra.is_empty() {
        return extra.iter()
        .filter(|s| !s.starts_with("--"))
        .cloned()
        .collect();
    }

    walkdir::WalkDir::new(".")
    .max_depth(6)
    .into_iter()
    .flatten()
    .filter(|e| {
        let p = e.path();
        let ext = p.extension().and_then(|x| x.to_str());
        let is_test = p.to_string_lossy().contains("test")
        || p.to_string_lossy().contains("spec")
        || ext == Some("h#")
        || ext == Some("hsp");
        e.file_type().is_file()
        && is_test
        && !p.starts_with("./build")
        && !p.starts_with("./.cache")
    })
    .map(|e| e.path().display().to_string())
    .collect()
}

fn run_file_tests(file: &str, verbose: bool) -> anyhow::Result<(usize, usize)> {
    // Parse #[test] functions from the source
    let source = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("  {} cannot read {}: {}", "warn:".yellow(), file, e);
            return Ok((0, 0));
        }
    };

    let test_fns = collect_test_functions(&source);
    if test_fns.is_empty() {
        return Ok((0, 0));
    }

    println!("  {} {}", "Testing:".cyan().bold(), file.dimmed());

    let mut passed = 0usize;
    let mut failed = 0usize;

    // Try hsharp preview --test first
    let hsharp_test_ok = try_hsharp_test(file, verbose);

    if hsharp_test_ok {
        // hsharp reported results itself — just count as all passed for now
        passed = test_fns.len();
    } else {
        // Fallback: generate a wrapper and run via interpreter
        for fn_name in &test_fns {
            let result = run_single_test(file, fn_name, verbose);
            match result {
                Ok(true) => {
                    passed += 1;
                    println!("    {} {}", "✓".green(), fn_name.dimmed());
                }
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
            file,
            passed,
            passed + failed,
    );
    Ok((passed, failed))
}

/// Extract all function names tagged with #[test]
fn collect_test_functions(source: &str) -> Vec<String> {
    let mut fns   = Vec::new();
    let mut lines = source.lines().peekable();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        if trimmed == "#[test]" || trimmed.starts_with("#[test]") {
            // Next non-empty line should be `fn name(...)`
            while let Some(next) = lines.peek() {
                let nt = next.trim();
                if nt.is_empty() {
                    lines.next();
                    continue;
                }
                if nt.starts_with("fn ") || nt.starts_with("pub fn ") {
                    let name = nt
                    .trim_start_matches("pub ")
                    .trim_start_matches("fn ")
                    .split('(')
                    .next()
                    .unwrap_or("")
                    .trim()
                    .to_string();
                    if !name.is_empty() {
                        fns.push(name);
                    }
                }
                break;
            }
        }
    }
    fns
}

fn try_hsharp_test(file: &str, verbose: bool) -> bool {
    // Try `hsharp preview --test <file>` — supported in h# v0.7
    let status = std::process::Command::new("hsharp")
    .args(["preview", "--test", file])
    .status();
    matches!(status, Ok(s) if s.success())
}

fn run_single_test(file: &str, fn_name: &str, verbose: bool) -> anyhow::Result<bool> {
    // Generate a tiny wrapper that calls the test fn
    let wrapper_src = format!(
        ";; bytes test wrapper — auto-generated\n\
;; source: {}\n\
;; test:   {}\n\n\
{}()\n",
                              file, fn_name, fn_name
    );

    let tmp = tempfile::NamedTempFile::with_suffix(".h#")?;
    std::fs::write(tmp.path(), &wrapper_src)?;

    // Concatenate source + wrapper into one temp file
    let full_src = format!("{}\n\nfn __bytes_test_main__() is\n    {}()\nend\n",
                           std::fs::read_to_string(file)?, fn_name);
    let tmp2 = tempfile::NamedTempFile::with_suffix(".h#")?;
    std::fs::write(tmp2.path(), &full_src)?;

    let ok = std::process::Command::new("hsharp")
    .args(["preview", tmp2.path().to_str().unwrap_or("")])
    .status()
    .map(|s| s.success())
    .unwrap_or(false);
    Ok(ok)
}
