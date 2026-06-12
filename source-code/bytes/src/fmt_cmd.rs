use colored::*;

pub fn format_files(extra: &[String], _verbose: bool) -> anyhow::Result<()> {
    println!();
    println!("  {}  H# Formatter", "bytes fmt".cyan().bold());
    println!();

    let files = collect_hsharp_files(extra);
    if files.is_empty() {
        println!("  {}", "No .h# files found.".dimmed());
        return Ok(());
    }

    let mut changed = 0usize;
    for file in &files {
        match format_file(file) {
            Ok(true)  => { changed += 1; println!("  {} {}", "edited".cyan(), file); }
            Ok(false) => {}
            Err(e)    => eprintln!("  {} {}: {}", "warn:".yellow(), file, e),
        }
    }

    println!();
    println!(
        "  {} {} file(s) formatted, {} unchanged",
             "ok".green().bold(),
             changed,
             files.len().saturating_sub(changed),
    );
    Ok(())
}

fn collect_hsharp_files(extra: &[String]) -> Vec<String> {
    if !extra.is_empty() {
        return extra.iter().filter(|s| !s.starts_with("--")).cloned().collect();
    }
    walkdir::WalkDir::new(".")
    .max_depth(6).into_iter().flatten()
    .filter(|e| {
        let p = e.path();
        e.file_type().is_file()
        && p.extension().map(|x| x == "h#" || x == "hsp").unwrap_or(false)
        && !p.starts_with("./build")
        && !p.starts_with("./.cache")
    })
    .map(|e| e.path().display().to_string())
    .collect()
}

fn format_file(path: &str) -> anyhow::Result<bool> {
    let original  = std::fs::read_to_string(path)?;
    let formatted = format_source(&original);
    if formatted == original { return Ok(false); }
    std::fs::write(path, &formatted)?;
    Ok(true)
}

/// Basic H# formatter:
/// - normalise indentation to 4 spaces
/// - collapse multiple blank lines to one
/// - strip trailing whitespace
fn format_source(src: &str) -> String {
    let mut output        = String::with_capacity(src.len());
    let mut indent_level  = 0usize;
    let mut blank_run     = 0usize;
    const INDENT: &str    = "    ";

    for line in src.lines() {
        let trimmed = line.trim();

        // Collapse consecutive blank lines to one
        if trimmed.is_empty() {
            blank_run += 1;
            if blank_run <= 1 { output.push('\n'); }
            continue;
        }
        blank_run = 0;

        // Decrease indent before writing for `end`, `else`, `elsif`
        if matches_closing(trimmed) && indent_level > 0 {
            indent_level -= 1;
        }

        // Comments keep relative indentation
        let formatted_line = format!("{}{}", INDENT.repeat(indent_level), trimmed);
        output.push_str(formatted_line.trim_end());
        output.push('\n');

        // Increase indent after `is` keyword (block openers)
        if matches_opening(trimmed) {
            indent_level += 1;
        }
    }

    // Single trailing newline
    while output.ends_with("\n\n") { output.pop(); }
    if !output.ends_with('\n') { output.push('\n'); }
    output
}

fn matches_opening(line: &str) -> bool {
    let lc = line.to_lowercase();
    // Ends with standalone `is` keyword
    lc.ends_with(" is") || lc == "is"
}

fn matches_closing(line: &str) -> bool {
    let lc = line.trim().to_lowercase();
    lc == "end"
    || lc.starts_with("end ")
    || lc.starts_with("else")
    || lc.starts_with("elsif")
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_indent() {
        let src = "fn main() is\nwrite(\"hello\")\nend\n";
        let out = format_source(src);
        assert!(out.contains("    write(\"hello\")"), "got: {}", out);
    }
    #[test]
    fn test_no_double_blank() {
        let src = "a\n\n\n\nb\n";
        let out = format_source(src);
        assert!(!out.contains("\n\n\n"), "got: {}", out);
    }
}
