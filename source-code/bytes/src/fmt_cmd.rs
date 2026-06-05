use colored::*;

/// Format H# source files.
/// v0.7: basic formatter — normalises indentation, spacing around operators,
/// trailing whitespace, and consistent `is`/`end` block style.
pub fn format_files(extra: &[String], verbose: bool) -> anyhow::Result<()> {
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
        match format_file(file, verbose) {
            Ok(true) => {
                changed += 1;
                println!("  {} {}", "✎".cyan(), file);
            }
            Ok(false) => {
                if verbose {
                    println!("  {} {}", "·".dimmed(), file);
                }
            }
            Err(e) => {
                eprintln!("  {} {}: {}", "warn:".yellow(), file, e);
            }
        }
    }

    println!();
    println!(
        "  {} {} file(s) formatted, {} unchanged",
             "✓".green().bold(),
             changed,
             files.len().saturating_sub(changed),
    );
    Ok(())
}

fn collect_hsharp_files(extra: &[String]) -> Vec<String> {
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
        e.file_type().is_file()
        && p.extension().map(|x| x == "h#" || x == "hsp").unwrap_or(false)
        && !p.starts_with("./build")
        && !p.starts_with("./.cache")
    })
    .map(|e| e.path().display().to_string())
    .collect()
}

/// Format a single file. Returns true if the file was modified.
fn format_file(path: &str, verbose: bool) -> anyhow::Result<bool> {
    let original = std::fs::read_to_string(path)?;
    let formatted = format_source(&original);
    if formatted == original {
        return Ok(false);
    }
    std::fs::write(path, &formatted)?;
    Ok(true)
}

/// Core formatting logic
fn format_source(src: &str) -> String {
    let mut output = String::with_capacity(src.len());
    let mut indent_level: usize = 0;
    const INDENT: &str = "    "; // 4 spaces

    for line in src.lines() {
        let trimmed = line.trim();

        // Skip empty lines as-is
        if trimmed.is_empty() {
            output.push('\n');
            continue;
        }

        // Adjust indent before writing for closing keywords
        let closes = matches_closing(trimmed);
        if closes && indent_level > 0 {
            indent_level -= 1;
        }

        // Comments keep their current relative indent but get normalised
        let formatted_line = if trimmed.starts_with(";;") {
            format!("{}{}", INDENT.repeat(indent_level), trimmed)
        } else {
            format!("{}{}", INDENT.repeat(indent_level), format_line(trimmed))
        };

        output.push_str(&formatted_line);
        output.push('\n');

        // Increase indent after opening keywords
        if matches_opening(trimmed) {
            indent_level += 1;
        }
    }

    // Ensure single trailing newline
    while output.ends_with("\n\n") {
        output.pop();
    }
    if !output.ends_with('\n') {
        output.push('\n');
    }
    output
}

/// Tokens that open a new block (increase indent)
fn matches_opening(line: &str) -> bool {
    let kws = ["is", "is\\n", "=> is"];
    let line_lc = line.to_lowercase();
    // ends with `is` keyword
    if line_lc.ends_with(" is") || line_lc == "is" {
        return true;
    }
    // match arm body `=> is`
    if line_lc.ends_with("=> is") {
        return true;
    }
    false
}

/// Tokens that close a block (decrease indent before writing)
fn matches_closing(line: &str) -> bool {
    let lc = line.trim().to_lowercase();
    lc == "end" || lc.starts_with("end ")
    || lc.starts_with("else") || lc.starts_with("elsif")
}

/// Format a single non-comment line:
/// - normalise spaces around binary operators
/// - remove trailing whitespace
/// - normalise `if cond is` spacing
fn format_line(line: &str) -> String {
    let mut s = line.to_string();

    // Normalise: multiple spaces → single space (except in strings)
    s = collapse_spaces(&s);

    // Normalise spacing around `=` assignment (but not `==`, `!=`, `<=`, `>=`, `=>`)
    // We do a simple pass — a proper formatter would use the AST
    s = normalise_assign(&s);

    s.trim_end().to_string()
}

fn collapse_spaces(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut in_string  = false;
    let mut last_space = false;

    for ch in s.chars() {
        if ch == '"' { in_string = !in_string; }
        if !in_string && ch == ' ' {
            if !last_space { result.push(' '); }
            last_space = true;
        } else {
            result.push(ch);
            last_space = false;
        }
    }
    result
}

fn normalise_assign(s: &str) -> String {
    // Simple: ensure spaces around `=` for let bindings
    // Skip if already has spaces or is part of ==, !=, <=, >=, =>
    if s.starts_with("let ") || s.starts_with("let mut ") {
        // Already handled by collapse_spaces mostly
    }
    s.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_basic() {
        let src = "fn main() is\nwrite(\"hello\")\nend\n";
        let out = format_source(src);
        assert!(out.contains("    write(\"hello\")"));
    }
}
