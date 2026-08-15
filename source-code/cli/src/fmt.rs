use colored::Colorize;
use std::path::PathBuf;
use walkdir::WalkDir;

pub fn run(files: Vec<PathBuf>, check: bool) {
    let targets: Vec<PathBuf> = if !files.is_empty() {
        files
    } else {
        let exts = ["h#", "hsp", "h-sharp"];
        WalkDir::new(".").max_depth(6).into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file()
                && e.path().extension().and_then(|s| s.to_str()).map(|x| exts.contains(&x)).unwrap_or(false)
                && !e.path().starts_with("./build"))
            .map(|e| e.path().to_path_buf())
            .collect()
    };

    if targets.is_empty() {
        eprintln!("{} no .h# files found", "Error:".red().bold());
        std::process::exit(1);
    }

    let mut changed = 0usize;
    let mut unchanged = 0usize;

    for path in &targets {
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => { eprintln!("{} cannot read `{}`: {}", "Error:".red().bold(), path.display(), e); std::process::exit(1); }
        };
        let formatted = format_source(&src);

        if formatted == src {
            unchanged += 1;
            continue;
        }

        if check {
            println!("{} {}", "would reformat:".yellow().bold(), path.display());
            changed += 1;
            continue;
        }

        if let Err(e) = std::fs::write(path, &formatted) {
            eprintln!("{} cannot write `{}`: {}", "Error:".red().bold(), path.display(), e);
            std::process::exit(1);
        }
        println!("{} {}", "reformatted:".green().bold(), path.display());
        changed += 1;
    }

    let verb = if check { "would reformat" } else { "reformatted" };
    println!("\n{} {} file(s), {} already formatted", verb, changed, unchanged);
    if check && changed > 0 {
        std::process::exit(1); // like `rustfmt --check`: non-zero if anything would change
    }
}

const INDENT: &str = "    ";

fn format_source(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let mut depth: i32 = 0;
    let mut blank_run = 0u32;

    for raw_line in src.lines() {
        let line = raw_line.trim_end();
        let trimmed = line.trim_start();

        if trimmed.is_empty() {
            blank_run += 1;
            if blank_run <= 1 { out.push('\n'); }
            continue;
        }
        blank_run = 0;

        let (leading_dedent, net_delta) = scan_line(trimmed);

        let this_line_depth = (depth - leading_dedent).max(0);
        for _ in 0..this_line_depth { out.push_str(INDENT); }
        out.push_str(trimmed);
        out.push('\n');

        depth = (depth + net_delta).max(0);
    }

    // Exactly one trailing newline, no trailing blank lines.
    while out.ends_with("\n\n") { out.pop(); }
    if !out.ends_with('\n') { out.push('\n'); }
    out
}

/// Returns `(leading_dedent, net_delta)`:
/// - `leading_dedent`: 1 if this line's *own* indentation should be one
///   level shallower than the running depth (e.g. it starts with `end`,
///   `else`, `elsif`, or a lone closing bracket).
/// - `net_delta`: how much the running depth changes by, after this line,
///   for every *following* line (opens minus closes on this line, net).
fn scan_line(trimmed: &str) -> (i32, i32) {
    // Whole-line comments: don't touch depth at all.
    if trimmed.starts_with(";;") || trimmed.starts_with("#") || trimmed.starts_with("///") {
        return (0, 0);
    }

    let starts_with_word = |w: &str| {
        trimmed == w || trimmed.starts_with(&format!("{} ", w))
            || trimmed.starts_with(&format!("{}(", w))
    };
    let leading_dedent = if starts_with_word("end") || starts_with_word("else")
        || starts_with_word("elsif") || trimmed.starts_with(')')
        || trimmed.starts_with('}') || trimmed.starts_with(']')
    { 1 } else { 0 };

    let mut delta = 0i32;
    let mut chars = trimmed.chars().peekable();
    let mut word = String::new();
    let mut in_string = false;

    let flush_word = |w: &mut String, delta: &mut i32| {
        match w.as_str() {
            "is" | "do" => *delta += 1,
            "end" => *delta -= 1,
            _ => {}
        }
        w.clear();
    };

    while let Some(c) = chars.next() {
        if in_string {
            if c == '\\' { chars.next(); }
            else if c == '"' { in_string = false; }
            continue;
        }
        match c {
            '"' => { flush_word(&mut word, &mut delta); in_string = true; }
            ';' if chars.peek() == Some(&';') => { flush_word(&mut word, &mut delta); break; } // ;; comment
            '#' => { flush_word(&mut word, &mut delta); break; }
            '(' | '[' | '{' => { flush_word(&mut word, &mut delta); delta += 1; }
            ')' | ']' | '}' => { flush_word(&mut word, &mut delta); delta -= 1; }
            c if c.is_alphanumeric() || c == '_' => word.push(c),
            _ => flush_word(&mut word, &mut delta),
        }
    }
    flush_word(&mut word, &mut delta);

    // `elsif`/bare `else` are same-level sibling-arm openers: whatever
    // `is`/`do` they contain (e.g. `elsif x > 1 is`) only reopens the
    // block at the *same* depth the previous arm was already at — not a
    // level deeper. `leading_dedent` already accounts for printing this
    // line itself one shallower; forcing the running-depth delta to 0
    // here (instead of the `+1` an embedded `is` would otherwise add)
    // keeps the arm's body at the same depth as the previous arm's body,
    // which is what a human reformatting this by hand would do.
    if starts_with_word("elsif") || starts_with_word("else") {
        delta = 0;
    }

    // The line that *opens* a block (e.g. `fn f() is`) also often starts
    // with a dedent-worthy keyword itself (e.g. `elsif x is`) — both are
    // independently correct: elsif still dedents its own line, and still
    // opens a new block for what follows.
    (leading_dedent, delta)
}
