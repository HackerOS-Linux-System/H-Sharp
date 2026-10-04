use colored::Colorize;
use hsharp_parser::edition::{self, Edition, EditionStatus};
use std::path::Path;

/// Where the default edition came from — shown by `h# editions` / `--verbose`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    Flag,
    Env,
    BitHk,
    Latest,
}

impl Source {
    pub fn describe(&self) -> &'static str {
        match self {
            Source::Flag => "--edition flag",
            Source::Env => "HSHARP_EDITION",
            Source::BitHk => "Bit.hk [edition]",
            Source::Latest => "newest known edition",
        }
    }
}

/// Pure resolution (no side effects, no exit) so it can be unit-tested.
/// `bit_hk_dir` is the directory to look for the project's `Bit.hk` from.
pub fn resolve(
    flag: Option<&str>,
    env: Option<&str>,
    bit_hk_dir: Option<&Path>,
) -> Result<(Edition, Source), String> {
    if let Some(f) = flag {
        return Edition::parse(f)
            .map(|e| (e, Source::Flag))
            .map_err(|e| format!("--edition {}: {}\n  hint: {}", f, e.message(), e.hints().join("; ")));
    }
    if let Some(v) = env.map(str::trim).filter(|v| !v.is_empty()) {
        return Edition::parse(v)
            .map(|e| (e, Source::Env))
            .map_err(|e| format!("HSHARP_EDITION={}: {}\n  hint: {}", v, e.message(), e.hints().join("; ")));
    }
    if let Some(dir) = bit_hk_dir {
        if let Some(e) = hsharp_compiler::bit_resolve::project_edition(dir)? {
            return Ok((e, Source::BitHk));
        }
    }
    Ok((Edition::LATEST, Source::Latest))
}

/// Resolve and install the process-wide default edition. Exits with a clear
/// message on an invalid value (a wrong edition must never silently fall
/// back to something else).
pub fn init(flag: Option<String>, anchor: &Path) -> (Edition, Source) {
    let env = std::env::var("HSHARP_EDITION").ok();
    // Walk up from the file's directory (or the cwd for `h# check`/`repl`).
    let dir = if anchor.is_dir() { Some(anchor.to_path_buf()) } else { anchor.parent().map(|p| p.to_path_buf()) }
        .map(|d| if d.as_os_str().is_empty() { std::path::PathBuf::from(".") } else { d })
        .and_then(|d| std::fs::canonicalize(&d).ok().or(Some(d)));
    match resolve(flag.as_deref(), env.as_deref(), dir.as_deref()) {
        Ok((e, src)) => {
            edition::set_default_edition(e);
            (e, src)
        }
        Err(msg) => {
            eprintln!("{} {}", "Error:".red().bold(), msg);
            std::process::exit(2);
        }
    }
}

/// `h# editions` — list what this toolchain accepts.
pub fn list(current: (Edition, Source)) {
    println!("{}", "Supported H# editions:".bold());
    for e in Edition::ALL {
        let mark = if *e == current.0 { "*" } else { " " };
        let status = match e.status() {
            EditionStatus::Stable => "stable".green().to_string(),
            EditionStatus::Deprecated => "deprecated".yellow().to_string(),
        };
        let latest = if *e == Edition::LATEST { " (latest)" } else { "" };
        println!("  {} {}  {}{}  {}", mark, e.as_str().cyan().bold(), status, latest, e.summary().dimmed());
    }
    println!();
    println!(
        "  {} {}  {}",
        "default for files without `using`:".bold(),
        current.0.as_str().cyan(),
        format!("(from {})", current.1.describe()).dimmed()
    );
    println!("{}", "  pick one per file:      using \"2026\"".dimmed());
    println!("{}", "  pick one per run:       h# compile main.h# --edition 2026   (or HSHARP_EDITION=2026)".dimmed());
    println!("{}", "  pick one per project:   Bit.hk  [edition] -> edition => 2026   (needs lang => h#)".dimmed());
}

/// Call right before parsing the entry file so every parsed file is recorded.
pub fn begin_build() {
    edition::start_recording();
}

/// Call after `expand_program`. Prints the edition mix (only when the build
/// really mixes editions, or always with `verbose`).
pub fn end_build(verbose: bool) {
    let records = edition::take_records();
    if verbose {
        for r in &records {
            println!(
                "  {} {}  {}",
                "edition".dimmed(),
                r.edition.as_str().cyan(),
                format!("{}{}", r.file, if r.declared { "" } else { "  (default)" }).dimmed()
            );
        }
    }
    if let Some(note) = edition::describe_mix(&records) {
        eprintln!("{}", note.trim_end().yellow());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hlib_and_parser_edition_lists_agree() {
        let parser: Vec<&str> = Edition::ALL.iter().map(|e| e.as_str()).collect();
        assert_eq!(parser, hsharp_hlib::manifest::SUPPORTED_EDITIONS.to_vec());
        assert_eq!(Edition::LATEST.as_str(), hsharp_hlib::manifest::DEFAULT_EDITION);
    }

    #[test]
    fn nothing_given_means_latest() {
        let (e, s) = resolve(None, None, None).unwrap();
        assert_eq!(e, Edition::LATEST);
        assert_eq!(s, Source::Latest);
    }

    #[test]
    fn flag_beats_env() {
        let (e, s) = resolve(Some("2026"), Some("2026"), None).unwrap();
        assert_eq!((e, s), (Edition::E2026, Source::Flag));
        let (_, s) = resolve(None, Some("2026"), None).unwrap();
        assert_eq!(s, Source::Env);
        let (_, s) = resolve(None, Some("  "), None).unwrap();
        assert_eq!(s, Source::Latest);
    }

    #[test]
    fn invalid_values_are_errors_not_fallbacks() {
        assert!(resolve(Some("2099"), None, None).unwrap_err().contains("newer"));
        assert!(resolve(None, Some("abc"), None).unwrap_err().contains("HSHARP_EDITION"));
        // even when a valid lower-priority source exists
        assert!(resolve(Some("2099"), Some("2026"), None).is_err());
    }

    #[test]
    fn bit_hk_edition_is_used_only_for_hsharp_projects() {
        let root = std::env::temp_dir().join(format!("hsharp_cli_edition_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for (dir, lang) in [("h", "h#"), ("s", "hs")] {
            std::fs::create_dir_all(root.join(dir)).unwrap();
            std::fs::write(
                root.join(dir).join("Bit.hk"),
                format!("[package]\n-> name => t\n-> lang => {}\n[edition]\n-> edition => 2026\n", lang),
            )
            .unwrap();
        }
        assert_eq!(resolve(None, None, Some(&root.join("h"))).unwrap().1, Source::BitHk);
        assert_eq!(resolve(None, None, Some(&root.join("s"))).unwrap().1, Source::Latest);
        // flag still wins over Bit.hk
        assert_eq!(resolve(Some("2026"), None, Some(&root.join("h"))).unwrap().1, Source::Flag);
        let _ = std::fs::remove_dir_all(&root);
    }
}
