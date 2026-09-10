use hsharp_parser::span::Span;


// ── §1: Diagnostics — full errors with location, matching h#'s format ──────

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Severity {
    Error,
    Warning,
}

/// A single type-checker diagnostic: a message tied to a source location,
/// with optional fix-it hints. `check_module` now collects ALL of these
/// (instead of bailing on the first error) and returns them to the caller,
/// who renders them with `print_diagnostics` — producing the same
/// `-- TYPE ERROR (file) -------` / `--> file:line:col` format that `h#`
/// already prints for syntax errors. This is the fix for the
/// `✗ type check failed [8s]`-with-no-detail problem: `hsharp build` should
/// call `print_diagnostics(&diags, &source, &file)` for every diagnostic
/// before reporting overall pass/fail.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub severity: Severity,
    pub span:     Span,
    pub message:  String,
    pub hints:    Vec<String>,
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Self { severity: Severity::Error, span, message: message.into(), hints: Vec::new() }
    }
    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Self { severity: Severity::Warning, span, message: message.into(), hints: Vec::new() }
    }
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.hints.push(hint.into());
        self
    }
}

/// Render diagnostics in the same visual format as `h#`'s parse errors,
/// with ANSI colors matching the rest of the `h#` CLI (red/bold errors,
/// yellow/bold warnings, cyan locations, dimmed context) — this crate has
/// no dependency on the `colored` crate on purpose (kept dependency-free
/// for the LSP/playground wasm32 targets, which never call this function
/// and build their own renderings straight from `Diagnostic`), so the
/// codes below are written out by hand instead of pulled in as a crate:
///
/// ```text
/// -- TYPE ERROR (src/main.h#) -------
/// --> src/main.h#:47:12
///
///   46 |     let x: int
///   47 |     let x: int = "hello"
///                          ^^^^^^^
///   48 | end
///
/// Error: type mismatch: expected `int`, found `string`
///
///   Hint: convert with to_string()/to_int(), or fix the declared type
/// ```
///
/// `source` is the full text of `file` (read by the caller — this function
/// avoids extra I/O for the common case where every diagnostic's span
/// belongs to `file` itself).
///
/// A diagnostic's `span.file` is **not always** `file`, though: once
/// `ModuleResolver::expand_program` inlines a `mod X` declaration, a
/// `use "std -> x"` import, or a `use "bytes -> x"` import (see
/// `hsharp-compiler`'s `modules.rs`), the inlined items keep the `Span`s
/// they were originally parsed with — `file` pointing at *that* module's
/// own source path, not the entry file's. Previously this function always
/// printed `source`/`file` regardless, so a real type error inside an
/// inlined module rendered as complete nonsense: the entry file's name in
/// the banner, the entry file's text (at an unrelated line number) as
/// "context", and — since `check_stmt`'s `fn_name` came from whatever
/// function the checker actually was inside — a function name that
/// doesn't appear anywhere near the shown location. The error itself was
/// real; only its presentation was garbled beyond use. Fixed by resolving
/// each diagnostic against its *own* `span.file`, reading it from disk
/// (memoized — many diagnostics commonly share one non-primary file) when
/// it differs from `file`.
pub fn print_diagnostics(diags: &[Diagnostic], source: &str, file: &str) {
    const RESET:  &str = "\x1b[0m";
    const BOLD:   &str = "\x1b[1m";
    const DIM:    &str = "\x1b[2m";
    const RED:    &str = "\x1b[31m";
    const YELLOW: &str = "\x1b[33m";
    const CYAN:   &str = "\x1b[36m";

    // Lazily-read cache of non-primary source files a diagnostic's span
    // might point into. `None` means "tried and failed to read" (e.g. the
    // path was relative to a working directory that no longer applies, or
    // it's a synthetic span like `Span::dummy()`'s `"<unknown>"`) — cached
    // too, so a bad path is only attempted once even if many diagnostics
    // share it.
    let mut other_sources: std::collections::HashMap<&str, Option<String>> = std::collections::HashMap::new();

    for diag in diags {
        let diag_file = diag.span.file.as_str();
        let owned_other;
        let lines: Vec<&str> = if diag_file == file {
            source.lines().collect()
        } else {
            owned_other = other_sources
                .entry(diag_file)
                .or_insert_with(|| std::fs::read_to_string(diag_file).ok())
                .clone();
            owned_other.as_deref().map(|s| s.lines().collect()).unwrap_or_default()
        };

        let (kind, accent) = match diag.severity {
            Severity::Error   => ("TYPE ERROR", RED),
            Severity::Warning => ("WARNING", YELLOW),
        };
        let label = match diag.severity {
            Severity::Error   => "Error",
            Severity::Warning => "Warning",
        };

        println!("{}{}-- {} ({}) -------{}", accent, BOLD, kind, diag_file, RESET);
        println!("{}--> {}:{}:{}{}", CYAN, diag_file, diag.span.start.line, diag.span.start.col, RESET);
        println!();

        let line_no   = diag.span.start.line;
        let col       = diag.span.start.col;
        let width     = (diag.span.end.col.max(col + 1)).saturating_sub(col).max(1);
        let gutter_w  = line_no.to_string().len().max(
            (line_no + 1).to_string().len()
        ) + 1;

        if lines.is_empty() {
            // The span's own file couldn't be read (moved/deleted since
            // parsing, or a synthetic span) — show the message without
            // fabricating context from an unrelated file, rather than
            // silently falling back to `source` the way this used to.
            println!("{}  (source not available for context){}", DIM, RESET);
            println!();
        } else {
        // Line before (context), if any
        if line_no >= 2 {
            if let Some(prev) = lines.get(line_no - 2) {
                println!("{}  {:>width$} | {}{}", DIM, line_no - 1, prev, RESET, width = gutter_w);
            }
        }
        // The offending line itself
        if let Some(this_line) = lines.get(line_no - 1) {
            println!("  {:>width$} {}|{} {}", line_no, DIM, RESET, this_line, width = gutter_w);
        }
        // Caret underline
        let pad = " ".repeat(gutter_w + 3 + col.saturating_sub(1));
        println!("{}{}{}{}{}", pad, accent, BOLD, "^".repeat(width), RESET);
        // Line after (context), if any
        if let Some(next) = lines.get(line_no) {
            println!("{}  {:>width$} | {}{}", DIM, line_no + 1, next, RESET, width = gutter_w);
        }
        println!();
        }

        println!("{}{}{}:{} {}", accent, BOLD, label, RESET, diag.message);
        for hint in &diag.hints {
            println!();
            println!("  {}{}Hint:{} {}", CYAN, BOLD, RESET, hint);
        }
        println!();
    }

    let errs = diags.iter().filter(|d| d.severity == Severity::Error).count();
    let warns = diags.iter().filter(|d| d.severity == Severity::Warning).count();
    if errs > 0 {
        println!("{}{}error:{} {} error(s), {} warning(s)", RED, BOLD, RESET, errs, warns);
    } else if warns > 0 {
        println!("{}{}warning:{} {} warning(s)", YELLOW, BOLD, RESET, warns);
    }
}


/// Legacy error type, kept for backward compatibility with any external
/// code that still matches on it. `check_module` no longer constructs these
/// — use `Diagnostic` (above) instead, which carries a `Span`.
#[allow(dead_code)]
#[derive(Debug, Clone, thiserror::Error)]
pub enum TypeError {
    #[error("undefined variable `{0}`")]
    UndefinedVar(String),
    #[error("std library not found: {0}")]
    StdNotFound(String),
    #[error("type mismatch: expected `{expected}`, found `{found}`")]
    TypeMismatch { expected: String, found: String },
    #[error("undefined function `{0}`")]
    UndefinedFn(String),
    #[error("undefined type `{0}`")]
    UndefinedType(String),
    #[error("wrong number of arguments to `{name}`: expected {expected}, found {found}")]
    ArgCount { name: String, expected: usize, found: usize },
    #[error("cannot assign to immutable variable `{0}`")]
    ImmutableAssign(String),
    #[error("return type mismatch in `{fn_name}`: expected `{expected}`, found `{found}`")]
    ReturnMismatch { fn_name: String, expected: String, found: String },
}
