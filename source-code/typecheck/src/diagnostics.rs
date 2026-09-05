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
/// does no I/O so it works the same whether the source came from disk, a
/// REPL buffer, or an in-memory test fixture).
pub fn print_diagnostics(diags: &[Diagnostic], source: &str, file: &str) {
    const RESET:  &str = "\x1b[0m";
    const BOLD:   &str = "\x1b[1m";
    const DIM:    &str = "\x1b[2m";
    const RED:    &str = "\x1b[31m";
    const YELLOW: &str = "\x1b[33m";
    const CYAN:   &str = "\x1b[36m";

    let lines: Vec<&str> = source.lines().collect();

    for diag in diags {
        let (kind, accent) = match diag.severity {
            Severity::Error   => ("TYPE ERROR", RED),
            Severity::Warning => ("WARNING", YELLOW),
        };
        let label = match diag.severity {
            Severity::Error   => "Error",
            Severity::Warning => "Warning",
        };

        println!("{}{}-- {} ({}) -------{}", accent, BOLD, kind, file, RESET);
        println!("{}--> {}:{}:{}{}", CYAN, file, diag.span.start.line, diag.span.start.col, RESET);
        println!();

        let line_no   = diag.span.start.line;
        let col       = diag.span.start.col;
        let width     = (diag.span.end.col.max(col + 1)).saturating_sub(col).max(1);
        let gutter_w  = line_no.to_string().len().max(
            (line_no + 1).to_string().len()
        ) + 1;

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
