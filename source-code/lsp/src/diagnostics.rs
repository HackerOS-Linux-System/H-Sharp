use hsharp_parser::span::{Position as HPosition, Span as HSpan};
use lsp_types::{Diagnostic as LspDiagnostic, DiagnosticSeverity, Position, Range};

pub fn compute(text: &str, file_label: &str) -> Vec<LspDiagnostic> {
    let parsed = hsharp_parser::parse(text, file_label);

    if parsed.has_errors() {
        return parsed.errors.iter().map(|e| {
            let mut message = e.message.clone();
            if !e.hints.is_empty() {
                message.push_str("\nhint: ");
                message.push_str(&e.hints.join("; "));
            }
            to_lsp_diagnostic(&e.span, DiagnosticSeverity::ERROR, message)
        }).collect();
    }

    let mut tc = hsharp_typecheck::TypeChecker::new();
    let diags = tc.check_module(&parsed.module);
    diags.iter().map(|d| {
        let sev = match d.severity {
            hsharp_typecheck::Severity::Error   => DiagnosticSeverity::ERROR,
            hsharp_typecheck::Severity::Warning => DiagnosticSeverity::WARNING,
        };
        let mut message = d.message.clone();
        if !d.hints.is_empty() {
            message.push_str("\nhint: ");
            message.push_str(&d.hints.join("; "));
        }
        to_lsp_diagnostic(&d.span, sev, message)
    }).collect()
}

/// H#'s own `Position` is 1-indexed (line 1, column 1 is the first
/// character — matches how the CLI's own error messages print
/// `file:line:col`, and how virtually every editor/terminal displays
/// positions to a human). LSP's `Position` is 0-indexed by protocol
/// specification. Every conversion between the two needs this subtraction
/// — getting it backwards is the single easiest off-by-one to introduce
/// in an LSP server, so it's centralized here rather than repeated at each
/// call site.
fn to_lsp_position(p: &HPosition) -> Position {
    Position {
        line: p.line.saturating_sub(1) as u32,
        character: p.col.saturating_sub(1) as u32,
    }
}

fn to_lsp_diagnostic(span: &HSpan, severity: DiagnosticSeverity, message: String) -> LspDiagnostic {
    LspDiagnostic {
        range: Range { start: to_lsp_position(&span.start), end: to_lsp_position(&span.end) },
        severity: Some(severity),
        source: Some("hsharp".to_string()),
        message,
        ..Default::default()
    }
}

/// Exposed for `symbols.rs`/`hover.rs`/`completion.rs`, which all need a
/// parsed module too and shouldn't each re-derive their own URL-to-label
/// convention. Returns `None` if parsing failed outright — callers should
/// degrade gracefully (e.g. `hover.rs`/`completion.rs` fall back to
/// word-level heuristics that don't need a full AST).
pub fn parse_ok(text: &str) -> Option<hsharp_parser::ast::Module> {
    let parsed = hsharp_parser::parse(text, "document.h#");
    if parsed.has_errors() { None } else { Some(parsed.module) }
}
