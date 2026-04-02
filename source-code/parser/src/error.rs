use crate::span::Span;
use colored::Colorize;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorKind {
    UnexpectedToken,
    UnexpectedChar(char),
    UnexpectedEof,
    UnterminatedString,
    InvalidEscape,
    InvalidType,
    ExpectedIdent,
    ExpectedToken(String),
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
    pub message: String,
    pub hints: Vec<String>,
    pub source_line: Option<String>,
}

impl ParseError {
    pub fn new(
        kind: ParseErrorKind,
        span: Span,
        message: impl Into<String>,
        hints: Vec<String>,
    ) -> Self {
        Self {
            kind,
            span,
            message: message.into(),
            hints,
            source_line: None,
        }
    }

    pub fn with_source(mut self, source: &str) -> Self {
        let line_idx = self.span.start.line.saturating_sub(1);
        self.source_line = source.lines().nth(line_idx).map(|s| s.to_string());
        self
    }

    /// Elm-like pretty error display
    pub fn render(&self, source: &str) -> String {
        let mut out = String::new();
        let line_idx = self.span.start.line.saturating_sub(1);
        let source_line = source.lines().nth(line_idx).unwrap_or("");

        // Header
        out.push_str(&format!(
            "{} {}\n",
            "-- SYNTAX ERROR".red().bold(),
            format!("({}) -------", self.span.file).dimmed(),
        ));
        out.push_str(&format!(
            "{} {}\n\n",
            "-->".cyan().bold(),
            format!("{}:{}:{}", self.span.file, self.span.start.line, self.span.start.col).cyan(),
        ));

        // Source context — show lines around the error
        let start_display = line_idx.saturating_sub(1);
        let lines: Vec<&str> = source.lines().collect();
        for (i, &line) in lines.iter().enumerate().skip(start_display).take(3) {
            let lineno = i + 1;
            let gutter = format!("{:4} | ", lineno);
            if lineno == self.span.start.line {
                out.push_str(&format!("{}{}\n", gutter.yellow().bold(), line));
                // Caret pointing to the error
                let spaces = " ".repeat(gutter.len() + self.span.start.col.saturating_sub(1));
                let span_len = if self.span.end.line == self.span.start.line {
                    (self.span.end.col.saturating_sub(self.span.start.col)).max(1)
                } else {
                    line.len().saturating_sub(self.span.start.col.saturating_sub(1)).max(1)
                };
                let carets = "^".repeat(span_len);
                out.push_str(&format!("{}{}\n", spaces, carets.red().bold()));
            } else {
                out.push_str(&format!("{}{}\n", gutter.dimmed(), line.dimmed()));
            }
        }

        out.push('\n');

        // Error message
        out.push_str(&format!("{} {}\n", "Error:".red().bold(), self.message.bold()));

        // Hints
        if !self.hints.is_empty() {
            out.push('\n');
            for hint in &self.hints {
                out.push_str(&format!("  {} {}\n", "Hint:".cyan().bold(), hint));
            }
        }

        out
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}:{}] {}", self.span.start.line, self.span.start.col, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Default)]
pub struct ErrorReporter {
    pub errors: Vec<ParseError>,
}

impl ErrorReporter {
    pub fn new() -> Self { Self::default() }

    pub fn report(&mut self, e: ParseError) {
        self.errors.push(e);
    }

    pub fn has_errors(&self) -> bool { !self.errors.is_empty() }

    pub fn render_all(&self, source: &str) -> String {
        self.errors.iter().map(|e| e.render(source)).collect::<Vec<_>>().join("\n")
    }
}
