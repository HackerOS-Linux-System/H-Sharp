use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Position {
    pub line: usize,
    pub col: usize,
    pub offset: usize,
}

impl Position {
    pub fn new(line: usize, col: usize, offset: usize) -> Self {
        Self { line, col, offset }
    }
}

impl std::fmt::Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Span {
    pub start: Position,
    pub end: Position,
    pub file: String,
}

impl Span {
    pub fn new(start: Position, end: Position, file: impl Into<String>) -> Self {
        Self { start, end, file: file.into() }
    }

    pub fn dummy() -> Self {
        Self {
            start: Position::new(0, 0, 0),
            end: Position::new(0, 0, 0),
            file: "<unknown>".to_string(),
        }
    }

    pub fn merge(&self, other: &Span) -> Span {
        Span {
            start: self.start.clone(),
            end: other.end.clone(),
            file: self.file.clone(),
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.start)
    }
}
