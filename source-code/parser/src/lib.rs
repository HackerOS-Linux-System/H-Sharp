pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod span;

use error::ParseError;
use lexer::Lexer;

pub use ast::Module;
pub use error::ErrorReporter;

pub struct ParseResult {
    pub module: Module,
    pub errors: Vec<ParseError>,
    pub source: String,
}

impl ParseResult {
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn render_errors(&self) -> String {
        self.errors.iter().map(|e| e.render(&self.source)).collect::<Vec<_>>().join("\n")
    }
}

pub fn parse(source: &str, file: &str) -> ParseResult {
    let mut lexer = Lexer::new(source, file);
    let (tokens, lex_errors) = match lexer.tokenize() {
        Ok(t) => (t, vec![]),
        Err(e) => {
            // Still try to parse with partial tokens — collect what we have
            // by re-running in recovery mode
            let mut l2 = Lexer::new(source, file);
            let toks = match l2.tokenize() {
                Ok(t) => t,
                Err(_) => vec![lexer::Token::new(
                    lexer::TokenKind::EOF,
                    span::Span::dummy(),
                    "",
                )],
            };
            (toks, e)
        }
    };

    let mut p = parser::Parser::new(tokens, source.to_string(), file.to_string());
    let module = p.parse_module();
    let mut errors = lex_errors;
    errors.extend(p.errors.errors);

    ParseResult {
        module,
        errors,
        source: source.to_string(),
    }
}
