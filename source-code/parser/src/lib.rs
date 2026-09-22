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

// ─────────────────────────────────────────────────────────────────────────
// Regression tests for the "return type mismatch: expected `GitInfo`,
// found `git_info_GitInfo`" bug (real-world repro: hsh's
// `build_git_info_for_prompt() -> git_info::GitInfo`, `run_statement_text`
// `-> execute::Shell`). See `parser::parse_type_base`'s and
// `parser::parse_ident_expr_from`'s (struct-literal arm) doc comments for
// the full root-cause explanation: `hsharp-compiler::modules::mangle_module_items`
// renames an inlined `mod`/`std ->`/`bytes ->` file's own structs/enums to
// `{prefix}_{Name}`, so a qualified type annotation or struct literal has
// to resolve to that same joined spelling, not just the bare last segment.
#[cfg(test)]
mod qualified_module_type_tests {
    use super::*;
    use ast::{Item, TypeExpr, Expr};

    /// `fn f() -> mod::Type` must parse its return type as the
    /// underscore-joined `mod_Type` — matching the name
    /// `mangle_module_items` actually renames the struct/enum
    /// definition to once `mod X` is inlined — not the bare `Type`.
    #[test]
    fn qualified_return_type_joins_segments() {
        let src = "fn build_git_info_for_prompt() -> git_info::GitInfo is\n    return git_info::git_fetch_info()\nend\n";
        let result = parse(src, "test.h#");
        assert!(!result.has_errors(), "unexpected parse errors: {}", result.render_errors());
        let f = result.module.items.iter().find_map(|i| match i {
            Item::FnDef(f) if f.name == "build_git_info_for_prompt" => Some(f),
            _ => None,
        }).expect("fn not found");
        assert_eq!(f.return_type, Some(TypeExpr::Named("git_info_GitInfo".to_string())));
    }

    /// A three-segment path (`a::b::Type`) joins all of them, not just
    /// the last two or the first two.
    #[test]
    fn qualified_return_type_joins_all_segments() {
        let src = "fn f() -> a::b::Type is\n    return a::b::make()\nend\n";
        let result = parse(src, "test.h#");
        assert!(!result.has_errors(), "unexpected parse errors: {}", result.render_errors());
        let f = result.module.items.iter().find_map(|i| match i {
            Item::FnDef(f) if f.name == "f" => Some(f),
            _ => None,
        }).expect("fn not found");
        assert_eq!(f.return_type, Some(TypeExpr::Named("a_b_Type".to_string())));
    }

    /// An *unqualified* type annotation (no `::` at all) must still
    /// resolve to the bare name, unaffected by the join logic above.
    #[test]
    fn unqualified_return_type_is_unaffected() {
        let src = "fn f() -> GitInfo is\n    return GitInfo { branch: \"\" }\nend\n";
        let result = parse(src, "test.h#");
        assert!(!result.has_errors(), "unexpected parse errors: {}", result.render_errors());
        let f = result.module.items.iter().find_map(|i| match i {
            Item::FnDef(f) if f.name == "f" => Some(f),
            _ => None,
        }).expect("fn not found");
        assert_eq!(f.return_type, Some(TypeExpr::Named("GitInfo".to_string())));
    }

    /// `mod::Type { field: val }` (a qualified struct *literal*, e.g.
    /// hsh's `git_info::GitInfo { branch: "", dirty: false, ahead: 0,
    /// behind: 0 }`) must build the same `mod_Type` name as the
    /// qualified type annotation above — they must agree, or the
    /// literal's inferred type never matches its own function's
    /// declared return type.
    #[test]
    fn qualified_struct_literal_joins_segments() {
        let src = "fn f() -> git_info::GitInfo is\n    return git_info::GitInfo { branch: \"\", dirty: false, ahead: 0, behind: 0 }\nend\n";
        let result = parse(src, "test.h#");
        assert!(!result.has_errors(), "unexpected parse errors: {}", result.render_errors());
        let f = result.module.items.iter().find_map(|i| match i {
            Item::FnDef(f) if f.name == "f" => Some(f),
            _ => None,
        }).expect("fn not found");
        assert_eq!(f.return_type, Some(TypeExpr::Named("git_info_GitInfo".to_string())));
        match f.body.first() {
            Some(ast::Stmt::Return(Some(Expr::StructLit(name, _, _)), _)) => {
                assert_eq!(name, "git_info_GitInfo");
            }
            other => panic!("expected `return git_info_GitInfo {{ .. }}`, got {:?}", other),
        }
    }
}
