pub mod ast;
pub mod edition;
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
    parse_with_default(source, file, None)
}

/// Like [`parse`], but a file with no `using "<edition>"` is read as
/// `file_default` instead of the process-wide default edition. The module
/// resolvers use this so that every imported file — a `mod`, a `bit`/`hlib`/
/// `workspace` library (default: that library's own `Bit.hk` `[edition]`), or
/// the bundled `std` (always [`edition::STD_EDITION`]) — is read under *its*
/// edition, whatever edition the importing file is written in.
pub fn parse_with_default(source: &str, file: &str, file_default: Option<edition::Edition>) -> ParseResult {
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
    let mut module = p.parse_module();
    let mut errors = lex_errors;
    errors.extend(p.errors.errors);

    // ── Edition handling (see `edition` module docs) ────────────────────
    // Every file is read under its *own* edition — its `using "<year>"`, or
    // the default for undeclared files — so entry files, `mod` files, bit/
    // hlib/workspace/std libraries may all sit on different editions. Each
    // file is feature-checked against, and lowered from, that edition here,
    // so everything downstream only ever sees one canonical AST.
    let declared = module.edition.is_some();
    let ed = edition::effective_edition_with(&module, file_default);
    for v in edition::check_features(&module, ed) {
        errors.push(ParseError::new(
            error::ParseErrorKind::Custom(v.message()),
            v.span.clone(),
            v.message(),
            vec![format!("use `using \"{}\"` (or newer) at the top of the file", v.feature.since())],
        ));
    }
    edition::lower_module(&mut module, ed);
    edition::record(file, ed, declared);

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
// renames an inlined `mod`/`std ->`/`bit ->` file's own structs/enums to
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

// ─────────────────────────────────────────────────────────────────────────
// `use "bit -> lib"` imports (the `bytes` package manager was replaced by
// `bit`, bit.io). `bytes -> x` is rejected with an explicit message.
#[cfg(test)]
mod bit_import_tests {
    use super::*;
    use ast::{ImportKind, ImportLinkKind};

    fn first_import(src: &str) -> ImportKind {
        let result = parse(src, "test.h#");
        assert!(!result.has_errors(), "unexpected parse errors: {}", result.render_errors());
        result.module.imports.first().expect("no import parsed").0.clone()
    }

    #[test]
    fn plain_bit_import() {
        match first_import("use \"bit -> mold\"\nfn main() is end\n") {
            ImportKind::BitRepo { name, version, alias, link } => {
                assert_eq!(name, "mold");
                assert_eq!(version, None);
                assert_eq!(alias, None);
                assert_eq!(link, ImportLinkKind::Static);
            }
            other => panic!("expected BitRepo, got {:?}", other),
        }
    }

    #[test]
    fn bit_import_with_alias_and_release_version() {
        match first_import("use \"bit -> tui/1.0.2\" from \"t\"\nfn main() is end\n") {
            ImportKind::BitRepo { name, version, alias, .. } => {
                assert_eq!(name, "tui");
                assert_eq!(version.as_deref(), Some("1.0.2"));
                assert_eq!(alias.as_deref(), Some("t"));
            }
            other => panic!("expected BitRepo, got {:?}", other),
        }
    }

    #[test]
    fn bit_import_with_tag_or_commit_version() {
        for (spec, want) in [("mold/v1.0", "v1.0"), ("mold/a1b2c3d4e5f6", "a1b2c3d4e5f6")] {
            let src = format!("use \"bit -> {}\"\nfn main() is end\n", spec);
            match first_import(&src) {
                ImportKind::BitRepo { name, version, .. } => {
                    assert_eq!(name, "mold");
                    assert_eq!(version.as_deref(), Some(want));
                }
                other => panic!("expected BitRepo, got {:?}", other),
            }
        }
    }

    #[test]
    fn dynamic_bit_import() {
        match first_import("dynamic use \"bit -> mold\"\nfn main() is end\n") {
            ImportKind::BitRepo { link, .. } => assert_eq!(link, ImportLinkKind::Dynamic),
            other => panic!("expected BitRepo, got {:?}", other),
        }
    }

    #[test]
    fn dynamic_std_is_still_rejected() {
        let result = parse("dynamic use \"std -> io\"\nfn main() is end\n", "test.h#");
        assert!(result.has_errors());
        assert!(result.render_errors().contains("bit"));
    }

    #[test]
    fn bytes_import_is_removed_with_a_helpful_error() {
        let result = parse("use \"bytes -> scanner\"\nfn main() is end\n", "test.h#");
        assert!(result.has_errors());
        let rendered = result.render_errors();
        assert!(rendered.contains("bytes"), "{}", rendered);
        assert!(rendered.contains("use \"bit -> scanner\""), "{}", rendered);
    }

    #[test]
    fn bit_prefix_is_not_confused_with_other_heads() {
        // `bitmap` is not `bit`; it is simply not a known import kind.
        let result = parse("use \"bitmap -> x\"\nfn main() is end\n", "test.h#");
        assert!(result.has_errors());
    }
}
