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
    let mut doc_lines: Vec<lexer::DocLine> = Vec::new();
    let (tokens, lex_errors) = match lexer.tokenize() {
        Ok(t) => { doc_lines = lexer.doc_lines().to_vec(); (t, vec![]) }
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

    let doc_comments = group_doc_comments(&doc_lines, &tokens);
    let mut p = parser::Parser::new(tokens, source.to_string(), file.to_string());
    let mut module = p.parse_module();
    module.doc_comments = doc_comments;
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

/// Merge consecutive `///` lines into [`ast::DocComment`] blocks and point
/// each at the line of the first real token that follows it.
fn group_doc_comments(lines: &[lexer::DocLine], tokens: &[lexer::Token]) -> Vec<ast::DocComment> {
    let mut out: Vec<ast::DocComment> = Vec::new();
    let mut i = 0;
    while i < lines.len() {
        let first = &lines[i];
        let mut j = i;
        let mut text = vec![first.text.clone()];
        // a block continues while the next `///` is on the very next line
        while j + 1 < lines.len() && lines[j + 1].span.start.line == lines[j].span.end.line + 1 {
            j += 1;
            text.push(lines[j].text.clone());
        }
        let last = &lines[j];
        let end_off = last.span.end.offset;
        let target_line = tokens
            .iter()
            .find(|t| {
                t.span.start.offset >= end_off
                    && !matches!(t.kind, lexer::TokenKind::Newline | lexer::TokenKind::EOF)
            })
            .map(|t| t.span.start.line);
        out.push(ast::DocComment {
            text: text.join("\n"),
            span: first.span.merge(&last.span),
            target_line,
        });
        i = j + 1;
    }
    out
}

#[cfg(test)]
mod comment_tests {
    use super::*;

    fn ok(src: &str) -> ParseResult {
        let r = parse(src, "t.h#");
        assert!(!r.has_errors(), "{}", r.render_errors());
        r
    }

    #[test]
    fn doc_comments_before_items_are_collected_and_attached() {
        let r = ok("/// Adds two numbers.\n/// Both are ints.\nfn add(a: int, b: int) -> int is\n    return a + b\nend\n\n/// Entry point.\nfn main() is\nend\n");
        assert_eq!(r.module.doc_comments.len(), 2);
        assert_eq!(r.module.doc_comments[0].text, "Adds two numbers.\nBoth are ints.");
        assert_eq!(r.module.doc_comments[0].target_line, Some(3));
        assert_eq!(r.module.doc_for_line(3), Some("Adds two numbers.\nBoth are ints."));
        assert_eq!(r.module.doc_for_line(8), Some("Entry point."));
        assert_eq!(r.module.doc_for_line(1), None);
    }

    #[test]
    fn doc_comments_may_sit_on_fields_variants_and_in_bodies() {
        ok("/// A point\nstruct P is\n    /// x coord\n    x: int\n    /// y coord\n    y: int\nend\n\nenum E is\n    /// first\n    A\n    /// second\n    B\nend\n\nfn main() is\n    /// not an item, still harmless\n    let a: int = 1\nend\n");
    }

    #[test]
    fn four_slashes_is_a_plain_comment_not_a_doc() {
        let r = parse("//// banner \\\\\nfn main() is\nend\n", "t.h#");
        assert!(r.module.doc_comments.is_empty());
    }

    #[test]
    fn multiline_comment_is_ignored_even_with_keywords_inside() {
        let r = ok("// this is a\n   multi-line comment: fn end is struct\n   \"strings\" too \\\\\nfn main() is\n    write(\"x\")\nend\n");
        assert_eq!(r.module.items.len(), 1);
    }

    #[test]
    fn multiline_comment_inline_and_trailing() {
        ok("fn main() is\n    // inline \\\\ write(\"y\")\nend\n");
        ok("fn main() is\n    write(\"a\") // trailing \\\\\nend\n");
    }

    #[test]
    fn comment_markers_inside_strings_are_not_comments() {
        let r = ok("fn main() is\n    write(\"http://x.y /// not doc ;; nor this\")\nend\n");
        assert!(r.module.doc_comments.is_empty());
    }

    #[test]
    fn unterminated_multiline_comment_is_an_error_at_its_start() {
        let r = parse("fn main() is\nend\n// never closed\nfn f() is\nend\n", "t.h#");
        assert!(r.has_errors());
        let msg = r.render_errors();
        assert!(msg.contains("unterminated block comment"), "{msg}");
        assert!(msg.contains(":3:1"), "{msg}");
    }

    #[test]
    fn line_numbers_after_a_multiline_comment_are_exact() {
        // the old lexer counted every newline inside `// … \\` twice
        let src = "// line 1\nline 2 \\\\\nfn main() is\n    let x: int = = 1\nend\n";
        let r = parse(src, "t.h#");
        assert!(r.has_errors());
        assert!(r.render_errors().contains(":4:"), "{}", r.render_errors());
    }
}
