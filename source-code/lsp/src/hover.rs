use hsharp_parser::ast::Item;
use lsp_types::{Hover, HoverContents, MarkupContent, MarkupKind, Position};

pub fn hover_at(text: &str, pos: Position) -> Option<Hover> {
    let module = crate::diagnostics::parse_ok(text)?;
    // LSP positions are 0-indexed; H#'s spans are 1-indexed — see
    // diagnostics.rs's `to_lsp_position` doc comment for why this
    // conversion direction matters and is centralized in spirit (this is
    // the one other place in the crate doing it, in reverse).
    let line = pos.line as usize + 1;
    let col  = pos.character as usize + 1;

    for item in &module.items {
        match item {
            Item::FnDef(f) if span_contains(&f.span, line, col) => {
                let params = f.params.iter()
                    .map(|p| format!("{}: {}", p.name, crate::symbols::type_name(&p.ty)))
                    .collect::<Vec<_>>().join(", ");
                let ret = f.return_type.as_ref().map(crate::symbols::type_name).unwrap_or_else(|| "void".to_string());
                let sig = format!("fn {}({}) -> {}", f.name, params, ret);
                return Some(make_hover_doc(sig, module.doc_for_line(f.span.start.line)));
            }
            Item::StructDef(s) if span_contains(&s.span, line, col) => {
                let fields = s.fields.iter()
                    .map(|fd| format!("    {}: {}", fd.name, crate::symbols::type_name(&fd.ty)))
                    .collect::<Vec<_>>().join("\n");
                let sig = format!("struct {} is\n{}\nend", s.name, fields);
                return Some(make_hover_doc(sig, module.doc_for_line(s.span.start.line)));
            }
            Item::ConstDef { name, ty, span, .. } if span_contains(span, line, col) => {
                let ty_str = ty.as_ref().map(crate::symbols::type_name).unwrap_or_else(|| "?".to_string());
                let sig = format!("const {}: {}", name, ty_str);
                return Some(make_hover_doc(sig, module.doc_for_line(span.start.line)));
            }
            _ => {}
        }
    }
    None
}

/// Signature in a code block, followed by the item's `///` documentation
/// (Markdown) when it has any.
fn make_hover_doc(code: String, doc: Option<&str>) -> Hover {
    let mut h = make_hover(code);
    if let (Some(doc), HoverContents::Markup(m)) = (doc, &mut h.contents) {
        m.value = format!("{}\n\n---\n\n{}", m.value, doc);
    }
    h
}

fn make_hover(code: String) -> Hover {
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```hsharp\n{}\n```", code),
        }),
        range: None,
    }
}

fn span_contains(span: &hsharp_parser::span::Span, line: usize, col: usize) -> bool {
    if line < span.start.line || line > span.end.line { return false; }
    if line == span.start.line && col < span.start.col { return false; }
    if line == span.end.line && col > span.end.col { return false; }
    true
}

#[cfg(test)]
mod doc_hover_tests {
    use super::*;

    #[test]
    fn hover_shows_triple_slash_docs() {
        let src = "/// Adds two numbers.\nfn add(a: int, b: int) -> int is\n    return a + b\nend\n";
        let h = hover_at(src, Position { line: 1, character: 4 }).expect("hover");
        let HoverContents::Markup(m) = h.contents else { panic!() };
        assert!(m.value.contains("fn add(a: int, b: int) -> int"), "{}", m.value);
        assert!(m.value.contains("Adds two numbers."), "{}", m.value);
    }

    #[test]
    fn hover_without_docs_is_unchanged() {
        let src = "fn add(a: int, b: int) -> int is\n    return a + b\nend\n";
        let h = hover_at(src, Position { line: 0, character: 4 }).expect("hover");
        let HoverContents::Markup(m) = h.contents else { panic!() };
        assert!(!m.value.contains("---"));
    }
}
