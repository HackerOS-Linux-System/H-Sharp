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
                return Some(make_hover(sig));
            }
            Item::StructDef(s) if span_contains(&s.span, line, col) => {
                let fields = s.fields.iter()
                    .map(|fd| format!("    {}: {}", fd.name, crate::symbols::type_name(&fd.ty)))
                    .collect::<Vec<_>>().join("\n");
                let sig = format!("struct {} is\n{}\nend", s.name, fields);
                return Some(make_hover(sig));
            }
            _ => {}
        }
    }
    None
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
