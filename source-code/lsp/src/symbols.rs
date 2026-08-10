use hsharp_parser::ast::{Item, TypeExpr};
use lsp_types::{DocumentSymbol, DocumentSymbolResponse, Position, Range, SymbolKind};
#[allow(deprecated)] // `DocumentSymbol::deprecated` has no non-deprecated replacement field yet in lsp-types
pub fn document_symbols(text: &str) -> DocumentSymbolResponse {
    let Some(module) = crate::diagnostics::parse_ok(text) else {
        return DocumentSymbolResponse::Nested(vec![]);
    };
    let syms = module.items.iter().filter_map(item_to_symbol).collect();
    DocumentSymbolResponse::Nested(syms)
}

fn item_to_symbol(item: &Item) -> Option<DocumentSymbol> {
    let (name, kind, span, detail, children) = match item {
        Item::FnDef(f) => {
            let params = f.params.iter().map(|p| type_name(&p.ty)).collect::<Vec<_>>().join(", ");
            let ret = f.return_type.as_ref().map(type_name).unwrap_or_else(|| "void".to_string());
            (f.name.clone(), SymbolKind::FUNCTION, &f.span, Some(format!("({}) -> {}", params, ret)), vec![])
        }
        Item::StructDef(s) => {
            let fields: Vec<DocumentSymbol> = s.fields.iter().map(|field| {
                #[allow(deprecated)]
                DocumentSymbol {
                    name: field.name.clone(),
                    detail: Some(type_name(&field.ty)),
                    kind: SymbolKind::FIELD,
                    tags: None,
                    deprecated: None,
                    range: span_to_range(&field.span),
                    selection_range: span_to_range(&field.span),
                    children: None,
                }
            }).collect();
            (s.name.clone(), SymbolKind::STRUCT, &s.span, None, fields)
        }
        Item::EnumDef(e) => (e.name.clone(), SymbolKind::ENUM, &e.span, None, vec![]),
        Item::TraitDef(t) => (t.name.clone(), SymbolKind::INTERFACE, &t.span, None, vec![]),
        Item::ImplBlock(_) | Item::TypeAlias { .. } | Item::Extern(_) | Item::ModDecl { .. } => return None,
    };

    #[allow(deprecated)]
    Some(DocumentSymbol {
        name,
        detail,
        kind,
        tags: None,
        deprecated: None,
        range: span_to_range(span),
        selection_range: span_to_range(span),
        children: if children.is_empty() { None } else { Some(children) },
    })
}

fn span_to_range(span: &hsharp_parser::span::Span) -> Range {
    Range {
        start: Position { line: span.start.line.saturating_sub(1) as u32, character: span.start.col.saturating_sub(1) as u32 },
        end:   Position { line: span.end.line.saturating_sub(1) as u32,   character: span.end.col.saturating_sub(1) as u32 },
    }
}

/// A short, best-effort rendering of a `TypeExpr` for hover text / symbol
/// details — not meant to be a fully general pretty-printer (H#'s own
/// diagnostics already have one for that, `HType::display()` in
/// `hsharp-typecheck`, which operates on the *checked* type, not the raw
/// syntax tree — this one works directly off the AST so it's available
/// even when type-checking hasn't run, e.g. mid-edit).
pub fn type_name(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Void => "void".to_string(),
        TypeExpr::Bool => "bool".to_string(),
        TypeExpr::I8 => "i8".to_string(), TypeExpr::I16 => "i16".to_string(),
        TypeExpr::I32 => "i32".to_string(), TypeExpr::I64 => "int".to_string(),
        TypeExpr::I128 => "i128".to_string(),
        TypeExpr::U8 => "u8".to_string(), TypeExpr::U16 => "u16".to_string(),
        TypeExpr::U32 => "u32".to_string(), TypeExpr::U64 => "u64".to_string(),
        TypeExpr::U128 => "u128".to_string(),
        TypeExpr::F32 => "f32".to_string(), TypeExpr::F64 => "f64".to_string(),
        TypeExpr::String => "string".to_string(),
        TypeExpr::Bytes => "bytes".to_string(),
        TypeExpr::Named(n) => n.clone(),
        TypeExpr::Array(inner) => format!("[{}]", type_name(inner)),
        TypeExpr::Slice(inner, _) => format!("[{}]", type_name(inner)),
        TypeExpr::Optional(inner) => format!("{}?", type_name(inner)),
        TypeExpr::Ref(inner) => format!("ref {}", type_name(inner)),
        TypeExpr::RefMut(inner) => format!("ref mut {}", type_name(inner)),
        TypeExpr::Tuple(items) => format!("({})", items.iter().map(type_name).collect::<Vec<_>>().join(", ")),
        TypeExpr::Fn(params, ret) => format!("fn({}) -> {}",
            params.iter().map(type_name).collect::<Vec<_>>().join(", "), type_name(ret)),
        TypeExpr::Generic(name, args) => format!("{}<{}>", name, args.iter().map(type_name).collect::<Vec<_>>().join(", ")),
    }
}
