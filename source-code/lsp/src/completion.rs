use hsharp_parser::ast::Item;
use lsp_types::{CompletionItem, CompletionItemKind};

const KEYWORDS: &[&str] = &[
    "fn", "let", "mut", "struct", "enum", "trait", "impl", "return",
    "if", "is", "else", "elsif", "end", "match", "while", "for", "in",
    "do", "break", "continue", "true", "false", "nil", "pub", "unsafe",
    "extern", "mod", "use", "using", "async", "await", "arena", "manual",
];

const BUILTINS: &[(&str, &str)] = &[
    ("write",              "write(value: string)"),
    ("print",              "print(value: string)"),
    ("to_string",          "to_string(value: any) -> string"),
    ("string_len",         "string_len(s: string) -> int"),
    ("string_slice",       "string_slice(s: string, start: int, end: int) -> string"),
    ("string_starts_with", "string_starts_with(s: string, prefix: string) -> bool"),
    ("string_ends_with",   "string_ends_with(s: string, suffix: string) -> bool"),
    ("string_split",       "string_split(s: string, sep: string) -> [string]"),
    ("string_replace",     "string_replace(s: string, from: string, to: string) -> string"),
    ("string_trim",        "string_trim(s: string) -> string"),
    ("array_len",          "array_len(a: [T]) -> int"),
    ("exit",               "exit(code: int)"),
    ("panic",              "panic(message: string)"),
];

pub fn builtin_completions() -> Vec<CompletionItem> {
    let mut items: Vec<CompletionItem> = KEYWORDS.iter().map(|k| CompletionItem {
        label: k.to_string(),
        kind: Some(CompletionItemKind::KEYWORD),
        ..Default::default()
    }).collect();
    items.extend(BUILTINS.iter().map(|(name, sig)| CompletionItem {
        label: name.to_string(),
        detail: Some(sig.to_string()),
        kind: Some(CompletionItemKind::FUNCTION),
        ..Default::default()
    }));
    // `using "<edition>"` — one completion per supported edition, newest first.
    items.extend(hsharp_parser::edition::Edition::ALL.iter().rev().map(|e| CompletionItem {
        label: format!("using \"{}\"", e.as_str()),
        detail: Some(format!("H# edition {} — {}", e.as_str(), e.summary())),
        kind: Some(CompletionItemKind::SNIPPET),
        ..Default::default()
    }));
    items
}

pub fn completions(text: &str) -> Vec<CompletionItem> {
    let mut items = builtin_completions();
    if let Some(module) = crate::diagnostics::parse_ok(text) {
        for item in &module.items {
            match item {
                Item::FnDef(f) => {
                    let params = f.params.iter()
                        .map(|p| format!("{}: {}", p.name, crate::symbols::type_name(&p.ty)))
                        .collect::<Vec<_>>().join(", ");
                    items.push(CompletionItem {
                        label: f.name.clone(),
                        detail: Some(format!("fn({})", params)),
                        kind: Some(CompletionItemKind::FUNCTION),
                        ..Default::default()
                    });
                }
                Item::StructDef(s) => {
                    items.push(CompletionItem {
                        label: s.name.clone(),
                        kind: Some(CompletionItemKind::STRUCT),
                        ..Default::default()
                    });
                }
                Item::EnumDef(e) => {
                    items.push(CompletionItem {
                        label: e.name.clone(),
                        kind: Some(CompletionItemKind::ENUM),
                        ..Default::default()
                    });
                }
                Item::ConstDef { name, ty, .. } => {
                    items.push(CompletionItem {
                        label: name.clone(),
                        detail: ty.as_ref().map(crate::symbols::type_name),
                        kind: Some(CompletionItemKind::CONSTANT),
                        ..Default::default()
                    });
                }
                _ => {}
            }
        }
    }
    items
}

#[cfg(test)]
mod edition_completion_tests {
    use super::*;

    #[test]
    fn offers_using_for_every_supported_edition() {
        let labels: Vec<String> = builtin_completions().into_iter().map(|i| i.label).collect();
        for e in hsharp_parser::edition::Edition::ALL {
            assert!(labels.contains(&format!("using \"{}\"", e.as_str())), "{:?}", labels);
        }
        assert!(labels.contains(&"using".to_string()));
    }
}
