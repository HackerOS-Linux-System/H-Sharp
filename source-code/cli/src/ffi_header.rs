use colored::Colorize;
use std::path::PathBuf;

/// `hsharp ffi-header <file> [--lang c|rust]` — the concrete tool behind
/// the `StructByValueFfi` compile error's hint (`compiler::features`):
/// parses `file`, collects its struct definitions and every `extern`
/// block's function signatures, and prints a header showing the *real*
/// on-disk/in-memory layout H# actually uses (see
/// `compiler::ffi::struct_c_def`'s doc comment) — an `int64_t`/`i64` slot
/// per field, in declaration order, with a comment on each field
/// explaining how to correctly reinterpret it from C/Rust when it isn't
/// already a plain integer (float bit patterns, string/bytes pointers).
///
/// This intentionally does not try to guess a "natural" C layout (packed
/// `int32_t`/`double`/etc. widths) — that would describe a struct that
/// doesn't match what's actually in memory once by-pointer struct FFI is
/// in play, which is worse than describing the real (if unusual) layout
/// H# uses. See `features::LangFeature::StructByValueFfi`'s doc comment
/// for why by-*value* struct FFI is a hard error rather than attempting
/// that "natural layout" translation automatically.
pub fn run(file: PathBuf, lang: String) {
    let source = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{} {}: {}", "Error:".red().bold(), file.display(), e);
            std::process::exit(1);
        }
    };

    let result = hsharp_parser::parse(&source, &file.display().to_string());
    if result.has_errors() {
        eprint!("{}", result.render_errors());
        std::process::exit(1);
    }

    let mut structs: std::collections::HashMap<String, Vec<hsharp_parser::ast::StructField>> = std::collections::HashMap::new();
    let mut externs: Vec<hsharp_compiler::ffi::ExternBlock> = Vec::new();
    for item in &result.module.items {
        match item {
            hsharp_parser::ast::Item::StructDef(sd) => {
                structs.insert(sd.name.clone(), sd.fields.clone());
            }
            hsharp_parser::ast::Item::Extern(ext) => {
                externs.push(hsharp_compiler::ffi::ExternBlock::from(ext));
            }
            _ => {}
        }
    }

    if externs.is_empty() {
        println!("{} no `extern` blocks found in {}", "Note:".yellow().bold(), file.display());
        return;
    }

    let is_rust = matches!(lang.to_lowercase().as_str(), "rust" | "rs");
    let mut wrote_any = false;
    for block in &externs {
        if block.lang == hsharp_compiler::ffi::ExternLang::Python {
            // The Python bridge marshals through strings/CPython objects,
            // not a C ABI struct layout — nothing for a header to say.
            continue;
        }
        wrote_any = true;
        if is_rust {
            println!("{}", hsharp_compiler::ffi::rust_extern_block_with_structs(&block.functions, &structs));
        } else {
            println!("{}", hsharp_compiler::ffi::c_header_block_with_structs(&block.functions, &structs));
        }
        println!();
    }

    if !wrote_any {
        println!("{} every `extern` block in {} is `[python]` — no C/Rust header to generate", "Note:".yellow().bold(), file.display());
    }
}
