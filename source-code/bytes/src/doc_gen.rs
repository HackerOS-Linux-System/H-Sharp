#![allow(dead_code)]
use colored::*;
use std::fmt::Write as FmtWrite;
use std::path::Path;

pub fn generate_docs(extra: &[String], _verbose: bool) -> anyhow::Result<()> {
    println!();
    println!("  {}  H# Doc Generator", "bytes doc".cyan().bold());
    println!();

    let out_dir = extra.iter()
    .find(|s| !s.starts_with("--"))
    .map(|s| s.as_str())
    .unwrap_or("docs/generated");

    std::fs::create_dir_all(out_dir)?;

    let files = collect_hsharp_files();
    if files.is_empty() {
        println!("  {}", "No .h# files found.".dimmed());
        return Ok(());
    }

    let mut all_items: Vec<DocItem> = Vec::new();
    for file in &files {
        let src = match std::fs::read_to_string(file) {
            Ok(s)  => s,
            Err(e) => { eprintln!("  {} {}: {}", "warn:".yellow(), file, e); continue; }
        };
        all_items.extend(extract_doc_items(&src, file));
    }

    let index_html = render_index_html(&all_items);
    let index_path = Path::new(out_dir).join("index.html");
    std::fs::write(&index_path, &index_html)?;

    // Per-module pages
    let mut modules: std::collections::BTreeMap<String, Vec<&DocItem>> = Default::default();
    for item in &all_items { modules.entry(item.module.clone()).or_default().push(item); }
    for (module, items) in &modules {
        let page_html = render_module_html(module, items);
        let page_path = Path::new(out_dir).join(format!("{}.html", sanitise_filename(module)));
        std::fs::write(&page_path, &page_html)?;
    }

    println!(
        "  {} {} item(s) documented -> {}",
             "ok".green().bold(),
             all_items.len(),
             index_path.display().to_string().cyan(),
    );
    Ok(())
}

fn collect_hsharp_files() -> Vec<String> {
    for root in &["src", "std", "."] {
        if !Path::new(root).exists() { continue; }
        let found: Vec<_> = walkdir::WalkDir::new(root)
        .max_depth(5).into_iter().flatten()
        .filter(|e| {
            let p = e.path();
            e.file_type().is_file()
            && p.extension().map(|x| x == "h#" || x == "hsp").unwrap_or(false)
            && !p.starts_with("./build")
        })
        .map(|e| e.path().display().to_string())
        .collect();
        if !found.is_empty() { return found; }
    }
    Vec::new()
}

#[derive(Debug, Clone)]
pub struct DocItem {
    pub kind:        String,
    pub name:        String,
    pub signature:   String,
    pub doc:         String,
    pub module:      String,
    pub source_file: String,
    pub line:        usize,
}

fn extract_doc_items(src: &str, file: &str) -> Vec<DocItem> {
    let module = Path::new(file)
    .file_stem().and_then(|s| s.to_str()).unwrap_or("unknown").to_string();

    let lines: Vec<&str> = src.lines().collect();
    let mut items   = Vec::new();
    let mut doc_buf = String::new();
    let mut i       = 0usize;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.starts_with("///") {
            doc_buf.clear();
            while i < lines.len() && lines[i].trim().starts_with("///") {
                let doc_line = lines[i].trim().trim_start_matches("///").trim();
                if !doc_buf.is_empty() { doc_buf.push('\n'); }
                doc_buf.push_str(doc_line);
                i += 1;
            }
            while i < lines.len() && lines[i].trim().is_empty() { i += 1; }
            if i < lines.len() {
                let item_line = lines[i].trim();
                if let Some(item) = parse_item_signature(item_line, &doc_buf, &module, file, i + 1) {
                    items.push(item);
                }
            }
        } else {
            i += 1;
        }
    }
    items
}

fn parse_item_signature(line: &str, doc: &str, module: &str, file: &str, ln: usize) -> Option<DocItem> {
    let line = line.trim_start_matches("pub ");
    let (kind, name, sig) = if line.starts_with("fn ") {
        let name = line[3..].split('(').next()?.trim().to_string();
        ("fn".to_string(), name, line.to_string())
    } else if line.starts_with("struct ") {
        let name = line[7..].split_whitespace().next()?.to_string();
        ("struct".to_string(), name, line.to_string())
    } else if line.starts_with("enum ") {
        let name = line[5..].split_whitespace().next()?.to_string();
        ("enum".to_string(), name, line.to_string())
    } else if line.starts_with("trait ") {
        let name = line[6..].split_whitespace().next()?.to_string();
        ("trait".to_string(), name, line.to_string())
    } else { return None; };

    Some(DocItem { kind, name, signature: sig, doc: doc.to_string(),
        module: module.to_string(), source_file: file.to_string(), line: ln })
}

fn render_index_html(items: &[DocItem]) -> String {
    let mut html = String::new();
    let _ = writeln!(html, r#"<!DOCTYPE html>
    <html lang="en"><head><meta charset="UTF-8"><title>H# Documentation</title>
    <style>
    body{{font-family:'Segoe UI',sans-serif;background:#0d1117;color:#e6edf3;margin:0}}
    .header{{background:#161b22;padding:24px 40px;border-bottom:1px solid #30363d}}
    .header h1{{margin:0;color:#58a6ff;font-size:1.8rem}}
    .content{{padding:32px 40px;max-width:1100px;margin:0 auto}}
    .item{{background:#161b22;border:1px solid #30363d;border-radius:8px;margin:16px 0;padding:20px}}
    .item-kind{{font-size:.75rem;color:#79c0ff;text-transform:uppercase;letter-spacing:1px}}
    .item-name{{font-size:1.2rem;font-weight:bold;color:#f0f6fc;margin:4px 0}}
    .item-sig{{font-family:monospace;color:#d2a8ff;font-size:.9rem;background:#0d1117;padding:8px 12px;border-radius:4px;margin:8px 0}}
    .item-doc{{color:#c9d1d9;line-height:1.6;white-space:pre-wrap}}
    .ml{{color:#58a6ff;text-decoration:none}} .ml:hover{{text-decoration:underline}}
    h2{{color:#58a6ff;border-bottom:1px solid #30363d;padding-bottom:8px}}
    </style></head><body>
    <div class="header"><h1>H# Documentation</h1><p style="color:#8b949e">Generated by <code>bytes doc</code> — H# v0.7</p></div>
    <div class="content">"#);

    let mut modules: std::collections::BTreeMap<String, Vec<&DocItem>> = Default::default();
    for item in items { modules.entry(item.module.clone()).or_default().push(item); }

    for (module, mod_items) in &modules {
        let _ = writeln!(html,
                         "<h2><a class=\"ml\" href=\"{}.html\">{}</a> ({} items)</h2>",
                         sanitise_filename(module), escape_html(module), mod_items.len());
        for item in mod_items {
            let _ = writeln!(html,
                             "<div class=\"item\"><div class=\"item-kind\">{}</div>\
<div class=\"item-name\">{}</div>\
<div class=\"item-sig\">{}</div>\
<div class=\"item-doc\">{}</div></div>",
escape_html(&item.kind), escape_html(&item.name),
                             escape_html(&item.signature), escape_html(&item.doc));
        }
    }
    let _ = writeln!(html, "</div></body></html>");
    html
}

fn render_module_html(module: &str, items: &[&DocItem]) -> String {
    let mut html = String::new();
    let _ = writeln!(html,
                     "<!DOCTYPE html><html lang=\"en\"><head><meta charset=\"UTF-8\">\
<title>H# - {}</title></head><body style=\"font-family:sans-serif;background:#0d1117;color:#e6edf3;padding:32px\">\
<h1 style=\"color:#58a6ff\">{}</h1><p><a href=\"index.html\" style=\"color:#58a6ff\">Back to index</a></p>",
escape_html(module), escape_html(module));

    for item in items {
        let _ = writeln!(html,
                         "<div style=\"background:#161b22;border:1px solid #30363d;border-radius:8px;\
margin:16px 0;padding:20px\">\
<div style=\"color:#79c0ff;font-size:.75rem\">{}</div>\
<div style=\"color:#f0f6fc;font-weight:bold\">{}</div>\
<pre style=\"color:#d2a8ff;background:#0d1117;padding:8px;border-radius:4px\">{}</pre>\
<div style=\"color:#c9d1d9;white-space:pre-wrap\">{}</div></div>",
escape_html(&item.kind), escape_html(&item.name),
                         escape_html(&item.signature), escape_html(&item.doc));
    }
    let _ = writeln!(html, "</body></html>");
    html
}

fn escape_html(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

fn sanitise_filename(s: &str) -> String {
    s.chars().map(|c| if c.is_alphanumeric() || c == '_' || c == '-' { c } else { '_' }).collect()
}
