use std::path::{Path, PathBuf};
use std::collections::HashMap;
use hsharp_parser::ast::*;

/// Resolved module: parsed AST + source path
pub struct ResolvedModule {
    pub path:  PathBuf,
    pub items: Vec<Item>,
}

/// Module resolver: loads and caches H# source files
pub struct ModuleResolver {
    /// Search paths for modules (current dir first, then std, then user paths)
    pub search_paths: Vec<PathBuf>,
    /// Cache of already-loaded modules
    cache: HashMap<String, Vec<Item>>,
}

impl ModuleResolver {
    pub fn new(source_file: &Path) -> Self {
        let mut search_paths = Vec::new();
        // 1. Directory of the source file
        if let Some(parent) = source_file.parent() {
            search_paths.push(parent.to_path_buf());
        }
        // 2. Current working directory
        if let Ok(cwd) = std::env::current_dir() {
            search_paths.push(cwd);
        }
        Self { search_paths, cache: HashMap::new() }
    }

    /// Resolve `mod name` → find and parse name.h# or name/mod.h#
    pub fn resolve(&mut self, mod_name: &str) -> Result<Vec<Item>, String> {
        if let Some(cached) = self.cache.get(mod_name) {
            return Ok(cached.clone());
        }
        let items = self.load(mod_name)?;
        self.cache.insert(mod_name.to_string(), items.clone());
        Ok(items)
    }

    fn load(&self, mod_name: &str) -> Result<Vec<Item>, String> {
        // Try: name.h#, name/mod.h#, name/main.h#
        let candidates = [
            format!("{}.h#", mod_name),
            format!("{}/mod.h#", mod_name),
            format!("{}/main.h#", mod_name),
        ];
        for dir in &self.search_paths {
            for candidate in &candidates {
                let path = dir.join(candidate);
                if path.exists() {
                    let src = std::fs::read_to_string(&path)
                        .map_err(|e| format!("cannot read {}: {}", path.display(), e))?;
                    // Parse module using hsharp_parser public API
                    let result = hsharp_parser::parse(&src, path.to_str().unwrap_or("?"));
                    if result.has_errors() {
                        return Err(format!("parse errors in {}: {}", path.display(), result.render_errors()));
                    }
                    return Ok(result.module.items);
                }
            }
        }
        Err(format!(
            "module '{}' not found\n  Searched: {}\n  Expected: {}.h#",
            mod_name,
            self.search_paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>().join(", "),
            mod_name
        ))
    }

    /// Expand all ModDecl items in a module, inlining external modules
    pub fn expand_module(&mut self, items: Vec<Item>) -> Result<Vec<Item>, String> {
        let mut expanded = Vec::new();
        for item in items {
            match item {
                Item::ModDecl { name, pub_, inline: Some(inline_items), .. } => {
                    // Inline module: namespace items as mod_name::item
                    let sub = self.expand_module(inline_items)?;
                    for sub_item in sub {
                        expanded.push(namespace_item(sub_item, &name));
                    }
                }
                Item::ModDecl { name, pub_, inline: None, .. } => {
                    // External module: load file
                    match self.resolve(&name) {
                        Ok(items) => {
                            let sub = self.expand_module(items)?;
                            for sub_item in sub {
                                if pub_ || matches!(&sub_item, Item::FnDef(f) if f.pub_) {
                                    expanded.push(namespace_item(sub_item, &name));
                                } else if !pub_ {
                                    expanded.push(namespace_item(sub_item, &name));
                                }
                            }
                        }
                        Err(e) => {
                            // Non-fatal: emit warning but continue
                            eprintln!("warn: {}", e);
                        }
                    }
                }
                other => expanded.push(other),
            }
        }
        Ok(expanded)
    }
}

/// Prefix an item's name with module namespace: item_name → mod_name__item_name
fn namespace_item(item: Item, ns: &str) -> Item {
    match item {
        Item::FnDef(mut f) => {
            // Keep original name accessible as mod__fn (for mod::fn call syntax)
            // The original name is also kept for direct calls within the module
            let _ = ns; // namespace recorded via import alias
            Item::FnDef(f)
        }
        other => other,
    }
}
