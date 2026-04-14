use hsharp_parser::ast::{Module, Item, ExternBlock, ExternLinkKind, ExternLang};

/// Collect all link flags from extern blocks in a module
pub fn collect_link_flags(module: &Module) -> LinkFlags {
    let mut flags = LinkFlags::default();

    for item in &module.items {
        if let Item::Extern(ext) = item {
            process_extern_block(ext, &mut flags);
        }
    }

    flags
}

fn process_extern_block(ext: &ExternBlock, flags: &mut LinkFlags) {
    match ext.link_kind {
        ExternLinkKind::Static => {
            // extern static [c, "libssl"] → -lssl -Bstatic
            // extern static [c]           → link against declared fn names
            if let Some(lib) = &ext.library {
                let lib_name = lib
                    .trim_start_matches("lib")
                    .trim_end_matches(".a")
                    .trim_end_matches(".so");
                flags.static_libs.push(lib_name.to_string());
            } else {
                // No explicit lib — functions resolved from object files
                // (typical for Rust static libs compiled separately)
                match ext.lang {
                    ExternLang::Rust => flags.rust_libs.push("(extern rust)".into()),
                    ExternLang::C    => {} // libc always linked
                    ExternLang::Cpp  => flags.dynamic_libs.push("stdc++".to_string()),
                }
            }
        }
        ExternLinkKind::Dynamic => {
            // extern dynamic [c, "libssl"] → -lssl
            if let Some(lib) = &ext.library {
                let lib_name = lib
                    .trim_start_matches("lib")
                    .trim_end_matches(".so")
                    .trim_end_matches(".a");
                flags.dynamic_libs.push(lib_name.to_string());
            }
            // C++ dynamic: always link stdc++
            if matches!(ext.lang, ExternLang::Cpp) {
                flags.dynamic_libs.push("stdc++".to_string());
                flags.dynamic_libs.dedup();
            }
        }
    }
}

/// All link flags derived from extern blocks
#[derive(Debug, Default, Clone)]
pub struct LinkFlags {
    /// -l<name> for static archives
    pub static_libs:  Vec<String>,
    /// -l<name> for dynamic shared libs
    pub dynamic_libs: Vec<String>,
    /// Rust static lib paths
    pub rust_libs:    Vec<String>,
}

impl LinkFlags {
    /// Generate cc/gcc command line arguments
    pub fn to_cc_args(&self) -> Vec<String> {
        let mut args = Vec::new();

        // Static libs: -Wl,-Bstatic -l<name> -Wl,-Bdynamic
        if !self.static_libs.is_empty() {
            args.push("-Wl,-Bstatic".to_string());
            for lib in &self.static_libs {
                args.push(format!("-l{}", lib));
            }
            args.push("-Wl,-Bdynamic".to_string());
        }

        // Dynamic libs: -l<name>
        for lib in &self.dynamic_libs {
            args.push(format!("-l{}", lib));
        }

        args
    }

    pub fn is_empty(&self) -> bool {
        self.static_libs.is_empty() && self.dynamic_libs.is_empty() && self.rust_libs.is_empty()
    }
}

/// Generate a summary string for display
pub fn describe_flags(flags: &LinkFlags) -> String {
    if flags.is_empty() { return String::new(); }
    let mut parts = Vec::new();
    if !flags.static_libs.is_empty() {
        parts.push(format!("static: {}", flags.static_libs.join(", ")));
    }
    if !flags.dynamic_libs.is_empty() {
        parts.push(format!("dynamic: {}", flags.dynamic_libs.join(", ")));
    }
    if !flags.rust_libs.is_empty() {
        parts.push(format!("rust: {}", flags.rust_libs.len()));
    }
    parts.join(" | ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dynamic_lib_flags() {
        // extern dynamic [c, "libssl"] → -lssl
        let flags = LinkFlags {
            dynamic_libs: vec!["ssl".into(), "crypto".into()],
            ..Default::default()
        };
        let args = flags.to_cc_args();
        assert!(args.contains(&"-lssl".to_string()));
        assert!(args.contains(&"-lcrypto".to_string()));
    }

    #[test]
    fn test_static_lib_flags() {
        // extern static [c, "libsqlite3"] → -Wl,-Bstatic -lsqlite3 -Wl,-Bdynamic
        let flags = LinkFlags {
            static_libs: vec!["sqlite3".into()],
            ..Default::default()
        };
        let args = flags.to_cc_args();
        assert!(args.contains(&"-lsqlite3".to_string()));
        assert!(args.iter().any(|a| a.contains("Bstatic")));
    }
}
