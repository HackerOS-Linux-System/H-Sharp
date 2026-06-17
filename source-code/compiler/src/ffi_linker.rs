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
    match ext.lang {
        ExternLang::Python => {
            // No link flags — Python externs are compiled to `hsh_py_eval`
            // trampolines (codegen.rs::compile_python_trampoline), which
            // call `python3` as a subprocess. Nothing to link here.
            return;
        }
        ExternLang::Rust => {
            // Rust staticlibs need --whole-archive (see module doc) —
            // handled specially regardless of Static/Dynamic, since a
            // "dynamic" Rust cdylib (.so) doesn't need whole-archive but a
            // staticlib (.a, the common case for `extern static [rust, ...]`)
            // does.
            match (&ext.library, ext.link_kind.clone()) {
                (Some(lib), ExternLinkKind::Static) => {
                    flags.rust_whole_archive_libs.push(sanitize_lib_name(lib));
                    return;
                }
                (Some(lib), ExternLinkKind::Dynamic) => {
                    // Rust cdylib (.so) — normal dynamic linking, no
                    // whole-archive needed (dynamic symbol tables aren't
                    // subject to --gc-sections the same way).
                    flags.dynamic_libs.push(sanitize_lib_name(lib));
                    return;
                }
                (None, _) => {
                    // No library named — the symbol must already be
                    // available from elsewhere (e.g. linked in via another
                    // extern block, or the H# binary itself provides it).
                    // Record for `bytes check`/diagnostics but emit no
                    // link flag (there's nothing to point `-l` at).
                    flags.rust_libs.push(format!(
                        "(no library specified for `extern static [rust]` — \
declared fn(s) must be provided by another linked library)"
                    ));
                    return;
                }
            }
        }
        ExternLang::C | ExternLang::Cpp => {} // fall through to the generic C/C++ handling below
    }

    match ext.link_kind.clone() {
        ExternLinkKind::Static => {
            // extern static [c, "ssl"] -> -Wl,-Bstatic -lssl -Wl,-Bdynamic
            // extern static [c]        -> declared fns resolved from libc /
            //                              an already-linked object — no flag.
            if let Some(lib) = &ext.library {
                flags.static_libs.push(sanitize_lib_name(lib));
            }
            if matches!(ext.lang, ExternLang::Cpp) {
                flags.dynamic_libs.push("stdc++".to_string());
                flags.dynamic_libs.dedup();
            }
        }
        ExternLinkKind::Dynamic => {
            // extern dynamic [c, "ssl"] -> -lssl
            if let Some(lib) = &ext.library {
                flags.dynamic_libs.push(sanitize_lib_name(lib));
            }
            // C++ dynamic: always link stdc++
            if matches!(ext.lang, ExternLang::Cpp) {
                flags.dynamic_libs.push("stdc++".to_string());
                flags.dynamic_libs.dedup();
            }
        }
    }
}

/// Normalize a library name from H# source (`"libssl.so"`, `"libssl"`,
/// `"ssl.a"`, `"ssl"`) down to the bare name `cc -l<name>` expects.
fn sanitize_lib_name(lib: &str) -> String {
    lib.trim_start_matches("lib")
    .trim_end_matches(".a")
    .trim_end_matches(".so")
    .to_string()
}

/// All link flags derived from extern blocks
#[derive(Debug, Default, Clone)]
pub struct LinkFlags {
    /// -l<name> for static archives (C/C++; wrapped in -Bstatic/-Bdynamic)
    pub static_libs:  Vec<String>,
    /// -l<name> for dynamic shared libs (C/C++/Rust cdylib)
    pub dynamic_libs: Vec<String>,
    /// -l<name> for Rust staticlibs, linked --whole-archive (see module doc)
    pub rust_whole_archive_libs: Vec<String>,
    /// Diagnostic notes for `extern` blocks that produce no link flag
    /// (e.g. `extern static [rust]` with no library named).
    pub rust_libs: Vec<String>,
}

impl LinkFlags {
    /// Generate cc/gcc command line arguments
    pub fn to_cc_args(&self) -> Vec<String> {
        let mut args = Vec::new();

        // Static C/C++ libs: -Wl,-Bstatic -l<name> -Wl,-Bdynamic
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

        // Rust staticlibs: -Wl,--whole-archive -l<name> -Wl,--no-whole-archive
        // (see module doc for why plain -l<name> is insufficient for Rust)
        if !self.rust_whole_archive_libs.is_empty() {
            args.push("-Wl,--whole-archive".to_string());
            for lib in &self.rust_whole_archive_libs {
                args.push(format!("-l{}", lib));
            }
            args.push("-Wl,--no-whole-archive".to_string());
        }

        args
    }

    pub fn is_empty(&self) -> bool {
        self.static_libs.is_empty()
        && self.dynamic_libs.is_empty()
        && self.rust_whole_archive_libs.is_empty()
        && self.rust_libs.is_empty()
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
    if !flags.rust_whole_archive_libs.is_empty() {
        parts.push(format!("rust (whole-archive): {}", flags.rust_whole_archive_libs.join(", ")));
    }
    if !flags.rust_libs.is_empty() {
        parts.push(format!("rust notes: {}", flags.rust_libs.len()));
    }
    parts.join(" | ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dynamic_lib_flags() {
        // extern dynamic [c, "libssl"] -> -lssl
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
        // extern static [c, "libsqlite3"] -> -Wl,-Bstatic -lsqlite3 -Wl,-Bdynamic
        let flags = LinkFlags {
            static_libs: vec!["sqlite3".into()],
            ..Default::default()
        };
        let args = flags.to_cc_args();
        assert!(args.contains(&"-lsqlite3".to_string()));
        assert!(args.iter().any(|a| a.contains("Bstatic")));
    }

    #[test]
    fn test_rust_whole_archive() {
        // extern static [rust, "mylib"] -> --whole-archive -lmylib --no-whole-archive
        let flags = LinkFlags {
            rust_whole_archive_libs: vec!["mylib".into()],
            ..Default::default()
        };
        let args = flags.to_cc_args();
        assert!(args.contains(&"-lmylib".to_string()));
        assert!(args.iter().any(|a| a.contains("--whole-archive")));
        assert!(args.iter().any(|a| a.contains("--no-whole-archive")));
    }

}
