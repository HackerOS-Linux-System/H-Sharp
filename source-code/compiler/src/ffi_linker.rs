use hsharp_parser::ast::{Module, Item, ExternBlock, ExternLinkKind, ExternLang};

// ─── Public API ──────────────────────────────────────────────────────────────

/// Collect all linker flags from every `extern` block in `module`.
pub fn collect_link_flags(module: &Module) -> LinkFlags {
    let mut flags = LinkFlags::default();
    for item in &module.items {
        if let Item::Extern(ext) = item {
            process_extern_block(ext, &mut flags);
        }
    }
    flags.dedup();
    flags
}

// ─── Per-block processing ─────────────────────────────────────────────────────

fn process_extern_block(ext: &ExternBlock, flags: &mut LinkFlags) {
    match ext.lang {
        // ── Python: subprocess bridge, zero link flags ────────────────────
        ExternLang::Python => {
            // Python externs are compiled to `hsh_py_eval` trampolines in
            // codegen.rs — they call `python3` as a subprocess.
            // Nothing to link; record for diagnostics only.
            let note = match &ext.library {
                Some(lib) => format!("python[{}] — bridge, no link flag", lib),
                None      => "python — bridge, no link flag".to_string(),
            };
            flags.python_notes.push(note);
        }

        // ── Rust ──────────────────────────────────────────────────────────
        ExternLang::Rust => {
            match (&ext.library, &ext.link_kind) {
                (Some(lib), ExternLinkKind::Static) => {
                    // Rust staticlibs need --whole-archive so the linker
                    // does not GC symbols not directly referenced from H#.
                    flags.rust_whole_archive_libs.push(sanitize(lib));
                }
                (Some(lib), ExternLinkKind::Dynamic) => {
                    // Rust cdylib (.so) — normal dynamic link, no whole-archive.
                    flags.dynamic_libs.push(sanitize(lib));
                    flags.rpath_hints.push(format!("-Wl,-rpath,$ORIGIN"));
                }
                (None, ExternLinkKind::Static) => {
                    flags.diagnostics.push(
                        "extern static [rust]: no library name given — \
                         declared fn(s) must already be provided by another \
                         linked object (no -l flag emitted)".to_string()
                    );
                }
                (None, ExternLinkKind::Dynamic) => {
                    flags.diagnostics.push(
                        "extern dynamic [rust]: no library name given — \
                         symbol must be in an already-linked cdylib".to_string()
                    );
                }
            }
        }

        // ── C ─────────────────────────────────────────────────────────────
        ExternLang::C => {
            process_c_like(ext, flags, /*need_stdcpp=*/ false);
        }

        // ── C++ ───────────────────────────────────────────────────────────
        ExternLang::Cpp => {
            process_c_like(ext, flags, /*need_stdcpp=*/ true);
            // Always link stdc++ for C++ externs; deduplicated later.
            flags.dynamic_libs.push("stdc++".to_string());
        }
    }
}

/// Shared logic for C and C++ extern blocks.
fn process_c_like(ext: &ExternBlock, flags: &mut LinkFlags, need_stdcpp: bool) {
    match &ext.link_kind {
        ExternLinkKind::Static => {
            if let Some(lib) = &ext.library {
                let name = sanitize(lib);
                // Try pkg-config first so we pick up -I/-L flags too.
                if let Some(pc) = try_pkg_config_static(&name) {
                    flags.pkg_config_args.extend(pc);
                } else {
                    flags.static_libs.push(name);
                }
            }
            if need_stdcpp {
                flags.dynamic_libs.push("stdc++".to_string());
            }
        }
        ExternLinkKind::Dynamic => {
            if let Some(lib) = &ext.library {
                let name = sanitize(lib);
                if let Some(pc) = try_pkg_config_dynamic(&name) {
                    flags.pkg_config_args.extend(pc);
                } else {
                    flags.dynamic_libs.push(name);
                }
            }
            if need_stdcpp {
                flags.dynamic_libs.push("stdc++".to_string());
            }
        }
    }
}

// ─── pkg-config helpers ───────────────────────────────────────────────────────

/// Try `pkg-config --static --libs <name>` and return the flags if available.
fn try_pkg_config_static(name: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config")
        .args(["--static", "--libs", name])
        .output().ok()?;
    if !out.status.success() { return None; }
    let flags = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
    if flags.is_empty() { None } else { Some(flags) }
}

/// Try `pkg-config --libs <name>` and return the flags if available.
fn try_pkg_config_dynamic(name: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config")
        .args(["--libs", name])
        .output().ok()?;
    if !out.status.success() { return None; }
    let flags = String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
    if flags.is_empty() { None } else { Some(flags) }
}

// ─── Name sanitisation ────────────────────────────────────────────────────────

/// Strip `lib` prefix and `.a` / `.so` / `.dylib` / `.dll` suffix so that
/// `"libssl.so"`, `"libssl"`, `"ssl.a"`, `"ssl"` all become `"ssl"` —
/// the bare name that `cc -l<name>` / `ar` expects.
fn sanitize(lib: &str) -> String {
    lib.trim_start_matches("lib")
       .trim_end_matches(".a")
       .trim_end_matches(".so")
       .trim_end_matches(".dylib")
       .trim_end_matches(".dll")
       .to_string()
}

// ─── LinkFlags ────────────────────────────────────────────────────────────────

/// All link flags derived from a module's extern blocks.
#[derive(Debug, Default, Clone)]
pub struct LinkFlags {
    /// `-l<name>` wrapped in `-Wl,-Bstatic` / `-Wl,-Bdynamic` (C/C++).
    pub static_libs: Vec<String>,
    /// `-l<name>` (C/C++ dynamic, Rust cdylib).
    pub dynamic_libs: Vec<String>,
    /// `-Wl,--whole-archive -l<name> -Wl,--no-whole-archive` (Rust staticlib).
    pub rust_whole_archive_libs: Vec<String>,
    /// Raw flags from a successful `pkg-config` query (take priority over
    /// hand-built `-l` flags to pick up correct -L paths and version flags).
    pub pkg_config_args: Vec<String>,
    /// `-Wl,-rpath,...` hints for dynamic Rust cdylibs.
    pub rpath_hints: Vec<String>,
    /// Human-readable notes for Python bridge externs (no link flag emitted).
    pub python_notes: Vec<String>,
    /// Warnings / diagnostics for incomplete or ambiguous extern blocks.
    pub diagnostics: Vec<String>,
}

impl LinkFlags {
    /// Deduplicate all flag lists in-place (preserve first occurrence order).
    pub fn dedup(&mut self) {
        dedup_vec(&mut self.static_libs);
        dedup_vec(&mut self.dynamic_libs);
        dedup_vec(&mut self.rust_whole_archive_libs);
        dedup_vec(&mut self.pkg_config_args);
        dedup_vec(&mut self.rpath_hints);
    }

    /// Generate `cc` / `gcc` command-line arguments from collected flags.
    ///
    /// Order:
    ///  1. pkg-config flags (already include -L paths)
    ///  2. static C/C++ libs:   -Wl,-Bstatic -l<x> … -Wl,-Bdynamic
    ///  3. dynamic C/C++ libs:  -l<x> …
    ///  4. Rust staticlibs:     -Wl,--whole-archive -l<x> -Wl,--no-whole-archive
    ///  5. rpath hints
    pub fn to_cc_args(&self) -> Vec<String> {
        let mut args = Vec::new();

        // 1. pkg-config (already fully formed flags)
        args.extend(self.pkg_config_args.iter().cloned());

        // 2. Static C/C++ libs
        if !self.static_libs.is_empty() {
            args.push("-Wl,-Bstatic".to_string());
            for lib in &self.static_libs {
                args.push(format!("-l{}", lib));
            }
            args.push("-Wl,-Bdynamic".to_string());
        }

        // 3. Dynamic C/C++ / Rust cdylib
        for lib in &self.dynamic_libs {
            args.push(format!("-l{}", lib));
        }

        // 4. Rust staticlibs (--whole-archive)
        if !self.rust_whole_archive_libs.is_empty() {
            args.push("-Wl,--whole-archive".to_string());
            for lib in &self.rust_whole_archive_libs {
                args.push(format!("-l{}", lib));
            }
            args.push("-Wl,--no-whole-archive".to_string());
        }

        // 5. rpath hints
        args.extend(self.rpath_hints.iter().cloned());

        args
    }

    pub fn is_empty(&self) -> bool {
        self.static_libs.is_empty()
            && self.dynamic_libs.is_empty()
            && self.rust_whole_archive_libs.is_empty()
            && self.pkg_config_args.is_empty()
    }

    /// True if there are any diagnostics / warnings to surface.
    pub fn has_warnings(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// Print any diagnostics to stderr (called by the CLI after compilation).
    pub fn print_warnings(&self) {
        for d in &self.diagnostics {
            eprintln!("  \x1b[33mwarn\x1b[0m  [extern] {}", d);
        }
        for n in &self.python_notes {
            eprintln!("  \x1b[2mnote\x1b[0m  [extern] {}", n);
        }
    }
}

/// One-liner human summary for `--verbose` / `bytes check`.
pub fn describe_flags(flags: &LinkFlags) -> String {
    if flags.is_empty() && flags.diagnostics.is_empty() {
        return String::new();
    }
    let mut parts = Vec::new();
    if !flags.static_libs.is_empty() {
        parts.push(format!("static: {}", flags.static_libs.join(", ")));
    }
    if !flags.dynamic_libs.is_empty() {
        parts.push(format!("dynamic: {}", flags.dynamic_libs.join(", ")));
    }
    if !flags.rust_whole_archive_libs.is_empty() {
        parts.push(format!("rust(whole-archive): {}", flags.rust_whole_archive_libs.join(", ")));
    }
    if !flags.pkg_config_args.is_empty() {
        parts.push(format!("pkg-config: {} flag(s)", flags.pkg_config_args.len()));
    }
    if !flags.python_notes.is_empty() {
        parts.push(format!("python-bridge: {} block(s)", flags.python_notes.len()));
    }
    if !flags.diagnostics.is_empty() {
        parts.push(format!("warnings: {}", flags.diagnostics.len()));
    }
    parts.join(" | ")
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

fn dedup_vec(v: &mut Vec<String>) {
    let mut seen = std::collections::HashSet::new();
    v.retain(|s| seen.insert(s.clone()));
}

// ─── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn make_flags(static_libs: &[&str], dynamic_libs: &[&str], rust_wa: &[&str]) -> LinkFlags {
        LinkFlags {
            static_libs:             static_libs.iter().map(|s| s.to_string()).collect(),
            dynamic_libs:            dynamic_libs.iter().map(|s| s.to_string()).collect(),
            rust_whole_archive_libs: rust_wa.iter().map(|s| s.to_string()).collect(),
            ..Default::default()
        }
    }

    #[test]
    fn dynamic_c_flags() {
        let f = make_flags(&[], &["ssl", "crypto"], &[]);
        let args = f.to_cc_args();
        assert!(args.contains(&"-lssl".to_string()));
        assert!(args.contains(&"-lcrypto".to_string()));
        assert!(!args.iter().any(|a| a.contains("Bstatic")));
    }

    #[test]
    fn static_c_flags() {
        let f = make_flags(&["sqlite3"], &[], &[]);
        let args = f.to_cc_args();
        assert!(args.contains(&"-lsqlite3".to_string()));
        assert!(args.iter().any(|a| a.contains("Bstatic")));
        assert!(args.iter().any(|a| a.contains("Bdynamic")));
    }

    #[test]
    fn rust_whole_archive_flags() {
        let f = make_flags(&[], &[], &["mylib"]);
        let args = f.to_cc_args();
        assert!(args.contains(&"-lmylib".to_string()));
        assert!(args.iter().any(|a| a.contains("--whole-archive")));
        assert!(args.iter().any(|a| a.contains("--no-whole-archive")));
    }

    #[test]
    fn cpp_always_adds_stdc_plus_plus() {
        // When process_c_like is called with need_stdcpp=true,
        // stdc++ ends up in dynamic_libs.
        let mut f = LinkFlags::default();
        f.dynamic_libs.push("stdc++".to_string());
        f.dynamic_libs.push("mylib".to_string());
        f.dedup();
        let args = f.to_cc_args();
        assert!(args.contains(&"-lstdc++".to_string()));
        assert!(args.contains(&"-lmylib".to_string()));
    }

    #[test]
    fn sanitize_lib_names() {
        assert_eq!(sanitize("libssl.so"),  "ssl");
        assert_eq!(sanitize("libssl"),     "ssl");
        assert_eq!(sanitize("ssl"),        "ssl");
        assert_eq!(sanitize("ssl.a"),      "ssl");
        assert_eq!(sanitize("libssl.a"),   "ssl");
        assert_eq!(sanitize("foo.dylib"),  "foo");
        assert_eq!(sanitize("foo.dll"),    "foo");
    }

    #[test]
    fn dedup_removes_duplicates() {
        let mut f = LinkFlags::default();
        f.dynamic_libs = vec!["ssl".into(), "ssl".into(), "crypto".into()];
        f.dedup();
        assert_eq!(f.dynamic_libs, vec!["ssl", "crypto"]);
    }

    #[test]
    fn python_note_no_link_flag() {
        let f = LinkFlags {
            python_notes: vec!["python[numpy] — bridge, no link flag".into()],
            ..Default::default()
        };
        // Python notes must never produce link flags
        let args = f.to_cc_args();
        assert!(args.is_empty());
        assert!(f.is_empty());
    }
}
