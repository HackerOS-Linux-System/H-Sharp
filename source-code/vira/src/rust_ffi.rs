use std::path::{Path, PathBuf};
use colored::*;

#[derive(Debug, Clone, serde::Deserialize)]
pub struct RustDep {
    /// Local path to Rust crate
    pub path:     Option<String>,
    /// Crates.io crate name
    pub crate_:   Option<String>,
    pub version:  Option<String>,
    pub features: Option<Vec<String>>,
    /// Output type: "staticlib" (.a) or "cdylib" (.so)
    pub output:   Option<String>,
}

pub struct RustFfiBuilder {
    cache_dir: PathBuf,
}

impl RustFfiBuilder {
    pub fn new(cache_dir: PathBuf) -> Self {
        std::fs::create_dir_all(&cache_dir).ok();
        Self { cache_dir }
    }

    /// Build a local Rust crate and generate H# FFI bindings
    pub fn build_local(&self, name: &str, dep: &RustDep) -> anyhow::Result<FfiArtifact> {
        let src_path = dep.path.as_deref()
            .ok_or_else(|| anyhow::anyhow!("rust dep {} missing path", name))?;
        let src_abs = std::fs::canonicalize(src_path)
            .map_err(|_| anyhow::anyhow!("rust dep path not found: {}", src_path))?;

        println!("  {} {} (Rust → H# FFI)...", "building".cyan().bold(), name.yellow());

        // Ensure Cargo.toml has crate-type = ["staticlib"]
        self.ensure_staticlib(&src_abs)?;

        // cargo build --release
        let ok = std::process::Command::new("cargo")
            .args(["build", "--release"])
            .current_dir(&src_abs)
            .status()
            .map(|s| s.success())
            .unwrap_or(false);

        if !ok {
            anyhow::bail!("cargo build failed for {}", name);
        }

        // Find the .a in target/release
        let lib_name = format!("lib{}.a", name.replace('-', "_"));
        let lib_path = src_abs.join("target/release").join(&lib_name);
        if !lib_path.exists() {
            anyhow::bail!("built library not found: {}", lib_path.display());
        }

        // Copy to cache
        let cached_lib = self.cache_dir.join(format!("{}.a", name));
        std::fs::copy(&lib_path, &cached_lib)?;

        // Generate H# FFI stub using cbindgen (if available) or from extern blocks
        let header = self.generate_header(&src_abs, name)?;
        let hsharp_stub = self.header_to_hsharp_stub(name, &header);

        let stub_path = self.cache_dir.join(format!("{}.h#", name));
        std::fs::write(&stub_path, &hsharp_stub)?;

        println!("  {} {} ({} bytes)", "✓".green().bold(), name.cyan(), 
                 std::fs::metadata(&cached_lib)?.len());

        Ok(FfiArtifact {
            name:       name.to_string(),
            lib_path:   cached_lib,
            stub_path,
            link_kind:  LinkKind::Static,
        })
    }

    /// Ensure the Rust crate has crate-type = ["staticlib"] in Cargo.toml
    fn ensure_staticlib(&self, src: &Path) -> anyhow::Result<()> {
        let cargo_path = src.join("Cargo.toml");
        let content = std::fs::read_to_string(&cargo_path)?;
        if content.contains("staticlib") || content.contains("cdylib") {
            return Ok(()); // already configured
        }
        // Add [lib] section
        let patched = content + "\n[lib]\ncrate-type = [\"staticlib\"]\n";
        std::fs::write(&cargo_path, patched)?;
        Ok(())
    }

    /// Generate C header using cbindgen (or basic stub if not available)
    fn generate_header(&self, src: &Path, name: &str) -> anyhow::Result<String> {
        // Try cbindgen first
        let has_cbindgen = std::process::Command::new("cbindgen")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);

        if has_cbindgen {
            let header_path = self.cache_dir.join(format!("{}.h", name));
            let ok = std::process::Command::new("cbindgen")
                .args([
                    "--crate", &src.display().to_string(),
                    "--output", &header_path.display().to_string(),
                    "--lang", "c",
                ])
                .current_dir(src)
                .status()
                .map(|s| s.success())
                .unwrap_or(false);

            if ok {
                return Ok(std::fs::read_to_string(&header_path).unwrap_or_default());
            }
        }

        // Fallback: parse #[no_mangle] pub extern "C" functions from src/lib.rs
        self.parse_rust_exports(src)
    }

    /// Parse Rust source for #[no_mangle] pub extern "C" fn declarations
    fn parse_rust_exports(&self, src: &Path) -> anyhow::Result<String> {
        let lib_rs = src.join("src/lib.rs");
        if !lib_rs.exists() { return Ok(String::new()); }

        let source = std::fs::read_to_string(&lib_rs)?;
        let mut header = String::from("// Auto-generated C header from Rust exports\n\n");

        let mut in_no_mangle = false;
        for line in source.lines() {
            let trimmed = line.trim();
            if trimmed == "#[no_mangle]" {
                in_no_mangle = true;
                continue;
            }
            if in_no_mangle && trimmed.starts_with("pub extern \"C\" fn ") {
                // Convert Rust sig to C sig (basic)
                let c_decl = rust_sig_to_c(trimmed);
                header.push_str(&c_decl);
                header.push('\n');
                in_no_mangle = false;
            } else {
                in_no_mangle = false;
            }
        }
        Ok(header)
    }

    /// Convert C header to H# extern block stub
    fn header_to_hsharp_stub(&self, name: &str, header: &str) -> String {
        let mut stub = format!(
            ";; H# FFI binding for Rust library: {}\n\
             ;; Link: extern static [rust] is...end\n\
             ;; The Rust library is compiled to a static archive (.a)\n\n\
             extern static [rust] is\n",
            name
        );

        // Parse C declarations from header (simple approach)
        for line in header.lines() {
            let l = line.trim();
            if l.starts_with("//") || l.is_empty() { continue; }
            if let Some(c_fn) = parse_c_decl(l) {
                stub.push_str(&format!("    ;; C: {}\n", l));
                stub.push_str(&format!("    fn {}\n", c_fn));
            }
        }

        stub.push_str("end\n");
        stub
    }
}

fn rust_sig_to_c(rust_sig: &str) -> String {
    // Very basic: pub extern "C" fn foo(x: i64) -> i64 → int64_t foo(int64_t x);
    let sig = rust_sig
        .trim_start_matches("pub extern \"C\" fn ")
        .trim_end_matches(" {")
        .trim_end_matches('{');

    let sig = sig
        .replace("i64", "int64_t")
        .replace("u64", "uint64_t")
        .replace("i32", "int32_t")
        .replace("u32", "uint32_t")
        .replace("f64", "double")
        .replace("f32", "float")
        .replace("bool", "int")
        .replace("*const c_char", "const char*")
        .replace("*mut c_char", "char*");

    format!("{};", sig)
}

fn parse_c_decl(line: &str) -> Option<String> {
    // Very basic C → H# conversion
    // "int64_t foo(int64_t x);" → "foo(x: int) -> int"
    if !line.ends_with(';') { return None; }
    let line = line.trim_end_matches(';');

    let paren = line.find('(')?;
    let name_start = line[..paren].rfind(|c: char| c == ' ' || c == '*')? + 1;
    let fn_name = &line[name_start..paren];
    let ret_type = c_type_to_hsharp(&line[..name_start].trim());
    let params_str = &line[paren+1..line.rfind(')')?];

    let params: Vec<String> = if params_str.trim() == "void" || params_str.trim().is_empty() {
        Vec::new()
    } else {
        params_str.split(',').enumerate().map(|(i, p)| {
            let p = p.trim();
            let parts: Vec<&str> = p.rsplitn(2, ' ').collect();
            if parts.len() == 2 {
                let param_name = parts[0].trim_start_matches('*');
                let c_ty       = parts[1];
                format!("{}: {}", param_name, c_type_to_hsharp(c_ty))
            } else {
                format!("arg{}: {}", i, c_type_to_hsharp(p))
            }
        }).collect()
    };

    let ret = if ret_type == "void" { String::new() } else { format!(" -> {}", ret_type) };
    Some(format!("{}({}){}",fn_name, params.join(", "), ret))
}

fn c_type_to_hsharp(c_ty: &str) -> &'static str {
    match c_ty.trim() {
        "int64_t" | "long"   => "int",
        "uint64_t"           => "uint",
        "int32_t" | "int"    => "int",
        "uint32_t"           => "uint",
        "double"             => "f64",
        "float"              => "f32",
        "int"                => "int",
        "void"               => "void",
        "const char*" | "char*" => "string",
        "uint8_t*"           => "bytes",
        _                    => "int",
    }
}

#[derive(Debug)]
pub struct FfiArtifact {
    pub name:      String,
    pub lib_path:  PathBuf,
    pub stub_path: PathBuf,
    pub link_kind: LinkKind,
}

#[derive(Debug)]
pub enum LinkKind { Static, Dynamic }
