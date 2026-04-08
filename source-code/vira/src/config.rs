/// vira.hcl project configuration

use std::collections::HashMap;
use crate::hcl;

/// Output artifact type — specified in vira.hcl [output] section
#[derive(Debug, Clone, PartialEq)]
pub enum OutputType {
    Binary,          // executable binary (default)
    SharedLib,       // .so  — shared library
    StaticLib,       // .a   — static library, linkable
    HsharpLib,       // .hsl — H# native library format (like .rlib for Rust)
}

impl Default for OutputType {
    fn default() -> Self { Self::Binary }
}

impl OutputType {
    pub fn from_str(s: &str) -> Self {
        match s.trim() {
            "so" | "shared" | "dylib" => Self::SharedLib,
            "a"  | "static"           => Self::StaticLib,
            "hsl" | "hsharp-lib"      => Self::HsharpLib,
            _                         => Self::Binary,
        }
    }
    pub fn extension(&self) -> &str {
        match self {
            Self::Binary    => "",
            Self::SharedLib => ".so",
            Self::StaticLib => ".a",
            Self::HsharpLib => ".hsl",
        }
    }
    pub fn cc_flags(&self) -> Vec<&str> {
        match self {
            Self::Binary    => vec![],
            Self::SharedLib => vec!["-shared", "-fPIC"],
            Self::StaticLib => vec![],   // handled via ar
            Self::HsharpLib => vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub struct ViraProject {
    pub name:         String,
    pub version:      String,
    pub description:  String,
    pub authors:      Vec<String>,
    pub dependencies: HashMap<String, String>,  // name → version/url
    pub dev_deps:     HashMap<String, String>,
    pub h_sharp_ver:  String,
    pub src_dir:      String,
    /// Output artifact type: binary | so | a | hsl
    pub output_type:  OutputType,
    /// Output file name (default: project name)
    pub output_name:  Option<String>,
}

impl Default for ViraProject {
    fn default() -> Self {
        Self {
            name:         "unnamed".into(),
            version:      "0.1.0".into(),
            description:  String::new(),
            authors:      Vec::new(),
            dependencies: HashMap::new(),
            dev_deps:     HashMap::new(),
            h_sharp_ver:  "0.1".into(),
            src_dir:      "src".into(),
            output_type:  OutputType::Binary,
            output_name:  None,
        }
    }
}

impl ViraProject {
    pub fn load(path: &str) -> anyhow::Result<Self> {
        let src = std::fs::read_to_string(path)
            .map_err(|e| anyhow::anyhow!("cannot read {}: {}", path, e))?;
        Self::parse(&src)
    }

    pub fn parse(src: &str) -> anyhow::Result<Self> {
        let map = hcl::parse(src)?;
        let mut proj = ViraProject::default();

        // project { name = "..." version = "..." }
        if let Some(hcl::HclValue::Block(b)) = map.get("project") {
            if let Some(v) = b.get("name")        { proj.name        = v.as_str().unwrap_or("").into(); }
            if let Some(v) = b.get("version")     { proj.version     = v.as_str().unwrap_or("0.1.0").into(); }
            if let Some(v) = b.get("description") { proj.description = v.as_str().unwrap_or("").into(); }
            if let Some(v) = b.get("h_sharp")     { proj.h_sharp_ver = v.as_str().unwrap_or("0.1").into(); }
            if let Some(v) = b.get("src_dir")     { proj.src_dir     = v.as_str().unwrap_or("src").into(); }
        }

        // dependencies { scanner = "1.2" github.com/user/repo = "latest" }
        if let Some(hcl::HclValue::Block(b)) = map.get("dependencies") {
            for (k, v) in b {
                if let Some(ver) = v.as_str() {
                    proj.dependencies.insert(k.clone(), ver.to_string());
                }
            }
        }

        // dev_dependencies { ... }
        if let Some(hcl::HclValue::Block(b)) = map.get("dev_dependencies") {
            for (k, v) in b {
                if let Some(ver) = v.as_str() {
                    proj.dev_deps.insert(k.clone(), ver.to_string());
                }
            }
        }

        // output { type = "so" name = "libmylib" }
        if let Some(hcl::HclValue::Block(b)) = map.get("output") {
            if let Some(v) = b.get("type") {
                proj.output_type = OutputType::from_str(v.as_str().unwrap_or("binary"));
            }
            if let Some(v) = b.get("name") {
                proj.output_name = v.as_str().map(|s| s.to_string());
            }
        }

        Ok(proj)
    }

    pub fn save(&self, path: &str) -> anyhow::Result<()> {
        let deps: Vec<(String, String)> = self.dependencies.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let content = hcl::serialize_project(&self.name, &self.version, &deps);
        std::fs::write(path, content)?;
        Ok(())
    }

    /// Find vira.hcl or Vira.hcl in current directory
    pub fn find() -> Option<String> {
        for name in &["vira.hcl", "Vira.hcl"] {
            if std::path::Path::new(name).exists() {
                return Some(name.to_string());
            }
        }
        None
    }

    /// Project-local .cache directory (next to vira.hcl, like .git/)
    pub fn cache_dir() -> std::path::PathBuf {
        std::path::PathBuf::from(".cache")
    }

    /// Project-local build directory
    pub fn build_dir() -> std::path::PathBuf {
        std::path::PathBuf::from("build")
    }
}

/// Generate default vira.hcl content for new project
pub fn default_vira_hcl(name: &str, template: &str) -> String {
    let output_section = match template {
        "lib" => r#"
output {
  type = "hsl"  // H# library format (.hsl)
  // type = "so"   // shared library (.so)
  // type = "a"    // static library (.a)
}"#,
        _ => r#"
output {
  type = "binary"  // binary | so | a | hsl
  // name = "custom-name"
}"#,
    };
    format!(r#"project "{name}" {{
  version     = "0.1.0"
  description = "A new H# project for HackerOS"
  h_sharp     = "0.1"
  src_dir     = "src"
}}
{output}
dependencies {{
  // H# packages from Vira registry or GitHub:
  // scanner          = "1.2"
  // github.com/user/repo = "latest"
}}

dev_dependencies {{
  // Dev-only packages
}}
"#, name = name, output = output_section)
}
