use hk_parser::{parse_hk, HkValue, HkConfig, load_hk_file};
use std::process::Command;

const VERSION: &str = "0.5";
const HK_FILE: &str = "bytes.hk";

fn print_usage() {
    println!("bytes {} — H# JIT package manager", VERSION);
    println!();
    println!("USAGE:");
    println!("  bytes new <n>        Create new bytes project");
    println!("  bytes run              Run in JIT mode");
    println!("  bytes add <pkg>        Add package to bytes.hk");
    println!("  bytes remove <pkg>     Remove package");
    println!("  bytes list             List installed packages");
    println!("  bytes update           Update all packages");
    println!("  bytes python <pkg>     Install Python package");
    println!("  bytes info             Show project info");
    println!("  bytes workspace        Show workspace");
    println!();
    println!("bytes.hk format example:");
    println!("  [project]");
    println!("  -> name => myapp");
    println!("  -> version => 0.1.0");
    println!("  [dependencies]");
    println!("  -> scanner => 1.2.0");
    println!("  [python]");
    println!("  -> numpy => latest");
}

fn find_bytes_hk() -> Option<String> {
    let mut dir = std::env::current_dir().ok()?;
    loop {
        let candidate = dir.join(HK_FILE);
        if candidate.exists() {
            return Some(candidate.to_string_lossy().to_string());
        }
        if !dir.pop() { break; }
    }
    None
}

fn load_config(path: &str) -> Result<HkConfig, String> {
    load_hk_file(path).map_err(|e| e.to_string())
}

fn get_str(config: &HkConfig, section: &str, key: &str) -> Option<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(key))
        .map(|v| v.to_string_val())
}

fn get_section_keys(config: &HkConfig, section: &str) -> Vec<(String, String)> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.as_map())
        .map(|m| m.iter().map(|(k,v)| (k.clone(), v.to_string_val())).collect())
        .unwrap_or_default()
}

fn get_array(config: &HkConfig, section: &str, key: &str) -> Vec<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(key))
        .and_then(|v| v.as_array())
        .map(|a| a.iter().map(|v| v.to_string_val()).collect())
        .unwrap_or_default()
}

fn create_project(name: &str) {
    std::fs::create_dir_all(format!("{}/src", name)).unwrap();

    let bytes_hk = format!(r#"[project]
-> name => {}
-> version => 0.1.0
-> description => H# bytes project

[run]
-> entry => src/main.h#
-> mode => jit

[dependencies]

[python]

[workspace]
-> members => []
"#, name);
    std::fs::write(format!("{}/{}", name, HK_FILE), bytes_hk).unwrap();

    let main_src = format!(r#";; {} — bytes JIT project
fn main() is
    write(bold("Hello from {}!"))
    write("Running in JIT mode via bytes")
end
"#, name, name);
    std::fs::write(format!("{}/src/main.h#", name), main_src).unwrap();

    println!("✓ Created: {}", name);
    println!("  {}/{}", name, HK_FILE);
    println!("  {}/src/main.h#", name);
    println!();
    println!("  Run: cd {} && bytes run", name);
}

fn run_project() -> i32 {
    let hk_path = match find_bytes_hk() {
        Some(p) => p,
        None => { eprintln!("error: no bytes.hk found"); return 1; }
    };
    let config = match load_config(&hk_path) {
        Ok(c) => c,
        Err(e) => { eprintln!("error: {}", e); return 1; }
    };

    // Check workspace
    let members = get_array(&config, "workspace", "members");
    if !members.is_empty() {
        for member in &members {
            println!("── Running member: {} ──", member);
            Command::new("bytes").arg("run").current_dir(member).status().ok();
        }
        return 0;
    }

    let name  = get_str(&config, "project", "name").unwrap_or_else(|| "app".into());
    let entry = get_str(&config, "run", "entry").unwrap_or_else(|| "src/main.h#".into());

    // Install python deps if any
    let py_deps = get_section_keys(&config, "python");
    for (pkg, ver) in &py_deps {
        if !pkg.is_empty() {
            let spec = if ver == "latest" { pkg.clone() } else { format!("{}=={}", pkg, ver) };
            println!("bytes: installing python dep: {}", spec);
            Command::new("pip3").args(["install", "--user", &spec]).status().ok();
        }
    }

    println!("bytes: running {} (JIT)", name);
    Command::new("h#")
        .args(["preview", &entry])
        .status()
        .map(|s| s.code().unwrap_or(0))
        .unwrap_or(1)
}

fn list_packages() {
    let hk_path = match find_bytes_hk() {
        Some(p) => p,
        None => { println!("No bytes.hk found"); return; }
    };
    let config = load_config(&hk_path).unwrap_or_default();
    let deps   = get_section_keys(&config, "dependencies");
    let py     = get_section_keys(&config, "python");

    println!("H# dependencies:");
    if deps.is_empty() {
        println!("  (none)");
    } else {
        for (k,v) in &deps { println!("  {} = {}", k, v); }
    }
    println!("Python dependencies:");
    if py.is_empty() {
        println!("  (none)");
    } else {
        for (k,v) in &py { println!("  {} = {}", k, v); }
    }
}

fn add_package(pkg: &str) {
    let hk_path = find_bytes_hk().unwrap_or_else(|| HK_FILE.to_string());
    let mut content = std::fs::read_to_string(&hk_path).unwrap_or_default();
    if content.contains(&format!("-> {}", pkg)) {
        println!("Package {} already in bytes.hk", pkg);
        return;
    }
    if content.contains("[dependencies]") {
        content = content.replace("[dependencies]\n", &format!("[dependencies]\n-> {} => latest\n", pkg));
    } else {
        content.push_str(&format!("\n[dependencies]\n-> {} => latest\n", pkg));
    }
    std::fs::write(&hk_path, content).unwrap();
    println!("✓ Added {} to bytes.hk", pkg);
}

fn install_python(pkg: &str) {
    println!("bytes: installing Python package: {}", pkg);
    let status = Command::new("pip3").args(["install", "--user", pkg]).status();
    match status {
        Ok(s) if s.success() => println!("✓ Installed {}", pkg),
        _ => eprintln!("✗ Failed to install {}", pkg),
    }
    // Also add to bytes.hk
    let hk_path = find_bytes_hk().unwrap_or_else(|| HK_FILE.to_string());
    let mut content = std::fs::read_to_string(&hk_path).unwrap_or_default();
    if !content.contains(&format!("-> {}", pkg)) {
        if content.contains("[python]") {
            content = content.replace("[python]\n", &format!("[python]\n-> {} => latest\n", pkg));
        } else {
            content.push_str(&format!("\n[python]\n-> {} => latest\n", pkg));
        }
        std::fs::write(&hk_path, content).unwrap();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("help");

    let code = match cmd {
        "new" => {
            let name = args.get(2).map(|s| s.as_str()).unwrap_or("myapp");
            create_project(name);
            0
        }
        "run"    => run_project(),
        "list"   => { list_packages(); 0 }
        "add"    => {
            let pkg = args.get(2).map(|s| s.as_str()).unwrap_or("");
            if pkg.is_empty() { eprintln!("usage: bytes add <pkg>"); 1 }
            else { add_package(pkg); 0 }
        }
        "remove" => {
            let pkg = args.get(2).map(|s| s.as_str()).unwrap_or("");
            let hk_path = find_bytes_hk().unwrap_or_else(|| HK_FILE.to_string());
            let content = std::fs::read_to_string(&hk_path).unwrap_or_default();
            let new_content: String = content.lines()
                .filter(|l| !l.contains(&format!("-> {} =>", pkg)))
                .map(|l| format!("{}\n", l))
                .collect();
            std::fs::write(&hk_path, new_content).unwrap();
            println!("✓ Removed {} from bytes.hk", pkg);
            0
        }
        "python" => {
            let pkg = args.get(2).map(|s| s.as_str()).unwrap_or("");
            if pkg.is_empty() { eprintln!("usage: bytes python <pkg>"); 1 }
            else { install_python(pkg); 0 }
        }
        "info"   => {
            let hk_path = match find_bytes_hk() {
                Some(p) => p,
                None => { println!("No bytes.hk"); return; }
            };
            let config = load_config(&hk_path).unwrap_or_default();
            println!("Name: {}", get_str(&config, "project", "name").unwrap_or_default());
            println!("Version: {}", get_str(&config, "project", "version").unwrap_or_default());
            println!("Entry: {}", get_str(&config, "run", "entry").unwrap_or_default());
            0
        }
        "workspace" => {
            let hk_path = find_bytes_hk().unwrap_or_default();
            let config  = load_config(&hk_path).unwrap_or_default();
            let members = get_array(&config, "workspace", "members");
            if members.is_empty() {
                println!("No workspace defined in bytes.hk");
            } else {
                println!("Workspace members:");
                for m in &members { println!("  - {}", m); }
            }
            0
        }
        "update" => {
            println!("bytes: update not yet implemented (packages come from Bytes-Repository)");
            0
        }
        _ => { print_usage(); 0 }
    };
    std::process::exit(code);
}
