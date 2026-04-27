use hk_parser::{parse_hk, HkValue, HkConfig, load_hk_file};
use std::path::Path;
use std::process::Command;

const VERSION: &str = "0.4.0";
const HK_FILE: &str = "vira.hk";

fn find_vira_hk() -> Option<String> {
    // Look in current dir and parent dirs
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

fn print_usage() {
    println!("vira {} — H# build manager", VERSION);
    println!();
    println!("USAGE:");
    println!("  vira new <name>      Create new project with vira.hk");
    println!("  vira build           Build project (reads vira.hk)");
    println!("  vira build --release Build with hhc LLVM O3");
    println!("  vira run             Build and run");
    println!("  vira check           Type-check only");
    println!("  vira clean           Remove build artifacts");
    println!("  vira info            Show project info from vira.hk");
    println!("  vira workspace       Show workspace members");
    println!();
    println!("WORKSPACE:");
    println!("  vira.hk supports [workspace] with members list.");
    println!("  Run 'vira build' from workspace root to build all members.");
}

fn create_project(name: &str) {
    std::fs::create_dir_all(format!("{}/src", name)).unwrap();
    std::fs::create_dir_all(format!("{}/tests", name)).unwrap();

    // Write vira.hk
    let vira_hk = format!(r#"[project]
-> name => {}
-> version => 0.1.0
-> edition => 2026
-> description => A H# project

[build]
-> entry => src/main.h#
-> output => build/{}
-> backend => cranelift

[release]
-> backend => hhc
-> optimize => O3
-> lto => true
-> strip => true

[dependencies]
"#, name, name);
    std::fs::write(format!("{}/{}", name, HK_FILE), vira_hk).unwrap();

    // Write main.h#
    let main_src = format!(r#";; {} — created with vira
fn main() is
    write(bold("Hello from {}!"))
end
"#, name, name);
    std::fs::write(format!("{}/src/main.h#", name), main_src).unwrap();

    // Write .gitignore
    std::fs::write(format!("{}/.gitignore", name), "build/\n*.o\n*.a\n").unwrap();

    println!("✓ Created project: {}", name);
    println!("  {}/{}", name, HK_FILE);
    println!("  {}/src/main.h#", name);
    println!();
    println!("  Run: cd {} && vira build", name);
}

fn load_project_config(path: &str) -> Result<HkConfig, String> {
    load_hk_file(path).map_err(|e| e.to_string())
}

fn get_str(config: &HkConfig, section: &str, key: &str) -> Option<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(key))
        .map(|v| v.to_string_val())
}

fn get_array(config: &HkConfig, section: &str, key: &str) -> Vec<String> {
    config.iter()
        .find(|(s,_)| s == section)
        .and_then(|(_,v)| v.get(key))
        .and_then(|v| v.as_array())
        .map(|a| a.iter().map(|v| v.to_string_val()).collect())
        .unwrap_or_default()
}

fn build(release: bool) -> i32 {
    let hk_path = match find_vira_hk() {
        Some(p) => p,
        None => {
            eprintln!("error: no vira.hk found (run vira new <name> or cd to project dir)");
            return 1;
        }
    };

    let config = match load_project_config(&hk_path) {
        Ok(c) => c,
        Err(e) => { eprintln!("error reading vira.hk: {}", e); return 1; }
    };

    // Check for workspace
    let members = get_array(&config, "workspace", "members");
    if !members.is_empty() {
        println!("vira: workspace build ({} members)", members.len());
        let mut any_fail = false;
        for member in &members {
            println!("\n── Building member: {} ──", member);
            let status = Command::new("vira")
                .arg(if release { "build --release" } else { "build" })
                .current_dir(member)
                .status();
            match status {
                Ok(s) if s.success() => println!("  ✓ {}", member),
                _ => { eprintln!("  ✗ {} failed", member); any_fail = true; }
            }
        }
        return if any_fail { 1 } else { 0 };
    }

    let name    = get_str(&config, "project", "name").unwrap_or_else(|| "app".into());
    let entry   = get_str(&config, "build", "entry").unwrap_or_else(|| "src/main.h#".into());
    let output  = get_str(&config, "build", "output").unwrap_or_else(|| format!("build/{}", name));
    let backend = if release {
        get_str(&config, "release", "backend").unwrap_or_else(|| "hhc".into())
    } else {
        get_str(&config, "build", "backend").unwrap_or_else(|| "cranelift".into())
    };

    // Create build dir
    if let Some(dir) = Path::new(&output).parent() {
        std::fs::create_dir_all(dir).ok();
    }

    println!("vira: building {} v{} ({} backend)",
        name,
        get_str(&config, "project", "version").unwrap_or_else(|| "?".into()),
        backend
    );

    let status = if backend == "hhc" {
        let mut args = vec![entry.clone(), "-o".to_string(), output.clone()];
        if get_str(&config, "release", "optimize").as_deref() == Some("O3") {
            args.push("--O3".into());
        }
        if get_str(&config, "release", "lto").as_deref() == Some("true") {
            args.push("--lto".into());
        }
        Command::new("hhc").args(&args).status()
    } else {
        Command::new("h#")
            .args(["build", &entry, "-o", &output])
            .status()
    };

    match status {
        Ok(s) if s.success() => {
            println!("  ✓ Build complete → {}", output);
            0
        }
        Ok(s) => { eprintln!("  ✗ Build failed (exit {})", s.code().unwrap_or(1)); 1 }
        Err(e) => { eprintln!("  ✗ Could not run compiler: {}", e); 1 }
    }
}

fn info() {
    let hk_path = match find_vira_hk() {
        Some(p) => p,
        None => { eprintln!("error: no vira.hk found"); return; }
    };
    let config = match load_project_config(&hk_path) {
        Ok(c) => c,
        Err(e) => { eprintln!("error: {}", e); return; }
    };
    println!("Project: {}", get_str(&config, "project", "name").unwrap_or_default());
    println!("Version: {}", get_str(&config, "project", "version").unwrap_or_default());
    println!("Entry:   {}", get_str(&config, "build", "entry").unwrap_or_default());
    println!("Backend: {}", get_str(&config, "build", "backend").unwrap_or_default());
    let members = get_array(&config, "workspace", "members");
    if !members.is_empty() {
        println!("Workspace members: {}", members.join(", "));
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
        "build" => build(args.iter().any(|a| a == "--release")),
        "run" => {
            let code = build(false);
            if code != 0 { std::process::exit(code); }
            // Run the binary
            let hk_path = find_vira_hk().unwrap_or_default();
            let config = load_project_config(&hk_path).unwrap_or_default();
            let name   = get_str(&config, "project", "name").unwrap_or_else(|| "app".into());
            let output = get_str(&config, "build", "output").unwrap_or_else(|| format!("build/{}", name));
            let _ = Command::new(&output).status();
            0
        }
        "check" => {
            let hk_path = find_vira_hk().unwrap_or_default();
            let config = load_project_config(&hk_path).unwrap_or_default();
            let entry  = get_str(&config, "build", "entry").unwrap_or_else(|| "src/main.h#".into());
            Command::new("h#").args(["check", &entry]).status().ok();
            0
        }
        "clean" => {
            let _ = std::fs::remove_dir_all("build");
            println!("✓ Cleaned");
            0
        }
        "workspace" => {
            let hk_path = find_vira_hk().unwrap_or_default();
            let config = load_project_config(&hk_path).unwrap_or_default();
            let members = get_array(&config, "workspace", "members");
            if members.is_empty() {
                println!("No workspace defined in vira.hk");
            } else {
                println!("Workspace members:");
                for m in &members { println!("  - {}", m); }
            }
            0
        }
        "info" => { info(); 0 }
        _ => { print_usage(); 0 }
    };
    std::process::exit(code);
}
