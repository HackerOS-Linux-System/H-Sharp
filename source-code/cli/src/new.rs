use colored::Colorize;
use std::path::Path;

pub fn run(name: String, template: String) {
    println!("{} H# project `{}`", "Creating:".cyan().bold(), name);
    let project_dir = Path::new(&name);
    if project_dir.exists() {
        eprintln!("{} directory `{}` already exists", "Error:".red().bold(), name);
        std::process::exit(1);
    }
    std::fs::create_dir_all(project_dir.join("src")).unwrap();
    std::fs::create_dir_all(project_dir.join("build")).unwrap();

    let manifest = serde_json::json!({
        "name": name,
        "version": "0.1.0",
        "template": template,
        "dependencies": {}
    });
    std::fs::write(project_dir.join("h#.json"), serde_json::to_string_pretty(&manifest).unwrap()).unwrap();
    std::fs::write(project_dir.join(".gitignore"), "build/\n*.c\n").unwrap();

    let main_src = match template.as_str() {
        "cybersec" | "security" => TEMPLATE_CYBERSEC,
        "net" | "network"       => TEMPLATE_NETWORK,
        "lib"                   => TEMPLATE_LIB,
        _                       => TEMPLATE_APP,
    };
    std::fs::write(project_dir.join("src").join("main.h#"), main_src).unwrap();

    println!("\n  {} {}/", "Created:".green().bold(), name);
    println!("  {} {}/src/main.h#", "Created:".green(), name);
    println!("  {} {}/h#.json", "Created:".green(), name);
    println!("\n  {}", "Get started:".bold());
    println!("    cd {}", name);
    println!("    hsharp preview    # run in interpreter mode");
    println!("    hsharp build      # compile to native binary");
}

const TEMPLATE_APP: &str = r#"# H# Application
fn main() do
    println("Hello from H#!")
    let x: int = 42
    println(to_string(x))
end
"#;

const TEMPLATE_CYBERSEC: &str = r#"# H# CyberSec Tool
import "std:io::net"
import "std:crypto::hash"

fn main() do
    println("H# CyberSec Tool v0.1")
    let target: string = "127.0.0.1"
    let port: int = 8080
    println("Target: " + target)
end

fn scan_port(host: string, port: int) -> bool do
    return false
end
"#;

const TEMPLATE_NETWORK: &str = r#"# H# Network Tool
import "std:io::net"

fn main() do
    println("H# Network Tool")
    let host: string = "localhost"
    println("Host: " + host)
end
"#;

const TEMPLATE_LIB: &str = r#"# H# Library

pub fn add(a: int, b: int) -> int = a + b

pub fn greet(name: string) -> string do
    return "Hello, " + name + "!"
end
"#;
