use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};
use std::net::TcpStream;

const REGISTRY_HOST: &str = "raw.githubusercontent.com";
const REGISTRY_PATH: &str = "/Bytes-Repository/repository/main/index.json";

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct PackageEntry {
    pub name: String,
    pub description: Option<String>,
    pub versions: Vec<String>,
    pub latest: String,
    pub url: Option<String>,
    pub keywords: Option<Vec<String>>,
    pub author: Option<String>,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct RegistryIndex {
    pub packages: Vec<PackageEntry>,
}

pub fn fetch_index() -> anyhow::Result<RegistryIndex> {
    let cache = cache_path();
    let text = match http_get(REGISTRY_HOST, REGISTRY_PATH) {
        Ok(body) => {
            if let Some(ref p) = cache {
                let _ = std::fs::create_dir_all(p.parent().unwrap_or(std::path::Path::new(".")));
                let _ = std::fs::write(p, &body);
            }
            body
        }
        Err(_) => {
            if let Some(ref p) = cache {
                std::fs::read_to_string(p).unwrap_or_default()
            } else {
                String::new()
            }
        }
    };
    if text.is_empty() {
        return Ok(RegistryIndex { packages: vec![] });
    }
    Ok(serde_json::from_str(&text).unwrap_or(RegistryIndex { packages: vec![] }))
}

fn http_get(host: &str, path: &str) -> anyhow::Result<String> {
    let addr = format!("{}:80", host);
    let addr: std::net::SocketAddr = addr.parse()?;
    let mut stream = TcpStream::connect_timeout(&addr, std::time::Duration::from_secs(5))?;
    write!(stream, "GET {} HTTP/1.0\r\nHost: {}\r\nConnection: close\r\n\r\n", path, host)?;
    stream.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
    let mut response = String::new();
    stream.read_to_string(&mut response)?;
    let body = response.split_once("\r\n\r\n").map(|(_, b)| b).unwrap_or(&response).to_string();
    Ok(body)
}

pub fn search(query: &str) {
    let spinner = make_spinner("Fetching registry index...");
    let index = match fetch_index() {
        Ok(i) => i,
        Err(e) => { spinner.finish_and_clear(); eprintln!("{} {}", "Error:".red().bold(), e); return; }
    };
    spinner.finish_and_clear();

    let q = query.to_lowercase();
    let results: Vec<&PackageEntry> = index.packages.iter()
        .filter(|p| {
            p.name.to_lowercase().contains(&q)
            || p.description.as_deref().unwrap_or("").to_lowercase().contains(&q)
            || p.keywords.as_ref().map(|ks| ks.iter().any(|k| k.to_lowercase().contains(&q))).unwrap_or(false)
        })
        .collect();

    println!("{} `{}`\n", "Searching Bytes Registry for:".cyan().bold(), query);
    if results.is_empty() {
        println!("  No packages found matching `{}`.", query);
        println!("\n  {}", "Tip: Try a broader search term.".dimmed());
        return;
    }
    println!("  Found {} package(s):\n", results.len());
    println!("  {:<25} {:<12} {}", "NAME".bold(), "LATEST".bold(), "DESCRIPTION".bold());
    println!("  {}", "─".repeat(70).dimmed());
    for pkg in results {
        println!("  {:<25} {:<12} {}", pkg.name.cyan(), pkg.latest.green(), pkg.description.as_deref().unwrap_or("—"));
    }
    println!("\n  {}", "Install with: bytes add <name>".dimmed());
}

pub fn info(package: &str) {
    let (pkg_name, _) = split_pkg_version(package);
    let spinner = make_spinner("Fetching registry...");
    let index = match fetch_index() {
        Ok(i) => i,
        Err(e) => { spinner.finish_and_clear(); eprintln!("{} {}", "Error:".red().bold(), e); return; }
    };
    spinner.finish_and_clear();
    match index.packages.iter().find(|p| p.name == pkg_name) {
        None => eprintln!("{} package `{}` not found", "Error:".red().bold(), pkg_name),
        Some(e) => {
            println!("{} {}", "Package: ".bold(), e.name.cyan().bold());
            println!("{} {}", "Latest:  ".bold(), e.latest.green());
            println!("{} {}", "Versions:".bold(), e.versions.join(", "));
            if let Some(d) = &e.description { println!("{} {}", "Desc:    ".bold(), d); }
            if let Some(a) = &e.author     { println!("{} {}", "Author:  ".bold(), a); }
            println!("\n  {}", format!("bytes add {}", e.name).dimmed());
        }
    }
}

pub fn split_pkg_version(package: &str) -> (String, Option<String>) {
    if let Some(idx) = package.rfind('/') {
        let name = package[..idx].to_string();
        let ver  = package[idx+1..].to_string();
        if ver.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            return (name, Some(ver));
        }
    }
    (package.to_string(), None)
}

fn cache_path() -> Option<std::path::PathBuf> {
    dirs::cache_dir().map(|d| d.join("bytes").join("index.json"))
}

pub fn make_spinner(msg: &str) -> indicatif::ProgressBar {
    use indicatif::{ProgressBar, ProgressStyle};
    let pb = ProgressBar::new_spinner();
    pb.set_style(ProgressStyle::default_spinner().template("{spinner:.cyan} {msg}").unwrap());
    pb.set_message(msg.to_string());
    pb.enable_steady_tick(std::time::Duration::from_millis(80));
    pb
}
