use hk_parser::{load_hk_file, HkConfig};
use colored::Colorize;
use std::process::Command;
use std::io::{self, Write};
use std::time::Instant;
use std::path::Path;

const VERSION: &str = "0.5.0";
const HK: &str = "bytes.hk";
const CACHE: &str = ".cache";
const BUILD: &str = "build";

// ── progress bars ──────────────────────────────────────────────────────────────

fn pb_build(pct: u8, msg: &str, eta: u64) {
    let w = 20usize;
    let f = (w * pct as usize) / 100;
    let bar = format!("{}{}", "#".repeat(f), "-".repeat(w - f));
    print!("\r\x1b[K<{}> [{:3}%] {} [{}s]", bar.dimmed(), pct, msg.cyan(), eta);
    io::stdout().flush().ok();
}

fn pb_dl(pct: u8, ms: u64, msg: &str, eta: u64) {
    let w = 20usize;
    let f = (w * pct as usize) / 100;
    let arrow = if f > 0 { format!("{}>", "-".repeat(f-1)) } else { ".".to_string() };
    let dots  = ".".repeat(w.saturating_sub(f));
    print!("\r\x1b[K[{}{} ] [{}ms] {} [{}s]", arrow.yellow(), dots, ms, msg.cyan(), eta);
    io::stdout().flush().ok();
}

fn pb_done() { println!(); }

// ── config ─────────────────────────────────────────────────────────────────────

fn find_hk() -> Option<String> {
    let mut d = std::env::current_dir().ok()?;
    loop {
        let c = d.join(HK);
        if c.exists() { return Some(c.to_string_lossy().into()); }
        if !d.pop() { break; }
    }
    None
}

fn cfg() -> HkConfig { find_hk().map(|p| load_hk_file(&p).unwrap_or_default()).unwrap_or_default() }
fn hk_str(c: &HkConfig, sec: &str, key: &str) -> Option<String> {
    c.iter().find(|(s,_)| s==sec).and_then(|(_,v)| v.get(key)).map(|v| v.to_string_val())
}
fn hk_arr(c: &HkConfig, sec: &str, key: &str) -> Vec<String> {
    c.iter().find(|(s,_)| s==sec).and_then(|(_,v)| v.get(key))
     .and_then(|v| v.as_array()).map(|a| a.iter().map(|v| v.to_string_val()).collect())
     .unwrap_or_default()
}
fn hk_kvs(c: &HkConfig, sec: &str) -> Vec<(String,String)> {
    c.iter().find(|(s,_)| s==sec).and_then(|(_,v)| v.as_map())
     .map(|m| m.iter().map(|(k,v)| (k.clone(), v.to_string_val())).collect())
     .unwrap_or_default()
}

// ── build ──────────────────────────────────────────────────────────────────────

fn do_build(file: Option<&str>, mode: &str) -> i32 {
    let c      = cfg();
    let name   = hk_str(&c, "project", "name").unwrap_or_else(|| "app".into());
    let entry  = file.map(str::to_string)
        .or_else(|| hk_str(&c, "build", "entry"))
        .unwrap_or_else(|| "src/main.h#".into());
    let out    = format!("{}/{}", BUILD, name);
    std::fs::create_dir_all(CACHE).ok();
    std::fs::create_dir_all(BUILD).ok();

    // workspace?
    let members = hk_arr(&c, "workspace", "members");
    if !members.is_empty() && file.is_none() {
        println!("{} workspace build", "bytes:".bold());
        let mut fail = false;
        for m in &members {
            let code = Command::new("bytes").arg("build")
                .args(match mode { "release" => vec!["--release"], _ => vec![] })
                .current_dir(m).status()
                .map(|s| if s.success() { println!("  {} {}", "✓".green(), m); 0 }
                         else { eprintln!("  {} {}", "✗".red(), m); 1 })
                .unwrap_or(1);
            if code != 0 { fail = true; }
        }
        return if fail { 1 } else { 0 };
    }

    println!("{} {} → {}", "bytes build:".bold(), entry.cyan(), mode.yellow());

    let deps = hk_kvs(&c, "dependencies");
    if !deps.is_empty() { install_deps(&deps); }

    let t = Instant::now();
    pb_build(15, &format!("Checking {}", entry), 8);
    let ok = Command::new("h#").args(["check", &entry]).output()
        .map(|o| o.status.success()).unwrap_or(false);
    if !ok { pb_done(); eprintln!("  {} type check failed", "✗".red()); return 1; }

    pb_build(50, &format!("Compiling {}", entry), 5);
    let status = match mode {
        "release" | "O3" => Command::new("hhc").args([&entry, "-o", &out, "--O3", "--lto"]).status(),
        "O2"             => Command::new("hhc").args([&entry, "-o", &out, "--O2"]).status(),
        _                => Command::new("h#").args(["build", &entry, "-o", &out]).status(),
    };

    pb_build(95, "Linking", 1);
    match status {
        Ok(s) if s.success() => {
            pb_build(100, "Done", 0); pb_done();
            println!("  {} {} ({:.1}s)", "✓".green().bold(), out.bold(), t.elapsed().as_secs_f32());
            0
        }
        _ => { pb_done(); eprintln!("  {} build failed", "✗".red()); 1 }
    }
}

// ── run ────────────────────────────────────────────────────────────────────────

fn do_run(file: Option<&str>, release: bool) -> i32 {
    let c     = cfg();
    let entry = file.map(str::to_string)
        .or_else(|| hk_str(&c, "run", "entry").or_else(|| hk_str(&c, "build", "entry")))
        .unwrap_or_else(|| "src/main.h#".into());

    // Python deps
    for (pkg, ver) in hk_kvs(&c, "python") {
        let spec = if ver == "latest" { pkg.clone() } else { format!("{}=={}", pkg, ver) };
        Command::new("pip3").args(["install", "-q", "--user", &spec]).status().ok();
    }

    if release {
        println!("{} {} (hhc O3 JIT)", "bytes run:".bold(), entry.cyan());
        let tmp = format!("/tmp/brun_{}", std::process::id());
        let ok  = Command::new("hhc").args([&entry, "-o", &tmp, "--O3", "--lto"])
            .status().map(|s| s.success()).unwrap_or(false);
        if ok {
            let code = Command::new(&tmp).status()
                .map(|s| s.code().unwrap_or(0)).unwrap_or(1);
            std::fs::remove_file(&tmp).ok();
            return code;
        }
        eprintln!("  {} hhc failed, falling back to interpreter", "⚠".yellow());
    }

    println!("{} {} (JIT)", "bytes run:".bold(), entry.cyan());
    Command::new("h#").args(["preview", &entry]).status()
        .map(|s| s.code().unwrap_or(0)).unwrap_or(1)
}

// ── packages ───────────────────────────────────────────────────────────────────

fn install_deps(deps: &[(String,String)]) {
    for (pkg, ver) in deps {
        if pkg.is_empty() || pkg.starts_with('!') { continue; }
        let cache = format!("{}/{}", CACHE, pkg);
        if Path::new(&cache).exists() {
            println!("  {} {} (cached)", "↯".cyan(), pkg.bold()); continue;
        }
        let t   = Instant::now();
        let url = format!("https://github.com/Bytes-Repository/{}-lib/releases/latest/download/{}.a", pkg, pkg);
        std::fs::create_dir_all(CACHE).ok();
        pb_dl(0, 0, &format!("Downloading {}", pkg), 10);
        std::thread::sleep(std::time::Duration::from_millis(80));
        pb_dl(40, t.elapsed().as_millis() as u64, &format!("Downloading {}", pkg), 5);
        let ok = Command::new("curl").args(["-sL", "-o", &cache, &url])
            .status().map(|s| s.success() && Path::new(&cache).exists()).unwrap_or(false);
        pb_dl(100, t.elapsed().as_millis() as u64, &format!("Downloading {}", pkg), 0);
        pb_done();
        if ok { println!("  {} {} v{}", "✓".green(), pkg.bold(), ver); }
        else { std::fs::remove_file(&cache).ok(); eprintln!("  {} {} not found", "⚠".yellow(), pkg); }
    }
}

fn do_install() {
    let c = cfg();
    let deps = hk_kvs(&c, "dependencies");
    let py   = hk_kvs(&c, "python");
    if deps.is_empty() && py.is_empty() { println!("No dependencies"); return; }
    println!("{} dependencies", "bytes install:".bold());
    if !deps.is_empty() { install_deps(&deps); }
    for (pkg, ver) in &py {
        let spec = if ver == "latest" { pkg.clone() } else { format!("{}=={}", pkg, ver) };
        print!("  {} python/{}", "↓".cyan(), pkg.bold());
        Command::new("pip3").args(["install", "-q", "--user", &spec]).status().ok();
        println!(" {}", "✓".green());
    }
}

fn do_add(pkg: &str) {
    let hk_path = find_hk().unwrap_or_else(|| HK.into());
    let mut c = std::fs::read_to_string(&hk_path).unwrap_or_default();
    if c.contains(&format!("-> {} =>", pkg)) {
        println!("{} already in bytes.hk", pkg.bold()); return;
    }
    let insert = format!("-> {} => latest\n", pkg);
    if c.contains("[dependencies]") {
        c = c.replace("[dependencies]\n", &format!("[dependencies]\n{}", insert));
    } else {
        c.push_str(&format!("\n[dependencies]\n{}", insert));
    }
    std::fs::write(&hk_path, c).unwrap();
    println!("{} {} added — run {} to install", "✓".green(), pkg.bold(), "bytes install".cyan());
}

// ── new project ────────────────────────────────────────────────────────────────

fn do_new(name: &str) {
    std::fs::create_dir_all(format!("{}/src", name)).unwrap();
    std::fs::create_dir_all(format!("{}/.cache", name)).unwrap();
    let hk = format!(r#"! H# project — bytes.hk
! Docs: https://hackeros-linux-system.github.io/HackerOS-Website/tools-docs/hk.html

[project]
-> name => {n}
-> version => 0.1.0
-> edition => 2026

[build]
-> entry => src/main.h#
-> backend => cranelift

[release]
-> backend => hhc
-> optimize => O3
-> lto => true
-> strip => true

[run]
-> entry => src/main.h#

[dependencies]
! use "bytes -> pkg" in .h# files, then: bytes add pkg && bytes install

[python]
! bytes python numpy

[workspace]
-> members => []
"#, n=name);
    std::fs::write(format!("{}/{}", name, HK), hk).unwrap();
    std::fs::write(format!("{}/src/main.h#", name),
        format!(";; {} — created with bytes\nfn main() is\n    write(bold(\"Hello from {}!\"))\nend\n", name, name)
    ).unwrap();
    std::fs::write(format!("{}/.gitignore", name), "build/\n.cache/\n").unwrap();
    println!("{} {} {}", "✓".green().bold(), "Created:".bold(), name.cyan());
    println!("  {}/{HK}\n  {}/src/main.h#", name, name);
    println!("\n  {}", format!("cd {} && bytes run", name).cyan());
}

fn do_new_ws(name: &str) {
    std::fs::create_dir_all(name).unwrap();
    let hk = format!(r#"! H# workspace — bytes.hk
[workspace]
-> name => {n}
-> version => 0.1.0
-> members => ["app", "lib"]

[build]
-> backend => cranelift

[release]
-> backend => hhc
-> optimize => O3
-> lto => true
"#, n=name);
    std::fs::write(format!("{}/{}", name, HK), hk).unwrap();
    for m in &["app", "lib"] {
        let mp = format!("{}/{}", name, m);
        std::fs::create_dir_all(format!("{}/src", mp)).unwrap();
        std::fs::write(format!("{}/{}", mp, HK),
            format!("[project]\n-> name => {m}\n-> version => 0.1.0\n\n[build]\n-> entry => src/main.h#\n-> output => build/{m}\n\n[dependencies]\n")
        ).unwrap();
        std::fs::write(format!("{}/src/main.h#", mp),
            format!(";; {}\nfn main() is write(\"hello from {}\") end\n", m, m)
        ).unwrap();
    }
    println!("{} {} {}", "✓".green().bold(), "Workspace:".bold(), name.cyan());
    println!("  {}/{HK}\n  {}/app/ + {}/lib/", name, name, name);
    println!("\n  {}", format!("cd {} && bytes build", name).cyan());
}

// ── settings TUI ───────────────────────────────────────────────────────────────

fn do_settings() {
    let home    = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    let s_path  = format!("{}/.bytes_settings.hk", home);
    println!("{}", "bytes settings".bold().cyan());
    println!("  Config: {}", s_path.dimmed());
    println!();
    println!("  {} Default backend (cranelift/hhc/O2)", "[1]".bold());
    println!("  {} Clear project cache", "[2]".bold());
    println!("  {} Show cache size", "[3]".bold());
    println!("  {} Quit", "[q]".bold());
    print!("\n  Choice: ");
    io::stdout().flush().ok();
    let mut inp = String::new();
    io::stdin().read_line(&mut inp).ok();
    match inp.trim() {
        "1" => {
            print!("  Backend [cranelift/hhc/O2]: ");
            io::stdout().flush().ok();
            let mut b = String::new();
            io::stdin().read_line(&mut b).ok();
            std::fs::write(&s_path, format!("[defaults]\n-> backend => {}\n", b.trim())).unwrap();
            println!("  {} saved", "✓".green());
        }
        "2" => { std::fs::remove_dir_all(CACHE).ok(); println!("  {} .cache cleared", "✓".green()); }
        "3" => {
            let sz: u64 = std::fs::read_dir(CACHE).ok().map(|d|
                d.flatten().map(|e| e.metadata().map(|m| m.len()).unwrap_or(0)).sum()
            ).unwrap_or(0);
            println!("  Cache: {} KB", sz/1024);
        }
        _ => {}
    }
}

// ── usage ──────────────────────────────────────────────────────────────────────

fn usage() {
    println!("{} {}", format!("bytes {}", VERSION).bold().cyan(), "— H# unified build system + JIT runtime".bold());
    println!();
    println!("{}:", "BUILD".bold());
    println!("  {}            Cranelift (fast dev build)", "bytes build".cyan());
    println!("  {}   hhc LLVM O3 (release)", "bytes build --release".cyan());
    println!("  {}       hhc LLVM O2", "bytes build --O2".cyan());
    println!("  {}  Build specific file", "bytes build --file <f.h#>".cyan());
    println!();
    println!("{}:", "RUN".bold());
    println!("  {}              Interpreter JIT (fast startup)", "bytes run".cyan());
    println!("  {}     hhc O3 JIT (max perf)", "bytes run --release".cyan());
    println!("  {}    Run specific file", "bytes run --file <f.h#>".cyan());
    println!();
    println!("{}:", "PACKAGES".bold());
    println!("  {}          Install all from bytes.hk", "bytes install".cyan());
    println!("  {}     Add package", "bytes add <pkg>".cyan());
    println!("  {}  Remove package", "bytes remove <pkg>".cyan());
    println!("  {}          Update all", "bytes update".cyan());
    println!("  {}    Install Python pkg", "bytes python <pkg>".cyan());
    println!("  {}            List packages", "bytes list".cyan());
    println!();
    println!("{}:", "PROJECT".bold());
    println!("  {}       New project", "bytes new <name>".cyan());
    println!("  {}  New workspace", "bytes new-workspace <n>".cyan());
    println!("  {}         TUI settings", "bytes settings".cyan());
    println!("  {}             Show info", "bytes info".cyan());
    println!();
    println!("{}:", "CLEAN".bold());
    println!("  {}            Remove .cache/", "bytes clean".cyan());
    println!("  {}  Remove .cache/ + build/", "bytes clean --everything".cyan());
    println!();
    println!("  Config: {} (HK format)", "bytes.hk".yellow());
    println!("  Cache:  {} (isolated per project)", ".cache/".dimmed());
    println!("  Output: {} (ELF / .so / .a)", "build/".dimmed());
}

// ── main ───────────────────────────────────────────────────────────────────────

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd  = args.get(1).map(|s| s.as_str()).unwrap_or("help");
    let has  = |f: &str| args.iter().any(|a| a == f);
    let flag = |f: &str| args.iter().position(|a| a == f).and_then(|i| args.get(i+1)).map(|s| s.as_str());

    let code = match cmd {
        "new"             => { do_new(args.get(2).map(|s| s.as_str()).unwrap_or("myapp")); 0 }
        "new-workspace" | "new-ws" => { do_new_ws(args.get(2).map(|s| s.as_str()).unwrap_or("ws")); 0 }
        "build" => {
            let mode = if has("--release") { "release" } else if has("--O2") { "O2" } else { "cranelift" };
            do_build(flag("--file"), mode)
        }
        "run" => do_run(flag("--file"), has("--release")),
        "install" => { do_install(); 0 }
        "add" => {
            let p = args.get(2).map(|s| s.as_str()).unwrap_or("");
            if p.is_empty() { eprintln!("usage: bytes add <pkg>"); 1 } else { do_add(p); 0 }
        }
        "remove" => {
            let p = args.get(2).map(|s| s.as_str()).unwrap_or("");
            let hk = find_hk().unwrap_or_else(|| HK.into());
            let new: String = std::fs::read_to_string(&hk).unwrap_or_default().lines()
                .filter(|l| !l.contains(&format!("-> {} =>", p)))
                .map(|l| format!("{}\n", l)).collect();
            std::fs::write(&hk, new).unwrap();
            std::fs::remove_file(format!("{}/{}", CACHE, p)).ok();
            println!("{} Removed {}", "✓".green(), p.bold()); 0
        }
        "update" => {
            let c = cfg();
            let deps = hk_kvs(&c, "dependencies");
            for (pkg, _) in &deps { std::fs::remove_file(format!("{}/{}", CACHE, pkg)).ok(); }
            do_install(); 0
        }
        "python" => {
            let p = args.get(2).map(|s| s.as_str()).unwrap_or("");
            if p.is_empty() { eprintln!("usage: bytes python <pkg>"); 1 }
            else {
                Command::new("pip3").args(["install", "--user", p]).status().ok();
                do_add(&format!("python::{}", p)); 0
            }
        }
        "list" => {
            let c = cfg();
            println!("{}", "H# packages:".bold());
            for (k,v) in hk_kvs(&c, "dependencies") { println!("  {} = {}", k.cyan(), v); }
            println!("{}", "Python packages:".bold());
            for (k,v) in hk_kvs(&c, "python") { println!("  {} = {}", k.cyan(), v); }
            0
        }
        "clean" => {
            std::fs::remove_dir_all(CACHE).ok();
            if has("--everything") { std::fs::remove_dir_all(BUILD).ok(); println!("{} .cache/ + build/ removed", "✓".green()); }
            else { println!("{} .cache/ removed", "✓".green()); }
            0
        }
        "info" => {
            let c = cfg();
            println!("{} {}", "Name:".bold(), hk_str(&c,"project","name").unwrap_or_default().cyan());
            println!("{} {}", "Version:".bold(), hk_str(&c,"project","version").unwrap_or_default());
            println!("{} {}", "Entry:".bold(), hk_str(&c,"build","entry").or_else(|| hk_str(&c,"run","entry")).unwrap_or_default());
            let mems = hk_arr(&c,"workspace","members");
            if !mems.is_empty() { println!("{} {}", "Workspace:".bold(), mems.join(", ").yellow()); }
            0
        }
        "workspace" => {
            let mems = hk_arr(&cfg(), "workspace", "members");
            if mems.is_empty() { println!("No workspace"); }
            else { for m in &mems { println!("  - {}", m.cyan()); } }
            0
        }
        "settings" => { do_settings(); 0 }
        _ => { usage(); 0 }
    };
    std::process::exit(code);
}
