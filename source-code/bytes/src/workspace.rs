use colored::*;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::config::{BytesProject, SUPPORTED_LANGUAGES, WorkspaceConfig};
use crate::progress::{BytesBar, BarTheme};

/// Build result for a single member
#[derive(Debug)]
pub struct MemberResult {
    pub name:     String,
    pub language: String,
    pub success:  bool,
    pub output:   String,
    pub elapsed:  std::time::Duration,
}

/// Build all workspace members in parallel or sequentially
pub fn build_workspace(
    ws:      &WorkspaceConfig,
    release: bool,
    verbose: bool,
) -> anyhow::Result<Vec<MemberResult>> {
    let parallel = ws.mode.as_deref() != Some("standard");
    let members: Vec<_> = ws.members.iter().map(|m| {
        let lang = ws.languages.get(m).map(|s| s.as_str()).unwrap_or("h#");
        (m.clone(), lang.to_string())
    }).collect();

    println!();
    println!(
        "  {}  {} workspace ({} member(s), {} mode)",
             "bytes".cyan().bold(),
             if release { "release".yellow() } else { "dev".green() },
                 members.len(),
             ws.mode.as_deref().unwrap_or("standard")
    );
    println!();

    if parallel && members.len() > 1 {
        build_parallel(&members, release, verbose)
    } else {
        build_sequential(&members, release, verbose)
    }
}

fn build_sequential(
    members: &[(String, String)],
                    release: bool,
                    verbose: bool,
) -> anyhow::Result<Vec<MemberResult>> {
    let mut results = Vec::new();
    for (name, lang) in members {
        let r = build_member(name, lang, release, verbose);
        let ok = r.success;
        results.push(r);
        if !ok {
            eprintln!("  {} member {} failed", "✗".red().bold(), name.cyan());
        }
    }
    Ok(results)
}

fn build_parallel(
    members: &[(String, String)],
                  release: bool,
                  verbose: bool,
) -> anyhow::Result<Vec<MemberResult>> {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let results = Arc::new(Mutex::new(Vec::new()));
    let mut handles = Vec::new();

    for (name, lang) in members {
        let name  = name.clone();
        let lang  = lang.clone();
        let res   = Arc::clone(&results);
        let h = thread::spawn(move || {
            let r = build_member(&name, &lang, release, verbose);
            res.lock().unwrap().push(r);
        });
        handles.push(h);
    }
    for h in handles {
        h.join().ok();
    }
    let mut r = results.lock().unwrap().drain(..).collect::<Vec<_>>();
    // Sort by member name for deterministic output
    r.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(r)
}

/// Build a single workspace member according to its language
fn build_member(name: &str, lang: &str, release: bool, verbose: bool) -> MemberResult {
    let dir = Path::new(name);
    let t0  = std::time::Instant::now();

    if !dir.exists() {
        return MemberResult {
            name:     name.to_string(),
            language: lang.to_string(),
            success:  false,
            output:   format!("directory `{}` not found", name),
            elapsed:  t0.elapsed(),
        };
    }

    let (success, output) = match lang {
        "h#" | "hsharp" => build_hsharp(dir, release, verbose),
        "rust"           => build_rust(dir, release, verbose),
        "c"              => build_c(dir, release, verbose),
        "cpp" | "c++"   => build_cpp(dir, release, verbose),
        "zig"            => build_zig(dir, release, verbose),
        "odin"           => build_odin(dir, release, verbose),
        "crystal"        => build_crystal(dir, release, verbose),
        "typescript"     => build_typescript(dir, release, verbose),
        "javascript"     => build_javascript(dir, verbose),
        "golang" | "go"  => build_go(dir, release, verbose),
        "kotlin"         => build_kotlin(dir, release, verbose),
        "lua"            => build_lua(dir, verbose),
        "dart"           => build_dart(dir, release, verbose),
        "vala"           => build_vala(dir, release, verbose),
        "python"         => build_python(dir, verbose),
        "nim"            => build_nim(dir, release, verbose),
        "d"              => build_dlang(dir, release, verbose),
        _                => (false, format!("unsupported language `{}`", lang)),
    };

    MemberResult {
        name:     name.to_string(),
        language: lang.to_string(),
        success,
        output,
        elapsed:  t0.elapsed(),
    }
}

// ── Language build helpers ────────────────────────────────────────────────────

fn run_cmd(args: &[&str], dir: &Path, verbose: bool) -> (bool, String) {
    let mut cmd = Command::new(args[0]);
    cmd.args(&args[1..]).current_dir(dir);
    if !verbose {
        cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    }
    match cmd.output() {
        Ok(o) => {
            let out = format!(
                "{}{}",
                String::from_utf8_lossy(&o.stdout),
                              String::from_utf8_lossy(&o.stderr)
            );
            (o.status.success(), out)
        }
        Err(e) => (false, format!("exec error: {}", e)),
    }
}

fn build_hsharp(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    // Use `bytes run` (JIT) or `h# build` for release
    if release {
        let entry = dir.join("src/main.h#");
        let out   = dir.join("build/main");
        std::fs::create_dir_all(dir.join("build")).ok();
        run_cmd(
            &["hsharp", "build", entry.to_str().unwrap_or("src/main.h#"),
                "-o", out.to_str().unwrap_or("build/main")],
                dir, verbose,
        )
    } else {
        // Just check syntax for dev builds
        run_cmd(&["hsharp", "check"], dir, verbose)
    }
}

fn build_rust(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    let mut args = vec!["cargo", "build"];
    if release { args.push("--release"); }
    run_cmd(&args, dir, verbose)
}

fn build_c(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    // Find all .c files
    let src: Vec<_> = walkdir::WalkDir::new(dir)
    .max_depth(3).into_iter().flatten()
    .filter(|e| e.path().extension().map(|x| x == "c").unwrap_or(false))
    .map(|e| e.path().display().to_string())
    .collect();
    if src.is_empty() {
        return (true, "no .c files".into());
    }
    std::fs::create_dir_all(dir.join("build")).ok();
    let out = dir.join("build/main");
    let mut args = vec!["cc"];
    args.extend(src.iter().map(|s| s.as_str()));
    let out_str = out.display().to_string();
    args.extend_from_slice(&["-o", &out_str]);
    if release { args.extend_from_slice(&["-O3", "-flto"]); }
    run_cmd(&args, dir, verbose)
}

fn build_cpp(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    let src: Vec<_> = walkdir::WalkDir::new(dir)
    .max_depth(3).into_iter().flatten()
    .filter(|e| {
        let ext = e.path().extension().map(|x| x.to_string_lossy().to_string());
        matches!(ext.as_deref(), Some("cpp") | Some("cc") | Some("cxx"))
    })
    .map(|e| e.path().display().to_string())
    .collect();
    if src.is_empty() {
        return (true, "no .cpp files".into());
    }
    std::fs::create_dir_all(dir.join("build")).ok();
    let out = dir.join("build/main");
    let mut args = vec!["c++"];
    args.extend(src.iter().map(|s| s.as_str()));
    let out_str = out.display().to_string();
    args.extend_from_slice(&["-o", &out_str]);
    if release { args.extend_from_slice(&["-O3", "-flto", "-lstdc++"]); }
    run_cmd(&args, dir, verbose)
}

fn build_zig(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    let mode = if release { "ReleaseFast" } else { "Debug" };
    run_cmd(&["zig", "build", &format!("-Doptimize={}", mode)], dir, verbose)
}

fn build_odin(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    std::fs::create_dir_all(dir.join("build")).ok();
    let mut args = vec!["odin", "build", "src", "-out:build/main"];
    if release { args.push("-o:aggressive"); }
    run_cmd(&args, dir, verbose)
}

fn build_crystal(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    let entry = "src/main.cr";
    std::fs::create_dir_all(dir.join("build")).ok();
    if release {
        run_cmd(&["crystal", "build", "--release", "-o", "build/main", entry], dir, verbose)
    } else {
        run_cmd(&["crystal", "build", "-o", "build/main", entry], dir, verbose)
    }
}

fn build_typescript(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    // Try deno compile, fall back to tsc
    if which("deno") {
        let entry = "src/main.ts";
        if release {
            return run_cmd(&["deno", "compile", "--allow-all", entry], dir, verbose);
        }
        return run_cmd(&["deno", "check", entry], dir, verbose);
    }
    run_cmd(&["tsc", "--noEmit"], dir, verbose)
}

fn build_javascript(dir: &Path, verbose: bool) -> (bool, String) {
    // Just syntax check with node --check
    run_cmd(&["node", "--check", "src/main.js"], dir, verbose)
}

fn build_go(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    if release {
        run_cmd(&["go", "build", "-ldflags=-s -w", "-o", "build/main", "./..."], dir, verbose)
    } else {
        run_cmd(&["go", "build", "./..."], dir, verbose)
    }
}

fn build_kotlin(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    std::fs::create_dir_all(dir.join("build")).ok();
    run_cmd(
        &["kotlinc", "src", "-include-runtime", "-d", "build/main.jar"],
        dir, verbose,
    )
}

fn build_lua(dir: &Path, verbose: bool) -> (bool, String) {
    // Syntax check via luac
    run_cmd(&["luac", "-p", "src/main.lua"], dir, verbose)
}

fn build_dart(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    if release {
        std::fs::create_dir_all(dir.join("build")).ok();
        run_cmd(&["dart", "compile", "exe", "bin/main.dart", "-o", "build/main"], dir, verbose)
    } else {
        run_cmd(&["dart", "analyze"], dir, verbose)
    }
}

fn build_vala(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    let src: Vec<_> = walkdir::WalkDir::new(dir)
    .max_depth(3).into_iter().flatten()
    .filter(|e| e.path().extension().map(|x| x == "vala").unwrap_or(false))
    .map(|e| e.path().display().to_string())
    .collect();
    if src.is_empty() {
        return (true, "no .vala files".into());
    }
    std::fs::create_dir_all(dir.join("build")).ok();
    let out = dir.join("build/main");
    let out_str = out.display().to_string();
    let mut args = vec!["valac", "-o", &out_str];
    if release { args.extend_from_slice(&["-X", "-O3"]); }
    args.extend(src.iter().map(|s| s.as_str()));
    run_cmd(&args, dir, verbose)
}

fn build_python(dir: &Path, verbose: bool) -> (bool, String) {
    run_cmd(&["python3", "-m", "py_compile", "src/main.py"], dir, verbose)
}

fn build_nim(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    std::fs::create_dir_all(dir.join("build")).ok();
    if release {
        run_cmd(
            &["nim", "c", "-d:release", "--opt:speed", "-o:build/main", "src/main.nim"],
            dir, verbose,
        )
    } else {
        run_cmd(&["nim", "c", "-o:build/main", "src/main.nim"], dir, verbose)
    }
}

fn build_dlang(dir: &Path, release: bool, verbose: bool) -> (bool, String) {
    std::fs::create_dir_all(dir.join("build")).ok();
    let mut args = vec!["dmd", "-ofbuild/main"];
    if release { args.extend_from_slice(&["-O", "-release", "-inline"]); }
    args.push("src/main.d");
    run_cmd(&args, dir, verbose)
}

fn which(cmd: &str) -> bool {
    Command::new("which").arg(cmd)
    .stdout(std::process::Stdio::null())
    .stderr(std::process::Stdio::null())
    .status()
    .map(|s| s.success())
    .unwrap_or(false)
}

// ── Workspace print summary ───────────────────────────────────────────────────

pub fn print_summary(results: &[MemberResult]) {
    println!();
    println!("  {}", "── Workspace build summary ──────────────────".dimmed());
    let mut ok = 0usize;
    let mut fail = 0usize;
    for r in results {
        let status = if r.success {
            ok += 1;
            "✓".green().bold()
        } else {
            fail += 1;
            "✗".red().bold()
        };
        println!(
            "  {} {:<20} {} ({:.0?})",
                 status,
                 r.name.cyan(),
                 r.language.dimmed(),
                 r.elapsed,
        );
        if !r.success && !r.output.is_empty() {
            for line in r.output.lines().take(5) {
                println!("      {}", line.dimmed());
            }
        }
    }
    println!("  {}", "─".repeat(48).dimmed());
    if fail == 0 {
        println!(
            "  {} all {} member(s) built successfully",
                 "✓".green().bold(),
                 ok
        );
    } else {
        println!(
            "  {} {}/{} succeeded, {} failed",
            "✗".red().bold(),
                 ok,
                 ok + fail,
                 fail,
        );
    }
    println!();
}

// ── New workspace scaffolding ─────────────────────────────────────────────────

/// Scaffold a new multi-language workspace
pub fn scaffold_workspace(name: &str, mode: &str, members: &[(&str, &str)]) -> anyhow::Result<()> {
    use crate::config::workspace_bytes_hk;

    let root = Path::new(name);
    anyhow::ensure!(!root.exists(), "directory `{}` already exists", name);

    std::fs::create_dir_all(root)?;
    std::fs::write(root.join("bytes.hk"), workspace_bytes_hk(name, members))?;
    std::fs::write(root.join(".gitignore"), "build/\n.cache/\n*.jit\n")?;

    for (member, lang) in members {
        scaffold_member(root, member, lang)?;
    }

    println!("  {} {} ({} workspace)", "Created:".green().bold(), name.cyan(), mode);
    for (m, l) in members {
        println!("  {}   {}/{}", "↳".dimmed(), m.cyan(), l.dimmed());
    }
    println!();
    println!("  {} cd {} && bytes build", "Next:".bold(), name.dimmed());
    Ok(())
}

fn scaffold_member(root: &Path, name: &str, lang: &str) -> anyhow::Result<()> {
    let dir = root.join(name);
    std::fs::create_dir_all(dir.join("src"))?;
    std::fs::create_dir_all(dir.join("build"))?;

    let main_content = member_main_template(name, lang);
    let main_file    = member_main_path(lang);
    std::fs::write(dir.join("src").join(main_file), main_content)?;

    // Write per-member bytes.hk
    let member_hk = format!(
        "[package]\n-> name    => {}\n-> version => 0.1.0\n\n[build]\n-> lang   => {}\n-> entry  => src/{}\n",
        name, lang, member_main_path(lang)
    );
    std::fs::write(dir.join("bytes.hk"), member_hk)?;
    Ok(())
}

fn member_main_path(lang: &str) -> &'static str {
    match lang {
        "h#" | "hsharp"      => "main.h#",
        "rust"               => "main.rs",
        "c"                  => "main.c",
        "cpp" | "c++"       => "main.cpp",
        "zig"                => "main.zig",
        "odin"               => "main.odin",
        "crystal"            => "main.cr",
        "typescript"         => "main.ts",
        "javascript"         => "main.js",
        "golang" | "go"     => "main.go",
        "kotlin"             => "main.kt",
        "lua"                => "main.lua",
        "dart"               => "main.dart",
        "vala"               => "main.vala",
        "python"             => "main.py",
        "nim"                => "main.nim",
        "d"                  => "main.d",
        _                    => "main.h#",
    }
}

fn member_main_template(name: &str, lang: &str) -> String {
    match lang {
        "h#" | "hsharp" => format!(
            ";; {} — H# member\nfn main() is\n    write(\"Hello from {}!\")\nend\n",
                                   name, name
        ),
        "rust" => format!(
            "fn main() {{\n    println!(\"Hello from {}!\");\n}}\n",
                          name
        ),
        "c" => format!(
            "#include <stdio.h>\nint main() {{\n    printf(\"Hello from {}!\\n\");\n    return 0;\n}}\n",
                       name
        ),
        "cpp" | "c++" => format!(
            "#include <iostream>\nint main() {{\n    std::cout << \"Hello from {}!\" << std::endl;\n    return 0;\n}}\n",
                                 name
        ),
        "zig" => format!(
            "const std = @import(\"std\");\npub fn main() void {{\n    std.debug.print(\"Hello from {}!\\n\", .{{}});\n}}\n",
                         name
        ),
        "golang" | "go" => format!(
            "package main\nimport \"fmt\"\nfunc main() {{\n    fmt.Println(\"Hello from {}!\")\n}}\n",
                                   name
        ),
        "python" => format!("print(\"Hello from {}!\")\n", name),
        "typescript" => format!("console.log(\"Hello from {}!\");\n", name),
        "javascript" => format!("console.log(\"Hello from {}!\");\n", name),
        "kotlin" => format!("fun main() {{\n    println(\"Hello from {}!\")\n}}\n", name),
        "lua"    => format!("print(\"Hello from {}!\")\n", name),
        "dart"   => format!("void main() {{\n  print('Hello from {}!');\n}}\n", name),
        "crystal"=> format!("puts \"Hello from {}!\"\n", name),
        "vala"   => format!(
            "void main() {{\n    stdout.printf(\"Hello from {}!\\n\");\n}}\n",
                            name
        ),
        "nim"    => format!("echo \"Hello from {}!\"\n", name),
        "odin"   => format!("package main\nimport \"core:fmt\"\nmain :: proc() {{\n    fmt.println(\"Hello from {}!\")\n}}\n", name),
        _        => format!(";; {}\nfn main() is\n    write(\"Hello from {}!\")\nend\n", name, name),
    }
}
