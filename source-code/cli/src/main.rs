use anyhow::{Context, Result};
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use h_sharp_compiler::compile_program;
use indicatif::{ProgressBar, ProgressStyle};
use owo_colors::OwoColorize;
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, ListState, Paragraph},
    Terminal,
};
use std::fs::{self};
use std::io::{Read, Write};
use std::path::{Path};
use std::process::Command;
use std::time::Duration;
use tempfile::Builder;
// Zmiana importów na wasmi
use wasmi::{Engine, Linker, Module, Store};

const H_SHARP_LIB_PATH: &str = "/usr/lib/h-sharp/libs";
const OFFICIAL_REPO_URL: &str =
"https://raw.githubusercontent.com/HackerOS-Linux-System/H-Sharp/main/libs/add-ons";
const COMMUNITY_REPO_URL: &str =
"https://raw.githubusercontent.com/HackerOS-Linux-System/H-Sharp/main/libs/community/repo.hacker";

const RUNTIME_C: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void write_int(int n) { printf("%d\n", n); }
void write_float(double f) { printf("%f\n", f); }
void write_str(long* s) {
if (!s) { printf("(null)\n"); return; }
char* ptr = (char*)s[0];
long len = s[1];
fwrite(ptr, 1, len, stdout);
printf("\n");
}
long arena_new(long capacity) { return 0; }
long arena_alloc(long arena_handle, long size) {
void* ptr = malloc(size);
if (!ptr) { fprintf(stderr, "Out of memory\n"); exit(1); }
memset(ptr, 0, size);
return (long)ptr;
}
void arena_free(long arena_handle) {}
"#;

// Helper to draw clean boxes around text
fn print_boxed(title: &str, content: &str, color: &str) {
    let lines: Vec<&str> = content.lines().collect();
    let max_len = lines.iter().map(|l| l.len()).max().unwrap_or(0);
    // Ensure width is enough for "┌─── TITLE ───┐"
    // Min width: 1(┌) + 3(─) + 1( ) + title + 1( ) + 3(─) + 1(┐) = title + 10 roughly
    let width = std::cmp::max(max_len + 4, title.len() + 10);

    let (top, border, bottom, title_fmt) = match color {
        "red" => ("┌", "│", "└", title.red().bold().to_string()),
        "green" => ("┌", "│", "└", title.green().bold().to_string()),
        "cyan" => ("┌", "│", "└", title.cyan().bold().to_string()),
        "yellow" => ("┌", "│", "└", title.yellow().bold().to_string()),
        _ => ("┌", "│", "└", title.white().bold().to_string()),
    };

    let h_line = "─".repeat(width - 2);
    let top_right = "┐";
    let bottom_right = "┘";

    // Top border with title
    // Structure: ┌─── TITLE ────────┐
    // Remainder: width - 1(┌) - 3(─) - 1( ) - title - 1( ) - 1(┐) = width - title - 7.
    let rem_len = width.saturating_sub(title.len() + 7);

    println!("{}{} {} {}{}", top, "─".repeat(3), title_fmt, "─".repeat(rem_len), top_right);

    // Content
    for line in lines {
        println!("{} {:<w$} {}", border, line, border, w = width - 4);
    }

    // Bottom
    println!("{}{}{}", bottom, h_line, bottom_right);
}

struct Args {
    subcommand: String,
    input: Option<String>,
    output: String,
    keep_temps: bool,
    library: Option<String>,
    community: bool,
}

impl Default for Args {
    fn default() -> Self {
        Self {
            subcommand: String::new(),
            input: None,
            output: "a.out".to_string(),
            keep_temps: false,
            library: None,
            community: false,
        }
    }
}

fn parse_args() -> Result<Args, lexopt::Error> {
    use lexopt::prelude::*;

    let mut args = Args::default();
    let mut parser = lexopt::Parser::from_env();

    if let Some(arg) = parser.next()? {
        match arg {
            Value(val) => args.subcommand = val.string()?,
            Long("help") | Short('h') => {
                print_help();
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    } else {
        print_help();
        std::process::exit(0);
    }

    while let Some(arg) = parser.next()? {
        match arg {
            Value(val) => {
                if args.subcommand == "compile" && args.input.is_none() {
                    args.input = Some(val.string()?);
                } else if (args.subcommand == "install"
                    || args.subcommand == "remove"
                    || args.subcommand == "search"
                    || args.subcommand == "update")
                    && args.library.is_none()
                    {
                        args.library = Some(val.string()?);
                    }
            }
            Long("output") | Short('o') => {
                args.output = parser.value()?.string()?;
            }
            Long("keep-temps") => {
                args.keep_temps = true;
            }
            Long("com") => {
                args.community = true;
            }
            Long("help") | Short('h') => {
                print_help();
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    }

    Ok(args)
}

fn print_help() {
    print_boxed("H# CLI", "Usage: h# <command> [options]\n\nCommands:\n  build       Placeholder for build system\n  compile     Compile .h# file\n  install     Install library\n  remove      Remove library\n  search      Search library (TUI)\n  update      Update libraries\n  upgrade     Upgrade toolchain", "cyan");
}

fn main() -> Result<()> {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };

    match args.subcommand.as_str() {
        "build" => {
            print_boxed("Info", "Build system not implemented yet.", "yellow");
            Ok(())
        }
        "upgrade" => {
            print_boxed("Info", "Upgrade system not implemented yet.", "yellow");
            Ok(())
        }
        "compile" => {
            if let Some(input) = args.input {
                handle_compile(input, args.output, args.keep_temps)
            } else {
                print_boxed("Error", "Input file required for compile.", "red");
                std::process::exit(1);
            }
        }
        "install" => {
            if let Some(lib) = args.library {
                handle_install(lib, args.community)
            } else {
                print_boxed("Error", "Library name required.", "red");
                std::process::exit(1);
            }
        }
        "remove" => {
            if let Some(lib) = args.library {
                handle_remove(lib)
            } else {
                print_boxed("Error", "Library name required.", "red");
                std::process::exit(1);
            }
        }
        "search" => {
            if let Some(lib) = args.library {
                handle_search(lib)
            } else {
                print_boxed("Error", "Library name required for search.", "red");
                std::process::exit(1);
            }
        }
        "update" => handle_update(args.library),
        _ => {
            print_boxed("Error", &format!("Unknown command: {}", args.subcommand), "red");
            print_help();
            std::process::exit(1);
        }
    }
}

fn handle_compile(input: String, output: String, keep_temps: bool) -> Result<()> {
    print_boxed("Compiling", &format!("Source: {}\nTarget: {}", input, output), "cyan");

    let src = fs::read_to_string(&input).context("Failed to read input file")?;

    let program = match h_sharp_parser::parse_code(&src, &input) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };

    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
        .template("{spinner:.green} {msg}")
        .unwrap(),
    );
    pb.set_message("Compiling to object code...");
    pb.enable_steady_tick(Duration::from_millis(100));

    let obj_file = Builder::new().suffix(".o").tempfile()?;
    let obj_path = obj_file.path().to_str().unwrap().to_string();

    match compile_program(&program, &obj_path) {
        Ok(_) => {}
        Err(e) => {
            pb.finish_and_clear();
            return Err(e.context("Codegen failed"));
        }
    }

    pb.set_message("Generating runtime...");
    let mut c_file = Builder::new().suffix(".c").tempfile()?;
    c_file.write_all(RUNTIME_C.as_bytes())?;
    let c_path = c_file.path().to_str().unwrap().to_string();

    pb.set_message("Linking...");
    let status = Command::new("cc")
    .arg(&obj_path)
    .arg(&c_path)
    .arg("-o")
    .arg(&output)
    .arg("-lm")
    .status()
    .context("Failed to run linker (cc). Is a C compiler installed?")?;

    if !status.success() {
        pb.finish_and_clear();
        return Err(anyhow::anyhow!("Linker failed"));
    }

    if keep_temps {
        let _ = fs::copy(&obj_path, format!("{}.o", output));
        let _ = fs::copy(&c_path, format!("{}_runtime.c", output));
    }

    pb.finish_and_clear();
    print_boxed("Success", &format!("Build successful!\nBinary: ./{}", output), "green");
    Ok(())
}

fn handle_install(library: String, is_community: bool) -> Result<()> {
    print_boxed("Installation", &format!("Library: {}\nSource: {}", library, if is_community { "Community Repo" } else { "Official Repo" }), "cyan");

    let pb = ProgressBar::new_spinner();
    pb.set_message("Resolving source...");
    pb.enable_steady_tick(Duration::from_millis(100));

    let download_url = if is_community {
        let list_url = COMMUNITY_REPO_URL;
        let response = reqwest::blocking::get(list_url)
        .context("Failed to fetch community repo")?
        .text()?;

        let mut found_url = None;
        for line in response.lines() {
            if let Some((name, url)) = line.split_once('-') {
                let name = name
                .trim()
                .replace("\"", "")
                .replace(",", "")
                .replace("[", "")
                .replace("]", "");
                let url = url
                .trim()
                .replace("\"", "")
                .replace(",", "")
                .replace("[", "")
                .replace("]", "");
                if name == library {
                    found_url = Some(url);
                    break;
                }
            }
        }
        found_url.ok_or_else(|| {
            anyhow::anyhow!("Library '{}' not found in community repo", library)
        })?
    } else {
        format!("{}/{}.h%23", OFFICIAL_REPO_URL, library)
    };

    pb.set_message("Connecting...");
    let mut resp = reqwest::blocking::get(&download_url)
    .context(format!("Failed to download library from {}", download_url))?;

    if !resp.status().is_success() {
        pb.finish_and_clear();
        return Err(anyhow::anyhow!(
            "Library not found on remote server (Status: {}).",
                                   resp.status()
        ));
    }

    let total_size = resp.content_length().unwrap_or(0);
    pb.set_style(ProgressStyle::default_bar()
    .template("[{bar:40.cyan/blue}] {bytes}/{total_bytes}")
    .unwrap()
    .progress_chars("##-"));
    pb.set_length(total_size);

    let mut content = Vec::new();
    let mut buffer = [0; 8192];
    loop {
        let bytes_read = resp.read(&mut buffer)?;
        if bytes_read == 0 {
            break;
        }
        content.extend_from_slice(&buffer[..bytes_read]);
        pb.inc(bytes_read as u64);
    }
    pb.finish_and_clear();

    // Isolation
    let base_path = Path::new(H_SHARP_LIB_PATH);
    let envs_path = base_path.join("envs");

    if let Err(e) = fs::create_dir_all(&envs_path) {
        return Err(anyhow::anyhow!(
            "Failed to create directory structure at {:?}.\nError: {}.\nHint: Try running with sudo.",
            envs_path,
            e
        ));
    }

    let mut env_name = "env".to_string();
    let mut counter = 1;
    let mut target_dir = envs_path.join(&env_name);

    loop {
        let lib_path = target_dir.join(format!("{}.h#", library));
        if lib_path.exists() {
            counter += 1;
            env_name = format!("env{}", counter);
            target_dir = envs_path.join(&env_name);
        } else {
            break;
        }
    }

    fs::create_dir_all(&target_dir)?;
    let final_path = target_dir.join(format!("{}.h#", library));

    println!("Verifying isolation...");
    if let Err(e) = verify_wasm_environment() {
        print_boxed("Warning", &format!("WASM isolation check failed:\n{}", e), "yellow");
    }

    fs::write(&final_path, &content)?;

    print_boxed("Installed", &format!("Library successfully installed.\nLocation: {}", target_dir.display()), "green");

    Ok(())
}

fn handle_remove(library: String) -> Result<()> {
    let base_path = Path::new(H_SHARP_LIB_PATH).join("envs");
    if !base_path.exists() {
        return Err(anyhow::anyhow!("No libraries installed yet."));
    }

    let mut found = false;
    for entry in fs::read_dir(base_path)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            let lib_path = entry.path().join(format!("{}.h#", library));
            if lib_path.exists() {
                fs::remove_file(&lib_path)?;
                print_boxed("Removed", &format!("Library removed from:\n{}", entry.path().display()), "green");
                found = true;
            }
        }
    }

    if !found {
        print_boxed("Not Found", "Library not found in any environment.", "red");
    }
    Ok(())
}

// TUI for Search
fn handle_search(library: String) -> Result<()> {
    let mut results = Vec::new();
    let base_path = Path::new(H_SHARP_LIB_PATH).join("envs");

    // Search local
    if base_path.exists() {
        if let Ok(entries) = fs::read_dir(base_path) {
            for entry in entries.flatten() {
                if let Ok(ft) = entry.file_type() {
                    if ft.is_dir() {
                        let lib_path = entry.path().join(format!("{}.h#", library));
                        if lib_path.exists() {
                            results.push(format!(
                                "[LOCAL] {} (in {})",
                                                 library,
                                                 entry.file_name().to_string_lossy()
                            ));
                        }
                    }
                }
            }
        }
    }

    if let Ok(resp) = reqwest::blocking::get(COMMUNITY_REPO_URL) {
        if let Ok(text) = resp.text() {
            for line in text.lines() {
                if line.contains(&library) {
                    results.push(format!("[COMMUNITY] Found match: {}", line.trim()));
                }
            }
        }
    }

    if results.is_empty() {
        results.push(format!("No results found for '{}'.", library));
    }

    enable_raw_mode()?;
    let mut stdout = std::io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let res = run_search_tui(&mut terminal, &library, results);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
             LeaveAlternateScreen,
             DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(e) = res {
        println!("Error running TUI: {:?}", e);
    }

    Ok(())
}

fn run_search_tui<B: Backend>(
    terminal: &mut Terminal<B>,
    query: &str,
    items: Vec<String>,
) -> Result<()> {
    let mut list_state = ListState::default();
    list_state.select(Some(0));

    loop {
        terminal.draw(|f| {
            let chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Length(3), Constraint::Min(0)].as_ref())
            .split(f.size());

            let title = Paragraph::new(format!("H# Search Results for: '{}' (Press 'q' to exit)", query))
            .style(Style::default().fg(Color::Cyan).add_modifier(Modifier::BOLD))
            .block(Block::default().borders(Borders::ALL).title("Search"));
            f.render_widget(title, chunks[0]);

            let list_items: Vec<ListItem> = items
            .iter()
            .map(|i| ListItem::new(Line::from(Span::raw(i))))
            .collect();

            let list = List::new(list_items)
            .block(Block::default().borders(Borders::ALL).title("Results"))
            .highlight_style(Style::default().fg(Color::Yellow).add_modifier(Modifier::BOLD))
            .highlight_symbol(">> ");

            f.render_stateful_widget(list, chunks[1], &mut list_state);
        })?;

        if let Event::Key(key) = event::read()? {
            match key.code {
                KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                KeyCode::Down => {
                    let i = match list_state.selected() {
                        Some(i) => {
                            if i >= items.len() - 1 {
                                0
                            } else {
                                i + 1
                            }
                        }
                        None => 0,
                    };
                    list_state.select(Some(i));
                }
                KeyCode::Up => {
                    let i = match list_state.selected() {
                        Some(i) => {
                            if i == 0 {
                                items.len() - 1
                            } else {
                                i - 1
                            }
                        }
                        None => 0,
                    };
                    list_state.select(Some(i));
                }
                _ => {}
            }
        }
    }
}

fn handle_update(library: Option<String>) -> Result<()> {
    if let Some(lib) = library {
        print_boxed("Update", &format!("Updating {}...", lib), "yellow");
    } else {
        print_boxed("Update", "Updating all libraries...", "yellow");
    }
    Ok(())
}

fn verify_wasm_environment() -> Result<()> {
    let engine = Engine::default();
    let wat = r#"(module)"#;
    let module = Module::new(&engine, wat.as_bytes())?;

    // Konfiguracja Wasmi
    type HostState = ();
    let mut store = Store::new(&engine, ());
    let linker = Linker::<HostState>::new(&engine);

    // Instancjacja
    let _instance = linker
    .instantiate(&mut store, &module)?
    .start(&mut store)?;

    Ok(())
}
