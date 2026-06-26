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
    std::fs::create_dir_all(project_dir.join("tests")).unwrap();

    let manifest = serde_json::json!({
        "name": name,
        "version": "0.1.0",
        "template": template,
        "dependencies": {}
    });
    std::fs::write(project_dir.join("h#.json"), serde_json::to_string_pretty(&manifest).unwrap()).unwrap();
    std::fs::write(project_dir.join(".gitignore"), "build/\n*.c\n.cache/\n").unwrap();

    let (main_src, readme_src, test_src) = match template.as_str() {
        "cybersec" | "security" => (TEMPLATE_CYBERSEC, README_CYBERSEC, TEST_CYBERSEC),
        "net" | "network"       => (TEMPLATE_NETWORK,  README_NETWORK,  TEST_NETWORK),
        "lib"                   => (TEMPLATE_LIB,       README_LIB,      TEST_LIB),
        "web"                   => (TEMPLATE_WEB,       README_WEB,      TEST_WEB),
        "tui"                   => (TEMPLATE_TUI,       README_TUI,      TEST_TUI),
        "wasm"                  => (TEMPLATE_WASM,      README_WASM,     TEST_WASM),
        _                       => (TEMPLATE_APP,       README_APP,      TEST_APP),
    };

    std::fs::write(project_dir.join("src").join("main.h#"), main_src).unwrap();
    std::fs::write(project_dir.join("README.md"), readme_src).unwrap();
    std::fs::write(project_dir.join("tests").join("main_test.h#"), test_src).unwrap();

    println!("\n  {} {}/", "Created:".green().bold(), name);
    println!("  {} {}/src/main.h#", "Created:".green(), name);
    println!("  {} {}/tests/main_test.h#", "Created:".green(), name);
    println!("  {} {}/README.md", "Created:".green(), name);
    println!("  {} {}/h#.json", "Created:".green(), name);
    println!("\n  {}", "Get started:".bold());
    println!("    cd {}", name);
    println!("    h# preview src/main.h#    # run in interpreter mode");
    println!("    h# compile src/main.h#    # compile to native binary");
    println!("    bytes test                # run tests");
}

// ── Templates — App ──────────────────────────────────────────────────────────

const TEMPLATE_APP: &str = r#";; H# Application
fn main() is
    let name: string = "World"
    write("Hello, " + name + "!")

    let x: int = 42
    let y: int = 8
    write("Sum: " + to_string(x + y))

    for i in 1..=5 is
        write(to_string(i) + ": " + repeat("*", i))
    end
end

fn repeat(s: string, n: int) -> string is
    let mut result: string = ""
    let mut i: int = 0
    while i < n is
        result = result + s
        i += 1
    end
    return result
end
"#;

const README_APP: &str = r#"# H# App

A simple H# application.

## Run
```bash
h# preview src/main.h#
h# compile src/main.h# --release -o build/app
```

## Test
```bash
bytes test
```
"#;

const TEST_APP: &str = r#";; H# Application Tests
use "std -> test" from "test"

#[test]
fn test_repeat() is
    ;; basic repeat
    let r = repeat("*", 3)
    assert_eq(r, "***")
end

#[test]
fn test_repeat_zero() is
    let r = repeat("x", 0)
    assert_eq(r, "")
end

fn repeat(s: string, n: int) -> string is
    let mut result: string = ""
    let mut i: int = 0
    while i < n is
        result = result + s
        i += 1
    end
    return result
end
"#;

// ── Templates — CyberSec ─────────────────────────────────────────────────────

const TEMPLATE_CYBERSEC: &str = r#";; H# CyberSec Tool
use "std -> net_tcp" from "tcp"
use "std -> sec"     from "sec"
use "std -> fmt"     from "fmt"

fn main() is
    write(fmt::bold("H# CyberSec Tool v0.1"))
    write("")

    let target: string = "127.0.0.1"
    let port_start: int = 1
    let port_end:   int = 1024

    write("Target: " + target)
    write("Scanning ports " + to_string(port_start) + ".." + to_string(port_end))
    write("")

    let found: int = scan_range(target, port_start, port_end)
    write("Open ports found: " + to_string(found))
end

fn scan_range(host: string, start: int, end_port: int) -> int is
    let mut found: int = 0
    for port in start..=end_port is
        if tcp::is_open(host, port) is
            write(fmt::green("[OPEN] ") + to_string(port) + "/tcp")
            found += 1
        end
    end
    return found
end

fn xor_encrypt(data: string, key: string) -> string is
    return sec::xor(data, key)
end
"#;

const README_CYBERSEC: &str = r#"# H# CyberSec Tool

A cybersecurity tool template for H#.

## Features
- TCP port scanner
- XOR cipher
- Extensible with `std -> sec`, `std -> crypto`

## Run
```bash
h# preview src/main.h#
h# compile src/main.h# --release -o build/tool
```
"#;

const TEST_CYBERSEC: &str = r#";; CyberSec Tests
use "std -> test" from "test"
use "std -> sec"  from "sec"

#[test]
fn test_xor_roundtrip() is
    let plain = "48656c6c6f"
    let key   = "AABBCCDDEE"
    let enc   = sec::xor(plain, key)
    let dec   = sec::xor(enc, key)
    assert_eq(dec, plain)
end

#[test]
fn test_rot13() is
    let result = sec::rot13("Hello")
    assert_eq(result, "Uryyb")
    assert_eq(sec::rot13(result), "Hello")
end
"#;

// ── Templates — Network ──────────────────────────────────────────────────────

const TEMPLATE_NETWORK: &str = r#";; H# Network Tool
use "std -> net_tcp"  from "tcp"
use "std -> net_dns"  from "dns"
use "std -> net_http" from "http"
use "std -> fmt"      from "fmt"

fn main() is
    write(fmt::bold("H# Network Tool v0.1"))
    write("")

    let host: string = "example.com"
    write("Resolving: " + host)

    let ip = dns::resolve(host)
    write("IP: " + ip)
    write("")

    write("HTTP GET https://" + host)
    let resp = http::get("https://" + host)
    write("Status: " + to_string(resp.status))
    write("Body length: " + to_string(resp.body.len()) + " bytes")
end
"#;

const README_NETWORK: &str = r#"# H# Network Tool

A network utilities template for H#.

## Features
- DNS resolution
- HTTP client
- TCP utilities

## Run
```bash
h# preview src/main.h#
```
"#;

const TEST_NETWORK: &str = r#";; Network Tests
use "std -> test"    from "test"
use "std -> net_ip"  from "ip"

#[test]
fn test_ip_parse() is
    assert_true(ip::is_valid("192.168.1.1"))
    assert_true(ip::is_private("192.168.1.1"))
    assert_true(ip::is_private("10.0.0.1"))
    assert_true(!ip::is_private("8.8.8.8"))
end

#[test]
fn test_ip_invalid() is
    assert_true(!ip::is_valid("999.999.999.999"))
    assert_true(!ip::is_valid("not-an-ip"))
end
"#;

// ── Templates — Library ──────────────────────────────────────────────────────

const TEMPLATE_LIB: &str = r#";; H# Library

/// Add two integers together.
pub fn add(a: int, b: int) -> int = a + b

/// Subtract b from a.
pub fn sub(a: int, b: int) -> int = a - b

/// Multiply two integers.
pub fn mul(a: int, b: int) -> int = a * b

/// Greet a name.
pub fn greet(name: string) -> string is
    return "Hello, " + name + "!"
end

/// Clamp a value to [min, max].
pub fn clamp(val: int, min: int, max: int) -> int is
    if val < min is return min end
    if val > max is return max end
    return val
end
"#;

const README_LIB: &str = r#"# H# Library

A reusable H# library.

## Usage
```hsharp
use "local -> mylib" from "lib"

fn main() is
    write(lib::greet("World"))
    write(to_string(lib::add(2, 3)))
end
```
"#;

const TEST_LIB: &str = r#";; Library Tests
use "std -> test" from "test"

#[test]
fn test_add() is
    assert_eq(add(2, 3), 5)
    assert_eq(add(-1, 1), 0)
    assert_eq(add(0, 0), 0)
end

#[test]
fn test_sub() is
    assert_eq(sub(10, 3), 7)
    assert_eq(sub(0, 5), -5)
end

#[test]
fn test_mul() is
    assert_eq(mul(3, 4), 12)
    assert_eq(mul(-2, 5), -10)
end

#[test]
fn test_clamp() is
    assert_eq(clamp(5, 1, 10), 5)
    assert_eq(clamp(-5, 0, 100), 0)
    assert_eq(clamp(200, 0, 100), 100)
end

#[test]
fn test_greet() is
    assert_eq(greet("H#"), "Hello, H#!")
end

pub fn add(a: int, b: int) -> int = a + b
pub fn sub(a: int, b: int) -> int = a - b
pub fn mul(a: int, b: int) -> int = a * b
pub fn greet(name: string) -> string is return "Hello, " + name + "!" end
pub fn clamp(val: int, min: int, max: int) -> int is
    if val < min is return min end
    if val > max is return max end
    return val
end
"#;

// ── Templates — Web ──────────────────────────────────────────────────────────

const TEMPLATE_WEB: &str = r#";; H# Web Application
use "std -> net_http" from "http"
use "std -> json"     from "json"
use "std -> log"      from "log"
use "std -> fmt"      from "fmt"

fn main() is
    let port: int = 8080
    write(fmt::bold("H# Web Server v0.1"))
    write("Listening on http://0.0.0.0:" + to_string(port))
    write("")

    http::listen("0.0.0.0", port, handle_request)
end

fn handle_request(method: string, path: string, body: string) -> http::Response is
    log::info(method + " " + path)

    if path == "/" is
        return http::ok(html_index(), "text/html")
    end

    if path == "/api/hello" && method == "GET" is
        let data = json::object([
            ("message", "Hello from H#!"),
            ("version", "0.6"),
            ("lang",    "H#")
        ])
        return http::json(200, data)
    end

    if path == "/api/echo" && method == "POST" is
        return http::json(200, body)
    end

    return http::not_found("404 Not Found")
end

fn html_index() -> string is
    return "<!DOCTYPE html><html><head><title>H# Web</title></head>" +
           "<body><h1>H# Web Server</h1><p>Built with H# v0.6</p>" +
           "<p><a href=\"/api/hello\">GET /api/hello</a></p>" +
           "</body></html>"
end
"#;

const README_WEB: &str = r#"# H# Web Application

A minimal HTTP web server template for H#.

## Run
```bash
h# preview src/main.h#
# Open http://localhost:8080
```

## Routes
- `GET /` — HTML index page
- `GET /api/hello` — JSON hello response
- `POST /api/echo` — Echo body as JSON
"#;

const TEST_WEB: &str = r#";; Web Application Tests
use "std -> test"     from "test"
use "std -> net_http" from "http"
use "std -> json"     from "json"

#[test]
fn test_json_response() is
    let data = json::object([("key", "value")])
    let s = json::stringify(data)
    assert_true(s.contains("key"))
    assert_true(s.contains("value"))
end

#[test]
fn test_json_parse() is
    ;; {{ / }} are H#'s escaped-literal-brace syntax — JSON's braces would
    ;; otherwise be parsed as string interpolation markers.
    let raw = "{{\"name\":\"H#\",\"version\":\"0.6\"}}"
    let obj = json::parse(raw)
    assert_eq(json::get_str(obj, "name"), "H#")
end
"#;

// ── Templates — TUI ──────────────────────────────────────────────────────────

const TEMPLATE_TUI: &str = r#";; H# TUI Application
use "std -> term" from "term"
use "std -> fmt"  from "fmt"
use "std -> cli"  from "cli"

fn main() is
    term::clear()
    term::hide_cursor()

    draw_header()
    draw_menu()

    let choice = read_choice()
    handle_choice(choice)

    term::show_cursor()
end

fn draw_header() is
    let w = term::width()
    write(fmt::bold(fmt::cyan(center("H# TUI App v0.1", w))))
    write(fmt::dim(repeat("─", w)))
    write("")
end

fn draw_menu() is
    write("  " + fmt::green("[1]") + " Option A")
    write("  " + fmt::green("[2]") + " Option B")
    write("  " + fmt::green("[3]") + " Option C")
    write("  " + fmt::red("[q]") + " Quit")
    write("")
    write("Choose: ")
end

fn read_choice() -> string is
    return cli::prompt("")
end

fn handle_choice(choice: string) is
    if choice == "1" is
        write("You chose: Option A")
    elsif choice == "2" is
        write("You chose: Option B")
    elsif choice == "3" is
        write("You chose: Option C")
    elsif choice == "q" is
        write("Goodbye!")
    else is
        write("Unknown choice: " + choice)
    end
end

fn center(s: string, width: int) -> string is
    let pad = (width - s.len()) / 2
    return repeat(" ", pad) + s
end

fn repeat(s: string, n: int) -> string is
    let mut r: string = ""
    let mut i: int = 0
    while i < n is r = r + s; i += 1 end
    return r
end
"#;

const README_TUI: &str = r#"# H# TUI Application

An interactive terminal UI application template for H#.

## Features
- Terminal width detection
- Color output
- Interactive menu

## Run
```bash
h# preview src/main.h#
h# compile src/main.h# --release -o build/app
```
"#;

const TEST_TUI: &str = r#";; TUI Tests
use "std -> test" from "test"

#[test]
fn test_center() is
    let result = center("hi", 10)
    assert_eq(result.len(), 10)
    assert_true(result.contains("hi"))
end

#[test]
fn test_repeat() is
    assert_eq(repeat("─", 3), "───")
    assert_eq(repeat("x", 0), "")
end

fn center(s: string, width: int) -> string is
    let pad = (width - s.len()) / 2
    return repeat(" ", pad) + s
end

fn repeat(s: string, n: int) -> string is
    let mut r: string = ""
    let mut i: int = 0
    while i < n is r = r + s; i += 1 end
    return r
end
"#;

// ── Templates — WASM ─────────────────────────────────────────────────────────

const TEMPLATE_WASM: &str = r#";; H# WASM Module
;; Compile: h# compile src/main.h# --target wasm32 -o build/module.wasm

/// Add two numbers — exported to JavaScript as wasmAdd(a, b)
#[export]
pub fn add(a: int, b: int) -> int = a + b

/// Multiply — exported as wasmMul(a, b)
#[export]
pub fn mul(a: int, b: int) -> int = a * b

/// Fibonacci
#[export]
pub fn fib(n: int) -> int is
    if n <= 1 is return n end
    return fib(n - 1) + fib(n - 2)
end

/// String length (from WASM memory)
#[export]
pub fn str_len(s: string) -> int = s.len()
"#;

const README_WASM: &str = r#"# H# WASM Module

A WebAssembly module template for H#.

## Compile
```bash
h# compile src/main.h# --target wasm32 -o build/module.wasm
```

## Use from JavaScript
```javascript
const wasm = await WebAssembly.instantiateStreaming(fetch('module.wasm'));
const { add, mul, fib } = wasm.instance.exports;
console.log(add(2, 3)); // 5
console.log(fib(10));   // 55
```
"#;

const TEST_WASM: &str = r#";; WASM Module Tests
use "std -> test" from "test"

#[test]
fn test_add() is
    assert_eq(add(2, 3), 5)
    assert_eq(add(-1, 1), 0)
end

#[test]
fn test_mul() is
    assert_eq(mul(3, 4), 12)
end

#[test]
fn test_fib() is
    assert_eq(fib(0), 0)
    assert_eq(fib(1), 1)
    assert_eq(fib(10), 55)
end

pub fn add(a: int, b: int) -> int = a + b
pub fn mul(a: int, b: int) -> int = a * b
pub fn fib(n: int) -> int is
    if n <= 1 is return n end
    return fib(n - 1) + fib(n - 2)
end
"#;
