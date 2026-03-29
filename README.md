# H# Programming Language

**H#** (H-Sharp) is a compiled, statically-typed programming language designed for **cybersecurity professionals**. It aims to replace Python in security tooling with a language that compiles to fast, fully-static native binaries.

---

## Features

| Feature | Description |
|---|---|
| **Syntax** | Ruby/Python-inspired, clean and readable |
| **Type system** | Static typing with inference |
| **Memory safety** | Rust-like ownership model in semantics |
| **Unsafe + Arena** | `unsafe arena` blocks with arena allocator |
| **Cross-compilation** | Linux, Windows, macOS (x86\_64 & ARM64) |
| **Static binaries** | Fully static by default (musl on Linux) |
| **Preview mode** | Built-in interpreter for rapid dev iteration |
| **Elm-like errors** | Beautiful, pinpointed error messages |

---

## Quick Start

```bash
# Create a new cybersec project
h# new mytool --template cybersec

cd mytool

# Run in interpreter (fast dev loop)
h# preview src/main.h#

# Compile to native binary
h# build

# Cross-compile to Windows
h# build --target windows-x86_64

# Check syntax + types only
h# check
```

---

## H# Syntax

### Hello World
```h-sharp
fn main() do
    println("Hello from H#!")
end
```

### Variables & Types
```h-sharp
let x: int = 42
let mut counter: int = 0
let name: string = "hsharp"
let flag: bool = true
let ratio: f64 = 3.14
let data: bytes = [0xDE, 0xAD, 0xBE, 0xEF]
```

### Functions
```h-sharp
fn add(a: int, b: int) -> int do
    return a + b
end

# Single-expression shorthand
fn square(n: int) -> int = n * n
```

### Control Flow
```h-sharp
# if / elsif / else
if score > 90 then do
    println("A")
elsif score > 70 then do
    println("B")
else do
    println("C")
end

# while
let mut i: int = 0
while i < 10 do
    i += 1
end

# for-in with range
for i in 0..10 do
    println(to_string(i))
end

# for-in inclusive range
for i in 1..=5 do
    println(to_string(i))
end

# match (pattern matching)
match status_code do
    200 => println("OK")
    404 => println("Not Found")
    500 => println("Server Error")
    _   => println("Unknown")
end
```

### Structs
```h-sharp
struct Packet do
    pub src_ip: string
    pub dst_ip: string
    pub port: int
    pub data: bytes
end

impl Packet do
    pub fn new(src: string, dst: string, port: int) -> Packet do
        return Packet { src_ip: src, dst_ip: dst, port: port, data: [] }
    end

    pub fn summary(self) -> string do
        return self.src_ip + " -> " + self.dst_ip
    end
end
```

### Enums
```h-sharp
enum ScanResult do
    Open
    Closed
    Filtered(string)
end
```

### Traits
```h-sharp
trait Scanner do
    fn scan(self, target: string) -> ScanResult
    fn name(self) -> string do
        return "GenericScanner"
    end
end
```

### Generics
```h-sharp
struct Pair<A, B> do
    pub first: A
    pub second: B
end
```

### Unsafe + Arena Allocator
```h-sharp
fn process_buffer(size: int) do
    unsafe arena(1048576) do   # 1MB arena
        # all allocations here come from the arena
        # automatically freed when block exits
        let buf: bytes = alloc(size)
    end
end
```

### Type Casting
```h-sharp
let n: int = 42
let f: f64 = n as f64
let b: u8 = n as u8
```

### Optional Types
```h-sharp
fn find_user(id: int) -> string? do
    return nil
end

let user = find_user(1)?   # propagate nil with ?
```

---

## Import System

```h-sharp
# Standard library
import "std:io::keyboard"
import "std:io::net"
import "std:crypto::hash"
import "std:crypto::hex"
import "std:encoding::base64"

# Bytes package registry
import "bytes:scanner"
import "bytes:scanner/1.2"    # specific version

# Local files
import "file:lib.h#"
import "file:../utils.h#"

# Native libraries
import "lib:static::openssl.a"    # static linking
import "lib:dynamic::libssl.so"   # dynamic linking
```

---

## Compilation Directives

```h-sharp
# Dynamic linking (default is static)
~ "dynamic:openssl"
~ "dynamic"              # all libs dynamic

# Fast compilation (larger binary, no LTO)
~~ "fast:all"
~~ "fast:debug"
```

---

## Available Targets

| Target | Description |
|---|---|
| `linux-x86_64` | Linux x86\_64 musl (fully static) **[default on Linux]** |
| `linux-x86_64-gnu` | Linux x86\_64 glibc |
| `linux-aarch64` | Linux ARM64 |
| `windows-x86_64` | Windows x86\_64 MSVC |
| `windows-aarch64` | Windows ARM64 |
| `macos-x86_64` | macOS Intel |
| `macos-aarch64` | macOS Apple Silicon |

```bash
h# targets          # list all
h# build --target windows-x86_64
```

---

## Standard Library Modules

```
std:io::keyboard       — stdin/stdout/stderr
std:io::net            — TCP/UDP networking
std:io::file           — file I/O
std:crypto::hash       — hashing (SHA-2, MD5, etc.)
std:crypto::hex        — hex encode/decode
std:crypto::bytes      — XOR, ROT13, byte manipulation
std:encoding::base64   — Base64 encode/decode
std:encoding::url      — URL encode/decode
std:regex              — regular expressions
std:time               — timestamps, sleep
std:fs                 — filesystem utilities
std:process            — subprocess execution
std:collections        — HashMap, HashSet, VecDeque
```

---

## bytes — Package Manager

```bash
bytes add scanner           # add latest
bytes add scanner/1.2       # add specific version
bytes remove scanner        # remove
bytes install               # install all from h#.json
bytes update                # update all to latest
bytes list                  # list installed
bytes search <query>        # search registry
bytes info <package>        # package details
```

Package index: `https://github.com/Bytes-Repository/repository/blob/main/index.json`

---

## Project Structure

```
myproject/
├── h#.json           ← project manifest + dependencies
├── bytes.lock        ← dependency lockfile
├── .gitignore
├── src/
│   └── main.h#       ← main source file
└── build/
    ├── myproject     ← compiled binary (also copied to root)
    └── packages/     ← downloaded library sources
```

### h#.json
```json
{
  "name": "myproject",
  "version": "0.1.0",
  "dependencies": {
    "scanner": "1.2",
    "exploit-db": "0.9"
  }
}
```

---

## Build Commands Reference

```bash
h# preview [file]             # interpret & run (dev mode)
h# build                      # compile project
h# build --target <target>    # cross-compile
h# build --debug              # with debug symbols
h# build --no-opt             # disable optimizations
h# check [file]               # syntax + type check only
h# new <name> [--template T]  # create new project
h# targets                    # list cross-compilation targets
```

Templates: `app` (default), `cybersec`, `network`, `lib`

---

## Architecture

```
hsharp/
├── parser/       ← lexer + parser → AST  (lib)
├── compiler/     ← type checker + C backend codegen  (lib)
├── interpreter/  ← tree-walk interpreter for preview mode  (lib)
├── cli/          ← hsharp CLI tool  (binary)
├── bytes/        ← bytes package manager  (binary)
└── std/          ← standard library Rust implementations  (lib)
```

The compiler uses **C as a portable backend** — H# source is compiled to
optimized C, then passed to `gcc`/`clang`/`musl-gcc` for native code
generation. This avoids LLVM installation requirements while still
producing Rust/C-level performance binaries.

---

## Error Messages (Elm-style)

```
-- SYNTAX ERROR (src/main.h#) -------
--> src/main.h#:5:15

   4 | fn add(a: int, b: int) -> int do
   5 |     return a ++ b
                    ^^
   6 | end

Error: unexpected token `+`

  Hint: did you mean `+` (addition)?
```

---

## License

MIT — HackerOS Team
