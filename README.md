# ![H# - Programing Language for HackerOS.](https://github.com/HackerOS-Linux-System/H-Sharp/blob/main/images/logo.png)
# H# — H-Sharp Language v0.1

**HackerOS-first compiled language** — built for the HackerOS distribution.  
Fast, safe, expressive. Replaces Python for CLI tools, GUI apps, cybersec utilities, and everyday scripts.

## Use Cases in HackerOS

| Use Case | H# Feature |
|----------|-----------|
| CLI tools | Fast native binaries, pattern matching, argument parsing |
| GUI apps | GTK/iced bindings via `std -> gui` |
| Cybersec tools | `std -> sec` (XOR, hex, port scan, hash) |
| Replace Python | Same ergonomics, 10-100x faster, `bytes` PM for Python interop |
| Web/HTTP | `std -> net -> tcp`, `std -> http` |
| System scripting | `std -> os`, `std -> process`, `std -> env` |
| Data processing | `std -> json`, `std -> yaml`, `std -> toml_fmt` |

## Install

```bash
hacker unpack h# # if you wont only h# cli tool

hacker unpack h#-utils # if you wont vira/bytes/bit
```

## Quick Start

```bash
# Interpreter preview (fast iteration)
h# preview hello.h#

# Compile native binary (Cranelift, fast compile)
h# build hello.h# -o hello

# Release binary (LLVM O3+AVX2, fast runtime)
hsharp-compiler-llvm hello.h# --release -o hello

# Vira: project build tool (compilation)
vira new myapp && cd myapp
vira build --release

# bytes: JIT interpreter (RAM cache, no artifacts)
bytes new myapp && cd myapp
bytes run
```

## Syntax

```hsharp
;; Line comment
/// Doc comment
// Block comment \\

use "std -> io" from "io"
use "std -> json" from "json"
use "std -> sec" from "sec"
use "vira -> scanner/1.2" from "scanner"
use "github.com/user/mylib" from "mylib"
use "python -> numpy" from "np"       ;; bytes PM only

fn greet(name: string) -> string is
    return "Hello, " + name + "!"
end

fn factorial(n: int) -> int is
    match n is
        0 | 1 => return 1
        _     => return n * factorial(n - 1)
    end
end

fn main() is
    write(greet("HackerOS"))
    write("10! = " + to_string(factorial(10)))

    let mut total: int = 0
    for i in 1..=100 is
        total += i
    end
    write("Sum 1..100 = " + to_string(total))

    ;; Unsafe modes
    unsafe arena(4096) is
        ;; Arena bump allocator — zero free() overhead
    end
    unsafe manual is
        ;; Raw malloc/free control
    end
end
```

## Three Compilation Modes

```
h# preview file.h#      → Tree-walk interpreter (instant start)
h# build   file.h#      → Cranelift native (fast compile, good speed)
hsharp-compiler-llvm --release → LLVM O3+AVX2 (slow compile, fastest runtime)
```

## vira — Project Build Manager

```bash
vira new myapp --template cybersec
vira build [--release]
vira add scanner/1.2
vira add github.com/user/repo
vira install
vira search crypto
vira settings        # TUI settings (progress bar theme etc.)
vira clean           # remove .cache/
```

### vira.hcl

```hcl
project "myapp" {
  version = "0.1.0"
  h_sharp = "0.1"
  src_dir = "src"
}

output {
  type = "binary"   # binary | so | a | hsl
  # name = "libmyapp"
}

dependencies {
  scanner        = "1.2"
  github.com/user/repo = "latest"
}
```

### Output types

| Type | Extension | Use |
|------|-----------|-----|
| `binary` | — | Executable (default) |
| `so` | `.so` | Shared library |
| `a` | `.a` | Static library |
| `hsl` | `.hsl` | H# native library (like Rust's .rlib) |

## bytes — RAM-JIT Package Manager

```bash
bytes new myapp && cd myapp
bytes run                        # JIT (RAM cache)
bytes run --tier interpreter     # Pure interpreter
bytes run --tier bytecode        # Bytecode VM
bytes add scanner                # H# package
bytes python numpy               # Python package
bytes install                    # Install all from bytes.toml
bytes clean                      # Clear /dev/shm cache
```

### bytes.toml

```toml
[package]
name = "myapp"
version = "0.1.0"
entry = "src/main.h#"

[jit]
tier = "jit"          # interpreter | bytecode | jit
hot_thresh = 100      # JIT after 100 calls

[dependencies]
scanner = "1.2"

[python]
version = "3.13"
packages = ["numpy", "cryptography", "pandas"]
```

### Python Interop

```hsharp
;; bytes.toml: python packages = ["numpy"]
use "python -> numpy" from "np"
use "python -> cryptography" from "crypto"

fn main() is
    let result: string = np_call("mean", "[1,2,3,4,5]")
    write("numpy mean: " + result)
end
```

## Standard Library

```hsharp
use "std -> io"           from "io"       ;; write, writeln, keyboard, file
use "std -> json"         from "json"     ;; parse, stringify
use "std -> yaml"         from "yaml"     ;; parse, stringify
use "std -> toml_fmt"     from "toml"     ;; parse
use "std -> sec"          from "sec"      ;; xor, rot13, scan_port, hex
use "std -> crypto -> hex" from "hex"     ;; encode/decode
use "std -> http"         from "http"     ;; GET, POST
use "std -> net -> tcp"   from "tcp"      ;; TcpStream
use "std -> math"         from "math"     ;; sin, cos, PI, sqrt
use "std -> strings"      from "str"      ;; trim, split, join, pad
use "std -> path"         from "path"     ;; join, filename, exists
use "std -> fs"           from "fs"       ;; read, write, exists
use "std -> os"           from "os"       ;; platform, hostname, username
use "std -> env"          from "env"      ;; get, set, args, cwd
use "std -> time"         from "t"        ;; now_unix, sleep_ms
use "std -> collections"  from "col"      ;; HashMap, HashSet
use "std -> encoding -> base64" from "b64" ;; encode, decode
use "std -> process"      from "proc"     ;; run, spawn
use "std -> regex"        from "re"       ;; is_match
```

## Architecture

```
H# Source (.h# / .hsp)
│
├── h# preview   → Interpreter (tree-walk, zero compile)
├── h# build     → Cranelift backend (fast compile, native .o)
├── hsharp-compiler-llvm --release → LLVM O3+AVX2 (production)
│
├── vira build       → invokes hsharp-compiler-llvm for release
│                       invokes hsharp build for debug
│
└── bytes run        → JIT in RAM (/dev/shm/bytes-PID/)
                        Tier 1: interpreter (hsharp preview)
                        Tier 2: bytecode (cached .h#bc in RAM)
                        Tier 3: JIT (cranelift → binary in RAM)

Bootstrap (always Rust):   parser + compiler + cranelift + llvm
Rewritable in H# later:    cli, vira, bytes, interpreter, std
```

## File Extensions

- `.h#` — H# source (main format)
- `.hsp` — H# source (alternate)
- `.hsl` — H# library (vira output type)
- `.h#bc` — H# bytecode (bytes PM cache, in RAM)

## Build from Source

```bash
# Standard build (Cranelift only)
cargo build --release

# With LLVM compiler (requires llvm-17-dev)
LLVM_SYS_170_PREFIX=/usr/lib/llvm-17 cargo build --release

# HackerOS install location
install -m755 target/release/hsharp               ~/.hackeros/H#/bins/
install -m755 target/release/vira                 ~/.hackeros/H#/bins/
install -m755 target/release/bytes                ~/.hackeros/H#/bins/
install -m755 target/release/hsharp-compiler-llvm ~/.hackeros/H#/bins/
```

Requires: Rust ≥ 1.75, gcc/cc, llvm-17-dev (for LLVM backend)
