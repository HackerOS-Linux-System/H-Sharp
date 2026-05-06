# ![H# - Programing Language for HackerOS.](https://github.com/HackerOS-Linux-System/H-Sharp/blob/main/images/logo.png)
# H# Language — v0.4

**H#** (H-Sharp) to kompilowany język programowania pisany z myślą o HackerOS — bezpieczny, ekstremalnie szybki, z natywnym wsparciem dla cybersecurity, systemów i narzędzi CLI.

```hsharp
fn main() is
    write("Hello from H#!")
    for i in 1..=10 is
        if i % 2 == 0 is
            write(to_string(i) + " is even")
        end
    end
end
```

---

## Instalacja

### HackerOS
```bash
hacker unpack h#          # kompilator + interpreter
hacker unpack h#-utils    # vira + bytes + hhc
```

### Manualna
```bash
tar -xzf h-sharp-0.3.0.tar.gz && cd h-sharp-0.3
sudo ./install.sh
# Std library
sudo cp std-h#/*.h# /usr/lib/HackerOS/H#/std/
```

### Z kodu źródłowego (wymaga LLVM 21 + Rust 1.85+)
```bash
LLVM_SYS_210_PREFIX=/usr/lib/llvm-21 cargo build --release
```

---

## Narzędzia

| Narzędzie | Opis | Backend |
|-----------|------|---------|
| `h#` | Kompilator + interpreter | Cranelift (fast-compile) |
| `hhc` | Produkcyjny kompilator | LLVM 21 O3+AVX2+LTO |
| `vira` | Build manager projektów | `.hcl` config |
| `bytes` | JIT package manager | RAM-based JIT |

### Komendy

```bash
# Interpreter — natychmiastowe uruchomienie
h# preview src/main.h#

# Cranelift — szybka kompilacja (dev)
h# build src/main.h#

# hhc LLVM — produkcyjna binarka (release)
hhc src/main.h# --release -o myapp

# Sprawdź składnię
h# check src/main.h#

# Projekt (vira)
vira new myapp && cd myapp
vira build           # debug (Cranelift)
vira build --release # release (hhc LLVM O3)

# JIT (bytes)
bytes new myapp && cd myapp
bytes run
bytes python numpy   # instaluj Python lib
```

---

## Składnia H#

```hsharp
;; Komentarz liniowy
/// Komentarz dokumentacyjny
// Komentarz blokowy \\

;; Import
use "std -> io"           from "io"
use "std -> crypto"       from "crypto"
use "std -> net_http"     from "http"
use "vira -> scanner/1.2" from "sc"
use "python -> numpy"     from "np"
use "github.com/u/repo"   from "repo"

;; Typy: int uint f64 f32 bool string bytes i8 i16 i32 i64 u8 u16 u32 u64

;; Zmienne
let x: int = 42
let mut counter: int = 0
let name: string = "HackerOS"

;; Funkcja
fn add(a: int, b: int) -> int is
    return a + b
end

;; Publiczna funkcja
pub fn greet(name: string) -> string is
    return "Hello, " + name + "!"
end

;; Struct
struct Point is
    pub x: f64
    pub y: f64
end

;; Enum
enum Status is
    Ok
    Error(string)
    Pending
end

;; Kontrola przepływu
if x > 10 is
    write("big")
else is
    write("small")
end

for i in 0..=9 is
    write(to_string(i))
end

let mut i: int = 0
while i < 10 is
    i += 1
end

match status is
    Status::Ok          => write("ok")
    Status::Error(msg)  => write("error: " + msg)
    Status::Pending     => write("pending")
end

;; FFI
extern static [c] is
    fn malloc(size: int) -> int
    fn free(ptr: int)
end

extern dynamic [c, "libssl"] is
    fn SSL_connect(fd: int) -> int
end

extern static [rust] is
    fn my_rust_fn(x: int) -> int
end

;; Unsafe
unsafe arena(65536) is
    let raw: string = "raw data"
end
```

---

## Standard Library (51 modułów)

```hsharp
use "std -> io"             from "io"      ;; read_line, write
use "std -> sec"            from "sec"     ;; xor, scan_port, rot13
use "std -> crypto"         from "crypto"  ;; sha256, aes, random
use "std -> json"           from "json"    ;; parse, stringify
use "std -> math"           from "math"    ;; sin, cos, sqrt, PI
use "std -> math_ext"       from "mx"      ;; mean, median, std_dev
use "std -> strings"        from "str"     ;; trim, split, join
use "std -> fs"             from "fs"      ;; read, write, mkdir
use "std -> path"           from "path"    ;; join, parent, stem
use "std -> net_tcp"        from "tcp"     ;; connect, recv, scan_port
use "std -> net_udp"        from "udp"     ;; bind, send_to
use "std -> net_http"       from "http"    ;; get, post, listen
use "std -> net_dns"        from "dns"     ;; resolve, lookup_mx
use "std -> net_ssh"        from "ssh"     ;; connect, exec_ssh
use "std -> net_ip"         from "ip"      ;; parse_ip, is_private
use "std -> http"           from "http"    ;; client only
use "std -> os"             from "os"      ;; platform, hostname
use "std -> env"            from "env"     ;; get, set, args
use "std -> sys"            from "sys"     ;; cpu_count, memory_total
use "std -> time"           from "t"       ;; now_unix, sleep_ms
use "std -> process"        from "proc"    ;; run, shell, spawn
use "std -> signal"         from "sig"     ;; on_sigint, SIGTERM
use "std -> log"            from "log"     ;; debug, info, warn, error
use "std -> fmt"            from "fmt"     ;; format, red, bold, green
use "std -> conv"           from "conv"    ;; str_to_int, int_to_hex
use "std -> buf"            from "buf"     ;; Buffer, write_buf
use "std -> regex"          from "re"      ;; is_match, find, replace
use "std -> collections"    from "col"     ;; HashMap, HashSet, Queue
use "std -> sort"           from "sort"    ;; sort_ints, binary_search
use "std -> iter"           from "iter"    ;; map, filter, reduce
use "std -> hash"           from "hash"    ;; fnv1a, murmur3, crc32
use "std -> mem"            from "mem"     ;; alloc, free_ptr
use "std -> sync"           from "sync"    ;; Mutex, Channel, atomic
use "std -> async"          from "async"   ;; spawn, await (v0.3+)
use "std -> io_file"        from "iof"     ;; open_read, write_fd
use "std -> encoding_base64" from "b64"   ;; encode, decode
use "std -> encoding_url"   from "url"     ;; encode, decode
use "std -> csv"            from "csv"     ;; parse, get_row
use "std -> yaml"           from "yaml"    ;; parse, stringify
use "std -> toml"           from "toml"    ;; parse, get
use "std -> xml"            from "xml"     ;; parse, get_attr
use "std -> db"             from "db"      ;; sqlite_open, pg_connect
use "std -> uuid"           from "uuid"    ;; v4, is_valid
use "std -> config"         from "cfg"     ;; load, get, get_int
use "std -> cli"            from "cli"     ;; ArgParser, prompt
use "std -> term"           from "term"    ;; width, read_key, clear
use "std -> test"           from "test"    ;; assert_eq, assert_true
use "std -> archive"        from "arc"     ;; tar_create, zip_extract
use "std -> container"      from "ctr"     ;; pull, run, exec_container
use "std -> cron"           from "cron"    ;; new_job, run_job
use "std -> gtk"            from "gtk"     ;; GTK4 GUI (HackerOS)
```

---

## Przykłady

```
examples/
  hello.h#          Hello World
  cli_tool.h#       CLI narzędzie
  port_scanner.h#   Port scanner
  net_scanner.h#    Network scanner z DNS
  xor_cipher.h#     XOR encrypt/decrypt
  json_example.h#   JSON parsing
  crypto_tool.h#    SHA256, AES, random
  file_manager.h#   Operacje na plikach
  web_scraper.h#    HTTP + regex + JSON
  log_analyzer.h#   Analiza logów
  task_cli.h#       Task manager CLI
  python_interop.h# Python libs bridge
  gui_hello.h#      GTK4 Hello (HackerOS)
  scanner.h#        Ogólny scanner
  http_server.h#    HTTP server stub
```

---

## Roadmap

| Wersja | Plan | Status |
|--------|------|--------|
| v0.2 | Parser, Cranelift, hhc LLVM 21, FFI extern, std 51 lib | ✅ Done |
| v0.3 | `?` operator, closures, stdlib real impl, async/await | 🔨 In Progress |
| v0.4 | Generics runtime, traits dispatch, modules, string interpolation | 📋 Planned |
| v0.5 | Borrow checker / lifetimes (region-based safety) | 📋 Planned |
| v0.6 | Performance, large projects, profiling | 📋 Planned |
| v0.7 | Final testing, pre-release | 📋 Planned |
| v1.0 | Stable + editions (2026, 2027...) | 🎯 Goal |

---

## Licencja

Apache 2.0 — HackerOS Team  
