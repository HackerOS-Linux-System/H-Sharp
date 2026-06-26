# ![H# - Programming Language for HackerOS.](https://github.com/HackerOS-Linux-System/H-Sharp/blob/main/images/logo.png)
# H# Language — v0.8

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
hacker unpack h#-utils    # bytes + h# check/new/targets
```

### Manualna
```bash
tar -xzf h-sharp-0.6.0.tar.gz && cd h-sharp-0.6
sudo ./install.sh
# Std library
sudo cp std/*.h# /usr/lib/HackerOS/H#/std/
```

### Z kodu źródłowego (wymaga LLVM 21 + Rust 1.85+)
```bash
LLVM_SYS_210_PREFIX=/usr/lib/llvm-21 cargo build --release
```

---

## Narzędzia

| Narzędzie | Opis | Backend |
|-----------|------|---------|
| `h#` | Kompilator + interpreter CLI | LLVM 21 (release) / interpreter (preview) |
| `bytes` | JIT package manager | RAM-based JIT (Cranelift) |

### Komendy

```bash
# Interpreter — natychmiastowe uruchomienie
h# preview src/main.h#

# Kompilacja LLVM — produkcyjna binarka
h# compile src/main.h#
h# compile src/main.h# --release -o myapp
h# compile src/main.h# --target linux-aarch64

# Sprawdź składnię i typy
h# check src/main.h#
h# check a.h# b.h# c.h#

# Nowy projekt
h# new myapp
h# new myapp --template cybersec
h# new myapp --template web
h# new myapp --template tui
h# new myapp --template lib

# Dostępne targety
h# targets

# JIT (bytes)
bytes new myapp && cd myapp
bytes run
bytes run --tier interpreter   # czysty interpreter
bytes run --tier jit           # Cranelift JIT (domyślny)
bytes add scanner              # dodaj pakiet H#
bytes python numpy             # dodaj bibliotekę Python
bytes test                     # uruchom testy
bytes fmt                      # formatuj kod
bytes doc                      # generuj dokumentację HTML
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
use "std -> json"         from "json"
use "python -> numpy"     from "np"
use "github.com/u/repo"   from "repo"

;; Typy: int uint f64 f32 bool string bytes i8 i16 i32 i64 u8 u16 u32 u64

;; Zmienne
let x: int = 42
let mut counter: int = 0
let name: string = "HackerOS"

;; String interpolation (v0.8 — now with working {expr} markers)
let msg: string = "Hello, {name}! x = {x}"
write(msg)

;; Funkcja
fn add(a: int, b: int) -> int is
    return a + b
end

;; Skrócona forma
fn double(x: int) -> int = x * 2

;; Publiczna funkcja
pub fn greet(name: string) -> string is
    return "Hello, " + name + "!"
end

;; Async
async fn fetch(url: string) -> string is
    let resp = http::get(url)?
    return resp.body
end

;; Struct
struct Point is
    pub x: f64
    pub y: f64
end

impl Point is
    fn distance(self, other: Point) -> f64 is
        let dx = self.x - other.x
        let dy = self.y - other.y
        return math::sqrt(dx * dx + dy * dy)
    end
end

;; Enum
enum Status is
    Ok
    Error(string)
    Pending
end

;; Generics
fn first<T>(arr: [T]) -> T? is
    if arr.len() == 0 is
        return nil
    end
    return arr[0]
end

;; Traits
trait Printable is
    fn print(self)
end

impl Point : Printable is
    fn print(self) is
        write("(" + to_string(self.x) + ", " + to_string(self.y) + ")")
    end
end

;; Closures (read-only capture; see Known Limitations for mutable capture)
let double = |x: int| -> int is x * 2 end
let sum = arr.iter().map(|x| x * 2).filter(|x| x > 4).collect()

;; Kontrola przepływu
if x > 10 is
    write("big")
elsif x > 5 is
    write("medium")
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

;; Operator ?
fn read_config(path: string) -> string? is
    let content = fs::read(path)?
    return content
end

;; FFI
extern static [c] is
    fn malloc(size: int) -> int
    fn free(ptr: int)
end

extern dynamic [c, "libssl"] is
    fn SSL_connect(fd: int) -> int
end

extern static [python, "numpy"] is
    fn array(data: string) -> any
    fn mean(arr: any) -> f64
end

;; Unsafe
unsafe arena(65536) is
    let raw: string = "raw data"
end

;; Moduły
mod utils is
    pub fn hex_encode(data: string) -> string is
        return conv::to_hex(data)
    end
end

;; Testy
#[test]
fn test_add() is
    assert_eq(add(2, 3), 5)
    assert_eq(add(-1, 1), 0)
end

#[test]
fn test_string_ops() is
    let s = "hello"
    assert_eq(s.len(), 5)
    assert_true(s.starts_with("hel"))
end
```

---

## Standard Library (84 modułów)

```hsharp
use "std -> io"             from "io"      ;; read_line, write
use "std -> sec"            from "sec"     ;; xor, scan_port, rot13
use "std -> crypto"         from "crypto"  ;; sha256, aes, random_bytes
use "std -> crypto_aes"     from "aes"     ;; encrypt, decrypt, GCM
use "std -> crypto_rsa"     from "rsa"     ;; generate, encrypt, sign
use "std -> json"           from "json"    ;; parse, stringify, get, set
use "std -> math"           from "math"    ;; sin, cos, sqrt, PI
use "std -> math_ext"       from "mx"      ;; mean, median, std_dev
use "std -> strings"        from "str"     ;; trim, split, join, replace
use "std -> fs"             from "fs"      ;; read, write, mkdir, exists
use "std -> path"           from "path"    ;; join, parent, stem, ext
use "std -> net_tcp"        from "tcp"     ;; connect, listen, recv, send
use "std -> net_udp"        from "udp"     ;; bind, send_to, recv_from
use "std -> net_http"       from "http"    ;; get, post, put, delete, listen
use "std -> net_dns"        from "dns"     ;; resolve, lookup_mx, lookup_ptr
use "std -> net_ssh"        from "ssh"     ;; connect, exec_ssh, sftp
use "std -> net_ip"         from "ip"      ;; parse_ip, is_private, cidr_match
use "std -> os"             from "os"      ;; platform, hostname, username
use "std -> env"            from "env"     ;; get, set, args, home
use "std -> sys"            from "sys"     ;; cpu_count, memory_total, uptime
use "std -> time"           from "t"       ;; now_unix, sleep_ms, format_time
use "std -> process"        from "proc"    ;; run, shell, spawn, kill
use "std -> signal"         from "sig"     ;; on_sigint, on_sigterm, raise
use "std -> log"            from "log"     ;; debug, info, warn, error
use "std -> fmt"            from "fmt"     ;; format, red, bold, green, table
use "std -> conv"           from "conv"    ;; str_to_int, int_to_hex, to_bytes
use "std -> buf"            from "buf"     ;; Buffer, write_buf, flush
use "std -> regex"          from "re"      ;; is_match, find, replace, split
use "std -> collections"    from "col"     ;; HashMap, HashSet, Queue, Stack
use "std -> sort"           from "sort"    ;; sort_ints, sort_by, binary_search
use "std -> iter"           from "iter"    ;; map, filter, reduce, zip, chain
use "std -> hash"           from "hash"    ;; fnv1a, murmur3, crc32, blake3
use "std -> mem"            from "mem"     ;; alloc, free_ptr, copy_mem
use "std -> sync"           from "sync"    ;; Mutex, RwLock, Channel, atomic
use "std -> async_"         from "async"   ;; spawn, await, select, timeout
use "std -> channel"        from "chan"    ;; unbounded, bounded, select
use "std -> io_file"        from "iof"     ;; open_read, write_fd, seek
use "std -> encoding_base64" from "b64"   ;; encode, decode
use "std -> encoding_url"   from "url"     ;; encode, decode, parse_query
use "std -> csv"            from "csv"     ;; parse, stringify, get_row
use "std -> yaml"           from "yaml"    ;; parse, stringify, get
use "std -> toml"           from "toml"    ;; parse, get, get_int, get_bool
use "std -> xml"            from "xml"     ;; parse, get_attr, get_text
use "std -> json"           from "json"    ;; parse, stringify, get, query
use "std -> db"             from "db"      ;; sqlite_open, pg_connect, query
use "std -> sqlite"         from "sqlite"  ;; open, exec, query, close
use "std -> postgres"       from "pg"      ;; connect, query, transaction
use "std -> redis"          from "redis"   ;; connect, get, set, expire
use "std -> uuid"           from "uuid"    ;; v4, v5, is_valid, parse
use "std -> config"         from "cfg"     ;; load, get, get_int, get_bool
use "std -> cli"            from "cli"     ;; ArgParser, Flag, prompt
use "std -> term"           from "term"    ;; width, height, read_key, clear
use "std -> test"           from "test"    ;; assert_eq, assert_true, assert_err
use "std -> archive"        from "arc"     ;; tar_create, zip_extract, gz
use "std -> container"      from "ctr"     ;; pull, run, exec_container, stop
use "std -> cron"           from "cron"    ;; new_job, run_job, parse_expr
use "std -> gtk"            from "gtk"     ;; GTK4 GUI (HackerOS)
use "std -> http"           from "http"    ;; HTTP/1.1 client
use "std -> websocket"      from "ws"      ;; connect, send, on_message
use "std -> grpc"           from "grpc"    ;; channel, call, stream
use "std -> graphql"        from "gql"     ;; query, mutation, subscribe
use "std -> jwt"            from "jwt"     ;; sign, verify, decode
use "std -> smtp"           from "smtp"    ;; connect, send_mail, auth
use "std -> pubsub"         from "pubsub"  ;; publish, subscribe, channel
use "std -> rate_limit"     from "rl"      ;; new, check, reset
use "std -> cache"          from "cache"   ;; get, set, ttl, invalidate
use "std -> image"          from "img"     ;; load, resize, save, convert
use "std -> audio"          from "audio"   ;; load, play, record, convert
use "std -> pdf_gen"        from "pdf"     ;; create, add_page, add_text
use "std -> template"       from "tpl"     ;; render, compile, from_file
use "std -> diff"           from "diff"    ;; unified, patch, apply
use "std -> money"          from "money"   ;; parse, add, format, convert
use "std -> msgpack"        from "mp"      ;; encode, decode
use "std -> protobuf"       from "proto"   ;; encode, decode, from_schema
use "std -> tls"            from "tls"     ;; wrap, handshake, load_cert
use "std -> mime"           from "mime"    ;; from_ext, from_bytes, is_text
use "std -> hk"             from "hk"      ;; HackerOS kernel interface
use "std -> sec"            from "sec"     ;; xor, rot13, scan_port, shellcode
use "std -> color"          from "color"   ;; rgb, hex, ansi, gradient
use "std -> date"           from "date"    ;; parse, format, diff, add_days
use "std -> hex"            from "hex"     ;; encode, decode, dump
use "std -> base64"         from "b64"     ;; encode, decode, url_safe
use "std -> tar_gen"        from "tar"     ;; create, add_file, extract
use "std -> zip_gen"        from "zip"     ;; create, add_file, extract
use "std -> net_ip"         from "ip"      ;; parse, is_private, subnet_of
use "std -> sort"           from "sort"    ;; quicksort, mergesort, search
use "std -> iter"           from "iter"    ;; map, filter, zip, fold, take
use "std -> hk"             from "hk"      ;; HackerOS — syscalls, HAL
```

---

## Przykłady

```
examples/
  hello-world.h#    Hello World
  showcase.h#       Prezentacja języka
  more/
    cli_tool.h#     CLI narzędzie
    port_scanner.h# Port scanner (cybersec)
    scanner.h#      Network scanner
    xor_cipher.h#   XOR encrypt/decrypt
    json_example.h# JSON parsing
    http_server.h#  HTTP server
    gui_hello.h#    GTK4 Hello (HackerOS)
    python_interop.h# Python libs bridge
```

---

## Testy

H# wspiera wbudowany system testów. Uruchamianie testów:

```bash
h# check tests/            # weryfikacja składni i typów
bytes test                 # uruchomienie wszystkich testów
bytes test tests/core/     # testy wybranego katalogu
```

Pisanie testów:

```hsharp
use "std -> test" from "test"

#[test]
fn test_arithmetic() is
    assert_eq(2 + 2, 4)
    assert_eq(10 / 2, 5)
    assert_true(3 > 2)
end

#[test]
fn test_strings() is
    let s = "hello"
    assert_eq(s.len(), 5)
    assert_true(s.contains("ell"))
end

#[test]
fn test_error_handling() is
    let result = fs::read("/nonexistent")?
    assert_err(result)
end
```

---

## Znane ograniczenia (v0.7)

Poniższe ograniczenia zostały zidentyfikowane podczas audytu i **większość naprawiona** w tej wersji. Poniżej lista tego, co **nadal** pozostaje otwarte:

- **Mutowalne przechwytywanie w closures** — closure może *odczytać* zmienną z otaczającego scope (`let f = |x| x * outer_var`), ale mutacja przechwyconej zmiennej wewnątrz closure (`let f = || counter += 1`) nie jest widoczna po powrocie z `f()`. Naprawienie wymaga zmiany `Env` na `Rc<RefCell<...>>` per-zmienna — architektoniczna zmiana zaplanowana na v0.8.
- **LLVM codegen — pełna weryfikacja** — backen LLVM obsługuje Path calls (`module::function()`) na poziomie kodu, ale nie był uruchamiany z pełnym zestawem stdlib bindings (LLVM kompiluje do maszynowego kodu, interpreter jest do preview/test). To normalne: LLVM target to produkcja, interpreter to dev.

### Co zostało naprawione w v0.7

Poniższe punkty były w poprzedniej liście "znanych ograniczeń" i zostały **całkowicie wdrożone**:

- ✅ **`crypto::hmac_sha256`** — prawdziwy HMAC-SHA256 przez `sha2`/`hmac` crates (native Rust, zero zależności od shella)
- ✅ **`crypto::sha256`/`sha512`/`md5`/`sha1`** — wszystkie przepisane z shella (`sha256sum`) na native Rust  
- ✅ **`sec::rot13`** — native Rust implementation
- ✅ **`fs::is_file`** — prawdziwe `Path::is_file()` odróżniające plik od katalogu (wcześniej błędny alias do `fs_exists`)
- ✅ **Literalne `{{`/`}}`** w stringach — poprawnie redukują się do `{`/`}`, w tym stringi zawierające **wyłącznie** escaped klamry bez żadnej prawdziwej interpolacji (np. literały JSON)
- ✅ **`module::function()` parsing** — `col::HashMap::new()`, `async::spawn()`, `fs::write()` i każda inna `keyword::fn()` ścieżka parsuje się poprawnie
- ✅ **`fn(int) -> int` jako typ parametru** — powodowało hang; teraz parsuje się do `TypeExpr::Fn` i jest obsługiwane przez typechecker i interpreter
- ✅ **Pełne pattern matching** — `match c is Color::Red =>`, `Color::Custom(_, _, _) =>`, struct patterns, range patterns — wszystkie działają
- ✅ **Enum wartości** — `Color::Red`, `Color::Custom(255, 0, 0)` jako wyrażenia tworzą runtime `Value::Struct`
- ✅ **`impl` method dispatch** — `p.distance_to(other)`, `Type::new(x, y)` i wszystkie user-defined metody na struct działają przez interpreter
- ✅ **`arr.push(x)`/`map.insert(k,v)` mutacja** — mutujące metody faktycznie modyfikują zmienną w scope (write-back do env)
- ✅ **`let (a, b) = swap(1, 2)`** — tuple destructuring w `let` przez desugar do tymczasowej zmiennej
- ✅ **`|| -> T is ... end`** (zero-param closures) — parser poprawnie rozróżnia `||` (Or token) jako pustą listę parametrów
- ✅ **`!expr.method()` precedencja** — krytyczny bug: `!map.contains_key("k")` parsowało się jako `(!map).contains_key("k")` zamiast `!(map.contains_key("k"))` — naprawiony przez `parse_expr(29)` zamiast `parse_prefix()`
- ✅ **`match arm => assignment`** — `match x is 1 => handled = true end` nie wykonywało przypisania (omijało `exec_stmt`); naprawione przez zawsze przechodzenie przez `exec_block`
- ✅ **Operator `?` short-circuit** — `let r = fn()?` nie przerywał funkcji przy `nil`, bo `Stmt::Let` nie sprawdzał `Value::Return` sygnału; naprawione
- ✅ **`assert_eq`/`assert_true`/etc.** — wszystkie wcześniej **cicho ignorowane** (catch-all `Ok(Nil)`); teraz prawdziwe buildiny z `RuntimeError::Panic`
- ✅ **`json::parse`/`json::get_str`/etc.** — brakowało aliasów `json::X → json_X`; wszystkie 19 funkcji json:: teraz poprawnie zmapowane

---

## Licencja

Apache 2.0 — HackerOS Team
