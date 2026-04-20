use cranelift_codegen::ir::{types, AbiParam, Signature};
use cranelift_codegen::isa::CallConv;
use cranelift_module::{Linkage, Module};

/// All builtin function signatures for import into Cranelift module
pub struct Builtins {
    pub println: cranelift_module::FuncId,
    pub print:   cranelift_module::FuncId,
    pub panic_fn: cranelift_module::FuncId,
    pub exit_fn:  cranelift_module::FuncId,
    pub hsh_int_to_string: cranelift_module::FuncId,
    pub hsh_strlen: cranelift_module::FuncId,
    pub hsh_strcat: cranelift_module::FuncId,
    pub hsh_assert: cranelift_module::FuncId,
    pub malloc: cranelift_module::FuncId,
    pub free:   cranelift_module::FuncId,
    // v0.3 stdlib builtins
    pub hsh_trim:       cranelift_module::FuncId,
    pub hsh_to_upper:   cranelift_module::FuncId,
    pub hsh_to_lower:   cranelift_module::FuncId,
    pub hsh_contains:   cranelift_module::FuncId,
    pub hsh_str_replace:cranelift_module::FuncId,
    pub hsh_now_unix:   cranelift_module::FuncId,
    pub hsh_now_ms:     cranelift_module::FuncId,
    pub hsh_sleep_ms:   cranelift_module::FuncId,
    pub hsh_shell:      cranelift_module::FuncId,
    pub hsh_getpid:     cranelift_module::FuncId,
    pub hsh_random_hex: cranelift_module::FuncId,
    pub hsh_random_int: cranelift_module::FuncId,
    pub hsh_sin:        cranelift_module::FuncId,
    pub hsh_cos:        cranelift_module::FuncId,
    pub hsh_sqrt:       cranelift_module::FuncId,
    pub hsh_hostname:   cranelift_module::FuncId,
    // fs + strings
    pub hsh_file_exists:  cranelift_module::FuncId,
    pub hsh_read_file:    cranelift_module::FuncId,
    pub hsh_write_file:   cranelift_module::FuncId,
    pub hsh_mkdir_all:    cranelift_module::FuncId,
    pub hsh_file_size:    cranelift_module::FuncId,
    pub hsh_is_dir:       cranelift_module::FuncId,
    pub hsh_starts_with:  cranelift_module::FuncId,
    pub hsh_ends_with:    cranelift_module::FuncId,
    pub hsh_uuid_v4:      cranelift_module::FuncId,
    pub hsh_random_string:cranelift_module::FuncId,
}

impl Builtins {
    pub fn declare<M: Module>(module: &mut M, call_conv: CallConv) -> Self {
        // println(ptr) -> void
        let println = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            module.declare_function("hsh_println", Linkage::Import, &sig).unwrap()
        };

        // print(ptr) -> void
        let print = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            module.declare_function("hsh_print", Linkage::Import, &sig).unwrap()
        };

        // panic(ptr) -> void  [noreturn, but we don't mark it]
        let panic_fn = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            module.declare_function("hsh_panic", Linkage::Import, &sig).unwrap()
        };

        // exit(i32) -> void
        let exit_fn = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I32));
            module.declare_function("exit", Linkage::Import, &sig).unwrap()
        };

        // hsh_int_to_string(i64) -> ptr
        let hsh_int_to_string = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_int_to_string", Linkage::Import, &sig).unwrap()
        };

        // hsh_strlen(ptr) -> i64
        let hsh_strlen = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_strlen", Linkage::Import, &sig).unwrap()
        };

        // hsh_strcat(ptr, ptr) -> ptr
        let hsh_strcat = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_strcat", Linkage::Import, &sig).unwrap()
        };

        // hsh_assert(i8 cond, ptr msg) -> void
        let hsh_assert = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I8));
            sig.params.push(AbiParam::new(types::I64));
            module.declare_function("hsh_assert", Linkage::Import, &sig).unwrap()
        };

        // malloc(i64 size) -> ptr
        let malloc = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("malloc", Linkage::Import, &sig).unwrap()
        };

        // free(ptr) -> void
        let free = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            module.declare_function("free", Linkage::Import, &sig).unwrap()
        };


        macro_rules! decl_ptr_to_ptr {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }
        macro_rules! decl_ptr_ptr_to_i64 {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.params.push(AbiParam::new(types::I64));
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }
        macro_rules! decl_i64_to_void {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.params.push(AbiParam::new(types::I64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }
        macro_rules! decl_no_args_i64 {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.returns.push(AbiParam::new(types::I64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }
        macro_rules! decl_no_args_ptr {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.returns.push(AbiParam::new(types::I64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }
        macro_rules! decl_f64_to_f64 {
            ($name:expr, $id:ident) => {
                let $id = { let mut sig = Signature::new(call_conv);
                    sig.params.push(AbiParam::new(types::F64));
                    sig.returns.push(AbiParam::new(types::F64));
                    module.declare_function($name, Linkage::Import, &sig).unwrap() };
            };
        }

        decl_ptr_to_ptr!("hsh_trim",        hsh_trim);
        decl_ptr_to_ptr!("hsh_to_upper",     hsh_to_upper);
        decl_ptr_to_ptr!("hsh_to_lower",     hsh_to_lower);
        decl_ptr_ptr_to_i64!("hsh_str_contains",  hsh_contains);
        let hsh_str_replace = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_str_replace", Linkage::Import, &sig).unwrap()
        };
        decl_no_args_i64!("hsh_now_unix",   hsh_now_unix);
        decl_no_args_i64!("hsh_now_ms",     hsh_now_ms);
        decl_i64_to_void!("hsh_sleep_ms",   hsh_sleep_ms);
        decl_ptr_to_ptr!("hsh_shell",        hsh_shell);
        decl_no_args_i64!("hsh_getpid",     hsh_getpid);
        let hsh_random_hex = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_random_hex", Linkage::Import, &sig).unwrap()
        };
        let hsh_random_int = {
            let mut sig = Signature::new(call_conv);
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            module.declare_function("hsh_random_int", Linkage::Import, &sig).unwrap()
        };
        decl_f64_to_f64!("hsh_sin",  hsh_sin);
        decl_f64_to_f64!("hsh_cos",  hsh_cos);
        decl_f64_to_f64!("hsh_sqrt", hsh_sqrt);
        decl_no_args_ptr!("hsh_hostname", hsh_hostname);

        let hsh_file_exists   = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_file_exists",   Linkage::Import, &s).unwrap() };
        let hsh_read_file     = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_read_file",     Linkage::Import, &s).unwrap() };
        let hsh_write_file    = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_write_file",    Linkage::Import, &s).unwrap() };
        let hsh_mkdir_all     = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_mkdir_all",     Linkage::Import, &s).unwrap() };
        let hsh_file_size     = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_file_size",     Linkage::Import, &s).unwrap() };
        let hsh_is_dir        = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_is_dir",        Linkage::Import, &s).unwrap() };
        let hsh_starts_with   = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_starts_with",   Linkage::Import, &s).unwrap() };
        let hsh_ends_with     = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_ends_with",     Linkage::Import, &s).unwrap() };
        let hsh_uuid_v4       = { let mut s = Signature::new(call_conv); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_uuid_v4",       Linkage::Import, &s).unwrap() };
        let hsh_random_string = { let mut s = Signature::new(call_conv); s.params.push(AbiParam::new(types::I64)); s.returns.push(AbiParam::new(types::I64)); module.declare_function("hsh_random_string", Linkage::Import, &s).unwrap() };

        Self {
            println, print, panic_fn, exit_fn,
            hsh_int_to_string, hsh_strlen, hsh_strcat,
            hsh_assert, malloc, free,
            hsh_trim, hsh_to_upper, hsh_to_lower, hsh_contains, hsh_str_replace,
            hsh_now_unix, hsh_now_ms, hsh_sleep_ms, hsh_shell, hsh_getpid,
            hsh_random_hex, hsh_random_int, hsh_sin, hsh_cos, hsh_sqrt, hsh_hostname,
            hsh_file_exists, hsh_read_file, hsh_write_file, hsh_mkdir_all, hsh_file_size,
            hsh_is_dir, hsh_starts_with, hsh_ends_with, hsh_uuid_v4, hsh_random_string,
        }
    }
}

/// Generate the H# runtime C source (linked alongside compiled output)
pub fn runtime_c_source() -> &'static str {
    r#"/* H# Runtime — linked with compiled output */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* H# core types */
typedef const char* hsh_string;
typedef struct { uint8_t* ptr; size_t len; size_t cap; } hsh_bytes;
typedef int64_t   hsh_int;
typedef double    hsh_float;
typedef int       hsh_bool;

// ── RAII Drop functions ────────────────────────────────────────────────────────

void hsh_string_free(hsh_string s) {
    // H# strings are interned — runtime decides when to actually free
    // For now: no-op (future: ref-counted strings)
    (void)s;
}

void hsh_bytes_free(uint8_t* b) {
    if (b) free(b);
}

void hsh_array_free(void* arr) {
    if (arr) free(arr);
}

void hsh_struct_free(void* ptr) {
    if (ptr) free(ptr);
}


/* ── String builtins ─────────────────────────────────────────────────── */
void hsh_print(const char* s)   { if (s) printf("%s", s); }
void hsh_println(const char* s) { if (s) printf("%s\n", s); else printf("\n"); }

char* hsh_int_to_string(int64_t n) {
    char* buf = (char*)malloc(32);
    snprintf(buf, 32, "%ld", (long)n);
    return buf;
}

char* hsh_float_to_string(double f) {
    char* buf = (char*)malloc(64);
    snprintf(buf, 64, "%g", f);
    return buf;
}

char* hsh_bool_to_string(int8_t b) {
    return b ? "true" : "false";
}

int64_t hsh_strlen(const char* s) {
    return s ? (int64_t)strlen(s) : 0;
}

char* hsh_strcat(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    size_t la = strlen(a), lb = strlen(b);
    char* out = (char*)malloc(la + lb + 1);
    memcpy(out, a, la);
    memcpy(out + la, b, lb);
    out[la + lb] = '\0';
    return out;
}

/* ── Assertion / panic ───────────────────────────────────────────────── */
void hsh_assert(int8_t cond, const char* msg) {
    if (!cond) {
        fprintf(stderr, "assertion failed: %s\n", msg ? msg : "(no message)");
        exit(1);
    }
}

void hsh_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg ? msg : "(no message)");
    exit(1);
}

/* ── Arena allocator ─────────────────────────────────────────────────── */
typedef struct {
    uint8_t* base;
    uint64_t cap;
    uint64_t used;
} HshArena;

HshArena* hsh_arena_new(uint64_t cap) {
    HshArena* a = (HshArena*)malloc(sizeof(HshArena));
    a->base = (uint8_t*)malloc(cap);
    a->cap  = cap;
    a->used = 0;
    return a;
}

void* hsh_arena_alloc(HshArena* a, uint64_t n) {
    /* align to 8 bytes */
    uint64_t aligned = (n + 7) & ~7ULL;
    if (a->used + aligned > a->cap) {
        fprintf(stderr, "H# arena OOM: requested %lu, have %lu\n",
                (unsigned long)aligned, (unsigned long)(a->cap - a->used));
        exit(1);
    }
    void* p = a->base + a->used;
    a->used += aligned;
    return p;
}

void hsh_arena_free(HshArena* a) {
    if (!a) return;
    free(a->base);
    free(a);
}

/* ── Bytes type (fat pointer: data ptr + len + cap) ─────────────────── */
typedef struct {
    uint8_t* data;
    uint64_t len;
    uint64_t cap;
} HshBytes;

HshBytes* hsh_bytes_new(void) {
    HshBytes* b = (HshBytes*)malloc(sizeof(HshBytes));
    b->data = NULL; b->len = 0; b->cap = 0;
    return b;
}

HshBytes* hsh_bytes_from(const uint8_t* data, uint64_t len) {
    HshBytes* b = hsh_bytes_new();
    b->data = (uint8_t*)malloc(len);
    memcpy(b->data, data, len);
    b->len = len; b->cap = len;
    return b;
}

char* hsh_bytes_to_hex(const HshBytes* b) {
    if (!b || !b->data) return (char*)strdup("");
    char* out = (char*)malloc(b->len * 2 + 1);
    for (uint64_t i = 0; i < b->len; i++)
        sprintf(out + i*2, "%02x", b->data[i]);
    out[b->len * 2] = '\0';
    return out;
}

/* ── Optional (nil = 0 / NULL pointer) ──────────────────────────────── */
/* H# optionals are represented as NULL pointers for pointer types,
   or as tagged i64 (0x8000000000000000 = nil tag) for value types */
#define HSH_NIL_TAG ((int64_t)0x8000000000000000LL)

int8_t hsh_is_nil(int64_t v) {
    return v == 0 || v == HSH_NIL_TAG;
}

/* ── Parse builtins ──────────────────────────────────────────────────── */
/* Returns HSH_NIL_TAG on failure, parsed value on success */
int64_t hsh_parse_int(const char* s) {
    if (!s || !*s) return HSH_NIL_TAG;
    char* end;
    long long v = strtoll(s, &end, 10);
    if (*end != '\0') return HSH_NIL_TAG;
    return (int64_t)v;
}

/* ── Comparison helpers ──────────────────────────────────────────────── */
int8_t hsh_str_eq(const char* a, const char* b) {
    if (!a && !b) return 1;
    if (!a || !b) return 0;
    return strcmp(a, b) == 0;
}

int8_t hsh_str_neq(const char* a, const char* b) {
    return !hsh_str_eq(a, b);
}
/* ── Strings ─────────────────────────────────────────────────────────────── */

hsh_string hsh_trim(hsh_string s) {
    if (!s) return "";
    while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') s++;
    const char *end = s + strlen(s) - 1;
    while (end > s && (*end == ' ' || *end == '\t' || *end == '\n' || *end == '\r')) end--;
    size_t len = end - s + 1;
    char *out = (char*)malloc(len + 1);
    memcpy(out, s, len);
    out[len] = '\0';
    return out;
}

int64_t hsh_str_contains(hsh_string haystack, hsh_string needle) {
    return strstr(haystack, needle) != NULL ? 1 : 0;
}

static int64_t hsh_str_starts_with(hsh_string s, hsh_string prefix) {
    return strncmp(s, prefix, strlen(prefix)) == 0 ? 1 : 0;
}

static int64_t hsh_str_ends_with(hsh_string s, hsh_string suffix) {
    size_t sl = strlen(s), xl = strlen(suffix);
    if (xl > sl) return 0;
    return strcmp(s + sl - xl, suffix) == 0 ? 1 : 0;
}

hsh_string hsh_to_upper(hsh_string s) {
    size_t n = strlen(s);
    char *out = (char*)malloc(n + 1);
    for (size_t i = 0; i <= n; i++) out[i] = toupper((unsigned char)s[i]);
    return out;
}

hsh_string hsh_to_lower(hsh_string s) {
    size_t n = strlen(s);
    char *out = (char*)malloc(n + 1);
    for (size_t i = 0; i <= n; i++) out[i] = tolower((unsigned char)s[i]);
    return out;
}

hsh_string hsh_str_replace(hsh_string s, hsh_string from, hsh_string to) {
    if (!s || !from || !to) return s;
    size_t flen = strlen(from), tlen = strlen(to), slen = strlen(s);
    // Count occurrences
    int count = 0;
    const char *p = s;
    while ((p = strstr(p, from))) { count++; p += flen; }
    if (!count) return s;
    char *out = (char*)malloc(slen + count * (tlen - flen + 1) + 1);
    char *w = out;
    p = s;
    const char *q;
    while ((q = strstr(p, from))) {
        size_t pre = q - p;
        memcpy(w, p, pre); w += pre;
        memcpy(w, to, tlen); w += tlen;
        p = q + flen;
    }
    strcpy(w, p);
    return out;
}

/* ── OS / Env ─────────────────────────────────────────────────────────────── */

static int64_t hsh_env_get(hsh_string key, hsh_string *out) {
    const char *v = getenv(key);
    *out = v ? v : "";
    return v ? 1 : 0;
}

#include <unistd.h>
hsh_string hsh_hostname(void) {
    static char buf[256];
    gethostname(buf, sizeof(buf));
    return buf;
}

/* ── Time ─────────────────────────────────────────────────────────────────── */
#include <time.h>

int64_t hsh_now_unix(void) {
    return (int64_t)time(NULL);
}

int64_t hsh_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

void hsh_sleep_ms(int64_t ms) {
    struct timespec ts = { ms / 1000, (ms % 1000) * 1000000 };
    nanosleep(&ts, NULL);
}

/* ── Math ─────────────────────────────────────────────────────────────────── */
#include <math.h>

double hsh_sin(double x)  { return sin(x);  }
double hsh_cos(double x)  { return cos(x);  }
double hsh_sqrt(double x) { return sqrt(x); }
static double hsh_pow(double b, double e) { return pow(b, e); }
double hsh_floor(double x) { return floor(x); }
double hsh_ceil(double x)  { return ceil(x);  }
double hsh_abs(double x)   { return fabs(x);  }
double hsh_log(double x)   { return log(x);   }
double hsh_log2(double x)  { return log2(x);  }

/* ── Process ─────────────────────────────────────────────────────────────── */

hsh_string hsh_shell(hsh_string cmd) {
    FILE *fp = popen(cmd, "r");
    if (!fp) return "";
    char *buf = NULL;
    size_t total = 0, cap = 0;
    char chunk[4096];
    while (fgets(chunk, sizeof(chunk), fp)) {
        size_t n = strlen(chunk);
        if (total + n + 1 > cap) {
            cap = (cap + n + 1) * 2;
            buf = (char*)realloc(buf, cap);
        }
        memcpy(buf + total, chunk, n);
        total += n;
    }
    pclose(fp);
    if (!buf) return "";
    buf[total] = '\0';
    return buf;
}

int64_t hsh_getpid(void) { return (int64_t)getpid(); }

/* ── Crypto helpers ──────────────────────────────────────────────────────── */

hsh_string hsh_random_hex(int64_t n) {
    char *buf = (char*)malloc(n * 2 + 1);
    FILE *fp = fopen("/dev/urandom", "rb");
    if (!fp) { buf[0] = '\0'; return buf; }
    for (int64_t i = 0; i < n; i++) {
        unsigned char b;
        fread(&b, 1, 1, fp);
        snprintf(buf + i * 2, 3, "%02x", b);
    }
    fclose(fp);
    buf[n * 2] = '\0';
    return buf;
}

int64_t hsh_random_int(int64_t min, int64_t max) {
    uint64_t r;
    FILE *fp = fopen("/dev/urandom", "rb");
    if (!fp) return min;
    fread(&r, 8, 1, fp);
    fclose(fp);
    if (max <= min) return min;
    return min + (int64_t)(r % (uint64_t)(max - min));
}


/* ── Filesystem ──────────────────────────────────────────────────────────── */
#include <sys/stat.h>
#include <dirent.h>

int64_t hsh_file_exists(hsh_string path) {
    struct stat st;
    return (stat(path, &st) == 0) ? 1 : 0;
}

hsh_string hsh_read_file(hsh_string path) {
    FILE *f = fopen(path, "rb");
    if (!f) return "";
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    char *buf = (char*)malloc(sz + 1);
    if (!buf) { fclose(f); return ""; }
    fread(buf, 1, sz, f);
    buf[sz] = '\0';
    fclose(f);
    return buf;
}

int64_t hsh_write_file(hsh_string path, hsh_string content) {
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    fputs(content, f);
    fclose(f);
    return 1;
}

int64_t hsh_mkdir_all(hsh_string path) {
    char tmp[4096];
    snprintf(tmp, sizeof(tmp), "%s", path);
    for (char *p = tmp + 1; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            mkdir(tmp, 0755);
            *p = '/';
        }
    }
    mkdir(tmp, 0755);
    return 1;
}

int64_t hsh_file_size(hsh_string path) {
    struct stat st;
    return (stat(path, &st) == 0) ? (int64_t)st.st_size : -1;
}

int64_t hsh_is_dir(hsh_string path) {
    struct stat st;
    return (stat(path, &st) == 0 && S_ISDIR(st.st_mode)) ? 1 : 0;
}

/* ── String helpers ──────────────────────────────────────────────────────── */

int64_t hsh_starts_with(hsh_string s, hsh_string prefix) {
    return strncmp(s, prefix, strlen(prefix)) == 0 ? 1 : 0;
}

int64_t hsh_ends_with(hsh_string s, hsh_string suffix) {
    size_t sl = strlen(s), xl = strlen(suffix);
    if (xl > sl) return 0;
    return strcmp(s + sl - xl, suffix) == 0 ? 1 : 0;
}

hsh_string hsh_uuid_v4(void) {
    uint8_t b[16];
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) {
        return "00000000-0000-4000-0000-000000000000";
    }
    fread(b, 1, 16, f);
    fclose(f);
    b[6] = (b[6] & 0x0f) | 0x40;
    b[8] = (b[8] & 0x3f) | 0x80;
    char *out = (char*)malloc(37);
    snprintf(out, 37,
        "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
        b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],
        b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]);
    return out;
}

hsh_string hsh_random_string(int64_t n) {
    static const char cs[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    if (n <= 0) return "";
    char *out = (char*)malloc(n + 1);
    uint8_t *tmp = (uint8_t*)malloc(n);
    FILE *f = fopen("/dev/urandom", "rb");
    if (f) { fread(tmp, 1, n, f); fclose(f); }
    for (int64_t i = 0; i < n; i++) out[i] = cs[tmp[i] % 62];
    free(tmp);
    out[n] = '\0';
    return out;
}
"#
}
