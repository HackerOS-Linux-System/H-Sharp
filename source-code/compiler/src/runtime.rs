/// H# runtime built-in function declarations for Cranelift
/// These are the C runtime functions that H# builtins map to.

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

        Self {
            println, print, panic_fn, exit_fn,
            hsh_int_to_string, hsh_strlen, hsh_strcat,
            hsh_assert, malloc, free,
        }
    }
}

/// Generate the H# runtime C source (linked alongside compiled output)
pub fn runtime_c_source() -> &'static str {
    r#"/* H# Runtime — linked with cranelift-compiled output */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
"#
}
