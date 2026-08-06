#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <math.h>
#include <netdb.h>
#include <sys/socket.h>

/* Global argc/argv storage — written by the H# main() entry point
 * (codegen emits: _hsh_argc = argc; _hsh_argv = argv;)
 * and read by hsh_env_args() so user code can call env::args().     */
int   _hsh_argc = 0;
char **_hsh_argv = NULL;

#include <netinet/in.h>
#include <arpa/inet.h>

typedef const char* hsh_string;
typedef int64_t     hsh_int;

/* Forward decl: arena-aware allocator, defined down in the Arena section,
 * but needed by hsh_strcat which comes first in the file. */
static void* hsh_alloc(uint64_t n);
typedef double      hsh_float;

/* ── Core I/O ────────────────────────────────────────────────────────────── */

void hsh_print(hsh_string s)   { if (s) printf("%s", s); }
void hsh_println(hsh_string s) { if (s) printf("%s\n", s); else printf("\n"); }

int64_t hsh_atoll(hsh_string s) { return s ? atoll(s) : 0; }
double  hsh_atof(hsh_string s)  { return s ? atof(s)  : 0.0; }

char* hsh_int_to_string(int64_t n) {
    char* buf = (char*)malloc(32);
    if (buf) snprintf(buf, 32, "%ld", (long)n);
    return buf ? buf : (char*)"";
}

char* hsh_float_to_string(double n) {
    char* buf = (char*)malloc(64);
    if (buf) snprintf(buf, 64, "%g", n);
    return buf ? buf : (char*)"";
}

int64_t hsh_strlen(hsh_string s) { return s ? (int64_t)strlen(s) : 0; }

char* hsh_strcat(hsh_string a, hsh_string b) {
    if (!a) a = "";
    if (!b) b = "";
    size_t la = strlen(a), lb = strlen(b);
    char* out = (char*)hsh_alloc(la + lb + 1);
    if (!out) return (char*)"";
    memcpy(out, a, la);
    memcpy(out + la, b, lb);
    out[la + lb] = '\0';
    return out;
}

void hsh_assert(int8_t cond, hsh_string msg) {
    if (!cond) {
        fprintf(stderr, "assertion failed: %s\n", msg ? msg : "(no message)");
        exit(1);
    }
}

void hsh_panic(hsh_string msg) {
    fprintf(stderr, "panic: %s\n", msg ? msg : "(no message)");
    exit(1);
}

/* ── RAII drop stubs ─────────────────────────────────────────────────────── */
void hsh_string_free(hsh_string s) { (void)s; }
void hsh_bytes_free(uint8_t* b)    { if (b) free(b); }
void hsh_array_free(void* arr)     { if (arr) free(arr); }
void hsh_struct_free(void* ptr)    { if (ptr) free(ptr); }

/* ── Arena ────────────────────────────────────────────────────────────────── */
/* `kind` mirrors the parser's `ArenaKind` (see ast.rs) as a plain tag so this
 * header doesn't need to depend on Rust enum layout:
 *   0 = General — malloc-fallback on exhaustion, 8-byte alignment (default).
 *   1 = Fixed   — PANICS on exhaustion instead of falling back to malloc;
 *                 for "I know the exact upper bound and never want to
 *                 silently degrade to a regular heap allocation" call sites.
 *   2 = Pool    — allocations are rounded up to HSH_ARENA_POOL_CHUNK-byte
 *                 chunks, so every allocation in the pool is a uniform
 *                 size — good for many same-shaped small allocations.
 *   3 = Page    — allocations are rounded up to 4096-byte page boundaries,
 *                 for mmap/DMA/kernel-interface-style buffers.
 *   4 = Ring    — on exhaustion, wraps back around to the start of the
 *                 buffer instead of falling back to malloc, silently
 *                 overwriting the oldest data — for capture buffers, ring
 *                 logs, streaming, where "keep only the most recent N
 *                 bytes" is exactly the desired behavior. */
#define HSH_ARENA_KIND_GENERAL 0
#define HSH_ARENA_KIND_FIXED   1
#define HSH_ARENA_KIND_POOL    2
#define HSH_ARENA_KIND_PAGE    3
#define HSH_ARENA_KIND_RING    4
#define HSH_ARENA_POOL_CHUNK   64
#define HSH_ARENA_PAGE_SIZE    4096

typedef struct { uint8_t* base; uint64_t cap; uint64_t used; int64_t kind; } HshArena;

/* Thread-local stack of "current" arenas, so nested @arena function calls
 * compose correctly (LIFO): each @arena function pushes its own arena on
 * entry and pops+frees it on every exit path, and arena-aware allocators
 * (hsh_array_new, hsh_struct_new, hsh_strcat, ...) always allocate from
 * whichever arena is topmost right now — or fall back to plain malloc if
 * none is active, which is the vast majority of H# code today. */
#define HSH_ARENA_STACK_MAX 64
static __thread HshArena* hsh_arena_stack[HSH_ARENA_STACK_MAX];
static __thread int       hsh_arena_stack_top = 0;

/* `kind` was previously parsed (see ast.rs's `ArenaKind`) but never once
 * read anywhere in codegen.rs or here — `arena(pool, N)`, `arena(page, N)`
 * and `arena(ring, N)` all silently compiled to the exact same bump
 * allocator as plain `arena(N)`, so the documented per-kind semantics
 * (equal-size pool chunks, page alignment, overwrite-oldest ring, panic-
 * on-overflow fixed) didn't actually exist at runtime. This constructor
 * plus the kind-aware logic in `hsh_arena_alloc` below is what makes each
 * kind behave differently for real. */
HshArena* hsh_arena_new_kind(uint64_t cap, int64_t kind) {
    HshArena* a = (HshArena*)malloc(sizeof(HshArena));
    if (!a) return NULL;
    a->base = (uint8_t*)malloc(cap);
    a->cap  = cap;
    a->used = 0;
    a->kind = kind;
    return a;
}
/* Plain `hsh_arena_new` is always General-kind — this is what every
 * `@arena`-annotated *function* prologue calls (the `@arena` annotation
 * itself has no kind syntax, only `unsafe arena(kind, N) is...end` /
 * `unsafe pool(N) is...end`/etc *blocks* do — see codegen.rs). */
HshArena* hsh_arena_new(uint64_t cap) {
    return hsh_arena_new_kind(cap, HSH_ARENA_KIND_GENERAL);
}
void* hsh_arena_alloc(HshArena* a, uint64_t n) {
    if (!a) return malloc(n);
    uint64_t align = 8;
    if (a->kind == HSH_ARENA_KIND_POOL) align = HSH_ARENA_POOL_CHUNK;
    else if (a->kind == HSH_ARENA_KIND_PAGE) align = HSH_ARENA_PAGE_SIZE;
    uint64_t aligned = (n + (align - 1)) & ~(align - 1);

    if (a->used + aligned > a->cap) {
        if (a->kind == HSH_ARENA_KIND_FIXED) {
            /* `arena(N)` / `arena(fixed, N)`: the whole point of asking for
             * an exact fixed capacity is to know for certain you'll never
             * silently spill onto the regular heap — so exceeding it is a
             * hard error, not a graceful degrade. */
            hsh_panic("arena(fixed) capacity exceeded — allocation would overflow the fixed-size arena");
        }
        if (a->kind == HSH_ARENA_KIND_RING && aligned <= a->cap) {
            /* Wrap around and overwrite the oldest data instead of
             * growing or falling back to malloc — this is the one kind
             * where "exhausted" isn't an error at all, it's the normal
             * steady state once the buffer has filled up once. */
            a->used = 0;
        } else {
            /* General/Pool/Page (or a Ring request bigger than the whole
             * buffer): degrade gracefully to a regular heap allocation
             * rather than aborting the process. Note the returned pointer
             * isn't necessarily arena memory even when an arena is active;
             * see the caution on hsh_array_free etc. below about not
             * blindly free()-ing arena-backed allocations. */
            return malloc(n);
        }
    }
    void* p = a->base + a->used;
    a->used += aligned;
    return p;
}
void hsh_arena_free(HshArena* a) { if (a) { free(a->base); free(a); } }

/* Push `a` as the current arena for this thread (emitted at the entry of
 * every `@arena`-annotated function). Past HSH_ARENA_STACK_MAX levels of
 * nesting this silently stops tracking (new allocations fall back to
 * malloc) rather than overflowing the stack array — @arena nesting that
 * deep would be unusual, and degrading gracefully beats corrupting
 * memory. */
void hsh_arena_push_current(HshArena* a) {
    if (hsh_arena_stack_top < HSH_ARENA_STACK_MAX) {
        hsh_arena_stack[hsh_arena_stack_top++] = a;
    }
}
/* Pop and return the current arena (the one this @arena function pushed
 * on entry), restoring whatever was active before it. The codegen'd
 * epilogue is expected to hsh_arena_free() the returned pointer itself
 * right after popping it — that single free() is what reclaims
 * everything the function bump-allocated during its call. */
HshArena* hsh_arena_pop_current(void) {
    if (hsh_arena_stack_top > 0) {
        return hsh_arena_stack[--hsh_arena_stack_top];
    }
    return NULL;
}
/* Current arena, or NULL if none is active. Internal — consulted by
 * arena-aware allocators below via hsh_alloc(), not called directly from
 * codegen. */
static HshArena* hsh_arena_current(void) {
    return hsh_arena_stack_top > 0 ? hsh_arena_stack[hsh_arena_stack_top - 1] : NULL;
}
/* Generic "allocate n bytes, arena-aware" — the one place that decides
 * arena-vs-malloc, used by every allocator we've made arena-aware so far
 * (hsh_array_new, hsh_struct_new, hsh_strcat). NOTE: because this can
 * return either arena memory (a sub-range of one big malloc'd block) or
 * a standalone malloc'd pointer depending on context, anything using it
 * must NOT be free()'d individually — only hsh_arena_free() on the whole
 * arena (for arena memory) or the matching *_free() function (for the
 * malloc fallback case) is safe, and today's codegen never calls those
 * per-object frees at all, so this is consistent with current behavior. */
static void* hsh_alloc(uint64_t n) {
    HshArena* a = hsh_arena_current();
    return a ? hsh_arena_alloc(a, n) : malloc(n);
}

/* ── @arena checkpoint / rewind ("basic v2") ─────────────────────────────────
 * The one thing every other arena kind was still missing: a way to reuse
 * *part* of an arena's lifetime for a shorter-lived burst of temporary
 * allocations without giving up the whole arena. Before this, the only
 * granularity was "the whole function's arena, freed all at once when it
 * returns" — perfectly fine for "do a bunch of work, throw it all away",
 * but there was no way to say "do a bunch of *temporary* work inside a
 * longer-lived arena, then throw away just that part" (e.g. a per-request
 * arena in a server loop, where each request needs its own scratch space
 * that shouldn't accumulate across requests, but the arena itself should
 * outlive any single request).
 *
 * `hsh_arena_checkpoint()` returns the current arena's `used` offset —
 * an opaque mark. `hsh_arena_rewind(mark)` resets `used` back to it,
 * instantly "freeing" (for reuse — nothing is actually deallocated,
 * exactly like a bump allocator's whole design) everything allocated
 * since the checkpoint, without disturbing anything allocated before it.
 * Both operate on whichever arena is current (`hsh_arena_current()`) —
 * same "always affects the topmost pushed arena" convention as
 * `hsh_alloc()` itself. A no-op (mark 0, rewind does nothing) when no
 * arena is active, so calling these in `@default` code is harmless
 * rather than a crash — consistent with `hsh_alloc()`'s own
 * malloc-fallback-when-no-arena behavior. */
int64_t hsh_arena_checkpoint(void) {
    HshArena* a = hsh_arena_current();
    return a ? (int64_t)a->used : 0;
}
void hsh_arena_rewind(int64_t mark) {
    HshArena* a = hsh_arena_current();
    if (!a || mark < 0 || (uint64_t)mark > a->cap) return;
    a->used = (uint64_t)mark;
}
/* Introspection — how much of the current arena is used/free, mainly for
 * diagnostics/tuning (picking a capacity that doesn't degrade to malloc
 * fallback in practice). Returns 0 for both if no arena is active. */
int64_t hsh_arena_used(void) {
    HshArena* a = hsh_arena_current();
    return a ? (int64_t)a->used : 0;
}
int64_t hsh_arena_capacity(void) {
    HshArena* a = hsh_arena_current();
    return a ? (int64_t)a->cap : 0;
}

/* ── String helpers ──────────────────────────────────────────────────────── */

hsh_string hsh_trim(hsh_string s) {
    if (!s) return "";
    while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') s++;
    const char* end = s + strlen(s) - 1;
    while (end > s && (*end == ' ' || *end == '\t' || *end == '\n' || *end == '\r')) end--;
    size_t len = end - s + 1;
    char* out = (char*)malloc(len + 1);
    if (!out) return s;
    memcpy(out, s, len);
    out[len] = '\0';
    return out;
}

int64_t hsh_str_contains(hsh_string h, hsh_string n) {
    return (h && n && strstr(h, n)) ? 1 : 0;
}

hsh_string hsh_to_upper(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);
    if (!out) return s;
    for (size_t i = 0; i <= n; i++) out[i] = toupper((unsigned char)s[i]);
    return out;
}

hsh_string hsh_to_lower(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);
    if (!out) return s;
    for (size_t i = 0; i <= n; i++) out[i] = tolower((unsigned char)s[i]);
    return out;
}

hsh_string hsh_str_replace(hsh_string s, hsh_string from, hsh_string to) {
    if (!s || !from || !to) return s ? s : "";
    size_t flen = strlen(from), tlen = strlen(to), slen = strlen(s);
    int count = 0;
    const char* p = s;
    while ((p = strstr(p, from))) { count++; p += flen; }
    if (!count) return s;
    char* out = (char*)malloc(slen + (size_t)count * (tlen + 1) + 1);
    if (!out) return s;
    char* w = out; p = s;
    const char* q;
    while ((q = strstr(p, from))) {
        size_t pre = (size_t)(q - p);
        memcpy(w, p, pre); w += pre;
        memcpy(w, to, tlen); w += tlen;
        p = q + flen;
    }
    strcpy(w, p);
    return out;
}

int64_t hsh_starts_with(hsh_string s, hsh_string prefix) {
    if (!s || !prefix) return 0;
    return strncmp(s, prefix, strlen(prefix)) == 0 ? 1 : 0;
}

int64_t hsh_ends_with(hsh_string s, hsh_string suffix) {
    if (!s || !suffix) return 0;
    size_t sl = strlen(s), xl = strlen(suffix);
    if (xl > sl) return 0;
    return strcmp(s + sl - xl, suffix) == 0 ? 1 : 0;
}

hsh_string hsh_substr(hsh_string s, int64_t start, int64_t end_idx) {
    if (!s) return "";
    int64_t len = (int64_t)strlen(s);
    if (start < 0) start = 0;
    if (end_idx < 0 || end_idx > len) end_idx = len;
    if (start >= end_idx) return "";
    size_t sz = (size_t)(end_idx - start);
    char* out = (char*)malloc(sz + 1);
    if (!out) return "";
    memcpy(out, s + start, sz);
    out[sz] = '\0';
    return out;
}

/* ── Time ────────────────────────────────────────────────────────────────── */

int64_t hsh_now_unix(void) { return (int64_t)time(NULL); }

int64_t hsh_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

void hsh_sleep_ms(int64_t ms) {
    struct timespec ts = { ms / 1000, (ms % 1000) * 1000000 };
    nanosleep(&ts, NULL);
}

/* ── Math ────────────────────────────────────────────────────────────────── */

double hsh_sin(double x)   { return sin(x);   }
double hsh_cos(double x)   { return cos(x);   }
double hsh_tan(double x)   { return tan(x);   }
double hsh_sqrt(double x)  { return sqrt(x);  }
double hsh_pow(double x, double y) { return pow(x, y); }
double hsh_floor(double x) { return floor(x); }
double hsh_ceil(double x)  { return ceil(x);  }
double hsh_abs_f(double x) { return fabs(x);  }
int64_t hsh_abs_i(int64_t x) { return x < 0 ? -x : x; }
int64_t hsh_min_i(int64_t a, int64_t b) { return a < b ? a : b; }
int64_t hsh_max_i(int64_t a, int64_t b) { return a > b ? a : b; }
double  hsh_min_f(double a, double b)   { return a < b ? a : b; }
double  hsh_max_f(double a, double b)   { return a > b ? a : b; }

/* ── System ──────────────────────────────────────────────────────────────── */

hsh_string hsh_hostname(void) {
    static char buf[256];
    gethostname(buf, sizeof(buf));
    return buf;
}

int64_t hsh_getpid(void) { return (int64_t)getpid(); }

hsh_string hsh_getenv(hsh_string key) {
    if (!key) return "";
    const char* v = getenv(key);
    return v ? v : "";
}

hsh_string hsh_shell(hsh_string cmd) {
    if (!cmd) return "";
    FILE* fp = popen(cmd, "r");
    if (!fp) return "";
    char* buf = NULL;
    size_t total = 0, cap = 0;
    char chunk[4096];
    while (fgets(chunk, sizeof(chunk), fp)) {
        size_t n = strlen(chunk);
        if (total + n + 1 > cap) {
            cap = (cap + n + 1) * 2;
            char* nb = (char*)realloc(buf, cap);
            if (!nb) { free(buf); pclose(fp); return ""; }
            buf = nb;
        }
        memcpy(buf + total, chunk, n);
        total += n;
    }
    pclose(fp);
    if (!buf) return "";
    buf[total] = '\0';
    return buf;
}

hsh_string hsh_shell_escape(hsh_string s) {
    if (!s) return "''";
    size_t n = strlen(s);
    char* out = (char*)malloc(n * 4 + 3);
    if (!out) return "''";
    size_t w = 0;
    out[w++] = '\'';
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '\'') {
            out[w++] = '\''; out[w++] = '\\'; out[w++] = '\''; out[w++] = '\'';
        } else {
            out[w++] = s[i];
        }
    }
    out[w++] = '\'';
    out[w] = '\0';
    return out;
}

/* fork+execve — no shell, no injection */
static hsh_string hsh_exec_argv(char* const argv[]) {
    int pipefd[2];
    if (pipe(pipefd) != 0) return "";
    pid_t pid = fork();
    if (pid < 0) { close(pipefd[0]); close(pipefd[1]); return ""; }
    if (pid == 0) {
        dup2(pipefd[1], STDOUT_FILENO);
        dup2(pipefd[1], STDERR_FILENO);
        close(pipefd[0]); close(pipefd[1]);
        execvp(argv[0], argv);
        _exit(127);
    }
    close(pipefd[1]);
    char* buf = NULL; size_t total = 0, cap = 0; char chunk[4096]; ssize_t n;
    while ((n = read(pipefd[0], chunk, sizeof(chunk))) > 0) {
        if (total + (size_t)n + 1 > cap) {
            cap = (cap + (size_t)n + 1) * 2;
            char* nb = (char*)realloc(buf, cap);
            if (!nb) { free(buf); close(pipefd[0]); waitpid(pid, NULL, 0); return ""; }
            buf = nb;
        }
        memcpy(buf + total, chunk, (size_t)n); total += (size_t)n;
    }
    close(pipefd[0]); waitpid(pid, NULL, 0);
    if (!buf) return "";
    buf[total] = '\0';
    return buf;
}

hsh_string hsh_exec1(hsh_string cmd) {
    if (!cmd) return "";
    char* argv[2] = { (char*)cmd, NULL };
    return hsh_exec_argv(argv);
}
hsh_string hsh_exec2(hsh_string cmd, hsh_string a1) {
    char* argv[3] = { (char*)cmd, (char*)(a1?a1:""), NULL };
    return hsh_exec_argv(argv);
}
hsh_string hsh_exec3(hsh_string cmd, hsh_string a1, hsh_string a2) {
    char* argv[4] = { (char*)cmd, (char*)(a1?a1:""), (char*)(a2?a2:""), NULL };
    return hsh_exec_argv(argv);
}
hsh_string hsh_exec4(hsh_string cmd, hsh_string a1, hsh_string a2, hsh_string a3) {
    char* argv[5] = { (char*)cmd, (char*)(a1?a1:""), (char*)(a2?a2:""), (char*)(a3?a3:""), NULL };
    return hsh_exec_argv(argv);
}

hsh_string hsh_py_eval(hsh_string code) {
    if (!code) return "";
    char* argv[4] = { (char*)"python3", (char*)"-c", (char*)code, NULL };
    return hsh_exec_argv(argv);
}
hsh_string hsh_py_repr(hsh_string s) {
    if (!s) return "''";
    size_t n = strlen(s);
    char* out = (char*)malloc(n * 2 + 3);
    if (!out) return "''";
    size_t w = 0; out[w++] = '\'';
    for (size_t i = 0; i < n; i++) {
        switch (s[i]) {
            case '\'': out[w++]='\\'; out[w++]='\''; break;
            case '\\': out[w++]='\\'; out[w++]='\\'; break;
            case '\n': out[w++]='\\'; out[w++]='n';  break;
            case '\r': out[w++]='\\'; out[w++]='r';  break;
            default:   out[w++]=s[i];
        }
    }
    out[w++] = '\''; out[w] = '\0';
    return out;
}

/* ── Random ──────────────────────────────────────────────────────────────── */

hsh_string hsh_random_hex(int64_t n) {
    if (n <= 0) return "";
    char* buf = (char*)malloc((size_t)n * 2 + 1);
    if (!buf) return "";
    FILE* fp = fopen("/dev/urandom", "rb");
    if (!fp) { buf[0] = '\0'; return buf; }
    for (int64_t i = 0; i < n; i++) {
        unsigned char b; fread(&b, 1, 1, fp);
        snprintf(buf + i * 2, 3, "%02x", b);
    }
    fclose(fp); buf[n * 2] = '\0';
    return buf;
}

int64_t hsh_random_int(int64_t min, int64_t max) {
    uint64_t r = 0;
    FILE* fp = fopen("/dev/urandom", "rb");
    if (fp) { fread(&r, 8, 1, fp); fclose(fp); }
    if (max <= min) return min;
    return min + (int64_t)(r % (uint64_t)(max - min));
}

hsh_string hsh_random_string(int64_t n) {
    static const char cs[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    if (n <= 0) return "";
    char* out = (char*)malloc((size_t)n + 1);
    uint8_t* tmp = (uint8_t*)malloc((size_t)n);
    if (!out || !tmp) { free(out); free(tmp); return ""; }
    FILE* f = fopen("/dev/urandom", "rb");
    if (f) { fread(tmp, 1, (size_t)n, f); fclose(f); }
    for (int64_t i = 0; i < n; i++) out[i] = cs[tmp[i] % 62];
    free(tmp); out[n] = '\0';
    return out;
}

hsh_string hsh_uuid_v4(void) {
    uint8_t b[16] = {0};
    FILE* f = fopen("/dev/urandom", "rb");
    if (f) { fread(b, 1, 16, f); fclose(f); }
    b[6] = (b[6] & 0x0f) | 0x40;
    b[8] = (b[8] & 0x3f) | 0x80;
    char* out = (char*)malloc(37);
    if (!out) return "00000000-0000-4000-0000-000000000000";
    snprintf(out, 37,
        "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
        b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],
        b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]);
    return out;
}

/* ── Filesystem ──────────────────────────────────────────────────────────── */

int64_t hsh_file_exists(hsh_string path) {
    if (!path) return 0;
    struct stat st; return (stat(path, &st) == 0) ? 1 : 0;
}

int64_t hsh_is_file(hsh_string path) {
    if (!path) return 0;
    struct stat st; return (stat(path, &st) == 0 && S_ISREG(st.st_mode)) ? 1 : 0;
}

int64_t hsh_is_dir(hsh_string path) {
    if (!path) return 0;
    struct stat st; return (stat(path, &st) == 0 && S_ISDIR(st.st_mode)) ? 1 : 0;
}

hsh_string hsh_read_file(hsh_string path) {
    if (!path) return "";
    FILE* f = fopen(path, "rb");
    if (!f) return "";
    fseek(f, 0, SEEK_END); long sz = ftell(f); rewind(f);
    if (sz < 0) { fclose(f); return ""; }
    char* buf = (char*)malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return ""; }
    fread(buf, 1, (size_t)sz, f); buf[sz] = '\0'; fclose(f);
    return buf;
}

int64_t hsh_write_file(hsh_string path, hsh_string content) {
    if (!path) return 0;
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f); return 1;
}

int64_t hsh_append_file(hsh_string path, hsh_string content) {
    if (!path) return 0;
    FILE* f = fopen(path, "ab");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f); return 1;
}

int64_t hsh_remove_file(hsh_string path) {
    return (path && remove(path) == 0) ? 1 : 0;
}

int64_t hsh_mkdir_all(hsh_string path) {
    if (!path) return 0;
    char tmp[4096];
    snprintf(tmp, sizeof(tmp), "%s", path);
    for (char* p = tmp + 1; *p; p++) {
        if (*p == '/') { *p = '\0'; mkdir(tmp, 0755); *p = '/'; }
    }
    mkdir(tmp, 0755); return 1;
}

int64_t hsh_file_size(hsh_string path) {
    if (!path) return -1;
    struct stat st;
    return (stat(path, &st) == 0) ? (int64_t)st.st_size : -1;
}

hsh_string hsh_getcwd(void) {
    char buf[4096];
    return getcwd(buf, sizeof(buf)) ? strdup(buf) : "";
}

int64_t hsh_rename(hsh_string from, hsh_string to) {
    return (from && to && rename(from, to) == 0) ? 1 : 0;
}

/* ── ANSI formatting ─────────────────────────────────────────────────────── */

#define ANSI_FMT(name, code) \
hsh_string name(hsh_string s) { \
    if (!s) return ""; \
    char* out = (char*)malloc(strlen(s) + 16); \
    if (out) sprintf(out, "\x1b[" code "m%s\x1b[0m", s); \
    return out ? out : s; \
}

ANSI_FMT(hsh_bold,        "1")
ANSI_FMT(hsh_green_text,  "32")
ANSI_FMT(hsh_red_text,    "31")
ANSI_FMT(hsh_yellow_text, "33")
ANSI_FMT(hsh_dim_text,    "2")
ANSI_FMT(hsh_cyan_text,   "36")

/* ── Closures ────────────────────────────────────────────────────────────── */

typedef struct { int64_t fn_ptr; int64_t n_caps; int64_t caps[8]; } HshClosure;

HshClosure* hsh_closure_create(int64_t fn_ptr, int64_t n_caps,
    int64_t c0,int64_t c1,int64_t c2,int64_t c3,
    int64_t c4,int64_t c5,int64_t c6,int64_t c7) {
    HshClosure* c = (HshClosure*)malloc(sizeof(HshClosure));
    if (!c) return NULL;
    c->fn_ptr = fn_ptr; c->n_caps = n_caps;
    int64_t ci[8] = {c0,c1,c2,c3,c4,c5,c6,c7};
    for (int64_t i = 0; i < n_caps && i < 8; i++) c->caps[i] = ci[i];
    return c;
}

int64_t hsh_closure_call1(HshClosure* c, int64_t a0) {
    typedef int64_t (*F1)(int64_t);
    typedef int64_t (*F2)(int64_t,int64_t);
    typedef int64_t (*F3)(int64_t,int64_t,int64_t);
    if (!c) return 0;
    switch (c->n_caps) {
        case 0: return ((F1)(void*)c->fn_ptr)(a0);
        case 1: return ((F2)(void*)c->fn_ptr)(a0, c->caps[0]);
        case 2: return ((F3)(void*)c->fn_ptr)(a0, c->caps[0], c->caps[1]);
        default: return ((F1)(void*)c->fn_ptr)(a0);
    }
}

int64_t hsh_closure_call2(HshClosure* c, int64_t a0, int64_t a1) {
    typedef int64_t (*F2)(int64_t,int64_t);
    typedef int64_t (*F3)(int64_t,int64_t,int64_t);
    typedef int64_t (*F4)(int64_t,int64_t,int64_t,int64_t);
    if (!c) return 0;
    switch (c->n_caps) {
        case 0: return ((F2)(void*)c->fn_ptr)(a0, a1);
        case 1: return ((F3)(void*)c->fn_ptr)(a0, a1, c->caps[0]);
        case 2: return ((F4)(void*)c->fn_ptr)(a0, a1, c->caps[0], c->caps[1]);
        default: return ((F2)(void*)c->fn_ptr)(a0, a1);
    }
}

hsh_string hsh_val_to_str(int64_t v) {
    if (v == 0) return "0";
    if ((uintptr_t)v > 65536 && (uintptr_t)v < (uintptr_t)0x7fffffffffff) {
        const char* p = (const char*)v;
        unsigned char first = (unsigned char)p[0];
        if (first == 0 || (first >= 0x20 && first < 0x80)) return (hsh_string)v;
    }
    return hsh_int_to_string(v);
}

hsh_string hsh_http_get(hsh_string url) {
    if (!url) return "";
    char cmd[4096];
    snprintf(cmd, sizeof(cmd), "curl -s -L --max-time 15 -A 'H#/0.7' '%s' 2>/dev/null", url);
    return hsh_shell(cmd);
}

hsh_string hsh_http_post(hsh_string url, hsh_string body) {
    if (!url) return "";
    char cmd[8192];
    snprintf(cmd, sizeof(cmd),
        "curl -s -L -X POST --max-time 15 -H 'Content-Type: application/json' -d '%s' '%s' 2>/dev/null",
        body ? body : "", url);
    return hsh_shell(cmd);
}

int64_t hsh_atoll_export(hsh_string s) { return hsh_atoll(s); }
double  hsh_atof_export(hsh_string s)  { return hsh_atof(s); }

/* ── Dynamic array runtime ───────────────────────────────────────────────────
 * H# dynamic arrays are represented as HshArray* pointers on the heap.
 * Layout: { int64_t len; int64_t cap; int64_t data[cap]; }
 * All elements are i64 (strings = char*, ints, bools cast to i64).
 */

typedef struct {
    int64_t len;
    int64_t cap;
    int64_t data[1]; /* flexible array */
} HshArray;

static HshArray *hsh_arr_alloc(int64_t cap) {
    if (cap < 4) cap = 4;
    HshArray *a = (HshArray*)hsh_alloc(sizeof(int64_t)*2 + sizeof(int64_t)*(size_t)cap);
    if (!a) return NULL;
    a->len = 0;
    a->cap = cap;
    return a;
}

HshArray *hsh_array_new(void) {
    return hsh_arr_alloc(4);
}

HshArray *hsh_array_push(HshArray *a, int64_t val) {
    if (!a) a = hsh_array_new();
    if (a->len >= a->cap) {
        int64_t new_cap = a->cap * 2;
        HshArray *b = hsh_arr_alloc(new_cap);
        if (!b) return a;
        b->len = a->len;
        b->cap = new_cap;
        for (int64_t i = 0; i < a->len; i++) b->data[i] = a->data[i];
        free(a);
        a = b;
    }
    a->data[a->len++] = val;
    return a;
}

int64_t hsh_array_len(HshArray *a) {
    if (!a) return 0;
    return a->len;
}

int64_t hsh_array_get(HshArray *a, int64_t idx) {
    if (!a || idx < 0 || idx >= a->len) return 0;
    return a->data[idx];
}

HshArray *hsh_array_set(HshArray *a, int64_t idx, int64_t val) {
    if (!a || idx < 0 || idx >= a->len) return a;
    a->data[idx] = val;
    return a;
}

HshArray *hsh_array_concat(HshArray *a, HshArray *b) {
    if (!a) return b ? b : hsh_array_new();
    if (!b) return a;
    HshArray *r = hsh_arr_alloc(a->len + b->len);
    r->len = a->len + b->len;
    for (int64_t i = 0; i < a->len; i++) r->data[i]        = a->data[i];
    for (int64_t i = 0; i < b->len; i++) r->data[a->len+i] = b->data[i];
    return r;
}

HshArray *hsh_array_contains(HshArray *a, int64_t val) {
    if (!a) return (HshArray*)0;
    for (int64_t i = 0; i < a->len; i++) {
        if (a->data[i] == val) return (HshArray*)1;
    }
    return (HshArray*)0;
}

/* ── env::args() ─────────────────────────────────────────────────────────────
 * Returns a HshArray* of char* pointers (command-line arguments).
 * The runtime main() in core.c stores argc/argv in globals when the
 * compiled binary starts; this function retrieves them.
 */
extern int   _hsh_argc;
extern char **_hsh_argv;

HshArray *hsh_env_args(void) {
    HshArray *a = hsh_arr_alloc(_hsh_argc > 0 ? _hsh_argc : 1);
    for (int i = 0; i < _hsh_argc; i++) {
        a->data[a->len++] = (int64_t)(uintptr_t)_hsh_argv[i];
    }
    return a;
}

/* ── struct / field access helpers ──────────────────────────────────────────
 * H# structs are heap-allocated arrays of i64 fields (in declaration order).
 * hsh_struct_new(n_fields)    — allocate struct with n_fields slots
 * hsh_struct_get(ptr, index)  — read field at index
 * hsh_struct_set(ptr, index, val) — write field; returns the struct ptr
 */
int64_t *hsh_struct_new(int64_t n) {
    int64_t *s = (int64_t*)hsh_alloc((size_t)n * sizeof(int64_t));
    if (s) memset(s, 0, (size_t)n * sizeof(int64_t));
    return s;
}

int64_t hsh_struct_get(int64_t *s, int64_t idx) {
    if (!s) return 0;
    return s[idx];
}

int64_t *hsh_struct_set(int64_t *s, int64_t idx, int64_t val) {
    if (s) s[idx] = val;
    return s;
}

/* ── string_split ────────────────────────────────────────────────────────────
 * Returns HshArray* of char* substrings split by sep.
 */
HshArray *hsh_string_split(const char *str, const char *sep) {
    HshArray *a = hsh_array_new();
    if (!str || !sep) return a;
    size_t slen = strlen(sep);
    if (slen == 0) { a = hsh_array_push(a, (int64_t)(uintptr_t)strdup(str)); return a; }
    const char *p = str;
    const char *found;
    while ((found = strstr(p, sep)) != NULL) {
        size_t part_len = (size_t)(found - p);
        char *part = (char*)malloc(part_len + 1);
        memcpy(part, p, part_len);
        part[part_len] = '\0';
        a = hsh_array_push(a, (int64_t)(uintptr_t)part);
        p = found + slen;
    }
    a = hsh_array_push(a, (int64_t)(uintptr_t)strdup(p));
    return a;
}

/* ── proc_id ─────────────────────────────────────────────────────────────────*/
int64_t hsh_proc_id(void) { return (int64_t)getpid(); }

/* ── string_at (single char as string) ──────────────────────────────────────*/
const char *hsh_string_at(const char *s, int64_t idx) {
    if (!s || idx < 0 || idx >= (int64_t)strlen(s)) return "";
    static __thread char buf[4];
    buf[0] = s[idx]; buf[1] = '\0';
    return buf;
}

/* ── string_slice ────────────────────────────────────────────────────────────*/
const char *hsh_string_slice(const char *s, int64_t start, int64_t end) {
    if (!s) return "";
    int64_t slen = (int64_t)strlen(s);
    if (start < 0) start = 0;
    if (end > slen) end = slen;
    if (start >= end) return "";
    int64_t len = end - start;
    char *out = (char*)malloc((size_t)len + 1);
    memcpy(out, s + start, (size_t)len);
    out[len] = '\0';
    return out;
}

/* ── string_find / string_rfind ─────────────────────────────────────────────*/
int64_t hsh_string_find(const char *haystack, const char *needle) {
    if (!haystack || !needle) return -1;
    const char *p = strstr(haystack, needle);
    return p ? (int64_t)(p - haystack) : -1;
}
int64_t hsh_string_rfind(const char *haystack, const char *needle) {
    if (!haystack || !needle) return -1;
    size_t hlen = strlen(haystack), nlen = strlen(needle);
    if (nlen > hlen) return -1;
    for (int64_t i = (int64_t)(hlen - nlen); i >= 0; i--) {
        if (memcmp(haystack + i, needle, nlen) == 0) return i;
    }
    return -1;
}

/* ── string_pad_right ────────────────────────────────────────────────────────*/
const char *hsh_string_pad_right(const char *s, int64_t width) {
    if (!s) s = "";
    int64_t slen = (int64_t)strlen(s);
    if (slen >= width) return s;
    char *out = (char*)malloc((size_t)width + 1);
    memcpy(out, s, (size_t)slen);
    memset(out + slen, ' ', (size_t)(width - slen));
    out[width] = '\0';
    return out;
}

/* ── string_repeat ───────────────────────────────────────────────────────────*/
const char *hsh_string_repeat(const char *s, int64_t n) {
    if (!s || n <= 0) return "";
    size_t slen = strlen(s);
    char *out = (char*)malloc(slen * (size_t)n + 1);
    for (int64_t i = 0; i < n; i++) memcpy(out + slen*(size_t)i, s, slen);
    out[slen*(size_t)n] = '\0';
    return out;
}

/* ── to_int / to_float ───────────────────────────────────────────────────────*/
int64_t hsh_to_int(const char *s) {
    if (!s) return 0;
    return (int64_t)strtoll(s, NULL, 10);
}
/* Convert a single hex-digit character ('0'-'9', 'a'-'f', 'A'-'F') to its
 * 0-15 value. Only the first character of `s` is examined (this mirrors
 * how callers use it: one character at a time while scanning a hex
 * string, e.g. `to_int_from_hex(string_at(s, i))`). Returns 0 for
 * anything that isn't a valid hex digit rather than erroring, matching
 * the permissive style of the other hsh_to_* conversion builtins. */
int64_t hsh_to_int_from_hex(const char *s) {
    if (!s || !s[0]) return 0;
    char c = s[0];
    if (c >= '0' && c <= '9') return (int64_t)(c - '0');
    if (c >= 'a' && c <= 'f') return (int64_t)(c - 'a' + 10);
    if (c >= 'A' && c <= 'F') return (int64_t)(c - 'A' + 10);
    return 0;
}
double hsh_to_float(const char *s) {
    if (!s) return 0.0;
    return strtod(s, NULL);
}

/* ── string_lower / string_upper ─────────────────────────────────────────────*/
const char *hsh_string_lower(const char *s) {
    if (!s) return "";
    size_t len = strlen(s);
    char *out = (char*)malloc(len + 1);
    for (size_t i = 0; i < len; i++) out[i] = (char)tolower((unsigned char)s[i]);
    out[len] = '\0';
    return out;
}
const char *hsh_string_upper(const char *s) {
    if (!s) return "";
    size_t len = strlen(s);
    char *out = (char*)malloc(len + 1);
    for (size_t i = 0; i < len; i++) out[i] = (char)toupper((unsigned char)s[i]);
    out[len] = '\0';
    return out;
}

/* ── string_trim_right ───────────────────────────────────────────────────────*/
const char *hsh_string_trim_right(const char *s) {
    if (!s) return "";
    size_t len = strlen(s);
    while (len > 0 && isspace((unsigned char)s[len-1])) len--;
    char *out = (char*)malloc(len + 1);
    memcpy(out, s, len);
    out[len] = '\0';
    return out;
}

/* ── file helpers ────────────────────────────────────────────────────────────*/
int64_t hsh_file_delete(const char *path) {
    return remove(path) == 0 ? 1 : 0;
}
int64_t hsh_dir_create(const char *path) {
    return mkdir(path, 0755) == 0 ? 1 : 0;
}
int64_t hsh_dir_exists(const char *path) {
    struct stat st;
    return (stat(path, &st) == 0 && S_ISDIR(st.st_mode)) ? 1 : 0;
}

/* ── hsh_readline — read line from stdin ─────────────────────────────────────*/
char *hsh_readline(void) {
    char *buf = (char*)malloc(4096);
    if (!buf) return (char*)"";
    if (!fgets(buf, 4096, stdin)) { buf[0] = '\0'; return buf; }
    size_t n = strlen(buf);
    if (n > 0 && buf[n-1] == '\n') buf[n-1] = '\0';
    return buf;
}

/* ── hsh_scan_port_net — already declared, stub if not present ───────────────*/
#ifndef HSH_SCAN_PORT_DEFINED
int64_t hsh_scan_port_net(const char *host, int64_t port, int64_t timeout_ms) {
    struct sockaddr_in addr = {0};
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return 0;
    addr.sin_family = AF_INET;
    addr.sin_port   = htons((uint16_t)port);
    inet_pton(AF_INET, host, &addr.sin_addr);
    struct timeval tv = { timeout_ms/1000, (timeout_ms%1000)*1000 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    int rc = connect(fd, (struct sockaddr*)&addr, sizeof(addr));
    close(fd);
    return rc == 0 ? 1 : 0;
}
#endif

/* ── hsh_string_chars — return HshArray* of single-char strings ──────────────*/
HshArray *hsh_string_chars(const char *s) {
    HshArray *a = hsh_array_new();
    if (!s) return a;
    size_t n = strlen(s);
    for (size_t i = 0; i < n; i++) {
        char *ch = (char*)malloc(2);
        ch[0] = s[i]; ch[1] = '\0';
        a = hsh_array_push(a, (int64_t)(uintptr_t)ch);
    }
    return a;
}

/* ── dir_remove_all — recursive delete ───────────────────────────────────────*/
int64_t hsh_dir_remove_all(const char *path) {
    char cmd[4096];
    snprintf(cmd, sizeof(cmd), "rm -rf '%s'", path);
    return system(cmd) == 0 ? 1 : 0;
}

/* ── bytes_to_string ─────────────────────────────────────────────────────────*/
const char *hsh_bytes_to_string(HshArray *bytes, int64_t n) {
    if (!bytes || n <= 0) return "";
    char *out = (char*)malloc((size_t)n + 1);
    for (int64_t i = 0; i < n && i < bytes->len; i++)
        out[i] = (char)(bytes->data[i] & 0xFF);
    out[n] = '\0';
    return out;
}

/* ── string_to_bytes ─────────────────────────────────────────────────────────*/
HshArray *hsh_string_to_bytes(const char *s) {
    HshArray *a = hsh_array_new();
    if (!s) return a;
    size_t n = strlen(s);
    for (size_t i = 0; i < n; i++)
        a = hsh_array_push(a, (int64_t)(uint8_t)s[i]);
    return a;
}

/* ── array_push for string convenience (alias) ───────────────────────────────*/
HshArray *hsh_array_push_str(HshArray *a, const char *s) {
    return hsh_array_push(a, (int64_t)(uintptr_t)s);
}

/* ── hsh_string_contains / hsh_string_replace (missing aliases) ──────────────*/
int64_t hsh_string_contains(const char *h, const char *n) { return hsh_str_contains(h,n); }
const char *hsh_string_replace(const char *s, const char *f, const char *r) { return hsh_str_replace(s,f,r); }
const char *hsh_string_trim(const char *s) { return hsh_trim(s); }
int64_t hsh_string_starts_with(const char *s, const char *p) { return hsh_starts_with(s,p); }
int64_t hsh_string_ends_with(const char *s, const char *p) { return hsh_ends_with(s,p); }
int64_t hsh_string_len(const char *s) { return s ? (int64_t)strlen(s) : 0; }
int64_t hsh_array_remove(HshArray *a, int64_t idx) {
    if (!a || idx < 0 || idx >= a->len) return 0;
    for (int64_t i = idx; i < a->len-1; i++) a->data[i] = a->data[i+1];
    a->len--;
    return 1;
}

/* ── hsh_dns_resolve ─────────────────────────────────────────────────────────*/
#include <netdb.h>
const char *hsh_dns_resolve(const char *hostname) {
    if (!hostname) return "";
    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_family   = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(hostname, NULL, &hints, &res) != 0) return "";
    char *out = (char*)malloc(INET_ADDRSTRLEN + 1);
    struct sockaddr_in *addr4 = (struct sockaddr_in *)res->ai_addr;
    inet_ntop(AF_INET, &addr4->sin_addr, out, INET_ADDRSTRLEN);
    freeaddrinfo(res);
    return out;
}

/* ── hsh_json_get ────────────────────────────────────────────────────────────
 * Minimal JSON string-field extractor: hsh_json_get(json, key)
 * Finds "key":"value" and returns the value string.
 * Not a full JSON parser — handles simple flat objects.              */
const char *hsh_json_get(const char *json, const char *key) {
    if (!json || !key) return "";
    /* Build search pattern: "key":" */
    size_t klen = strlen(key);
    char *pattern = (char*)malloc(klen + 4);
    pattern[0] = '"';
    memcpy(pattern + 1, key, klen);
    pattern[klen + 1] = '"';
    pattern[klen + 2] = ':';
    pattern[klen + 3] = '\0';
    const char *p = strstr(json, pattern);
    free(pattern);
    if (!p) return "";
    p += klen + 3; /* skip "key": */
    while (*p == ' ' || *p == '\t') p++;
    if (*p == '"') {
        p++; /* skip opening quote */
        const char *end = strchr(p, '"');
        if (!end) return "";
        size_t vlen = (size_t)(end - p);
        char *out = (char*)malloc(vlen + 1);
        memcpy(out, p, vlen);
        out[vlen] = '\0';
        return out;
    }
    /* Numeric / bool / null value */
    const char *end = p;
    while (*end && *end != ',' && *end != '}' && *end != ']' && *end != '\n') end++;
    size_t vlen = (size_t)(end - p);
    char *out = (char*)malloc(vlen + 1);
    memcpy(out, p, vlen);
    out[vlen] = '\0';
    return out;
}

/* ── @arc (basic v3) ──────────────────────────────────────────────────────
 * Real, working refcounting primitives. Every arc-allocated block gets a
 * leading header with an atomic *strong* refcount word (hsh_rc_alloc
 * starts it at 1, hsh_rc_retain/_release increment/decrement) and the
 * originally-requested size, so hsh_ptr_alloc_size (see the @pointers
 * section below) can report it back for exactly this kind of pointer.
 *
 * The compiler DOES now insert automatic retain-on-assignment/release-on-
 * scope-exit for straight-line top-level `let` bindings in an `@arc`
 * function (see codegen.rs's `arc_owned` field and `emit_arc_epilogue`) —
 * `arc_retain`/`arc_release` (wired up as H# builtins in codegen.rs) are
 * still there directly too, for anything the automatic tracking doesn't
 * reach (a value stored in a struct field, one only bound inside an
 * if/while/match branch, etc).
 *
 * v3 adds a *weak* count alongside the strong one — the header (and thus
 * the whole allocation) now survives until *both* counts hit zero, not
 * just the strong one. This is what makes `arc_downgrade`/`arc_upgrade`
 * safe: a weak reference alone is never enough to keep the data alive
 * (so cyclic structures — the `@arc` gap this fixes — can break the cycle
 * by making one direction weak), but it *is* enough to safely ask "is
 * this still alive?" without a use-after-free, because the header itself
 * — the thing `arc_upgrade` has to read to answer that question — is
 * guaranteed to still be valid memory as long as any weak ref exists.
 * Same design as Rust's `std::sync::{Arc, Weak}`.
 */
#include <stdatomic.h>
typedef struct { _Atomic int64_t count; _Atomic int64_t weak; uint64_t size; } HshRcHeader;

void* hsh_rc_alloc(uint64_t n) {
    HshRcHeader* h = (HshRcHeader*)malloc(sizeof(HshRcHeader) + (size_t)n);
    if (!h) return NULL;
    atomic_init(&h->count, 1);
    atomic_init(&h->weak, 0);
    h->size = n;
    return (void*)(h + 1);
}
void hsh_rc_retain(void* p) {
    if (!p) return;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    atomic_fetch_add(&h->count, 1);
}
void hsh_rc_release(void* p) {
    if (!p) return;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    if (atomic_fetch_sub(&h->count, 1) == 1) {
        // Last *strong* ref gone — the data is logically dropped from
        // here on (arc_upgrade will correctly start refusing it), but
        // the allocation itself is only actually freed once no weak
        // refs are watching it either.
        if (atomic_load(&h->weak) == 0) free(h);
    }
}
int64_t hsh_rc_count(void* p) {
    if (!p) return 0;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    return (int64_t)atomic_load(&h->count);
}

/* ── @arc weak references ────────────────────────────────────────────────
 * `arc_downgrade(p)` — takes a strong (or weak) pointer, returns a weak
 * handle (same pointer value; the distinction is purely which counter
 * governs it, not the bits themselves). Does not affect the strong count
 * at all, so it can't keep an otherwise-dead object alive.
 *
 * `arc_upgrade(weak)` — tries to produce a new *strong* reference from a
 * weak one. Returns NULL if the object's strong count has already hit
 * zero (nothing left to upgrade to); otherwise atomically bumps the
 * strong count and returns the same pointer, now a real owning
 * reference the caller must eventually `arc_release`. The
 * compare-exchange loop (rather than a plain fetch-add) is what makes
 * this safe: a plain "load then increment" could resurrect an object
 * whose count was legitimately at zero and being freed by another
 * thread at that exact moment; only incrementing from a strictly-
 * positive value, atomically, avoids that race.
 *
 * `arc_weak_release(weak)` — drops a weak reference. Frees the
 * allocation if this was the last reference of *either* kind.
 *
 * `arc_weak_count(p)` — introspection, mainly for tests/debugging.
 */
void* hsh_arc_downgrade(void* p) {
    if (!p) return NULL;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    atomic_fetch_add(&h->weak, 1);
    return p;
}
void* hsh_arc_upgrade(void* p) {
    if (!p) return NULL;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    int64_t cur = atomic_load(&h->count);
    while (cur > 0) {
        if (atomic_compare_exchange_weak(&h->count, &cur, cur + 1)) {
            return p;
        }
        // cur was refreshed to the actual current value by a failed CAS;
        // loop re-checks `cur > 0` with that fresh value.
    }
    return NULL;
}
void hsh_arc_weak_release(void* p) {
    if (!p) return;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    if (atomic_fetch_sub(&h->weak, 1) == 1) {
        if (atomic_load(&h->count) == 0) free(h);
    }
}
int64_t hsh_arc_weak_count(void* p) {
    if (!p) return 0;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    return (int64_t)atomic_load(&h->weak);
}

/* ── @pointers (basic v1) ─────────────────────────────────────────────────
 * Raw memory access for people who want it: read/write an i64 at a byte
 * offset from a pointer, no bounds checking at all — "modern" only in the
 * sense of being explicit function calls instead of `*`/`&` syntax, and
 * of not aliasing with the rest of H#'s i64-boxed-value convention by
 * accident. It fully trusts the caller, same as raw pointers in C/C++:
 * an out-of-range offset is undefined behavior, not a caught error. */
int64_t hsh_ptr_read_i64(void* p, int64_t byte_offset) {
    if (!p) return 0;
    return *(int64_t*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_i64(void* p, int64_t byte_offset, int64_t val) {
    if (!p) return;
    *(int64_t*)((uint8_t*)p + byte_offset) = val;
}
int64_t hsh_ptr_is_null(void* p) {
    return p == NULL;
}
void* hsh_ptr_add(void* p, int64_t byte_offset) {
    if (!p) return NULL;
    return (void*)((uint8_t*)p + byte_offset);
}

/* ── @pointers (basic v2) — narrower/wider and floating-point variants ────
 * Same no-bounds-checking contract as hsh_ptr_{read,write}_i64 above,
 * just at different widths (and a raw pointer-to-pointer variant for
 * walking arrays of pointers/structs-by-reference). Kept as one function
 * per width, matching the i64 pair above, rather than a single generic
 * entry point, so each stays a trivial one-line load/store that's easy
 * to audit and impossible to get the width of confused at the call site. */
int64_t hsh_ptr_read_i32(void* p, int64_t byte_offset) {
    if (!p) return 0;
    return (int64_t)*(int32_t*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_i32(void* p, int64_t byte_offset, int64_t val) {
    if (!p) return;
    *(int32_t*)((uint8_t*)p + byte_offset) = (int32_t)val;
}
int64_t hsh_ptr_read_i16(void* p, int64_t byte_offset) {
    if (!p) return 0;
    return (int64_t)*(int16_t*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_i16(void* p, int64_t byte_offset, int64_t val) {
    if (!p) return;
    *(int16_t*)((uint8_t*)p + byte_offset) = (int16_t)val;
}
int64_t hsh_ptr_read_i8(void* p, int64_t byte_offset) {
    if (!p) return 0;
    return (int64_t)*(int8_t*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_i8(void* p, int64_t byte_offset, int64_t val) {
    if (!p) return;
    *(int8_t*)((uint8_t*)p + byte_offset) = (int8_t)val;
}
double hsh_ptr_read_f64(void* p, int64_t byte_offset) {
    if (!p) return 0.0;
    return *(double*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_f64(void* p, int64_t byte_offset, double val) {
    if (!p) return;
    *(double*)((uint8_t*)p + byte_offset) = val;
}
double hsh_ptr_read_f32(void* p, int64_t byte_offset) {
    if (!p) return 0.0;
    return (double)*(float*)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_f32(void* p, int64_t byte_offset, double val) {
    if (!p) return;
    *(float*)((uint8_t*)p + byte_offset) = (float)val;
}
void* hsh_ptr_read_ptr(void* p, int64_t byte_offset) {
    if (!p) return NULL;
    return *(void**)((uint8_t*)p + byte_offset);
}
void hsh_ptr_write_ptr(void* p, int64_t byte_offset, void* val) {
    if (!p) return;
    *(void**)((uint8_t*)p + byte_offset) = val;
}

/* ── @pointers (basic v3) ──────────────────────────────────────────────────
 * Fills in the gaps basic v2 left: no way to sanity-check a pointer
 * against its allocation size, no bulk copy/compare (so anyone needing
 * memcpy/memcmp semantics had to write a byte-at-a-time loop with
 * ptr_read_i8/ptr_write_i8), and no way at all to check a pointer *before*
 * touching it. None of this makes @pointers "safe" — that's still not the
 * point of this mode — it just gives you the same handful of primitives
 * C gives you for working with raw memory carefully by hand. */

/* Only meaningful for a pointer that actually came from arc_alloc — it
 * reads the HshRcHeader that hsh_rc_alloc wrote just before `p`. There is
 * no universal way to know the size of an arbitrary pointer (one from
 * `unsafe arena(...)`, or an `extern`-declared C function, carries no
 * such header at all) — calling this on anything but an arc_alloc result
 * reads whatever bytes happen to sit before it and returns garbage. This
 * is exactly why it's `ptr_alloc_size`, not "ptr_size": it answers "how
 * big was the allocation this arc pointer owns", not "how big is
 * whatever this pointer happens to point at" in general. */
int64_t hsh_ptr_alloc_size(void* p) {
    if (!p) return 0;
    HshRcHeader* h = ((HshRcHeader*)p) - 1;
    return (int64_t)h->size;
}
/* memcpy/memmove semantics (overlap-safe, unlike plain memcpy) — copies
 * `n` bytes from `src` to `dst`. */
void hsh_ptr_copy(void* dst, void* src, int64_t n) {
    if (!dst || !src || n <= 0) return;
    memmove(dst, src, (size_t)n);
}
/* memcmp semantics: 0 if equal, negative if `a` sorts before `b`,
 * positive if after — over the first `n` bytes of each. */
int64_t hsh_ptr_compare(void* a, void* b, int64_t n) {
    if (a == b) return 0;
    if (!a || !b || n <= 0) return a ? 1 : (b ? -1 : 0);
    return (int64_t)memcmp(a, b, (size_t)n);
}
/* memset semantics: fill `n` bytes starting at `p` with the low byte of
 * `val`. `hsh_ptr_zero` is the extremely common `fill(p, 0, n)` case
 * given its own name — zeroing a freshly-`arc_alloc`'d buffer before use
 * is common enough (and easy enough to write `ptr_fill(p, 1, n)` by
 * mistake, filling with 0x01 instead of clearing) that it earns a
 * dedicated, harder-to-misuse builtin. */
void hsh_ptr_fill(void* p, int64_t val, int64_t n) {
    if (!p || n <= 0) return;
    memset(p, (int)(val & 0xff), (size_t)n);
}
void hsh_ptr_zero(void* p, int64_t n) {
    if (!p || n <= 0) return;
    memset(p, 0, (size_t)n);
}

/* ── @pointers (basic v4) — opt-in bounds-checked read/write ────────────────
 * `@pointers` stays unchecked by default — that's the whole point of the
 * mode, and staying a thin wrapper over C-style raw access is what keeps
 * it fast and simple. But "no safety net at all, ever" was an all-or-
 * nothing choice: these are an *opt-in* checked path for the one case
 * that's actually checkable — a pointer that came from `arc_alloc`, whose
 * size `hsh_ptr_alloc_size` can read back from its header. Reach for
 * `ptr_read_checked`/`ptr_write_checked` (width in bytes, one of
 * 1/2/4/8) when you want the mistake caught with a clear message instead
 * of quietly corrupting adjacent memory; reach for the unchecked
 * `ptr_read_*`/`ptr_write_*` when you already know the access is in
 * bounds and don't want to pay for the check (e.g. in a hot loop). Like
 * `arena(fixed, N)`'s overflow behavior, a bounds violation here is a
 * hard `hsh_panic` — the whole reason to opt into the checked path is to
 * turn "silent corruption" into "loud, immediate failure", not into
 * another quietly-ignored condition. Only meaningful for arc_alloc
 * pointers, same caveat as `hsh_ptr_alloc_size` itself: called on a
 * pointer without a real HshRcHeader (arena memory, an `extern` C
 * pointer, ...) it reads a garbage "size" and the check is meaningless —
 * this is a safety net for the one specific case it can actually verify,
 * not a general bounds checker. */
int64_t hsh_ptr_read_checked(void* p, int64_t offset, int64_t width) {
    if (!p) { hsh_panic("ptr_read_checked: null pointer"); return 0; }
    int64_t size = hsh_ptr_alloc_size(p);
    if (offset < 0 || width <= 0 || offset + width > size) {
        hsh_panic("ptr_read_checked: access out of bounds of the arc_alloc allocation");
        return 0;
    }
    switch (width) {
        case 1: return (int64_t)*(int8_t*)((uint8_t*)p + offset);
        case 2: return (int64_t)*(int16_t*)((uint8_t*)p + offset);
        case 4: return (int64_t)*(int32_t*)((uint8_t*)p + offset);
        case 8: return *(int64_t*)((uint8_t*)p + offset);
        default:
            hsh_panic("ptr_read_checked: width must be 1, 2, 4, or 8 bytes");
            return 0;
    }
}
void hsh_ptr_write_checked(void* p, int64_t offset, int64_t width, int64_t val) {
    if (!p) { hsh_panic("ptr_write_checked: null pointer"); return; }
    int64_t size = hsh_ptr_alloc_size(p);
    if (offset < 0 || width <= 0 || offset + width > size) {
        hsh_panic("ptr_write_checked: access out of bounds of the arc_alloc allocation");
        return;
    }
    switch (width) {
        case 1: *(int8_t*)((uint8_t*)p + offset)  = (int8_t)val;  return;
        case 2: *(int16_t*)((uint8_t*)p + offset) = (int16_t)val; return;
        case 4: *(int32_t*)((uint8_t*)p + offset) = (int32_t)val; return;
        case 8: *(int64_t*)((uint8_t*)p + offset) = val;          return;
        default: hsh_panic("ptr_write_checked: width must be 1, 2, 4, or 8 bytes");
    }
}
