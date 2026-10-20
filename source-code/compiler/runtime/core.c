#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>  /* strcasecmp (db:: col_bool) */
#include <ctype.h>
#include <unistd.h>
#include <pwd.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <signal.h>
#include <math.h>
#include <netdb.h>
#include <sys/socket.h>
#include <dirent.h>  /* fs::list_dir / fs::walk (added this session) */
#include <sys/utsname.h>  /* sys::sysname/machine/kernel_version (added this session) */
#include <sys/statvfs.h>  /* sys::disk_total/disk_free (added this session) */

/* Global argc/argv storage — written by the H# main() entry point
 * (codegen emits: _hsh_argc = argc; _hsh_argv = argv;)
 * and read by hsh_env_args() so user code can call env::args().     */
int   _hsh_argc = 0;
char **_hsh_argv = NULL;

#include <netinet/in.h>
#include <arpa/inet.h>
#include <poll.h>
#include <fcntl.h>
#include <errno.h>

typedef const char* hsh_string;
typedef int64_t     hsh_int;

/* Forward decl: arena-aware allocator, defined down in the Arena section,
 * but needed by hsh_strcat which comes first in the file. */
static void* hsh_alloc(uint64_t n);
typedef double      hsh_float;

/* H#'s dynamic-array representation — moved up from its original spot
 * in the "── Dynamic arrays ──" section (further down this file) so
 * that functions added this session earlier in the file
 * (fs::read_bytes/write_bytes/read_lines/walk/list_dir,
 * process::run_args) can dereference `->len`/`->data` directly instead
 * of only holding an opaque pointer. `hsh_array_new`/`hsh_array_push`
 * themselves are still *defined* down in that section (an ordinary
 * forward declaration is enough for those, since nothing here needs to
 * see inside them) — only the struct layout needed to move. */
struct HshArray {
    int64_t len;
    int64_t cap;
    int64_t data[1]; /* flexible array */
};
typedef struct HshArray HshArray;
HshArray *hsh_array_new(void);
HshArray *hsh_array_push(HshArray *a, int64_t val);

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

/* strings::index_of(s, sub) -> int. Byte offset of the first
 * occurrence, -1 if absent (matches the interpreter's contract — see
 * builtins_registry.rs). An empty `sub` matches at offset 0, same as
 * strstr's own documented behavior. Added this session. */
int64_t hsh_str_index_of(hsh_string s, hsh_string sub) {
    if (!s || !sub) return -1;
    const char* found = strstr(s, sub);
    return found ? (int64_t)(found - s) : -1;
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
double hsh_round(double x) { return round(x); } /* half away from zero, like Rust f64::round */
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

/* date::format(ts, fmt) / the direct `__builtin_date_format(ts, fmt)` a
 * few std-adjacent callers use (e.g. a shell prompt's clock, a history
 * list's timestamps) — thin `strftime` wrapper. The interpreter's own
 * version is deliberately a "lite" reimplementation supporting only a
 * handful of codes (`%Y %m %d %H %M %S`, per its own doc comment) rather
 * than the real libc `strftime`, presumably to keep interpreter behavior
 * identical across platforms without relying on the host libc's locale
 * data — but every one of those codes IS a standard, locale-independent
 * strftime conversion, so for the LLVM/AOT backend (this runtime, always
 * compiled against and run against a real host libc anyway) calling the
 * real `strftime` directly is strictly a superset of the interpreter's
 * behavior for any format string that only uses those codes, and simply
 * supports more if a caller ever uses others. `localtime_r` (not
 * `gmtime_r`) to match a shell prompt's/history's expectation of
 * wall-clock local time, not UTC. Truncates rather than growing the
 * buffer on a pathological format string — 256 bytes covers any
 * reasonable date/time format many times over. */
hsh_string hsh_date_format(int64_t ts, hsh_string fmt) {
    time_t t = (time_t)ts;
    struct tm tm_buf;
    localtime_r(&t, &tm_buf);
    char buf[256];
    size_t n = strftime(buf, sizeof(buf), (fmt && fmt[0]) ? fmt : "%Y-%m-%d %H:%M:%S", &tm_buf);
    char* out = (char*)hsh_alloc(n + 1);
    memcpy(out, buf, n);
    out[n] = '\0';
    return out;
}

/* ── date::parse ─────────────────────────────────────────────────────────────
 * Backs `__builtin_date_parse(s)`. Same contract as the interpreter's
 * "date_parse": accepts "YYYY-MM-DD" or "YYYY-MM-DD HH:MM:SS" (UTC) and
 * returns a unix timestamp; anything that does not have exactly three
 * date components yields 0. Missing time components default to 0. A 'T'
 * separator is accepted as well (superset of the interpreter).
 * Howard Hinnant's days_from_civil, no libc/timezone dependency. */
static int64_t hsh_days_from_civil(int64_t y, int64_t m, int64_t d) {
    y -= m <= 2;
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    int64_t yoe = y - era * 400;
    int64_t mp  = m > 2 ? m - 3 : m + 9;
    int64_t doy = (153 * mp + 2) / 5 + d - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + doe - 719468;
}

/* Splits `s` on `sep` and parses up to `max` integer components; returns
 * the number of components that parsed successfully (like the
 * interpreter's filter_map over split().parse()). */
static int hsh_parse_parts(const char *s, char sep, int64_t *out, int max) {
    int n = 0;
    while (*s && n < max) {
        char *end;
        while (*s == ' ') s++;
        errno = 0;
        long long v = strtoll(s, &end, 10);
        const char *next = end;
        while (*next && *next != sep) next++;
        if (end != s && (*end == sep || *end == '\0') && errno == 0) out[n++] = (int64_t)v;
        s = *next ? next + 1 : next;
    }
    return n;
}

int64_t hsh_date_parse(hsh_string s) {
    if (!s) return 0;
    char buf[128];
    size_t len = strlen(s);
    if (len >= sizeof(buf)) len = sizeof(buf) - 1;
    memcpy(buf, s, len);
    buf[len] = '\0';
    char *sp = strchr(buf, ' ');
    if (!sp) sp = strchr(buf, 'T');
    const char *time_part = "00:00:00";
    if (sp) { *sp = '\0'; time_part = sp + 1; }
    int64_t d[3] = {0, 0, 0}, t[3] = {0, 0, 0};
    if (hsh_parse_parts(buf, '-', d, 3) != 3) return 0;
    int nt = hsh_parse_parts(time_part, ':', t, 3);
    (void)nt;
    return hsh_days_from_civil(d[0], d[1], d[2]) * 86400 + t[0] * 3600 + t[1] * 60 + t[2];
}

/* ── http::request ───────────────────────────────────────────────────────────
 * Backs `__builtin_http_request(method, url, body)`. Plain HTTP/1.1 over a
 * raw TCP socket (no TLS, no redirects, no chunked-transfer decoding, no
 * keep-alive) — the same limitations as the interpreter's implementation.
 * Returns a 2-slot H# struct { status: int, body: string } laid out like
 * `struct Response` in std/http.h# (status = slot 0, body = slot 1).
 * status 0 means the request itself failed; body then holds the reason. */
int64_t *hsh_struct_new(int64_t n); /* defined in the struct helpers section below */
static int64_t *hsh_http_make(int64_t status, const char *body, size_t blen) {
    char *b = (char*)hsh_alloc(blen + 1);
    memcpy(b, body, blen);
    b[blen] = '\0';
    int64_t *r = hsh_struct_new(2);
    r[0] = status;
    r[1] = (int64_t)(uintptr_t)b;
    return r;
}
static int64_t *hsh_http_fail(const char *msg) { return hsh_http_make(0, msg, strlen(msg)); }

int64_t *hsh_http_request(hsh_string method, hsh_string url, hsh_string body) {
    if (!method || !method[0]) method = "GET";
    if (!url) url = "";
    if (!body) body = "";
    const char *rest = url;
    if (strncmp(url, "http://", 7) == 0) rest = url + 7;
    else if (strncmp(url, "https://", 8) == 0)
        return hsh_http_fail("https:// is not supported — this runtime has no TLS backend, use http:// or a reverse proxy");

    const char *slash = strchr(rest, '/');
    size_t hp_len = slash ? (size_t)(slash - rest) : strlen(rest);
    const char *path = slash ? slash : "/";
    char host_port[300];
    if (hp_len == 0 || hp_len >= sizeof(host_port)) return hsh_http_fail("DNS resolution failed");
    memcpy(host_port, rest, hp_len);
    host_port[hp_len] = '\0';

    char host[300], port[16] = "80";
    strcpy(host, host_port);
    char *colon = strrchr(host, ':');
    if (colon && strchr(host, ']') == NULL) {
        *colon = '\0';
        long p = strtol(colon + 1, NULL, 10);
        if (p > 0 && p < 65536) snprintf(port, sizeof(port), "%ld", p);
    }

    struct addrinfo hints, *res = NULL;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(host, port, &hints, &res) != 0 || !res) return hsh_http_fail("DNS resolution failed");

    int fd = -1;
    int saved_errno = 0;
    for (struct addrinfo *ai = res; ai; ai = ai->ai_next) {
        fd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
        if (fd < 0) { saved_errno = errno; continue; }
        int fl = fcntl(fd, F_GETFL, 0);
        fcntl(fd, F_SETFL, fl | O_NONBLOCK);
        int rc = connect(fd, ai->ai_addr, ai->ai_addrlen);
        if (rc < 0 && errno == EINPROGRESS) {
            struct pollfd pfd = { fd, POLLOUT, 0 };
            if (poll(&pfd, 1, 10000) == 1) {
                int err = 0; socklen_t el = sizeof(err);
                getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &el);
                if (err == 0) rc = 0; else errno = err;
            } else errno = ETIMEDOUT;
        }
        if (rc == 0) { fcntl(fd, F_SETFL, fl); break; }
        saved_errno = errno;
        close(fd); fd = -1;
    }
    freeaddrinfo(res);
    if (fd < 0) {
        char msg[200];
        snprintf(msg, sizeof(msg), "connection failed: %s", strerror(saved_errno));
        return hsh_http_fail(msg);
    }
    struct timeval tv = { 10, 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    size_t blen = strlen(body);
    size_t cap = strlen(method) + strlen(path) + strlen(host_port) + blen + 160;
    char *req = (char*)malloc(cap);
    if (!req) { close(fd); return hsh_http_fail("out of memory"); }
    int hl;
    if (blen == 0)
        hl = snprintf(req, cap, "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\nUser-Agent: hsharp\r\n\r\n", method, path, host);
    else
        hl = snprintf(req, cap, "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\nUser-Agent: hsharp\r\nContent-Length: %zu\r\n\r\n", method, path, host, blen);
    size_t total = (size_t)hl;
    if (blen) { memcpy(req + total, body, blen); total += blen; }
    size_t sent = 0;
    while (sent < total) {
        ssize_t w = send(fd, req + sent, total - sent, MSG_NOSIGNAL);
        if (w < 0) {
            if (errno == EINTR) continue;
            char msg[200]; snprintf(msg, sizeof(msg), "write failed: %s", strerror(errno));
            free(req); close(fd); return hsh_http_fail(msg);
        }
        sent += (size_t)w;
    }
    free(req);

    size_t rcap = 8192, rlen = 0;
    char *raw = (char*)malloc(rcap);
    if (!raw) { close(fd); return hsh_http_fail("out of memory"); }
    for (;;) {
        if (rlen + 4096 + 1 > rcap) {
            rcap *= 2;
            char *nr = (char*)realloc(raw, rcap);
            if (!nr) { free(raw); close(fd); return hsh_http_fail("out of memory"); }
            raw = nr;
        }
        ssize_t n = recv(fd, raw + rlen, 4096, 0);
        if (n < 0) {
            if (errno == EINTR) continue;
            char msg[200]; snprintf(msg, sizeof(msg), "read failed: %s", strerror(errno));
            free(raw); close(fd); return hsh_http_fail(msg);
        }
        if (n == 0) break;
        rlen += (size_t)n;
    }
    close(fd);
    raw[rlen] = '\0';

    int64_t status = 0;
    char *sp1 = strchr(raw, ' ');
    if (sp1 && strncmp(raw, "HTTP/", 5) == 0) status = (int64_t)strtoll(sp1 + 1, NULL, 10);
    char *sep = strstr(raw, "\r\n\r\n");
    int64_t *r;
    if (sep) r = hsh_http_make(status, sep + 4, rlen - (size_t)(sep + 4 - raw));
    else     r = hsh_http_make(status, "", 0);
    free(raw);
    return r;
}

int64_t hsh_getpid(void) { return (int64_t)getpid(); }

/* hsh_proc_id — backs the bare `proc_id()` builtin (codegen.rs's "proc_id"
 * dispatch arm / builtins.rs's `hsh_proc_id` extern). This was declared and
 * called on the compiler side but never given a runtime implementation, so
 * any H# program that called proc_id() failed at link time with an
 * "undefined reference to `hsh_proc_id`" error. Same value as hsh_getpid()
 * (the current process's PID) — kept as a separate symbol rather than
 * aliased so os::pid and the bare proc_id() builtin stay independently
 * resolvable/overridable. */
int64_t hsh_proc_id(void) { return (int64_t)getpid(); }

hsh_string hsh_getenv(hsh_string key) {
    if (!key) return "";
    const char* v = getenv(key);
    return v ? v : "";
}

/* os::username — $USER/$LOGNAME first (works even under contexts where
 * getpwuid's NSS lookup might not, e.g. some minimal containers), falls
 * back to the real passwd-database lookup. */
hsh_string hsh_username(void) {
    const char* v = getenv("USER");
    if (v && v[0]) return v;
    v = getenv("LOGNAME");
    if (v && v[0]) return v;
    struct passwd* pw = getpwuid(getuid());
    return (pw && pw->pw_name) ? pw->pw_name : "";
}

/* os::platform — matches Rust's std::env::consts::OS naming
 * ("linux"/"macos"/"windows") since that's the most common convention
 * an H# programmer coming from Rust would expect. */
hsh_string hsh_platform(void) {
#if defined(__APPLE__)
    return "macos";
#elif defined(_WIN32)
    return "windows";
#elif defined(__linux__)
    return "linux";
#else
    return "unknown";
#endif
}

/* ── sys:: — native machine/process introspection (native AOT support) ───────
 * EXPANSION: every one of these was `Backend::Interpreter`-only before —
 * the interpreter reads `/proc` files directly for the Linux-specific ones
 * and shells out to `id`/`ps`/`getconf`/`uname`/`df` for the rest (see
 * `hsharp-interpreter::call.rs`'s own `sys_*` arms, which this section
 * mirrors for exact behavioral parity: same `/proc` files, same parsing,
 * same fallback-to-0/1/"unknown" on failure — nothing here should ever
 * observably disagree with what the interpreter already returns).
 * Where native libc/syscalls give the *exact* same value more directly
 * than shelling out to an external binary would (`getuid()` instead of
 * spawning `id -u`, `sysconf(_SC_PAGE_SIZE)` instead of spawning
 * `getconf PAGESIZE`, `uname()`/`statvfs()` instead of `uname`/`df`),
 * this uses the syscall — same observable result, no subprocess, no
 * dependency on those binaries existing in `$PATH`. Every function here
 * is a read-only query with no meaningful failure mode worth surfacing
 * to H# code (a shell prompt segment reading "0% used" because
 * `/proc/meminfo` was unreadable in some exotic container is a far
 * better failure than crashing the whole shell), so — again matching
 * the interpreter — everything degrades to a sane default rather than
 * erroring. */

/* sys::cpu_count — number of "processor" lines in /proc/cpuinfo,
 * minimum 1 (matches the interpreter's own `.max(1)` — a shell prompt
 * dividing by this should never divide by zero even on some unusual
 * system where the parse comes back empty). */
int64_t hsh_sys_cpu_count(void) {
    FILE* f = fopen("/proc/cpuinfo", "r");
    if (!f) return 1;
    int64_t n = 0;
    char line[256];
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, "processor", 9) == 0) n++;
    }
    fclose(f);
    return n > 0 ? n : 1;
}

/* sys::memory_total / sys::memory_free — parses /proc/meminfo's
 * "MemTotal:"/"MemAvailable:" lines (kB), returns bytes. `MemAvailable`
 * (not `MemFree`) matches the interpreter's own choice — it's the
 * kernel's own "actually available for a new process, including
 * reclaimable cache" estimate, which is what a human reading "free
 * memory" on a shell prompt actually wants, not the much smaller raw
 * `MemFree`. */
static int64_t hsh_sys_meminfo_kb(const char* key) {
    FILE* f = fopen("/proc/meminfo", "r");
    if (!f) return 0;
    size_t klen = strlen(key);
    char line[256];
    int64_t kb = 0;
    while (fgets(line, sizeof(line), f)) {
        if (strncmp(line, key, klen) == 0) {
            kb = strtoll(line + klen, NULL, 10);
            break;
        }
    }
    fclose(f);
    return kb;
}
int64_t hsh_sys_memory_total(void) { return hsh_sys_meminfo_kb("MemTotal:") * 1024; }
int64_t hsh_sys_memory_free(void)  { return hsh_sys_meminfo_kb("MemAvailable:") * 1024; }

/* sys::uptime — whole seconds since boot, from /proc/uptime's first field. */
int64_t hsh_sys_uptime(void) {
    FILE* f = fopen("/proc/uptime", "r");
    if (!f) return 0;
    double secs = 0.0;
    if (fscanf(f, "%lf", &secs) != 1) secs = 0.0;
    fclose(f);
    return (int64_t)secs;
}

/* sys::load_avg — 1-minute load average, from /proc/loadavg's first field. */
double hsh_sys_load_avg(void) {
    FILE* f = fopen("/proc/loadavg", "r");
    if (!f) return 0.0;
    double load = 0.0;
    if (fscanf(f, "%lf", &load) != 1) load = 0.0;
    fclose(f);
    return load;
}

/* sys::disk_total / sys::disk_free — statvfs() on the filesystem
 * containing `path`, in bytes. `disk_free` uses `f_bavail` (blocks
 * available to an unprivileged user), matching `df`'s own "Available"
 * column (not `f_bfree`, which also counts blocks reserved for root —
 * `df -k`'s 4th column is `f_bavail`-based, and the interpreter's own
 * `sys_disk_free` reads exactly that column, so this matches it). Falls
 * back to `/` if `path` can't be resolved (statvfs fails) — same
 * fallback shape as the interpreter's own "column not found -> 0"; 0
 * bytes total/free is a safer default for a broken/missing path than
 * an error that could crash a shell prompt render. */
int64_t hsh_sys_disk_total(hsh_string path) {
    struct statvfs sv;
    if (statvfs((path && path[0]) ? path : "/", &sv) != 0) return 0;
    return (int64_t)sv.f_blocks * (int64_t)sv.f_frsize;
}
int64_t hsh_sys_disk_free(hsh_string path) {
    struct statvfs sv;
    if (statvfs((path && path[0]) ? path : "/", &sv) != 0) return 0;
    return (int64_t)sv.f_bavail * (int64_t)sv.f_frsize;
}

/* sys::page_size — sysconf(_SC_PAGE_SIZE), exactly what `getconf
 * PAGESIZE` prints, without spawning it. 4096 fallback matches the
 * interpreter's own default for the (essentially never happens on a
 * real system) case sysconf itself fails. */
int64_t hsh_sys_page_size(void) {
    long sz = sysconf(_SC_PAGE_SIZE);
    return sz > 0 ? (int64_t)sz : 4096;
}

/* sys::get_uid / sys::get_gid / sys::get_ppid — direct syscalls,
 * exactly what `id -u`/`id -g`/`ps -o ppid=` print without spawning
 * them. */
int64_t hsh_sys_get_uid(void)  { return (int64_t)getuid(); }
int64_t hsh_sys_get_gid(void)  { return (int64_t)getgid(); }
int64_t hsh_sys_get_ppid(void) { return (int64_t)getppid(); }

/* sys::is_64bit / sys::is_little_endian — compile-time-constant checks
 * on the actual pointer width and byte order this binary was compiled
 * for, matching the interpreter's own `size_of::<usize>() == 8`/
 * `cfg!(target_endian = "little")` (both properties of the *running*
 * program, not something that could differ between backends on the
 * same machine). */
int64_t hsh_sys_is_64bit(void) { return sizeof(void*) == 8 ? 1 : 0; }
int64_t hsh_sys_is_little_endian(void) {
    const uint16_t probe = 1;
    return (*(const unsigned char*)&probe == 1) ? 1 : 0;
}

/* sys::sysname / sys::machine / sys::kernel_version — uname(2), exactly
 * what `uname -s`/`uname -m`/`uname -r` print without spawning them. */
static hsh_string hsh_sys_uname_field(int which) {
    struct utsname u;
    if (uname(&u) != 0) return "";
    const char* src = (which == 0) ? u.sysname : (which == 1) ? u.machine : u.release;
    size_t n = strlen(src);
    char* out = (char*)hsh_alloc(n + 1);
    if (!out) return "";
    memcpy(out, src, n + 1);
    return out;
}
hsh_string hsh_sys_sysname(void)        { return hsh_sys_uname_field(0); }
hsh_string hsh_sys_machine(void)        { return hsh_sys_uname_field(1); }
hsh_string hsh_sys_kernel_version(void) { return hsh_sys_uname_field(2); }

/* env::set(name, value) — setenv() wrapper; affects this process (and
 * anything it later shell()s/run_cmd()s) only, same scope as every
 * other language's env::set. */
int64_t hsh_setenv(hsh_string name, hsh_string value) {
    if (!name) return 0;
    return (setenv(name, value ? value : "", 1) == 0) ? 1 : 0;
}

/* encoding::base64 (standard alphabet, with '=' padding — matches every
 * other language's default base64 codec, so output round-trips through
 * `base64`/`openssl base64` on the command line without a --url-safe
 * flag). */
static const char HSH_B64_CHARS[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

hsh_string hsh_base64_encode(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    size_t out_len = ((n + 2) / 3) * 4;
    char* out = (char*)hsh_alloc(out_len + 1);
    size_t i = 0, w = 0;
    while (i + 2 < n) {
        uint32_t v = ((unsigned char)s[i] << 16) | ((unsigned char)s[i+1] << 8) | (unsigned char)s[i+2];
        out[w++] = HSH_B64_CHARS[(v >> 18) & 0x3F];
        out[w++] = HSH_B64_CHARS[(v >> 12) & 0x3F];
        out[w++] = HSH_B64_CHARS[(v >> 6) & 0x3F];
        out[w++] = HSH_B64_CHARS[v & 0x3F];
        i += 3;
    }
    size_t rem = n - i;
    if (rem == 1) {
        uint32_t v = (unsigned char)s[i] << 16;
        out[w++] = HSH_B64_CHARS[(v >> 18) & 0x3F];
        out[w++] = HSH_B64_CHARS[(v >> 12) & 0x3F];
        out[w++] = '='; out[w++] = '=';
    } else if (rem == 2) {
        uint32_t v = ((unsigned char)s[i] << 16) | ((unsigned char)s[i+1] << 8);
        out[w++] = HSH_B64_CHARS[(v >> 18) & 0x3F];
        out[w++] = HSH_B64_CHARS[(v >> 12) & 0x3F];
        out[w++] = HSH_B64_CHARS[(v >> 6) & 0x3F];
        out[w++] = '=';
    }
    out[w] = '\0';
    return out;
}

static int hsh_b64_val(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1; /* padding or invalid — treated as end of data */
}

hsh_string hsh_base64_decode(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    char* out = (char*)hsh_alloc(n + 1); /* decoded is always <= input length */
    size_t w = 0;
    int buf[4]; int bn = 0;
    for (size_t i = 0; i < n; i++) {
        int v = hsh_b64_val(s[i]);
        if (v < 0) continue; /* skip padding/whitespace/invalid chars */
        buf[bn++] = v;
        if (bn == 4) {
            out[w++] = (char)((buf[0] << 2) | (buf[1] >> 4));
            out[w++] = (char)(((buf[1] & 0xF) << 4) | (buf[2] >> 2));
            out[w++] = (char)(((buf[2] & 0x3) << 6) | buf[3]);
            bn = 0;
        }
    }
    if (bn == 2) {
        out[w++] = (char)((buf[0] << 2) | (buf[1] >> 4));
    } else if (bn == 3) {
        out[w++] = (char)((buf[0] << 2) | (buf[1] >> 4));
        out[w++] = (char)(((buf[1] & 0xF) << 4) | (buf[2] >> 2));
    }
    out[w] = '\0';
    return out;
}

/* encoding::url — percent-encoding. `hsh_url_encode` leaves the
 * standard "unreserved" RFC 3986 characters (letters, digits, -_.~)
 * untouched and percent-encodes everything else, matching every
 * mainstream language's default `encodeURIComponent`-style behavior
 * (space becomes %20, not '+' — the older application/x-www-form-
 * urlencoded convention is deliberately not what this implements,
 * since URL paths and query values are the far more common use case). */
static int hsh_url_safe_char(unsigned char c) {
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
        || c == '-' || c == '_' || c == '.' || c == '~';
}

hsh_string hsh_url_encode(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    char* out = (char*)hsh_alloc(n * 3 + 1);
    size_t w = 0;
    static const char hexd[] = "0123456789ABCDEF";
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        if (hsh_url_safe_char(c)) {
            out[w++] = (char)c;
        } else {
            out[w++] = '%';
            out[w++] = hexd[(c >> 4) & 0xF];
            out[w++] = hexd[c & 0xF];
        }
    }
    out[w] = '\0';
    return out;
}

static int hsh_hex_val(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

hsh_string hsh_url_decode(hsh_string s) {
    if (!s) return "";
    size_t n = strlen(s);
    char* out = (char*)hsh_alloc(n + 1);
    size_t w = 0;
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '%' && i + 2 < n) {
            int hi = hsh_hex_val(s[i+1]), lo = hsh_hex_val(s[i+2]);
            if (hi >= 0 && lo >= 0) {
                out[w++] = (char)((hi << 4) | lo);
                i += 2;
                continue;
            }
        }
        out[w++] = (s[i] == '+') ? ' ' : s[i];
    }
    out[w] = '\0';
    return out;
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

/* [ADDED] `db_query_bind`'s C implementation. The H# std module
 * (std/db.h#) and the compiler's own builtin registry both already
 * declared this as an LLVM-backed builtin (`hsh_sqlite_query_bind1/2/3`,
 * dispatched by arity — see codegen.rs's "db_query_bind" match arm) but
 * no C definition existed anywhere in this runtime: a real gap, not a
 * naming mismatch like most of the other "interpreter only" builtins
 * turned out to be. `std/db.h#`'s doc comment for `query_params` et al.
 * promises SQL-injection safety "via sqlite3_bind_text" — true
 * prepared-statement binding against libsqlite3 directly — but linking
 * a new C library dependency into every H# binary isn't something this
 * change takes on. Instead, `?` placeholders are substituted with
 * properly SQL-escaped (quote-doubled) string literals and handed to
 * the real `sqlite3` CLI via `hsh_exec_argv` above — no shell, so no
 * shell-injection surface, and every value is always quoted, so no
 * SQL-injection surface either, just not via the exact binding
 * mechanism the doc comment describes. A real libsqlite3 FFI link
 * remains the natural follow-up if this project ever needs it.
 *
 * Rows come back one per line, columns tab-separated (`sqlite3
 * -separator '\t'`), matching what `std/db.h#`'s "array of maps" query
 * result would need a caller to split apart manually on this backend
 * (there is no separate row/column decoder builtin here — see hco's
 * db.h# for the parsing side of this contract). */

/* Escapes a value for embedding as an SQL string literal: wraps it in
 * single quotes, doubling any embedded single quote (the standard SQL
 * escaping rule). This is SQL escaping, not shell escaping — the
 * result is never interpreted by a shell (hsh_exec_argv execvp's
 * `sqlite3` directly), only by sqlite3's own SQL parser. */
static char* hsh_sql_escape(const char* s) {
    if (!s) return strdup("''");
    size_t n = strlen(s);
    char* out = (char*)malloc(n * 2 + 3);
    if (!out) return strdup("''");
    size_t w = 0;
    out[w++] = '\'';
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '\'') { out[w++] = '\''; out[w++] = '\''; }
        else out[w++] = s[i];
    }
    out[w++] = '\'';
    out[w] = '\0';
    return out;
}

/* Substitutes each `?` in `sql` (in source order) with the
 * corresponding already-SQL-escaped bind value. A `?` beyond
 * `n_binds` is left as literal text — sqlite3 itself will then report
 * a normal "?" syntax error for it, the same way a real prepared
 * statement would reject a missing binding, rather than this silently
 * guessing. */
static char* hsh_sql_bind(const char* sql, char** escaped_binds, int n_binds) {
    size_t cap = strlen(sql) + 1;
    for (int i = 0; i < n_binds; i++) cap += strlen(escaped_binds[i]);
    char* out = (char*)malloc(cap);
    if (!out) return strdup(sql);
    size_t w = 0;
    int bi = 0;
    for (const char* p = sql; *p; p++) {
        if (*p == '?' && bi < n_binds) {
            size_t elen = strlen(escaped_binds[bi]);
            memcpy(out + w, escaped_binds[bi], elen);
            w += elen;
            bi++;
        } else {
            out[w++] = *p;
        }
    }
    out[w] = '\0';
    return out;
}

/* Runs `sqlite3 -separator '<tab>' <db> <bound_sql>` via the existing
 * fork+execvp helper above (no shell involved at all) and returns its
 * combined stdout/stderr, exactly like `hsh_shell`/`hsh_exec_argv`
 * already do for every other shelled-out builtin in this runtime. */
static hsh_string hsh_sqlite_query_bind_n(hsh_string db, hsh_string sql, hsh_string* binds, int n_binds) {
    if (!db || !sql) return "";
    char* escaped[3];
    for (int i = 0; i < n_binds; i++) escaped[i] = hsh_sql_escape(binds[i]);
    char* bound_sql = hsh_sql_bind(sql, escaped, n_binds);
    for (int i = 0; i < n_binds; i++) free(escaped[i]);

    char* argv[6];
    argv[0] = (char*)"sqlite3";
    argv[1] = (char*)"-separator";
    argv[2] = (char*)"\t";
    argv[3] = (char*)db;
    argv[4] = bound_sql;
    argv[5] = NULL;
    hsh_string result = hsh_exec_argv(argv);
    free(bound_sql);
    return result;
}

hsh_string hsh_sqlite_query_bind1(hsh_string db, hsh_string sql, hsh_string b1) {
    hsh_string binds[1] = { b1 };
    /* An absent bind arg arrives here as "" (see codegen.rs's str_arg!
     * macro), which would otherwise consume the first "?" with an
     * empty-string literal instead of leaving it for sqlite3 to report
     * — only treat it as a real bind value if the caller actually
     * passed something non-empty via a 3-arg `db_query_bind` call. */
    int n = (b1 && b1[0] != '\0') ? 1 : 0;
    return hsh_sqlite_query_bind_n(db, sql, binds, n);
}

hsh_string hsh_sqlite_query_bind2(hsh_string db, hsh_string sql, hsh_string b1, hsh_string b2) {
    hsh_string binds[2] = { b1, b2 };
    return hsh_sqlite_query_bind_n(db, sql, binds, 2);
}

hsh_string hsh_sqlite_query_bind3(hsh_string db, hsh_string sql, hsh_string b1, hsh_string b2, hsh_string b3) {
    hsh_string binds[3] = { b1, b2, b3 };
    return hsh_sqlite_query_bind_n(db, sql, binds, 3);
}

/* Read every byte currently available from `fd` into a heap buffer
 * (non-blocking use: caller only calls this once the child is known to
 * have exited or been killed, so a plain blocking read-to-EOF is fine —
 * same pattern as hsh_shell/hsh_exec_argv above). */
static char* hsh_drain_fd(int fd) {
    char* buf = NULL; size_t total = 0, cap = 0; char chunk[4096]; ssize_t n;
    while ((n = read(fd, chunk, sizeof(chunk))) > 0) {
        if (total + (size_t)n + 1 > cap) {
            cap = (cap + (size_t)n + 1) * 2;
            char* nb = (char*)realloc(buf, cap);
            if (!nb) { free(buf); return strdup(""); }
            buf = nb;
        }
        memcpy(buf + total, chunk, (size_t)n); total += (size_t)n;
    }
    if (!buf) return strdup("");
    buf[total] = '\0';
    return buf;
}

/* ══════════════════════════════════════════════════════════════════════════
 * db:: (std -> db) on the AOT / LLVM backend.
 *
 * Until now `__builtin_db_*` was "interpreter only": codegen.rs already had
 * `sqlite_open/exec/query/close` arms and builtins.rs already declared the
 * `hsh_sqlite_*` symbols, but no C definition existed for them (sqlite.c was
 * removed) and `emit_binary_with_machine` bailed out early on any program
 * that touched `db ->`.  This section is the missing native bridge.
 *
 * Same philosophy as regex:: and `hsh_sqlite_query_bind*` above: no new C
 * library dependency, the real `sqlite3` CLI is driven through fork+execvp
 * (no shell => no shell injection).  SQL is fed through a temp file on the
 * child's stdin (no ARG_MAX limit, no pipe deadlock on large statements).
 *
 * Contract (mirrors the interpreter where it has one):
 *   open(path|uri)   -> handle string "sqlite://<path>"
 *   exec(h, sql)     -> rows changed (int), -1 on error (message on stderr)
 *   query(h, sql)    -> [[string]]  one inner array per row, columns split on TAB
 *   begin(h)         -> tx handle "sqlite-tx://<n>"
 *       exec(tx, sql) only BUFFERS the statement; commit(tx) runs the whole
 *       buffer as ONE `BEGIN; ... COMMIT;` script (atomic); rollback(tx) drops it.
 *       query(tx, sql) runs buffer + query inside BEGIN..ROLLBACK (read-your-writes).
 *   exec_params / query_params: every `?` outside a quoted literal is replaced
 *       by a properly escaped literal (strings quoted, ints bare).
 *   col_*(row, col)  -> `col` is a column NAME (resolved against the header of
 *       the most recent query) or a decimal INDEX ("0", "1", ...).
 *       NULL comes back from the sqlite3 CLI as an empty string, so
 *       col_is_null is true for NULL and for "" alike.
 * ══════════════════════════════════════════════════════════════════════════ */

#define HSH_DB_PREFIX    "sqlite://"
#define HSH_DB_TX_PREFIX "sqlite-tx://"
#define HSH_DB_MAX_TX    64

typedef struct { int used; char* path; char* buf; size_t len, cap; } HshDbTx;
static HshDbTx g_hsh_db_tx[HSH_DB_MAX_TX];
static char**  g_hsh_db_cols  = NULL;   /* header of the last query */
static int     g_hsh_db_ncols = 0;

static char* hsh_db_dup(const char* s, size_t n) {
    char* o = (char*)hsh_alloc((uint64_t)n + 1);
    if (!o) return (char*)"";
    memcpy(o, s, n); o[n] = '\0';
    return o;
}

static int hsh_db_is_tx(const char* h) {
    return h && strncmp(h, HSH_DB_TX_PREFIX, strlen(HSH_DB_TX_PREFIX)) == 0;
}

static HshDbTx* hsh_db_tx_get(const char* h) {
    if (!hsh_db_is_tx(h)) return NULL;
    long i = strtol(h + strlen(HSH_DB_TX_PREFIX), NULL, 10);
    if (i < 0 || i >= HSH_DB_MAX_TX || !g_hsh_db_tx[i].used) return NULL;
    return &g_hsh_db_tx[i];
}

static const char* hsh_db_path_of(const char* h) {
    if (!h) return "";
    HshDbTx* t = hsh_db_tx_get(h);
    if (t) return t->path;
    if (strncmp(h, HSH_DB_PREFIX, strlen(HSH_DB_PREFIX)) == 0) return h + strlen(HSH_DB_PREFIX);
    return h;
}

static void hsh_db_tx_append(HshDbTx* t, const char* sql) {
    size_t n = strlen(sql);
    size_t add = n + 3; /* sql + "\n;\n" */
    if (t->len + add + 1 > t->cap) {
        size_t nc = (t->cap + add + 1) * 2;
        char* nb = (char*)realloc(t->buf, nc);
        if (!nb) return;
        t->buf = nb; t->cap = nc;
    }
    memcpy(t->buf + t->len, sql, n); t->len += n;
    t->buf[t->len++] = '\n';
    t->buf[t->len++] = ';';
    t->buf[t->len++] = '\n';
    t->buf[t->len] = '\0';
}

/* Runs `sqlite3` on `path`, SQL on stdin (temp file). Returns exit status
 * (0 = ok, -1 = could not start). *out receives stdout (malloc'd), *err stderr. */
static int hsh_db_run(const char* path, const char* sql, int header, char** out, char** err) {
    *out = NULL; *err = NULL;
    const char* tmpd = getenv("TMPDIR");
    if (!tmpd || !*tmpd) tmpd = "/tmp";
    char in_t[4096], err_t[4096];
    snprintf(in_t,  sizeof(in_t),  "%s/hshdbinXXXXXX",  tmpd);
    snprintf(err_t, sizeof(err_t), "%s/hshdberrXXXXXX", tmpd);
    int in_fd = mkstemp(in_t);
    if (in_fd < 0) return -1;
    int err_fd = mkstemp(err_t);
    if (err_fd < 0) { close(in_fd); unlink(in_t); return -1; }
    size_t sl = strlen(sql), done = 0;
    while (done < sl) {
        ssize_t w = write(in_fd, sql + done, sl - done);
        if (w <= 0) break;
        done += (size_t)w;
    }
    lseek(in_fd, 0, SEEK_SET);
    int pipefd[2];
    if (done != sl || pipe(pipefd) != 0) {
        close(in_fd); close(err_fd); unlink(in_t); unlink(err_t); return -1;
    }
    pid_t pid = fork();
    if (pid < 0) {
        close(pipefd[0]); close(pipefd[1]); close(in_fd); close(err_fd);
        unlink(in_t); unlink(err_t); return -1;
    }
    if (pid == 0) {
        dup2(in_fd, STDIN_FILENO);
        dup2(pipefd[1], STDOUT_FILENO);
        dup2(err_fd, STDERR_FILENO);
        close(pipefd[0]); close(pipefd[1]); close(in_fd); close(err_fd);
        char* argv[12]; int k = 0;
        argv[k++] = (char*)"sqlite3";
        argv[k++] = (char*)"-batch";
        argv[k++] = (char*)"-bail";
        if (header) argv[k++] = (char*)"-header";
        argv[k++] = (char*)"-separator";
        argv[k++] = (char*)"\t";
        argv[k++] = (char*)"-cmd";
        argv[k++] = (char*)".timeout 5000";
        argv[k++] = (char*)path;
        argv[k] = NULL;
        execvp("sqlite3", argv);
        _exit(127);
    }
    close(pipefd[1]); close(in_fd);
    *out = hsh_drain_fd(pipefd[0]);
    close(pipefd[0]);
    int status = 0;
    waitpid(pid, &status, 0);
    lseek(err_fd, 0, SEEK_SET);
    *err = hsh_drain_fd(err_fd);
    close(err_fd);
    unlink(in_t); unlink(err_t);
    if (WIFEXITED(status)) {
        int c = WEXITSTATUS(status);
        if (c == 127) {
            free(*err);
            *err = strdup("sqlite3 binary not found in PATH (install the `sqlite3` package)");
        }
        return c;
    }
    return -1;
}

static void hsh_db_report(int rc, const char* err) {
    if (rc == 0) return;
    fprintf(stderr, "db error: %s\n", (err && *err) ? err : "sqlite3 failed");
}

static char* hsh_db_cat3(const char* a, const char* b, const char* c) {
    size_t la = strlen(a), lb = strlen(b), lc = strlen(c);
    char* o = (char*)malloc(la + lb + lc + 1);
    if (!o) return NULL;
    memcpy(o, a, la); memcpy(o + la, b, lb); memcpy(o + la + lb, c, lc);
    o[la + lb + lc] = '\0';
    return o;
}

hsh_string hsh_sqlite_open(hsh_string uri) {
    const char* p = uri ? uri : "./db.sqlite";
    if (strncmp(p, HSH_DB_PREFIX, strlen(HSH_DB_PREFIX)) == 0) p += strlen(HSH_DB_PREFIX);
    size_t n = strlen(HSH_DB_PREFIX) + strlen(p);
    char* o = (char*)hsh_alloc((uint64_t)n + 1);
    if (!o) return "";
    snprintf(o, n + 1, "%s%s", HSH_DB_PREFIX, p);
    return o;
}

int64_t hsh_sqlite_exec(hsh_string h, hsh_string sql) {
    if (!h || !sql) return -1;
    HshDbTx* t = hsh_db_tx_get(h);
    if (t) { hsh_db_tx_append(t, sql); return 0; }
    size_t n = strlen(sql);
    /* "\n;" (not just ";") so a trailing `-- comment` can't swallow what follows */
    (void)n;
    char* full = hsh_db_cat3(sql, "\n;\n", "SELECT changes();\n");
    if (!full) return -1;
    char *out, *err;
    int rc = hsh_db_run(hsh_db_path_of(h), full, 0, &out, &err);
    free(full);
    int64_t changed = -1;
    if (rc == 0 && out) {
        size_t ol = strlen(out);
        while (ol > 0 && (out[ol - 1] == '\n' || out[ol - 1] == '\r')) out[--ol] = '\0';
        const char* last = strrchr(out, '\n');
        last = last ? last + 1 : out;
        changed = (int64_t)strtoll(last, NULL, 10);
    } else {
        hsh_db_report(rc, err);
    }
    free(out); free(err);
    return changed;
}

static void hsh_db_set_header(char* line) {
    for (int i = 0; i < g_hsh_db_ncols; i++) free(g_hsh_db_cols[i]);
    free(g_hsh_db_cols);
    g_hsh_db_cols = NULL; g_hsh_db_ncols = 0;
    int cnt = 1;
    for (char* p = line; *p; p++) if (*p == '\t') cnt++;
    g_hsh_db_cols = (char**)calloc((size_t)cnt, sizeof(char*));
    if (!g_hsh_db_cols) return;
    char* start = line;
    for (char* p = line;; p++) {
        if (*p == '\t' || *p == '\0') {
            g_hsh_db_cols[g_hsh_db_ncols++] = strndup(start, (size_t)(p - start));
            if (*p == '\0') break;
            start = p + 1;
        }
    }
}

static HshArray* hsh_db_parse_rows(char* out) {
    HshArray* rows = hsh_array_new();
    if (!out) return rows;
    int first = 1;
    char* line = out;
    while (line && *line) {
        char* nl = strchr(line, '\n');
        if (nl) *nl = '\0';
        size_t ll = strlen(line);
        if (ll && line[ll - 1] == '\r') line[ll - 1] = '\0';
        if (first) { hsh_db_set_header(line); first = 0; }
        else if (*line) {
            HshArray* row = hsh_array_new();
            char* s = line;
            for (char* p = line;; p++) {
                if (*p == '\t' || *p == '\0') {
                    row = hsh_array_push(row, (int64_t)(uintptr_t)hsh_db_dup(s, (size_t)(p - s)));
                    if (*p == '\0') break;
                    s = p + 1;
                }
            }
            rows = hsh_array_push(rows, (int64_t)(uintptr_t)row);
        }
        line = nl ? nl + 1 : NULL;
    }
    return rows;
}

HshArray* hsh_sqlite_query(hsh_string h, hsh_string sql) {
    if (!h || !sql) return hsh_array_new();
    HshDbTx* t = hsh_db_tx_get(h);
    size_t n = strlen(sql);
    (void)n;
    const char* tail = "\n;\n";
    char* full;
    if (t) {
        char* a = hsh_db_cat3("BEGIN;\n", t->buf ? t->buf : "", sql);
        full = a ? hsh_db_cat3(a, tail, "ROLLBACK;\n") : NULL;
        free(a);
    } else {
        full = hsh_db_cat3(sql, tail, "");
    }
    if (!full) return hsh_array_new();
    char *out, *err;
    int rc = hsh_db_run(hsh_db_path_of(h), full, 1, &out, &err);
    free(full);
    HshArray* rows;
    if (rc != 0) { hsh_db_report(rc, err); rows = hsh_array_new(); }
    else rows = hsh_db_parse_rows(out);
    free(out); free(err);
    return rows;
}

void hsh_sqlite_close(hsh_string h) {
    HshDbTx* t = hsh_db_tx_get(h);
    if (t) { free(t->path); free(t->buf); memset(t, 0, sizeof(*t)); }
}

int64_t hsh_sqlite_ping(hsh_string h) {
    if (!h) return 0;
    char *out, *err;
    int rc = hsh_db_run(hsh_db_path_of(h), "SELECT 1;\n", 0, &out, &err);
    int ok = (rc == 0 && out && out[0] == '1');
    free(out); free(err);
    return ok;
}

int64_t hsh_sqlite_begin(hsh_string h) {
    /* returns a handle string, cast to i64 for `any` */
    if (!h || hsh_db_is_tx(h)) return 0;
    for (int i = 0; i < HSH_DB_MAX_TX; i++) {
        if (!g_hsh_db_tx[i].used) {
            g_hsh_db_tx[i].used = 1;
            g_hsh_db_tx[i].path = strdup(hsh_db_path_of(h));
            g_hsh_db_tx[i].buf = NULL; g_hsh_db_tx[i].len = g_hsh_db_tx[i].cap = 0;
            char tmp[64];
            snprintf(tmp, sizeof(tmp), "%s%d", HSH_DB_TX_PREFIX, i);
            return (int64_t)(uintptr_t)hsh_db_dup(tmp, strlen(tmp));
        }
    }
    fprintf(stderr, "db error: too many open transactions\n");
    return 0;
}

int64_t hsh_sqlite_commit(hsh_string h) {
    HshDbTx* t = hsh_db_tx_get(h);
    if (!t) return 0;
    int ok = 1;
    if (t->buf && t->len) {
        char* full = hsh_db_cat3("BEGIN;\n", t->buf, "COMMIT;\n");
        char *out, *err;
        int rc = full ? hsh_db_run(t->path, full, 0, &out, &err) : -1;
        if (full) { hsh_db_report(rc, rc == -1 ? NULL : err); free(out); free(err); }
        free(full);
        ok = (rc == 0);
    }
    free(t->path); free(t->buf); memset(t, 0, sizeof(*t));
    return ok;
}

int64_t hsh_sqlite_rollback(hsh_string h) {
    HshDbTx* t = hsh_db_tx_get(h);
    if (!t) return 0;
    free(t->path); free(t->buf); memset(t, 0, sizeof(*t));
    return 1;
}

/* ?-binding that (unlike the older hsh_sql_bind above) leaves `?` inside
 * quoted literals alone. Ints (the <=0x10000 / >=0x7ffffffffffe magnitude
 * convention hsh_val_to_str already uses) are emitted bare, anything else
 * is treated as a char* and emitted as an escaped literal. */
static char* hsh_db_bind_array(const char* sql, HshArray* params) {
    int64_t np = params ? params->len : 0;
    size_t cap = strlen(sql) + 1;
    char** lit = (char**)calloc((size_t)(np > 0 ? np : 1), sizeof(char*));
    if (!lit) return strdup(sql);
    for (int64_t i = 0; i < np; i++) {
        int64_t v = params->data[i];
        if ((uint64_t)v <= 0x10000ULL || (uint64_t)v >= 0x7ffffffffffeULL) {
            char tmp[32]; snprintf(tmp, sizeof(tmp), "%lld", (long long)v);
            lit[i] = strdup(tmp);
        } else {
            lit[i] = hsh_sql_escape((const char*)(uintptr_t)v);
        }
        cap += lit[i] ? strlen(lit[i]) : 0;
    }
    char* o = (char*)malloc(cap + 1);
    if (!o) { for (int64_t i = 0; i < np; i++) free(lit[i]); free(lit); return strdup(sql); }
    size_t w = 0; int64_t bi = 0; char q = 0;
    for (const char* p = sql; *p; p++) {
        if (q) { o[w++] = *p; if (*p == q) q = 0; }
        else if (*p == '\'' || *p == '"') { q = *p; o[w++] = *p; }
        else if (*p == '?' && bi < np) { size_t l = strlen(lit[bi]); memcpy(o + w, lit[bi], l); w += l; bi++; }
        else o[w++] = *p;
    }
    o[w] = '\0';
    for (int64_t i = 0; i < np; i++) free(lit[i]);
    free(lit);
    return o;
}

int64_t hsh_sqlite_exec_params(hsh_string h, hsh_string sql, HshArray* params) {
    if (!h || !sql) return -1;
    char* bound = hsh_db_bind_array(sql, params);
    int64_t r = hsh_sqlite_exec(h, bound);
    free(bound);
    return r;
}

HshArray* hsh_sqlite_query_params(hsh_string h, hsh_string sql, HshArray* params) {
    if (!h || !sql) return hsh_array_new();
    char* bound = hsh_db_bind_array(sql, params);
    HshArray* r = hsh_sqlite_query(h, bound);
    free(bound);
    return r;
}

static const char* hsh_db_cell(HshArray* row, hsh_string col) {
    if (!row || !col) return "";
    int64_t idx = -1;
    int digits = (*col != '\0');
    for (const char* p = col; *p; p++) if (*p < '0' || *p > '9') { digits = 0; break; }
    if (digits) idx = (int64_t)strtoll(col, NULL, 10);
    else for (int i = 0; i < g_hsh_db_ncols; i++)
        if (g_hsh_db_cols[i] && strcmp(g_hsh_db_cols[i], col) == 0) { idx = i; break; }
    if (idx < 0 || idx >= row->len) return "";
    const char* v = (const char*)(uintptr_t)row->data[idx];
    return v ? v : "";
}

hsh_string hsh_db_col_str(HshArray* row, hsh_string col)  { return hsh_db_cell(row, col); }
int64_t    hsh_db_col_int(HshArray* row, hsh_string col)  { return (int64_t)strtoll(hsh_db_cell(row, col), NULL, 10); }
double     hsh_db_col_float(HshArray* row, hsh_string col){ return strtod(hsh_db_cell(row, col), NULL); }
int64_t    hsh_db_col_bool(HshArray* row, hsh_string col) {
    const char* v = hsh_db_cell(row, col);
    return (strcmp(v, "1") == 0 || strcasecmp(v, "true") == 0 || strcasecmp(v, "t") == 0);
}
int64_t    hsh_db_col_is_null(HshArray* row, hsh_string col) { return hsh_db_cell(row, col)[0] == '\0'; }


/* ══════════════════════════════════════════════════════════════════════════
 * crypto:: / path:: / os:: / sort:: native implementations for the AOT backend.
 *
 * These `std -> crypto/path/os/sort` builtins used to be "interpreter only":
 * every program importing those std modules failed to compile with
 * "`__builtin_crypto_sha256` is not supported by the h# (LLVM) backend".
 * Pure C, no new library dependencies. Digests/KDFs were verified bit-for-bit
 * against Python hashlib / blake3 / argon2-cffi (SHA-1/256/512, MD5, HMAC,
 * PBKDF2-HMAC-SHA256, BLAKE3 incl. multi-chunk trees, Argon2id incl. multi-lane).
 * `bytes` in this runtime is an HshArray* of byte values (see hsh_fs_read_bytes).
 * ══════════════════════════════════════════════════════════════════════════ */
static const uint32_t hsh_sha256_k[64] = {
    0x428a2f98u,
    0x71374491u,
    0xb5c0fbcfu,
    0xe9b5dba5u,
    0x3956c25bu,
    0x59f111f1u,
    0x923f82a4u,
    0xab1c5ed5u,
    0xd807aa98u,
    0x12835b01u,
    0x243185beu,
    0x550c7dc3u,
    0x72be5d74u,
    0x80deb1feu,
    0x9bdc06a7u,
    0xc19bf174u,
    0xe49b69c1u,
    0xefbe4786u,
    0x0fc19dc6u,
    0x240ca1ccu,
    0x2de92c6fu,
    0x4a7484aau,
    0x5cb0a9dcu,
    0x76f988dau,
    0x983e5152u,
    0xa831c66du,
    0xb00327c8u,
    0xbf597fc7u,
    0xc6e00bf3u,
    0xd5a79147u,
    0x06ca6351u,
    0x14292967u,
    0x27b70a85u,
    0x2e1b2138u,
    0x4d2c6dfcu,
    0x53380d13u,
    0x650a7354u,
    0x766a0abbu,
    0x81c2c92eu,
    0x92722c85u,
    0xa2bfe8a1u,
    0xa81a664bu,
    0xc24b8b70u,
    0xc76c51a3u,
    0xd192e819u,
    0xd6990624u,
    0xf40e3585u,
    0x106aa070u,
    0x19a4c116u,
    0x1e376c08u,
    0x2748774cu,
    0x34b0bcb5u,
    0x391c0cb3u,
    0x4ed8aa4au,
    0x5b9cca4fu,
    0x682e6ff3u,
    0x748f82eeu,
    0x78a5636fu,
    0x84c87814u,
    0x8cc70208u,
    0x90befffau,
    0xa4506cebu,
    0xbef9a3f7u,
    0xc67178f2u,
};
static const uint32_t hsh_sha256_h0[8] = {
    0x6a09e667u,
    0xbb67ae85u,
    0x3c6ef372u,
    0xa54ff53au,
    0x510e527fu,
    0x9b05688cu,
    0x1f83d9abu,
    0x5be0cd19u,
};
static const uint64_t hsh_sha512_k[80] = {
    0x428a2f98d728ae22ULL,
    0x7137449123ef65cdULL,
    0xb5c0fbcfec4d3b2fULL,
    0xe9b5dba58189dbbcULL,
    0x3956c25bf348b538ULL,
    0x59f111f1b605d019ULL,
    0x923f82a4af194f9bULL,
    0xab1c5ed5da6d8118ULL,
    0xd807aa98a3030242ULL,
    0x12835b0145706fbeULL,
    0x243185be4ee4b28cULL,
    0x550c7dc3d5ffb4e2ULL,
    0x72be5d74f27b896fULL,
    0x80deb1fe3b1696b1ULL,
    0x9bdc06a725c71235ULL,
    0xc19bf174cf692694ULL,
    0xe49b69c19ef14ad2ULL,
    0xefbe4786384f25e3ULL,
    0x0fc19dc68b8cd5b5ULL,
    0x240ca1cc77ac9c65ULL,
    0x2de92c6f592b0275ULL,
    0x4a7484aa6ea6e483ULL,
    0x5cb0a9dcbd41fbd4ULL,
    0x76f988da831153b5ULL,
    0x983e5152ee66dfabULL,
    0xa831c66d2db43210ULL,
    0xb00327c898fb213fULL,
    0xbf597fc7beef0ee4ULL,
    0xc6e00bf33da88fc2ULL,
    0xd5a79147930aa725ULL,
    0x06ca6351e003826fULL,
    0x142929670a0e6e70ULL,
    0x27b70a8546d22ffcULL,
    0x2e1b21385c26c926ULL,
    0x4d2c6dfc5ac42aedULL,
    0x53380d139d95b3dfULL,
    0x650a73548baf63deULL,
    0x766a0abb3c77b2a8ULL,
    0x81c2c92e47edaee6ULL,
    0x92722c851482353bULL,
    0xa2bfe8a14cf10364ULL,
    0xa81a664bbc423001ULL,
    0xc24b8b70d0f89791ULL,
    0xc76c51a30654be30ULL,
    0xd192e819d6ef5218ULL,
    0xd69906245565a910ULL,
    0xf40e35855771202aULL,
    0x106aa07032bbd1b8ULL,
    0x19a4c116b8d2d0c8ULL,
    0x1e376c085141ab53ULL,
    0x2748774cdf8eeb99ULL,
    0x34b0bcb5e19b48a8ULL,
    0x391c0cb3c5c95a63ULL,
    0x4ed8aa4ae3418acbULL,
    0x5b9cca4f7763e373ULL,
    0x682e6ff3d6b2b8a3ULL,
    0x748f82ee5defb2fcULL,
    0x78a5636f43172f60ULL,
    0x84c87814a1f0ab72ULL,
    0x8cc702081a6439ecULL,
    0x90befffa23631e28ULL,
    0xa4506cebde82bde9ULL,
    0xbef9a3f7b2c67915ULL,
    0xc67178f2e372532bULL,
    0xca273eceea26619cULL,
    0xd186b8c721c0c207ULL,
    0xeada7dd6cde0eb1eULL,
    0xf57d4f7fee6ed178ULL,
    0x06f067aa72176fbaULL,
    0x0a637dc5a2c898a6ULL,
    0x113f9804bef90daeULL,
    0x1b710b35131c471bULL,
    0x28db77f523047d84ULL,
    0x32caab7b40c72493ULL,
    0x3c9ebe0a15c9bebcULL,
    0x431d67c49c100d4cULL,
    0x4cc5d4becb3e42b6ULL,
    0x597f299cfc657e2aULL,
    0x5fcb6fab3ad6faecULL,
    0x6c44198c4a475817ULL,
};
static const uint64_t hsh_sha512_h0[8] = {
    0x6a09e667f3bcc908ULL,
    0xbb67ae8584caa73bULL,
    0x3c6ef372fe94f82bULL,
    0xa54ff53a5f1d36f1ULL,
    0x510e527fade682d1ULL,
    0x9b05688c2b3e6c1fULL,
    0x1f83d9abfb41bd6bULL,
    0x5be0cd19137e2179ULL,
};
static const uint32_t hsh_md5_t[64] = {
    0xd76aa478u,
    0xe8c7b756u,
    0x242070dbu,
    0xc1bdceeeu,
    0xf57c0fafu,
    0x4787c62au,
    0xa8304613u,
    0xfd469501u,
    0x698098d8u,
    0x8b44f7afu,
    0xffff5bb1u,
    0x895cd7beu,
    0x6b901122u,
    0xfd987193u,
    0xa679438eu,
    0x49b40821u,
    0xf61e2562u,
    0xc040b340u,
    0x265e5a51u,
    0xe9b6c7aau,
    0xd62f105du,
    0x02441453u,
    0xd8a1e681u,
    0xe7d3fbc8u,
    0x21e1cde6u,
    0xc33707d6u,
    0xf4d50d87u,
    0x455a14edu,
    0xa9e3e905u,
    0xfcefa3f8u,
    0x676f02d9u,
    0x8d2a4c8au,
    0xfffa3942u,
    0x8771f681u,
    0x6d9d6122u,
    0xfde5380cu,
    0xa4beea44u,
    0x4bdecfa9u,
    0xf6bb4b60u,
    0xbebfbc70u,
    0x289b7ec6u,
    0xeaa127fau,
    0xd4ef3085u,
    0x04881d05u,
    0xd9d4d039u,
    0xe6db99e5u,
    0x1fa27cf8u,
    0xc4ac5665u,
    0xf4292244u,
    0x432aff97u,
    0xab9423a7u,
    0xfc93a039u,
    0x655b59c3u,
    0x8f0ccc92u,
    0xffeff47du,
    0x85845dd1u,
    0x6fa87e4fu,
    0xfe2ce6e0u,
    0xa3014314u,
    0x4e0811a1u,
    0xf7537e82u,
    0xbd3af235u,
    0x2ad7d2bbu,
    0xeb86d391u,
};

/* ── SHA-256 / SHA-512 / SHA-1 / MD5 ─────────────────────────────────────── */
#define HSH_ROR32(x,n) (((x) >> (n)) | ((x) << (32 - (n))))
#define HSH_ROR64(x,n) (((x) >> (n)) | ((x) << (64 - (n))))
#define HSH_ROL32(x,n) (((x) << (n)) | ((x) >> (32 - (n))))

typedef struct { uint32_t h[8]; uint64_t len; uint8_t buf[64]; size_t n; } HshSha256;
static void hsh_sha256_block(HshSha256* c, const uint8_t* p) {
    uint32_t w[64], a,b,cc,d,e,f,g,h;
    for (int i = 0; i < 16; i++) w[i] = ((uint32_t)p[4*i]<<24)|((uint32_t)p[4*i+1]<<16)|((uint32_t)p[4*i+2]<<8)|p[4*i+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = HSH_ROR32(w[i-15],7) ^ HSH_ROR32(w[i-15],18) ^ (w[i-15]>>3);
        uint32_t s1 = HSH_ROR32(w[i-2],17) ^ HSH_ROR32(w[i-2],19) ^ (w[i-2]>>10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    a=c->h[0];b=c->h[1];cc=c->h[2];d=c->h[3];e=c->h[4];f=c->h[5];g=c->h[6];h=c->h[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = HSH_ROR32(e,6) ^ HSH_ROR32(e,11) ^ HSH_ROR32(e,25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + S1 + ch + hsh_sha256_k[i] + w[i];
        uint32_t S0 = HSH_ROR32(a,2) ^ HSH_ROR32(a,13) ^ HSH_ROR32(a,22);
        uint32_t mj = (a & b) ^ (a & cc) ^ (b & cc);
        uint32_t t2 = S0 + mj;
        h=g; g=f; f=e; e=d+t1; d=cc; cc=b; b=a; a=t1+t2;
    }
    c->h[0]+=a;c->h[1]+=b;c->h[2]+=cc;c->h[3]+=d;c->h[4]+=e;c->h[5]+=f;c->h[6]+=g;c->h[7]+=h;
}
static void hsh_sha256_init(HshSha256* c){ memcpy(c->h, hsh_sha256_h0, 32); c->len=0; c->n=0; }
static void hsh_sha256_update(HshSha256* c, const uint8_t* d, size_t l) {
    c->len += l;
    while (l) { size_t t = 64 - c->n; if (t > l) t = l; memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
        if (c->n == 64) { hsh_sha256_block(c, c->buf); c->n = 0; } }
}
static void hsh_sha256_final(HshSha256* c, uint8_t out[32]) {
    uint64_t bits = c->len * 8; uint8_t pad = 0x80; hsh_sha256_update(c, &pad, 1);
    uint8_t z = 0; while (c->n != 56) hsh_sha256_update(c, &z, 1);
    uint8_t lb[8]; for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (56 - 8*i));
    hsh_sha256_update(c, lb, 8);
    for (int i = 0; i < 8; i++) { out[4*i]=(uint8_t)(c->h[i]>>24); out[4*i+1]=(uint8_t)(c->h[i]>>16); out[4*i+2]=(uint8_t)(c->h[i]>>8); out[4*i+3]=(uint8_t)c->h[i]; }
}

typedef struct { uint64_t h[8]; uint64_t len; uint8_t buf[128]; size_t n; } HshSha512;
static void hsh_sha512_block(HshSha512* c, const uint8_t* p) {
    uint64_t w[80], a,b,cc,d,e,f,g,h;
    for (int i = 0; i < 16; i++) { w[i] = 0; for (int j = 0; j < 8; j++) w[i] = (w[i] << 8) | p[8*i+j]; }
    for (int i = 16; i < 80; i++) {
        uint64_t s0 = HSH_ROR64(w[i-15],1) ^ HSH_ROR64(w[i-15],8) ^ (w[i-15]>>7);
        uint64_t s1 = HSH_ROR64(w[i-2],19) ^ HSH_ROR64(w[i-2],61) ^ (w[i-2]>>6);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    a=c->h[0];b=c->h[1];cc=c->h[2];d=c->h[3];e=c->h[4];f=c->h[5];g=c->h[6];h=c->h[7];
    for (int i = 0; i < 80; i++) {
        uint64_t S1 = HSH_ROR64(e,14) ^ HSH_ROR64(e,18) ^ HSH_ROR64(e,41);
        uint64_t ch = (e & f) ^ (~e & g);
        uint64_t t1 = h + S1 + ch + hsh_sha512_k[i] + w[i];
        uint64_t S0 = HSH_ROR64(a,28) ^ HSH_ROR64(a,34) ^ HSH_ROR64(a,39);
        uint64_t mj = (a & b) ^ (a & cc) ^ (b & cc);
        uint64_t t2 = S0 + mj;
        h=g; g=f; f=e; e=d+t1; d=cc; cc=b; b=a; a=t1+t2;
    }
    c->h[0]+=a;c->h[1]+=b;c->h[2]+=cc;c->h[3]+=d;c->h[4]+=e;c->h[5]+=f;c->h[6]+=g;c->h[7]+=h;
}
static void hsh_sha512_init(HshSha512* c){ memcpy(c->h, hsh_sha512_h0, 64); c->len=0; c->n=0; }
static void hsh_sha512_update(HshSha512* c, const uint8_t* d, size_t l) {
    c->len += l;
    while (l) { size_t t = 128 - c->n; if (t > l) t = l; memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
        if (c->n == 128) { hsh_sha512_block(c, c->buf); c->n = 0; } }
}
static void hsh_sha512_final(HshSha512* c, uint8_t out[64]) {
    uint64_t bits = c->len * 8; uint8_t pad = 0x80; hsh_sha512_update(c, &pad, 1);
    uint8_t z = 0; while (c->n != 112) hsh_sha512_update(c, &z, 1);
    uint8_t lb[16] = {0}; for (int i = 0; i < 8; i++) lb[8+i] = (uint8_t)(bits >> (56 - 8*i));
    hsh_sha512_update(c, lb, 16);
    for (int i = 0; i < 8; i++) for (int j = 0; j < 8; j++) out[8*i+j] = (uint8_t)(c->h[i] >> (56 - 8*j));
}

typedef struct { uint32_t h[5]; uint64_t len; uint8_t buf[64]; size_t n; } HshSha1;
static void hsh_sha1_block(HshSha1* c, const uint8_t* p) {
    uint32_t w[80], a,b,cc,d,e;
    for (int i = 0; i < 16; i++) w[i] = ((uint32_t)p[4*i]<<24)|((uint32_t)p[4*i+1]<<16)|((uint32_t)p[4*i+2]<<8)|p[4*i+3];
    for (int i = 16; i < 80; i++) w[i] = HSH_ROL32(w[i-3]^w[i-8]^w[i-14]^w[i-16], 1);
    a=c->h[0];b=c->h[1];cc=c->h[2];d=c->h[3];e=c->h[4];
    for (int i = 0; i < 80; i++) {
        uint32_t f, k;
        if (i < 20)      { f = (b & cc) | (~b & d); k = 0x5A827999u; }
        else if (i < 40) { f = b ^ cc ^ d;          k = 0x6ED9EBA1u; }
        else if (i < 60) { f = (b & cc) | (b & d) | (cc & d); k = 0x8F1BBCDCu; }
        else             { f = b ^ cc ^ d;          k = 0xCA62C1D6u; }
        uint32_t t = HSH_ROL32(a,5) + f + e + k + w[i];
        e=d; d=cc; cc=HSH_ROL32(b,30); b=a; a=t;
    }
    c->h[0]+=a;c->h[1]+=b;c->h[2]+=cc;c->h[3]+=d;c->h[4]+=e;
}
static void hsh_sha1_init(HshSha1* c){ c->h[0]=0x67452301u;c->h[1]=0xEFCDAB89u;c->h[2]=0x98BADCFEu;c->h[3]=0x10325476u;c->h[4]=0xC3D2E1F0u; c->len=0; c->n=0; }
static void hsh_sha1_update(HshSha1* c, const uint8_t* d, size_t l) {
    c->len += l;
    while (l) { size_t t = 64 - c->n; if (t > l) t = l; memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
        if (c->n == 64) { hsh_sha1_block(c, c->buf); c->n = 0; } }
}
static void hsh_sha1_final(HshSha1* c, uint8_t out[20]) {
    uint64_t bits = c->len * 8; uint8_t pad = 0x80; hsh_sha1_update(c, &pad, 1);
    uint8_t z = 0; while (c->n != 56) hsh_sha1_update(c, &z, 1);
    uint8_t lb[8]; for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (56 - 8*i));
    hsh_sha1_update(c, lb, 8);
    for (int i = 0; i < 5; i++) { out[4*i]=(uint8_t)(c->h[i]>>24); out[4*i+1]=(uint8_t)(c->h[i]>>16); out[4*i+2]=(uint8_t)(c->h[i]>>8); out[4*i+3]=(uint8_t)c->h[i]; }
}

typedef struct { uint32_t h[4]; uint64_t len; uint8_t buf[64]; size_t n; } HshMd5;
static void hsh_md5_block(HshMd5* c, const uint8_t* p) {
    static const int s[64] = {7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22, 5,9,14,20,5,9,14,20,5,9,14,20,5,9,14,20,
                              4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23, 6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21};
    uint32_t m[16], a=c->h[0], b=c->h[1], cc=c->h[2], d=c->h[3];
    for (int i = 0; i < 16; i++) m[i] = (uint32_t)p[4*i] | ((uint32_t)p[4*i+1]<<8) | ((uint32_t)p[4*i+2]<<16) | ((uint32_t)p[4*i+3]<<24);
    for (int i = 0; i < 64; i++) {
        uint32_t f; int g;
        if (i < 16)      { f = (b & cc) | (~b & d); g = i; }
        else if (i < 32) { f = (d & b) | (~d & cc); g = (5*i + 1) % 16; }
        else if (i < 48) { f = b ^ cc ^ d;          g = (3*i + 5) % 16; }
        else             { f = cc ^ (b | ~d);       g = (7*i) % 16; }
        f = f + a + hsh_md5_t[i] + m[g];
        a = d; d = cc; cc = b; b = b + HSH_ROL32(f, s[i]);
    }
    c->h[0]+=a;c->h[1]+=b;c->h[2]+=cc;c->h[3]+=d;
}
static void hsh_md5_init(HshMd5* c){ c->h[0]=0x67452301u;c->h[1]=0xefcdab89u;c->h[2]=0x98badcfeu;c->h[3]=0x10325476u; c->len=0; c->n=0; }
static void hsh_md5_update(HshMd5* c, const uint8_t* d, size_t l) {
    c->len += l;
    while (l) { size_t t = 64 - c->n; if (t > l) t = l; memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
        if (c->n == 64) { hsh_md5_block(c, c->buf); c->n = 0; } }
}
static void hsh_md5_final(HshMd5* c, uint8_t out[16]) {
    uint64_t bits = c->len * 8; uint8_t pad = 0x80; hsh_md5_update(c, &pad, 1);
    uint8_t z = 0; while (c->n != 56) hsh_md5_update(c, &z, 1);
    uint8_t lb[8]; for (int i = 0; i < 8; i++) lb[i] = (uint8_t)(bits >> (8*i));
    hsh_md5_update(c, lb, 8);
    for (int i = 0; i < 4; i++) { out[4*i]=(uint8_t)c->h[i]; out[4*i+1]=(uint8_t)(c->h[i]>>8); out[4*i+2]=(uint8_t)(c->h[i]>>16); out[4*i+3]=(uint8_t)(c->h[i]>>24); }
}

/* one-shot helpers -> raw digest; algo: 0=sha256 1=sha512 2=sha1 3=md5 */
static size_t hsh_digest_len(int algo) { static const size_t l[4] = {32, 64, 20, 16}; return l[algo]; }
static size_t hsh_digest_block(int algo) { return algo == 1 ? 128 : 64; }
static void hsh_digest2(int algo, const uint8_t* a, size_t al, const uint8_t* b, size_t bl, uint8_t* out) {
    switch (algo) {
        case 0: { HshSha256 c; hsh_sha256_init(&c); hsh_sha256_update(&c,a,al); if (bl) hsh_sha256_update(&c,b,bl); hsh_sha256_final(&c,out); break; }
        case 1: { HshSha512 c; hsh_sha512_init(&c); hsh_sha512_update(&c,a,al); if (bl) hsh_sha512_update(&c,b,bl); hsh_sha512_final(&c,out); break; }
        case 2: { HshSha1   c; hsh_sha1_init(&c);   hsh_sha1_update(&c,a,al);   if (bl) hsh_sha1_update(&c,b,bl);   hsh_sha1_final(&c,out);   break; }
        default:{ HshMd5    c; hsh_md5_init(&c);    hsh_md5_update(&c,a,al);    if (bl) hsh_md5_update(&c,b,bl);    hsh_md5_final(&c,out);    break; }
    }
}
static void hsh_hmac(int algo, const uint8_t* key, size_t kl, const uint8_t* msg, size_t ml, uint8_t* out) {
    size_t bs = hsh_digest_block(algo), dl = hsh_digest_len(algo);
    uint8_t k[128] = {0}, ipad[128], opad[128], inner[64];
    if (kl > bs) hsh_digest2(algo, key, kl, NULL, 0, k); else memcpy(k, key, kl);
    for (size_t i = 0; i < bs; i++) { ipad[i] = k[i] ^ 0x36; opad[i] = k[i] ^ 0x5c; }
    /* inner = H(ipad || msg) */
    uint8_t* tmp = (uint8_t*)malloc(bs + ml);
    if (!tmp) { memset(out, 0, dl); return; }
    memcpy(tmp, ipad, bs); memcpy(tmp + bs, msg, ml);
    hsh_digest2(algo, tmp, bs + ml, NULL, 0, inner);
    free(tmp);
    hsh_digest2(algo, opad, bs, inner, dl, out);
}

static hsh_string hsh_hex_of(const uint8_t* d, size_t n) {
    static const char* hx = "0123456789abcdef";
    char* o = (char*)hsh_alloc((uint64_t)n * 2 + 1);
    if (!o) return "";
    for (size_t i = 0; i < n; i++) { o[2*i] = hx[d[i] >> 4]; o[2*i+1] = hx[d[i] & 15]; }
    o[2*n] = '\0';
    return o;
}
/* bytes in this runtime == HshArray* of byte values 0-255 (see hsh_fs_read_bytes) */
static uint8_t* hsh_bytes_flatten(HshArray* a, size_t* n) {
    *n = a ? (size_t)a->len : 0;
    uint8_t* b = (uint8_t*)malloc(*n ? *n : 1);
    if (!b) { *n = 0; return NULL; }
    for (size_t i = 0; i < *n; i++) b[i] = (uint8_t)a->data[i];
    return b;
}
static HshArray* hsh_bytes_wrap(const uint8_t* d, size_t n) {
    HshArray* a = hsh_array_new();
    for (size_t i = 0; i < n; i++) a = hsh_array_push(a, (int64_t)d[i]);
    return a;
}

hsh_string hsh_crypto_sha256(hsh_string s)  { uint8_t o[32]; hsh_digest2(0,(const uint8_t*)(s?s:""),s?strlen(s):0,NULL,0,o); return hsh_hex_of(o,32); }
hsh_string hsh_crypto_sha512(hsh_string s)  { uint8_t o[64]; hsh_digest2(1,(const uint8_t*)(s?s:""),s?strlen(s):0,NULL,0,o); return hsh_hex_of(o,64); }
hsh_string hsh_crypto_sha1(hsh_string s)    { uint8_t o[20]; hsh_digest2(2,(const uint8_t*)(s?s:""),s?strlen(s):0,NULL,0,o); return hsh_hex_of(o,20); }
hsh_string hsh_crypto_md5(hsh_string s)     { uint8_t o[16]; hsh_digest2(3,(const uint8_t*)(s?s:""),s?strlen(s):0,NULL,0,o); return hsh_hex_of(o,16); }
hsh_string hsh_crypto_sha256_bytes(HshArray* b) {
    size_t n; uint8_t* d = hsh_bytes_flatten(b, &n);
    uint8_t o[32]; hsh_digest2(0, d ? d : (const uint8_t*)"", n, NULL, 0, o); free(d);
    return hsh_hex_of(o, 32);
}
hsh_string hsh_crypto_hmac_sha256(hsh_string k, hsh_string m) {
    uint8_t o[32]; hsh_hmac(0,(const uint8_t*)(k?k:""),k?strlen(k):0,(const uint8_t*)(m?m:""),m?strlen(m):0,o); return hsh_hex_of(o,32);
}
hsh_string hsh_crypto_hmac_sha512(hsh_string k, hsh_string m) {
    uint8_t o[64]; hsh_hmac(1,(const uint8_t*)(k?k:""),k?strlen(k):0,(const uint8_t*)(m?m:""),m?strlen(m):0,o); return hsh_hex_of(o,64);
}

/* PBKDF2-HMAC-SHA256: (password: string, salt: bytes, iterations, key_len) -> bytes */
HshArray* hsh_crypto_pbkdf2(hsh_string pw, HshArray* salt, int64_t iters, int64_t klen) {
    if (klen <= 0 || iters <= 0) return hsh_array_new();
    size_t sl; uint8_t* s = hsh_bytes_flatten(salt, &sl);
    size_t pl = pw ? strlen(pw) : 0;
    uint8_t* dk = (uint8_t*)malloc((size_t)klen + 32);
    uint8_t* sb = (uint8_t*)malloc(sl + 4);
    if (!dk || !sb) { free(dk); free(sb); free(s); return hsh_array_new(); }
    size_t blocks = ((size_t)klen + 31) / 32;
    for (size_t b = 1; b <= blocks; b++) {
        uint8_t u[32], t[32];
        memcpy(sb, s, sl);
        sb[sl] = (uint8_t)(b >> 24); sb[sl+1] = (uint8_t)(b >> 16); sb[sl+2] = (uint8_t)(b >> 8); sb[sl+3] = (uint8_t)b;
        hsh_hmac(0, (const uint8_t*)(pw?pw:""), pl, sb, sl + 4, u);
        memcpy(t, u, 32);
        for (int64_t i = 1; i < iters; i++) {
            hsh_hmac(0, (const uint8_t*)(pw?pw:""), pl, u, 32, u);
            for (int j = 0; j < 32; j++) t[j] ^= u[j];
        }
        memcpy(dk + (b - 1) * 32, t, 32);
    }
    HshArray* r = hsh_bytes_wrap(dk, (size_t)klen);
    free(dk); free(sb); free(s);
    return r;
}

static void hsh_urandom(uint8_t* buf, size_t n) {
    FILE* f = fopen("/dev/urandom", "rb");
    size_t got = f ? fread(buf, 1, n, f) : 0;
    if (f) fclose(f);
    if (got != n) { fprintf(stderr, "crypto: cannot read /dev/urandom\n"); exit(1); }
}
HshArray* hsh_crypto_random_bytes(int64_t n) {
    if (n <= 0) return hsh_array_new();
    uint8_t* b = (uint8_t*)malloc((size_t)n);
    if (!b) return hsh_array_new();
    hsh_urandom(b, (size_t)n);
    HshArray* r = hsh_bytes_wrap(b, (size_t)n);
    free(b);
    return r;
}
/* constant-time (does not short-circuit on the first mismatch) */
int64_t hsh_crypto_bytes_eq(HshArray* a, HshArray* b) {
    int64_t la = a ? a->len : 0, lb = b ? b->len : 0;
    uint8_t diff = (la != lb);
    int64_t m = la > lb ? la : lb;
    for (int64_t i = 0; i < m; i++) {
        uint8_t x = i < la ? (uint8_t)a->data[i] : 0, y = i < lb ? (uint8_t)b->data[i] : 0;
        diff |= x ^ y;
    }
    return diff == 0;
}
HshArray* hsh_crypto_xor_bytes(HshArray* a, HshArray* b) {
    int64_t la = a ? a->len : 0, lb = b ? b->len : 0;
    if (la != lb || la == 0) return hsh_array_new();
    HshArray* r = hsh_array_new();
    for (int64_t i = 0; i < la; i++) r = hsh_array_push(r, (int64_t)(((uint8_t)a->data[i]) ^ ((uint8_t)b->data[i])));
    return r;
}

/* ── BLAKE3 (default hash mode, 32-byte output) ──────────────────────────── */
static const uint8_t hsh_b3_perm[16] = {2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8};
#define HSH_B3_CHUNK_START 1
#define HSH_B3_CHUNK_END   2
#define HSH_B3_PARENT      4
#define HSH_B3_ROOT        8
static void hsh_b3_g(uint32_t* s, int a, int b, int c, int d, uint32_t mx, uint32_t my) {
    s[a] = s[a] + s[b] + mx; s[d] = HSH_ROR32(s[d] ^ s[a], 16);
    s[c] = s[c] + s[d];      s[b] = HSH_ROR32(s[b] ^ s[c], 12);
    s[a] = s[a] + s[b] + my; s[d] = HSH_ROR32(s[d] ^ s[a], 8);
    s[c] = s[c] + s[d];      s[b] = HSH_ROR32(s[b] ^ s[c], 7);
}
static void hsh_b3_round(uint32_t* s, const uint32_t* m) {
    hsh_b3_g(s,0,4,8,12,m[0],m[1]);  hsh_b3_g(s,1,5,9,13,m[2],m[3]);
    hsh_b3_g(s,2,6,10,14,m[4],m[5]); hsh_b3_g(s,3,7,11,15,m[6],m[7]);
    hsh_b3_g(s,0,5,10,15,m[8],m[9]); hsh_b3_g(s,1,6,11,12,m[10],m[11]);
    hsh_b3_g(s,2,7,8,13,m[12],m[13]);hsh_b3_g(s,3,4,9,14,m[14],m[15]);
}
static void hsh_b3_compress(const uint32_t cv[8], const uint32_t blk[16], uint64_t ctr, uint32_t blen, uint32_t flags, uint32_t out[16]) {
    uint32_t s[16] = { cv[0],cv[1],cv[2],cv[3],cv[4],cv[5],cv[6],cv[7],
                       hsh_sha256_h0[0],hsh_sha256_h0[1],hsh_sha256_h0[2],hsh_sha256_h0[3],
                       (uint32_t)ctr, (uint32_t)(ctr >> 32), blen, flags };
    uint32_t m[16], t[16];
    memcpy(m, blk, 64);
    for (int r = 0; r < 7; r++) {
        hsh_b3_round(s, m);
        if (r < 6) { for (int i = 0; i < 16; i++) t[i] = m[hsh_b3_perm[i]]; memcpy(m, t, 64); }
    }
    for (int i = 0; i < 8; i++) { s[i] ^= s[i+8]; s[i+8] ^= cv[i]; }
    memcpy(out, s, 64);
}
static void hsh_b3_words(const uint8_t* b, size_t n, uint32_t w[16]) {
    uint8_t p[64] = {0}; memcpy(p, b, n);
    for (int i = 0; i < 16; i++) w[i] = (uint32_t)p[4*i] | ((uint32_t)p[4*i+1]<<8) | ((uint32_t)p[4*i+2]<<16) | ((uint32_t)p[4*i+3]<<24);
}
typedef struct { uint32_t cv[8]; uint32_t blk[16]; uint64_t ctr; uint32_t blen; uint32_t flags; } HshB3Out;
static void hsh_b3_out_cv(const HshB3Out* o, uint32_t cv[8]) {
    uint32_t t[16]; hsh_b3_compress(o->cv, o->blk, o->ctr, o->blen, o->flags, t); memcpy(cv, t, 32);
}
typedef struct { uint32_t cv[8]; uint64_t ctr; uint8_t buf[64]; size_t n; uint8_t nblocks; } HshB3Chunk;
static void hsh_b3_chunk_init(HshB3Chunk* c, uint64_t ctr) { memcpy(c->cv, hsh_sha256_h0, 32); c->ctr = ctr; c->n = 0; c->nblocks = 0; }
static size_t hsh_b3_chunk_len(const HshB3Chunk* c) { return 64 * (size_t)c->nblocks + c->n; }
static void hsh_b3_chunk_update(HshB3Chunk* c, const uint8_t* d, size_t l) {
    while (l) {
        if (c->n == 64) {
            uint32_t w[16], t[16]; hsh_b3_words(c->buf, 64, w);
            hsh_b3_compress(c->cv, w, c->ctr, 64, c->nblocks == 0 ? HSH_B3_CHUNK_START : 0, t);
            memcpy(c->cv, t, 32); c->nblocks++; c->n = 0;
        }
        size_t t = 64 - c->n; if (t > l) t = l;
        memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
    }
}
static HshB3Out hsh_b3_chunk_output(const HshB3Chunk* c) {
    HshB3Out o; memcpy(o.cv, c->cv, 32); hsh_b3_words(c->buf, c->n, o.blk);
    o.ctr = c->ctr; o.blen = (uint32_t)c->n;
    o.flags = (c->nblocks == 0 ? HSH_B3_CHUNK_START : 0) | HSH_B3_CHUNK_END;
    return o;
}
static HshB3Out hsh_b3_parent_out(const uint32_t l[8], const uint32_t r[8]) {
    HshB3Out o; memcpy(o.cv, hsh_sha256_h0, 32);
    memcpy(o.blk, l, 32); memcpy(o.blk + 8, r, 32);
    o.ctr = 0; o.blen = 64; o.flags = HSH_B3_PARENT; return o;
}
static void hsh_b3_hash(const uint8_t* d, size_t l, uint8_t out[32]) {
    uint32_t stack[54][8]; int sp = 0;
    HshB3Chunk ch; hsh_b3_chunk_init(&ch, 0);
    while (l) {
        if (hsh_b3_chunk_len(&ch) == 1024) {
            HshB3Out o = hsh_b3_chunk_output(&ch);
            uint32_t cv[8]; hsh_b3_out_cv(&o, cv);
            uint64_t total = ch.ctr + 1;
            while ((total & 1) == 0) {
                HshB3Out p = hsh_b3_parent_out(stack[--sp], cv);
                hsh_b3_out_cv(&p, cv); total >>= 1;
            }
            memcpy(stack[sp++], cv, 32);
            hsh_b3_chunk_init(&ch, ch.ctr + 1);
        }
        size_t t = 1024 - hsh_b3_chunk_len(&ch); if (t > l) t = l;
        hsh_b3_chunk_update(&ch, d, t); d += t; l -= t;
    }
    HshB3Out o = hsh_b3_chunk_output(&ch);
    while (sp > 0) {
        uint32_t cv[8]; hsh_b3_out_cv(&o, cv);
        o = hsh_b3_parent_out(stack[--sp], cv);
    }
    uint32_t w[16]; hsh_b3_compress(o.cv, o.blk, 0, o.blen, o.flags | HSH_B3_ROOT, w);
    for (int i = 0; i < 8; i++) { out[4*i]=(uint8_t)w[i]; out[4*i+1]=(uint8_t)(w[i]>>8); out[4*i+2]=(uint8_t)(w[i]>>16); out[4*i+3]=(uint8_t)(w[i]>>24); }
}
hsh_string hsh_crypto_blake3(hsh_string s) {
    uint8_t o[32]; hsh_b3_hash((const uint8_t*)(s ? s : ""), s ? strlen(s) : 0, o); return hsh_hex_of(o, 32);
}

/* ── BLAKE2b (variable output, unkeyed) — needed by Argon2 ────────────────── */
static const uint8_t hsh_b2_sigma[12][16] = {
    {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15},{14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3},
    {11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4},{7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8},
    {9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13},{2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9},
    {12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11},{13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10},
    {6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5},{10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0},
    {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15},{14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3} };
typedef struct { uint64_t h[8]; uint64_t t; uint8_t buf[128]; size_t n; size_t outlen; } HshB2;
#define HSH_B2G(a,b,c,d,x,y) do { v[a]=v[a]+v[b]+(x); v[d]=HSH_ROR64(v[d]^v[a],32); v[c]=v[c]+v[d]; v[b]=HSH_ROR64(v[b]^v[c],24); \
    v[a]=v[a]+v[b]+(y); v[d]=HSH_ROR64(v[d]^v[a],16); v[c]=v[c]+v[d]; v[b]=HSH_ROR64(v[b]^v[c],63); } while (0)
static void hsh_b2_compress(HshB2* c, const uint8_t* blk, int last) {
    uint64_t m[16], v[16];
    for (int i = 0; i < 16; i++) { m[i] = 0; for (int j = 7; j >= 0; j--) m[i] = (m[i] << 8) | blk[8*i+j]; }
    for (int i = 0; i < 8; i++) { v[i] = c->h[i]; v[i+8] = hsh_sha512_h0[i]; }
    v[12] ^= c->t; /* high half of the 128-bit counter is always 0 here */
    if (last) v[14] = ~v[14];
    for (int r = 0; r < 12; r++) {
        const uint8_t* s = hsh_b2_sigma[r];
        HSH_B2G(0,4,8,12,m[s[0]],m[s[1]]);  HSH_B2G(1,5,9,13,m[s[2]],m[s[3]]);
        HSH_B2G(2,6,10,14,m[s[4]],m[s[5]]); HSH_B2G(3,7,11,15,m[s[6]],m[s[7]]);
        HSH_B2G(0,5,10,15,m[s[8]],m[s[9]]); HSH_B2G(1,6,11,12,m[s[10]],m[s[11]]);
        HSH_B2G(2,7,8,13,m[s[12]],m[s[13]]);HSH_B2G(3,4,9,14,m[s[14]],m[s[15]]);
    }
    for (int i = 0; i < 8; i++) c->h[i] ^= v[i] ^ v[i+8];
}
static void hsh_b2_init(HshB2* c, size_t outlen) {
    memcpy(c->h, hsh_sha512_h0, 64);
    c->h[0] ^= 0x01010000ULL ^ (uint64_t)outlen;
    c->t = 0; c->n = 0; c->outlen = outlen;
}
static void hsh_b2_update(HshB2* c, const uint8_t* d, size_t l) {
    while (l) {
        if (c->n == 128) { c->t += 128; hsh_b2_compress(c, c->buf, 0); c->n = 0; }
        size_t t = 128 - c->n; if (t > l) t = l;
        memcpy(c->buf + c->n, d, t); c->n += t; d += t; l -= t;
    }
}
static void hsh_b2_final(HshB2* c, uint8_t* out) {
    c->t += c->n; memset(c->buf + c->n, 0, 128 - c->n);
    hsh_b2_compress(c, c->buf, 1);
    for (size_t i = 0; i < c->outlen; i++) out[i] = (uint8_t)(c->h[i / 8] >> (8 * (i % 8)));
}
static void hsh_b2(const uint8_t* a, size_t al, const uint8_t* b, size_t bl, uint8_t* out, size_t outlen) {
    HshB2 c; hsh_b2_init(&c, outlen); hsh_b2_update(&c, a, al); if (bl) hsh_b2_update(&c, b, bl); hsh_b2_final(&c, out);
}

/* ── Argon2id (RFC 9106), PHC string format ───────────────────────────────── */
#define HSH_A2_BLK 128 /* 1024-byte block = 128 u64 */
static void hsh_a2_hprime(uint8_t* out, size_t T, const uint8_t* in, size_t inl) {
    uint8_t lt[4] = { (uint8_t)T, (uint8_t)(T >> 8), (uint8_t)(T >> 16), (uint8_t)(T >> 24) };
    if (T <= 64) {
        HshB2 c; hsh_b2_init(&c, T); hsh_b2_update(&c, lt, 4); hsh_b2_update(&c, in, inl); hsh_b2_final(&c, out); return;
    }
    uint8_t v[64];
    HshB2 c; hsh_b2_init(&c, 64); hsh_b2_update(&c, lt, 4); hsh_b2_update(&c, in, inl); hsh_b2_final(&c, v);
    memcpy(out, v, 32);
    size_t pos = 32, rem = T - 32;
    while (rem > 64) {
        uint8_t nv[64]; hsh_b2(v, 64, NULL, 0, nv, 64);
        memcpy(v, nv, 64); memcpy(out + pos, v, 32); pos += 32; rem -= 32;
    }
    hsh_b2(v, 64, NULL, 0, out + pos, rem);
}
static uint64_t hsh_a2_mka(uint64_t x, uint64_t y) { return x + y + 2ULL * (uint64_t)(uint32_t)x * (uint64_t)(uint32_t)y; }
#define HSH_A2G(a,b,c,d) do { a = hsh_a2_mka(a,b); d = HSH_ROR64(d^a,32); c = hsh_a2_mka(c,d); b = HSH_ROR64(b^c,24); \
    a = hsh_a2_mka(a,b); d = HSH_ROR64(d^a,16); c = hsh_a2_mka(c,d); b = HSH_ROR64(b^c,63); } while (0)
static void hsh_a2_round(uint64_t* v0,uint64_t* v1,uint64_t* v2,uint64_t* v3,uint64_t* v4,uint64_t* v5,uint64_t* v6,uint64_t* v7,
                         uint64_t* v8,uint64_t* v9,uint64_t* v10,uint64_t* v11,uint64_t* v12,uint64_t* v13,uint64_t* v14,uint64_t* v15) {
    HSH_A2G(*v0,*v4,*v8,*v12); HSH_A2G(*v1,*v5,*v9,*v13); HSH_A2G(*v2,*v6,*v10,*v14); HSH_A2G(*v3,*v7,*v11,*v15);
    HSH_A2G(*v0,*v5,*v10,*v15); HSH_A2G(*v1,*v6,*v11,*v12); HSH_A2G(*v2,*v7,*v8,*v13); HSH_A2G(*v3,*v4,*v9,*v14);
}
static void hsh_a2_fill(uint64_t* next, const uint64_t* prev, const uint64_t* ref, int with_xor) {
    uint64_t R[HSH_A2_BLK], T[HSH_A2_BLK];
    for (int i = 0; i < HSH_A2_BLK; i++) R[i] = ref[i] ^ prev[i];
    memcpy(T, R, sizeof(R));
    if (with_xor) for (int i = 0; i < HSH_A2_BLK; i++) T[i] ^= next[i];
    for (int i = 0; i < 8; i++) { uint64_t* b = R + 16*i;
        hsh_a2_round(&b[0],&b[1],&b[2],&b[3],&b[4],&b[5],&b[6],&b[7],&b[8],&b[9],&b[10],&b[11],&b[12],&b[13],&b[14],&b[15]); }
    for (int i = 0; i < 8; i++)
        hsh_a2_round(&R[2*i],&R[2*i+1],&R[2*i+16],&R[2*i+17],&R[2*i+32],&R[2*i+33],&R[2*i+48],&R[2*i+49],
                     &R[2*i+64],&R[2*i+65],&R[2*i+80],&R[2*i+81],&R[2*i+96],&R[2*i+97],&R[2*i+112],&R[2*i+113]);
    for (int i = 0; i < HSH_A2_BLK; i++) next[i] = T[i] ^ R[i];
}
static void hsh_a2_next_addr(uint64_t* addr, uint64_t* in) {
    uint64_t zero[HSH_A2_BLK] = {0};
    in[6]++;
    hsh_a2_fill(addr, zero, in, 0);
    hsh_a2_fill(addr, zero, addr, 0);
}
/* returns 0 ok */
static int hsh_argon2id_raw(const uint8_t* pw, size_t pwl, const uint8_t* salt, size_t sl,
                            uint32_t t_cost, uint32_t m_cost, uint32_t lanes, uint8_t* out, size_t outlen) {
    if (lanes < 1 || t_cost < 1 || m_cost < 8 * lanes) return -1;
    uint32_t mblocks = (m_cost / (4 * lanes)) * (4 * lanes);
    uint32_t lane_len = mblocks / lanes, seg_len = lane_len / 4;
    uint64_t* mem = (uint64_t*)malloc((size_t)mblocks * 1024);
    if (!mem) return -1;
    /* H0 */
    uint8_t h0in_hdr[24]; uint32_t hv[6] = { lanes, (uint32_t)outlen, m_cost, t_cost, 0x13, 2 };
    for (int i = 0; i < 6; i++) for (int j = 0; j < 4; j++) h0in_hdr[4*i+j] = (uint8_t)(hv[i] >> (8*j));
    HshB2 hc; hsh_b2_init(&hc, 64); hsh_b2_update(&hc, h0in_hdr, 24);
    uint8_t l4[4];
    #define HSH_A2_LE(v) do { l4[0]=(uint8_t)(v); l4[1]=(uint8_t)((v)>>8); l4[2]=(uint8_t)((v)>>16); l4[3]=(uint8_t)((v)>>24); hsh_b2_update(&hc, l4, 4); } while (0)
    HSH_A2_LE((uint32_t)pwl); hsh_b2_update(&hc, pw, pwl);
    HSH_A2_LE((uint32_t)sl);  hsh_b2_update(&hc, salt, sl);
    HSH_A2_LE(0u); HSH_A2_LE(0u); /* no secret, no associated data */
    uint8_t h0[72]; hsh_b2_final(&hc, h0);
    for (uint32_t l = 0; l < lanes; l++) for (uint32_t i = 0; i < 2; i++) {
        h0[64] = (uint8_t)i; h0[65] = h0[66] = h0[67] = 0;
        h0[68] = (uint8_t)l; h0[69] = (uint8_t)(l >> 8); h0[70] = (uint8_t)(l >> 16); h0[71] = (uint8_t)(l >> 24);
        uint8_t blk[1024]; hsh_a2_hprime(blk, 1024, h0, 72);
        uint64_t* dst = mem + ((size_t)l * lane_len + i) * HSH_A2_BLK;
        for (int w = 0; w < HSH_A2_BLK; w++) { dst[w] = 0; for (int j = 7; j >= 0; j--) dst[w] = (dst[w] << 8) | blk[8*w+j]; }
    }
    for (uint32_t pass = 0; pass < t_cost; pass++) for (uint32_t slice = 0; slice < 4; slice++) for (uint32_t lane = 0; lane < lanes; lane++) {
        int indep = (pass == 0 && slice < 2);
        uint64_t in[HSH_A2_BLK] = {0}, addr[HSH_A2_BLK] = {0};
        in[0] = pass; in[1] = lane; in[2] = slice; in[3] = mblocks; in[4] = t_cost; in[5] = 2;
        uint32_t start = 0;
        if (pass == 0 && slice == 0) { start = 2; if (indep) hsh_a2_next_addr(addr, in); }
        size_t cur = (size_t)lane * lane_len + (size_t)slice * seg_len + start;
        size_t prv = (cur % lane_len == 0) ? cur + lane_len - 1 : cur - 1;
        for (uint32_t i = start; i < seg_len; i++, cur++, prv++) {
            if (cur % lane_len == 1) prv = cur - 1;
            uint64_t rnd;
            if (indep) { if (i % 128 == 0) hsh_a2_next_addr(addr, in); rnd = addr[i % 128]; }
            else rnd = mem[prv * HSH_A2_BLK];
            uint32_t rlane = (uint32_t)((rnd >> 32) % lanes);
            if (pass == 0 && slice == 0) rlane = lane;
            int same = (rlane == lane);
            int64_t area;
            if (pass == 0) {
                if (slice == 0) area = (int64_t)i - 1;
                else if (same)  area = (int64_t)slice * seg_len + i - 1;
                else            area = (int64_t)slice * seg_len + (i == 0 ? -1 : 0);
            } else {
                if (same) area = (int64_t)lane_len - seg_len + i - 1;
                else      area = (int64_t)lane_len - seg_len + (i == 0 ? -1 : 0);
            }
            uint64_t rel = rnd & 0xFFFFFFFFULL;
            rel = (rel * rel) >> 32;
            rel = (uint64_t)area - 1 - (((uint64_t)area * rel) >> 32);
            uint64_t startpos = 0;
            if (pass != 0) startpos = (slice == 3) ? 0 : (uint64_t)(slice + 1) * seg_len;
            size_t refidx = (size_t)((startpos + rel) % lane_len);
            hsh_a2_fill(mem + cur * HSH_A2_BLK, mem + prv * HSH_A2_BLK, mem + ((size_t)rlane * lane_len + refidx) * HSH_A2_BLK, pass != 0);
        }
    }
    uint64_t fin[HSH_A2_BLK];
    memcpy(fin, mem + ((size_t)0 * lane_len + lane_len - 1) * HSH_A2_BLK, 1024);
    for (uint32_t l = 1; l < lanes; l++) {
        const uint64_t* b = mem + ((size_t)l * lane_len + lane_len - 1) * HSH_A2_BLK;
        for (int w = 0; w < HSH_A2_BLK; w++) fin[w] ^= b[w];
    }
    uint8_t fb[1024];
    for (int w = 0; w < HSH_A2_BLK; w++) for (int j = 0; j < 8; j++) fb[8*w+j] = (uint8_t)(fin[w] >> (8*j));
    hsh_a2_hprime(out, outlen, fb, 1024);
    memset(mem, 0, (size_t)mblocks * 1024);
    free(mem);
    return 0;
}

static const char hsh_cr_b64_tab[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static size_t hsh_cr_b64_enc_nopad(const uint8_t* d, size_t n, char* o) {
    size_t w = 0, i = 0;
    for (; i + 2 < n; i += 3) {
        uint32_t v = ((uint32_t)d[i] << 16) | ((uint32_t)d[i+1] << 8) | d[i+2];
        o[w++] = hsh_cr_b64_tab[v >> 18]; o[w++] = hsh_cr_b64_tab[(v >> 12) & 63]; o[w++] = hsh_cr_b64_tab[(v >> 6) & 63]; o[w++] = hsh_cr_b64_tab[v & 63];
    }
    if (n - i == 1) { uint32_t v = (uint32_t)d[i] << 16; o[w++] = hsh_cr_b64_tab[v >> 18]; o[w++] = hsh_cr_b64_tab[(v >> 12) & 63]; }
    else if (n - i == 2) { uint32_t v = ((uint32_t)d[i] << 16) | ((uint32_t)d[i+1] << 8);
        o[w++] = hsh_cr_b64_tab[v >> 18]; o[w++] = hsh_cr_b64_tab[(v >> 12) & 63]; o[w++] = hsh_cr_b64_tab[(v >> 6) & 63]; }
    o[w] = '\0'; return w;
}
static int hsh_cr_b64_val(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}
static int hsh_cr_b64_dec_nopad(const char* s, size_t sl, uint8_t* o, size_t* ol) {
    uint32_t acc = 0; int bits = 0; size_t w = 0;
    for (size_t i = 0; i < sl; i++) {
        int v = hsh_cr_b64_val(s[i]); if (v < 0) return -1;
        acc = (acc << 6) | (uint32_t)v; bits += 6;
        if (bits >= 8) { bits -= 8; o[w++] = (uint8_t)(acc >> bits); }
    }
    *ol = w; return 0;
}
/* Defaults of the `argon2` crate (m=19456 KiB, t=2, p=1, 32-byte tag, 16-byte salt). */
hsh_string hsh_crypto_argon2_hash(hsh_string pw) {
    uint8_t salt[16], tag[32];
    hsh_urandom(salt, 16);
    const uint32_t m = 19456, t = 2, p = 1;
    if (hsh_argon2id_raw((const uint8_t*)(pw ? pw : ""), pw ? strlen(pw) : 0, salt, 16, t, m, p, tag, 32) != 0) return "";
    char sb[32], hb[64]; hsh_cr_b64_enc_nopad(salt, 16, sb); hsh_cr_b64_enc_nopad(tag, 32, hb);
    char* o = (char*)hsh_alloc(160);
    if (!o) return "";
    snprintf(o, 160, "$argon2id$v=19$m=%u,t=%u,p=%u$%s$%s", m, t, p, sb, hb);
    return o;
}
int64_t hsh_crypto_argon2_verify(hsh_string pw, hsh_string hash) {
    if (!hash) return 0;
    unsigned m, t, p; int v = 19; char salt_b[128], hash_b[256];
    int n = sscanf(hash, "$argon2id$v=%d$m=%u,t=%u,p=%u$%127[^$]$%255s", &v, &m, &t, &p, salt_b, hash_b);
    if (n != 6 || v != 19 || m > (1u << 22) || p == 0 || p > 64) return 0;
    uint8_t salt[96], want[128], got[128]; size_t sl, wl;
    if (hsh_cr_b64_dec_nopad(salt_b, strlen(salt_b), salt, &sl) != 0 || sl > sizeof(salt)) return 0;
    if (hsh_cr_b64_dec_nopad(hash_b, strlen(hash_b), want, &wl) != 0 || wl < 4 || wl > sizeof(got)) return 0;
    if (hsh_argon2id_raw((const uint8_t*)(pw ? pw : ""), pw ? strlen(pw) : 0, salt, sl, t, m, p, got, wl) != 0) return 0;
    uint8_t diff = 0; for (size_t i = 0; i < wl; i++) diff |= got[i] ^ want[i];
    return diff == 0;
}

/* ── path:: (lexical, never touches the filesystem — mirrors Rust's
 *    std::path::Path as used by the interpreter) ───────────────────────── */
static char* hsh_p_dup(const char* s, size_t n) { return hsh_db_dup(s, n); }
/* length of `s` without trailing '/' (a path of only slashes keeps 0) */
static size_t hsh_p_trim_slash(const char* s, size_t n) { while (n > 0 && s[n-1] == '/') n--; return n; }
/* drops trailing "/." components too (Rust treats `a/.` as `a`) */
static size_t hsh_p_trim_tail(const char* s, size_t n) {
    for (;;) {
        n = hsh_p_trim_slash(s, n);
        if (n >= 2 && s[n-1] == '.' && s[n-2] == '/') { n -= 2; continue; }
        if (n == 1 && s[0] == '.') return 0;
        return n;
    }
}
hsh_string hsh_path_join(hsh_string a, hsh_string b) {
    if (!a) a = "";
    if (!b) b = "";
    if (b[0] == '/' || a[0] == '\0') return hsh_p_dup(b, strlen(b));
    size_t al = strlen(a), bl = strlen(b);
    int slash = (a[al-1] != '/');
    char* o = (char*)hsh_alloc((uint64_t)(al + bl + 2));
    if (!o) return "";
    memcpy(o, a, al); if (slash) o[al++] = '/';
    memcpy(o + al, b, bl + 1);
    return o;
}
static void hsh_p_filename(const char* p, const char** name, size_t* nl) {
    size_t n = hsh_p_trim_tail(p, strlen(p));
    size_t s = n; while (s > 0 && p[s-1] != '/') s--;
    *name = p + s; *nl = n - s;
    if (*nl == 2 && (*name)[0] == '.' && (*name)[1] == '.') *nl = 0;
}
hsh_string hsh_path_filename(hsh_string p) {
    if (!p) return "";
    const char* nm; size_t nl; hsh_p_filename(p, &nm, &nl); return hsh_p_dup(nm, nl);
}
/* index of the extension dot inside name, or -1 (a leading dot is part of the stem) */
static long hsh_p_dot(const char* nm, size_t nl) {
    for (long i = (long)nl - 1; i > 0; i--) if (nm[i] == '.') return i;
    return -1;
}
hsh_string hsh_path_stem(hsh_string p) {
    if (!p) return "";
    const char* nm; size_t nl; hsh_p_filename(p, &nm, &nl);
    long d = hsh_p_dot(nm, nl); return hsh_p_dup(nm, d < 0 ? nl : (size_t)d);
}
hsh_string hsh_path_extension(hsh_string p) {
    if (!p) return "";
    const char* nm; size_t nl; hsh_p_filename(p, &nm, &nl);
    long d = hsh_p_dot(nm, nl); return d < 0 ? "" : hsh_p_dup(nm + d + 1, nl - (size_t)d - 1);
}
hsh_string hsh_path_parent(hsh_string p) {
    if (!p || !*p) return "";
    size_t n = hsh_p_trim_tail(p, strlen(p));
    if (n == 0) return "";                       /* "/" , "." or "" -> no parent */
    size_t s = n; while (s > 0 && p[s-1] != '/') s--;
    if (s == 0) return "";                       /* single relative component */
    size_t e = hsh_p_trim_slash(p, s);
    if (e == 0) return "/";                      /* "/a" -> "/" */
    return hsh_p_dup(p, e);
}
int64_t hsh_path_is_absolute(hsh_string p) { return p && p[0] == '/'; }
hsh_string hsh_path_normalize(hsh_string p) {
    if (!p) return "";
    size_t n = strlen(p);
    char** seg = (char**)calloc(n + 2, sizeof(char*)); size_t ns = 0; int root = (n > 0 && p[0] == '/');
    int have_root = root;
    size_t i = 0;
    while (i < n) {
        while (i < n && p[i] == '/') i++;
        size_t st = i; while (i < n && p[i] != '/') i++;
        size_t l = i - st; if (l == 0) continue;
        if (l == 1 && p[st] == '.') continue;
        if (l == 2 && p[st] == '.' && p[st+1] == '.') { if (ns > 0) free(seg[--ns]); else have_root = 0; continue; }
        seg[ns++] = strndup(p + st, l);
    }
    size_t cap = n + 2; char* o = (char*)hsh_alloc((uint64_t)cap); size_t w = 0;
    if (!o) { for (size_t k = 0; k < ns; k++) free(seg[k]); free(seg); return ""; }
    if (have_root) o[w++] = '/';
    for (size_t k = 0; k < ns; k++) { if (k) o[w++] = '/'; size_t l = strlen(seg[k]); memcpy(o + w, seg[k], l); w += l; free(seg[k]); }
    o[w] = '\0'; free(seg);
    return o;
}
hsh_string hsh_path_with_extension(hsh_string p, hsh_string ext) {
    if (!p) return "";
    if (!ext) ext = "";
    const char* nm; size_t nl; hsh_p_filename(p, &nm, &nl);
    if (nl == 0) return hsh_p_dup(p, strlen(p));
    long d = hsh_p_dot(nm, nl); size_t stem = d < 0 ? nl : (size_t)d;
    size_t pre = (size_t)(nm - p), el = strlen(ext);
    char* o = (char*)hsh_alloc((uint64_t)(pre + stem + el + 2)); size_t w = 0;
    if (!o) return "";
    memcpy(o, p, pre); w = pre; memcpy(o + w, nm, stem); w += stem;
    if (el) { o[w++] = '.'; memcpy(o + w, ext, el); w += el; }
    o[w] = '\0'; return o;
}

/* ── os:: additions ────────────────────────────────────────────────────── */
hsh_string hsh_os_home_dir(void) { const char* h = getenv("HOME");
    return h ? hsh_p_dup(h, strlen(h)) : ""; }
hsh_string hsh_os_temp_dir(void) { const char* t = getenv("TMPDIR");
    if (!t || !*t) t = "/tmp";
    return hsh_p_dup(t, strlen(t)); }
int64_t    hsh_os_is_root(void)  { return getuid() == 0; }

/* ── sort:: — in place AND returns the same array, so both call styles work:
 *    `sort::sort_ints(a)`  (statement, as the std doc says "in-place") and
 *    `a = sort::sort_ints(a)`. ─────────────────────────────────────────── */
static int hsh_cmp_i64(const void* a, const void* b) { int64_t x = *(const int64_t*)a, y = *(const int64_t*)b; return (x > y) - (x < y); }
HshArray* hsh_sort_ints(HshArray* a) {
    if (!a) return hsh_array_new();
    if (a->len > 1) qsort(a->data, (size_t)a->len, sizeof(int64_t), hsh_cmp_i64);
    return a;
}
typedef int64_t (*HshCmpFn)(int64_t, int64_t);
static void hsh_msort(int64_t* d, int64_t* tmp, int64_t n, HshCmpFn f) {
    if (n < 2) return;
    int64_t m = n / 2;
    hsh_msort(d, tmp, m, f); hsh_msort(d + m, tmp, n - m, f);
    int64_t i = 0, j = m, k = 0;
    while (i < m && j < n) tmp[k++] = (f(d[i], d[j]) > 0) ? d[j++] : d[i++];   /* stable */
    while (i < m) tmp[k++] = d[i++];
    while (j < n) tmp[k++] = d[j++];
    memcpy(d, tmp, (size_t)n * sizeof(int64_t));
}
/* sort_by(arr, cmp): cmp(a, b) > 0 means a goes after b. Stable. `cmp` is a plain
 * (named) function pointer; closure literals are not supported on this backend. */
HshArray* hsh_sort_by(HshArray* a, HshCmpFn f) {
    if (!a) return hsh_array_new();
    if (!f || a->len < 2) return a;
    int64_t* tmp = (int64_t*)malloc((size_t)a->len * sizeof(int64_t));
    if (!tmp) return a;
    hsh_msort(a->data, tmp, a->len, f);
    free(tmp);
    return a;
}
/* sort_by_key(arr, key_fn): keys are compared as strings when both look like
 * pointers and as signed ints otherwise (same magnitude test hsh_val_to_str uses —
 * an `any` slot carries no runtime tag on this backend). Stable. */
static int hsh_looks_ptr(int64_t v) { return (uint64_t)v > 0x10000ULL && (uint64_t)v < 0x7ffffffffffeULL; }
HshArray* hsh_sort_by_key(HshArray* a, int64_t (*key)(int64_t)) {
    if (!a) return hsh_array_new();
    if (!key || a->len < 2) return a;
    int64_t n = a->len;
    int64_t* keys = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    int64_t* idx  = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    int64_t* out  = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    if (!keys || !idx || !out) { free(keys); free(idx); free(out); return a; }
    for (int64_t i = 0; i < n; i++) { keys[i] = key(a->data[i]); idx[i] = i; }
    /* stable insertion sort on idx (arrays handled here are small: lists of packages/files) */
    for (int64_t i = 1; i < n; i++) {
        int64_t cur = idx[i], j = i;
        while (j > 0) {
            int64_t k1 = keys[idx[j-1]], k2 = keys[cur];
            int gt = (hsh_looks_ptr(k1) && hsh_looks_ptr(k2)) ? (strcmp((const char*)(uintptr_t)k1, (const char*)(uintptr_t)k2) > 0) : (k1 > k2);
            if (!gt) break;
            idx[j] = idx[j-1]; j--;
        }
        idx[j] = cur;
    }
    for (int64_t i = 0; i < n; i++) out[i] = a->data[idx[i]];
    memcpy(a->data, out, (size_t)n * sizeof(int64_t));
    free(keys); free(idx); free(out);
    return a;
}

/* proc::run_cmd(cmd, timeout_secs) / proc::run_cmd_live(cmd, timeout_secs)
 * — run `cmd` through /bin/sh, capturing stdout and stderr *separately*
 * (unlike hsh_shell above, which only gives combined stdout and
 * silently drops the child's real exit status).
 *
 * ABI shape, deliberately simple: `hsh_run_cmd_exec` takes the command
 * + timeout and returns just the exit code (a plain i64 — no struct-
 * return or out-params, so codegen only needs the same "declare a C
 * function, call it" pattern already used for every other builtin
 * here); stdout/stderr are stashed in the two globals below and read
 * back by the separate zero-arg getters `hsh_run_cmd_last_stdout` /
 * `hsh_run_cmd_last_stderr`. The H# side (see
 * compiler/src/stdlib_shims.rs) calls all three back-to-back and packs
 * the results into a real `ProcResult` struct via an ordinary struct
 * literal — so the *only* new runtime ABI surface is three functions
 * with plain scalar/string args and returns, each independently as
 * simple as `hsh_shell` already is.
 *
 * Caveat that comes with the "last call" global-storage design: not
 * reentrant/thread-safe (a second run_cmd before reading the first's
 * result would clobber it). Fine for H#'s current single-threaded
 * runtime and for how getit actually calls it (always read
 * immediately, sequentially) — flagged here for whoever adds real
 * threading later.
 *
 * Timeout: `timeout_secs <= 0` means "no timeout". On timeout the
 * child gets SIGKILL and the returned exit code is -2. If the command
 * can't even be started (fork/pipe failure), the returned exit code is
 * -1 and both stdout/stderr read back as "".
 */
static char* g_hsh_run_cmd_stdout = NULL;
static char* g_hsh_run_cmd_stderr = NULL;

int64_t hsh_run_cmd_exec(hsh_string cmd, int64_t timeout_secs) {
    free(g_hsh_run_cmd_stdout); g_hsh_run_cmd_stdout = strdup("");
    free(g_hsh_run_cmd_stderr); g_hsh_run_cmd_stderr = strdup("");
    if (!cmd) return -1;

    int out_pipe[2], err_pipe[2];
    if (pipe(out_pipe) != 0) return -1;
    if (pipe(err_pipe) != 0) { close(out_pipe[0]); close(out_pipe[1]); return -1; }

    pid_t pid = fork();
    if (pid < 0) {
        close(out_pipe[0]); close(out_pipe[1]);
        close(err_pipe[0]); close(err_pipe[1]);
        return -1;
    }
    if (pid == 0) {
        dup2(out_pipe[1], STDOUT_FILENO);
        dup2(err_pipe[1], STDERR_FILENO);
        close(out_pipe[0]); close(out_pipe[1]);
        close(err_pipe[0]); close(err_pipe[1]);
        execl("/bin/sh", "sh", "-c", cmd, (char*)NULL);
        _exit(127);
    }
    close(out_pipe[1]);
    close(err_pipe[1]);

    int status = 0;
    int64_t exit_code;
    if (timeout_secs <= 0) {
        waitpid(pid, &status, 0);
        exit_code = WIFEXITED(status) ? WEXITSTATUS(status) : -1;
    } else {
        time_t deadline = time(NULL) + (time_t)timeout_secs;
        int killed = 0;
        for (;;) {
            pid_t r = waitpid(pid, &status, WNOHANG);
            if (r == pid) break;
            if (time(NULL) >= deadline) {
                kill(pid, SIGKILL);
                waitpid(pid, &status, 0);
                killed = 1;
                break;
            }
            struct timespec ts = { 0, 50 * 1000 * 1000 }; /* 50ms poll */
            nanosleep(&ts, NULL);
        }
        exit_code = killed ? -2 : (WIFEXITED(status) ? WEXITSTATUS(status) : -1);
    }

    free(g_hsh_run_cmd_stdout);
    free(g_hsh_run_cmd_stderr);
    g_hsh_run_cmd_stdout = hsh_drain_fd(out_pipe[0]);
    g_hsh_run_cmd_stderr = hsh_drain_fd(err_pipe[0]);
    close(out_pipe[0]);
    close(err_pipe[0]);
    return exit_code;
}

hsh_string hsh_run_cmd_last_stdout(void) {
    return g_hsh_run_cmd_stdout ? g_hsh_run_cmd_stdout : "";
}

hsh_string hsh_run_cmd_last_stderr(void) {
    return g_hsh_run_cmd_stderr ? g_hsh_run_cmd_stderr : "";
}

/* str::split(s, sep) — `hsh_str_split_count` returns how many parts `s`
 * splits into on `sep`, `hsh_str_split_part` returns the i-th part
 * (0-indexed). Deliberately two simple scalar-return functions instead
 * of one that returns an array — same reasoning as `hsh_run_cmd_exec`
 * above: constructing a runtime `HshArray` correctly from C means
 * matching its exact boxing/tagging layout, which I can't verify against
 * the real LLVM-side array codegen without LLVM in this environment. See
 * `stdlib_shims.rs`'s `str_split` for the H# wrapper that loops these
 * into a real `[string]` using the *already-existing, already-verified*
 * `.push()` array-building codegen instead.
 *
 * Recomputes the split from scratch on every `_part` call — O(n) per
 * call, O(n^2) for a full loop over all parts. Deliberately fine: every
 * real call site in getit splits short strings (URLs, HTTP header
 * lines, file paths), not megabyte payloads.
 *
 * Empty `sep` splits between every byte (mirrors Rust's `str::split`
 * behavior, which is what the interpreter's `"split"` arm in
 * `interpreter/src/call.rs` uses under the hood — kept consistent so a
 * program behaves the same whether run via `hsharp compile` or
 * `hsharp preview`/`hsharp repl`). Not hit by any getit call site
 * (every separator there is non-empty: "?", "/", "\n", ":", " ").
 */
int64_t hsh_str_split_count(hsh_string s, hsh_string sep) {
    if (!s) return 0;
    if (!sep || sep[0] == '\0') {
        size_t n = strlen(s);
        return (int64_t)(n == 0 ? 1 : n);
    }
    size_t seplen = strlen(sep);
    int64_t count = 1;
    const char* p = s;
    const char* hit;
    while ((hit = strstr(p, sep)) != NULL) {
        count++;
        p = hit + seplen;
    }
    return count;
}

hsh_string hsh_str_split_part(hsh_string s, hsh_string sep, int64_t index) {
    if (!s || index < 0) return "";
    if (!sep || sep[0] == '\0') {
        size_t n = strlen(s);
        if ((size_t)index >= n) return "";
        char* out = (char*)hsh_alloc(2);
        out[0] = s[index];
        out[1] = '\0';
        return out;
    }
    size_t seplen = strlen(sep);
    const char* p = s;
    int64_t cur = 0;
    for (;;) {
        const char* hit = strstr(p, sep);
        const char* part_end = hit ? hit : p + strlen(p);
        if (cur == index) {
            size_t len = (size_t)(part_end - p);
            char* out = (char*)hsh_alloc(len + 1);
            memcpy(out, p, len);
            out[len] = '\0';
            return out;
        }
        if (!hit) return ""; /* index out of range */
        p = hit + seplen;
        cur++;
    }
}

/* fs::remove_dir(path) — recursive directory removal. Deliberately shells
 * out to `rm -rf` (via the already-existing, already-tested
 * hsh_shell_escape for safe quoting) rather than hand-rolling a
 * recursive nftw()-based walk-and-unlink in C: `rm -rf` is a single,
 * extremely well-tested syscall-sequence that's much less likely to
 * have an edge-case bug (symlinks, permission-denied subdirs, ENOTEMPTY
 * races) than a from-scratch reimplementation would be — the same
 * "prefer battle-tested existing tools over new risky C" reasoning as
 * hsh_run_cmd_exec using `/bin/sh -c` instead of trying to reimplement
 * shell parsing.
 */
int64_t hsh_remove_dir_recursive(hsh_string path) {
    if (!path || path[0] == '\0') return 0;
    char* quoted = (char*)hsh_shell_escape(path);
    size_t cmdlen = strlen(quoted) + 16;
    char* cmd = (char*)malloc(cmdlen);
    if (!cmd) { free(quoted); return 0; }
    snprintf(cmd, cmdlen, "rm -rf %s", quoted);
    int rc = system(cmd);
    free(cmd);
    free(quoted);
    return (rc == 0) ? 1 : 0;
}

/* conv::int_to_str / conv::str_to_int */
hsh_string hsh_int_to_str(int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
    char* out = (char*)hsh_alloc((size_t)len + 1);
    memcpy(out, buf, (size_t)len + 1);
    return out;
}

int64_t hsh_str_to_int(hsh_string s) {
    if (!s) return 0;
    /* strtoll skips leading whitespace and stops at the first non-digit
     * (matches how getit always calls this after str::trim anyway), and
     * returns 0 on a string with no valid digits — never crashes on
     * garbage input, unlike atoll's undefined behavior on overflow. */
    return (int64_t)strtoll(s, NULL, 10);
}

/* Bare `parse_int(s)`: the Option-shaped sibling of hsh_str_to_int. The interpreter
 * returns `nil` unless the WHOLE string is a base-10 i64 (optional +/- sign, no
 * whitespace — exactly Rust's `str::parse::<i64>`). An `int?` is a plain i64 on this
 * backend and `nil` is 0, so a failed parse yields 0 — which means a successfully
 * parsed "0" is indistinguishable from nil here (callers use `parse_int_or`-style
 * defaults / 1-based menu indices, where that is harmless). */
int64_t hsh_parse_int_opt(hsh_string s) {
    if (!s || !*s) return 0;
    const char* p = s;
    int neg = 0;
    if (*p == '+' || *p == '-') { neg = (*p == '-'); p++; }
    if (!*p) return 0;
    unsigned long long acc = 0;
    for (; *p; p++) {
        if (*p < '0' || *p > '9') return 0;
        unsigned d = (unsigned)(*p - '0');
        if (acc > (0x7fffffffffffffffULL - d) / 10ULL + (neg ? 1ULL : 0ULL)) return 0; /* overflow */
        acc = acc * 10ULL + d;
    }
    if (!neg && acc > 0x7fffffffffffffffULL) return 0;
    if (neg && acc > 0x8000000000000000ULL) return 0;
    return neg ? (int64_t)(0ULL - acc) : (int64_t)acc;
}

/* conv::int_to_hex(n) — lowercase hex, no "0x" prefix (matches the
 * interpreter's formatting). Added this session. */
hsh_string hsh_conv_int_to_hex(int64_t n) {
    char buf[20];
    int len = snprintf(buf, sizeof(buf), "%llx", (unsigned long long)n);
    char* out = (char*)hsh_alloc((size_t)len + 1);
    if (!out) return "";
    memcpy(out, buf, (size_t)len + 1);
    return out;
}

/* conv::float_to_int(f) — truncating (toward zero), matching C's
 * float-to-int cast semantics and the interpreter's `as i64`. Added
 * this session. */
int64_t hsh_conv_float_to_int(double f) {
    return (int64_t)f;
}

/* env::get(name) — "" if unset, matching every other "absent value"
 * convention in this runtime (hsh_json_get, hsh_run_cmd_last_stdout, …
 * all return "" rather than a null pointer H# code would have to
 * null-check). */
hsh_string hsh_env_get(hsh_string name) {
    if (!name) return "";
    const char* v = getenv(name);
    return v ? v : "";
}

/* env::read_line() — one line from stdin, newline stripped (matches
 * every interactive y/n prompt getit uses this for — see
 * `str::to_lower(answer) != "y"`, which would never match "y\n"). EOF
 * or a read error returns "". */
hsh_string hsh_env_read_line(void) {
    char buf[4096];
    if (!fgets(buf, sizeof(buf), stdin)) return "";
    size_t n = strlen(buf);
    while (n > 0 && (buf[n-1] == '\n' || buf[n-1] == '\r')) buf[--n] = '\0';
    char* out = (char*)hsh_alloc(n + 1);
    memcpy(out, buf, n + 1);
    return out;
}

/* io::read_char() — one raw byte from stdin as a 1-character string,
 * "" on EOF or a read error. Added this session (previously interpreter
 * only — see builtins_registry.rs's matching BuiltinSpec). */
hsh_string hsh_io_read_char(void) {
    int c = getchar();
    if (c == EOF) return "";
    char* out = (char*)hsh_alloc(2);
    if (!out) return "";
    out[0] = (char)c;
    out[1] = '\0';
    return out;
}

/* json::set_str(json, key, val) — insert-or-replace a `"key":"value"`
 * entry in a *flat* JSON object string (same "not a full JSON parser,
 * handles simple flat objects" scope as hsh_json_get above — getit only
 * ever uses this for a single-level etag cache, see stdlib_shims.rs's
 * `json` type-alias doc comment for the full design rationale). Always
 * returns well-formed flat JSON: `{}` in, `{"k":"v"}` out; `{"a":"1"}`
 * + set b→2 → `{"a":"1","b":"2"}`; `{"a":"1"}` + set a→2 →
 * `{"a":"2"}`. Values are stored as JSON strings (quoted) regardless of
 * their H# type, matching `json_get_str`'s name — this is a
 * string-keyed string-value cache, not a general JSON value store. */
hsh_string hsh_json_set_str(hsh_string json, hsh_string key, hsh_string val) {
    if (!key) key = "";
    if (!val) val = "";
    if (!json || json[0] == '\0') json = "{}";

    size_t klen = strlen(key);
    char* pattern = (char*)malloc(klen + 4);
    pattern[0] = '"'; memcpy(pattern + 1, key, klen);
    pattern[klen+1] = '"'; pattern[klen+2] = ':'; pattern[klen+3] = '\0';
    const char* hit = strstr(json, pattern);
    free(pattern);

    size_t jlen = strlen(json);
    size_t vlen = strlen(val);
    /* room for: existing object + new entry + quotes/commas/braces,
     * generously over-allocated (exact accounting isn't worth the risk
     * of an off-by-one here — a few extra bytes of slack is free). */
    char* out = (char*)hsh_alloc(jlen + klen + vlen + 32);
    size_t w = 0;

    if (hit) {
        /* Replace existing "key":"...value..." span with the new value. */
        size_t prefix_len = (size_t)(hit - json);
        memcpy(out + w, json, prefix_len); w += prefix_len;
        w += (size_t)snprintf(out + w, klen + vlen + 8, "\"%s\":\"%s\"", key, val);
        const char* after_key = hit + klen + 3; /* skip "key": */
        while (*after_key == ' ' || *after_key == '\t') after_key++;
        const char* value_end;
        if (*after_key == '"') {
            value_end = strchr(after_key + 1, '"');
            value_end = value_end ? value_end + 1 : after_key + strlen(after_key);
        } else {
            value_end = after_key;
            while (*value_end && *value_end != ',' && *value_end != '}') value_end++;
        }
        size_t suffix_len = strlen(value_end);
        memcpy(out + w, value_end, suffix_len + 1); w += suffix_len;
    } else {
        /* Insert a new entry just before the closing '}'. */
        const char* close = strrchr(json, '}');
        size_t body_len = close ? (size_t)(close - json) : jlen;
        int is_empty = 1;
        for (size_t i = 1; i < body_len; i++) {
            if (json[i] != ' ' && json[i] != '\t' && json[i] != '\n') { is_empty = 0; break; }
        }
        memcpy(out + w, json, body_len); w += body_len;
        if (!is_empty) { out[w++] = ','; }
        w += (size_t)snprintf(out + w, klen + vlen + 8, "\"%s\":\"%s\"", key, val);
        out[w++] = '}';
        out[w] = '\0';
    }
    return out;
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

/* ── process:: v2 (added this session) ───────────────────────────────────── */

/* process::run_args(cmd, args: [string]) -> string. Builds a real
 * argv[] from `cmd` + the `[string]` array and runs it via the
 * existing fork+execvp `hsh_exec_argv` helper — no shell, no
 * injection, same contract as `exec(...)`. Capped at 63 extra args
 * (plenty for this runtime's purposes; a longer argv silently
 * truncates rather than overflowing the fixed-size buffer). */
hsh_string hsh_process_run_args(hsh_string cmd, HshArray *args) {
    if (!cmd) return "";
    enum { MAXA = 64 };
    char* argv[MAXA + 1];
    argv[0] = (char*)cmd;
    int n = 0;
    if (args) {
        n = (int)args->len;
        if (n > MAXA - 1) n = MAXA - 1;
        for (int i = 0; i < n; i++) argv[i + 1] = (char*)(uintptr_t)args->data[i];
    }
    argv[n + 1] = NULL;
    return hsh_exec_argv(argv);
}

/* process::spawn(cmd) -> int (pid). Backgrounds `cmd` via `/bin/sh -c`
 * (so pipes/redirects/&&/etc. in `cmd` still work, same shell contract
 * as `shell()`), does NOT wait for it, and does not capture its
 * output (inherits the parent's stdout/stderr — the natural behavior
 * for a detached background job). Returns -1 on fork failure. */
int64_t hsh_process_spawn(hsh_string cmd) {
    if (!cmd) return -1;
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        /* Detach from the controlling terminal's signal delivery, same
         * spirit as a real shell backgrounding a job with `&`. */
        setsid();
        execl("/bin/sh", "sh", "-c", cmd, (char*)NULL);
        _exit(127);
    }
    return (int64_t)pid;
}

/* process::kill(pid) -> bool. Sends SIGTERM (not SIGKILL) — same
 * "polite" default every other shell/process API uses, letting the
 * target clean up if it wants to. */
int64_t hsh_process_kill(int64_t pid) {
    return (kill((pid_t)pid, SIGTERM) == 0) ? 1 : 0;
}

/* process::which(cmd) -> string. Hand-rolled $PATH search (rather than
 * shelling out to a real `which`, which isn't guaranteed to exist on a
 * minimal container) — first `$PATH` entry where `cmd` exists and is
 * executable, "" if none. An already-qualified `cmd` (contains a `/`)
 * is checked directly instead of being searched for. */
hsh_string hsh_process_which(hsh_string cmd) {
    if (!cmd || cmd[0] == '\0') return "";
    if (strchr(cmd, '/')) {
        return (access(cmd, X_OK) == 0) ? strdup(cmd) : "";
    }
    const char* path_env = getenv("PATH");
    if (!path_env) return "";
    char* path_copy = strdup(path_env);
    if (!path_copy) return "";
    const char* result = "";
    char* saveptr = NULL;
    for (char* dir = strtok_r(path_copy, ":", &saveptr); dir; dir = strtok_r(NULL, ":", &saveptr)) {
        char full[4096];
        snprintf(full, sizeof(full), "%s/%s", dir, cmd);
        if (access(full, X_OK) == 0) {
            result = strdup(full);
            break;
        }
    }
    free(path_copy);
    return result;
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

/*
 * hsh_chdir(path) — change the process's current working directory.
 * Returns 1 on success, 0 on failure (missing/inaccessible path, not a
 * directory, permissions, etc. — errno is left set by chdir(2) for
 * whatever diagnostic use a caller might want, same as hsh_rename below
 * doesn't surface errno either; this matches that existing convention of
 * "a plain success/fail flag, not a full error channel").
 *
 * Previously `fs::chdir` was aliased straight to `fs_cwd` (i.e. it just
 * read and returned the cwd, silently doing nothing to actually change
 * it — see interpreter/src/helpers.rs's alias table, now fixed to point
 * at this real implementation instead of that no-op placeholder).
 */
int64_t hsh_chdir(hsh_string path) {
    return (path && chdir(path) == 0) ? 1 : 0;
}

int64_t hsh_rename(hsh_string from, hsh_string to) {
    return (from && to && rename(from, to) == 0) ? 1 : 0;
}

/* ── Filesystem v2 (added this session) ─────────────────────────────────────
 * fs::read_bytes / fs::write_bytes / fs::read_lines / fs::walk /
 * fs::modified_time / fs::temp_file / fs::list_dir / fs::copy / fs::rmdir —
 * see each's BuiltinSpec doc comment in builtins_registry.rs for the
 * "why" behind each design choice. All previously interpreter-only.
 */

/* fs::read_bytes(path) -> bytes. Binary-safe: reads the file's exact
 * byte count via fseek/ftell/fread rather than treating it as a C
 * string, so embedded NUL bytes survive (unlike hsh_read_file, which is
 * fine for text but would silently truncate at the first NUL if
 * something downstream ever called strlen() on its result). Returns an
 * HshArray* of byte values 0-255 — the exact same representation
 * hsh_string_to_bytes already uses for `bytes`. */
HshArray *hsh_fs_read_bytes(hsh_string path) {
    HshArray *out = hsh_array_new();
    if (!path) return out;
    FILE* f = fopen(path, "rb");
    if (!f) return out;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    if (sz <= 0) { fclose(f); return out; }
    unsigned char* buf = (unsigned char*)malloc((size_t)sz);
    if (!buf) { fclose(f); return out; }
    size_t got = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    for (size_t i = 0; i < got; i++) out = hsh_array_push(out, (int64_t)buf[i]);
    free(buf);
    return out;
}

/* fs::write_bytes(path, data: bytes) -> bool. Writes each element of
 * the HshArray* (masked to a byte, same convention hsh_bytes_to_string
 * already uses) via a single fwrite. */
int64_t hsh_fs_write_bytes(hsh_string path, HshArray *bytes) {
    if (!path) return 0;
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    if (bytes && bytes->len > 0) {
        unsigned char* buf = (unsigned char*)malloc((size_t)bytes->len);
        if (buf) {
            for (int64_t i = 0; i < bytes->len; i++) buf[i] = (unsigned char)(bytes->data[i] & 0xFF);
            fwrite(buf, 1, (size_t)bytes->len, f);
            free(buf);
        }
    }
    fclose(f);
    return 1;
}

/* fs::read_lines(path) -> [string]. Splits on '\n'; a trailing '\r' on
 * each line is stripped so CRLF files behave the same as LF-only ones
 * (matches every other line-oriented helper in this runtime — see
 * hsh_env_read_line above). A final line with no trailing newline is
 * still included, matching Rust's `str::lines()` (which this is a
 * straight port of the spirit of). */
HshArray *hsh_fs_read_lines(hsh_string path) {
    HshArray *out = hsh_array_new();
    if (!path) return out;
    FILE* f = fopen(path, "rb");
    if (!f) return out;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    if (sz < 0) { fclose(f); return out; }
    char* buf = (char*)malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return out; }
    size_t got = fread(buf, 1, (size_t)sz, f);
    fclose(f);
    buf[got] = '\0';
    size_t start = 0;
    for (size_t i = 0; i <= got; i++) {
        if (i == got || buf[i] == '\n') {
            if (i == got && i == start) break; /* no trailing empty line */
            size_t end = i;
            if (end > start && buf[end - 1] == '\r') end--;
            size_t len = end - start;
            char* line = (char*)hsh_alloc(len + 1);
            memcpy(line, buf + start, len);
            line[len] = '\0';
            out = hsh_array_push(out, (int64_t)(uintptr_t)line);
            start = i + 1;
        }
    }
    free(buf);
    return out;
}

/* fs::walk(root) -> [string]. Recursive depth-first directory walk,
 * yielding full paths of every regular file found (directories
 * themselves aren't yielded — matches the doc comment's "yields file
 * paths only"). Symlinks are not followed (lstat via readdir's d_type
 * where available, falling back to stat), to avoid infinite recursion
 * on a symlink cycle. */
static void hsh_fs_walk_into(const char* dir, HshArray** out) {
    DIR* d = opendir(dir);
    if (!d) return;
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        size_t dl = strlen(dir), nl = strlen(ent->d_name);
        char* path = (char*)malloc(dl + nl + 2);
        if (!path) continue;
        int need_slash = (dl > 0 && dir[dl - 1] != '/');
        snprintf(path, dl + nl + 2, "%s%s%s", dir, need_slash ? "/" : "", ent->d_name);
        struct stat st;
        if (lstat(path, &st) == 0) {
            if (S_ISDIR(st.st_mode)) {
                hsh_fs_walk_into(path, out);
                free(path);
            } else {
                char* kept = (char*)hsh_alloc(strlen(path) + 1);
                if (kept) { memcpy(kept, path, strlen(path) + 1); *out = hsh_array_push(*out, (int64_t)(uintptr_t)kept); }
                free(path);
            }
        } else {
            free(path);
        }
    }
    closedir(d);
}

HshArray *hsh_fs_walk(hsh_string root) {
    HshArray *out = hsh_array_new();
    if (!root) return out;
    hsh_fs_walk_into(root, &out);
    return out;
}

/* fs::list_dir(path) -> [string]. One level only (unlike fs::walk),
 * bare entry names (not full paths), "." and ".." excluded. */
HshArray *hsh_fs_list_dir(hsh_string path) {
    HshArray *out = hsh_array_new();
    if (!path) return out;
    DIR* d = opendir(path);
    if (!d) return out;
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        size_t n = strlen(ent->d_name);
        char* name = (char*)hsh_alloc(n + 1);
        if (name) { memcpy(name, ent->d_name, n + 1); out = hsh_array_push(out, (int64_t)(uintptr_t)name); }
    }
    closedir(d);
    return out;
}

/* fs::modified_time(path) -> int (unix seconds), -1 if the path
 * doesn't exist / stat fails. */
int64_t hsh_fs_modified_time(hsh_string path) {
    if (!path) return -1;
    struct stat st;
    return (stat(path, &st) == 0) ? (int64_t)st.st_mtime : -1;
}

/* fs::temp_file(prefix) -> string. Actually creates the file (via
 * mkstemp, so the name is guaranteed unique and reserved — not just a
 * generated name someone else could race), and returns its path.
 * "" on failure. */
hsh_string hsh_fs_temp_file(hsh_string prefix) {
    const char* dir = getenv("TMPDIR");
    if (!dir || dir[0] == '\0') dir = "/tmp";
    const char* pfx = prefix ? prefix : "hsh";
    char tmpl[4096];
    snprintf(tmpl, sizeof(tmpl), "%s/%sXXXXXX", dir, pfx);
    int fd = mkstemp(tmpl);
    if (fd < 0) return "";
    close(fd);
    size_t n = strlen(tmpl);
    char* out = (char*)hsh_alloc(n + 1);
    if (!out) return "";
    memcpy(out, tmpl, n + 1);
    return out;
}

/* fs::copy(src, dst) -> bool. Binary-safe (fread/fwrite by exact byte
 * count), unlike a text-based read+write which would go through
 * hsh_read_file/hsh_write_file's NUL-terminated-string assumptions. */
int64_t hsh_fs_copy(hsh_string src, hsh_string dst) {
    if (!src || !dst) return 0;
    FILE* in = fopen(src, "rb");
    if (!in) return 0;
    FILE* out = fopen(dst, "wb");
    if (!out) { fclose(in); return 0; }
    char buf[8192];
    size_t n;
    int ok = 1;
    while ((n = fread(buf, 1, sizeof(buf), in)) > 0) {
        if (fwrite(buf, 1, n, out) != n) { ok = 0; break; }
    }
    fclose(in);
    fclose(out);
    return ok;
}

/* std/test.h# helpers. __builtin_test_fail(msg): there is no separate test
 * runner on the AOT backend, so a failed assertion behaves exactly like the
 * interpreter's RuntimeError::Panic — message on stderr, exit code 1.
 * __builtin_test_skip(reason): like the interpreter, skipping is not a
 * failure; a note goes to stderr and execution continues (returns 1). */
int64_t hsh_test_fail(hsh_string msg) {
    fflush(stdout);
    fprintf(stderr, "test failed: %s\n", msg ? msg : "(no message)");
    exit(1);
    return 0;
}

int64_t hsh_test_skip(hsh_string reason) {
    fprintf(stderr, "test skipped: %s\n", reason ? reason : "(no reason)");
    return 1;
}

/* fs::rmdir(path) -> bool. Non-recursive — fails (returns 0) if the
 * directory isn't empty, deliberately NOT falling back to the
 * recursive hsh_remove_dir_recursive (see that BuiltinSpec's doc
 * comment: different, much more destructive semantics). */
int64_t hsh_fs_rmdir(hsh_string path) {
    return (path && rmdir(path) == 0) ? 1 : 0;
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
    snprintf(cmd, sizeof(cmd), "curl -s -L --max-time 15 -A 'H#/0.9' '%s' 2>/dev/null", url);
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
 * (struct layout itself now declared up near the top of this file — see
 * the comment there for why it moved.)
 */

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

/* strings::sort(arr) / the direct `__builtin_sort_strings(arr)` call —
 * alphabetical sort of a `[string]` array, following exactly the same
 * `HshArray*`-of-`char*` construction `hsh_env_args` above already does
 * (this comment intentionally repeats that one's layout note rather than
 * assuming the reader has it in view): each element of the array is an
 * `int64_t` that's really a `char*` in disguise, cast back for `strcmp`
 * and cast forward again into the result array. Sorts a fresh copy
 * (`qsort` in place on `data` after copying it out) rather than mutating
 * the input in place — H# arrays are otherwise treated as
 * copy-on-mutation values everywhere else in this runtime (see
 * `hsh_array_push`'s grow-and-copy behavior), so a sort that silently
 * reordered the caller's original backing storage would be the one
 * array operation that broke that convention. */
static int hsh_strcmp_for_qsort(const void* a, const void* b) {
    const char* sa = (const char*)(uintptr_t)(*(const int64_t*)a);
    const char* sb = (const char*)(uintptr_t)(*(const int64_t*)b);
    return strcmp(sa ? sa : "", sb ? sb : "");
}

HshArray *hsh_sort_strings(HshArray *a) {
    /* Sorts IN PLACE and returns the same array: std/sort.h# documents
     * "sort a string array in-place", and callers (hpm) call it as a bare
     * statement. It used to return a sorted *copy*, which made
     * `sort::sort_strings(xs)` a silent no-op on this backend. */
    if (!a) return hsh_array_new();
    if (a->len > 1) qsort(a->data, (size_t)a->len, sizeof(int64_t), hsh_strcmp_for_qsort);
    return a;
}

/* strings::split_whitespace(s) / the direct
 * `__builtin_str_split_whitespace(s)` call — splits on any run of
 * whitespace (space, tab, newline, CR — `isspace()`), discarding empty
 * fields between/around runs (so `"  a   b  "` is `["a", "b"]`, not
 * `["", "a", "", "", "b", ""]`) — the conventional meaning of "split on
 * whitespace" (matches Rust's `str::split_whitespace`, Python's
 * `str.split()` with no separator, etc.), as opposed to a delimiter
 * split that preserves empty fields. Each returned token is a fresh
 * `hsh_alloc`'d copy (never a pointer into the original `s`), consistent
 * with every other string-returning function in this runtime, since `s`
 * may be arena/caller-owned memory this array needs to outlive. */
HshArray *hsh_str_split_whitespace(hsh_string s) {
    HshArray *out = hsh_array_new();
    if (!s) return out;
    size_t i = 0, n = strlen(s);
    while (i < n) {
        while (i < n && isspace((unsigned char)s[i])) i++;
        if (i >= n) break;
        size_t start = i;
        while (i < n && !isspace((unsigned char)s[i])) i++;
        size_t len = i - start;
        char* tok = (char*)hsh_alloc(len + 1);
        memcpy(tok, s + start, len);
        tok[len] = '\0';
        out = hsh_array_push(out, (int64_t)(uintptr_t)tok);
    }
    return out;
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

/* EXPANSION: array-of-strings join — the counterpart `hsh_string_split`
 * never had. `.join(sep)` on `[string]` (e.g. `hsh`'s
 * `theme::theme_names().join(", ")`, `v.positional.join(" ")`,
 * `commands.join(",")`) had no LLVM backing at all before this; the
 * `MethodCall` dispatch in codegen.rs now routes `.join(sep)` here.
 * Treats every array element as a `char*` (cast back from the generic
 * i64 slot) — same "this container doesn't care what's in the slot"
 * convention as the rest of this runtime; a non-string element would
 * read garbage, exactly as e.g. `hsh_array_contains` would for a
 * mismatched element type, which is an existing, accepted trade-off in
 * this untyped-at-the-C-level runtime, not something new here. */
hsh_string hsh_array_join(HshArray *a, hsh_string sep) {
    if (!a || a->len == 0) return "";
    size_t seplen = sep ? strlen(sep) : 0;
    size_t total = 0;
    for (int64_t i = 0; i < a->len; i++) {
        const char *s = (const char*)(intptr_t)a->data[i];
        total += s ? strlen(s) : 0;
        if (i > 0) total += seplen;
    }
    char *out = (char*)malloc(total + 1);
    if (!out) return "";
    char *w = out;
    for (int64_t i = 0; i < a->len; i++) {
        if (i > 0 && seplen) { memcpy(w, sep, seplen); w += seplen; }
        const char *s = (const char*)(intptr_t)a->data[i];
        if (s) { size_t l = strlen(s); memcpy(w, s, l); w += l; }
    }
    *w = '\0';
    return out;
}

/* ── regex:: — grep/sed-backed regex support (native AOT support) ────────────
 * EXPANSION: was `Backend::Interpreter`-only. The interpreter itself
 * doesn't embed a real regex engine either — `hsharp-interpreter::call.rs`
 * implements every one of these by spawning `grep -P`/`sed -E` as a
 * subprocess and piping text through it (see its own extensive comments
 * on *why*: portable, no new dependency, and two prior security fixes —
 * a shell-injection hole in the old `sed` script construction, and an
 * `std::process::exit` that was an uncatchable WASM trap under the
 * playground target). This mirrors that exact approach for the AOT
 * backend, for two reasons: (1) it avoids re-implementing an actual
 * regex engine from scratch in C, which is a large amount of easy-to-
 * get-subtly-wrong surface area for a security-sensitive feature (`hsh`
 * uses this for *secret redaction* — `security.h#`'s `redact()`); (2) it
 * guarantees identical observable behavior between the interpreter and
 * the compiled binary — the same `grep -P`/`sed -E` binary, the same
 * flags, the same PCRE-flavored pattern syntax and its quirks either
 * way, rather than two independently-behaving regex implementations
 * that could silently diverge on some edge-case pattern.
 *
 * SECURITY: every subprocess here is spawned with `fork`+`execvp` and an
 * explicit argv array — never `system()`/`popen()` — so a pattern or
 * replacement string containing shell metacharacters (`;`, `$(...)`,
 * backticks, quotes, ...) is passed to `grep`/`sed` as a single literal
 * argv element, never interpreted by a shell. This is the same guarantee
 * Rust's `std::process::Command::new(...).args([...])` (no shell)
 * already gives the interpreter; a C implementation using `popen()`
 * would NOT have this guarantee (popen always runs `/bin/sh -c
 * "..."`), which is exactly why this doesn't use it.
 */

/* Runs `argv[0]` with `argv` (NULL-terminated), writes `input`
 * (`input_len` bytes) to its stdin, and captures all of its stdout into
 * a fresh `hsh_alloc`'d, NUL-terminated buffer (`*out_len` excludes the
 * NUL). Returns the child's exit status (like `system()`'s convention,
 * but from `waitpid`'s `WEXITSTATUS` — 0 typically means success), or
 * -1 if the child couldn't even be spawned (e.g. `grep`/`sed` missing
 * from `$PATH`) — callers treat -1 the same way the interpreter's own
 * `.map_err(...)` on a failed `spawn()` does: fall back to a safe
 * default rather than propagating a hard error, since a shell prompt or
 * a redaction filter failing outright on a machine missing `grep` is a
 * far worse failure mode than silently doing nothing. */
static int hsh_run_piped(char *const argv[], const char *input, size_t input_len,
                          char **out_buf, size_t *out_len) {
    int in_pipe[2];  /* parent writes[1] -> child reads[0] (child's stdin) */
    int out_pipe[2]; /* child writes[1] -> parent reads[0] (child's stdout) */
    *out_buf = NULL;
    *out_len = 0;
    if (pipe(in_pipe) != 0) return -1;
    if (pipe(out_pipe) != 0) { close(in_pipe[0]); close(in_pipe[1]); return -1; }

    pid_t pid = fork();
    if (pid < 0) {
        close(in_pipe[0]); close(in_pipe[1]); close(out_pipe[0]); close(out_pipe[1]);
        return -1;
    }
    if (pid == 0) {
        /* child */
        dup2(in_pipe[0], STDIN_FILENO);
        dup2(out_pipe[1], STDOUT_FILENO);
        close(in_pipe[0]);  close(in_pipe[1]);
        close(out_pipe[0]); close(out_pipe[1]);
        execvp(argv[0], argv);
        _exit(127); /* execvp failed (binary not found, etc.) */
    }
    /* parent */
    close(in_pipe[0]);
    close(out_pipe[1]);

    /* Write the input, then close so the child sees EOF on its stdin —
     * matters for `grep`/`sed`, which otherwise block waiting for more
     * input forever. A large `input` could in principle deadlock against
     * a child that fills its stdout pipe before we've finished writing
     * (classic pipe-both-directions deadlock) — real `grep`/`sed` on
     * shell-prompt/log-line/secret-scanning-sized text (this runtime's
     * actual use cases, never megabytes) never gets remotely close to a
     * full 64KB pipe buffer, so this keeps the simple
     * write-everything-then-read-everything shape rather than a
     * poll()-based one, matching the same trade-off the interpreter's
     * blocking `Write::write_all` + `wait_with_output()` already makes. */
    if (input && input_len > 0) {
        size_t written = 0;
        while (written < input_len) {
            ssize_t w = write(in_pipe[1], input + written, input_len - written);
            if (w <= 0) break;
            written += (size_t)w;
        }
    }
    close(in_pipe[1]);

    size_t cap = 4096, len = 0;
    char *buf = (char*)malloc(cap);
    if (buf) {
        for (;;) {
            if (len + 4096 > cap) { cap *= 2; char *nb = (char*)realloc(buf, cap); if (!nb) break; buf = nb; }
            ssize_t r = read(out_pipe[0], buf + len, cap - len);
            if (r <= 0) break;
            len += (size_t)r;
        }
    }
    close(out_pipe[0]);

    int status = -1;
    waitpid(pid, &status, 0);

    if (buf) {
        char *owned = (char*)hsh_alloc(len + 1);
        if (owned) { memcpy(owned, buf, len); owned[len] = '\0'; }
        free(buf);
        *out_buf = owned;
        *out_len = owned ? len : 0;
    }
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

/* regex::is_match(text, pattern) -> bool. `grep -qP pattern`, exit 0 = matched. */
int64_t hsh_regex_match(hsh_string pattern, hsh_string text) {
    if (!pattern) pattern = "";
    if (!text) text = "";
    char *argv[] = { (char*)"grep", (char*)"-qP", (char*)pattern, NULL };
    char *out = NULL; size_t outlen = 0;
    int rc = hsh_run_piped(argv, text, strlen(text), &out, &outlen);
    return (rc == 0) ? 1 : 0;
}

/* regex::find(text, pattern) -> string. `grep -oP pattern`, first line
 * of output, trimmed (matches the interpreter's `.trim()`). "" if no
 * match or grep itself couldn't run. */
hsh_string hsh_regex_find(hsh_string pattern, hsh_string text) {
    if (!pattern) pattern = "";
    if (!text) text = "";
    char *argv[] = { (char*)"grep", (char*)"-oP", (char*)pattern, NULL };
    char *out = NULL; size_t outlen = 0;
    int rc = hsh_run_piped(argv, text, strlen(text), &out, &outlen);
    if (rc < 0 || !out) return "";
    /* First line only, and trim (both ends, matching Rust's `.trim()`). */
    char *nl = strchr(out, '\n');
    if (nl) *nl = '\0';
    return hsh_trim(out);
}

/* regex::find_all(text, pattern) -> [string]. `grep -oP pattern`, every
 * non-empty output line becomes one array element. */
HshArray *hsh_regex_find_all(hsh_string pattern, hsh_string text) {
    HshArray *result = hsh_array_new();
    if (!pattern) pattern = "";
    if (!text) text = "";
    char *argv[] = { (char*)"grep", (char*)"-oP", (char*)pattern, NULL };
    char *out = NULL; size_t outlen = 0;
    int rc = hsh_run_piped(argv, text, strlen(text), &out, &outlen);
    if (rc < 0 || !out) return result;
    char *p = out;
    while (*p) {
        char *nl = strchr(p, '\n');
        size_t linelen = nl ? (size_t)(nl - p) : strlen(p);
        if (linelen > 0) {
            char *line = (char*)hsh_alloc(linelen + 1);
            if (line) { memcpy(line, p, linelen); line[linelen] = '\0'; result = hsh_array_push(result, (int64_t)(uintptr_t)line); }
        }
        if (!nl) break;
        p = nl + 1;
    }
    return result;
}

/* regex::replace(text, pattern, repl) / regex::replace_all(...) -> string.
 * `sed -E 's{d}pattern{d}repl{d}g'` — the `g` flag already replaces
 * every match, which is why `replace` and `replace_all` are the same
 * operation on this backend (matching the interpreter's own doc comment
 * on exactly this).
 *
 * SECURITY: mirrors the interpreter's two fixes precisely (see
 * `hsharp-interpreter::call.rs`'s own "SECURITY FIX" comment on
 * `re_replace` for the full history) — reject `pattern`/`repl`
 * containing a newline or NUL (either could inject an additional sed
 * script line/command regardless of delimiter choice), and pick a
 * delimiter character guaranteed absent from *both* strings instead of
 * hardcoding one that a caller-controlled pattern/replacement could
 * collide with. `argv`-based `execvp` (no shell) closes the other half
 * of that hole on its own — the old vulnerability was entirely about
 * what ends up *inside* the sed script, not shell interpretation of the
 * `sed` invocation itself, which was never present here. */
hsh_string hsh_regex_replace(hsh_string pattern, hsh_string repl, hsh_string text) {
    if (!pattern) pattern = "";
    if (!repl) repl = "";
    if (!text) text = "";
    if (strchr(pattern, '\n') || strchr(repl, '\n')) return text; /* refuse: same as interpreter's Err, but this fn has no Result to return through */
    static const char delim_candidates[] = { '|', '#', '~', 1, 2, 3, 0 };
    char delim = 0;
    for (int i = 0; delim_candidates[i]; i++) {
        char d = delim_candidates[i];
        if (!strchr(pattern, d) && !strchr(repl, d)) { delim = d; break; }
    }
    if (!delim) return text; /* couldn't find a safe delimiter — refuse, same as the interpreter's Err */

    /* "s" + delim + pattern + delim + repl + delim + "g" + NUL
     * = 1 + 1 + P + 1 + R + 1 + 1 + 1 = P + R + 7. An earlier version of
     * this got that arithmetic wrong (allocated 2 bytes short), which
     * `snprintf` silently truncated into — for some pattern/repl
     * lengths that cut the trailing `g` flag clean off the script,
     * silently turning "replace every match" into "replace only the
     * first". Caught by a round-trip test against known input/output,
     * not by inspection, which is exactly why this comment now spells
     * the arithmetic out in full rather than leaving it as a bare
     * expression again.
     */
    size_t script_len = strlen(pattern) + strlen(repl) + 7;
    char *script = (char*)malloc(script_len);
    if (!script) return text;
    snprintf(script, script_len, "s%c%s%c%s%cg", delim, pattern, delim, repl, delim);

    char *argv[] = { (char*)"sed", (char*)"-E", script, NULL };
    char *out = NULL; size_t outlen = 0;
    int rc = hsh_run_piped(argv, text, strlen(text), &out, &outlen);
    free(script);
    if (rc < 0 || !out) return text;
    /* Rust's `.trim_end()` — strip only trailing whitespace/newline sed
     * adds, keep any leading whitespace the match legitimately produced. */
    size_t n = strlen(out);
    while (n > 0 && (out[n-1] == '\n' || out[n-1] == '\r' || out[n-1] == ' ' || out[n-1] == '\t')) n--;
    out[n] = '\0';
    return out;
}

/* regex::split(text, pattern) -> [string]. Real regex-aware splitting
 * needs a real regex engine to find match *positions* (not just
 * extracted matches, which is all `grep -o` gives us) — out of scope
 * for the same reason a full regex engine is (see this section's own
 * top comment). Matches the interpreter's own documented, honest
 * fallback exactly (`call.rs`'s `re_split_ta`): the extremely common
 * `\s+`/`\s*` (whitespace) case gets real whitespace splitting, and
 * anything else falls back to a literal-substring split rather than
 * silently pretending to be regex-aware. */
HshArray *hsh_regex_split(hsh_string text, hsh_string pattern) {
    if (!text) text = "";
    if (!pattern) pattern = "";
    if (strcmp(pattern, "\\s+") == 0 || strcmp(pattern, "\\s*") == 0) {
        return hsh_str_split_whitespace(text);
    }
    return hsh_string_split(text, pattern);
}

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

/* ── hsh_flush — flush stdout ─────────────────────────────────────────────
 * Paired with hsh_readline: a `write_no_nl(prompt)` immediately followed
 * by a blocking `read_line()` needs the prompt actually on the terminal
 * (or pipe) before the read blocks, same reason the interpreter's own
 * `io_read_line`/`io_write_no_nl` arms (call.rs) explicitly flush
 * std::io::stdout() around a real read. */
void hsh_flush(void) { fflush(stdout); }

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

/* ── str::char_to_int / str::int_to_char — UTF-8 codepoint <-> string
 * (added this session; previously interpreter only). Decodes/encodes a
 * real Unicode codepoint (1-4 byte UTF-8 sequences), not just the raw
 * first byte, matching the "Unicode codepoint" contract in
 * builtins_registry.rs's doc comment. */
int64_t hsh_str_to_char_code(hsh_string s) {
    if (!s || s[0] == '\0') return 0;
    const unsigned char* b = (const unsigned char*)s;
    if (b[0] < 0x80) return b[0];
    if ((b[0] & 0xE0) == 0xC0 && b[1]) return ((b[0] & 0x1F) << 6) | (b[1] & 0x3F);
    if ((b[0] & 0xF0) == 0xE0 && b[1] && b[2])
        return ((b[0] & 0x0F) << 12) | ((b[1] & 0x3F) << 6) | (b[2] & 0x3F);
    if ((b[0] & 0xF8) == 0xF0 && b[1] && b[2] && b[3])
        return ((b[0] & 0x07) << 18) | ((b[1] & 0x3F) << 12) | ((b[2] & 0x3F) << 6) | (b[3] & 0x3F);
    return b[0]; /* malformed lead byte — fall back to the raw byte */
}

hsh_string hsh_char_code_to_str(int64_t code) {
    char* out = (char*)hsh_alloc(5);
    if (!out) return "";
    if (code < 0) code = 0;
    if (code < 0x80) {
        out[0] = (char)code; out[1] = '\0';
    } else if (code < 0x800) {
        out[0] = (char)(0xC0 | (code >> 6));
        out[1] = (char)(0x80 | (code & 0x3F));
        out[2] = '\0';
    } else if (code < 0x10000) {
        out[0] = (char)(0xE0 | (code >> 12));
        out[1] = (char)(0x80 | ((code >> 6) & 0x3F));
        out[2] = (char)(0x80 | (code & 0x3F));
        out[3] = '\0';
    } else {
        out[0] = (char)(0xF0 | (code >> 18));
        out[1] = (char)(0x80 | ((code >> 12) & 0x3F));
        out[2] = (char)(0x80 | ((code >> 6) & 0x3F));
        out[3] = (char)(0x80 | (code & 0x3F));
        out[4] = '\0';
    }
    return out;
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

/* ── HashMap ──────────────────────────────────────────────────────────────
 * Open addressing (linear probing) hash table, generic over int64_t keys
 * *and* string keys (the overwhelming majority of real use — config maps,
 * caches, JSON-like structures) — selected at construction time via
 * `string_keys` so one implementation serves both `HashMap<int, V>` and
 * `HashMap<string, V>` without duplicating the probing/resize logic.
 *
 * String keys are stored as *owned copies* (strdup'd on insert, freed on
 * overwrite/removal/table free) and compared/hashed by *content*, not by
 * pointer identity — critical correctness point: two equal strings at
 * different addresses (the normal case — nothing in this runtime interns
 * strings) must hash equal and compare equal, or every lookup with a
 * freshly-built key string would silently miss. Int keys are hashed and
 * compared as plain 64-bit values (pointer-identity is fine there — an int
 * key's bit pattern *is* its value, unlike a string key's pointer).
 *
 * Values are always a plain `int64_t` slot — same "everything is one i64
 * slot; strings are a pointer cast to i64" convention `HshArray` already
 * uses throughout this runtime (see the comment above `HshArray`'s
 * typedef) — so a `HashMap<K, string>` stores each value as a `char*`
 * reinterpreted as `int64_t`, exactly like an array of strings does.
 *
 * Tombstones (a `deleted` flag per slot, distinct from `occupied=0`) are
 * needed for correct open-addressing removal: a linear probe sequence must
 * keep scanning *through* a deleted slot to find keys that were inserted
 * after it and probed past it, which stopping at "first empty-looking
 * slot" would incorrectly break.
 */
typedef struct {
    int64_t key;        /* int64 key value, OR a strdup'd `char*` cast to int64_t when string_keys */
    int64_t value;
    uint8_t occupied;
    uint8_t deleted;     /* tombstone — see doc comment above */
} HshMapEntry;

typedef struct {
    int64_t count;        /* live entries (excludes tombstones) */
    int64_t cap;
    int     string_keys;  /* 0 = int64 keys (identity hash/eq), 1 = string keys (content hash/eq) */
    HshMapEntry* entries;
} HshMap;

/* FNV-1a — same well-known, non-cryptographic string hash used all over
 * (git, many language runtimes' default string hashers). Fast, simple,
 * good-enough distribution for a general-purpose hash table; deliberately
 * *not* claimed anywhere as suitable for anything security-sensitive
 * (HashDoS resistance, content hashing) — just table bucketing. */
static uint64_t hsh_fnv1a(const char* s) {
    uint64_t h = 1469598103934665603ULL; /* offset basis */
    while (*s) {
        h ^= (unsigned char)(*s++);
        h *= 1099511628211ULL; /* prime */
    }
    return h;
}

static uint64_t hsh_map_hash(HshMap* m, int64_t key) {
    if (m->string_keys) return hsh_fnv1a((const char*)(intptr_t)key);
    /* int64 identity hash — Fibonacci/multiplicative hashing (Knuth's
     * constant) so sequential integer keys (very common: IDs, indices)
     * spread across buckets instead of clustering in the low bits. */
    uint64_t k = (uint64_t)key;
    k ^= k >> 33;
    k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33;
    return k;
}

static int hsh_map_keys_eq(HshMap* m, int64_t a, int64_t b) {
    if (m->string_keys) {
        const char* sa = (const char*)(intptr_t)a;
        const char* sb = (const char*)(intptr_t)b;
        if (!sa || !sb) return sa == sb;
        return strcmp(sa, sb) == 0;
    }
    return a == b;
}

HshMap* hsh_map_new(int64_t string_keys) {
    HshMap* m = (HshMap*)malloc(sizeof(HshMap));
    if (!m) return NULL;
    m->count = 0;
    m->cap = 16;
    m->string_keys = string_keys ? 1 : 0;
    m->entries = (HshMapEntry*)calloc((size_t)m->cap, sizeof(HshMapEntry));
    return m;
}

static void hsh_map_grow(HshMap* m) {
    int64_t old_cap = m->cap;
    HshMapEntry* old_entries = m->entries;
    m->cap *= 2;
    m->entries = (HshMapEntry*)calloc((size_t)m->cap, sizeof(HshMapEntry));
    m->count = 0;
    for (int64_t i = 0; i < old_cap; i++) {
        if (old_entries[i].occupied && !old_entries[i].deleted) {
            /* Reinsert — can't just memcpy the slots, probe positions
             * depend on `cap`, which just changed. */
            uint64_t h = hsh_map_hash(m, old_entries[i].key);
            int64_t idx = (int64_t)(h % (uint64_t)m->cap);
            while (m->entries[idx].occupied) idx = (idx + 1) % m->cap;
            m->entries[idx] = old_entries[i];
            m->count++;
        }
    }
    free(old_entries);
}

/* Returns the slot index for `key`: an existing occupied match if present,
 * otherwise the first free-or-tombstoned slot along the probe sequence
 * (where a fresh insert should go). Callers distinguish "found" from
 * "insert point" by checking `.occupied && !.deleted` themselves. */
static int64_t hsh_map_probe(HshMap* m, int64_t key) {
    uint64_t h = hsh_map_hash(m, key);
    int64_t idx = (int64_t)(h % (uint64_t)m->cap);
    int64_t first_free = -1;
    for (int64_t i = 0; i < m->cap; i++) {
        HshMapEntry* e = &m->entries[idx];
        if (!e->occupied) {
            return (first_free >= 0) ? first_free : idx;
        }
        if (e->deleted) {
            if (first_free < 0) first_free = idx;
        } else if (hsh_map_keys_eq(m, e->key, key)) {
            return idx;
        }
        idx = (idx + 1) % m->cap;
    }
    return first_free; /* table full of tombstones — reuse one */
}

void hsh_map_set(HshMap* m, int64_t key, int64_t value) {
    if (!m) return;
    if (m->count * 2 >= m->cap) hsh_map_grow(m); /* keep load factor <= 0.5 for short probe chains */

    int64_t idx = hsh_map_probe(m, key);
    HshMapEntry* e = &m->entries[idx];
    int is_new = !(e->occupied && !e->deleted);

    if (m->string_keys) {
        if (!is_new) free((void*)(intptr_t)e->key); /* replacing: drop the old owned copy */
        const char* s = (const char*)(intptr_t)key;
        e->key = (int64_t)(intptr_t)(s ? strdup(s) : strdup(""));
    } else {
        e->key = key;
    }
    e->value = value;
    e->occupied = 1;
    e->deleted = 0;
    if (is_new) m->count++;
}

/* Returns 1 and writes *out if found, else returns 0 (leaves *out
 * untouched) — the has/get split (see hsh_map_get below) exists because a
 * stored value of 0 is completely legitimate and must be distinguishable
 * from "key absent". */
static int hsh_map_find(HshMap* m, int64_t key, int64_t* out) {
    if (!m || m->count == 0) return 0;
    int64_t idx = hsh_map_probe(m, key);
    HshMapEntry* e = &m->entries[idx];
    if (e->occupied && !e->deleted) {
        if (out) *out = e->value;
        return 1;
    }
    return 0;
}

int64_t hsh_map_get(HshMap* m, int64_t key) {
    int64_t out = 0;
    hsh_map_find(m, key, &out);
    return out; /* 0 on miss — see hsh_map_has for a real presence check */
}

int64_t hsh_map_has(HshMap* m, int64_t key) {
    return hsh_map_find(m, key, NULL);
}

int64_t hsh_map_remove(HshMap* m, int64_t key) {
    if (!m || m->count == 0) return 0;
    int64_t idx = hsh_map_probe(m, key);
    HshMapEntry* e = &m->entries[idx];
    if (!(e->occupied && !e->deleted)) return 0;
    if (m->string_keys) free((void*)(intptr_t)e->key);
    e->deleted = 1;
    m->count--;
    return 1;
}

int64_t hsh_map_len(HshMap* m) {
    return m ? m->count : 0;
}

/* Returns an HshArray* of the map's keys (int64 values, or char* cast to
 * int64 for string_keys — same convention as everywhere else). Order is
 * unspecified (bucket order) — same caveat as literally every hash table
 * in every language without an explicit "ordered map" variant. */
HshArray* hsh_map_keys(HshMap* m) {
    HshArray* a = hsh_arr_alloc(m && m->count > 0 ? m->count : 1);
    if (!m) return a;
    for (int64_t i = 0; i < m->cap; i++) {
        HshMapEntry* e = &m->entries[i];
        if (e->occupied && !e->deleted) {
            a = hsh_array_push(a, e->key);
        }
    }
    return a;
}

/* EXPANSION: the values counterpart to hsh_map_keys above — added so
 * the `hashmap_new()`/`.values()` surface-syntax family (see the
 * `hashmap_*`/`hashset_*` bridge in codegen.rs's call_fn/MethodCall
 * dispatch, and the matching `builtins_registry.rs` entries) has a real
 * value-side counterpart to pair with hsh_map_keys, instead of only
 * ever being able to enumerate keys. Same "one HshArray* of i64 slots,
 * unspecified bucket order" convention as hsh_map_keys — and critically
 * the *same* iteration order as it, so `hsh_map_keys(m)[i]` and
 * `hsh_map_values(m)[i]` refer to the same entry for a given `m`
 * between calls (no mutation in between), letting callers zip them
 * together the same way most languages' `.keys()`/`.values()` pair
 * promises to. */
HshArray* hsh_map_values(HshMap* m) {
    HshArray* a = hsh_arr_alloc(m && m->count > 0 ? m->count : 1);
    if (!m) return a;
    for (int64_t i = 0; i < m->cap; i++) {
        HshMapEntry* e = &m->entries[i];
        if (e->occupied && !e->deleted) {
            a = hsh_array_push(a, e->value);
        }
    }
    return a;
}

void hsh_map_clear(HshMap* m) {
    if (!m) return;
    if (m->string_keys) {
        for (int64_t i = 0; i < m->cap; i++) {
            if (m->entries[i].occupied && !m->entries[i].deleted) {
                free((void*)(intptr_t)m->entries[i].key);
            }
        }
    }
    memset(m->entries, 0, (size_t)m->cap * sizeof(HshMapEntry));
    m->count = 0;
}
