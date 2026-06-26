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
#include <netinet/in.h>
#include <arpa/inet.h>

typedef const char* hsh_string;
typedef int64_t     hsh_int;
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
    char* out = (char*)malloc(la + lb + 1);
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
typedef struct { uint8_t* base; uint64_t cap; uint64_t used; } HshArena;

HshArena* hsh_arena_new(uint64_t cap) {
    HshArena* a = (HshArena*)malloc(sizeof(HshArena));
    if (!a) return NULL;
    a->base = (uint8_t*)malloc(cap);
    a->cap  = cap;
    a->used = 0;
    return a;
}
void* hsh_arena_alloc(HshArena* a, uint64_t n) {
    uint64_t aligned = (n + 7) & ~7ULL;
    if (!a || a->used + aligned > a->cap) { fprintf(stderr, "H# arena OOM\n"); exit(1); }
    void* p = a->base + a->used;
    a->used += aligned;
    return p;
}
void hsh_arena_free(HshArena* a) { if (a) { free(a->base); free(a); } }

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
