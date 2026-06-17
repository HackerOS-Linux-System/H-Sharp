pub fn runtime_c_source() -> &'static str {
    r#"/* H# Runtime v0.7 — linked with every compiled H# binary */
    /* Uses real libpcre2-8 (regex) and libsqlite3 (prepared statements). */
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
    /* PCRE2: must define code unit width before including the header.        */
    /* Requires libpcre2-dev / -lpcre2-8 at link time (§11).                   */
    #define PCRE2_CODE_UNIT_WIDTH 8
    #include <pcre2.h>
    #include <sqlite3.h>
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

    /* extern [python, "mod"] phase-1.5 trampoline helpers (codegen.rs):
     * marshal py_eval()'s string result back to numeric H# return types. */
    int64_t hsh_atoll(hsh_string s) { return s ? atoll(s) : 0; }
    double  hsh_atof(hsh_string s)  { return s ? atof(s)  : 0.0; }

    char* hsh_int_to_string(int64_t n) {
    char* buf = (char*)malloc(32);
    if (buf) snprintf(buf, 32, "%ld", (long)n);
    return buf ? buf : "";
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

double hsh_sin(double x)  { return sin(x);  }
double hsh_cos(double x)  { return cos(x);  }
double hsh_sqrt(double x) { return sqrt(x); }

/* ── System ──────────────────────────────────────────────────────────────── */

hsh_string hsh_hostname(void) {
static char buf[256];
gethostname(buf, sizeof(buf));
return buf;
}

int64_t hsh_getpid(void) { return (int64_t)getpid(); }

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

/* ── SECURITY: shell_escape + exec (no-shell) ───────────────────────────── */
/*                                                                            */
/* shell() above invokes /bin/sh via popen(). Any untrusted data            */
/* concatenated into that command string is a Command Injection vector:    */
/* the shell re-parses the string for ; && | $() backticks etc. before     */
/* the kernel ever sees a syscall.                                          */
/*                                                                            */
/* Two mitigations are provided:                                           */
/*   1. hsh_shell_escape(s) — POSIX single-quote escaping. Wrap any         */
/*      variable interpolated into shell() with this:                      */
/*        shell("mkdir " + shell_escape(user_path))                         */
/*      A value containing `'; rm -rf / #` becomes the single literal      */
/*      argument  '; rm -rf / #  — the shell cannot break out of the       */
/*      quotes.                                                             */
/*                                                                            */
/*   2. hsh_exec1..4(cmd, a1, a2, a3) — direct fork+execve. NO /bin/sh is   */
/*      spawned at all. Arguments are passed as a true argv[] array to the  */
/*      kernel; metacharacters are inert literal bytes. Use this whenever   */
/*      the command name and argument count are known at the call site:    */
/*        exec3("mount", "-t", "tmpfs", "/mnt/x")   // no shell, no parsing */
/*      stdout+stderr are captured and returned as a string, same as       */
/*      shell(), but with none of the injection or fork-bomb-via-shell     */
/*      overhead (one fork+exec instead of fork+exec(/bin/sh)+exec(cmd)).  */

hsh_string hsh_shell_escape(hsh_string s) {
if (!s) return "''";
size_t n = strlen(s);
/* worst case: every char is a ' -> needs '\'' (4 chars) */
char* out = (char*)malloc(n * 4 + 3);
if (!out) return "''";
size_t w = 0;
out[w++] = '\'';
for (size_t i = 0; i < n; i++) {
    if (s[i] == '\'') {
        /* close quote, escaped quote, reopen quote: '\'' */
        out[w++] = '\''; out[w++] = '\\'; out[w++] = '\''; out[w++] = '\'';
} else {
    out[w++] = s[i];
}
}
out[w++] = '\'';
out[w] = '\0';
return out;
}

/* extern [python, "mod"] bridge: build a Python single-quoted string
 * literal from an H# string, for embedding into generated `py_eval(code)`
 * source (see codegen.rs's Python trampoline generation). Python string
 * escaping differs from POSIX shell escaping (hsh_shell_escape above) —
 * Python uses backslash escapes (\\, \', \n) inside '...' literals, not
 * shell's '\'' close-escape-reopen trick. */
hsh_string hsh_py_repr(hsh_string s) {
if (!s) return "''";
size_t n = strlen(s);
/* worst case: every char becomes a 2-char escape, +2 for quotes, +1 NUL */
char* out = (char*)malloc(n * 2 + 3);
if (!out) return "''";
size_t w = 0;
out[w++] = '\'';
for (size_t i = 0; i < n; i++) {
    switch (s[i]) {
        case '\'':  out[w++] = '\\'; out[w++] = '\''; break;
        case '\\': out[w++] = '\\'; out[w++] = '\\'; break;
        case '\n':  out[w++] = '\\'; out[w++] = 'n';  break;
        case '\r':  out[w++] = '\\'; out[w++] = 'r';  break;
        default:    out[w++] = s[i];
}
}
out[w++] = '\'';
out[w] = '\0';
return out;
}

/* Internal: fork+execve with argv[], capture combined stdout+stderr.
 * No shell is involved — argv entries are passed verbatim to the kernel. */
static hsh_string hsh_exec_argv(char* const argv[]) {
int pipefd[2];
if (pipe(pipefd) != 0) return "";

pid_t pid = fork();
if (pid < 0) { close(pipefd[0]); close(pipefd[1]); return ""; }

if (pid == 0) {
    /* child */
    dup2(pipefd[1], STDOUT_FILENO);
    dup2(pipefd[1], STDERR_FILENO);
    close(pipefd[0]);
    close(pipefd[1]);
    execvp(argv[0], argv);
    /* execvp only returns on failure */
    _exit(127);
}

/* parent */
close(pipefd[1]);
char* buf = NULL;
size_t total = 0, cap = 0;
char chunk[4096];
ssize_t n;
while ((n = read(pipefd[0], chunk, sizeof(chunk))) > 0) {
    if (total + (size_t)n + 1 > cap) {
        cap = (cap + (size_t)n + 1) * 2;
        char* nb = (char*)realloc(buf, cap);
        if (!nb) { free(buf); close(pipefd[0]); waitpid(pid, NULL, 0); return ""; }
        buf = nb;
}
memcpy(buf + total, chunk, (size_t)n);
total += (size_t)n;
}
close(pipefd[0]);
waitpid(pid, NULL, 0);
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
if (!cmd) return "";
char* argv[3] = { (char*)cmd, (char*)(a1 ? a1 : ""), NULL };
return hsh_exec_argv(argv);
}

hsh_string hsh_exec3(hsh_string cmd, hsh_string a1, hsh_string a2) {
if (!cmd) return "";
char* argv[4] = { (char*)cmd, (char*)(a1 ? a1 : ""), (char*)(a2 ? a2 : ""), NULL };
return hsh_exec_argv(argv);
}

hsh_string hsh_exec4(hsh_string cmd, hsh_string a1, hsh_string a2, hsh_string a3) {
if (!cmd) return "";
char* argv[5] = { (char*)cmd, (char*)(a1 ? a1 : ""), (char*)(a2 ? a2 : ""), (char*)(a3 ? a3 : ""), NULL };
return hsh_exec_argv(argv);
}

/* ── extern [python, "mod"] bridge ───────────────────────────────────────── */
/* Phase 1 (current): subprocess via execve, NO shell.                       */
/*   py_eval("print(2+2)") -> "4\n"                                          */
/* The `code` string is passed as a single argv element to `python3 -c`,   */
/* so shell metacharacters in `code` are inert — they're just source text  */
/* the Python interpreter parses, same as any .py file.                    */
/*                                                                            */
/* Phase 2 (future, see roadmap): embed libpython directly via Py_Initialize*/
/* + PyRun_String for in-process calls without fork/exec overhead, plus a  */
/* typed marshaling layer so `extern [python, "numpy"] fn array(...)`      */
/* declarations map to real PyObject* calls with H#<->Python type bridging.*/
hsh_string hsh_py_eval(hsh_string code) {
if (!code) return "";
char* argv[4] = { (char*)"python3", (char*)"-c", (char*)code, NULL };
return hsh_exec_argv(argv);
}



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
fclose(fp);
buf[n * 2] = '\0';
return buf;
}

int64_t hsh_random_int(int64_t min, int64_t max) {
uint64_t r = 0;
FILE* fp = fopen("/dev/urandom", "rb");
if (fp) { fread(&r, 8, 1, fp); fclose(fp); }
if (max <= min) return min;
return min + (int64_t)(r % (uint64_t)(max - min));
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

hsh_string hsh_random_string(int64_t n) {
static const char cs[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
if (n <= 0) return "";
char* out = (char*)malloc((size_t)n + 1);
uint8_t* tmp = (uint8_t*)malloc((size_t)n);
if (!out || !tmp) { free(out); free(tmp); return ""; }
FILE* f = fopen("/dev/urandom", "rb");
if (f) { fread(tmp, 1, (size_t)n, f); fclose(f); }
for (int64_t i = 0; i < n; i++) out[i] = cs[tmp[i] % 62];
free(tmp);
out[n] = '\0';
return out;
}

/* ── Filesystem ──────────────────────────────────────────────────────────── */

int64_t hsh_file_exists(hsh_string path) {
if (!path) return 0;
struct stat st;
return (stat(path, &st) == 0) ? 1 : 0;
}

hsh_string hsh_read_file(hsh_string path) {
if (!path) return "";
FILE* f = fopen(path, "rb");
if (!f) return "";
fseek(f, 0, SEEK_END);
long sz = ftell(f);
rewind(f);
if (sz < 0) { fclose(f); return ""; }
char* buf = (char*)malloc((size_t)sz + 1);
if (!buf) { fclose(f); return ""; }
fread(buf, 1, (size_t)sz, f);
buf[sz] = '\0';
fclose(f);
return buf;
}

int64_t hsh_write_file(hsh_string path, hsh_string content) {
if (!path) return 0;
FILE* f = fopen(path, "wb");
if (!f) return 0;
if (content) fputs(content, f);
fclose(f);
return 1;
}

int64_t hsh_mkdir_all(hsh_string path) {
if (!path) return 0;
char tmp[4096];
snprintf(tmp, sizeof(tmp), "%s", path);
for (char* p = tmp + 1; *p; p++) {
    if (*p == '/') { *p = '\0'; mkdir(tmp, 0755); *p = '/'; }
}
mkdir(tmp, 0755);
return 1;
}

int64_t hsh_file_size(hsh_string path) {
if (!path) return -1;
struct stat st;
return (stat(path, &st) == 0) ? (int64_t)st.st_size : -1;
}

int64_t hsh_is_dir(hsh_string path) {
if (!path) return 0;
struct stat st;
return (stat(path, &st) == 0 && S_ISDIR(st.st_mode)) ? 1 : 0;
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

/* ── Smart value-to-string ───────────────────────────────────────────────── */

hsh_string hsh_val_to_str(int64_t v) {
if (v == 0) return "0";
/* Heuristic: if value looks like a valid C string pointer, return it */
if ((uintptr_t)v > 65536 && (uintptr_t)v < (uintptr_t)0x7fffffffffff) {
    const char* p = (const char*)v;
    unsigned char first = (unsigned char)p[0];
    if (first == 0 || (first >= 0x20 && first < 0x80)) {
        return (hsh_string)v;
}
}
return hsh_int_to_string(v);
}

/* ── HTTP (curl-based) ───────────────────────────────────────────────────── */

hsh_string hsh_http_get(hsh_string url) {
if (!url) return "";
char cmd[4096];
snprintf(cmd, sizeof(cmd),
"curl -s -L --max-time 15 -A 'H#/0.7' '%s' 2>/dev/null", url);
return hsh_shell(cmd);
}

hsh_string hsh_http_post(hsh_string url, hsh_string body) {
if (!url) return "";
char cmd[8192];
snprintf(cmd, sizeof(cmd),
"curl -s -L -X POST --max-time 15 "
"-H 'Content-Type: application/json' "
"-d '%s' '%s' 2>/dev/null",
body ? body : "", url);
return hsh_shell(cmd);
}

hsh_string hsh_json_get(hsh_string json_str, hsh_string key) {
if (!json_str || !key) return "";
char cmd[8192];
snprintf(cmd, sizeof(cmd),
"echo '%s' | jq -r '.%s' 2>/dev/null | tr -d '\n'",
json_str, key);
hsh_string r = hsh_shell(cmd);
return (r && *r && strcmp(r, "null") != 0) ? r : "";
}

/* ── Regex (PCRE2 — \d \w \s, lookaround, non-greedy all native) ─────────── */
/* ── Regex — PCRE2 (§11) ─────────────────────────────────────────────────── */
/* Previously: POSIX ERE via <regex.h> with hand-translated \d \w \s, no     */
/* lookahead/lookbehind/non-greedy. Now: real PCRE2 via libpcre2-8.          */
/* Link requirement: -lpcre2-8 (added in llvm-compiler emit_binary_with_machine). */

int64_t hsh_regex_match(hsh_string pattern, hsh_string text) {
if (!pattern || !text) return 0;
int errcode; PCRE2_SIZE erroffset;
pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
0, &errcode, &erroffset, NULL);
if (!re) return 0;
pcre2_match_data* md = pcre2_match_data_create(1, NULL);
int rc = pcre2_match(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0, 0, md, NULL);
pcre2_match_data_free(md);
pcre2_code_free(re);
return rc >= 0 ? 1 : 0;
}

hsh_string hsh_regex_find(hsh_string pattern, hsh_string text) {
if (!pattern || !text) return "";
int errcode; PCRE2_SIZE erroffset;
pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
0, &errcode, &erroffset, NULL);
if (!re) return "";
pcre2_match_data* md = pcre2_match_data_create(1, NULL);
int rc = pcre2_match(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0, 0, md, NULL);
hsh_string result = "";
if (rc >= 0) {
    PCRE2_SIZE* ov = pcre2_get_ovector_pointer(md);
    size_t len = ov[1] - ov[0];
    char* out = (char*)malloc(len + 1);
    if (out) {
        memcpy(out, text + ov[0], len);
        out[len] = '\0';
        result = out;
}
}
pcre2_match_data_free(md);
pcre2_code_free(re);
return result;
}

hsh_string hsh_regex_replace(hsh_string pattern, hsh_string replacement, hsh_string text) {
if (!pattern || !text || !replacement) return text ? text : "";
int errcode; PCRE2_SIZE erroffset;
pcre2_code* re = pcre2_compile((PCRE2_SPTR)pattern, PCRE2_ZERO_TERMINATED,
0, &errcode, &erroffset, NULL);
if (!re) return text;

/* PCRE2_SUBSTITUTE_GLOBAL replaces all matches. PCRE2 substitution
 * syntax uses $1, $2, ... for capture groups (vs POSIX \1) — H#
 * `replacement` strings using $N work directly. */
PCRE2_SIZE outlen = strlen(text) * 2 + strlen(replacement) + 64;
PCRE2_UCHAR* out = (PCRE2_UCHAR*)malloc(outlen);
if (!out) { pcre2_code_free(re); return text; }

int rc = pcre2_substitute(re, (PCRE2_SPTR)text, PCRE2_ZERO_TERMINATED, 0,
PCRE2_SUBSTITUTE_GLOBAL | PCRE2_SUBSTITUTE_EXTENDED, NULL, NULL,
(PCRE2_SPTR)replacement, PCRE2_ZERO_TERMINATED, out, &outlen);

pcre2_code_free(re);
if (rc < 0) { free(out); return text; }
return (hsh_string)out;
}

/* ── SQLite3 — real libpsqlite3 with prepared statements (§12) ───────────── */
/* Previously: shelled out to `sqlite3 'path' 'sql'` — both shell-quoting   */
/* AND SQL injection (string-concatenated SQL) vulnerable.                 */
/*                                                                            */
/* Now: links libsqlite3 directly (-lsqlite3, added in                     */
/* emit_binary_with_machine). hsh_sqlite_exec/query use                    */
/* sqlite3_prepare_v2/sqlite3_step directly — no shell involved at all.    */
/*                                                                            */
/* SQL INJECTION: hsh_sqlite_exec/query still take a single `sql` string — */
/* if that string was built via H# string concatenation with untrusted    */
/* data, it's still injectable (the vulnerability is in how the SQL TEXT  */
/* was constructed, independent of how it's executed). The NEW             */
/* hsh_sqlite_query_bind1/2/3 functions below take the SQL as a literal   */
/* TEMPLATE containing `?` placeholders plus 1-3 separate bind values,     */
/* using sqlite3_bind_text — this is the parameterized-query API that      */
/* eliminates SQL injection BY CONSTRUCTION (the bind values are sent to  */
/* SQLite as DATA, never re-parsed as SQL syntax), exactly mirroring how   */
/* exec()/hsh_exec_argv eliminates shell injection. H# surface API:        */
/*   db_query_bind(db, "SELECT * FROM t WHERE id = ?", id)                 */

hsh_string hsh_sqlite_open(hsh_string path) {
if (!path || !*path) path = "db.sqlite";
char* h = (char*)malloc(strlen(path) + 1);
if (h) strcpy(h, path);
return h ? h : path;
}

hsh_string hsh_sqlite_exec(hsh_string db_path, hsh_string sql) {
if (!db_path || !sql) return "";
sqlite3* db;
if (sqlite3_open(db_path, &db) != SQLITE_OK) {
    hsh_string err = sqlite3_errmsg(db);
    char* out = (char*)malloc(strlen(err) + 1);
    if (out) strcpy(out, err);
    sqlite3_close(db);
    return out ? out : "";
}
char* errmsg = NULL;
int rc = sqlite3_exec(db, sql, NULL, NULL, &errmsg);
hsh_string result = "";
if (rc != SQLITE_OK && errmsg) {
    char* out = (char*)malloc(strlen(errmsg) + 1);
    if (out) strcpy(out, errmsg);
    result = out ? out : "";
    sqlite3_free(errmsg);
}
sqlite3_close(db);
return result;
}

/* Internal: run `sql` (no placeholders, or placeholders bound from `binds`)
 * and return all rows as CSV (one row per line, columns comma-separated) —
 * matches the output shape of the old CLI-based hsh_sqlite_query. */
static hsh_string hsh_sqlite_run_query(hsh_string db_path, hsh_string sql, hsh_string* binds, int nbinds) {
if (!db_path || !sql) return "";
sqlite3* db;
if (sqlite3_open(db_path, &db) != SQLITE_OK) {
    sqlite3_close(db);
    return "";
}
sqlite3_stmt* stmt;
if (sqlite3_prepare_v2(db, sql, -1, &stmt, NULL) != SQLITE_OK) {
    hsh_string err = sqlite3_errmsg(db);
    char* out = (char*)malloc(strlen(err) + 1);
    if (out) strcpy(out, err);
    sqlite3_close(db);
    return out ? out : "";
}
for (int i = 0; i < nbinds; i++) {
    sqlite3_bind_text(stmt, i + 1, binds[i] ? binds[i] : "", -1, SQLITE_TRANSIENT);
}

char* buf = NULL;
size_t total = 0, cap = 0;
int ncols = sqlite3_column_count(stmt);

while (sqlite3_step(stmt) == SQLITE_ROW) {
    for (int c = 0; c < ncols; c++) {
        const unsigned char* val = sqlite3_column_text(stmt, c);
        const char* cell = val ? (const char*)val : "";
        size_t clen = strlen(cell);
        size_t needed = clen + 2; /* +1 for ',' or '\n', +1 for NUL */
        if (total + needed > cap) {
            cap = (cap + needed) * 2;
            char* nb = (char*)realloc(buf, cap);
            if (!nb) { free(buf); sqlite3_finalize(stmt); sqlite3_close(db); return ""; }
            buf = nb;
}
memcpy(buf + total, cell, clen); total += clen;
buf[total++] = (c == ncols - 1) ? '\n' : ',';
}
}
sqlite3_finalize(stmt);
sqlite3_close(db);

if (!buf) return "";
buf[total] = '\0';
return buf;
}

hsh_string hsh_sqlite_query(hsh_string db_path, hsh_string sql) {
return hsh_sqlite_run_query(db_path, sql, NULL, 0);
}

/* §12: parameterized queries — SQL injection-safe by construction.       */
/* H# usage:                                                                */
/*   db_query_bind(db, "SELECT * FROM users WHERE name = ?", name)         */
/*   db_query_bind(db, "SELECT * FROM t WHERE a=? AND b=?", a, b)          */
hsh_string hsh_sqlite_query_bind1(hsh_string db_path, hsh_string sql, hsh_string b1) {
hsh_string binds[1] = { b1 };
return hsh_sqlite_run_query(db_path, sql, binds, 1);
}
hsh_string hsh_sqlite_query_bind2(hsh_string db_path, hsh_string sql, hsh_string b1, hsh_string b2) {
hsh_string binds[2] = { b1, b2 };
return hsh_sqlite_run_query(db_path, sql, binds, 2);
}
hsh_string hsh_sqlite_query_bind3(hsh_string db_path, hsh_string sql, hsh_string b1, hsh_string b2, hsh_string b3) {
hsh_string binds[3] = { b1, b2, b3 };
return hsh_sqlite_run_query(db_path, sql, binds, 3);
}

void hsh_sqlite_close(hsh_string db_path) { (void)db_path; /* each call opens/closes its own connection */ }

/* ── Closures ────────────────────────────────────────────────────────────── */

typedef struct { int64_t fn_ptr; int64_t n_caps; int64_t caps[8]; } HshClosure;

HshClosure* hsh_closure_create(int64_t fn_ptr, int64_t n_caps,
int64_t c0, int64_t c1, int64_t c2, int64_t c3,
int64_t c4, int64_t c5, int64_t c6, int64_t c7) {
HshClosure* c = (HshClosure*)malloc(sizeof(HshClosure));
if (!c) return NULL;
c->fn_ptr = fn_ptr; c->n_caps = n_caps;
int64_t caps_in[8] = {c0,c1,c2,c3,c4,c5,c6,c7};
for (int64_t i = 0; i < n_caps && i < 8; i++) c->caps[i] = caps_in[i];
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
"#
}
