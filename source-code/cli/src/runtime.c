#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/mman.h>

/* ── I/O ── */
void write_u8(uint8_t n)    { printf("%hhu\n", n); }
void write_i64(int64_t n)   { printf("%lld\n", (long long)n); }
void write_u64(uint64_t n)  { printf("%llu\n", (unsigned long long)n); }
void write_hex(uint64_t n)  { printf("0x%llx\n", (unsigned long long)n); }
void write_bool(int8_t b)   { puts(b ? "true" : "false"); }
void write_bytes(uint8_t* p, long len) { fwrite(p, 1, len, stdout); }

/* ── String ops ── */
long* str_concat(long* a, long* b) {
    char* ap = (char*)a[0]; long al = a[1];
    char* bp = (char*)b[0]; long bl = b[1];
    long total = al + bl;
    char* buf = malloc(total + 1);
    memcpy(buf, ap, al);
    memcpy(buf + al, bp, bl);
    buf[total] = 0;
    long* r = malloc(16);
    r[0] = (long)buf; r[1] = total;
    return r;
}
int str_cmp(long* a, long* b) {
    return memcmp((void*)a[0], (void*)b[0],
                  a[1] < b[1] ? a[1] : b[1]);
}

/* ── Memory ── */
void  mem_copy(void* d, void* s, long n) { memcpy(d, s, n); }
void  mem_set(void* d, int v, long n)    { memset(d, v, n); }
int   mem_cmp(void* a, void* b, long n)  { return memcmp(a, b, n); }

/* ── Arena (prawdziwa implementacja) ── */
typedef struct {
    uint8_t* base;
    long     cap;
    long     used;
} Arena;

long arena_new(long cap) {
    Arena* a = malloc(sizeof(Arena));
    // mmap dla wydajności - brak fragmentacji
    a->base = mmap(NULL, cap,
                   PROT_READ|PROT_WRITE,
                   MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    a->cap  = cap;
    a->used = 0;
    return (long)a;
}
long arena_alloc(long handle, long size) {
    Arena* a = (Arena*)handle;
    // Alignment do 8 bajtów
    size = (size + 7) & ~7;
    if (a->used + size > a->cap) {
        fprintf(stderr, "Arena OOM\n"); exit(1);
    }
    void* ptr = a->base + a->used;
    a->used += size;
    return (long)ptr;
}
void arena_free(long handle) {
    Arena* a = (Arena*)handle;
    munmap(a->base, a->cap);
    free(a);
}

/* ── Networking ── */
int net_tcp_connect(long* host_str, int port, int timeout_ms) {
    char* host = (char*)host_str[0];
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;

    // Non-blocking dla timeout
    fcntl(fd, F_SETFL, O_NONBLOCK);

    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_port   = htons(port);
    inet_pton(AF_INET, host, &addr.sin_addr);

    connect(fd, (struct sockaddr*)&addr, sizeof(addr));

    // Select z timeout
    struct timeval tv = {
        timeout_ms / 1000,
        (timeout_ms % 1000) * 1000
    };
    fd_set fds; FD_ZERO(&fds); FD_SET(fd, &fds);
    if (select(fd+1, NULL, &fds, NULL, &tv) <= 0) {
        close(fd); return -1;
    }
    // Przywróć blocking
    fcntl(fd, F_SETFL, 0);
    return fd;
}

int   net_tcp_listen(int port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    int opt = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    struct sockaddr_in a = {0};
    a.sin_family = AF_INET;
    a.sin_port   = htons(port);
    a.sin_addr.s_addr = INADDR_ANY;
    bind(fd, (struct sockaddr*)&a, sizeof(a));
    listen(fd, 128);
    return fd;
}
int   net_tcp_accept(int fd)              { return accept(fd, NULL, NULL); }
long  net_send(int fd, void* b, long n)   { return send(fd, b, n, 0); }
long  net_recv(int fd, void* b, long n)   { return recv(fd, b, n, 0); }
void  net_close(int fd)                   { close(fd); }
int   raw_socket(int dom, int type, int proto) {
    return socket(dom, type, proto);
}

/* ── Syscall direct ── */
long sys_call3(long nr, long a, long b, long c) {
    return syscall(nr, a, b, c);
}

/* ── Process ── */
int  proc_pid()  { return getpid(); }
void proc_exit(int c) { _exit(c); }
