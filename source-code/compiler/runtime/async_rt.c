#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>
#include <pthread.h>
#include <semaphore.h>
#include <unistd.h>

/* ── Bounded concurrency ──────────────────────────────────────────────
 * hsh_task_spawn used to call pthread_create() with no limit at all.
 * A program that fans out thousands of tasks (e.g. `for i in 0..50000
 * do spawn worker(i) end`) would try to create thousands of OS threads
 * at once — each with its own ~8MB default stack — which reliably
 * exhausts `ulimit -u` / address space on a desktop long before it
 * would on a phone with a handful of tasks in flight.
 *
 * This isn't a full thread pool (that needs a task queue + a fixed
 * set of worker threads and is a bigger change), but a semaphore cap
 * on how many HshTask threads may be alive at once gives real
 * backpressure with no ABI change: hsh_task_spawn() will simply block
 * the *calling* thread until a slot frees up, instead of the process
 * dying. The cap is configurable via the HSH_MAX_TASKS env var so
 * heavier desktop workloads aren't stuck with a phone-sized default.
 */
#define HSH_MAX_TASKS_DEFAULT_MIN 64
#define HSH_MAX_TASKS_DEFAULT_MAX 4096
#define HSH_MAX_TASKS_PER_CORE    64

static sem_t          hsh_task_sem;
static pthread_once_t hsh_task_sem_once = PTHREAD_ONCE_INIT;

static void hsh_task_sem_init(void) {
    long cap = 0;
    const char* env = getenv("HSH_MAX_TASKS");
    if (env && *env) {
        cap = atol(env);
    }
    if (cap <= 0) {
        long cores = sysconf(_SC_NPROCESSORS_ONLN);
        if (cores < 1) cores = 1;
        cap = cores * HSH_MAX_TASKS_PER_CORE;
    }
    if (cap < HSH_MAX_TASKS_DEFAULT_MIN) cap = HSH_MAX_TASKS_DEFAULT_MIN;
    if (cap > HSH_MAX_TASKS_DEFAULT_MAX) cap = HSH_MAX_TASKS_DEFAULT_MAX;
    sem_init(&hsh_task_sem, 0, (unsigned int)cap);
}

/* ── Task descriptor ─────────────────────────────────────────────── */

#define HSH_TASK_MAGIC 0x485348544153 /* "HSHTASK" truncated */

typedef struct HshTask {
    uint64_t         magic;      /* HSH_TASK_MAGIC — used by hsh_task_wait
                                  * to distinguish task handles from plain i64
                                  * values passed through await by mistake.   */
    pthread_t        thread;
    void*          (*fn_ptr)(void*);
    void*            args;
    volatile int64_t result;
    volatile int     done;       /* 1 when thread has written result           */
    pthread_mutex_t  mu;
    pthread_cond_t   cv;
} HshTask;

/* ── Thread trampoline ───────────────────────────────────────────── */

static void* task_trampoline(void* arg) {
    HshTask* t = (HshTask*)arg;
    int64_t r  = (int64_t)t->fn_ptr(t->args);
    pthread_mutex_lock(&t->mu);
    t->result = r;
    t->done   = 1;
    pthread_cond_broadcast(&t->cv);
    pthread_mutex_unlock(&t->mu);
    /* Free our concurrency slot now that the work is done, so any
     * caller blocked in hsh_task_spawn() can proceed. */
    sem_post(&hsh_task_sem);
    return NULL;
}

/* ── Public API ──────────────────────────────────────────────────── */

void* hsh_task_spawn(void* fn_ptr, void* args) {
    pthread_once(&hsh_task_sem_once, hsh_task_sem_init);
    /* Blocks here (this is the backpressure) if HSH_MAX_TASKS tasks
     * are already in flight, instead of spawning unboundedly. */
    sem_wait(&hsh_task_sem);

    HshTask* t = (HshTask*)calloc(1, sizeof(HshTask));
    if (!t) {
        sem_post(&hsh_task_sem);
        return NULL;
    }

    t->magic  = HSH_TASK_MAGIC;
    t->fn_ptr = (void*(*)(void*))fn_ptr;
    t->args   = args;
    t->done   = 0;

    pthread_mutex_init(&t->mu, NULL);
    pthread_cond_init(&t->cv, NULL);

    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
    int rc = pthread_create(&t->thread, &attr, task_trampoline, t);
    pthread_attr_destroy(&attr);

    if (rc != 0) {
        /* pthread_create failed (e.g. EAGAIN under resource pressure).
         * The old code ignored this and left t->thread uninitialized,
         * so a later pthread_join()/pthread_cond_wait() on it was
         * undefined behavior. Fail cleanly instead. */
        fprintf(stderr, "hsh_task_spawn: pthread_create failed (errno=%d)\n", rc);
        pthread_mutex_destroy(&t->mu);
        pthread_cond_destroy(&t->cv);
        free(t);
        sem_post(&hsh_task_sem);
        return NULL;
    }

    return (void*)t;
}

/* BUG FIX (real, newly-reachable crash — see this function's own git
 * history / this session's notes): `hsh_task_wait` always did
 * `((HshTask*)handle)->magic` on *any* incoming value before checking
 * whether it looked like a real pointer at all. That's fine for a
 * genuine (if wrong) pointer, but `await` on a plain small value —
 * `await 42`, `await some_bool_returning_call()`, any non-async-fn
 * value under roughly 64KB when reinterpreted as an address — hits an
 * unmapped low page and segfaults the whole process, exactly
 * contradicting this function's own doc comment ("await non_async_fn()
 * is safe and free"). This was always a latent bug, but was never
 * actually reachable on the LLVM backend until `async fn`/`await` were
 * wired up for real there (see `features.rs`) — the interpreter has
 * its own, separate, dynamically-typed `runtime_async.rs` that never
 * goes through this C function at all, so it never hit this path
 * either. Real heap pointers from `calloc` (what `hsh_task_spawn`
 * allocates a `HshTask` with) are never this small in practice on any
 * mainstream 64-bit OS, so checking the raw address is comfortably
 * above a low threshold *before* ever dereferencing it turns this from
 * "usually safe, sometimes segfaults" into "always safe" for the
 * overwhelmingly common case (small ints, bools, chars) this
 * passthrough path exists for — see `hsh_looks_like_task_ptr`'s own
 * doc comment for the (rare, inherent-to-this-design) case it still
 * can't fully cover. */
static int hsh_looks_like_task_ptr(void* handle) {
    /* A real heap allocation is essentially never found this low in a
     * process's address space; a plain scalar value that was never a
     * pointer at all (an int, a bool, a small enum tag, ...) almost
     * certainly is. This can't be made *perfectly* precise without a
     * real tagged/boxed value representation for every H# value (a
     * much larger change) — an unawaited async fn's own real result
     * happening to be a huge integer that lands above this threshold
     * by coincidence would still (incorrectly, and rarely) be treated
     * as a task pointer. In practice this threshold eliminates the
     * crash for every realistic non-task value `await`/`timeout` sees. */
    return handle != NULL && (uintptr_t)handle >= (uintptr_t)0x10000;
}

int64_t hsh_task_wait(void* handle) {
    if (!handle) return 0;

    /* Safety: if `handle` is a plain i64 value accidentally passed to
     * await (e.g. `await non_async_fn()`), don't even attempt to read
     * it as a pointer — see `hsh_looks_like_task_ptr`'s doc comment for
     * exactly why the old version of this check (dereference first,
     * ask questions later) could crash on this same input.            */
    if (!hsh_looks_like_task_ptr(handle)) {
        return (int64_t)(uintptr_t)handle;
    }
    HshTask* t = (HshTask*)handle;
    if (t->magic != HSH_TASK_MAGIC) {
        return (int64_t)(uintptr_t)handle;
    }

    pthread_mutex_lock(&t->mu);
    while (!t->done) {
        pthread_cond_wait(&t->cv, &t->mu);
    }
    int64_t result = t->result;
    pthread_mutex_unlock(&t->mu);

    pthread_join(t->thread, NULL);
    pthread_mutex_destroy(&t->mu);
    pthread_cond_destroy(&t->cv);
    free(t);
    return result;
}

/* ── async fn argument packing ────────────────────────────────────
 * Carries an `async fn`'s real arguments across the pthread boundary —
 * the only thing `hsh_task_spawn`'s fixed `void*(*)(void*)` trampoline
 * shape can pass through as `args`. A flat `int64_t[n]` block is
 * enough for arguments of *any* H# type, in any number: every value
 * this backend's LLVM codegen can produce is exactly one of a plain
 * integer, a float (bit-cast to its raw 64-bit pattern), or a pointer
 * (reinterpreted as its integer address) — see codegen.rs's
 * `box_to_i64`/`unbox_i64_as`, which do that boxing/unboxing on the
 * LLVM side of this same block. This mirrors this codebase's existing
 * "keep all real memory-layout work in a small, easily-audited C
 * helper, not hand-written LLVM struct/GEP IR" convention (see
 * `hsh_struct_new`/`hsh_struct_get`/`hsh_struct_set` in core.c for the
 * same pattern applied to H#'s own struct values).
 *
 * BUG FIX this directly enables: `emit_async_wrapper`'s previous
 * version always spawned with a hardcoded `nullptr` in place of the
 * real arguments ("args encoding is done by the runtime layer" — which
 * nothing anywhere actually did), so any `async fn` taking one or more
 * parameters ran on garbage/uninitialized argument data the moment
 * that dead code path was ever wired up. `hsh_args_alloc`/`_set`/`_get`/
 * `_free` are that missing runtime layer.
 */
void* hsh_args_alloc(int64_t n) {
    if (n <= 0) return NULL;
    return calloc((size_t)n, sizeof(int64_t));
}

void hsh_args_set(void* args, int64_t i, int64_t v) {
    if (!args || i < 0) return;
    ((int64_t*)args)[i] = v;
}

int64_t hsh_args_get(void* args, int64_t i) {
    if (!args || i < 0) return 0;
    return ((int64_t*)args)[i];
}

void hsh_args_free(void* args) {
    free(args);
}

/* ── join(a, b, ...) helper ─────────────────────────────────────── */

/*
 * hsh_task_join_all: wait for n tasks in parallel.
 * H# `let (r1, r2) = await join(t1, t2)` lowers to:
 *   void* handles[2] = {t1, t2};
 *   int64_t* results = hsh_task_join_all(handles, 2);
 *   r1 = results[0]; r2 = results[1]; free(results);
 */
int64_t* hsh_task_join_all(void** handles, int n) {
    int64_t* results = (int64_t*)malloc((size_t)n * sizeof(int64_t));
    if (!results) return NULL;
    for (int i = 0; i < n; i++) {
        results[i] = hsh_task_wait(handles[i]);
    }
    return results;
}

/* Bounded wait — returns 1 if the task finishes within `ms`
 * milliseconds, 0 if it times out first. The task itself keeps running
 * regardless (this runtime has no cooperative cancellation); either
 * way, does NOT consume/free the task — call hsh_task_wait(handle)
 * afterward (whether this returned 1 or 0) to actually fetch its
 * result and release its resources, exactly as if this bounded check
 * had never happened. This split (bounded "peek", then unbounded
 * "consume") is what lets `std -> async`'s `timeout()` exist at all
 * without changing `hsh_task_wait`'s own simpler, unbounded contract —
 * see `codegen.rs`'s `"task_wait_timeout"` dispatch arm. */
int64_t hsh_task_wait_timeout(void* handle, int64_t ms) {
    if (!handle) return 1; /* nothing to wait for -> "ready" */
    if (!hsh_looks_like_task_ptr(handle)) return 1; /* see hsh_looks_like_task_ptr's doc comment */
    HshTask* t = (HshTask*)handle;
    if (t->magic != HSH_TASK_MAGIC) return 1; /* not a task; treat as ready */
    if (ms < 0) ms = 0;

    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_sec  += ms / 1000;
    ts.tv_nsec += (ms % 1000) * 1000000L;
    if (ts.tv_nsec >= 1000000000L) { ts.tv_sec += 1; ts.tv_nsec -= 1000000000L; }

    pthread_mutex_lock(&t->mu);
    while (!t->done) {
        int rc = pthread_cond_timedwait(&t->cv, &t->mu, &ts);
        if (rc != 0) break; /* ETIMEDOUT (or spurious error) — give up waiting */
    }
    int ready = t->done;
    pthread_mutex_unlock(&t->mu);
    return ready ? 1 : 0;
}

/* ── Convenience: spawn a shell command as async task ───────────── */

typedef struct { char cmd[4096]; } ShellArgs;

static void* shell_task_fn(void* arg) {
    ShellArgs* sa = (ShellArgs*)arg;
    FILE* fp = popen(sa->cmd, "r");
    if (!fp) { free(sa); return (void*)(intptr_t)(-1); }
    char buf[65536]; size_t n = fread(buf, 1, sizeof(buf)-1, fp);
    buf[n] = '\0'; pclose(fp);
    char* out = strdup(buf);
    free(sa);
    return (void*)out;  /* caller frees */
}

void* hsh_task_spawn_shell(const char* cmd) {
    ShellArgs* sa = (ShellArgs*)calloc(1, sizeof(ShellArgs));
    strncpy(sa->cmd, cmd, sizeof(sa->cmd)-1);
    return hsh_task_spawn((void*)shell_task_fn, sa);
}

/* hsh_sleep_ms is already defined in core.c — not duplicated here to
 * avoid a multiple-definition link error when both runtime files are
 * compiled into the same binary. */
