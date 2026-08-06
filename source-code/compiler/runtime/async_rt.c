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

int64_t hsh_task_wait(void* handle) {
    if (!handle) return 0;

    /* Safety: if `handle` is a plain i64 value accidentally passed to
     * await (e.g. `await non_async_fn()`), the magic check prevents us
     * from treating it as a HshTask*.  We return it as-is.            */
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
