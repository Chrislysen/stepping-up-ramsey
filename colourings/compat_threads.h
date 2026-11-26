/* compat_threads.h -- a few Windows calls (threads, a millisecond clock, one atomic compare-and-swap, a 64-bit
   ftell), given by pthreads on Linux so that verify_affine.c, which uses the threads and the clock, builds there
   with gcc. On Windows it is windows.h and nothing else. */
#ifndef COMPAT_THREADS_H
#define COMPAT_THREADS_H
#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
typedef unsigned long DWORD;
typedef void *LPVOID;
typedef long LONG;
typedef unsigned long long ULONGLONG;
#define WINAPI
typedef DWORD (*LPTHREAD_START_ROUTINE)(LPVOID);
typedef struct compat_thread { pthread_t th; LPTHREAD_START_ROUTINE f; LPVOID arg; volatile int done; } *HANDLE;
#define TRUE 1
#define FALSE 0
#define WAIT_TIMEOUT 258
#define INFINITE 0xFFFFFFFFu
#define THREAD_PRIORITY_BELOW_NORMAL 0
static void *compat_tramp(void *p) { HANDLE h = p; h->f(h->arg); h->done = 1; return NULL; }
static HANDLE CreateThread(void *sa, size_t stack, LPTHREAD_START_ROUTINE f, LPVOID arg, DWORD flags, void *id) {
    (void)sa; (void)stack; (void)flags; (void)id;
    HANDLE h = malloc(sizeof *h);
    h->f = f; h->arg = arg; h->done = 0;
    if (pthread_create(&h->th, NULL, compat_tramp, h)) { free(h); return NULL; }
    return h;
}
static int SetThreadPriority(HANDLE h, int p) { (void)h; (void)p; return 1; }
static ULONGLONG GetTickCount64(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (ULONGLONG)ts.tv_sec * 1000ULL + (ULONGLONG)(ts.tv_nsec / 1000000);
}
static DWORD WaitForMultipleObjects(DWORD n, HANDLE *h, int all, DWORD ms) {   /* waits for all of them */
    (void)all;
    ULONGLONG t0 = GetTickCount64();
    for (;;) {
        int alldone = 1;
        for (DWORD i = 0; i < n; i++) if (!h[i]->done) alldone = 0;
        if (alldone) return 0;
        if (ms != INFINITE && GetTickCount64() - t0 >= ms) return WAIT_TIMEOUT;
        usleep(50000);
    }
}
#define InterlockedCompareExchange(dest, exchange, comparand) __sync_val_compare_and_swap((dest), (comparand), (exchange))
#define _ftelli64 ftello
#endif
#endif
