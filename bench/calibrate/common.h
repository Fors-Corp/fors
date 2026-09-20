/* Shared helpers for the M0.P roofline calibration kernels (bandwidth.c, flops.c).
 * Kept in a header, not a .o, so calibrate.py can compile each kernel with one clang
 * invocation and never has to link a separate object file. */
#ifndef CALIBRATE_COMMON_H
#define CALIBRATE_COMMON_H

#include <sched.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* Monotonic wall clock, seconds, as a double. CLOCK_MONOTONIC never jumps for NTP/user
 * clock changes, unlike gettimeofday/CLOCK_REALTIME. */
static double cal_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

/* Parse a required positive-integer CLI argument, or exit(2) with a message on stderr.
 * exit(2) (not abort/assert) so a calling driver can distinguish "bad arguments" from
 * a crash while still getting a message it can show the user. */
static long cal_parse_long(const char *s, const char *what) {
    char *end = NULL;
    long v = strtol(s, &end, 10);
    if (s[0] == '\0' || *end != '\0' || v <= 0) {
        fprintf(stderr, "invalid %s: %s (must be a positive integer)\n", what, s);
        exit(2);
    }
    return v;
}

/* Start barrier. macOS has no pthread_barrier_t, and without a barrier a thread that
 * finished its first-touch initialisation early starts its timed loop while its siblings are
 * still page-faulting: the reported span (max end - min start) then covers a stretch in which
 * the machine was NOT fully parallel, and the derived throughput is silently understated.
 * Every calibration kernel therefore joins this barrier between init and its first clock read.
 * sched_yield() in the spin keeps it correct when threads > cores. */
typedef struct {
    atomic_long arrived;
    long total;
} cal_barrier;

static void cal_barrier_init(cal_barrier *b, long total) {
    atomic_init(&b->arrived, 0);
    b->total = total;
}

static void cal_barrier_wait(cal_barrier *b) {
    atomic_fetch_add_explicit(&b->arrived, 1, memory_order_acq_rel);
    while (atomic_load_explicit(&b->arrived, memory_order_acquire) < b->total) {
        sched_yield();
    }
}

/* Cache-line padding for per-thread scratch. Apple silicon's line is 128 bytes; per-thread
 * structs that live in one malloc'd array must not share a line, or two threads' writes ping-pong
 * the line between cores and the kernel measures coherence traffic instead of what it meant to. */
#define CAL_CACHELINE 128

#endif
