/* Roofline calibration: peak double-precision FLOP rate.
 *
 * Kernel choice (ch06-measurement.md open question 4): CHAINS independent
 * multiply-add recurrences per thread, `iterations` steps each, operating on a
 * handful of doubles held in local variables -- a working set of a few dozen bytes,
 * far under any L1 -- rather than a blocked dgemm micro-kernel. Rationale, for the
 * owner to confirm or override:
 *
 *   1. A correct blocked-dgemm micro-kernel is compute-bound only if its tile size is
 *      tuned to the machine's actual register file and L1 size; get the tile wrong and
 *      it silently measures *bandwidth*, which is exactly the failure mode a roofline
 *      calibration must not have. A multi-accumulator recurrence has no tile to tune:
 *      its arithmetic intensity grows without bound in `iterations` (memory traffic is
 *      O(1), work is O(iterations)), so it is compute-bound by construction.
 *   2. Its FLOP count is exact and trivial to audit: 2 FLOPs (one multiply, one add)
 *      per chain per iteration, full stop -- no dependence on loop order, blocking, or
 *      whether the compiler fuses multiply+add into one hardware FMA (a fusion still
 *      does the same 2 mathematical FLOPs, just in one instruction, which is exactly
 *      the throughput a peak-rate calibration should credit).
 *   3. CHAINS independent accumulators (not one) give the compiler independent
 *      dependency chains to interleave, which is what lets a superscalar/pipelined FPU
 *      approach its issue-rate peak; too few accumulators measure FMA LATENCY, not
 *      throughput. CHAINS is therefore a -D knob that calibrate.py sweeps, taking the
 *      best observed rate as the peak (see the #ifndef below).
 *
 * This calibration measures the MACHINE's achievable peak, not a language's fairness
 * baseline, so unlike bench/langs/c.toml it does not pass -ffp-contract=off: contraction
 * into hardware FMA is exactly the hardware capability being measured here.
 *
 * Usage: flops <iterations> <threads>
 * Prints: "flops_gflops=<v> checksum=<v> wall_s=<v> iterations=<n> threads=<t> chains=<k>"
 *
 * `iterations` is a runtime argument specifically so the compiler cannot fold the
 * recurrence into a closed form at compile time (it would be free to do that for a
 * compile-time-constant trip count). The per-chain multiplier is kept just under 1 and
 * the addend small, so the recurrence is numerically stable (converges towards a fixed
 * point) for any iteration count instead of over/underflowing -- needed because the real
 * calibration run may use iteration counts many orders of magnitude larger than the
 * smoke test's.
 */
#include <pthread.h>
#include <stdlib.h>
#include "common.h"

/* CHAINS is a -D compile-time knob, and calibrate.py SWEEPS it, taking the best rate as the
 * machine's peak. It must not be a guessed constant: each chain is a serial acc = acc*mul + add
 * dependency, so the loop saturates the FPU only when the number of INDEPENDENT chains in flight
 * reaches (FP issue width) x (FMA latency). Below that the kernel measures FMA LATENCY and reports
 * it as "peak FLOP rate" -- a plausible number meaning something else, which would make every
 * later fraction-of-roofline look far better than it is. The compiler also vectorises pairs of
 * chains into one 2-wide FMLA, so the independent-chain count in the emitted loop is CHAINS/2 on
 * this target, not CHAINS. Too many chains spills the 32 vector registers and the rate falls
 * again, so the peak is empirical, per machine and per compiler: sweep, don't assume. */
#ifndef CHAINS
#define CHAINS 32
#endif

typedef struct {
    long iterations;
    cal_barrier *start_barrier;
    double acc[CHAINS];
    double t_start, t_end;
    /* One Block per thread in one malloc'd array: pad to a full cache line so no two threads'
     * accumulator slots or timestamps share one (CAL_CACHELINE, common.h). */
    char pad[CAL_CACHELINE];
} Block;

static void *worker(void *arg) {
    Block *w = arg;
    double mul[CHAINS], add[CHAINS];
    for (int k = 0; k < CHAINS; k++) {
        w->acc[k] = 1.0 + 0.001 * (double)k;
        mul[k] = 0.999999 - 0.0000001 * (double)k;
        add[k] = 0.000001 * (double)(k + 1);
    }
    cal_barrier_wait(w->start_barrier);  /* all threads started before anyone starts timing */
    w->t_start = cal_now();
    for (long i = 0; i < w->iterations; i++) {
        for (int k = 0; k < CHAINS; k++) {
            w->acc[k] = w->acc[k] * mul[k] + add[k];
        }
    }
    w->t_end = cal_now();
    return NULL;
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s <iterations> <threads>\n", argv[0]);
        return 2;
    }
    long iterations = cal_parse_long(argv[1], "iterations");
    long threads = cal_parse_long(argv[2], "threads");

    pthread_t *tids = malloc((size_t)threads * sizeof(pthread_t));
    Block *blocks = malloc((size_t)threads * sizeof(Block));
    if (!tids || !blocks) {
        fprintf(stderr, "allocation failed for threads=%ld\n", threads);
        return 1;
    }
    cal_barrier barrier;
    cal_barrier_init(&barrier, threads);
    for (long t = 0; t < threads; t++) {
        blocks[t].iterations = iterations;
        blocks[t].start_barrier = &barrier;
    }
    for (long t = 0; t < threads; t++) {
        pthread_create(&tids[t], NULL, worker, &blocks[t]);
    }
    for (long t = 0; t < threads; t++) {
        pthread_join(tids[t], NULL);
    }

    double wall_start = blocks[0].t_start, wall_end = blocks[0].t_end;
    double checksum = 0.0;
    for (long t = 0; t < threads; t++) {
        if (blocks[t].t_start < wall_start) wall_start = blocks[t].t_start;
        if (blocks[t].t_end > wall_end) wall_end = blocks[t].t_end;
        for (int k = 0; k < CHAINS; k++) checksum += blocks[t].acc[k];
    }
    double wall = wall_end - wall_start;

    double flops = 2.0 * (double)CHAINS * (double)iterations * (double)threads;
    double gflops = wall > 0.0 ? flops / wall / 1e9 : 0.0;

    printf("flops_gflops=%.6f checksum=%.6f wall_s=%.9f iterations=%ld threads=%ld chains=%d\n",
           gflops, checksum, wall, iterations, threads, CHAINS);

    free(tids);
    free(blocks);
    return 0;
}
