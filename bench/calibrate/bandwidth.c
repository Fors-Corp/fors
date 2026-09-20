/* Roofline calibration: memory bandwidth, STREAM-triad style.
 *
 * a[i] = b[i] + s*c[i] over three arrays of `n` doubles, run `reps` times per invocation,
 * split into `threads` contiguous blocks (block t owns [t*n/threads, (t+1)*n/threads)).
 * Each thread first-touches (initialises) its own block before the timed loop, so pages
 * are faulted in by the same thread that later reads/writes them.
 *
 * Usage: bandwidth <n> <reps> <threads>
 *   n        total array length (doubles); size arrays several times the last-level
 *            cache for a real calibration run, or tiny for a smoke test.
 *   reps     repetitions of the triad within the timed region (amortises thread
 *            start/join cost and gives the clock enough elapsed time to be accurate).
 *   threads  thread count.
 *
 * Prints one line: "bandwidth_gbps=<v> checksum=<v> wall_s=<v> n=<n> reps=<r> threads=<t>"
 * bandwidth_gbps counts 3 * 8 bytes moved per element per rep (2 reads of b/c, 1 write
 * of a) -- the standard STREAM-triad accounting. The checksum (serial sum of a[] after
 * the timed region) is printed so the compiler cannot dead-code-eliminate the loop, and
 * so calibrate.py can sanity-check that repeated runs at a fixed size, reps and thread
 * count are stable (an unstable checksum would mean the arithmetic itself is broken,
 * not just noisy timing).
 *
 * Timing excludes malloc and first-touch: every thread initialises its own block, then all
 * threads meet at a start barrier (cal_barrier, common.h -- macOS has no pthread_barrier_t),
 * and only then does each record its own monotonic timestamp around its timed loop. The wall
 * time reported is max(end) - min(start) across threads. The barrier is what makes that span
 * mean "the machine was running this kernel on `threads` threads": without it a thread that
 * finished first-touch early would time itself while siblings were still page-faulting, and
 * the aggregate byte rate would be understated by the start skew.
 */
#include <pthread.h>
#include <stdlib.h>
#include "common.h"

typedef struct {
    double *a, *b, *c;
    long start, end;
    long reps;
    cal_barrier *start_barrier;
    double t_start, t_end;
    /* One Block per thread lives in one malloc'd array; pad each to a full cache line so two
     * threads' t_start/t_end writes never share one (CAL_CACHELINE, common.h). */
    char pad[CAL_CACHELINE];
} Block;

static void *worker(void *arg) {
    Block *w = (Block *)arg;
    for (long i = w->start; i < w->end; i++) {
        w->b[i] = (double)(i % 7) + 1.0;
        w->c[i] = (double)(i % 5) + 1.0;
        w->a[i] = 0.0;
    }
    const double s = 3.0;
    /* Every thread has finished first-touching its own block before ANY thread starts timing:
     * without this the span below would include siblings' page faults (see common.h). */
    cal_barrier_wait(w->start_barrier);
    w->t_start = cal_now();
    for (long r = 0; r < w->reps; r++) {
        for (long i = w->start; i < w->end; i++) {
            w->a[i] = w->b[i] + s * w->c[i];
        }
    }
    w->t_end = cal_now();
    return NULL;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s <n> <reps> <threads>\n", argv[0]);
        return 2;
    }
    long n = cal_parse_long(argv[1], "n");
    long reps = cal_parse_long(argv[2], "reps");
    long threads = cal_parse_long(argv[3], "threads");
    if (threads > n) threads = n;

    double *a = malloc((size_t)n * sizeof(double));
    double *b = malloc((size_t)n * sizeof(double));
    double *c = malloc((size_t)n * sizeof(double));
    if (!a || !b || !c) {
        fprintf(stderr, "allocation failed for n=%ld\n", n);
        return 1;
    }

    pthread_t *tids = malloc((size_t)threads * sizeof(pthread_t));
    Block *blocks = malloc((size_t)threads * sizeof(Block));
    if (!tids || !blocks) {
        fprintf(stderr, "allocation failed for threads=%ld\n", threads);
        return 1;
    }
    cal_barrier barrier;
    cal_barrier_init(&barrier, threads);
    for (long t = 0; t < threads; t++) {
        blocks[t].start_barrier = &barrier;
        blocks[t].a = a;
        blocks[t].b = b;
        blocks[t].c = c;
        blocks[t].start = t * n / threads;
        blocks[t].end = (t + 1) * n / threads;
        blocks[t].reps = reps;
    }
    for (long t = 0; t < threads; t++) {
        pthread_create(&tids[t], NULL, worker, &blocks[t]);
    }
    for (long t = 0; t < threads; t++) {
        pthread_join(tids[t], NULL);
    }

    double wall_start = blocks[0].t_start, wall_end = blocks[0].t_end;
    for (long t = 1; t < threads; t++) {
        if (blocks[t].t_start < wall_start) wall_start = blocks[t].t_start;
        if (blocks[t].t_end > wall_end) wall_end = blocks[t].t_end;
    }
    double wall = wall_end - wall_start;

    double checksum = 0.0;
    for (long i = 0; i < n; i++) checksum += a[i];

    double bytes = 3.0 * 8.0 * (double)n * (double)reps;
    double gbps = wall > 0.0 ? bytes / wall / 1e9 : 0.0;

    printf("bandwidth_gbps=%.6f checksum=%.6f wall_s=%.9f n=%ld reps=%ld threads=%ld\n",
           gbps, checksum, wall, n, reps, threads);

    free(a);
    free(b);
    free(c);
    free(tids);
    free(blocks);
    return 0;
}
