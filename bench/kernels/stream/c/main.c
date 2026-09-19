#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

static long long N;
static long long R;
static double *a, *b, *carr;
static const double s = 3.0;

typedef struct {
    long long start;
    long long end; /* exclusive */
} work_t;

static void *worker(void *arg) {
    work_t *w = (work_t *)arg;
    /* First-touch: each thread initialises its own block. */
    for (long long i = w->start; i < w->end; i++) {
        b[i] = (double)((i % 7) + 1);
        carr[i] = (double)((i % 5) + 1);
        a[i] = 0.0;
    }
    for (long long r = 0; r < R; r++) {
        for (long long i = w->start; i < w->end; i++) {
            a[i] = b[i] + s * carr[i];
        }
    }
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: %s N R threads\n", argv[0]);
        return 1;
    }
    N = atoll(argv[1]);
    R = atoll(argv[2]);
    int threads = atoi(argv[3]);
    if (threads < 1) threads = 1;
    if (threads > N) threads = (int)N;

    a = (double *)malloc((size_t)N * sizeof(double));
    b = (double *)malloc((size_t)N * sizeof(double));
    carr = (double *)malloc((size_t)N * sizeof(double));
    if (!a || !b || !carr) {
        fprintf(stderr, "allocation failed\n");
        return 1;
    }

    pthread_t *tids = (pthread_t *)malloc((size_t)threads * sizeof(pthread_t));
    work_t *works = (work_t *)malloc((size_t)threads * sizeof(work_t));

    long long base = N / threads;
    long long rem = N % threads;
    long long idx = 0;
    for (int t = 0; t < threads; t++) {
        long long count = base + (t < rem ? 1 : 0);
        works[t].start = idx;
        works[t].end = idx + count;
        idx += count;
    }

    for (int t = 0; t < threads; t++) {
        pthread_create(&tids[t], NULL, worker, &works[t]);
    }
    for (int t = 0; t < threads; t++) {
        pthread_join(tids[t], NULL);
    }

    double sum = 0.0;
    for (long long i = 0; i < N; i++) {
        sum += a[i];
    }

    printf("%.0f\n", sum);

    free(a);
    free(b);
    free(carr);
    free(tids);
    free(works);

    return 0;
}
