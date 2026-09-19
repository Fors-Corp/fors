#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

static int N;
static int NUM_THREADS;
static long *row_counts;

static void *worker(void *arg) {
    long tid = (long)arg;
    int row_start = (int)((long)N * tid / NUM_THREADS);
    int row_end = (int)((long)N * (tid + 1) / NUM_THREADS);
    long count = 0;

    for (int py = row_start; py < row_end; py++) {
        double ci0 = 2.0 * py / N - 1.0;
        for (int px = 0; px < N; px++) {
            double cr = 2.0 * px / N - 1.5;
            double zr = 0.0, zi = 0.0;
            int iter = 0;
            while (iter < 50 && zr * zr + zi * zi <= 4.0) {
                double tr = zr * zr - zi * zi + cr;
                double ti = 2.0 * zr * zi + ci0;
                zr = tr;
                zi = ti;
                iter++;
            }
            if (iter == 50) {
                count++;
            }
        }
    }
    row_counts[tid] = count;
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s N threads\n", argv[0]);
        return 1;
    }
    N = atoi(argv[1]);
    NUM_THREADS = atoi(argv[2]);
    if (NUM_THREADS < 1) NUM_THREADS = 1;

    pthread_t *threads = malloc(sizeof(pthread_t) * NUM_THREADS);
    row_counts = malloc(sizeof(long) * NUM_THREADS);

    for (long t = 0; t < NUM_THREADS; t++) {
        pthread_create(&threads[t], NULL, worker, (void *)t);
    }
    long total = 0;
    for (long t = 0; t < NUM_THREADS; t++) {
        pthread_join(threads[t], NULL);
        total += row_counts[t];
    }

    printf("%ld\n", total);

    free(threads);
    free(row_counts);
    return 0;
}
