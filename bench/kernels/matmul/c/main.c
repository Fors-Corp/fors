#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

static int N;
static double *A, *B, *C;

typedef struct {
    int row_start;
    int row_end; /* exclusive */
} work_t;

static void *worker(void *arg) {
    work_t *w = (work_t *)arg;
    for (int i = w->row_start; i < w->row_end; i++) {
        for (int j = 0; j < N; j++) {
            C[i * N + j] = 0.0;
        }
        for (int k = 0; k < N; k++) {
            double a = A[i * N + k];
            for (int j = 0; j < N; j++) {
                C[i * N + j] += a * B[k * N + j];
            }
        }
    }
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s N threads\n", argv[0]);
        return 1;
    }
    N = atoi(argv[1]);
    int threads = atoi(argv[2]);
    if (threads < 1) threads = 1;
    if (threads > N) threads = N;

    A = (double *)malloc((size_t)N * N * sizeof(double));
    B = (double *)malloc((size_t)N * N * sizeof(double));
    C = (double *)malloc((size_t)N * N * sizeof(double));
    if (!A || !B || !C) {
        fprintf(stderr, "allocation failed\n");
        return 1;
    }

    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            A[i * N + j] = (double)(((i * j) % 7) + 1);
            B[i * N + j] = (double)(((i + j) % 5) + 1);
        }
    }

    pthread_t *tids = (pthread_t *)malloc((size_t)threads * sizeof(pthread_t));
    work_t *works = (work_t *)malloc((size_t)threads * sizeof(work_t));

    int base = N / threads;
    int rem = N % threads;
    int row = 0;
    for (int t = 0; t < threads; t++) {
        int count = base + (t < rem ? 1 : 0);
        works[t].row_start = row;
        works[t].row_end = row + count;
        row += count;
    }

    for (int t = 0; t < threads; t++) {
        pthread_create(&tids[t], NULL, worker, &works[t]);
    }
    for (int t = 0; t < threads; t++) {
        pthread_join(tids[t], NULL);
    }

    double sum = 0.0;
    double trace = 0.0;
    for (int i = 0; i < N; i++) {
        for (int j = 0; j < N; j++) {
            sum += C[i * N + j];
        }
        trace += C[i * N + i];
    }

    printf("%.0f\n", sum);
    printf("%.0f\n", trace);

    free(A);
    free(B);
    free(C);
    free(tids);
    free(works);

    return 0;
}
