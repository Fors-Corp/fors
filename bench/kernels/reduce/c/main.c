#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static long long N;
static int NUM_THREADS;
static uint64_t *partials;

static uint32_t lowbias32(uint32_t x) {
    x ^= x >> 16;
    x = x * 0x7feb352du;
    x ^= x >> 15;
    x = x * 0x846ca68bu;
    x ^= x >> 16;
    return x;
}

static void *worker(void *arg) {
    long tid = (long)arg;
    long long start = N * tid / NUM_THREADS;
    long long end = N * (tid + 1) / NUM_THREADS;
    uint64_t sum = 0;

    for (long long i = start; i < end; i++) {
        uint32_t x = (uint32_t)i;
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        sum += x % 1000;
    }
    partials[tid] = sum;
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s N threads\n", argv[0]);
        return 1;
    }
    N = atoll(argv[1]);
    NUM_THREADS = atoi(argv[2]);
    if (NUM_THREADS < 1) NUM_THREADS = 1;

    pthread_t *threads = malloc(sizeof(pthread_t) * NUM_THREADS);
    partials = malloc(sizeof(uint64_t) * NUM_THREADS);

    for (long t = 0; t < NUM_THREADS; t++) {
        pthread_create(&threads[t], NULL, worker, (void *)t);
    }
    uint64_t total = 0;
    for (long t = 0; t < NUM_THREADS; t++) {
        pthread_join(threads[t], NULL);
        total += partials[t];
    }

    printf("%llu\n", (unsigned long long)total);

    free(threads);
    free(partials);
    return 0;
}
