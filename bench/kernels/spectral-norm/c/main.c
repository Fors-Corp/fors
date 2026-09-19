#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static double eval_A(long i, long j) {
    long ij = i + j;
    return 1.0 / (double)((ij * (ij + 1)) / 2 + i + 1);
}

static void eval_A_times_u(long n, const double *u, double *Au) {
    for (long i = 0; i < n; i++) {
        double sum = 0.0;
        for (long j = 0; j < n; j++) {
            sum += eval_A(i, j) * u[j];
        }
        Au[i] = sum;
    }
}

static void eval_At_times_u(long n, const double *u, double *Au) {
    for (long i = 0; i < n; i++) {
        double sum = 0.0;
        for (long j = 0; j < n; j++) {
            sum += eval_A(j, i) * u[j];
        }
        Au[i] = sum;
    }
}

static void eval_AtA_times_u(long n, const double *u, double *AtAu, double *tmp) {
    eval_A_times_u(n, u, tmp);
    eval_At_times_u(n, tmp, AtAu);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s n\n", argv[0]);
        return 1;
    }
    long n = atol(argv[1]);

    double *u = malloc((size_t)n * sizeof(double));
    double *v = malloc((size_t)n * sizeof(double));
    double *tmp = malloc((size_t)n * sizeof(double));

    for (long i = 0; i < n; i++) {
        u[i] = 1.0;
    }

    for (int i = 0; i < 10; i++) {
        eval_AtA_times_u(n, u, v, tmp);
        eval_AtA_times_u(n, v, u, tmp);
    }

    double vBv = 0.0;
    double vv = 0.0;
    for (long i = 0; i < n; i++) {
        vBv += u[i] * v[i];
        vv += v[i] * v[i];
    }

    printf("%.9f\n", sqrt(vBv / vv));

    free(u);
    free(v);
    free(tmp);
    return 0;
}
