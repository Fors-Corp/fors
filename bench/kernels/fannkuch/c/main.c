#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    int n = atoi(argv[1]);
    int perm[n];
    int perm1[n];
    int count[n];

    for (int i = 0; i < n; i++) perm1[i] = i;

    int r = n;
    int checksum = 0;
    int maxflips = 0;
    int sign = 1;

    for (;;) {
        while (r != 1) {
            count[r - 1] = r;
            r--;
        }
        for (int i = 0; i < n; i++) perm[i] = perm1[i];

        int flips = 0;
        int k;
        while (!((k = perm[0]) == 0)) {
            int k2 = (k + 1) >> 1;
            for (int i = 0; i < k2; i++) {
                int t = perm[i];
                perm[i] = perm[k - i];
                perm[k - i] = t;
            }
            flips++;
        }

        checksum += sign * flips;
        if (flips > maxflips) maxflips = flips;

        int done = 0;
        for (;;) {
            if (r == n) {
                done = 1;
                break;
            }
            int perm0 = perm1[0];
            for (int i = 0; i < r; i++) perm1[i] = perm1[i + 1];
            perm1[r] = perm0;
            if (--count[r] > 0) break;
            r++;
        }
        if (done) break;
        sign = -sign;
    }

    printf("%d\n", checksum);
    printf("Pfannkuchen(%d) = %d\n", n, maxflips);
    return 0;
}
