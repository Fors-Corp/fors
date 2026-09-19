public class Main {
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);

        int[] perm = new int[n];
        int[] perm1 = new int[n];
        int[] count = new int[n];
        for (int i = 0; i < n; i++) perm1[i] = i;

        int r = n;
        long checksum = 0;
        int maxflips = 0;
        long sign = 1;

        for (;;) {
            while (r != 1) {
                count[r - 1] = r;
                r--;
            }
            System.arraycopy(perm1, 0, perm, 0, n);

            int flips = 0;
            for (;;) {
                int k = perm[0];
                if (k == 0) break;
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

            boolean done = false;
            for (;;) {
                if (r == n) {
                    done = true;
                    break;
                }
                int perm0 = perm1[0];
                for (int i = 0; i < r; i++) perm1[i] = perm1[i + 1];
                perm1[r] = perm0;
                count[r]--;
                if (count[r] > 0) break;
                r++;
            }
            if (done) break;
            sign = -sign;
        }

        System.out.println(checksum);
        System.out.println("Pfannkuchen(" + n + ") = " + maxflips);
    }
}
