public class Main {
    static long countRows(long n, long rowStart, long rowEnd) {
        long count = 0;
        for (long py = rowStart; py < rowEnd; py++) {
            double ci0 = 2.0 * py / n - 1.0;
            for (long px = 0; px < n; px++) {
                double cr = 2.0 * px / n - 1.5;
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
        return count;
    }

    public static void main(String[] args) throws InterruptedException {
        long n = Long.parseLong(args[0]);
        long numThreads = Long.parseLong(args[1]);
        if (numThreads < 1) numThreads = 1;

        final long nf = n;
        final long numThreadsFinal = numThreads;
        long[] counts = new long[(int) numThreads];
        Thread[] threads = new Thread[(int) numThreads];

        for (int t = 0; t < numThreads; t++) {
            final int idx = t;
            long rowStart = nf * idx / numThreadsFinal;
            long rowEnd = nf * (idx + 1) / numThreadsFinal;
            threads[t] = new Thread(() -> {
                counts[idx] = countRows(nf, rowStart, rowEnd);
            });
            threads[t].start();
        }
        for (Thread th : threads) {
            th.join();
        }

        long total = 0;
        for (long c : counts) total += c;
        System.out.println(total);
    }
}
