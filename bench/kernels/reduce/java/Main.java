public class Main {
    static int lowbias32(int x0) {
        int x = x0;
        x ^= x >>> 16;
        x = x * 0x7feb352d;
        x ^= x >>> 15;
        x = x * 0x846ca68b;
        x ^= x >>> 16;
        return x;
    }

    static long partialSum(long start, long end) {
        long sum = 0;
        for (long i = start; i < end; i++) {
            int x = (int) i;
            x = lowbias32(x);
            x = lowbias32(x);
            x = lowbias32(x);
            x = lowbias32(x);
            sum += Integer.toUnsignedLong(x) % 1000;
        }
        return sum;
    }

    public static void main(String[] args) throws InterruptedException {
        long n = Long.parseLong(args[0]);
        long numThreads = Long.parseLong(args[1]);
        if (numThreads < 1) numThreads = 1;

        final long nf = n;
        final long numThreadsFinal = numThreads;
        long[] partials = new long[(int) numThreads];
        Thread[] threads = new Thread[(int) numThreads];

        for (int t = 0; t < numThreads; t++) {
            final int idx = t;
            long start = nf * idx / numThreadsFinal;
            long end = nf * (idx + 1) / numThreadsFinal;
            threads[t] = new Thread(() -> {
                partials[idx] = partialSum(start, end);
            });
            threads[t].start();
        }
        for (Thread th : threads) {
            th.join();
        }

        long total = 0;
        for (long p : partials) total += p;
        System.out.println(total);
    }
}
