import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

public class Main {
    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        int r = Integer.parseInt(args[1]);
        int threads = Integer.parseInt(args[2]);
        if (threads < 1) threads = 1;
        if (threads > n) threads = n;

        double[] a = new double[n];
        double[] b = new double[n];
        double[] c = new double[n];
        double s = 3.0;

        int base = n / threads;
        int rem = n % threads;
        int[] bounds = new int[threads + 1];
        int idx = 0;
        bounds[0] = 0;
        for (int t = 0; t < threads; t++) {
            int count = base + (t < rem ? 1 : 0);
            idx += count;
            bounds[t + 1] = idx;
        }

        ExecutorService pool = Executors.newFixedThreadPool(threads);
        List<Future<?>> futures = new ArrayList<>();
        final int rr = r;
        for (int t = 0; t < threads; t++) {
            final int start = bounds[t];
            final int end = bounds[t + 1];
            futures.add(pool.submit(() -> {
                for (int i = start; i < end; i++) {
                    b[i] = (i % 7) + 1;
                    c[i] = (i % 5) + 1;
                    a[i] = 0.0;
                }
                for (int rep = 0; rep < rr; rep++) {
                    for (int i = start; i < end; i++) {
                        a[i] = b[i] + s * c[i];
                    }
                }
            }));
        }
        for (Future<?> f : futures) {
            f.get();
        }
        pool.shutdown();

        double sum = 0.0;
        for (int i = 0; i < n; i++) {
            sum += a[i];
        }
        System.out.printf("%.0f%n", sum);
    }
}
