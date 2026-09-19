import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.ArrayList;
import java.util.List;

public class Main {
    static int n;
    static double[] a;
    static double[] b;
    static double[] c;

    public static void main(String[] args) throws Exception {
        n = Integer.parseInt(args[0]);
        int threads = Integer.parseInt(args[1]);
        if (threads < 1) threads = 1;
        if (threads > n) threads = n;

        a = new double[n * n];
        b = new double[n * n];
        c = new double[n * n];

        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                a[i * n + j] = ((i * j) % 7) + 1;
                b[i * n + j] = ((i + j) % 5) + 1;
            }
        }

        int base = n / threads;
        int rem = n % threads;
        int[] bounds = new int[threads + 1];
        int row = 0;
        bounds[0] = 0;
        for (int t = 0; t < threads; t++) {
            int count = base + (t < rem ? 1 : 0);
            row += count;
            bounds[t + 1] = row;
        }

        ExecutorService pool = Executors.newFixedThreadPool(threads);
        List<Future<?>> futures = new ArrayList<>();
        for (int t = 0; t < threads; t++) {
            final int rowStart = bounds[t];
            final int rowEnd = bounds[t + 1];
            futures.add(pool.submit(() -> {
                for (int i = rowStart; i < rowEnd; i++) {
                    for (int j = 0; j < n; j++) {
                        c[i * n + j] = 0.0;
                    }
                    for (int k = 0; k < n; k++) {
                        double av = a[i * n + k];
                        for (int j = 0; j < n; j++) {
                            c[i * n + j] += av * b[k * n + j];
                        }
                    }
                }
            }));
        }
        for (Future<?> f : futures) {
            f.get();
        }
        pool.shutdown();

        double sum = 0.0;
        double trace = 0.0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                sum += c[i * n + j];
            }
            trace += c[i * n + i];
        }

        System.out.printf("%.0f%n", sum);
        System.out.printf("%.0f%n", trace);
    }
}
