import java.util.concurrent.ForkJoinPool;
import java.util.stream.IntStream;

public class MainStream {
    static int n;
    static double[] a;
    static double[] b;
    static double[] c;

    public static void main(String[] args) throws Exception {
        n = Integer.parseInt(args[0]);
        int threads = Integer.parseInt(args[1]);
        if (threads < 1) threads = 1;
        if (threads > n) threads = n;
        final int fthreads = threads;

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

        // Tuned axis vs Main.java (ExecutorService + Future): the same row-block
        // decomposition, driven by a ForkJoinPool plus a parallel IntStream over the
        // same precomputed block bounds. Same per-row values, same serial reduction
        // after the join, so output is byte-identical at every thread count.
        ForkJoinPool pool = new ForkJoinPool(fthreads);
        pool.submit(() -> IntStream.range(0, fthreads).parallel().forEach(t -> {
            int rowStart = bounds[t];
            int rowEnd = bounds[t + 1];
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
        })).get();
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
