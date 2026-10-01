import java.util.concurrent.ForkJoinPool;
import java.util.stream.IntStream;

public class MainStream {
    static int n;
    static double[] a;
    static double[] b;
    static double[] c;

    // Same BLOCK = 64 as every other matmul-blocked implementation.
    static final int BLOCK = 64;

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

        // Tuned axes vs naive matmul/java: cache blocking (same kk/ii/jj tiles as
        // matmul-blocked Main.java) driven by a ForkJoinPool + parallel IntStream
        // over the same block bounds (same pattern as matmul MainStream.java).
        ForkJoinPool pool = new ForkJoinPool(fthreads);
        pool.submit(() -> IntStream.range(0, fthreads).parallel().forEach(t -> {
            int rowStart = bounds[t];
            int rowEnd = bounds[t + 1];
            for (int i = rowStart; i < rowEnd; i++) {
                for (int j = 0; j < n; j++) {
                    c[i * n + j] = 0.0;
                }
            }
            for (int kk = 0; kk < n; kk += BLOCK) {
                int kEnd = Math.min(kk + BLOCK, n);
                for (int ii = rowStart; ii < rowEnd; ii += BLOCK) {
                    int iEnd = Math.min(ii + BLOCK, rowEnd);
                    for (int jj = 0; jj < n; jj += BLOCK) {
                        int jEnd = Math.min(jj + BLOCK, n);
                        for (int i = ii; i < iEnd; i++) {
                            for (int k = kk; k < kEnd; k++) {
                                double av = a[i * n + k];
                                for (int j = jj; j < jEnd; j++) {
                                    c[i * n + j] += av * b[k * n + j];
                                }
                            }
                        }
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
