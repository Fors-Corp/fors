import java.util.Locale;

public class Main {
    static double evalA(long i, long j) {
        long ij = i + j;
        return 1.0 / (double) ((ij * (ij + 1)) / 2 + i + 1);
    }

    static void evalATimesU(long n, double[] u, double[] au) {
        for (int i = 0; i < n; i++) {
            double sum = 0.0;
            for (int j = 0; j < n; j++) {
                sum += evalA(i, j) * u[j];
            }
            au[i] = sum;
        }
    }

    static void evalAtTimesU(long n, double[] u, double[] au) {
        for (int i = 0; i < n; i++) {
            double sum = 0.0;
            for (int j = 0; j < n; j++) {
                sum += evalA(j, i) * u[j];
            }
            au[i] = sum;
        }
    }

    static void evalAtATimesU(long n, double[] u, double[] atAu, double[] tmp) {
        evalATimesU(n, u, tmp);
        evalAtTimesU(n, tmp, atAu);
    }

    public static void main(String[] args) {
        long n = Long.parseLong(args[0]);
        int ni = (int) n;

        double[] u = new double[ni];
        double[] v = new double[ni];
        double[] tmp = new double[ni];

        for (int i = 0; i < ni; i++) {
            u[i] = 1.0;
        }

        for (int i = 0; i < 10; i++) {
            evalAtATimesU(n, u, v, tmp);
            evalAtATimesU(n, v, u, tmp);
        }

        double vBv = 0.0;
        double vv = 0.0;
        for (int i = 0; i < ni; i++) {
            vBv += u[i] * v[i];
            vv += v[i] * v[i];
        }

        System.out.printf(Locale.ROOT, "%.9f%n", Math.sqrt(vBv / vv));
    }
}
