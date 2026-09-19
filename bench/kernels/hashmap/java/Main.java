import java.util.HashMap;

public class Main {
    public static void main(String[] args) {
        long n = Long.parseLong(args[0]);

        HashMap<Long, Long> countsInt = new HashMap<>();
        HashMap<String, Long> countsStr = new HashMap<>();

        long x = 42L;
        long mod1 = n / 4 + 1;
        for (long i = 0; i < n; i++) {
            x = (x * 48271L) % 2147483647L;
            long key = x % mod1;
            countsInt.merge(key, 1L, Long::sum);
        }

        long n2 = n / 4;
        long mod2 = n / 16 + 1;
        for (long i = 0; i < n2; i++) {
            x = (x * 48271L) % 2147483647L;
            long num = x % mod2;
            String key = "k" + num;
            countsStr.merge(key, 1L, Long::sum);
        }

        final long MOD = 1000000007L;
        long checksum = 0;
        for (var e : countsInt.entrySet()) {
            checksum = (checksum + (e.getKey() % MOD) * (e.getValue() % MOD)) % MOD;
        }
        for (var e : countsStr.entrySet()) {
            long num = Long.parseLong(e.getKey().substring(1));
            checksum = (checksum + (num % MOD) * (e.getValue() % MOD)) % MOD;
        }

        System.out.println(countsInt.size());
        System.out.println(countsStr.size());
        System.out.println(checksum);
    }
}
