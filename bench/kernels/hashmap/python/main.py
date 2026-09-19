import sys


def main():
    n = int(sys.argv[1])

    counts_int = {}
    counts_str = {}

    x = 42
    mod1 = n // 4 + 1
    for _ in range(n):
        x = (x * 48271) % 2147483647
        key = x % mod1
        counts_int[key] = counts_int.get(key, 0) + 1

    n2 = n // 4
    mod2 = n // 16 + 1
    for _ in range(n2):
        x = (x * 48271) % 2147483647
        num = x % mod2
        key = "k" + str(num)
        counts_str[key] = counts_str.get(key, 0) + 1

    MOD = 1000000007
    checksum = 0
    for k, c in counts_int.items():
        checksum = (checksum + k * c) % MOD
    for k, c in counts_str.items():
        num = int(k[1:])
        checksum = (checksum + num * c) % MOD

    print(len(counts_int))
    print(len(counts_str))
    print(checksum)


if __name__ == "__main__":
    main()
