import sys


def main():
    n = int(sys.argv[1])

    perm = list(range(n))
    perm1 = list(range(n))
    count = [0] * n

    r = n
    checksum = 0
    maxflips = 0
    sign = 1

    while True:
        while r != 1:
            count[r - 1] = r
            r -= 1
        perm[:] = perm1

        flips = 0
        while True:
            k = perm[0]
            if k == 0:
                break
            k2 = (k + 1) >> 1
            i = 0
            while i < k2:
                perm[i], perm[k - i] = perm[k - i], perm[i]
                i += 1
            flips += 1

        checksum += sign * flips
        if flips > maxflips:
            maxflips = flips

        done = False
        while True:
            if r == n:
                done = True
                break
            perm0 = perm1[0]
            for i in range(r):
                perm1[i] = perm1[i + 1]
            perm1[r] = perm0
            count[r] -= 1
            if count[r] > 0:
                break
            r += 1
        if done:
            break
        sign = -sign

    print(checksum)
    print(f"Pfannkuchen({n}) = {maxflips}")


if __name__ == "__main__":
    main()
