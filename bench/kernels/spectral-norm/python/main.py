import sys
import math


def eval_a(i, j):
    ij = i + j
    return 1.0 / ((ij * (ij + 1)) // 2 + i + 1)


def eval_a_times_u(n, u, au):
    for i in range(n):
        s = 0.0
        for j in range(n):
            s += eval_a(i, j) * u[j]
        au[i] = s


def eval_at_times_u(n, u, au):
    for i in range(n):
        s = 0.0
        for j in range(n):
            s += eval_a(j, i) * u[j]
        au[i] = s


def eval_ata_times_u(n, u, at_au, tmp):
    eval_a_times_u(n, u, tmp)
    eval_at_times_u(n, tmp, at_au)


def main():
    n = int(sys.argv[1])

    u = [1.0] * n
    v = [0.0] * n
    tmp = [0.0] * n

    for _ in range(10):
        eval_ata_times_u(n, u, v, tmp)
        eval_ata_times_u(n, v, u, tmp)

    v_bv = 0.0
    vv = 0.0
    for i in range(n):
        v_bv += u[i] * v[i]
        vv += v[i] * v[i]

    print(f"{math.sqrt(v_bv / vv):.9f}")


if __name__ == "__main__":
    main()
