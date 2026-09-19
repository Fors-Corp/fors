import sys
import multiprocessing as mp
from multiprocessing import shared_memory


def row_bounds(n, threads):
    base, rem = divmod(n, threads)
    bounds = [0] * (threads + 1)
    row = 0
    for t in range(threads):
        count = base + (1 if t < rem else 0)
        row += count
        bounds[t + 1] = row
    return bounds


def worker(n, a_bytes, b_bytes, c_shm_name, row_start, row_end):
    a = memoryview(a_bytes)
    b = memoryview(b_bytes)
    c_shm = shared_memory.SharedMemory(name=c_shm_name)
    c = memoryview(c_shm.buf).cast("d")
    for i in range(row_start, row_end):
        base_i = i * n
        for j in range(n):
            c[base_i + j] = 0.0
        for k in range(n):
            av = a[base_i + k]
            base_k = k * n
            for j in range(n):
                c[base_i + j] += av * b[base_k + j]
    c.release()
    c_shm.close()


def main():
    n = int(sys.argv[1])
    threads = int(sys.argv[2])
    if threads < 1:
        threads = 1
    if threads > n:
        threads = n

    a = [0.0] * (n * n)
    b = [0.0] * (n * n)
    for i in range(n):
        for j in range(n):
            a[i * n + j] = float(((i * j) % 7) + 1)
            b[i * n + j] = float(((i + j) % 5) + 1)

    import array
    a_arr = array.array("d", a)
    b_arr = array.array("d", b)

    c_shm = shared_memory.SharedMemory(create=True, size=n * n * 8)
    try:
        bounds = row_bounds(n, threads)
        procs = []
        for t in range(threads):
            row_start = bounds[t]
            row_end = bounds[t + 1]
            p = mp.Process(
                target=worker,
                args=(n, a_arr, b_arr, c_shm.name, row_start, row_end),
            )
            procs.append(p)
            p.start()
        for p in procs:
            p.join()

        c = memoryview(c_shm.buf).cast("d")
        total = 0.0
        trace = 0.0
        for i in range(n):
            base_i = i * n
            for j in range(n):
                total += c[base_i + j]
            trace += c[base_i + i]

        print(f"{total:.0f}")
        print(f"{trace:.0f}")
        c.release()
    finally:
        c_shm.close()
        c_shm.unlink()


if __name__ == "__main__":
    main()
