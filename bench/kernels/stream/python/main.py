import sys
import multiprocessing as mp
from multiprocessing import shared_memory


def block_bounds(n, threads):
    base, rem = divmod(n, threads)
    bounds = [0] * (threads + 1)
    idx = 0
    for t in range(threads):
        count = base + (1 if t < rem else 0)
        idx += count
        bounds[t + 1] = idx
    return bounds


def worker(r, a_shm_name, b_shm_name, c_shm_name, start, end):
    a_shm = shared_memory.SharedMemory(name=a_shm_name)
    b_shm = shared_memory.SharedMemory(name=b_shm_name)
    c_shm = shared_memory.SharedMemory(name=c_shm_name)
    a = memoryview(a_shm.buf).cast("d")
    b = memoryview(b_shm.buf).cast("d")
    c = memoryview(c_shm.buf).cast("d")

    s = 3.0
    # First-touch: this process initialises b, c and a for its own block only.
    for i in range(start, end):
        b[i] = float((i % 7) + 1)
        c[i] = float((i % 5) + 1)
        a[i] = 0.0
    for _ in range(r):
        for i in range(start, end):
            a[i] = b[i] + s * c[i]

    a.release()
    b.release()
    c.release()
    a_shm.close()
    b_shm.close()
    c_shm.close()


def main():
    n = int(sys.argv[1])
    r = int(sys.argv[2])
    threads = int(sys.argv[3])
    if threads < 1:
        threads = 1
    if threads > n:
        threads = n

    a_shm = shared_memory.SharedMemory(create=True, size=n * 8)
    b_shm = shared_memory.SharedMemory(create=True, size=n * 8)
    c_shm = shared_memory.SharedMemory(create=True, size=n * 8)
    try:
        bounds = block_bounds(n, threads)
        procs = []
        for t in range(threads):
            start = bounds[t]
            end = bounds[t + 1]
            p = mp.Process(
                target=worker,
                args=(r, a_shm.name, b_shm.name, c_shm.name, start, end),
            )
            procs.append(p)
            p.start()
        for p in procs:
            p.join()

        a = memoryview(a_shm.buf).cast("d")
        total = 0.0
        for i in range(n):
            total += a[i]
        a.release()

        print(f"{total:.0f}")
    finally:
        a_shm.close()
        a_shm.unlink()
        b_shm.close()
        b_shm.unlink()
        c_shm.close()
        c_shm.unlink()


if __name__ == "__main__":
    main()
