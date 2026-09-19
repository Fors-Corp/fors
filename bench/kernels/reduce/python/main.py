import multiprocessing
import sys

MASK = 0xFFFFFFFF


def lowbias32(x):
    x ^= x >> 16
    x = (x * 0x7feb352d) & MASK
    x ^= x >> 15
    x = (x * 0x846ca68b) & MASK
    x ^= x >> 16
    return x & MASK


def partial_sum(args):
    start, end = args
    total = 0
    for i in range(start, end):
        x = i & MASK
        x = lowbias32(x)
        x = lowbias32(x)
        x = lowbias32(x)
        x = lowbias32(x)
        total += x % 1000
    return total


def main():
    n = int(sys.argv[1])
    num_threads = int(sys.argv[2])
    if num_threads < 1:
        num_threads = 1

    tasks = []
    for t in range(num_threads):
        start = n * t // num_threads
        end = n * (t + 1) // num_threads
        tasks.append((start, end))

    if num_threads == 1:
        total = partial_sum(tasks[0])
    else:
        with multiprocessing.Pool(num_threads) as pool:
            total = sum(pool.map(partial_sum, tasks))

    print(total)


if __name__ == "__main__":
    main()
