import multiprocessing
import sys


def count_rows(args):
    n, row_start, row_end = args
    count = 0
    for py in range(row_start, row_end):
        ci0 = 2.0 * py / n - 1.0
        for px in range(n):
            cr = 2.0 * px / n - 1.5
            zr = 0.0
            zi = 0.0
            iter_ = 0
            while iter_ < 50 and zr * zr + zi * zi <= 4.0:
                tr = zr * zr - zi * zi + cr
                ti = 2.0 * zr * zi + ci0
                zr = tr
                zi = ti
                iter_ += 1
            if iter_ == 50:
                count += 1
    return count


def main():
    n = int(sys.argv[1])
    num_threads = int(sys.argv[2])
    if num_threads < 1:
        num_threads = 1

    tasks = []
    for t in range(num_threads):
        row_start = n * t // num_threads
        row_end = n * (t + 1) // num_threads
        tasks.append((n, row_start, row_end))

    if num_threads == 1:
        total = count_rows(tasks[0])
    else:
        with multiprocessing.Pool(num_threads) as pool:
            total = sum(pool.map(count_rows, tasks))

    print(total)


if __name__ == "__main__":
    main()
