#!/usr/bin/env python3
"""
Timing harness: 50 reps each, median + p95 in ms, for:
  (a) resign.py clone-patch-rename, 1-page patch and 16-page patch
  (b) `codesign -f -s -` on the same binary
  (c) a full clang relink of the toy
at two __TEXT sizes (~1MB, ~50MB of generated padding).
"""
import json
import os
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import resign
import toy_lib

DIR = os.path.dirname(os.path.abspath(__file__))
N_REPS = 50
PAGE = 4096


def median_p95(samples_ms):
    s = sorted(samples_ms)
    med = statistics.median(s)
    p95_idx = min(len(s) - 1, int(round(0.95 * (len(s) - 1))))
    return med, s[p95_idx]


def find_pad_section_fileoff(binary_path):
    out = subprocess.run(["otool", "-l", binary_path], capture_output=True, text=True, check=True).stdout
    lines = out.splitlines()
    for i, line in enumerate(lines):
        if line.strip() == "sectname __pad":
            block = "\n".join(lines[i:i + 8])
            fileoff = None
            size = None
            for l2 in lines[i:i + 8]:
                l2 = l2.strip()
                if l2.startswith("size "):
                    size = int(l2.split()[1], 16)
                if l2.startswith("offset "):
                    fileoff = int(l2.split()[1])
            return fileoff, size
    raise RuntimeError("no __pad section found")


def bench_resign(binary_path, work, n_pages):
    fileoff, size = find_pad_section_fileoff(binary_path)
    # page-align within the section
    patch_off = (fileoff + PAGE - 1) // PAGE * PAGE
    patch_len = n_pages * PAGE
    assert patch_off + patch_len <= fileoff + size, "pad section too small for patch size"
    patch_data = bytes((n_pages * 7 + i) & 0xFF for i in range(patch_len))

    times = []
    target = os.path.join(work, f"resign_target_{n_pages}p")
    shutil.copyfile(binary_path, target)
    os.chmod(target, 0o755)
    for _ in range(N_REPS):
        t0 = time.perf_counter()
        resign.clone_patch_rename(target, patch_off, patch_data)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000.0)
    return times


def bench_codesign(binary_path, work):
    times = []
    target = os.path.join(work, "codesign_target")
    shutil.copyfile(binary_path, target)
    os.chmod(target, 0o755)
    for _ in range(N_REPS):
        t0 = time.perf_counter()
        subprocess.run(["codesign", "-f", "-s", "-", target],
                        capture_output=True, check=True)
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000.0)
    return times


def bench_relink(work, pad_bytes):
    # Pre-generate the pad file once; relinking (not pad-generation) is what
    # we are timing.
    padfile = os.path.join(work, "relink_pad.bin")
    if pad_bytes > 0:
        chunk = bytes((i * 2654435761) & 0xFF for i in range(65536))
        with open(padfile, "wb") as f:
            written = 0
            while written < pad_bytes:
                take = min(len(chunk), pad_bytes - written)
                f.write(chunk[:take])
                written += take
    out_bin = os.path.join(work, "relink_out")
    times = []
    for _ in range(N_REPS):
        t0 = time.perf_counter()
        if pad_bytes > 0:
            subprocess.run(
                ["clang", "-O0", "-arch", "arm64", os.path.join(DIR, "main.c"),
                 "-o", out_bin, f"-Wl,-sectcreate,__TEXT,__pad,{padfile}"],
                check=True, capture_output=True,
            )
        else:
            subprocess.run(
                ["clang", "-O0", "-arch", "arm64", os.path.join(DIR, "main.c"), "-o", out_bin],
                check=True, capture_output=True,
            )
        t1 = time.perf_counter()
        times.append((t1 - t0) * 1000.0)
    return times


def run_size(label, pad_bytes, work):
    print(f"\n--- size: {label} (pad_bytes={pad_bytes}) ---", file=sys.stderr)
    binary_path = os.path.join(work, f"toy_{label}")
    toy_lib.build_toy(binary_path, pad_bytes=pad_bytes)
    actual_size = os.path.getsize(binary_path)
    print(f"built {binary_path}: {actual_size} bytes", file=sys.stderr)

    results = {"label": label, "pad_bytes": pad_bytes, "binary_size": actual_size}

    t = bench_resign(binary_path, work, 1)
    results["resign_1page_ms"] = dict(zip(("median", "p95"), median_p95(t)))
    print(f"resign 1-page:  median={results['resign_1page_ms']['median']:.3f}ms "
          f"p95={results['resign_1page_ms']['p95']:.3f}ms", file=sys.stderr)

    t = bench_resign(binary_path, work, 16)
    results["resign_16page_ms"] = dict(zip(("median", "p95"), median_p95(t)))
    print(f"resign 16-page: median={results['resign_16page_ms']['median']:.3f}ms "
          f"p95={results['resign_16page_ms']['p95']:.3f}ms", file=sys.stderr)

    t = bench_codesign(binary_path, work)
    results["codesign_adhoc_ms"] = dict(zip(("median", "p95"), median_p95(t)))
    print(f"codesign -f -s -: median={results['codesign_adhoc_ms']['median']:.3f}ms "
          f"p95={results['codesign_adhoc_ms']['p95']:.3f}ms", file=sys.stderr)

    t = bench_relink(work, pad_bytes)
    results["full_relink_ms"] = dict(zip(("median", "p95"), median_p95(t)))
    print(f"full clang relink: median={results['full_relink_ms']['median']:.3f}ms "
          f"p95={results['full_relink_ms']['p95']:.3f}ms", file=sys.stderr)

    return results


def main():
    work = tempfile.mkdtemp(prefix="macho_resign_bench_")
    all_results = []
    # ~1MB and ~50MB of __TEXT via the __pad section (main.c itself is tiny)
    all_results.append(run_size("1MB", 1 * 1024 * 1024, work))
    all_results.append(run_size("50MB", 50 * 1024 * 1024, work))
    print(json.dumps(all_results, indent=2))


if __name__ == "__main__":
    main()
