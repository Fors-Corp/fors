#!/usr/bin/env python3
"""Fors benchmark harness runner (stdlib only, Python 3.11+).

  run.py check [--kernel K]... [--lang L]...   build + verify on the small "check" size
  run.py bless --kernel K                      record expected outputs from the kernel's reference language
  run.py bench [--kernel K]... [--lang L]...   build + verified timed runs -> results/<stamp>-<host>.json

Languages are data (langs/*.toml), kernels are data (kernels/<k>/spec.toml + expected/*.txt).
A parallel kernel lists `threads = [...]` in its spec; the thread count is passed as the LAST argument.
Every timed run's stdout must equal the blessed expected output, or the cell is marked incorrect.
"""
import argparse
import json
import os
import platform
import shutil
import statistics
import subprocess
import sys
import threading
import time
import tomllib
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / ".build"
# ru_maxrss is bytes on macOS, kilobytes on Linux.
RSS_UNIT = 1 if sys.platform == "darwin" else 1024


def load_langs(only):
    langs = {}
    for path in sorted((ROOT / "langs").glob("*.toml")):
        lang = tomllib.loads(path.read_text())
        if only and lang["name"] not in only:
            continue
        langs[lang["name"]] = lang
    return langs


def load_kernels(only):
    kernels = {}
    for path in sorted((ROOT / "kernels").glob("*/spec.toml")):
        spec = tomllib.loads(path.read_text())
        if only and spec["name"] not in only:
            continue
        spec["dir"] = path.parent
        kernels[spec["name"]] = spec
    return kernels


def toolchain_version(lang):
    """First line the probe command prints, or None if the toolchain is not installed."""
    if shutil.which(lang["probe"][0]) is None:
        return None
    try:
        p = subprocess.run(lang["probe"], capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = (p.stdout + p.stderr).strip().splitlines()  # `java -version` prints to stderr
    return lines[0] if p.returncode == 0 and lines else None


def measure(cmd, stdout_path, timeout):
    """Run cmd to completion; wall time plus the kernel's own rusage accounting for the child."""
    with open(stdout_path, "wb") as out, open(str(stdout_path) + ".err", "wb") as err:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, stdout=out, stderr=err, cwd=ROOT)
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            proc.kill()

        timer = threading.Timer(timeout, kill)
        timer.start()
        _, status, ru = os.wait4(proc.pid, 0)
        wall = time.perf_counter() - start
        timer.cancel()
        proc.returncode = os.waitstatus_to_exitcode(status)
    return {
        "wall_s": wall,
        "user_s": ru.ru_utime,
        "sys_s": ru.ru_stime,
        "max_rss_bytes": ru.ru_maxrss * RSS_UNIT,
        "exit_code": proc.returncode,
        "timed_out": timed_out.is_set(),
    }


def expand(cmd, src, out):
    return [part.replace("{src}", str(src)).replace("{out}", str(out)) for part in cmd]


def stderr_tail(stdout_path):
    text = Path(str(stdout_path) + ".err").read_text(errors="replace").strip()
    return text[-2000:]


def build(kernel, lang, timeout):
    """Clean build. Returns (out_dir, build_record). build_record["ok"] is False on failure."""
    src = kernel["dir"] / lang.get("dir", lang["name"])
    out = BUILD / kernel["name"] / lang["name"]
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True)
    if "build" not in lang:
        return out, {"ok": True, "wall_s": 0.0, "user_s": 0.0, "sys_s": 0.0, "max_rss_bytes": 0}
    log = out / "build.out"
    rec = measure(expand(lang["build"], src, out), log, timeout)
    rec["ok"] = rec["exit_code"] == 0 and not rec["timed_out"]
    if not rec["ok"]:
        rec["error"] = stderr_tail(log)
    return out, rec


def run_once(kernel, lang, out, size, threads, timeout):
    """One execution. Returns (measurement, stdout_text)."""
    src = kernel["dir"] / lang.get("dir", lang["name"])
    cmd = expand(lang["run"], src, out) + [str(a) for a in kernel["sizes"][size]]
    if threads is not None:
        cmd.append(str(threads))
    stdout_path = out / "run.out"
    rec = measure(cmd, stdout_path, timeout)
    if rec["exit_code"] != 0 or rec["timed_out"]:
        rec["error"] = "timeout" if rec["timed_out"] else stderr_tail(stdout_path)
    return rec, stdout_path.read_text(errors="replace").strip()


def expected_output(kernel, size):
    path = kernel["dir"] / "expected" / f"{size}.txt"
    return path.read_text().strip() if path.exists() else None


def thread_counts(kernel):
    if "threads" not in kernel:
        return [None]
    return [t for t in kernel["threads"] if t <= os.cpu_count()]


def implemented(kernel, lang):
    if lang["name"] in kernel.get("exclude", []):
        return False
    return (kernel["dir"] / lang.get("dir", lang["name"]) / lang["source"]).exists()


def host_info():
    info = {
        "hostname": platform.node(),
        "os": f"{platform.system()} {platform.release()}",
        "arch": platform.machine(),
        "cpus": os.cpu_count(),
        "python": platform.python_version(),
    }
    if sys.platform == "darwin":
        def sysctl(key):
            p = subprocess.run(["sysctl", "-n", key], capture_output=True, text=True)
            return p.stdout.strip() or None

        info["cpu"] = sysctl("machdep.cpu.brand_string")
        info["performance_cores"] = sysctl("hw.perflevel0.physicalcpu")
        info["efficiency_cores"] = sysctl("hw.perflevel1.physicalcpu")
        info["ram_bytes"] = sysctl("hw.memsize")
        batt = subprocess.run(["pmset", "-g", "batt"], capture_output=True, text=True).stdout
        info["on_battery"] = "Battery Power" in batt
    return info


# Thermal canary: a fixed slice of compute timed before every kernel. Its time should not move; if it
# drifts, the machine throttled or something else was running, and the results file says so.
CANARY = ("reduce", "c", ["200000000", "1"])


def build_canary(timeout):
    """The canary command, or None when its kernel or toolchain is unavailable."""
    kernel_name, lang_name, argv = CANARY
    kernel, lang = load_kernels([kernel_name]).get(kernel_name), load_langs([lang_name]).get(lang_name)
    if not kernel or not lang or toolchain_version(lang) is None:
        return None
    out, b = build(kernel, lang, timeout)
    if not b["ok"]:
        return None
    keep = BUILD / "_canary"
    keep.mkdir(parents=True, exist_ok=True)
    shutil.copy2(expand([lang["artifact"]], kernel["dir"], out)[0], keep / "main")  # survives the cell's clean build
    cmd = [str(keep / "main"), *argv]
    measure(cmd, keep / "run.out", timeout)  # untimed: first exec of a fresh binary pays signature validation
    return cmd


def git_commit():
    """HEAD hash (+ "-dirty" if kernels/langs/harness differ from it): every results file names the exact
    sources it measured, which is what makes the kernel set pre-registered rather than picked after the fact."""
    def git(*argv):
        return subprocess.run(["git", "-C", str(ROOT), *argv], capture_output=True, text=True).stdout.strip()

    try:
        head = git("rev-parse", "HEAD")
        dirty = git("status", "--porcelain", "--", "kernels", "langs", "harness")
    except OSError:
        return None
    return (head + ("-dirty" if dirty else "")) if head else None


def cmd_check(args):
    langs, kernels = load_langs(args.lang), load_kernels(args.kernel)
    failures = 0
    for kernel in kernels.values():
        want = expected_output(kernel, "check")
        for lang in langs.values():
            if not implemented(kernel, lang):
                continue
            cell = f"{kernel['name']}/{lang['name']}"
            if toolchain_version(lang) is None:
                print(f"SKIP  {cell}: toolchain not installed")
                continue
            out, b = build(kernel, lang, args.timeout)
            if not b["ok"]:
                print(f"FAIL  {cell}: build failed\n{b['error']}")
                failures += 1
                continue
            # a parallel kernel must give the same answer on 1 thread and on many
            counts = thread_counts(kernel)
            for threads in sorted({counts[0], counts[-1]}, key=lambda t: t or 0):
                rec, got = run_once(kernel, lang, out, "check", threads, args.timeout)
                label = cell if threads is None else f"{cell} t={threads}"
                if "error" in rec:
                    print(f"FAIL  {label}: {rec['error']}")
                    failures += 1
                elif want is None:
                    print(f"????  {label}: no expected/check.txt yet (run `bless`)")
                    failures += 1
                elif got != want:
                    print(f"FAIL  {label}: output mismatch\n  want: {want[:200]!r}\n  got:  {got[:200]!r}")
                    failures += 1
                else:
                    print(f"ok    {label}  ({rec['wall_s']:.3f}s)")
    return 1 if failures else 0


def cmd_bless(args):
    kernels = load_kernels(args.kernel)
    for kernel in kernels.values():
        lang = load_langs([kernel["reference"]])[kernel["reference"]]
        out, b = build(kernel, lang, args.timeout)
        if not b["ok"]:
            print(f"FAIL  {kernel['name']}: reference build failed\n{b['error']}")
            return 1
        (kernel["dir"] / "expected").mkdir(exist_ok=True)
        for size in kernel["sizes"]:
            rec, got = run_once(kernel, lang, out, size, thread_counts(kernel)[-1], args.timeout)
            if "error" in rec:
                print(f"FAIL  {kernel['name']} {size}: {rec['error']}")
                return 1
            (kernel["dir"] / "expected" / f"{size}.txt").write_text(got + "\n")
            print(f"blessed {kernel['name']} {size} from {lang['name']} ({rec['wall_s']:.3f}s): {got[:80]!r}")
    return 0


def timed_runs(kernel, lang, out, threads, want, args):
    """Adaptive repetition: at least --runs-min, until --budget seconds are spent, at most --runs-max.
    The first execution is an untimed warmup (macOS validates a fresh binary's signature on first exec,
    ~0.2s) unless it is slower than --slow, in which case it is kept as the cell's single run."""
    runs, spent, warm = [], 0.0, False
    while len(runs) < args.runs_max:
        rec, got = run_once(kernel, lang, out, "bench", threads, args.timeout)
        if "error" in rec:
            return runs, False, rec["error"]
        if got != want:
            return runs, False, f"output mismatch: {got[:200]!r}"
        if not warm and rec["wall_s"] <= args.slow:
            warm = True
            continue
        runs.append({k: rec[k] for k in ("wall_s", "user_s", "sys_s", "max_rss_bytes")})
        spent += rec["wall_s"]
        if rec["wall_s"] > args.slow or (len(runs) >= args.runs_min and spent >= args.budget):
            break
    return runs, True, None


def summarize(runs):
    walls = sorted(r["wall_s"] for r in runs)
    if not walls:
        return None
    p95 = walls[min(len(walls) - 1, round(0.95 * (len(walls) - 1)))]
    return {
        "n": len(walls),
        "min": walls[0],
        "median": statistics.median(walls),
        "p95": p95,
        "mean": statistics.fmean(walls),
        "stdev": statistics.stdev(walls) if len(walls) > 1 else 0.0,
        "max_rss_bytes": max(r["max_rss_bytes"] for r in runs),
    }


def cmd_bench(args):
    langs, kernels = load_langs(args.lang), load_kernels(args.kernel)
    host = host_info()
    if host.get("on_battery"):
        print("WARNING: on battery power - timings will be throttled and noisy", file=sys.stderr)
    versions = {name: toolchain_version(lang) for name, lang in langs.items()}
    results = []
    now = datetime.now(timezone.utc)
    doc = {"schema": 1, "timestamp": now.strftime("%Y-%m-%dT%H:%M:%SZ"), "commit": git_commit(), "host": host,
           "toolchains": versions, "langs": langs, "canary": [], "results": results}
    canary = build_canary(args.timeout)
    (ROOT / "results").mkdir(exist_ok=True)
    stem = f"{now.strftime('%Y%m%dT%H%M%SZ')}-{platform.node().split('.')[0]}"
    path, n = ROOT / "results" / f"{stem}.json", 1
    while path.exists():  # two runs in the same second must never overwrite each other's evidence
        n += 1
        path = ROOT / "results" / f"{stem}-{n}.json"
    path.touch()
    for kernel in kernels.values():
        want = expected_output(kernel, "bench")
        if want is None:
            print(f"SKIP  {kernel['name']}: no expected/bench.txt (run `bless`)")
            continue
        if canary:
            wall = measure(canary, BUILD / "_canary" / "run.out", args.timeout)["wall_s"]
            doc["canary"].append({"before": kernel["name"], "wall_s": wall})
        for lang in langs.values():
            if not implemented(kernel, lang) or versions[lang["name"]] is None:
                continue
            out, b = build(kernel, lang, args.timeout)
            artifact = lang.get("artifact")
            size = None
            if b["ok"] and artifact:
                size = Path(expand([artifact], kernel["dir"], out)[0]).stat().st_size
            for threads in thread_counts(kernel):
                cell = {"kernel": kernel["name"], "category": kernel["category"], "lang": lang["name"],
                        "threads": threads, "build": b, "binary_bytes": size}
                if b["ok"]:
                    runs, correct, error = timed_runs(kernel, lang, out, threads, want, args)
                    cell.update(runs=runs, stats=summarize(runs), correct=correct, error=error)
                else:
                    cell.update(runs=[], stats=None, correct=False, error="build failed")
                results.append(cell)
                label = f"{kernel['name']}/{lang['name']}" + ("" if threads is None else f" t={threads}")
                if cell["correct"] and cell["stats"]:
                    s = cell["stats"]
                    print(f"{label:40s} median {s['median']:9.4f}s  n={s['n']:<2d} rss {s['max_rss_bytes'] / 2**20:8.1f} MiB")
                else:
                    print(f"{label:40s} FAILED: {cell['error']}")
        path.write_text(json.dumps(doc, indent=1))  # after every kernel: a killed long run keeps its data
    print(f"\nwrote {path.relative_to(ROOT.parent)}")
    return 0 if all(r["correct"] for r in results) else 1


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("check", cmd_check), ("bless", cmd_bless), ("bench", cmd_bench)):
        p = sub.add_parser(name)
        p.set_defaults(fn=fn)
        p.add_argument("--kernel", action="append", help="limit to this kernel (repeatable)")
        p.add_argument("--lang", action="append", help="limit to this language (repeatable)")
        p.add_argument("--timeout", type=float, default=900, help="seconds per build or run")
        if name == "bench":
            p.add_argument("--runs-min", type=int, default=3)
            p.add_argument("--runs-max", type=int, default=10)
            p.add_argument("--budget", type=float, default=20, help="seconds of timed runs per cell before stopping")
            p.add_argument("--slow", type=float, default=60, help="a first run slower than this is the only run")
    args = ap.parse_args()
    sys.exit(args.fn(args))


if __name__ == "__main__":
    main()
