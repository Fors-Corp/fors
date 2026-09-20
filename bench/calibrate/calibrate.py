#!/usr/bin/env python3
"""M0.P roofline + P-vs-E capacity calibration (stdlib only, Python 3.10+).

  python3 bench/calibrate/calibrate.py                       # full sweep, writes results/machine-<host>.json
  python3 bench/calibrate/calibrate.py --smoke                # tiny sizes, writes results/smoke/, contaminated=true

Builds bench/calibrate/{bandwidth,flops}.c, runs each across the declared thread counts
under BOTH performance QoS (the default) and background QoS (`taskpolicy -b`, macOS's
only lever for steering a process towards the efficiency cores -- macOS gives no API to
pin a thread to a specific core), and writes a single machine-*.json with:

  - bandwidth_gbps / flops_gflops per (core_class, threads)
  - the machine balance point (peak FLOP/s / peak byte/s), from ch06-measurement.md's
    "Roofline" definition
  - a P-vs-E capacity model derived from the single-thread performance-vs-background
    ratio, plus an explicit "did taskpolicy -b actually change anything" check (open
    question 4 asks for the calibration kernel; this file is the answer to open question
    3's sibling, "is the only lever real on this OS version").

Every value here is machine-instance-specific and MUST be re-taken on the target box; a
copy from a different Mac (or the same Mac after a macOS update) is not valid. See
bench/README.md "Parallel family (M0.P)" for the full command sequence and for why the
methodology choices below (CHAINS, reps, k, canary N) are what they are.
"""
import argparse
import json
import platform
import re
import shutil
import statistics
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent  # bench/
BUILD = HERE / ".build"

sys.path.insert(0, str(ROOT / "harness"))
from run import host_info, git_commit  # noqa: E402  (reuse, not duplicate -- see compile-speed/README precedent)

LINE_RE = re.compile(r"(\w+)=([^\s]+)")


def parse_line(text):
    """The calibration binaries print one `key=value key=value ...` line; turn it into a dict
    of floats/ints, leaving anything that doesn't parse as a number out (there is none today,
    but a future field addition should fail loudly in the caller, not here)."""
    out = {}
    for key, value in LINE_RE.findall(text.strip().splitlines()[-1] if text.strip() else ""):
        try:
            out[key] = int(value)
        except ValueError:
            try:
                out[key] = float(value)
            except ValueError:
                pass
    return out


def cc_flags():
    """clang flags for the calibration kernels. Deliberately NOT bench/langs/c.toml's flags:
    those pin -ffp-contract=off for cross-language fairness; this tool measures the machine's
    raw achievable peak, so contraction into hardware FMA is left on (see flops.c docstring)."""
    arch_flag = "-mcpu=native" if platform.machine() in ("arm64", "aarch64") else "-march=native"
    return ["clang", "-O3", arch_flag, "-pthread"]


def build(name, timeout, defines=None, suffix=""):
    """Compile bench/calibrate/<name>.c -> BUILD/<name><suffix>. Returns the binary path."""
    BUILD.mkdir(parents=True, exist_ok=True)
    src = HERE / f"{name}.c"
    exe = BUILD / f"{name}{suffix}"
    cmd = cc_flags() + [f"-D{k}={v}" for k, v in (defines or {}).items()] + ["-o", str(exe), str(src), "-lm"]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    if proc.returncode != 0:
        sys.exit(f"FAIL  build {name}: {proc.stderr.strip()[-2000:]}")
    return exe


def clang_version():
    """First line of `clang --version`, or None. Never indexes an empty list: a clang that is on
    PATH but prints nothing (a broken shim) must not crash the run after the measurements are done."""
    if shutil.which("clang") is None:
        return None
    proc = subprocess.run(["clang", "--version"], capture_output=True, text=True)
    lines = proc.stdout.strip().splitlines()
    return lines[0] if lines else None


def taskpolicy_available():
    return shutil.which("taskpolicy") is not None


def run_binary(exe, args, background, timeout):
    """One execution. Returns the parsed key=value dict, or None on failure (with a message
    already printed to stderr)."""
    cmd = (["taskpolicy", "-b"] if background else []) + [str(exe)] + [str(a) for a in args]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        print(f"WARN  {' '.join(cmd)}: timed out", file=sys.stderr)
        return None
    if proc.returncode != 0:
        print(f"WARN  {' '.join(cmd)}: exit {proc.returncode}: {proc.stderr.strip()[-500:]}", file=sys.stderr)
        return None
    return parse_line(proc.stdout)


def best_of_k(exe, args, background, k, timeout, throughput_key):
    """Run the binary k times, return (best_record, all_throughputs, checksums). "Best" is
    highest throughput (least contaminated by scheduling jitter, GC-less languages don't apply
    here but a stalled thread creation or a context switch mid-run only ever hurts throughput)."""
    records, throughputs, checksums = [], [], []
    for _ in range(k):
        rec = run_binary(exe, args, background, timeout)
        if rec is None or throughput_key not in rec:
            continue
        records.append(rec)
        throughputs.append(rec[throughput_key])
        checksums.append(rec.get("checksum"))
    if not records:
        return None, [], []
    best = max(records, key=lambda r: r[throughput_key])
    return best, throughputs, checksums


# Any timed region shorter than this is reported, but never trusted: CLOCK_MONOTONIC comes back at
# roughly microsecond granularity here, so a kernel that ran for a few microseconds carries tens of
# percent of quantisation error in its rate -- the classic way measurement code prints a plausible
# number that means nothing. Smoke sizes are deliberately under it; a REAL calibration cell under it
# is a misconfiguration, and says so.
MIN_TRUSTWORTHY_WALL_S = 1e-3


def cov(values):
    """Coefficient of variation, or None with fewer than 2 samples."""
    if len(values) < 2:
        return None
    mean = statistics.fmean(values)
    return (statistics.stdev(values) / mean) if mean else None


def declared_threads(cpus, requested):
    if requested:
        return sorted({t for t in requested if t <= cpus})
    return sorted({t for t in (1, 2, 4, 6, 8) if t <= cpus})


def measure_sweep(exe, args_for_t, threads, k, timeout, throughput_key, background):
    """Run best_of_k at every thread count for one QoS class. Returns {t: {...}}."""
    out = {}
    qos = "background (taskpolicy -b)" if background else "performance (default)"
    for t in threads:
        best, throughputs, checksums = best_of_k(exe, args_for_t(t), background, k, timeout, throughput_key)
        if best is None:
            print(f"WARN  no successful run for t={t}, {qos}", file=sys.stderr)
            continue
        distinct = set(checksums)
        too_short = best.get("wall_s", 0.0) < MIN_TRUSTWORTHY_WALL_S
        out[t] = {
            "best": best,
            "throughputs": throughputs,
            "checksum_stable_across_repeats": len(distinct) <= 1,
            "cov": cov(throughputs),
            "below_timer_resolution": too_short,
        }
        print(f"  t={t:<2d} {qos:28s} {throughput_key}={best[throughput_key]:.3f}"
              + ("" if len(distinct) <= 1 else "  ** UNSTABLE CHECKSUM ACROSS REPEATS **")
              + ("" if not too_short else f"  ** timed region {best.get('wall_s', 0.0) * 1e6:.0f}us"
                                          f" < {MIN_TRUSTWORTHY_WALL_S * 1e6:.0f}us: rate is timer"
                                          f" quantisation, not throughput **"))
    return out


def choose_chains(iterations, k, timeout, chain_counts):
    """Build flops.c at several CHAINS values and keep the one with the highest single-thread
    rate. Each chain is a serial acc = acc*mul + add dependency, so a chain count below
    (FP issue width x FMA latency) measures FMA LATENCY and would report it as "peak FLOP rate";
    too many chains spill the vector register file and the rate falls again. The saturating count
    depends on the micro-architecture AND on how the compiler vectorises pairs of chains, so it is
    measured here rather than assumed. Returns (exe, chosen_chains, {chains: gflops}).
    ch06 open question 4 names the calibration kernel; this is the part of it the owner should see
    a sweep table for, not a constant."""
    table, best = {}, None
    for chains in chain_counts:
        exe = build("flops", timeout, defines={"CHAINS": chains}, suffix=f"-c{chains}")
        rec, _, _ = best_of_k(exe, (iterations, 1), False, k, timeout, "flops_gflops")
        if rec is None:
            print(f"WARN  CHAINS={chains}: no successful run", file=sys.stderr)
            continue
        table[chains] = rec["flops_gflops"]
        print(f"  CHAINS={chains:<3d} single-thread flops_gflops={rec['flops_gflops']:.3f}")
        if best is None or table[chains] > table[best[1]]:
            best = (exe, chains)
    if best is None:
        sys.exit("FAIL  flops: no CHAINS value produced a successful run")
    print(f"  -> peak FLOP calibration uses CHAINS={best[1]}")
    return best[0], best[1], table


def capacity_model(p_cores, flops_sweep_perf, flops_sweep_bg):
    """Single-thread performance-vs-background ratio -> an E-core capacity weight, plus the
    empirical check that taskpolicy -b actually moved the needle (rule: never publish a weight
    of 1.0 by default when the mechanism might just not be doing anything on this OS)."""
    p1 = flops_sweep_perf.get(1)
    e1 = flops_sweep_bg.get(1)
    if p1 is None or e1 is None:
        return {"available": False, "reason": "t=1 measurement missing for performance or background QoS"}
    p_val, e_val = p1["best"]["flops_gflops"], e1["best"]["flops_gflops"]
    if not p_val:
        # Without a non-zero performance-QoS rate there is no ratio to take, and formatting one
        # below would raise. Say so instead of publishing a capacity model built on nothing.
        return {"available": False,
                "reason": "performance-QoS single-thread FLOP rate was zero or missing"}
    weight = e_val / p_val
    # Noise floor at t=1: how much the SAME QoS class varies run to run, from the k repeats.
    # A weight indistinguishable from 1.0 at that noise level means "no detectable effect",
    # not "perfect E-core parity" -- those are very different claims.
    noise = max(x for x in (cov(p1["throughputs"]), cov(e1["throughputs"])) if x is not None) \
        if (cov(p1["throughputs"]) or cov(e1["throughputs"])) else 0.02
    threshold = max(2 * noise, 0.03)  # never trust a <3% delta as "real" even if repeats were suspiciously tidy
    effective = abs(1.0 - weight) > threshold
    result = {
        "available": True,
        "p_core_gflops_t1": p_val,
        "e_core_gflops_t1": e_val,
        "e_weight": weight,
        "noise_floor_t1": noise,
        "effect_threshold": threshold,
        "taskpolicy_effective": effective,
        "p_cores": p_cores,
        "formula": "capacity(T) = min(T, p_cores)*1.0 + max(0, T - p_cores)*e_weight",
    }
    if not effective:
        msg = (f"taskpolicy -b changed single-thread throughput by only "
               f"{abs(1.0 - weight):.1%} (noise floor ~{noise:.1%}) -- NOT distinguishable from no "
               f"effect on this OS/machine. Publishing the measured weight below, but "
               f"'taskpolicy_effective' is false: do NOT build a capacity(T) curve on it without "
               f"re-checking on a quiet box.")
        print(f"WARNING: {msg}", file=sys.stderr)
        result["warning"] = msg
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--smoke", action="store_true",
                     help="tiny sizes (<2s total), writes under results/smoke/, contaminated=true")
    ap.add_argument("--n", type=int, help="bandwidth kernel array length (doubles)")
    ap.add_argument("--bw-reps", type=int, help="bandwidth kernel internal repetitions")
    ap.add_argument("--iterations", type=int, help="flops kernel iteration count")
    ap.add_argument("--k", type=int, help="best-of-k process repetitions per (kernel, class, t)")
    ap.add_argument("--chains", type=str,
                     help="comma-separated CHAINS values to sweep for the FLOP kernel; the highest "
                          "single-thread rate wins (default 8,16,32,64; --smoke uses 8,32)")
    ap.add_argument("--threads", type=str, help="comma-separated thread counts, default 1,2,4,6,8 (capped at cpu count)")
    ap.add_argument("--timeout", type=float, default=900.0,
                     help="seconds per build or per single kernel execution. The full sizes under "
                          "background QoS (8 threads crowded onto 2 efficiency cores) are ~10x "
                          "slower than the same cell under performance QoS: a short timeout does "
                          "not fail loudly, it silently leaves holes in the sweep.")
    ap.add_argument("--out", type=str, help="output path (default results/machine-<host>.json,"
                     " or results/smoke/machine-<host>-smoke.json with --smoke)")
    ap.add_argument("--contaminated", choices=["true", "false", "auto"], default="auto",
                     help="auto flags contamination from in-run CoV; pass explicitly when you "
                          "independently know the box was not quiet (e.g. other workflows compiling)")
    args = ap.parse_args()

    if args.smoke:
        n = args.n or 20000
        bw_reps = args.bw_reps or 5
        iterations = args.iterations or 200000
        k = args.k or 3
        chain_counts = [8, 32]
    else:
        n = args.n or 200_000_000       # 200M doubles/array = 1.6 GB/array, well past any LLC
        bw_reps = args.bw_reps or 20
        iterations = args.iterations or 2_000_000_000
        k = args.k or 7
        chain_counts = [8, 16, 32, 64]

    host = host_info()
    cpus = host["cpus"] or 1
    threads = declared_threads(cpus, [int(x) for x in args.threads.split(",")] if args.threads else None)
    if args.chains:
        chain_counts = [int(x) for x in args.chains.split(",")]
    p_cores = int(host.get("performance_cores") or 0) or None

    print(f"building calibration kernels ({'smoke' if args.smoke else 'full'} sizes)...")
    bandwidth_exe = build("bandwidth", args.timeout)
    print("flops: CHAINS sweep (peak is measured, not assumed -- see choose_chains)")
    flops_exe, chains, chains_table = choose_chains(iterations, k, args.timeout, chain_counts)

    if not taskpolicy_available():
        print("WARNING: `taskpolicy` not found on PATH -- background-QoS (E-core) measurements "
              "will be skipped entirely; the P-vs-E capacity model will be unavailable.", file=sys.stderr)

    results = {}
    for kernel_name, exe, args_for_t, tkey in (
        ("bandwidth", bandwidth_exe, lambda t: (n, bw_reps, t), "bandwidth_gbps"),
        ("flops", flops_exe, lambda t: (iterations, t), "flops_gflops"),
    ):
        print(f"{kernel_name}, performance QoS:")
        perf = measure_sweep(exe, args_for_t, threads, k, args.timeout, tkey, background=False)
        bg = {}
        if taskpolicy_available():
            print(f"{kernel_name}, background QoS (taskpolicy -b):")
            bg = measure_sweep(exe, args_for_t, threads, k, args.timeout, tkey, background=True)
        results[kernel_name] = {"performance": perf, "background": bg}

    flop_peak = max((r["best"]["flops_gflops"] for r in results["flops"]["performance"].values()), default=None)
    bw_peak = max((r["best"]["bandwidth_gbps"] for r in results["bandwidth"]["performance"].values()), default=None)
    balance = (flop_peak * 1e9) / (bw_peak * 1e9) if flop_peak and bw_peak else None

    capacity = None
    if taskpolicy_available() and p_cores:
        capacity = capacity_model(
            p_cores,
            results["flops"]["performance"],
            results["flops"]["background"],
        )
    elif taskpolicy_available() and not p_cores:
        print("WARNING: performance-core count unknown (host_info sysctl failed) -- capacity model skipped.",
              file=sys.stderr)

    short = [(kname, cls, t) for kname, kernel in results.items() for cls, cells in kernel.items()
              for t, r in cells.items() if r.get("below_timer_resolution")]
    if short and not args.smoke:
        print(f"WARNING: {len(short)} cell(s) had a timed region below {MIN_TRUSTWORTHY_WALL_S * 1e3:.0f}ms "
              f"-- raise --n/--bw-reps/--iterations; these rates are timer quantisation, not throughput.",
              file=sys.stderr)

    contaminated = args.contaminated == "true"
    all_covs = [r["cov"] for kernel in results.values() for cls in kernel.values() for r in cls.values() if r["cov"]]
    if args.contaminated == "auto" and all_covs and max(all_covs) > 0.15:
        contaminated = True
        print(f"WARNING: auto-contamination check tripped (worst in-run CoV {max(all_covs):.1%} > 15%).",
              file=sys.stderr)

    doc = {
        "schema": 1,
        "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "commit": git_commit(),
        "host": host,
        "toolchain": {"clang": clang_version(), "os": f"{platform.system()} {platform.release()}"},
        "contaminated": contaminated,
        "smoke": args.smoke,
        "params": {"n": n, "bandwidth_reps": bw_reps, "flops_iterations": iterations, "k": k,
                    "threads": threads, "flops_chains": chains, "flops_chains_sweep": chains_table},
        "results": results,
        "roofline": {"flop_peak_gflops": flop_peak, "bandwidth_peak_gbps": bw_peak,
                     "balance_point_flops_per_byte": balance,
                     "cells_below_timer_resolution": [list(x) for x in short]},
        "capacity_model": capacity,
    }

    if args.out:
        out_path = ROOT / args.out if not Path(args.out).is_absolute() else Path(args.out)
    elif args.smoke:
        out_path = ROOT / "results" / "smoke" / f"machine-{platform.node().split('.')[0]}-smoke.json"
    else:
        out_path = ROOT / "results" / f"machine-{platform.node().split('.')[0]}.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(doc, f, indent=1)

    print(f"\nflop peak (performance QoS): {num(flop_peak)} GFLOP/s")
    print(f"bandwidth peak (performance QoS): {num(bw_peak)} GB/s")
    print(f"balance point: {num(balance)} FLOP/byte")
    if capacity:
        print(f"E-core weight: {num(capacity.get('e_weight'))}"
              + ("" if capacity["taskpolicy_effective"] else "  (NOT statistically effective -- see warning above)"))
    print(f"contaminated: {contaminated}")
    print(f"wrote {out_path.relative_to(ROOT.parent)}")
    return 0


def num(value):
    return "n/a" if value is None else f"{value:.3f}"


if __name__ == "__main__":
    sys.exit(main())
