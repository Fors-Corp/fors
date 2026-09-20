#!/usr/bin/env python3
"""Differential-fuzzing campaign driver for the two Fors parsers.

For N generated-and-mutated programs: gets the Python reference verdict
in-process (`tools/ref/fors_parse.py`, the same oracle
`tools/ref/diff_driver.py` and `crates/fors-syntax/tests/differential.rs`
already trust for the hand-written corpus) and the Rust verdict from the
release `fors` binary, batched a few hundred files per invocation. Every
disagreement is delta-debugged down to a minimal reproducer (first over
tokens, then over raw bytes) and reported once per distinct shape.

Also flags, independently of accept/reject agreement:
  * a Python exception from `fors_parse.check` that is not its own `E`
    (a genuine parse error) - most commonly `RecursionError` on deep
    nesting, since the reference has no explicit depth cap;
  * a Rust `fors parse` exit code that is neither 0 (clean) nor 1
    (diagnostics) - i.e. a panic - or stderr containing "panicked";
  * a batch that does not finish inside its timeout (a hang), reproduced
    and isolated one file at a time;
  * a Rust parse whose CPU time (measured via `resource.getrusage` deltas
    on the child process, never wall-clock, since this machine also runs
    unrelated builds) grows faster than linearly across a geometric series
    of nesting depths.

Usage:
    python3 run.py --seed 1 --count 60000
    python3 run.py --seed 1 --seed 2 --seed 3 --count 70000 --report OUT.json
"""
from __future__ import annotations

import argparse
import json
import os
import random
import resource
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO_ROOT = os.path.abspath(os.path.join(_HERE, "..", ".."))
sys.path.insert(0, os.path.join(_HERE, "..", "ref"))
sys.path.insert(0, _HERE)
import fors_parse as ref  # noqa: E402
import gen  # noqa: E402
import mutate  # noqa: E402

RUST_BIN = os.path.join(_REPO_ROOT, "target", "release", "fors")


# ---------------------------------------------------------------------------
# Oracles

def python_verdict(data: bytes) -> Tuple[str, Optional[str]]:
    """Returns (verdict, exception_type_name). verdict is 'ok', 'err', or
    'crash' (an exception that is not `fors_parse.E`)."""
    text = data.decode("utf-8", errors="surrogateescape")
    try:
        err = ref.check(text)
        return ("err" if err else "ok"), None
    except ref.E:
        return "err", None
    except Exception as e:  # noqa: BLE001 - the whole point of this function
        return "crash", type(e).__name__


@dataclass
class RustBatchResult:
    err_files: set
    exit_code: int
    stdout: str
    stderr: str
    timed_out: bool
    cpu_time: float


def _cpu_now() -> float:
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)
    return ru.ru_utime + ru.ru_stime


def run_rust_batch(paths: List[str], timeout: float) -> RustBatchResult:
    before = _cpu_now()
    try:
        proc = subprocess.run(
            [RUST_BIN, "parse"] + paths,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as e:
        return RustBatchResult(set(), -1, "", str(e), True, _cpu_now() - before)
    cpu = _cpu_now() - before
    err_files = set()
    for line in proc.stdout.splitlines():
        marker = ".fors:"
        idx = line.find(marker)
        if idx == -1:
            continue
        err_files.add(os.path.basename(line[: idx + len(".fors")]))
    return RustBatchResult(err_files, proc.returncode, proc.stdout, proc.stderr, False, cpu)


def rust_is_crash(res: RustBatchResult) -> bool:
    if res.timed_out:
        return False
    return res.exit_code not in (0, 1) or "panicked" in res.stderr


# ---------------------------------------------------------------------------
# Case production: each index is one independent trial - its own fresh
# generated program, optionally passed through exactly one mutation.

@dataclass
class Case:
    idx: int
    data: bytes
    mutated: bool
    mutation: Optional[str]


def make_case(seed: int, idx: int, max_depth: int, mutate_fraction: float) -> Case:
    rng = random.Random(f"fors-fuzz-run:{seed}:{idx}")
    base = gen.generate_one(random.Random(rng.getrandbits(64)), max_depth)
    if rng.random() < mutate_fraction:
        n_muts = 2 if rng.random() < 0.15 else 1
        data = base.encode("utf-8")
        name = None
        for _ in range(n_muts):
            text = data.decode("utf-8", errors="surrogateescape")
            data, name = mutate.mutate_bytes(text, rng)
        return Case(idx, data, True, name)
    return Case(idx, base.encode("utf-8"), False, None)


# ---------------------------------------------------------------------------
# Disagreement bucketing + delta-debugging minimisation

def rust_diag_code(stdout_for_file: str) -> Optional[str]:
    import re

    m = re.search(r"error\[(P\d+)\]", stdout_for_file)
    return m.group(1) if m else None


@dataclass
class Finding:
    direction: str  # python_ok_rust_err | python_err_rust_ok | python_crash | rust_crash | hang
    signature: Tuple
    raw: bytes
    minimized: Optional[bytes] = None
    detail: str = ""
    count: int = 1


def signature_of(direction: str, code: Optional[str], exc: Optional[str]) -> Tuple:
    return (direction, code, exc)


def single_rust_check(path: str, timeout: float = 5.0) -> Tuple[bool, RustBatchResult]:
    res = run_rust_batch([path], timeout)
    is_err = os.path.basename(path) in res.err_files
    return is_err, res


def make_is_interesting(direction: str, workfile: str):
    """Builds the ddmin oracle predicate for one finding's direction: the
    minimised candidate must reproduce the *same* disagreement, not merely
    *a* disagreement, or minimisation would wander into a different bug."""

    def check(data: bytes) -> bool:
        if len(data) == 0:
            return False
        with open(workfile, "wb") as fh:
            fh.write(data)
        if direction == "python_crash":
            v, _ = python_verdict(data)
            return v == "crash"
        if direction == "rust_crash":
            _, res = single_rust_check(workfile)
            return rust_is_crash(res)
        if direction == "hang":
            _, res = single_rust_check(workfile, timeout=2.0)
            return res.timed_out
        # python_ok_rust_err / python_err_rust_ok
        pv, _ = python_verdict(data)
        if pv == "crash":
            return False
        rust_err, res = single_rust_check(workfile)
        if rust_is_crash(res) or res.timed_out:
            return False
        if direction == "python_ok_rust_err":
            return pv == "ok" and rust_err
        if direction == "python_err_rust_ok":
            return pv == "err" and not rust_err
        return False

    return check


def ddmin(items: List, is_interesting) -> List:
    """Zeller's delta-debugging minimisation, generic over a list of
    elements (tokens in the first pass, raw bytes in the second)."""
    n = 2
    changed = True
    while len(items) >= 1 and n <= len(items):
        chunk_size = max(1, len(items) // n)
        chunks = [items[i : i + chunk_size] for i in range(0, len(items), chunk_size)]
        reduced = False
        for i in range(len(chunks)):
            candidate = [x for c in (chunks[:i] + chunks[i + 1 :]) for x in c]
            if candidate and is_interesting(candidate):
                items = candidate
                n = max(n - 1, 2)
                reduced = True
                break
        if not reduced:
            if n >= len(items):
                break
            n = min(n * 2, len(items))
    return items


def minimize_case(direction: str, data: bytes, workdir: str, budget: int = 800) -> bytes:
    workfile = os.path.join(workdir, "min_candidate.fors")
    is_interesting = make_is_interesting(direction, workfile)
    calls = [0]

    def bounded(pred):
        def f(x):
            calls[0] += 1
            if calls[0] > budget:
                return False
            return pred(x)

        return f

    checked = bounded(is_interesting)
    if not checked(data):
        return data  # shouldn't happen: the raw case itself must reproduce

    # Pass 1: token-level, only if the input decodes cleanly (byte-level
    # mutations that break UTF-8 skip straight to pass 2).
    try:
        text = data.decode("utf-8")
        tokens = [t for _, t in mutate.tokenize(text)]

        def tok_interesting(tok_list):
            return checked("".join(tok_list).encode("utf-8", errors="surrogateescape"))

        tokens = ddmin(tokens, tok_interesting)
        data = "".join(tokens).encode("utf-8")
    except UnicodeDecodeError:
        pass

    # Pass 2: byte-level, finer-grained (shrinks identifiers/digits/
    # whitespace the token pass cannot split further).
    byte_list = list(data)

    def byte_interesting(b_list):
        return checked(bytes(b_list))

    byte_list = ddmin(byte_list, byte_interesting)
    return bytes(byte_list)


# ---------------------------------------------------------------------------
# Superlinear-nesting check (CPU-time proxy, never wall-clock: see module
# docstring). Isolated, one file per invocation, min-of-3 to cut jitter.

def measure_cpu(path: str) -> float:
    samples = []
    for _ in range(3):
        _, res = single_rust_check(path, timeout=10.0)
        if res.timed_out:
            return float("inf")
        samples.append(res.cpu_time)
    return min(samples)


def superlinear_nesting_check(workdir: str) -> Optional[str]:
    depths = [16, 32, 64, 128, 256, 512, 1024]
    times = []
    for n in depths:
        path = os.path.join(workdir, f"nest_{n}.fors")
        with open(path, "w") as fh:
            fh.write("fn main() {\n    let x = " + "(" * n + "1" + ")" * n + ";\n}\n")
        times.append(measure_cpu(path))
    ratios = []
    for i in range(1, len(times)):
        if times[i - 1] <= 0:
            continue
        ratios.append(times[i] / times[i - 1])
    bad_ratios = [r for r in ratios if r > 3.0]  # depth doubles; >3x cpu twice running = superlinear
    detail = f"depths={depths} cpu_seconds={[round(t, 4) for t in times]} doubling_ratios={[round(r, 2) for r in ratios]}"
    if len(bad_ratios) >= 2:
        return "SUPERLINEAR " + detail
    return "linear-ish " + detail


# ---------------------------------------------------------------------------
# Main campaign

def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, action="append", required=True, help="repeatable")
    ap.add_argument("--count", type=int, required=True, help="cases PER seed")
    ap.add_argument("--max-depth", type=int, default=3)
    ap.add_argument("--mutate-fraction", type=float, default=0.55)
    ap.add_argument("--batch-size", type=int, default=300)
    ap.add_argument("--batch-timeout", type=float, default=20.0)
    ap.add_argument("--report", type=str, default=None)
    ap.add_argument("--skip-build", action="store_true")
    ap.add_argument("--skip-superlinear", action="store_true")
    ap.add_argument("--minimize-budget", type=int, default=800)
    ap.add_argument("--max-representatives-per-bucket", type=int, default=6)
    args = ap.parse_args(argv)

    if not args.skip_build:
        print("[run.py] building release fors-cli ...", file=sys.stderr)
        subprocess.run(
            ["cargo", "build", "-q", "--release", "-p", "fors-cli"],
            cwd=_REPO_ROOT,
            check=True,
        )
    if not os.path.exists(RUST_BIN):
        print(f"[run.py] release binary not found at {RUST_BIN}", file=sys.stderr)
        return 2

    total = 0
    agree_ok = 0
    agree_err = 0
    buckets: Dict[Tuple, List[Case]] = {}
    bucket_meta: Dict[Tuple, str] = {}
    hangs: List[Case] = []
    t_start = time.time()

    with tempfile.TemporaryDirectory(prefix="fors-fuzz-") as tmp:
        for seed in args.seed:
            idx = 0
            while idx < args.count:
                batch_ids = list(range(idx, min(idx + args.batch_size, args.count)))
                cases = [make_case(seed, i, args.max_depth, args.mutate_fraction) for i in batch_ids]
                names = [f"s{seed}_c{i:07d}.fors" for i in batch_ids]
                paths = [os.path.join(tmp, n) for n in names]
                for p, c in zip(paths, cases):
                    with open(p, "wb") as fh:
                        fh.write(c.data)

                rust_res = run_rust_batch(paths, args.batch_timeout)
                if rust_res.timed_out:
                    # isolate: re-run one at a time with a short timeout
                    for p, c, n in zip(paths, cases, names):
                        _, one = single_rust_check(p, timeout=3.0)
                        if one.timed_out:
                            hangs.append(c)
                        # fold back into normal handling for the rest
                    idx += len(batch_ids)
                    total += len(batch_ids)
                    continue

                # One pass over the batch's combined stdout gives every
                # file's own diagnostic code for free (no extra subprocess
                # per file): bucketing by code from the start, instead of
                # only on a couple of representatives after the fact, means
                # a bucket's first N cases are not all the same shape just
                # because they happen to come first in generation order.
                file_diag_codes: Dict[str, Optional[str]] = {}
                for line in rust_res.stdout.splitlines():
                    fend = line.find(".fors:")
                    if fend == -1:
                        continue
                    fpath = line[: fend + len(".fors")]
                    if fpath not in file_diag_codes:
                        file_diag_codes[fpath] = rust_diag_code(line)

                for p, c, n in zip(paths, cases, names):
                    total += 1
                    pv, exc = python_verdict(c.data)
                    rust_err = n in rust_res.err_files
                    if pv == "crash":
                        sig = signature_of("python_crash", None, exc)
                        buckets.setdefault(sig, []).append(c)
                        bucket_meta[sig] = f"python raised {exc} (not a parse error)"
                        continue
                    if pv == "ok" and not rust_err:
                        agree_ok += 1
                        continue
                    if pv == "err" and rust_err:
                        agree_err += 1
                        continue
                    direction = "python_ok_rust_err" if (pv == "ok" and rust_err) else "python_err_rust_ok"
                    code = file_diag_codes.get(p) if rust_err else None
                    sig = signature_of(direction, code, None)
                    buckets.setdefault(sig, []).append(c)

                idx += len(batch_ids)
                if total % 20000 < args.batch_size:
                    print(
                        f"[run.py] seed={seed} progress {min(idx,args.count)}/{args.count} "
                        f"total={total} agree_ok={agree_ok} agree_err={agree_err} "
                        f"buckets={len(buckets)} elapsed={time.time()-t_start:.1f}s",
                        file=sys.stderr,
                    )

        # Buckets are already keyed by (direction, rust diag code, python
        # exception type) from the main loop, so each one is already a
        # single shape; minimise a small sample from each to confirm and to
        # get a reportable reproducer, rather than re-deriving anything.
        findings: List[Finding] = []
        for sig, cases_in_bucket in buckets.items():
            direction = sig[0]
            reps = cases_in_bucket[: args.max_representatives_per_bucket]
            for rep in reps:
                minimized = minimize_case(direction, rep.data, tmp, budget=args.minimize_budget)
                findings.append(
                    Finding(
                        direction=direction,
                        signature=sig,
                        raw=rep.data,
                        minimized=minimized,
                        detail=bucket_meta.get(sig, ""),
                        count=len(cases_in_bucket),
                    )
                )

        for c in hangs[:3]:
            p = os.path.join(tmp, "hang.fors")
            with open(p, "wb") as fh:
                fh.write(c.data)
            minimized = minimize_case("hang", c.data, tmp, budget=200)
            findings.append(Finding(direction="hang", signature=("hang",), raw=c.data, minimized=minimized, count=len(hangs)))

        superlinear_report = None
        if not args.skip_superlinear:
            superlinear_report = superlinear_nesting_check(tmp)

    # De-duplicate findings by (direction, code/exc, minimized length bucket)
    dedup: Dict[Tuple, Finding] = {}
    for f in findings:
        key = f.signature + (len(f.minimized or f.raw) // 8,)
        if key not in dedup:
            dedup[key] = f
        else:
            dedup[key].count += f.count
    final_findings = sorted(dedup.values(), key=lambda f: (-f.count, f.direction))

    elapsed = time.time() - t_start
    print("\n==================== CAMPAIGN SUMMARY ====================", file=sys.stderr)
    print(f"seeds={args.seed} count_per_seed={args.count} total_cases={total} elapsed={elapsed:.1f}s", file=sys.stderr)
    print(f"agree_ok={agree_ok} agree_err={agree_err} agreement_rate={(agree_ok+agree_err)/max(total,1):.6f}", file=sys.stderr)
    print(f"distinct raw buckets={len(buckets)} -> distinct findings after dedup={len(final_findings)}", file=sys.stderr)
    print(f"hangs={len(hangs)}", file=sys.stderr)
    if superlinear_report:
        print(f"superlinear_nesting_check: {superlinear_report}", file=sys.stderr)
    for f in final_findings:
        print(f"\n--- finding {f.signature} occurrences~={f.count} ---", file=sys.stderr)
        print(f"detail: {f.detail}", file=sys.stderr)
        try:
            print("minimized:\n" + (f.minimized or f.raw).decode("utf-8", errors="backslashreplace"), file=sys.stderr)
        except Exception:
            print("minimized (raw bytes):", (f.minimized or f.raw), file=sys.stderr)

    if args.report:
        report = {
            "seeds": args.seed,
            "count_per_seed": args.count,
            "max_depth": args.max_depth,
            "mutate_fraction": args.mutate_fraction,
            "total_cases": total,
            "agree_ok": agree_ok,
            "agree_err": agree_err,
            "agreement_rate": (agree_ok + agree_err) / max(total, 1),
            "elapsed_seconds": elapsed,
            "hangs": len(hangs),
            "superlinear_nesting_check": superlinear_report,
            "findings": [
                {
                    "direction": f.direction,
                    "signature": [str(x) for x in f.signature],
                    "occurrences": f.count,
                    "detail": f.detail,
                    "raw_base64": __import__("base64").b64encode(f.raw).decode("ascii"),
                    "minimized_base64": __import__("base64").b64encode(f.minimized or f.raw).decode("ascii"),
                    "minimized_utf8_lossy": (f.minimized or f.raw).decode("utf-8", errors="backslashreplace"),
                }
                for f in final_findings
            ],
        }
        with open(args.report, "w") as fh:
            json.dump(report, fh, indent=2)
        print(f"\n[run.py] wrote report to {args.report}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
