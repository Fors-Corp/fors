#!/usr/bin/env python3
"""Compile-speed track: measures COMPILER wall time (build + link) on a synthetic,
pinned corpus of many small, distinct, non-trivially-dedupable functions.

Reuses bench/harness/run.py instead of duplicating it: languages (build/run commands,
toolchain probes) come from langs/*.toml via load_langs(); measurement, {src}/{out}
expansion and host info come straight from run.py.

  python3 bench/compile-speed/compile_speed.py --sizes 1000 10000
  python3 bench/compile-speed/compile_speed.py --sizes 100000 --allow-100000

Only c, rust, go, swift, java are measured here (compiled languages). node and python
have no build step and are skipped, by design, for this track.
"""
import argparse
import json
import platform
import random
import statistics
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "harness"))
from run import load_langs, toolchain_version, measure, expand, host_info  # noqa: E402

BENCH_ROOT = HERE.parent  # bench/
BUILD_ROOT = BENCH_ROOT / ".build" / "compile-speed"
RESULTS_DIR = BENCH_ROOT / "results" / "compile"

COMPILED_LANGS = ["c", "rust", "go", "swift", "java"]
MODULUS = 1000003
FUNCS_PER_CALL_GROUP = 100     # calls threaded per "block" helper function
JAVA_FUNCS_PER_CLASS = 1000    # ~1000 fn_i methods per top-level class (64KB/const-pool limits)
JAVA_BLOCKS_PER_CLASS = 300    # a block calls 100 fns; keep cross-class const-pool refs well under 65535


def minstd_stream(seed, n):
    """n draws from x = x*48271 mod 2147483647, each reduced mod 1000 (< 1000, so products
    stay well below 2^31 in every language, including exact-as-double in JS -- not that JS
    is generated here, but the same generator's constants are reused if it ever is)."""
    x = seed
    out = []
    for _ in range(n):
        x = (x * 48271) % 2147483647
        out.append(x % 1000)
    return out


def gen_constants(seed, count):
    stream = minstd_stream(seed, count * 3)
    return [(stream[3 * i], stream[3 * i + 1], stream[3 * i + 2]) for i in range(count)]


def expected_value(consts):
    """Reference simulation of the driver, in Python, used to verify every language's output."""
    acc = 1
    for a_c, b_c, c_c in consts:
        x = acc
        a = x * a_c + b_c
        b = a % MODULUS
        acc = b + c_c if b % 2 == 0 else (b * 3) % MODULUS
    return acc


def blocks(count, group=FUNCS_PER_CALL_GROUP):
    """[(block_index, [fn indices]), ...] covering 0..count-1 in groups of `group`."""
    return [(bi, list(range(start, min(start + group, count))))
            for bi, start in enumerate(range(0, count, group))]


def gen_c(consts):
    lines = ["#include <stdio.h>", "#include <stdint.h>", ""]
    for i, (a, b, c) in enumerate(consts):
        lines.append(f"static int64_t f{i}(int64_t x) {{")
        lines.append(f"    int64_t a = x * {a}LL + {b}LL;")
        lines.append(f"    int64_t r = a % {MODULUS}LL;")
        lines.append(f"    if (r % 2 == 0) return r + {c}LL;")
        lines.append(f"    return (r * 3LL) % {MODULUS}LL;")
        lines.append("}")
    for bi, idxs in blocks(len(consts)):
        lines.append(f"static int64_t block{bi}(int64_t x) {{")
        for i in idxs:
            lines.append(f"    x = f{i}(x);")
        lines.append("    return x;")
        lines.append("}")
    lines.append("int main(void) {")
    lines.append("    int64_t acc = 1;")
    for bi, _ in blocks(len(consts)):
        lines.append(f"    acc = block{bi}(acc);")
    lines.append('    printf("%lld\\n", (long long)acc);')
    lines.append("    return 0;")
    lines.append("}")
    return "\n".join(lines) + "\n"


def gen_rust(consts):
    lines = []
    for i, (a, b, c) in enumerate(consts):
        lines.append(f"fn f{i}(x: i64) -> i64 {{")
        lines.append(f"    let a = x * {a} + {b};")
        lines.append(f"    let r = a % {MODULUS};")
        lines.append(f"    if r % 2 == 0 {{ r + {c} }} else {{ (r * 3) % {MODULUS} }}")
        lines.append("}")
    for bi, idxs in blocks(len(consts)):
        lines.append(f"fn block{bi}(mut x: i64) -> i64 {{")
        for i in idxs:
            lines.append(f"    x = f{i}(x);")
        lines.append("    x")
        lines.append("}")
    lines.append("fn main() {")
    lines.append("    let mut acc: i64 = 1;")
    for bi, _ in blocks(len(consts)):
        lines.append(f"    acc = block{bi}(acc);")
    lines.append('    println!("{}", acc);')
    lines.append("}")
    return "\n".join(lines) + "\n"


def gen_go(consts):
    lines = ["package main", "", 'import "fmt"', ""]
    for i, (a, b, c) in enumerate(consts):
        lines.append(f"func f{i}(x int64) int64 {{")
        lines.append(f"\ta := x*{a} + {b}")
        lines.append(f"\tr := a % {MODULUS}")
        lines.append("\tif r%2 == 0 {")
        lines.append(f"\t\treturn r + {c}")
        lines.append("\t}")
        lines.append(f"\treturn (r * 3) % {MODULUS}")
        lines.append("}")
    for bi, idxs in blocks(len(consts)):
        lines.append(f"func block{bi}(x int64) int64 {{")
        for i in idxs:
            lines.append(f"\tx = f{i}(x)")
        lines.append("\treturn x")
        lines.append("}")
    lines.append("func main() {")
    lines.append("\tvar acc int64 = 1")
    for bi, _ in blocks(len(consts)):
        lines.append(f"\tacc = block{bi}(acc)")
    lines.append("\tfmt.Println(acc)")
    lines.append("}")
    return "\n".join(lines) + "\n"


def gen_swift(consts):
    lines = []
    for i, (a, b, c) in enumerate(consts):
        lines.append(f"func f{i}(_ x: Int64) -> Int64 {{")
        lines.append(f"    let a = x * {a} + {b}")
        lines.append(f"    let r = a % {MODULUS}")
        lines.append(f"    if r % 2 == 0 {{ return r + {c} }}")
        lines.append(f"    return (r * 3) % {MODULUS}")
        lines.append("}")
    for bi, idxs in blocks(len(consts)):
        lines.append(f"func block{bi}(_ x0: Int64) -> Int64 {{")
        lines.append("    var x = x0")
        for i in idxs:
            lines.append(f"    x = f{i}(x)")
        lines.append("    return x")
        lines.append("}")
    lines.append("var acc: Int64 = 1")
    for bi, _ in blocks(len(consts)):
        lines.append(f"acc = block{bi}(acc)")
    lines.append("print(acc)")
    return "\n".join(lines) + "\n"


def gen_java(consts):
    n = len(consts)
    lines = ["public class Main {", "    public static void main(String[] args) {", "        long acc = 1L;"]
    for bi, _ in blocks(n):
        cls = f"Blocks{bi // JAVA_BLOCKS_PER_CLASS}"
        lines.append(f"        acc = {cls}.block{bi}(acc);")
    lines.append("        System.out.println(acc);")
    lines.append("    }")
    lines.append("}")

    # fn_i methods, ~JAVA_FUNCS_PER_CLASS per top-level class
    for i, (a, b, c) in enumerate(consts):
        if i % JAVA_FUNCS_PER_CLASS == 0:
            if i != 0:
                lines.append("}")
            lines.append(f"class Funcs{i // JAVA_FUNCS_PER_CLASS} {{")
        lines.append(f"    static long f{i}(long x) {{")
        lines.append(f"        long a = x * {a}L + {b}L;")
        lines.append(f"        long r = a % {MODULUS}L;")
        lines.append(f"        if (r % 2 == 0) return r + {c}L;")
        lines.append(f"        return (r * 3L) % {MODULUS}L;")
        lines.append("    }")
    if n:
        lines.append("}")

    # block methods, ~JAVA_BLOCKS_PER_CLASS per top-level class, calling their Funcs class
    all_blocks = blocks(n)
    for bi, idxs in all_blocks:
        if bi % JAVA_BLOCKS_PER_CLASS == 0:
            if bi != 0:
                lines.append("}")
            lines.append(f"class Blocks{bi // JAVA_BLOCKS_PER_CLASS} {{")
        lines.append(f"    static long block{bi}(long x) {{")
        for i in idxs:
            lines.append(f"        x = Funcs{i // JAVA_FUNCS_PER_CLASS}.f{i}(x);")
        lines.append("        return x;")
        lines.append("    }")
    if all_blocks:
        lines.append("}")
    return "\n".join(lines) + "\n"


GENERATORS = {"c": gen_c, "rust": gen_rust, "go": gen_go, "swift": gen_swift, "java": gen_java}


def run_one(lang, size, timeout, results_note):
    seed = random.SystemRandom().randrange(1, 2**31 - 1)
    consts = gen_constants(seed, size)
    want = expected_value(consts)
    source_text = GENERATORS[lang["name"]](consts)

    src_dir = BUILD_ROOT / f"{lang['name']}-{size}" / "src"
    out_dir = BUILD_ROOT / f"{lang['name']}-{size}" / "out"
    for d in (src_dir, out_dir):
        import shutil
        shutil.rmtree(d, ignore_errors=True)
        d.mkdir(parents=True)
    src_file = src_dir / lang["source"]
    src_file.write_text(source_text)

    log = out_dir / "build.out"
    build_rec = measure(expand(lang["build"], src_dir, out_dir), log, timeout)
    build_rec["ok"] = build_rec["exit_code"] == 0 and not build_rec["timed_out"]
    if not build_rec["ok"]:
        err = Path(str(log) + ".err").read_text(errors="replace").strip()
        results_note.append(f"FAIL  {lang['name']} F={size}: build failed\n{err[-2000:]}")
        return None

    run_cmd = expand(lang["run"], src_dir, out_dir)
    run_log = out_dir / "run.out"
    run_rec = measure(run_cmd, run_log, timeout)
    got_text = run_log.read_text(errors="replace").strip()
    if run_rec["exit_code"] != 0 or run_rec["timed_out"]:
        results_note.append(f"FAIL  {lang['name']} F={size}: run failed (exit {run_rec['exit_code']})")
        return None
    try:
        got = int(got_text)
    except ValueError:
        got = None
    if got != want:
        results_note.append(
            f"FAIL  {lang['name']} F={size}: MISCOMPILE or generator bug -- want {want}, got {got_text!r}"
        )
        return None

    return {
        "lang": lang["name"],
        "size": size,
        "seed": seed,
        "build_wall_s": build_rec["wall_s"],
        "build_user_s": build_rec["user_s"],
        "build_sys_s": build_rec["sys_s"],
        "build_cpu_s": build_rec["user_s"] + build_rec["sys_s"],
        "build_max_rss_bytes": build_rec["max_rss_bytes"],
        "source_lines": source_text.count("\n"),
        "source_bytes": len(source_text.encode()),
        "correct": True,
    }


def render_markdown(rows):
    header = "| language | F | build wall (s) | user+sys CPU (s) | peak RSS (MiB) | src lines | src bytes |"
    sep = "|---|---|---|---|---|---|---|"
    out = [header, sep]
    for r in rows:
        out.append(
            f"| {r['lang']} | {r['size']} | {r['build_wall_s']:.3f} | {r['build_cpu_s']:.3f} | "
            f"{r['build_max_rss_bytes'] / 2**20:.1f} | {r['source_lines']} | {r['source_bytes']} |"
        )
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--sizes", type=int, nargs="+", default=[1000, 10000],
                     help="function counts F to generate and compile (default: 1000 10000)")
    ap.add_argument("--allow-100000", action="store_true",
                     help="permit F=100000 in --sizes; some compilers take minutes at this size")
    ap.add_argument("--lang", action="append", help="limit to this language (repeatable)")
    ap.add_argument("--timeout", type=float, default=900)
    args = ap.parse_args()

    for size in args.sizes:
        if size >= 100000 and not args.allow_100000:
            print(f"refusing F={size}: pass --allow-100000 to permit sizes this large (slow compiles)", file=sys.stderr)
            return 1

    only = set(args.lang) if args.lang else set(COMPILED_LANGS)
    all_langs = load_langs(only & set(COMPILED_LANGS))
    langs = [all_langs[n] for n in COMPILED_LANGS if n in all_langs]

    skipped = [n for n in ("node", "python", "deno") if n in only or not args.lang]
    for n in ("node", "python"):
        print(f"SKIP  {n}: no build step in this track (interpreted, tracked elsewhere)")

    versions = {}
    rows = []
    notes = []
    BUILD_ROOT.mkdir(parents=True, exist_ok=True)
    for lang in langs:
        v = toolchain_version(lang)
        versions[lang["name"]] = v
        if v is None:
            print(f"SKIP  {lang['name']}: toolchain not installed")
            continue
        for size in args.sizes:
            print(f"compiling {lang['name']} F={size} ...", flush=True)
            row = run_one(lang, size, args.timeout, notes)
            if row is None:
                continue
            rows.append(row)
            print(f"ok    {lang['name']} F={size}  build {row['build_wall_s']:.3f}s  "
                  f"rss {row['build_max_rss_bytes'] / 2**20:.1f} MiB")

    for note in notes:
        print(note, file=sys.stderr)

    table = render_markdown(rows)
    print("\n" + table)

    now = datetime.now(timezone.utc)
    doc = {
        "schema": 1,
        "timestamp": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "host": host_info(),
        "toolchains": versions,
        "seed": {f"{r['lang']}-{r['size']}": r["seed"] for r in rows},
        "rows": rows,
    }
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    path = RESULTS_DIR / f"{now.strftime('%Y%m%dT%H%M%SZ')}-{platform.node().split('.')[0]}.json"
    path.write_text(json.dumps(doc, indent=1))
    print(f"\nwrote {path.relative_to(BENCH_ROOT.parent)}")

    return 1 if notes else 0


if __name__ == "__main__":
    main()
