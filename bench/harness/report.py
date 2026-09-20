#!/usr/bin/env python3
"""Markdown scoreboard from a harness results file.

  report.py [results.json ...]  default: the newest file in bench/results/; several files are merged
"""
import json
import math
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "c"


def score(ratios):
    """Collapse the per-kernel ratios into ONE number per language (lower = better).

    ratios[lang][axis] is a list with one entry per kernel. "runtime", "memory" and "compile" are
    relative to the C baseline (1.0 = same as C, 2.0 = twice as slow / large):
      "runtime"  best median wall time
      "memory"   peak RSS
      "compile"  clean build wall time (axis absent for languages with no build step)
      "scaling"  threads / speedup at the highest thread count: 1.0 = perfect linear scaling.
                 NOT relative to C. Parallel kernels only.
    Return {lang: number}.

    Default: weighted geometric mean of the per-axis geometric means. The weights are a value judgment
    about what Fors is for (compile speed first) - edit them. A language with no "compile" axis is
    scored over the axes it has.
    """
    weights = {"compile": 3, "runtime": 2, "scaling": 2, "memory": 1}
    totals = {}
    for lang, axes in ratios.items():
        log_sum = sum(weights[axis] * statistics.fmean(map(math.log, values)) for axis, values in axes.items())
        totals[lang] = math.exp(log_sum / sum(weights[axis] for axis in axes))
    return totals


def load(argv):
    """Merge the given results files (default: the newest one). A later file overrides an earlier one per
    (kernel, lang, threads) cell, so a partial run (`bench --lang fors`) can be laid over a full baseline."""
    paths = [Path(a) for a in argv[1:]]
    if not paths:
        paths = sorted((ROOT / "results").glob("*.json"))[-1:]
        if not paths:
            sys.exit("no results yet: run `python3 bench/harness/run.py bench` first")
    docs = [json.loads(p.read_text()) for p in paths]
    cells, toolchains, baselines = {}, {}, {}
    for index, doc in enumerate(docs):
        for r in doc["results"]:
            r["_file"] = index
            if r["lang"] == BASELINE and r["correct"] and r["stats"]:
                baselines.setdefault((index, r["kernel"]), []).append(r)
        cells.update({(r["kernel"], r["lang"], r["threads"]): r for r in doc["results"]})
        toolchains.update({lang: v for lang, v in doc["toolchains"].items() if v or lang not in toolchains})
    merged = {**docs[-1], "results": list(cells.values()), "toolchains": toolchains, "_baselines": baselines}
    return " + ".join(p.name for p in paths), merged


def num(value, spec):
    return "-" if value is None else format(value, spec)


def ratio(a, b):
    return a / b if a and b else None


def main():
    name, doc = load(sys.argv)
    host = doc["host"]
    good = [r for r in doc["results"] if r["correct"] and r["stats"]]
    print("# Fors benchmark scoreboard\n")
    print(f"`{name}` | {doc['timestamp']} | {host.get('cpu') or host['arch']}, {host['cpus']} cpus | {host['os']}"
          + (" | **ON BATTERY**" if host.get("on_battery") else ""))
    print(f"\nKernel sources: commit `{doc.get('commit') or 'unrecorded'}`")
    # The noise floor is measured and published, never targeted: a difference smaller than this is not a result.
    noise = sorted((r["stats"]["stdev"] / r["stats"]["mean"], f"{r['kernel']}/{r['lang']}")
                   for r in good if r["stats"]["n"] >= 3 and r["stats"]["mean"] > 0.05)
    if noise:
        worst = noise[-1]
        print(f"\nRun-to-run noise (stdev/mean, cells with >= 3 runs): median {noise[len(noise) // 2][0]:.1%}, "
              f"worst {worst[0]:.1%} ({worst[1]})")
    canary = [c["wall_s"] for c in doc.get("canary", [])]
    if len(canary) >= 2:
        # One slow sample is ordinary desktop interference. Contamination is a sustained first-to-last
        # trend (throttling) or repeated spikes (something else running), so those are what get flagged.
        median = statistics.median(canary)
        spikes = sum(w > 1.05 * median for w in canary)
        third = max(1, len(canary) // 3)
        trend = statistics.median(canary[-third:]) / statistics.median(canary[:third]) - 1
        bad = abs(trend) > 0.05 or spikes > 0.2 * len(canary)
        print(f"\nThermal canary (newest file, {len(canary)} samples): median {median:.3f} s, "
              f"{spikes} spike(s) > 5%, first-to-last trend {trend:+.1%}" + ("  **CONTAMINATED RUN**" if bad else ""))

    kernels, ratios = {}, {}
    for r in good:
        kernels.setdefault(r["kernel"], {}).setdefault(r["lang"], []).append(r)

    for kernel, by_lang in kernels.items():
        best = {lang: min(cells, key=lambda c: c["stats"]["median"]) for lang, cells in by_lang.items()}
        print(f"\n## {kernel}\n")
        print("| language | threads | median s | vs C | peak RSS MiB | vs C | build s | binary KiB | runs |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
        for lang, c in sorted(best.items(), key=lambda kv: kv[1]["stats"]["median"]):
            s = c["stats"]
            build_s = c["build"]["wall_s"] or None
            # Compare against the baseline measured in the SAME session (same results file): machine
            # conditions differ between runs, so a cross-file ratio mixes two experiments.
            own = doc["_baselines"].get((c["_file"], kernel))
            base = min(own, key=lambda b: b["stats"]["median"]) if own else best.get(BASELINE)
            axes = {
                "runtime": ratio(s["median"], base and base["stats"]["median"]),
                "memory": ratio(s["max_rss_bytes"], base and base["stats"]["max_rss_bytes"]),
                "compile": ratio(build_s, base and base["build"]["wall_s"]),
            }
            for axis, value in axes.items():
                if value is not None:
                    ratios.setdefault(lang, {}).setdefault(axis, []).append(value)
            size = c["binary_bytes"] / 1024 if c["binary_bytes"] else None
            print(f"| {lang} | {num(c['threads'], 'd')} | {s['median']:.4f} | {num(axes['runtime'], '.2f')} "
                  f"| {s['max_rss_bytes'] / 2**20:.1f} | {num(axes['memory'], '.2f')} "
                  f"| {num(build_s, '.2f')} | {num(size, '.0f')} | {s['n']} |")

        scaling = {lang: sorted((c for c in cells if c["threads"]), key=lambda c: c["threads"])
                   for lang, cells in by_lang.items()}
        scaling = {lang: cells for lang, cells in scaling.items() if len(cells) > 1 and cells[0]["threads"] == 1}
        if scaling:
            counts = sorted({c["threads"] for cells in scaling.values() for c in cells})
            print(f"\nSpeedup over the same language on 1 thread:\n")
            print("| language | " + " | ".join(f"t={t}" for t in counts) + " |")
            print("|---|" + "---:|" * len(counts))
            for lang, cells in scaling.items():
                t1 = cells[0]["stats"]["median"]
                by_t = {c["threads"]: t1 / c["stats"]["median"] for c in cells}
                print(f"| {lang} | " + " | ".join(num(by_t.get(t), ".2f") for t in counts) + " |")
                top = cells[-1]["threads"]
                ratios.setdefault(lang, {}).setdefault("scaling", []).append(top / by_t[top])

    print("\n## Aggregate\n")
    try:
        totals = score(ratios)
    except NotImplementedError:
        print("_Not defined yet: implement `score()` in bench/harness/report.py._")
    else:
        # Normalised so the baseline reads 1.00; a language measured on fewer kernels is not comparable.
        base = totals.get(BASELINE) or 1.0
        for lang, value in sorted(totals.items(), key=lambda kv: kv[1]):
            covered = len(ratios[lang].get("runtime", []))
            partial = "" if covered == len(kernels) else f"  (partial: {covered}/{len(kernels)} kernels - not comparable)"
            print(f"- {lang}: {value / base:.2f}{partial}")

    failed = [r for r in doc["results"] if not r["correct"]]
    if failed:
        print("\n## Failed cells (excluded above)\n")
        for r in failed:
            print(f"- {r['kernel']}/{r['lang']} t={r['threads']}: {(r['error'] or '')[:200]}")

    print("\n## Toolchains\n")
    for lang, version in doc["toolchains"].items():
        print(f"- {lang}: {version or 'not installed'}")


if __name__ == "__main__":
    main()
