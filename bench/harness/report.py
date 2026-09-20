#!/usr/bin/env python3
"""Markdown scoreboard from a harness results file.

  report.py [results.json ...]  default: the newest file in bench/results/; several files are merged
"""
import json
import math
import statistics
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "c"


def load_machine(host):
    """The M0.P roofline/capacity calibration for THIS host (bench/calibrate/calibrate.py's
    output), or None if it has never been run here. ch06-measurement.md names the consequence:
    no roofline fraction may be printed without one, and this is what enforces that below."""
    hostname = (host.get("hostname") or "").split(".")[0]
    path = ROOT / "results" / f"machine-{hostname}.json"
    if not path.exists():
        return None
    doc = json.loads(path.read_text())
    # calibrate.py's per-thread-count dicts round-trip through JSON with string keys.
    for kernel_results in doc.get("results", {}).values():
        for qos_class in kernel_results.values():
            for key in list(qos_class.keys()):
                if isinstance(key, str) and key.lstrip("-").isdigit():
                    qos_class[int(key)] = qos_class.pop(key)
    return doc


def capacity_at(t, model):
    """capacity(T) from the P-vs-E capacity model calibrate.py measured -- R18's "capacity-
    normalised denominator" for compute-bound efficiency. None (not 1.0) when the model itself
    says its taskpolicy-based E-core weight was not statistically distinguishable from no effect."""
    if not model or not model.get("available") or model.get("e_weight") is None or not model.get("taskpolicy_effective"):
        return None
    p = model["p_cores"]
    return min(t, p) * 1.0 + max(0, t - p) * model["e_weight"]


def bandwidth_peak_at(t, machine):
    if not machine:
        return None
    cell = machine["results"]["bandwidth"]["performance"].get(t)
    return cell["best"]["bandwidth_gbps"] if cell else None


_kernel_spec_cache = {}


def kernel_spec(name):
    if name not in _kernel_spec_cache:
        path = ROOT / "kernels" / name / "spec.toml"
        _kernel_spec_cache[name] = tomllib.loads(path.read_text()) if path.exists() else None
    return _kernel_spec_cache[name]


def stream_gbps(median_s, size_args=None):
    """STREAM-triad byte accounting (2 reads + 1 write, 8 bytes each, per element per rep) -- the
    same convention bench/calibrate/bandwidth.c uses, so numerator and denominator of the
    fraction-of-roofline are counted the same way (this convention excludes the write-allocate
    read; it is a convention, stated, applied on BOTH sides).

    The sizes come from the cell itself (`size_args`, recorded by run.py at measurement time) and
    fall back to spec.toml's bench sizes only for older results files -- dividing a measured time
    by sizes read out of today's spec.toml would silently produce a wrong throughput for any cell
    measured at other sizes."""
    args = size_args or (kernel_spec("stream") or {}).get("sizes", {}).get("bench")
    if not args or len(args) < 2 or not median_s:
        return None
    n, reps = int(args[0]), int(args[1])
    return 3 * 8 * n * reps / median_s / 1e9


# Kernel-specific achieved-throughput formulas for bandwidth-bound kernels: deliberately NOT a
# generic guess (a different memory-traffic shape needs its own formula), so a new bandwidth-
# bound kernel silently gets no fraction-of-roofline row until someone adds one here.
BANDWIDTH_THROUGHPUT = {"stream": stream_gbps}


def qos_of(cell):
    """A results cell's core class. Cells without an explicit "qos" are performance-QoS (today
    every cell `run.py bench` writes is; there is no background-QoS kernel-run mode yet)."""
    return cell.get("qos") or "performance"


def series_label(cell):
    """The identity a cell is reported under. R17 (performance-core and efficiency-core points
    MUST NOT be merged) is enforced HERE, at the identity itself, rather than only in the scaling
    grouping: a background-QoS cell is a different series from the same language's performance-QoS
    cell everywhere in this report -- in the per-kernel table, in the cell-merge key in load(), in
    the vs-C baseline lookup, and in the aggregate score. Grouping alone was not enough: load()
    merges cells by key, so a key without the core class silently let a background cell REPLACE
    the performance cell of the same (kernel, lang, threads) before any grouping ran."""
    qos = qos_of(cell)
    return cell["lang"] if qos == "performance" else f"{cell['lang']} [{qos}]"


def group_scaling(by_series):
    """Group a kernel's parallel (threads is not None) cells by (series, qos), sorted by thread
    count, keeping only groups that start at t=1 with more than one point. by_series is already
    keyed by series_label(), so each group is single-core-class by construction (R17)."""
    groups = {}
    for series, cells in by_series.items():
        for c in sorted((c for c in cells if c["threads"]), key=lambda c: c["threads"]):
            groups.setdefault((series, qos_of(c)), []).append(c)
    return {key: cells for key, cells in groups.items() if len(cells) > 1 and cells[0]["threads"] == 1}


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
    (kernel, series, threads) cell -- series, not language, so a background-QoS cell never overwrites the
    performance-QoS cell it is supposed to sit beside (R17). A partial run (`bench --lang fors`) can still
    be laid over a full baseline."""
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
                # Baselines are per core class too: a background-QoS C run must never be the
                # denominator of a performance-QoS cell.
                baselines.setdefault((index, r["kernel"], qos_of(r)), []).append(r)
        cells.update({(r["kernel"], series_label(r), r["threads"]): r for r in doc["results"]})
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
    if doc.get("canary_baseline") is not None:
        # Authoritative path (run.py >= M0.P): a pre-run calibration burst gives THIS run's own
        # canary noise floor, and the drift threshold is sized relative to it (rules 19 and 21),
        # not a fixed percentage -- run.py already made the contaminated/not decision; this just
        # surfaces it.
        base, thr = doc["canary_baseline"], doc.get("canary_threshold")
        print(f"\nThermal canary (newest file, {len(canary)} samples, {base['reps']}-rep calibration): "
              f"baseline median {base['median_s']:.4f}s (cov {base['cov']:.1%}), "
              f"drift threshold {thr:.1%}" + ("  **CONTAMINATED RUN**" if doc.get("contaminated") else ""))
    elif len(canary) >= 2:
        # Fallback for results files predating the calibrated threshold above: a sustained
        # first-to-last trend (throttling) or repeated spikes, against fixed percentages.
        median = statistics.median(canary)
        spikes = sum(w > 1.05 * median for w in canary)
        third = max(1, len(canary) // 3)
        head = statistics.median(canary[:third])
        trend = (statistics.median(canary[-third:]) / head - 1) if head else 0.0
        bad = abs(trend) > 0.05 or spikes > 0.2 * len(canary)
        print(f"\nThermal canary (newest file, {len(canary)} samples, legacy heuristic -- no "
              f"calibration burst in this results file): median {median:.3f} s, "
              f"{spikes} spike(s) > 5%, first-to-last trend {trend:+.1%}" + ("  **CONTAMINATED RUN**" if bad else ""))

    machine = load_machine(host)
    if machine is None:
        print("\nRoofline: not calibrated for this host -- run `python3 bench/calibrate/calibrate.py` "
              "on a quiet, pinned machine, then re-run this report. No roofline fraction below.")
    elif machine.get("contaminated"):
        print(f"\nRoofline: machine-{host.get('hostname', '?').split('.')[0]}.json is marked "
              f"contaminated -- treat any fraction-of-roofline number below as provisional.")

    kernels, ratios = {}, {}
    for r in good:
        kernels.setdefault(r["kernel"], {}).setdefault(series_label(r), []).append(r)

    for kernel, by_series in kernels.items():
        best = {series: min(cells, key=lambda c: c["stats"]["median"]) for series, cells in by_series.items()}
        print(f"\n## {kernel}\n")
        # "language (qos)": a background-QoS series is listed under its own name, never folded
        # into the language's row (R17).
        print("| language (qos) | threads | median s | vs C | peak RSS MiB | vs C | build s | binary KiB | runs |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
        for series, c in sorted(best.items(), key=lambda kv: kv[1]["stats"]["median"]):
            s = c["stats"]
            build_s = c["build"]["wall_s"] or None
            # Compare against the baseline measured in the SAME session (same results file): machine
            # conditions differ between runs, so a cross-file ratio mixes two experiments.
            own = doc["_baselines"].get((c["_file"], kernel, qos_of(c)))
            base = min(own, key=lambda b: b["stats"]["median"]) if own else best.get(BASELINE)
            axes = {
                "runtime": ratio(s["median"], base and base["stats"]["median"]),
                "memory": ratio(s["max_rss_bytes"], base and base["stats"]["max_rss_bytes"]),
                "compile": ratio(build_s, base and base["build"]["wall_s"]),
            }
            for axis, value in axes.items():
                if value is not None:
                    ratios.setdefault(series, {}).setdefault(axis, []).append(value)
            size = c["binary_bytes"] / 1024 if c["binary_bytes"] else None
            print(f"| {series} | {num(c['threads'], 'd')} | {s['median']:.4f} | {num(axes['runtime'], '.2f')} "
                  f"| {s['max_rss_bytes'] / 2**20:.1f} | {num(axes['memory'], '.2f')} "
                  f"| {num(build_s, '.2f')} | {num(size, '.0f')} | {s['n']} |")

        scaling = group_scaling(by_series)  # R17: (series, qos) groups, never merged across QoS classes
        bound = next((c.get("bound") for cells in scaling.values() for c in cells if c.get("bound")), None)
        if scaling:
            counts = sorted({c["threads"] for cells in scaling.values() for c in cells})
            print(f"\nSpeedup over the same language on 1 thread (bound = **{bound or 'unclassified'}**):\n")
            print("| language (qos) | " + " | ".join(f"t={t}" for t in counts) + " |")
            print("|---|" + "---:|" * len(counts))
            by_key_speedup = {}
            for (label, qos), cells in scaling.items():
                t1 = cells[0]["stats"]["median"]
                by_t = {c["threads"]: t1 / c["stats"]["median"] for c in cells}
                by_key_speedup[label] = by_t
                print(f"| {label} | " + " | ".join(num(by_t.get(t), ".2f") for t in counts) + " |")
                if bound == "compute":
                    # Rule 15: parallel efficiency (speedup/cores, here speedup/capacity) only
                    # gates COMPUTE-bound kernels -- a bandwidth-bound kernel's speedup never
                    # feeds the single aggregate "scaling" score below.
                    top = cells[-1]["threads"]
                    ratios.setdefault(label, {}).setdefault("scaling", []).append(top / by_t[top])

            if bound == "compute":
                model = machine.get("capacity_model") if machine else None
                # R18: the capacity-normalised denominator, stated explicitly, not left implicit.
                denom = model["formula"] if model and model.get("available") else \
                    "unavailable (no machine calibration, or taskpolicy had no measurable effect on this box)"
                print(f"\nCapacity-normalised efficiency = speedup / capacity(T). capacity(T) = {denom}\n")
                if model and model.get("available"):
                    print("| language (qos) | " + " | ".join(f"t={t}" for t in counts) + " |")
                    print("|---|" + "---:|" * len(counts))
                    for label, by_t in by_key_speedup.items():
                        eff = {t: ratio(by_t.get(t), capacity_at(t, model)) for t in counts}
                        print(f"| {label} | " + " | ".join(num(eff.get(t), ".2f") for t in counts) + " |")
            elif bound == "bandwidth":
                # Rule 16: bandwidth-bound kernels are gated on fraction of measured roofline, as
                # a CURVE, never collapsed into one ratio -- so no `ratios[...]["scaling"]` entry
                # is ever added for them (see the `if bound == "compute"` guard above).
                formula = BANDWIDTH_THROUGHPUT.get(kernel)
                print("\nFraction of measured bandwidth roofline at that T (never a single ratio - rule 16):\n")
                if machine is None:
                    print("_roofline not calibrated for this host -- no fraction printed (see above)._")
                elif formula is None:
                    print(f"_no achieved-throughput formula registered for `{kernel}` in report.py's "
                          f"BANDWIDTH_THROUGHPUT -- add one before trusting a roofline claim for it._")
                else:
                    print("| language (qos) | " + " | ".join(f"t={t}" for t in counts) + " |")
                    print("|---|" + "---:|" * len(counts))
                    for (label, _qos), cells in scaling.items():
                        fracs = {c["threads"]: ratio(formula(c["stats"]["median"], c.get("size_args")),
                                                     bandwidth_peak_at(c["threads"], machine))
                                 for c in cells}
                        print(f"| {label} | " + " | ".join(num(fracs.get(t), ".2f") for t in counts) + " |")

    print("\n## Aggregate\n")
    try:
        totals = score(ratios)
    except NotImplementedError:
        print("_Not defined yet: implement `score()` in bench/harness/report.py._")
    else:
        # Normalised so the baseline reads 1.00; a language measured on fewer kernels is not comparable.
        base = totals.get(BASELINE) or 1.0
        for series, value in sorted(totals.items(), key=lambda kv: kv[1]):
            covered = len(ratios[series].get("runtime", []))
            partial = "" if covered == len(kernels) else f"  (partial: {covered}/{len(kernels)} kernels - not comparable)"
            print(f"- {series}: {value / base:.2f}{partial}")

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
