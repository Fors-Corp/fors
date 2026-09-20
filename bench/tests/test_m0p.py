#!/usr/bin/env python3
"""Unit tests for the M0.P measurement tooling (stdlib unittest only).

  python3 -m unittest discover -s bench/tests

These are UNIT tests over pure arithmetic/parsing functions plus one build-only smoke test;
none of them time anything meaningfully (ch06 rule 20: benchmarks never run concurrently with
other workloads, so nothing here may be added to CI as a timing claim -- see bench/README.md's
"Parallel family (M0.P)" section for why the C-compiling tests specifically are NOT wired into
CI even though they need no *time*, only a C compiler CI may not have).
"""
import json
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

BENCH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCH / "harness"))
sys.path.insert(0, str(BENCH / "calibrate"))

import run as harness          # noqa: E402
import report                  # noqa: E402
import calibrate               # noqa: E402


class CanaryContaminationTests(unittest.TestCase):
    """run.py's canary_drift_threshold / canary_contaminated (rules 19, 21)."""

    def test_threshold_scales_with_measured_noise(self):
        quiet = harness.canary_drift_threshold(cov=0.01)
        noisy = harness.canary_drift_threshold(cov=0.10)
        self.assertLess(quiet, noisy)

    def test_threshold_has_a_floor(self):
        # A suspiciously perfect calibration (cov=0) must not make ordinary jitter "contaminated".
        self.assertEqual(harness.canary_drift_threshold(cov=0.0), harness.CANARY_DRIFT_FLOOR)

    def test_no_drift_is_not_contaminated(self):
        ok, bad = harness.canary_contaminated(0.200, [0.199, 0.201, 0.198], threshold=0.05)
        self.assertFalse(ok)
        self.assertEqual(bad, [])

    def test_drift_beyond_threshold_is_contaminated(self):
        ok, bad = harness.canary_contaminated(0.200, [0.199, 0.35, 0.201], threshold=0.05)
        self.assertTrue(ok)
        self.assertEqual(bad, [0.35])

    def test_no_samples_is_never_contaminated(self):
        ok, bad = harness.canary_contaminated(0.200, [], threshold=0.05)
        self.assertFalse(ok)
        self.assertEqual(bad, [])


class DeterminismComparerTests(unittest.TestCase):
    """run.py's compare_outputs -- the determinism gate's core (separate from, and not a
    weakening of, the existing quantized correctness check)."""

    def test_identical_outputs_pass(self):
        ok, diverged = harness.compare_outputs({1: "42", 2: "42", 4: "42"})
        self.assertTrue(ok)
        self.assertEqual(diverged, [])

    def test_diverging_output_fails_and_names_the_thread_count(self):
        ok, diverged = harness.compare_outputs({1: "42", 2: "43", 4: "42"})
        self.assertFalse(ok)
        self.assertEqual(diverged, [2])

    def test_empty_is_trivially_ok(self):
        ok, diverged = harness.compare_outputs({})
        self.assertTrue(ok)
        self.assertEqual(diverged, [])


class ManifestParsingTests(unittest.TestCase):
    """The new `bound` / `deterministic` spec.toml fields parse and don't leak into [sizes]
    (the exact TOML trap bench/README.md already warns about for `threads`/`exclude`)."""

    EXPECTED_BOUND = {"mandelbrot": "compute", "matmul": "compute", "reduce": "compute", "stream": "bandwidth"}

    def test_parallel_kernels_declare_bound_and_deterministic(self):
        for name, bound in self.EXPECTED_BOUND.items():
            with self.subTest(kernel=name):
                spec = tomllib.loads((BENCH / "kernels" / name / "spec.toml").read_text())
                self.assertEqual(spec.get("bound"), bound)
                self.assertIs(spec.get("deterministic"), True)
                self.assertNotIn("bound", spec["sizes"])
                self.assertNotIn("deterministic", spec["sizes"])

    def test_load_kernels_carries_the_fields(self):
        kernels = harness.load_kernels(["stream"])
        self.assertEqual(kernels["stream"]["bound"], "bandwidth")
        self.assertTrue(kernels["stream"]["deterministic"])

    def test_non_parallel_kernel_has_no_bound(self):
        kernels = harness.load_kernels(["nbody"])
        self.assertIsNone(kernels["nbody"].get("bound"))


class ReportCoreClassTests(unittest.TestCase):
    """report.py must never merge performance-QoS and background-QoS points into one curve
    (rule 17), and must refuse a roofline fraction with no calibration file (open question 4 /
    rule 16)."""

    def test_group_scaling_separates_qos_classes(self):
        by_lang = {
            "c": [
                {"threads": 1, "qos": "performance"}, {"threads": 2, "qos": "performance"},
                {"threads": 1, "qos": "background"}, {"threads": 2, "qos": "background"},
            ],
        }
        groups = report.group_scaling(by_lang)
        self.assertEqual(set(groups.keys()), {("c", "performance"), ("c", "background")})
        for cells in groups.values():
            self.assertTrue(all(c["qos"] == cells[0]["qos"] for c in cells), "a group mixed QoS classes")

    def test_group_scaling_defaults_missing_qos_to_performance(self):
        by_lang = {"c": [{"threads": 1}, {"threads": 2}]}
        groups = report.group_scaling(by_lang)
        self.assertEqual(list(groups.keys()), [("c", "performance")])

    def test_group_scaling_drops_single_point_or_non_t1_start(self):
        by_lang = {"c": [{"threads": 2, "qos": "performance"}, {"threads": 4, "qos": "performance"}]}
        self.assertEqual(report.group_scaling(by_lang), {})

    def test_capacity_at_uses_p_cores_then_e_weight(self):
        model = {"available": True, "taskpolicy_effective": True, "p_cores": 6, "e_weight": 0.5}
        self.assertAlmostEqual(report.capacity_at(1, model), 1.0)
        self.assertAlmostEqual(report.capacity_at(6, model), 6.0)
        self.assertAlmostEqual(report.capacity_at(8, model), 6.0 + 2 * 0.5)

    def test_capacity_at_none_when_taskpolicy_not_effective(self):
        model = {"available": True, "taskpolicy_effective": False, "p_cores": 6, "e_weight": 0.98}
        self.assertIsNone(report.capacity_at(8, model))

    def test_capacity_at_none_without_model(self):
        self.assertIsNone(report.capacity_at(4, None))
        self.assertIsNone(report.capacity_at(4, {"available": False}))

    def test_load_machine_absent_returns_none(self):
        with tempfile.TemporaryDirectory() as tmp:
            old_root = report.ROOT
            report.ROOT = Path(tmp)
            try:
                self.assertIsNone(report.load_machine({"hostname": "nonexistent-host"}))
            finally:
                report.ROOT = old_root

    def test_load_machine_restores_integer_thread_keys(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "results").mkdir()
            doc = {"results": {"bandwidth": {"performance": {"1": {"best": {"bandwidth_gbps": 90.0}},
                                                               "2": {"best": {"bandwidth_gbps": 80.0}}}}}}
            (root / "results" / "machine-testhost.json").write_text(json.dumps(doc))
            old_root = report.ROOT
            report.ROOT = root
            try:
                machine = report.load_machine({"hostname": "testhost.local"})
                self.assertIsNotNone(machine)
                self.assertEqual(report.bandwidth_peak_at(1, machine), 90.0)
                self.assertEqual(report.bandwidth_peak_at(2, machine), 80.0)
                self.assertIsNone(report.bandwidth_peak_at(4, machine))
            finally:
                report.ROOT = old_root

    def test_stream_gbps_matches_the_triad_byte_count(self):
        spec = tomllib.loads((BENCH / "kernels" / "stream" / "spec.toml").read_text())
        n, reps = (int(x) for x in spec["sizes"]["bench"][:2])
        median_s = 2.0
        expected = 3 * 8 * n * reps / median_s / 1e9
        self.assertAlmostEqual(report.stream_gbps(median_s), expected)

    def test_stream_gbps_none_without_a_median(self):
        self.assertIsNone(report.stream_gbps(0))
        self.assertIsNone(report.stream_gbps(None))


class ResultsMergeCoreClassTests(unittest.TestCase):
    """report.py's load() merge key. Regression: the key used to be (kernel, lang, threads), so a
    background-QoS cell REPLACED the performance-QoS cell of the same (kernel, lang, threads) and
    the performance curve vanished from the report entirely -- R17 violated upstream of the
    grouping that was supposed to enforce it."""

    @staticmethod
    def cell(lang, threads, median, qos):
        return {"kernel": "mandelbrot", "category": "parallel", "lang": lang, "threads": threads,
                "qos": qos, "build": {"ok": True, "wall_s": 1.0}, "binary_bytes": 1,
                "bound": "compute", "deterministic": True, "runs": [], "correct": True, "error": None,
                "stats": {"n": 3, "min": median, "median": median, "p95": median, "mean": median,
                          "stdev": 0.0, "max_rss_bytes": 1}}

    def results_doc(self):
        results = [self.cell("c", t, m, "performance") for t, m in ((1, 1.0), (2, 0.5))]
        results += [self.cell("c", t, m, "background") for t, m in ((1, 4.0), (2, 2.0))]
        return {"schema": 1, "timestamp": "2026-01-01T00:00:00Z", "commit": "x",
                "host": {"hostname": "no-such-host", "os": "Darwin", "arch": "arm64", "cpus": 8},
                "toolchains": {"c": "clang"}, "langs": {}, "canary": [], "canary_baseline": None,
                "canary_threshold": None, "contaminated": False, "results": results}

    def test_background_cells_do_not_overwrite_performance_cells(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "crafted.json"
            path.write_text(json.dumps(self.results_doc()))
            _, doc = report.load(["report.py", str(path)])
            self.assertEqual(len(doc["results"]), 4, "a core class was merged away by the cell key")
            labels = {report.series_label(r) for r in doc["results"]}
            self.assertEqual(labels, {"c", "c [background]"})

    def test_baselines_are_per_core_class(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "crafted.json"
            path.write_text(json.dumps(self.results_doc()))
            _, doc = report.load(["report.py", str(path)])
            keys = set(doc["_baselines"].keys())
            self.assertEqual(keys, {(0, "mandelbrot", "performance"), (0, "mandelbrot", "background")})

    def test_report_prints_both_series_separately(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "crafted.json"
            path.write_text(json.dumps(self.results_doc()))
            proc = subprocess.run([sys.executable, str(BENCH / "harness" / "report.py"), str(path)],
                                  capture_output=True, text=True, timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("| c [background] |", proc.stdout)
            self.assertIn("\n| c | ", proc.stdout)


class StreamThroughputProvenanceTests(unittest.TestCase):
    """The bandwidth-bound throughput formula must divide by the sizes the CELL was measured at."""

    def test_uses_the_cells_own_size_args(self):
        self.assertAlmostEqual(report.stream_gbps(2.0, ["1000", "10"]), 3 * 8 * 1000 * 10 / 2.0 / 1e9)

    def test_falls_back_to_spec_sizes_for_older_files(self):
        spec = tomllib.loads((BENCH / "kernels" / "stream" / "spec.toml").read_text())
        n, reps = (int(x) for x in spec["sizes"]["bench"][:2])
        self.assertAlmostEqual(report.stream_gbps(2.0), 3 * 8 * n * reps / 2.0 / 1e9)

    def test_run_py_records_size_args_and_qos_on_every_bench_cell(self):
        source = (BENCH / "harness" / "run.py").read_text()
        self.assertIn('"size_args"', source)
        self.assertIn('"qos": "performance"', source)


class DeterminismComparesBytesTests(unittest.TestCase):
    """The gate must compare raw bytes, not run_once()'s decoded/stripped text."""

    def test_stdout_bytes_returns_raw_bytes_including_trailing_whitespace(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "run.out").write_bytes(b"42 \n")
            self.assertEqual(harness.stdout_bytes(out), b"42 \n")

    def test_comparer_separates_byte_strings_that_strip_to_the_same_text(self):
        ok, diverged = harness.compare_outputs({1: b"42\n", 2: b"42 \n"})
        self.assertFalse(ok)
        self.assertEqual(diverged, [2])


class CalibrateArithmeticTests(unittest.TestCase):
    """calibrate.py's capacity_model / cov on synthetic numbers -- no C compiler, no subprocess."""

    def test_cov_needs_at_least_two_samples(self):
        self.assertIsNone(calibrate.cov([1.0]))
        self.assertIsNone(calibrate.cov([]))

    def test_cov_zero_for_identical_samples(self):
        self.assertEqual(calibrate.cov([5.0, 5.0, 5.0]), 0.0)

    def test_capacity_model_reports_effective_when_ratio_exceeds_threshold(self):
        perf = {1: {"best": {"flops_gflops": 10.0}, "throughputs": [10.0, 10.0, 10.0]}}
        bg = {1: {"best": {"flops_gflops": 5.0}, "throughputs": [5.0, 5.0, 5.0]}}
        model = calibrate.capacity_model(p_cores=6, flops_sweep_perf=perf, flops_sweep_bg=bg)
        self.assertTrue(model["available"])
        self.assertTrue(model["taskpolicy_effective"])
        self.assertAlmostEqual(model["e_weight"], 0.5)

    def test_capacity_model_flags_ineffective_taskpolicy(self):
        # Background QoS barely different from performance QoS: must NOT be reported as a
        # trustworthy weight (this is the "say so loudly, don't publish 1.0 silently" check).
        perf = {1: {"best": {"flops_gflops": 10.0}, "throughputs": [10.0, 9.9, 10.1]}}
        bg = {1: {"best": {"flops_gflops": 9.9}, "throughputs": [9.9, 9.8, 10.0]}}
        model = calibrate.capacity_model(p_cores=6, flops_sweep_perf=perf, flops_sweep_bg=bg)
        self.assertTrue(model["available"])
        self.assertFalse(model["taskpolicy_effective"])
        self.assertIn("warning", model)

    def test_capacity_model_unavailable_when_performance_rate_is_zero(self):
        # Regression: this used to compute weight=None and then crash formatting the warning.
        perf = {1: {"best": {"flops_gflops": 0.0}, "throughputs": [0.0]}}
        bg = {1: {"best": {"flops_gflops": 0.0}, "throughputs": [0.0]}}
        model = calibrate.capacity_model(p_cores=6, flops_sweep_perf=perf, flops_sweep_bg=bg)
        self.assertFalse(model["available"])
        self.assertIn("reason", model)

    def test_capacity_model_unavailable_without_t1(self):
        model = calibrate.capacity_model(p_cores=6, flops_sweep_perf={}, flops_sweep_bg={})
        self.assertFalse(model["available"])

    def test_parse_line_reads_key_value_pairs(self):
        parsed = calibrate.parse_line("bandwidth_gbps=12.5 checksum=3.0 n=100 threads=2\n")
        self.assertEqual(parsed["bandwidth_gbps"], 12.5)
        self.assertEqual(parsed["n"], 100)
        self.assertEqual(parsed["threads"], 2)

    def test_declared_threads_caps_at_cpu_count(self):
        self.assertEqual(calibrate.declared_threads(cpus=4, requested=None), [1, 2, 4])
        self.assertEqual(calibrate.declared_threads(cpus=8, requested=[1, 3, 8]), [1, 3, 8])


class CalibrationKernelSmokeTest(unittest.TestCase):
    """Builds both calibration kernels at tiny sizes (clang must be on PATH; this is exactly
    the C-compiler dependency bench/README.md says keeps this class out of CI) and checks their
    checksums are stable in the two well-defined senses: bandwidth's checksum is IDENTICAL
    across thread counts (disjoint blocks, order-independent exact sums); flops' checksum
    scales EXACTLY with thread count (every thread runs an identical, independent recurrence)."""

    @classmethod
    def setUpClass(cls):
        import shutil
        if shutil.which("clang") is None:
            raise unittest.SkipTest("clang not on PATH")
        cls.tmp = tempfile.TemporaryDirectory()
        build_dir = Path(cls.tmp.name)
        cls.bandwidth = build_dir / "bandwidth"
        cls.flops = build_dir / "flops"
        for name, exe in (("bandwidth", cls.bandwidth), ("flops", cls.flops)):
            cmd = calibrate.cc_flags() + ["-o", str(exe), str(BENCH / "calibrate" / f"{name}.c"), "-lm"]
            subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=60)

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def run_bin(self, exe, args):
        proc = subprocess.run([str(exe), *map(str, args)], capture_output=True, text=True, timeout=10)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        return calibrate.parse_line(proc.stdout)

    def test_bandwidth_checksum_identical_across_thread_counts(self):
        checksums = {t: self.run_bin(self.bandwidth, [2000, 2, t])["checksum"] for t in (1, 2, 4)}
        self.assertEqual(len(set(checksums.values())), 1, checksums)

    def test_flops_default_chain_count_is_not_latency_bound(self):
        """The FLOP kernel's default CHAINS must stay high enough to measure FMA THROUGHPUT.
        With too few independent chains the loop measures FMA latency and reports it as the
        machine's peak FLOP rate -- which would make every later fraction-of-roofline claim look
        several times better than it is. No timing here: this asserts the structural constant."""
        rec = self.run_bin(self.flops, [1000, 1])
        self.assertGreaterEqual(rec["chains"], 16)

    def test_flops_chain_count_is_a_compile_time_knob(self):
        """calibrate.py sweeps CHAINS and keeps the best rate; that requires -DCHAINS to work."""
        exe = Path(self.tmp.name) / "flops-c16"
        cmd = calibrate.cc_flags() + ["-DCHAINS=16", "-o", str(exe),
                                       str(BENCH / "calibrate" / "flops.c"), "-lm"]
        subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=60)
        self.assertEqual(self.run_bin(exe, [1000, 1])["chains"], 16)

    def test_flops_checksum_scales_exactly_with_thread_count(self):
        # The C program prints the checksum at 6 decimal places (see flops.c), so a single
        # printed value already carries ~1e-6 of rounding; compare with that much slack rather
        # than demanding bit-exactness from a %.6f-formatted round trip.
        c1 = self.run_bin(self.flops, [5000, 1])["checksum"]
        c2 = self.run_bin(self.flops, [5000, 2])["checksum"]
        c4 = self.run_bin(self.flops, [5000, 4])["checksum"]
        self.assertAlmostEqual(c2, 2 * c1, delta=1e-5)
        self.assertAlmostEqual(c4, 4 * c1, delta=1e-5)


if __name__ == "__main__":
    unittest.main()
