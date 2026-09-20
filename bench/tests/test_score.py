#!/usr/bin/env python3
"""Unit tests pinning score()'s DECIDED policy: a per-axis headline plus an equal-weight
summary, never the old single compile-weighted number (bench/harness/report.py::score(),
docs/spec/06-measurement.md ch06 R9, and the "LoC/sec" vocabulary rule its docstring cites).

  python3 -m unittest discover -s bench/tests
"""
import json
import math
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

BENCH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCH / "harness"))

import report  # noqa: E402


class ScorePerAxisTests(unittest.TestCase):
    """score() returns a geometric mean PER AXIS, not one collapsed number -- pins the decided
    per-axis headline (report.py's score() docstring; ch06-measurement.md)."""

    def test_per_axis_geomeans_are_independent_of_each_other(self):
        ratios = {"fors": {"runtime": [2.0, 8.0], "memory": [4.0], "compile": [9.0]}}
        axes = report.score(ratios)["fors"]["axes"]
        self.assertAlmostEqual(axes["runtime"], 4.0)  # geomean(2, 8) == 4
        self.assertAlmostEqual(axes["memory"], 4.0)
        self.assertAlmostEqual(axes["compile"], 9.0)

    def test_coverage_counts_kernels_per_axis_not_globally(self):
        ratios = {"fors": {"runtime": [2.0, 8.0], "compile": [9.0]}}
        coverage = report.score(ratios)["fors"]["coverage"]
        self.assertEqual(coverage["runtime"], 2)
        self.assertEqual(coverage["compile"], 1)


class ScoreEqualWeightTests(unittest.TestCase):
    """"summary" is an EQUAL-weight geometric mean over whatever axes a language has -- pins the
    removal of the old compile:3/runtime:2/scaling:2/memory:1 weights, which flattered Fors by
    construction (compile speed is this project's headline goal)."""

    def test_summary_is_the_plain_unweighted_geomean(self):
        ratios = {"fors": {"runtime": [1.0], "compile": [100.0]}}
        summary = report.score(ratios)["fors"]["summary"]
        self.assertAlmostEqual(summary, math.sqrt(1.0 * 100.0))  # equal weight: sqrt(1 * 100) = 10

    def test_summary_is_not_the_old_compile_weighted_number(self):
        # Old weights (compile:3, runtime:2) gave exp((3*ln(100) + 2*ln(1)) / 5) =~ 15.85 != 10.
        ratios = {"fors": {"runtime": [1.0], "compile": [100.0]}}
        summary = report.score(ratios)["fors"]["summary"]
        old_weighted = math.exp((3 * math.log(100.0) + 2 * math.log(1.0)) / 5)
        self.assertNotAlmostEqual(summary, old_weighted, delta=1.0)


class ScoreMissingAxisTests(unittest.TestCase):
    """A language with no "compile" axis (no build step, e.g. an interpreter) is scored over the
    axes it has -- never given a fabricated 1.0 filler for the axis it lacks."""

    def test_language_missing_compile_axis_has_no_compile_key(self):
        ratios = {"python": {"runtime": [2.0], "memory": [2.0]}}
        result = report.score(ratios)["python"]
        self.assertNotIn("compile", result["axes"])
        self.assertNotIn("compile", result["coverage"])
        self.assertAlmostEqual(result["summary"], 2.0)  # geomean(2.0, 2.0) -- no compile filler

    def test_missing_axis_does_not_raise_and_does_not_affect_other_languages(self):
        ratios = {
            "c": {"runtime": [1.0, 1.0], "compile": [1.0, 1.0]},
            "python": {"runtime": [2.0]},  # no compile axis at all
        }
        result = report.score(ratios)
        self.assertAlmostEqual(result["c"]["summary"], 1.0)
        self.assertNotIn("compile", result["python"]["axes"])


class ScoreboardLabelTests(unittest.TestCase):
    """The printed scoreboard leads with the four per-axis rankings and labels the aggregate
    number a SUMMARY, never a bare claim (ch06 R9; docs/spec/06-measurement.md vocabulary rule)."""

    @staticmethod
    def cell(kernel, lang, median, build_s=1.0, rss=1000):
        return {"kernel": kernel, "category": "sequential", "lang": lang, "threads": None,
                "qos": "performance", "build": {"ok": True, "wall_s": build_s}, "binary_bytes": 1000,
                "bound": None, "deterministic": False, "runs": [], "correct": True, "error": None,
                "stats": {"n": 3, "min": median, "median": median, "p95": median, "mean": median,
                          "stdev": 0.0, "max_rss_bytes": rss}}

    def results_doc(self, results):
        return {"schema": 1, "timestamp": "2026-01-01T00:00:00Z", "commit": "x",
                "host": {"hostname": "no-such-host", "os": "Darwin", "arch": "arm64", "cpus": 8},
                "toolchains": {"c": "clang", "fors": "0.1", "python": "3.14"}, "langs": {},
                "canary": [], "canary_baseline": None, "canary_threshold": None,
                "contaminated": False, "results": results}

    def run_report(self, results):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "crafted.json"
            path.write_text(json.dumps(self.results_doc(results)))
            proc = subprocess.run([sys.executable, str(BENCH / "harness" / "report.py"), str(path)],
                                  capture_output=True, text=True, timeout=60)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            return proc.stdout

    def test_summary_section_is_labelled_not_a_ranking_claim(self):
        stdout = self.run_report([self.cell("k1", "c", 1.0), self.cell("k1", "fors", 2.0)])
        self.assertIn("Summary", stdout)
        self.assertIn("not a ranking claim", stdout)

    def test_report_leads_the_aggregate_with_four_per_axis_headings_before_the_summary(self):
        stdout = self.run_report([self.cell("k1", "c", 1.0), self.cell("k1", "fors", 2.0)])
        aggregate = stdout.split("## Aggregate", 1)[1]
        self.assertLess(aggregate.index("### Runtime"), aggregate.index("### Summary"),
                         "the per-axis headline must lead the equal-weight summary")

    def test_a_language_on_fewer_kernels_is_labelled_partial_not_silently_ranked(self):
        # python only ran k1, c and fors ran both k1 and k2 -- ch06 R9: python must not share a
        # ranking with the fully-measured languages on any axis.
        stdout = self.run_report([
            self.cell("k1", "c", 1.0), self.cell("k1", "fors", 2.0), self.cell("k1", "python", 4.0),
            self.cell("k2", "c", 1.0), self.cell("k2", "fors", 2.0),
        ])
        runtime_section = stdout.split("### Runtime", 1)[1].split("###", 1)[0]
        self.assertIn("python", runtime_section)
        self.assertIn("partial", runtime_section)
        summary_section = stdout.split("### Summary", 1)[1]
        self.assertIn("partial", summary_section)

    def test_a_fast_partial_language_is_listed_after_every_ranked_one(self):
        """ch06 R9 is "excluded from ranking", not "annotated": a partial-coverage language with
        the BEST number on an axis must not appear at the top of that axis's list, where a reader
        (or a scraper taking the first row) would read it as rank 1."""
        stdout = self.run_report([
            self.cell("k1", "c", 1.0), self.cell("k1", "fors", 0.9),
            self.cell("k2", "c", 1.0), self.cell("k2", "fors", 0.9),
            # rust ran one kernel only, and is 10x faster on it
            self.cell("k1", "rust", 0.1, rss=500),
        ])
        for section in ("### Runtime", "### Memory", "### Summary"):
            body = stdout.split(section, 1)[1].split("###", 1)[0].split("\n## ", 1)[0]
            rows = [ln for ln in body.splitlines() if ln.startswith("- ")]
            self.assertTrue(rows, section)
            partial = [i for i, ln in enumerate(rows) if "partial" in ln]
            ranked = [i for i, ln in enumerate(rows) if "partial" not in ln]
            self.assertTrue(partial and ranked, f"{section}: {rows}")
            self.assertGreater(min(partial), max(ranked),
                               f"{section}: a partial row is ranked above a fully-measured one: {rows}")


if __name__ == "__main__":
    unittest.main()
