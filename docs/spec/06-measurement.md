# 06 — Measurement: kernel tiers, baselines and metric definitions

## Status

Normative; owns the definitions below (no other document may redefine them, per `docs/PLAN.md` §6). Authority: `docs/PLAN.md` §§3, 5, 6. Supersedes conflicting wording in `docs/design/reviews.md` and `bench/README.md`, which stay descriptive.

## Scope

What may be measured, on which kernels/applications, under what freeze discipline, and how compile-speed, parallel, noise and security numbers are computed and published. Not numeric pass/fail targets (PLAN.md §3/§5) or harness implementation (`bench/README.md`).

## Definitions

**Tier A** — the enumerated kernel set gating codegen-quality (compiler C6/C7, roadmap M5–M7). Only kernels in the Tier A table count toward a Tier A geomean.

**Tier B** — five real applications gating end-to-end competitiveness (M7 "Tier B within 15%").

**Pre-registration** — a kernel enters Tier A/B only via a dated, committed addition; membership at the time of a published number is reconstructable from that commit.

**Roofline** — the machine's measured peak memory bandwidth and peak FLOP rate, from calibration kernels, not vendor spec sheets.

**Noise floor** — the measured run-to-run variation of a metric on this machine, idle; not a target.

**The three cold variants** — applied identically to every language: (a) *everything-from-source* (stdlib and dependencies compiled from source); (b) *stdlib-prebuilt-project-cold* (stdlib/toolchain warm, project's own cache empty); (c) *warm-incremental* (daemon/cache warm, one declared edit applied).

**Edit classes** (for the incremental distribution) — comment/whitespace, function body, private signature, public signature in a leaf module, public signature in a core module.

**Geomean formula** — for a language L over kernel set K, `geomean_L = (Π_{k∈K} time_L(k)/time_C(k))^(1/|K|)`, C being the strict-IEEE baseline; only kernels where L has a published, correctness-gated result enter K.

**Tracks** — *stdlib-only* (no third-party libraries; the default, rule-compliant track) and *best-of-ecosystem* (external libraries permitted, reported separately, never merged into the stdlib-only geomean).

## Rules

1. No performance/security claim MUST be published without a committed harness run producing it (results JSON + commit hash).
2. Tier A/B MUST be frozen tables in this document; a numeric exit gate MUST NOT cite an unenumerated kernel set.
3. Kernels MUST only be ADDED, each with a labelled addition date; none MUST be removed or re-tuned once a published result depends on it.
4. Every published number MUST record the source commit of the kernel and baseline sources.
5. Every baseline implementation MUST be published next to every number it produced.
6. Exact compiler versions/flags MUST live in `bench/langs/*.toml`, copied verbatim into every results file.
7. Strict-IEEE (`c`) and compiler-default-contraction (`c-fma`) columns MUST both be published wherever contraction affects output; Fors MUST default to strict IEEE.
8. Parallel baselines (Rayon, OpenMP, OpenCilk, Kokkos) MUST publish naive and tuned columns, tuned sources cited by upstream commit where one exists.
9. A language measured on fewer kernels than the current tables MUST NOT share a geomean with a fully-measured one; partial coverage MUST be labelled and excluded from ranking. Stdlib-only and best-of-ecosystem geomeans MUST NOT be merged.
10. Compile-speed MUST be wall-clock including link time; lines-per-second MUST NOT be published.
11. Every cold-build claim MUST name which of the three cold variants (§Definitions) it uses; compared languages MUST use the same variant.
12. The incremental benchmark MUST report p50/p95 over the declared edit-class distribution, never a single chosen edit, with a named comparator row per toolchain.
13. Daemon incremental numbers MUST be published beside a `--no-daemon` row for the same edit; daemon RSS and first-build-after-start MUST also be reported.
14. Edit-to-test-result latency MUST be reported alongside raw build time wherever incremental numbers are published.
15. Parallel efficiency (speedup/cores) MUST only gate kernels marked compute-bound in the Tier A table.
16. Bandwidth-bound kernels MUST be gated on fraction of measured roofline; their scaling MUST be reported as a curve, not one ratio.
17. Performance-core and efficiency-core points MUST NOT be merged into one scaling curve.
18. Every scaling figure MUST state its capacity-normalised denominator.
19. The noise floor MUST be measured and published per metric before any comparison uses it; a difference below it MUST NOT be reported as a result.
20. Benchmarks MUST run only on the pinned box, never concurrently with other workloads, never on battery.
21. Every run set MUST interleave a fixed thermal-canary kernel at least every N measurements (N stated in the results file); drift beyond its own noise floor marks the run contaminated and unpublishable as clean.
22. The confinement suite MUST draw from an external malicious-package corpus with per-case provenance; an in-house-only suite MUST NOT back a confinement claim.
23. No "100%" confinement claim MUST be published before a red-team round has run against that suite.
24. Every confinement claim MUST publish, beside the pass rate, the attack classes the model does not stop.
25. Safety cost MUST be measured against the internal checks-off instrumentation build and reported separately from any competitiveness-vs-C claim; the two MUST NOT be conflated.

## Tier A table

From `bench/kernels/*/spec.toml` (added 2026-09-19, this document's commit):

| Kernel | Category | Bound |
|---|---|---|
| nbody | compute | compute-bound |
| spectral-norm | compute | compute-bound |
| fannkuch | compute | compute-bound |
| mandelbrot | parallel | compute-bound (per-pixel escape) |
| matmul | parallel | compute-bound (naive i-k-j; blocked pending) |
| reduce | parallel | compute-bound (hash chain) |
| stream | parallel | **bandwidth-bound** — spec.toml forbids gating any ≥90% efficiency claim on it |
| binary-trees | alloc | allocation-bound |
| hashmap | alloc | allocation-bound |
| hello | startup | startup |

Additions still to be ported (none pre-registered before this commit):

| Addition | Source | Status |
|---|---|---|
| PolyBench/C subset (gemm, 2mm, jacobi-2d, correlation) | PolyBench/C | not started |
| PRK kernels (stencil, transpose, dgemm) | Parallel Research Kernels | not started |
| Graph kernel (BFS or PageRank) | GAP Benchmark Suite | not started |

Rule 3 applies once any addition lands with its own dated commit; this table is not that commit.

## Tier B table

Five applications, none ported yet, each pending its own pre-registration commit:

| Application | Stresses |
|---|---|
| Parser | allocation churn, branch-heavy control flow, string/byte handling |
| LSM key-value store | write amplification, background compaction concurrency, durable I/O |
| Ray tracer | FP-heavy compute, cache locality, embarrassingly-parallel scaling |
| HTTP server | async I/O throughput, connection-scale concurrency, tail latency |
| Codec (lossless compressor) | bit-level manipulation, table-driven branching, throughput/byte |

## Rejected alternatives

- Lines-per-second for compile speed — discredited V's claims; rule 10.
- Bit-identical checksums as sole correctness gate — conflicts with legitimate reduction-order differences (reviews.md #5); kept separate from the determinism gate.
- Merged P+E-core scaling curve — hides which core class drove the speedup; rule 17.
- Naive-only Rayon/OpenMP baseline — a strawman; rule 8 requires both columns.
- Fixed CoV target as exit criterion — unachievable on an unthrottled M1 Pro; the floor is measured, not targeted (rule 19).
- In-house-only security corpus — provenance-free "100%" claims are indefensible; rule 22.

## Open questions for the owner

1. Tier A additions' exact kernel names/sizes — needs an M0.5 decision before pre-registration.
2. Tier B port order and per-application acceptance thresholds (PLAN.md gates Tier B only at M7).
3. Thermal-canary `N` and its drift threshold — M0.P names the mechanism, not the constant.
4. Roofline: bandwidth calibration is implied by `stream`; the FLOP-rate calibration kernel is unspecified.
5. Whether `matmul`'s blocked variant (PLAN.md §2, absent from `bench/kernels/`) is a Tier A addition or non-gating.

## Audit checklist

- [ ] Results JSON names a source commit matching that commit's `spec.toml`.
- [ ] Kernel is in the frozen Tier A/B table, addition date at or before the result.
- [ ] Baseline flags visible in `bench/langs/*.toml`, `c` and `c-fma` both present where contraction matters.
- [ ] Parallel claim's bound classification matches speedup/cores vs. roofline-fraction usage.
- [ ] P-core and P+E-core points on separate curves with a stated capacity denominator.
- [ ] Compile-speed claim names its cold variant; comparator uses the same one.
- [ ] Incremental claim is p50/p95 over the full edit-class mix, `--no-daemon` row beside the daemon row.
- [ ] Claimed difference exceeds the published noise floor.
- [ ] Thermal canary was interleaved, drift trace referenced.
- [ ] Security "100%" claim: external provenance, red-team done, not-stopped classes published.
- [ ] Safety cost reported against the checks-off build, separate from any vs-C number.
- [ ] Cross-language comparison restricted to equally-covered languages (rule 9).
