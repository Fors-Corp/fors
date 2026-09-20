# Fors benchmark harness

The referee for every performance claim Fors will ever make. It exists before the language does:
baseline languages are measured now, and Fors joins kernel by kernel as its compiler matures.
Stdlib-only Python 3.11+; no dependencies.

```bash
python3 bench/harness/run.py check                  # build + verify every kernel/language (small inputs, fast)
python3 bench/harness/run.py bench                  # verified timed runs -> bench/results/<stamp>-<host>.json
python3 bench/harness/run.py bench --kernel nbody --lang c --lang rust
python3 bench/harness/report.py                     # markdown scoreboard from the newest results file
```

## What is measured

Per kernel x language (x thread count for parallel kernels): clean build wall time, run wall time
(min / median / p95 / stdev), user + sys CPU, peak RSS (from the kernel's own `wait4` rusage accounting),
binary size. The `hello` kernel isolates process startup. One untimed warmup run precedes the timed runs.
Runs repeat at least 3x and until 20 s are spent per cell (max 10); a cell slower than 60 s runs once.

## Rules that keep the numbers defensible

- **Correctness gate.** Every timed run's stdout must equal `kernels/<k>/expected/bench.txt`, blessed from the
  kernel's reference implementation. A wrong answer never gets a time.
- **Same algorithm** in every language; the spec in `kernels/<k>/spec.toml` says which one.
- **Standard library only.** No rayon, NumPy, OpenMP. (A separate best-of-ecosystem track can come later.)
- **Strict IEEE-754.** No fast-math and no FMA contraction in any language (C builds with `-ffp-contract=off`;
  Go needs explicit `float64(x*y)` conversions where it would fuse), so outputs match bit for bit.
- **Safe, portable code.** No SIMD intrinsics, inline assembly, `unsafe`/unchecked indexing or `-Ounchecked`.
- **Thread-count independence.** A parallel kernel must print the same output for any thread count.
- **Flags are data.** Each language's exact build/run commands live in `langs/<lang>.toml` and are copied into
  every results file together with toolchain versions and host details.
- **No claim without a results file.** Publish the JSON with the number.

## Known caveats (say them out loud)

- Apple Silicon has performance and efficiency cores and macOS cannot pin threads: scaling numbers past the
  performance-core count include the slower cores. Do not benchmark on battery (the runner warns).
- `go build` reuses its global build cache, so Go build times are warm-cache times.
- The Java baseline is only as good as the JDK on `PATH`; use a current LTS without changing your default:
  `PATH="$HOME/.sdkman/candidates/java/25.0.4-tem/bin:$PATH" python3 bench/harness/run.py bench`.
- `c-fma` is the same C source built with clang's default FMA contraction, published next to the strict `c`
  column so the baseline is never handicapped; Fors itself is strict IEEE by default.
- Zig (0.16) has ports of every kernel except `stream`. On `matmul` (2.1x) and `reduce` (1.6x) it is slower than
  C with clean, idiomatic sources: a measured toolchain difference, not an implementation handicap.

## Adding a language (this is how Fors joins)

1. `langs/fors.toml`: `name`, `display`, `source`, `probe`, optional `build`, `run`, optional `artifact`.
   `{src}` is the kernel's source directory for the language, `{out}` a clean build directory.
2. `kernels/<k>/fors/main.fors` for each kernel you are ready to compete on.
3. `run.py check --lang fors`.

## Adding a kernel

`kernels/<k>/spec.toml` (`name`, `category`, `description`, `reference`, `[sizes] check/bench` argument lists,
optional `threads = [1, 2, 4, 6, 8]`, optional `exclude = ["lang"]`), the reference implementation, then
`run.py bless --kernel <k>` and `run.py check --kernel <k>`. Size `bench` so the C version runs about 1 s.
A parallel kernel receives the thread count as its last argument. A parallel kernel should also declare
`bound = "compute" | "bandwidth"` and `deterministic = true|false` (see "Parallel family (M0.P)" below).
TOML trap: `threads`, `exclude`, `bound` and `deterministic` must all appear BEFORE the `[sizes]` header,
or they silently become keys of `sizes`.

Ratios are always computed against the C cell measured in the SAME results file, because machine conditions
differ between sessions: include `--lang c` in every partial run (a file without C falls back to the newest C).
`report.py a.json b.json` merges results files (later wins per cell): run the slow languages separately
(`bench --lang python --timeout 3600`), or lay a `--lang fors` run over a full baseline.

## Parallel family (M0.P)

The measurement tooling that makes the parallel kernels' numbers defensible, per `docs/spec/06-measurement.md`
("ch06"), which is the normative owner of the rules cited by number below (R15-R21) and of the Tier A `bound`
table. This section is descriptive, not normative: ch06 wins on any conflict.

### Roofline calibration (`bench/calibrate/`)

`bandwidth.c` and `flops.c` measure THIS machine's achievable peaks (never vendor spec sheets - ch06's
"Roofline" definition): a STREAM-triad-style bandwidth kernel and a multi-accumulator FMA-chain peak-FLOP-rate
kernel, both pthreads, both timed with `CLOCK_MONOTONIC` around only their own kernel loop (allocation and
first-touch excluded), both printing a checksum so the compiler cannot dead-code-eliminate them, both taking
size and thread count as CLI arguments so they can run at smoke-test-tiny sizes or real-calibration-huge ones.
Unlike `bench/langs/c.toml`, they do NOT pass `-ffp-contract=off`: this tool measures the hardware's raw
capability, and FMA fusion is part of that capability, not a fairness violation.

**FLOP-kernel choice (ch06 open question 4).** A multi-accumulator recurrence (`x = x*a + b`, `CHAINS`
independent chains) was chosen over a blocked dgemm micro-kernel: a dgemm micro-kernel is compute-bound only
if its tile size is tuned to this machine's register file and L1 size, and a wrong tile silently measures
bandwidth instead - exactly the failure mode a roofline calibration cannot have. The recurrence's arithmetic
intensity is unbounded in the iteration count (O(1) memory traffic, O(n) work), so it is compute-bound by
construction, and its FLOP count (2 per chain per iteration) is exact and audit-trivial regardless of
instruction fusion.

**`CHAINS` is swept, never assumed.** Each chain is a serial `acc = acc*mul + add` dependency, so the loop
reaches the FPU's issue-rate peak only once the number of INDEPENDENT chains in flight is at least
(FP issue width) x (FMA latency). Below that the kernel measures FMA *latency* and prints it as the machine's
"peak FLOP rate" - which would make every later fraction-of-roofline look several times better than it is.
The compiler also fuses pairs of chains into one 2-wide `FMLA` on arm64, so the independent-chain count in
the emitted loop is `CHAINS/2`, not `CHAINS`; and too many chains spill the 32 vector registers and the rate
falls again. The saturating value is therefore micro-architecture- AND compiler-specific, so `CHAINS` is a
`-DCHAINS=` compile-time knob and `calibrate.py` builds several variants, measures each at one thread, and
takes the best rate as the peak (`choose_chains()`; the whole sweep table is written into
`machine-<host>.json` under `params.flops_chains_sweep`, so the choice is auditable and re-derivable).
Default sweep `8,16,32,64`; `--chains` overrides it.

**Timed region.** Both kernels allocate and first-touch outside the timed region, then meet at a spin start
barrier (`cal_barrier` in `calibrate/common.h`; macOS has no `pthread_barrier_t`) before any thread reads the
clock. Without the barrier a thread that finished first-touch early times itself while its siblings are still
page-faulting, and the reported span - `max(end) - min(start)` across threads - covers a stretch in which the
machine was not actually running `T` threads, understating the aggregate rate. Per-thread scratch structs are
padded to a 128-byte Apple-silicon cache line so no two threads' accumulators or timestamps share one.

**Timer resolution.** `CLOCK_MONOTONIC` returns roughly microsecond-granular values here, so `calibrate.py`
flags any cell whose timed region ran for less than `MIN_TRUSTWORTHY_WALL_S` (1 ms) with
`below_timer_resolution: true` and, outside `--smoke`, warns: at that scale the printed rate is clock
quantisation, not throughput. The smoke sizes are deliberately below it - which is one of several reasons a
`--smoke` file is never a publishable calibration.

`calibrate.py` (stdlib only, reuses `harness/run.py`'s `measure`/`host_info`/`git_commit` the same way
`compile-speed/` does) runs both kernels across the declared thread counts under performance QoS (the
default) and background QoS (`taskpolicy -b`), best-of-`k` per cell, and writes
`bench/results/machine-<host>.json`: bandwidth/FLOP peaks per (core class, T), the machine balance point
(FLOP/s ÷ byte/s), toolchain/OS versions, commit, and `"contaminated"`.

```bash
python3 bench/calibrate/calibrate.py --smoke     # tiny sizes, <2s, writes results/smoke/, contaminated=true
python3 bench/calibrate/calibrate.py             # the real run - see "Real calibration run" below
```

### QoS method and its limits

macOS gives no API to pin a thread to a specific physical core. The only lever is Quality of Service: a
process launched under `taskpolicy -b` is scheduled background QoS, which macOS steers towards the
efficiency cores; default/user-interactive QoS prefers the performance cores. `calibrate.py` verifies this
lever is REAL on the current OS/machine rather than assuming it (`capacity_model()`'s `taskpolicy_effective`
flag): it compares single-thread throughput under both QoS classes against the measured noise floor at that
same thread count, and if the difference isn't distinguishable from noise it prints a loud warning and marks
the derived E-core weight untrustworthy instead of silently publishing a weight of 1.0. On this machine (Darwin 25.6, M1 Pro) `taskpolicy -b` was confirmed to change throughput in the expected
direction, by a large factor, for both the single-threaded and the 8-threaded FLOP kernel - i.e. the lever is
real here and does reach threads the child creates after launch. No NUMBER from that check is quoted
anywhere, because every observation so far was taken on a machine that was busy with other work
(ch06 rule 20); the magnitude is whatever the real calibration run on a quiet box measures, and it MUST be
re-checked after any macOS upgrade or on any other machine, not assumed to transfer.

**P-vs-E capacity model.** `e_weight = background_QoS_throughput(T=1) / performance_QoS_throughput(T=1)` on
the FLOP kernel, and `capacity(T) = min(T, p_cores)*1.0 + max(0, T - p_cores)*e_weight` - the first `p_cores`
threads are modelled as running at full (P-core) weight, any beyond that at the E-core weight. This is a
simple two-class model, not a scheduler simulation: it assumes macOS actually fills the performance cores
before spilling to efficiency ones under default QoS, which is the documented (not independently verified
here beyond the T=1 check above) behaviour.

### Kernel classification (`bound`, `deterministic`)

Every parallel kernel's `spec.toml` declares `bound = "compute" | "bandwidth"`, matching ch06's frozen Tier A
table exactly (mandelbrot, matmul and reduce are compute-bound; stream is bandwidth-bound), plus a rationale
comment. `matmul`'s comment in particular works out the naive i-k-j loop's arithmetic intensity at N=1800
(≈0.25 FLOP/byte in the worst case - deep in the bandwidth-bound regime by the roofline model) as a caveat on
the frozen "compute-bound" label, without overriding it (ch06 rule 3: kernels are added, never re-tuned).

Every parallel kernel also declares `deterministic = true`: checked, not assumed, by reading each language's
source for how per-thread partial results are combined (bench/kernels/<k>/<lang>/main.*). All four kernels
follow the same pattern in every implemented language (c, rust, go, swift, zig, js, python where present):
each thread writes into an INDEX-addressed slot (never an append/race), and the final reduction is a single
serial pass after `join()`, in a fixed order that doesn't depend on how many threads did the work. Combined
with every value being an exact integer (or an integer held in a double, per each kernel's own spec), the
result is bit-identical at every thread count by construction, not by luck.

**Output contract.** Every parallel kernel's stdout today is an exact integer (or two, for matmul) - never
quantized. The determinism gate (`run.py determinism`, below) therefore compares that SAME stdout, not a
separate `bits` line. A future kernel whose correctness gate accepts a QUANTIZED/tolerance-based output
(e.g. a checksum rounded to N significant figures) MUST add a `bits` line to its output - the exact bit
pattern of its accumulator(s) - so the stricter byte-identity gate has something non-quantized to compare;
it must not compare the already-tolerant quantized line, which would silently weaken the gate.

### Determinism gate

```bash
python3 bench/harness/run.py determinism [--kernel K] [--lang L]
```

For every parallel kernel marked `deterministic = true`, builds each implemented language and runs it at
EVERY declared thread count (the `check` size), requiring byte-identical stdout across all of them - compared
against each other, not against `expected/check.txt`. The comparison is over the RAW BYTES of each run's
stdout (`stdout_bytes()`), not the decoded, `.strip()`ed text the correctness path uses: decoding with
`errors="replace"` and stripping would hide exactly the kinds of difference a bit-identity gate exists to
catch. As of the last run of this gate, all 39 implementations of the four parallel kernels (c, c-fma, rust,
go, swift, zig, java, node, deno, python where present) are byte-identical across t = 1, 2, 4, 6, 8 - a
measured result, not a reading of the sources. This is deliberately separate from, and does not
weaken, the existing correctness gate (`check`/`bench`, which only compares two thread counts against the
blessed reference and would accept a legitimately different-but-numerically-equal summation order). The
comparison itself is `run.py`'s `compare_outputs()`, unit-tested in isolation in `bench/tests/test_m0p.py`.

### Scaling report (`report.py`)

For each parallel kernel, `report.py` prints a **curve** per `(language, QoS class)` series - never per
language. R17 is enforced at the SERIES IDENTITY (`series_label()`), not only in the scaling grouping: the
core class is part of the cell-merge key in `load()`, of the vs-C baseline lookup, of the per-kernel table
row, of the scaling group, and of the aggregate score. (Grouping alone was not enough. `load()` merges cells
by key, and while that key was `(kernel, lang, threads)` a background-QoS cell silently REPLACED the
performance-QoS cell with the same thread count - the performance curve disappeared from the report entirely
before any grouping ran. `bench/tests/test_m0p.py::ResultsMergeCoreClassTests` is the regression test.)
`run.py bench` stamps every cell it writes with `"qos": "performance"`, so a cell can never be mistaken for
one taken under another core class.

- **compute-bound**: speedup over the same language's own 1-thread time, AND capacity-normalised efficiency
  = `speedup / capacity(T)`, with `capacity(T)`'s formula printed literally every time (R18 - the denominator
  is always named, never left implicit). Efficiency is only computed when `bench/results/machine-<host>.json`
  exists AND its `taskpolicy_effective` is true; otherwise the report says why not, rather than dividing by
  an unverified or default capacity.
- **bandwidth-bound**: fraction of measured roofline (achieved GB/s ÷ the calibration's bandwidth peak at
  that SAME thread count) - a curve, never a single ratio (R16), and never folded into the aggregate
  `score()` "scaling" axis (R15: parallel efficiency only gates compute-bound kernels - see the `if bound ==
  "compute"` guard around the one place that axis is populated).
- With no `machine-<host>.json` at all, the report prints "roofline not calibrated" and refuses to print
  any roofline fraction, for either kernel class.

Achieved throughput for a bandwidth-bound kernel needs a kernel-specific byte-accounting formula (its memory
traffic shape isn't generic); today only `stream`'s is registered (`BANDWIDTH_THROUGHPUT` in `report.py`,
reusing the exact STREAM-triad formula `bandwidth.c` uses). A future bandwidth-bound kernel gets no fraction
printed until its own formula is added there - a deliberate refusal to guess, not an oversight.

### Noise floor and canary (R19, R21)

```bash
python3 bench/harness/run.py noise [--kernel K] [--lang L] [--reps N]   # writes results/noise-floor.json
```

Measures the coefficient of variation (stdev/mean) of the thermal canary and of one representative
kernel/lang cell over `--reps` repetitions, right now, on this box - the noise floor ch06 rule 19 requires be
measured (never targeted) before any comparison uses it.

`run.py bench` uses the same idea live: before touching any kernel, it runs the canary
(`CANARY_CALIBRATION_REPS` = **5** reps, proposed) to get THIS run's own baseline median and CoV, then
interleaves one canary sample at least every `CANARY_INTERVAL_CELLS` = **5** timed cells (proposed N for
rule 21) through the run. The drift threshold is defined RELATIVE to that measured baseline, not a magic
constant (`canary_drift_threshold()`): `max(3.0 * measured_cov, 0.02)` - a 3x multiplier on the measured
noise (roughly a 3-sigma-style margin assuming near-normal timing jitter, chosen to keep false positives
rare) floored at 2% (so a suspiciously quiet calibration burst can't flag ordinary jitter as contamination).
Any interleaved sample drifting beyond that threshold from the baseline marks the whole results file
`"contaminated": true` (`canary_contaminated()`). **N = 5 and the 3x/2% threshold are this project's proposal
for ch06 open question 3; the owner confirms or overrides both.**

`report.py` prints this decision directly when a results file has it (`canary_baseline`/`canary_threshold`/
`contaminated`), falling back to its older fixed-percentage heuristic only for results files predating this
mechanism.

### Tests

```bash
python3 -m unittest discover -s bench/tests
```

`bench/tests/test_m0p.py` (stdlib `unittest`) covers: the capacity and roofline arithmetic on synthetic
numbers; the determinism comparer (identical and diverging outputs); manifest parsing of `bound` and
`deterministic` (including the TOML-leaking-into-`[sizes]` trap); `report.py`'s refusal to merge QoS/core
classes and its roofline-not-calibrated refusal; and a smoke test that builds both calibration kernels at
tiny sizes and checks their checksums are stable across thread counts (`bandwidth`'s checksum is IDENTICAL
at every thread count - disjoint blocks, exact integer sums; `flops`'s checksum scales EXACTLY with thread
count - every thread runs an identical independent recurrence). **The smoke-build test needs a C compiler
and is therefore NOT added to CI** (ch06 rule 20 also forbids timing anything in CI, which none of these
tests do - they're pure arithmetic over synthetic numbers, except that one build); every other test in this
file needs no compiler and could be added to the existing CI test job.

### Real calibration run (quiet, pinned machine only)

Never concurrently with other workloads, never on battery (rule 20). Exact sequence:

```bash
# 0. Preconditions: on AC power, no other workload (no editors/compilers/agents/sync clients),
#    Wi-Fi/Bluetooth idle, lid open, and at least ~10 GB of free RAM - the bandwidth kernel's default
#    sizes allocate 3 x 1.6 GB, and swapping would be measured as "bandwidth".
python3 -m unittest discover -s bench/tests                           # tooling gate first (needs clang)
python3 bench/harness/run.py determinism                              # correctness gate before timing anything

# 1. Roofline + P-vs-E capacity. Sweeps CHAINS, both QoS classes, best-of-7.
#    Expect tens of minutes: the background-QoS sweep crowds up to 8 threads onto 2 efficiency cores
#    and is ~10x slower per cell than the performance-QoS one. Do NOT shorten --timeout to "fail fast":
#    a short timeout leaves silent holes in the sweep rather than an error.
python3 bench/calibrate/calibrate.py                                  # writes results/machine-<host>.json
#    Check before continuing: "contaminated": false, capacity_model.taskpolicy_effective == true,
#    roofline.cells_below_timer_resolution == [], and params.flops_chains_sweep peaking at an interior
#    value (if the best rate is at the LAST chain count tried, re-run with --chains including larger ones).

# 2. Noise floor per metric (rule 19), published before any comparison uses it.
python3 bench/harness/run.py noise --reps 20                          # writes results/noise-floor.json

# 3. The timed run: canary-calibrated, canary-interleaved, contamination-checked.
python3 bench/harness/run.py bench                                    # exit code is non-zero if contaminated

# 4. Scaling curves + roofline fractions.
python3 bench/harness/report.py                                       # or: report.py results/<stamp>-<host>.json
```

If `report.py` prints "roofline not calibrated", or any `machine-<host>.json`/results file says
`"contaminated": true`, or a difference you want to quote is smaller than the noise floor from step 2, the
number is not publishable (ch06 rules 19, 20, 21): re-calibrate or re-run before publishing anything from it.
Anything under `results/smoke/` is a tooling smoke test taken on a busy machine, carries
`"contaminated": true`, and is never an input to a published number.

## Compile-speed track

A separate track under `compile-speed/` measures **compiler speed**, not the runtime programs above.
It builds a pinned, generated corpus of synthetic programs and times the compiler (wall-clock, with
linking included) on each one -- never lines-per-second claims, since generated lines are not
representative of hand-written code.

```bash
python3 bench/compile-speed/compile_speed.py                        # F = 1000, 10000
python3 bench/compile-speed/compile_speed.py --sizes 100000 --allow-100000   # some compilers take minutes
```

It reuses this harness (`load_langs`, `toolchain_version`, `measure`, `expand`, `host_info` from
`harness/run.py`) instead of duplicating it. For a language and a function count `F` it generates one
source file with `F` small, distinct, non-trivially-dedupable functions (per-function constants drawn
from a seeded MINSTD stream, recorded per run so every measurement is a cold compile even though `go
build` otherwise caches by content) plus a driver that threads an accumulator through all of them, calls
grouped into ~100-call helper functions. Only the five compiled languages are measured here -- **c, rust,
go, swift, java**; node and python have no build step and are skipped in this track (their startup/runtime
cost is covered by the `hello` kernel instead). Results land in `results/compile/<stamp>-<host>.json`
(schema 1), not in `results/`, so `report.py`'s "newest results file" logic never picks one up by mistake.

**Methodology caveats:**
- One huge single-file source is a worst case for some compilers (notably whole-module/whole-program
  optimizers); a multi-file/multi-module corpus, closer to real project structure, is future work.
- Go's build measurement is still a *warm standard-library* cache -- only the generated user code is
  guaranteed cold (via the per-run random seed changing its content).
- Java's method/class layout (about 1000 functions per top-level class, about 300 block-helpers per
  class) exists only to stay under the JVM's 64 KB method and 65535-entry constant-pool limits at large
  `F`; it is not idiomatic Java and should not be read as one.

## Incremental rebuild comparator

`compile-speed/incremental.py` is the multi-file companion to `compile_speed.py` above: instead of one
huge source file, it generates a *project* -- `--modules` modules (default 200) of `--functions`
functions each (default 50), identical shape in every language -- and measures each ecosystem's normal
edit-run loop: a cold build, an immediate no-op rebuild, then `--reps` repetitions (default 10) of five
edit classes, each rebuilt, run and checksum-verified:

```bash
python3 bench/compile-speed/incremental.py --modules 40 --functions 20 --reps 3   # smoke test
python3 bench/compile-speed/incremental.py                                        # default M=200 F=50
```

**Project shape.** Module 0 ("core") is imported, via a fixed `module_index % K` pub-slot assignment,
by every other module; module `i` also imports two lower-numbered modules chosen from a seeded MINSTD
stream (recorded per run). Module `M-1` is a guaranteed leaf (nothing has a higher index to import it).
Each module has `F` small integer-arithmetic private functions (same generator family as
`compile_speed.py`, values kept under 2^31) grouped into `K = min(reps, F)` public functions; `main`
calls every module's public functions in order and prints a checksum that a pure-Python reference
(`simulate()`, mirroring the exact call graph) also computes, so every rebuilt binary is executed and
its output checked -- a stale-cache bug that reuses an old binary is a hard failure, not a slow pass.

**Edit classes**, each a source mutation to the leaf module (or, for E5, the core module) that keeps
the program valid and changes its expected checksum (except E1, whose whole point is that it must
NOT change the checksum): **E1** comment-only, **E2** a private function's constant, **E3** a private
function's signature (adds a parameter, updates its one in-module caller), **E4** a leaf module's
public function's signature (updates main's single call site), **E5** a core module's public
function's signature (updates every module that calls that pub slot -- the "every caller" case).

**Build drivers**, each that ecosystem's normal dev/debug workflow: C = generated Makefile with
`-MMD -MP`, `make -j8`, clang `-O0`; Rust = `cargo build` (dev profile, incremental on) plus a second
`cargo check` row (build-timing only -- `check` has no artifact to run, so its correctness is covered
by the paired `build` row over the same edits); Go = `go build -o prog .` (compiles the whole package
graph since `main` imports every module); Zig 0.16 = `zig build-exe`, `-fincremental` tried and
reported on rather than assumed; Java = plain `javac` of the whole tree (no incremental mode --
labelled as the honest full-rebuild comparator, not a bug).

**Methodology notes and decisions:**
- The "cold" variant is *stdlib-prebuilt-project-cold*: the project's own build cache is wiped (`.o`/
  `.d`/binary for C, `target/` for Rust, Zig's `--cache-dir`/`--global-cache-dir`, `out/` for Java)
  but the toolchain's standard-library cache is left warm. Go is the one exception: its build cache is
  content-addressed, so wiping it would force a cold *stdlib* rebuild too (the *everything-from-source*
  variant, not this one); each run's freshly-seeded source is already a guaranteed cache miss on its
  own, which is the same approach `compile_speed.py` and this README already document for Go.
- Edit classes run sequentially and **cumulatively** on top of one warm build (E1's reps, then E2's,
  etc., without resetting the source to pristine between classes). This trades strict per-class
  isolation for not paying an extra untimed resync rebuild between every class; each class still
  targets its own distinct function(s) so the classes don't overwrite each other's edits.
- macOS's `make` (GNU Make 3.81) compares file modification times at whole-second resolution; the tool
  waits to cross a one-second boundary before writing each edit, or a same-second edit is invisible to
  `make` and it silently reuses the stale binary (this is exactly the kind of stale-cache bug the
  checksum verification exists to catch, so it must not be allowed to hide behind measurement noise).
- Zig identifiers are generated as `fx{i}`, not `f{i}`: at `i` = 16/32/64/128 a plain `f16`/`f32`/...
  would shadow Zig's built-in float-type primitives, which zig 0.16 rejects as a hard error.

Results land in `results/compile/incremental-<stamp>-<host>.json` (schema 1), next to but distinct
from `compile_speed.py`'s files.
