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
A parallel kernel receives the thread count as its last argument. TOML trap: `threads` and `exclude` must
appear BEFORE the `[sizes]` header, or they silently become keys of `sizes`.

Ratios are always computed against the C cell measured in the SAME results file, because machine conditions
differ between sessions: include `--lang c` in every partial run (a file without C falls back to the newest C).
`report.py a.json b.json` merges results files (later wins per cell): run the slow languages separately
(`bench --lang python --timeout 3600`), or lay a `--lang fors` run over a full baseline.

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
