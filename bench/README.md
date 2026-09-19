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
- Zig (0.16) has only the `hello` kernel so far; its stdout API changes between releases.

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
