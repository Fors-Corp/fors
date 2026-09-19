# Fors — a new systems/HPC programming language (plan)

> Status: v1 of the plan, 2026-09-19. Synthesized from a 5-survey research pass, a 5-architect design panel and 3 adversarial reviews (all in `docs/`). Living document: re-baseline at every milestone exit.

## 1. Context

Marc wants to create a new programming language from scratch, **Fors** (nickname "F"; source extension **`.fors`**, CLI **`fors`** — `.f`/`.for` rejected because they are Fortran/Forth and every editor, GitHub Linguist and build tool would misdetect them).

Headline goals, as stated: (1) most efficient language in existence, (2) security built in, (3) faster compiler than any current language, (4) fastest compute-parallelization of any language. Plus: a **benchmark harness** comparing Fors against C, Java, JS, Python, Rust and others.

Decisions already made by Marc (2026-09-19):
- **First domain to win:** systems + HPC compute (C/C++/Rust/Fortran territory; no GC; full layout control).
- **Parallel targets (all first-class, staged):** multicore CPU + SIMD → GPU single-source kernels → distributed clusters → AI accelerators/NPUs.
- **Security scope (all non-negotiable):** memory safety + data-race freedom; capability-based authority (no ambient I/O); supply-chain hardening; verification (contracts) + side-channel (`secret`) types.

- **v1 scope = everything** (all four hardware classes + all four security layers). This defines what the *1.0 label* means; work is still ordered into internal milestones with risk gates (section 5). Gates re-sequence, they never drop mandated scope.
- **No LLVM, ever** (hence no MLIR): own fast dev backend, own optimizing release backend, own multi-level IR, own GPU emitters (MSL / SPIR-V / PTX text-or-binary formats that need no LLVM).
- **Bootstrap compiler in Rust** (disposable; self-host only after semantics freeze).
- **Resources:** solo + AI coding agents, multi-year. Research-calibrated expectation: credible v0.1 (CPU-only, safe, fast-building) in ~12–18 months; the full "everything" 1.0 is a 4–6+ year program. Research flagged full-scope-at-once as the top project risk — accepted by owner; mitigated by milestone gates and by making every milestone independently useful and benchmarked.

Dev machine (verified): Apple M1 Pro, 6P+2E cores, 16 GB, arm64, macOS. Installed: clang 21, rustc 1.98.1, go 1.27.1, node 24.15, deno, python 3.14.5, swiftc, java **11** (stale). Missing: zig, hyperfine, cmake/ninja, pypy, julia. The working directory `/Users/marcfors/Programming Language` contains only a `graft/` index and is not yet a git repo.

### Honest framing of the superlatives
"Best in existence" is not a testable statement; the plan converts each goal into **falsifiable targets on named benchmarks** (section 3) and the harness (Milestone 0) is the referee. The goals also collide (e.g. optimizing backends are slow; monomorphization is fast at runtime and slow at compile time; safety checks cost cycles). The architecture in section 4 exists to resolve those collisions rather than pretend they are absent.

### Governing design rule
**Anything that cannot be retrofitted is designed on day one; everything else is staged.**
- Day one (type-system / stdlib / IR shape): ownership + aliasing model, data-race freedom, capability-passing stdlib (no ambient authority), sandboxed compile-time execution, reserved contract + `secret` syntax, a multi-level IR that keeps parallel structure explicit.
- Staged (additive): GPU/cluster/NPU backends, optimizing release backend, package registry, contract prover, self-hosting.

## 2. Milestone 0 — Benchmark harness (built BEFORE Fors exists)

Purpose: freeze the scoreboard first. Baseline languages are measured now; Fors joins kernel-by-kernel as the compiler matures. Every later performance claim is a harness run, reproducible from a commit.

Layout (new repo rooted at the working directory):
```
bench/
  harness/run.py            # stdlib-only Python runner (no deps): build, verify, time, record
  harness/report.py         # results JSON -> markdown scoreboard (+ static HTML chart later)
  langs/<lang>.toml         # per-language manifest: toolchain probe, build cmd, run cmd, flags, version cmd
  kernels/<kernel>/spec.md  # algorithm, input sizes, expected checksum
  kernels/<kernel>/<lang>/  # one implementation per language (same algorithm, idiomatic-optimized)
  compile-speed/gen.py      # synthetic program generator: N-LOC equivalent programs per language
  results/<date>-<host>.json
```
Measurement (per kernel × language): clean **compile time**; **wall time** (warmup + N runs → min/median/p95, stddev); user+sys CPU and **peak RSS** via `os.wait4` rusage (no external tools needed); **binary size**; **startup time** (hello world); **parallel scaling** at 1/2/4/6/8 threads → speedup + efficiency; optional **energy** via `powermetrics` (needs sudo → opt-in flag). `hyperfine` is optional cross-check, not a dependency.

Rules that make results defensible:
- **Correctness gate:** an implementation's output checksum must match `spec.md` before its timing counts.
- **Fairness policy (documented in `bench/README.md`):** same algorithm per kernel; max-optimization flags per language recorded in the manifest (`-O3 -mcpu=native`, `-C target-cpu=native` + LTO, JVM with in-process warmup iterations, etc.); toolchain versions + machine metadata captured in every results file; runs refused on battery/thermal throttle where detectable.
- **M1 noise control:** macOS cannot pin cores; run at user-interactive QoS, report P-core count separately from E-cores in scaling plots, use ≥1 s kernels and ≥10 runs.

Kernel suite v1:
- *Single-thread compute:* nbody, spectral-norm, mandelbrot, fannkuch-redux, matmul (naive + blocked).
- *Allocation / data structures:* binary-trees, k-nucleotide (hash map + strings), JSON-ish parse.
- *Parallel:* parallel mandelbrot, parallel matmul, parallel reduce/prefix-sum, parallel sort, 2D stencil (PRK-style).
- *Compile speed:* synthetic 10k / 100k / 1M-LOC programs + real kernel build times → **lines/sec**, clean and incremental.
- *Security conformance (pass/fail, not timed; starts when Fors compiles):* Juliet-style memory-unsafety cases must be rejected at compile time or trap deterministically; capability tests (a dependency without a `Net` capability cannot open a socket).

Baselines: C (clang), Rust, Go, Swift, Java (**install current LTS JDK**, 11 is unfair), JS (node + deno), Python (CPython 3.14; NumPy track reported separately), Zig (**install**). Later for the parallel tier: Julia, Chapel, Mojo, ISPC where installable.

**Your contribution point (learning mode):** the scoreboard's aggregate score — how kernels are weighted into one number (geometric mean of ratios vs C? separate runtime / memory / compile-speed / scaling axes?) is a judgment call that defines what "winning" means. `harness/report.py` will be scaffolded with a `score()` stub for Marc to write (~10 lines).

## 3. Measurable targets (the superlatives, made falsifiable)

Hard rule: **no comparative claim leaves the repo before the harness run that produces it is public and reproducible by a stranger** (±5%). Compile speed is always wall-clock on a pinned corpus with link included — never LoC/sec (the metric that wrecked V's credibility).

| Goal | Metric & benchmark | Baseline to beat | Honest expectation |
|---|---|---|---|
| G3 fastest compiler | cold / warm / single-token-edit incremental (p50, p95) on: synthetic 100k-line/1000-module corpus + the Fors compiler itself | Go `gc`, Zig self-hosted debug backend | **Winnable outright.** Targets: p95 incremental < 50 ms at 100k lines; cold debug build ≥ 3× faster than Go |
| G2 security | (a) Juliet CWE subsets + Magma → deterministic trap or compile error; (b) adversarial ~50-package suite trying fs/net/exec at build + run time → 100% confined; (c) bit-identical rebuilds on 3 hosts; (d) safety overhead geomean | C+ASan/UBSan; Rust+cargo-vet/deny (cannot stop `build.rs`) | **Largely winnable.** (b) is unoccupied territory and the most differentiated claim. Overhead target ≤ 2–3% |
| G1 runtime efficiency | geomean wall-clock, ≥10 runs, median+p95: harness kernels → PolyBench/C, LLVM test-suite subsets, real apps | best-of(clang -O3, gcc -O3, rustc -O) with expert-reviewed implementations | Parity, not supremacy: within 5% geomean long-term, 1.3–4× wins on layout/vectorization-sensitive kernels. **Harder without LLVM** — the own optimizing backend is the project's largest technical bet |
| G4 parallelism | parallel efficiency (speedup/cores), absolute kernel time, portability-per-effort: PRK, NAS-class, graph workload | OpenMP, Rayon, OpenCilk, Kokkos (CPU); vendor libs (GPU) | CPU: ≥ 90% efficiency on regular kernels and ≥ Rayon — achievable. GPU: expect 60–100% of vendor-tuned peak; claim portability + safety, not peak |

## 4. Language + compiler architecture

Full subsystem designs live in the repo: `docs/design/{compiler-architecture,safety-security,parallel-heterogeneous,surface-language,roadmap-execution}.md`; the three adversarial reviews in `docs/design/reviews.md`; research in `docs/research/sota-survey.md`. This section is the **authoritative synthesis**: where a design doc disagrees with it, this wins.

### 4.1 Agreed architecture (all five designs converge)
- **Pipeline (Rust bootstrap, zero LLVM):** SoA tokens → SoA AST → **FIR** (typed semantic IR = the binary module interface, no textual include) → **FMIR** (checked mid IR: ownership, isolation, contracts, `spawn/sync`, `tile.*`, `secret`) → **OIR** (CFG-SSA, mandatory alias-class operands, Tapir `detach/reattach/sync`) → **LIR** → Mach-O/ELF atoms.
- **Compile speed is architecture, not backend:** per-declaration BLAKE3 content-hash query DAG (signature and body hashed separately → early cutoff), mandatory acyclic module graph, imports-first, order-independent declarations, resident `fors-driver` daemon that *is* the LSP server (`--no-daemon` for honest benchmarks), parallel frontend from day one.
- **Two backends, one semantics:** copy-and-patch dev tier; release tier = CFG-SSA + Cranelift-style acyclic e-graph, ISLE-style declarative isel (aarch64 first), SSA chordal-graph register allocation, PGO with profiles as content-addressed inputs.
- **One FMIR interpreter, three jobs:** comptime VM, Miri-class reference semantics, differential-testing oracle (interpreter vs dev vs release). The IR-level random program generator lands with the *first* dev-backend instruction.
- **macOS incremental link:** own atom-based Mach-O writer; APFS `clonefile` the previous image, patch dirty pages, rehash only dirty CodeDirectory slots, ad-hoc re-sign, rename. System `ld64` for release until the own linker matures.
- **Memory model:** mutable value semantics, conventions `let / inout / sink / set` with call-site markers (`&x`, `move x`, `&out x`), destructive moves, explicit allocators, no lifetimes, no region inference, no interior mutability in the safe sequential subset.
- **Surface:** braces + keyword-led declarations, grammar parseable with no symbol table; generics in `[...]`; exactly two inference judgments (`synth` / `check`), no solver, no overloading, closed operator-trait set; `soa struct`; trap-on-overflow everywhere with explicit `wrap_/sat_/unchecked_`; no implicit conversions.
- **Parallelism:** one mechanism (structured fork/join) reused for CPU tasks, async I/O (same fibers → no function coloring; `Io` passed explicitly), GPU launches and locale transfers. Continuation-stealing runtime, P/E-core worker classes, explicit SPMD + fixed-width `vector[T,N]` / `mask[N]`. GPU without LLVM: MSL text (Metal, first), SPIR-V binary (Vulkan), PTX text (CUDA driver JIT). Distributed = library over isolation domains + structural serialize + `net` capability. NPU = restricted `@tensor` sub-language exporting CoreML MIL first.
- **Security:** per-module `needs {fs.read, net, ...}` checked over the module graph at build and link; capability *values* where authority narrows; FFI is a capability that taints its subtree; declarative build graph with **no executable build steps**; pure deterministic comptime with declared inputs and step/alloc budgets; minimal-version selection + lockfile pinning each dependency's capability set (a capability gained in an update is a build error until `fors grant`); signed reproducible packages; `@unsafe(invariant: "...")` as a declaration attribute with a published inventory.

### 4.2 Resolutions of cross-design conflicts (decided here; each becomes a normative spec chapter in M0.5)
| # | Conflict | Resolution |
|---|---|---|
| R1 | 3 different reference-capability lattices | **Two sharing qualifiers `iso`, `imm`**; exclusive-mutable and read-only come from `inout`/`let`. `secret` is an orthogonal one-bit taint, never joined with the sharing lattice. One sendability rule. |
| R2 | Graph-shaped data: branded arenas vs "no safe encoding" | **Branded arenas are in the language** (`with arena nodes: Arena[Node] {…}`, `Ref[Node, nodes]`); brand non-escape is a local check; generation check stays on in *all* modes. Allocators branded the same way (`Own[T, A]`) so a safe program cannot free with the wrong allocator. |
| R3 | Escape rule forbids what `split_at`/slices need | One narrow **scoped-return rule**: a function may return a scoped projection derived from exactly one designated parameter. |
| R4 | Failure ABI specified 4 ways | One chapter, one crate (`fors-abi/failure.rs`): keyword `raises`, postfix `?`, status tag in a register outside the C return set, sret above a single classifier threshold. Trap = **whole-process abort** (`brk` + side table), stated prominently; "domain abort" deleted. No unwinder; C++ exception shim is a prebuilt C++ object, optional. Backtraces across fibers via a sentinel frame in the fiber ABI. |
| R5 | Determinism default + reduction-tree shape specified 3–4 ways | **Deterministic by default.** `reduce` is its own primitive whose semantics *are* the declared tree: shape = f(n, B), B a target-independent literal (default 256) — never lanes, grain, threads or locales. Reductions lower to tree form *before* parallel lowering so `--serial-elide` is a bit-exact oracle. A plain accumulator loop is never auto-parallelized. |
| R6 | Shape-based generics vs G1 and vs SPMD | **Flip the default before std is written:** monomorphize when the instantiation shape is scalar/≤16 bytes or the body is under an instruction threshold (content-addressed instantiation cache bounds the cost); witness tables otherwise; `@specialize` compiler-enforced inside `simd/spmd/kernel` regions. |
| R7 | Two check-elimination engines; contracts dropped in release | OIR pass is the only authority that deletes a bounds/overflow check. Contract checks are never removed by optimization level — only by proof or an explicit per-module policy identical in both tiers. Checks-off exists only as an internal, unshippable instrumentation build. |
| R8 | Comptime: one engine or two | One (the FMIR interpreter); tier-up only for bodies with no address observation. |
| R9 | Capability declaration has two sites | Manifest = **policy** (upper bound per target/dependency); module `needs` = **requirement**; build fails unless requirement ⊆ policy. `asm` and `syscall` are capabilities distinct from `unsafe`; because we own the assembler and object writer, emitted code is scanned for syscall-class instructions. Capability manifest is bound into the artifact. |
| R10 | `secret`, tiles, alias sources have no IR home | `secret` bit + `ct_region` are mandatory verified fields FMIR→LIR (plus a spill class); `tile.*` lives in FMIR and the device pipeline forks before OIR; alias classes derive from five sources (conventions, affine ownership, arena brands, split-token provenance, SoA field identity). |
| R11 | Sea-of-nodes (roadmap) vs CFG-SSA (compiler) | CFG-SSA + acyclic e-graph. **Add a restricted autovectorizer + unroll-and-jam to the first release-backend milestone** — without it the C-parity target is unreachable (every third-party suite is plain loops); mandatory alias classes make it cheap. |
| R12 | Scalable vectors in or out | `SVec[T]` syntax and scoping rule (legal only inside `simd/spmd`, never in aggregates/heap/generics) reserved in the spec; implementation gated on SVE/RVV CI hardware. |
| R13 | DWARF churn dirties signed pages | Dev tier keeps debug info in an unsigned companion artifact. |

### 4.3 Owner decisions still open (Marc, during M0.5)
1. **FP contraction default — DECIDED 2026-09-19: strict IEEE, no FMA contraction by default, lexical `@fastmath(contract)` opt-in.** The harness publishes both a strict `c` column and a `c-fma` column (clang's default) so the baseline is never handicapped.
2. **What gates the 1.0 label — DEFERRED 2026-09-19 to the semantics freeze (M7), when backend quality and real velocity are known; the roadmap is identical until then.** The two options: reviewers' "thinnest viable v1" for mandated scope: GPU with hand-written `.fsched` schedules (no auto-tiling), NPU = CoreML MIL export only, distributed = localhost multi-process + one 4-node TCP run gated on checksum identity, SMT prover tier / public registry / automatic C-header importer / scalable vectors shipping in 1.x. Nothing mandated is absent from 1.0; each arrives in its thinnest honest form. Accepting this is the difference between ~7 and ~9.5 years.
3. Syntax calls the surface architect left to Marc: mandatory `;` vs ASI, integer-literal default type, bitwise-operator precedence.
4. Trap = whole-process abort is a genuine disqualifier for some server users; confirm it.

## 5. Roadmap

**Schedule honesty.** The roadmap architect's top-down estimate was 6.5 years to 1.0; summing the subsystem owners' own estimates gives ~70 months uncontingented = **9–9.5 years at the plan's own 1.6× contingency**. With the 4.3(2) thinning, ~7. Public **v0.1 (CPU-only, safe, fast-building, capability-confined) ≈ 2–2.5 years**. No-LLVM costs ~18–24 months on G1 specifically. Re-baseline at every milestone exit.

| # | Milestone | Size | Exit gate (all measured by the harness) |
|---|---|---|---|
| **M0** | Benchmark harness, perf family — **built 2026-09-19** (`bench/`) | 3 wk | All cells pass the checksum gate; noise floor *measured and published* (not targeted); kernel manifest frozen + hashed (pre-registration); baselines include tuned-vs-naive columns |
| M0.P | Parallel family: roofline calibration, capacity table, determinism gate, thermal canary | 3 wk | Scaling reported as curves; P-only and P+E never merged |
| **M0.5** | **Semantics core on paper**: the R1–R13 chapters + 4.3 decisions; Tier A / Tier B kernel sets enumerated | 6–8 wk | No IR op, stdlib signature or verifier rule is written before this exits |
| M1 | Frontend, query engine, FMIR interpreter, spec v0.1, formatter, LSP skeleton. *Parallel 3-week spike:* Mach-O clonefile/patch/re-sign on a toy binary → go/no-go | 4–5 mo | 100k-line corpus checks; type-check cost CI-proven near-linear; single-decl edit invalidates only its dependents |
| M2 | Dev backend aarch64/Mach-O, incremental link + sign, DWARF sidecar, IR fuzzer + differential runner from the first instruction | 4–6 mo | p95 ≤ 50 ms over a *distribution of edit classes* (comment, body, private sig, public sig leaf/core) at 100k lines, with a named comparator row; cold build ≥ 3× Go under all three published "cold" definitions; edit-to-test-result latency reported |
| M3 | Memory model, zero-UB semantics, failure ABI, runtime contracts, race checker | 4–6 mo | Juliet CWE subsets → 100% deterministic trap or compile error; safety cost ≤ 6% (→ ≤ 3%) vs the internal checks-off build |
| M4 | Capabilities, declarative confined build, signed packages → **public v0.1** | 3–4 mo | Confinement suite built from an *external* malicious-package corpus + red-team round **before** any "100%" claim; published list of attack classes the model does not stop; bit-identical rebuild on 2 hosts |
| M5a/b | Own optimizing backend (aarch64) incl. restricted autovectorizer; PGO in 5b | 10–14 mo | 2.0× then 1.6× geomean of best-of(clang, gcc, rustc) on Tier A, weekly published; 3-way differential clean; zero open miscompiles |
| M5.5 | Minimal x86_64/ELF correctness path (fallback for the incremental claim, de-Apple-ifies codegen); one Tier-B application port; own scalar+vector libm | 4–6 mo | Conformance green on Linux; app within stated factor |
| M6 | SPMD/SIMD, work-stealing runtime, deterministic reductions | 5–8 mo | ≥ 90% efficiency on **compute-bound** kernels; fraction-of-roofline on bandwidth-bound ones; ≥ *tuned, published* Rayon/OpenMP baselines; bit-identity across thread counts and two declared widths |
| M7 | Backend v2 → 1.3× → 1.1×; **semantics freeze** (spec 1.0-beta) | 9 mo | Tier B within 15%; 100% spec-clause conformance coverage |
| M8 | x86_64 full, DWARF at -O, debugger, sanitizers | 5 mo | Both architectures published |
| M9 | GPU single-source: Metal/MSL → SPIR-V → PTX | 8–9 mo | Checksum-portable across backends; vs MPS/MLX baselines with launch overhead reported |
| M10 | Distributed (localhost multi-process → 4-node TCP → scaling) | 6–7 mo | Checksum identity across locale counts first; scaling gates second |
| M11 | NPU: CoreML MIL export → StableHLO/ONNX | 5–6 mo | CPU lowering as differential oracle within declared tolerance |
| M12 | SMT prover tier, constant-time verifier hardening, registry, self-hosting → **1.0** | 10 mo | Prover ≥ 80% of std contracts in budget; dudect-style timing tests; registry red-teamed |

**Execution model.** Fuzzing/differential testing in cloud CI (throughput-bound, noise-indifferent); benchmarks only on the pinned M1 box, never concurrently. Agent sizing per Marc's rule — haiku/low: encoding tables, struct definitions, kernel ports, snapshot churn; sonnet/default: one bounded unit with an acceptance test; opus/top + high effort: architecture, root-cause debugging, security review, adversarial verification. Structure before source; read only files being edited; own tests while iterating, full suite once. Licensing: Apache-2.0 (compiler/tools), Apache-2.0 OR MIT (std/runtime), CC-BY-4.0 (spec). BDFL + numbered public RFCs.

**Learning-mode contribution points** (5–10 lines each, Marc writes them): `bench/harness/report.py::score()` (now); then `fors-query::decl_fingerprint()`, `fors-oir::may_alias()`, `fors-abi::classify_aggregate()` and `failure_class()`, `fors-sema::conflicts()` (convention conflict matrix), `fors-pkg::classify_cap_change()`, `fors-link::rehash_dirty_pages()`, `runtime::choose_victim()` and `reduction_block_size()` (a results-visible constant — cannot change after publication), parser `binding_power()`. Full list with trade-offs in each design doc.

**Vocabulary rule.** "Most efficient in existence" and "fastest parallelization of any language" are retired in writing. The honest public position for the first four years: fastest builds, zero-UB safe subset, confined dependencies, competitive-not-leading scalar codegen, best-in-class parallel determinism.

## 6. Verification

- **Harness (M0), now:** `python3 bench/harness/run.py check` (every kernel × language passes the checksum gate) → `run.py bench` → `report.py` renders the scoreboard; `python3 bench/compile-speed/compile_speed.py` for the compiler-speed track.
- **Every later milestone:** its exit gate above is a harness run committed as a results JSON; the three-way differential suite (interpreter / dev / release) green; security conformance suite green; `--check-repro` bit-identical.
- **Plan integrity:** M0.5 exits only when each of the six contested facts (qualifier set, failure ABI, reduction constant, comptime engine, capability site, IR ownership of tiles/secrets/alias sources) has exactly one normative chapter and CI forbids other docs from redefining them.
