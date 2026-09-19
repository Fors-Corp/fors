# Fors

Fors (`.fors`, CLI `fors`) is a systems and HPC programming language under construction: mutable value
semantics with no lifetimes, capability-based authority with no ambient I/O, deterministic-by-default
parallelism, and a from-scratch toolchain with no LLVM. The bootstrap compiler is written in Rust.

Status: pre-alpha. The frontend parses and name-resolves; nothing is code-generated yet.

| Path | What it is |
|---|---|
| `docs/PLAN.md` | The authoritative plan: decisions, architecture, roadmap, measurable targets |
| `docs/spec/` | Normative specification, one owning chapter per fact (`README.md` is the index) |
| `tests/conformance/` | Conformance corpus: `.fors` files with `//! expect:` directives |
| `crates/` | Bootstrap compiler: `fors-lex`, `fors-syntax`, `fors-index`, `fors-resolve`, `fors-cli` |
| `tools/ref/` | Independent reference parser and reduction reference; the Rust parser must agree with it |
| `bench/` | Benchmark harness: the referee for every performance claim (see `bench/README.md`) |
| `spikes/` | Feasibility spikes with GO / NO-GO reports |

```bash
cargo test --workspace
```

```bash
python3 tools/ref/fors_parse.py tests/conformance
```

```bash
cargo run --release -p fors-cli -- check tests/conformance/08-names/enum-variant-path-accepted
```

No performance claim is made anywhere in this repository without a results file that reproduces it.

## Licensing

- Compiler, tools and benchmark harness: Apache-2.0 ([LICENSE](LICENSE)).
- Standard library and runtime, once they exist: Apache-2.0 OR MIT, at your option
  ([LICENSE](LICENSE), [LICENSE-MIT](LICENSE-MIT)).
- The specification in `docs/spec/`: CC-BY-4.0 ([docs/spec/LICENSE](docs/spec/LICENSE)).
