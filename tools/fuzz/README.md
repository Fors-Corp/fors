# Grammar-based differential fuzzer

A fuzzer for the two independent Fors parsers:

- the Rust parser, `crates/fors-lex` + `crates/fors-syntax`, driven through
  `cargo run --release -p fors-cli -- parse <file>...`;
- the Python reference parser, `tools/ref/fors_parse.py`
  (`fors_parse.check(src)` returns an error string or `None`).

The oracle is **agreement**: both parsers must accept, or both must
reject, the same input. Before this tool existed, that was checked only
over the ~1000 hand-written files in `tests/conformance/` (see
`tools/ref/diff_driver.py` and `crates/fors-syntax/tests/differential.rs`).
This directory generates and mutates programs by the hundred thousand to
check it far more broadly, on inputs no one wrote by hand.

## Files

| File | Job |
|---|---|
| `gen.py` | Generates programs by weighted random expansion of the EBNF in `docs/spec/07-grammar.md`, from a fixed `(seed, count)`. Mostly produces syntactically valid programs (see "Design" below). |
| `mutate.py` | Turns one program into a *near*-valid one: a single token-level or byte-level mutation, chosen from a fixed catalogue (see "Mutation catalogue"). |
| `run.py` | The campaign driver: generates+mutates N cases, gets both parsers' verdicts, and minimises and reports every disagreement. |
| `fuzz_smoke.rs` (`crates/fors-syntax/tests/`) | A small, fixed-seed, in-process CI smoke test built on `gen.py` alone (see "CI smoke test"). |

## Running a campaign

```sh
# Build once (run.py also does this itself unless you pass --skip-build):
cargo build -q --release -p fors-cli

# A few hundred cases, quick sanity check:
python3 tools/fuzz/run.py --seed 1 --count 2000 --report /tmp/report.json

# A real campaign: several independent seeds, >= 200000 cases total.
# --count is PER seed, so this is 4 x 55000 = 220000 cases.
python3 tools/fuzz/run.py \
  --seed 101 --seed 102 --seed 103 --seed 104 \
  --count 55000 \
  --report /tmp/campaign_report.json
```

Useful flags (all optional):

- `--max-depth N` (default 3): the generator's recursion bound. Bigger
  means larger, more deeply-nested programs; the default keeps the median
  generated program under 1KB so a 200000-case campaign finishes in a few
  minutes even though `cargo test`'s own build is competing for the
  machine.
- `--mutate-fraction F` (default 0.55): the fraction of cases that get one
  (occasionally two) mutations applied on top of a freshly generated
  program, instead of being used as-is.
- `--batch-size N` (default 300): how many files go into one
  `fors parse` invocation. Bigger batches amortise process-startup cost;
  smaller ones narrow a hang down faster.
- `--batch-timeout SECONDS` (default 20): a batch that does not finish in
  time is re-run one file at a time (3s each) to find exactly which file
  hangs.
- `--skip-superlinear`: skip the nesting-depth CPU-time check (see below);
  useful for a quick run.
- `--skip-build`: reuse whatever `target/release/fors` already exists.

Every run prints a summary to stderr (agreement rate, one paragraph per
distinct finding with its minimised reproducer) and, with `--report PATH`,
writes the same information as JSON (raw + minimised source, base64, for
every distinct finding, plus the superlinearity check's numbers).

Determinism: `(seed, count, max_depth)` always yields the same generated
programs byte for byte (`gen.generate`), and `(seed, index)` always yields
the same case (base program *and*, if chosen, mutation) inside a `run.py`
campaign (`make_case`) - reproducing a reported finding never depends on
timing or on how many cases ran before it.

## Design: why the generator is "mostly valid"

`gen.py` hand-encodes the EBNF of `docs/spec/07-grammar.md` as a set of
recursive, depth-bounded random-expansion functions (one per grammar
production, named to match: `gen_cmp` for `cmp_expr`, `gen_bit` for
`bit_expr`, and so on), and the token-level rules the EBNF leaves to prose:

- identifiers are drawn from a pool disjoint from `fors_parse.RES` (the
  reserved words), imported directly from `tools/ref/fors_parse.py` so the
  generator's vocabulary can never drift from what the two parsers agree
  is reserved; contextual keywords (`arena`, `out`, `set`, ...) are used as
  ordinary identifiers often, to exercise ch07's contextual-keyword rules;
- integer/float literals cover all four radices, the `_` digit-group rule,
  and every legal suffix (`gen_number`);
- strings cover every escape (`gen_string`); comments are not emitted
  inline (kept for `mutate.py`'s tokenizer instead - see below);
- every statement form ends its own `;` where the grammar requires one;
- the flat bitwise tier and non-chaining comparisons/ranges are enforced
  *by construction*: `gen_cmp` picks `bit_expr` **or** `range_expr [cmp_op
  range_expr]`, never both, and `gen_bit` only ever emits a chain of ONE
  repeated operator (or a single shift) - exactly ch07's `cmp_expr` and
  `bit_expr` productions. A bitwise/comparison/range expression can still
  appear nested inside arithmetic, because `gen_primary` can wrap a fresh
  `gen_expr` in parentheses (`(a & b)` is a `tuple_or_paren`, a legal
  operand anywhere), which is how the grammar itself allows it too.

Because only *syntax* is generated (no attempt is made to make identifiers
resolve, types check, or a `struct`/`enum`/`impl` triad line up
semantically - ch07 "Defines no semantics"), the generator can be much
looser than a program you'd actually compile, which is exactly what a
grammar-boundary fuzzer wants.

At the default `--max-depth 3`, about 3 in 4 freshly generated programs
parse cleanly and 1 in 4 do not (the generator's own probabilities put a
comparison/range/cast operand where a stricter production was needed
often enough to hit ch07's disambiguation rules honestly) - "mostly valid"
without being exclusively so.

## Mutation catalogue

`mutate.py` tokenizes a program with its own small tokenizer (`tokenize` /
`render`; unlike `fors_parse.lex`, it keeps whitespace and comments as
trivia tokens, so `render(tokenize(src)) == src` exactly - verified for
every generated program before any mutation is trusted), then applies
**one** of:

Token-level (`TOKEN_MUTATIONS`):
- `mut_delete_token` / `mut_duplicate_token` / `mut_swap_adjacent`: generic
  single-token edits.
- `mut_drop_semicolon` / `mut_drop_closer`: remove one `;` or one of
  `) ] }`.
- `mut_mix_bitwise`: replace one `& | ^` with a *different* one of the
  three - same-operator chains are legal, mixed ones are not (ch07 rule
  12).
- `mut_chain_comparison` / `mut_chain_range`: duplicate a `cmp_op`/range
  operator plus a filler operand right after an existing one, so `a < b`
  becomes `a < b < zz` - both are single-use only.
- `mut_reserved_as_identifier`: replace an `id` token with a random
  reserved word.
- `mut_deep_nesting`: pick a matched `( ... )` pair and multiply its
  parens by a large random amount (20-400), to probe each parser's
  expression-nesting limit (`fors-syntax`'s is `MAX_DEPTH = 128`,
  `crates/fors-syntax/src/parser.rs`; see "Known disagreements").
- `mut_truncate_mid_token`: cut the file in the middle of a
  string/number/identifier/comment token, not on a token boundary.

Byte-level (`BYTE_MUTATIONS`, applied after re-encoding to UTF-8, so they
can produce input that is not even well-formed UTF-8):
`byte_insert_nul`, `byte_insert_lone_surrogate` (one of the three-byte
CESU-8-style encodings of an unpaired UTF-16 surrogate - never legal
UTF-8), `byte_insert_crlf`, `byte_insert_bom`.

`mutate_bytes(src, rng)` always returns `bytes` and never raises: a
mutation that finds nothing to act on (e.g. `mut_drop_semicolon` on a
`;`-free fragment) is retried with another randomly chosen one.

## How minimisation works

Every disagreement `run.py` finds is reduced with delta-debugging
(`ddmin`, Zeller's algorithm: repeatedly try removing larger and then
smaller contiguous chunks, keeping a removal exactly when the *same*
disagreement still reproduces), in two passes:

1. **Over tokens** - `mutate.tokenize()`'s output, so a whole identifier,
   string, or operator disappears in one step instead of being nibbled
   character by character.
2. **Over raw bytes** - runs on whatever pass 1 leaves, so identifiers
   shrink to one letter, numbers lose digits, and any leftover whitespace
   goes away. This pass also handles inputs pass 1 skips entirely (byte
   mutations that broke UTF-8 can't be tokenized as text).

The "is this still interesting" oracle (`make_is_interesting`) re-checks
the **same direction** the original case showed (Python accepted /
Rust rejected, or vice versa; a Python crash of the same exception type;
a Rust non-0/1 exit or "panicked" stderr; a batch timeout) - never merely
"some disagreement or other", or minimisation could wander from one bug
into a completely different one and report something misleading.

Each distinct `(direction, rust diagnostic code, python exception type)`
bucket is sampled (a handful of representatives, not just the first case
that happened to land in it) and minimised independently, then results
are de-duplicated once more by minimised size - see `run.py`'s
`buckets`/`dedup` for the exact logic. This is what "distinct, de-duplicated
by shape" means in the campaign summary.

## The superlinear-nesting check

`superlinear_nesting_check` parses a geometric series of nested-paren
programs (depth 16, 32, 64, ..., 1024) through the Rust CLI, one file per
invocation, and measures **CPU time of the child process** via
`resource.getrusage(RUSAGE_CHILDREN)` deltas (never wall-clock: this
machine runs other builds concurrently, so wall-clock elapsed time for a
subprocess is not attributable to that subprocess - CPU-seconds consumed
by the child process specifically is the closest available proxy for
"how much work did the parser do", from outside the binary, without
instrumenting it). Each measurement is the min of 3 samples, to cut
scheduler jitter. A run is flagged `SUPERLINEAR` when CPU time more than
triples across a doubling of nesting depth, twice in a row (a generous
margin: linear work should almost exactly double).

## Known disagreements

(Fill in / update this section after each campaign; the numbers below are
from the campaign in this change's report - see the workflow's final
report for the exact counts and minimised sources.)

1. **Closure body bounds a single-use operator, but the outer context
   doesn't see it that way** (ch07 Disambiguation rule 2 vs. the
   non-chaining `cmp_expr` / flat `bit_expr` / single-use `range_expr` of
   rule 12 and the Grammar section). Minimal reproducer:

   ```fors
   fn f() {
       let r = || 1 < 2 < 3;
   }
   ```

   A closure's body is a full, independently-bounded `expr` (Disambiguation
   rule 2's `|a| a | b` example is exactly this: the body keeps consuming
   *while its own grammar still permits it*, no further). Here the body's
   own `cmp_expr` legally consumes `1 < 2` and stops - `cmp_expr` forbids a
   second comparison, so "greedily" cannot mean "past what `cmp_expr`
   itself allows". The closure literal, complete, is an ordinary
   `cast_expr`; nothing in the grammar stops it from being the operand of
   a *new*, separate `cmp_expr` at the outer level, so `< 3` is that new
   comparison, and the whole thing is syntactically legal (what it would
   *mean* is a checker question ch07 explicitly disclaims). Python
   (`fors_parse.py`) accepts it on exactly this reading. The Rust parser
   rejects it (`P0006`, "comparison operators do not chain"), which reads
   as the same underlying implementation issue reaching across the
   closure's own sub-expression boundary. The bitwise (`P0005`) and range
   (`P0010`) tiers show the identical pattern:
   `|| 1 & 2 | 3` and `|| 1 ..< 2 ..< 3`. See
   `tests/conformance/07-grammar/fuzz-closure-body-bounds-{comparison,bitwise,range}-accepted.fors`.

2. **Very deep nesting: Rust caps it and reports one diagnostic; the
   Python reference has no cap and crashes.** `fors-syntax`'s parser has
   an explicit `MAX_DEPTH = 128` (`crates/fors-syntax/src/parser.rs`) and
   its module doc states the design intent in so many words: "Never
   panics: every failure, including recursion past the nesting limit,
   becomes a diagnostic" (`crates/fors-syntax/src/lib.rs`). `ch07` itself
   sets no numeric bound (nesting depth is not mentioned in "Grammar" or
   "Disambiguation rules" at all), so a bounded implementation limit looks
   like the intended reading. `tools/ref/fors_parse.py` has no equivalent
   guard: a few hundred nested parens push it past Python's own recursion
   limit and it raises an uncaught `RecursionError` - not one of its own
   `E(...)` parse errors, so `fors_parse.check` does not return a message,
   it crashes the caller. Minimal reproducer (any large enough N; found
   reliably by `mutate.mut_deep_nesting` and by the generator's own
   `--nesting-case`):

   ```fors
   fn main() {
       let x = ((((((( /* ~150+ more */ 1 /* ... */ )))))));
   }
   ```

   **This one is deliberately *not* added as a `tests/conformance/`
   regression file.** `tools/ref/diff_driver.py` (which
   `crates/fors-syntax/tests/differential.rs` invokes over the whole
   corpus) calls `fors_parse.check` with no exception handling at all, so
   a corpus file that reproduces this would make `diff_driver.py` itself
   crash with an uncaught `RecursionError` **for the whole corpus run**,
   not report one clean disagreement - taking down every other file's
   verdict along with it. That is a materially worse outcome than "one
   more failing assertion", and neither `tools/ref/diff_driver.py` nor
   `tools/ref/fors_parse.py` is in this change's writable scope to harden.
   Instead, `crates/fors-syntax/tests/fuzz_smoke.rs` demonstrates and
   guards this exact disagreement safely, through `gen.py --out`'s own
   `verdict_of`, which *does* catch the exception and records a `crash`
   verdict rather than propagating it. Recommendation for whoever owns
   `tools/ref/`: give `fors_parse.py` (or at least `diff_driver.py`'s call
   site) a depth guard that turns "too deep" into an ordinary `E(...)`
   parse error, matching the Rust side's own stated intent.

## CI smoke test

One `cargo test` can't run a 200000-case campaign, so
`crates/fors-syntax/tests/fuzz_smoke.rs` runs `gen.py` for a small fixed
`--seed 1 --count 200 --max-depth 3 --nesting-case 300`, parses every
resulting program with `fors_syntax::parse` **in process**, and compares
against `gen.py`'s own recorded verdict for that program. It finishes in a
couple of seconds in debug mode (generation of 200 small programs plus one
forced-deep-nesting case, then 201 in-process parses - no cargo build
inside the test). It skips (does not fail) when `python3` is not on
`PATH`.

This seed was chosen *because* it currently reproduces both disagreements
above (organically, from generation and one deliberate `--nesting-case`,
with no mutation involved) - so the test currently **fails**, on purpose,
until they are resolved; see "Known disagreements". Do not change the
seed/count/depth to make it pass without fixing the underlying issue - the
whole point of committing a currently-red test is that CI keeps reporting
the bug until someone closes it.

## Adding a regression from a finding

1. Get the minimised source from a campaign's `--report` JSON
   (`minimized_utf8_lossy`, or decode `minimized_base64`) or from stderr's
   `--- finding ... ---` block.
2. Decide `expect:` from what the SPEC says is correct (not from either
   parser's current behaviour) - cite the exact production or
   Disambiguation rule, as in "Known disagreements" above.
3. Add `tests/conformance/07-grammar/fuzz-<short-description>-{accepted|rejected}.fors`
   following `tests/conformance/README.md`'s directive format:
   ```
   //! name: <snake_case_name>
   //! rule: 07.D<n> (or a Grammar production / section name)
   //! expect: parse-ok | parse-error
   //! detail: <what the cited rule requires, and which parser gets it wrong>
   ```
4. Run `cargo test -p fors-syntax --test differential` and
   `cargo test -p fors-syntax --test conformance`: the new file is
   expected to turn one or both **red**, on the parser that disagrees with
   the spec. That is the point - do not weaken the new file or either test
   to make it pass; report the failure to whoever owns that parser.
5. Never add a case built the way "Known disagreements" #2 above is NOT
   added: first check that `tools/ref/diff_driver.py` (called with no
   exception guard by `differential.rs`) can actually finish over the
   whole corpus with your file in it. If `fors_parse.check` would raise
   something other than its own `E(...)` on it, that is a
   `tools/fuzz/fuzz_smoke.rs`-style finding, not a `tests/conformance/`
   file - it would break the harness for every other file, not just fail
   cleanly on its own.
