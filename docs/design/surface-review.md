# Surface review: readability RFC batch (round-5 grammar freeze)

> **Status:** RFC batch draft, 2026-09-22. Read-only review: this document
> proposes, it changes nothing. Normative spec (`docs/spec/`),
> grammar (`docs/spec/07-grammar.md`), corpus (`tests/conformance/`),
> `std/`, and all crates were read but not modified.
>
> **Frozen baseline:** `docs/spec/07-grammar.md` (round-5 freeze, D1/D2/D4/D5;
> round-6 O2 `defer`/`errdefer`), design intent
> `docs/design/surface-language.md`, call-site markers
> (`docs/spec/01-ownership.md` Rule 2), error/member rules
> (`docs/spec/09-types.md` Rules 36, 42-46; `raise e;`, `scoped(p)`,
> `?.else` rejection, `spawn`), owner directives (`docs/PLAN.md` §4.3:
> mandatory `;` no ASI, flat bitwise tier, 4-space/100-col `fors fmt`,
> `defer`/`errdefer`, separate `main` parameters).
>
> **Samples read (15):** `std/io.fors`, `std/fs.fors`, `std/gpu.fors`,
> `std/mem.fors`, `std/mem/seq.fors` (Iterator + adaptors),
> `std/mem/vec.fors`, `std/mem/hashmap.fors` (7 files);
> `tests/conformance/09-types/adaptor-chain-method-accepted.fors`,
> `map-sum-closure-checked-accepted.fors`, `callable-bound-closure-accepted`
> (shape, via grep), `02-failure/postfix-try-propagate-accepted.fors`,
> `handler-block-value-accepted.fors`, `raises-call-handled-accepted.fors`,
> `01-ownership/defer-consumes-linear-on-all-exits-accepted.fors`,
> `scoped-result-extends-inout-access-accepted.fors` (shape, via grep),
> `07-grammar/bitwise-reject-shift-chain.fors` (8 files).
>
> **Corpus size (counted, not edited):** 1026 `.fors` files total =
> 1011 under `tests/conformance/` + 15 under `std/`; fenced `fors` blocks
> in 11 `docs/spec/*.md` files. Per-feature file counts below were produced
> by `grep -rl` over those three roots; each proposal states exactly what
> was counted.

## Evaluation rule (owner-ordered)

Against every proposal, in this order: (1) does it keep the language
readable **without making it worse** — any proposal introducing hidden
costs, implicit conversions, ASI-style ambiguity, or overload-like
resolution is rejected outright, no matter its ergonomic appeal;
(2) parse cost for the lossless handwritten LL(2) parser (lookahead bound
is 2 tokens; lexer 2 characters); (3) migration cost in files.

## Verdict classes

- **adopt** — the frozen surface is kept (or a purely additive,
  non-breaking clarification is proposed). Freeze impact: **none** unless
  marked "additive-only" (extends accepted code without invalidating any).
- **defer** — worth revisiting post-v0.1 through an additive path.
  Freeze impact: **additive-only** (explicitly argued per proposal).
- **reject** — considered and refused, with reason. Freeze impact: n/a
  (no change); the "breaking" label marks what lifting the freeze *would*
  cost, as a warning.

---

## S1 — Mandatory `;`, no ASI (adopt: keep)

(a) Current: every `let`/`assign`/`expr`/`return`/`raise`/`use`/header
statement ends in `;`; newlines are never terminators (ch07 Lexical 1,
round-5 D4). Pain example — the tax is real but small; from `std/io.fors`:
`self.latched = none;` inside a two-line arm reads fine, and the
`recover_missing_semicolon` diagnostic (`let a = 1 let b = 2;` → exactly
one diagnostic) is the payoff.

(b) Proposed change: none. Keep mandatory `;`.

(c) Readability gain vs cost: `;`+`}` are the two recovery anchors (P3)
and the token-level brace-count prepass depends on statement boundaries
being explicit. Removing them buys one saved keystroke per line and costs
a newline-sensitivity rule every future syntax addition must be checked
against (see R5).

(d) Migration: all 1026 files end statements with `;`; removing the rule
would touch every file. Keeping it touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S2 — Flat bitwise tier (adopt: keep)

(a) Current: level 7b — `& | ^` chain with themselves only, `<<`/`>>`
single-use, operands at cast level; any mix with arithmetic, range,
comparison, or a different bitwise operator is a parse error asking for
parentheses (ch07 Disambiguation 12, round-5 D4). Pain example, from
`bitwise-reject-shift-chain.fors`:
`let r = a << b << c;` is rejected; the writer must parenthesize.
In `std/mem/hashmap.fors`, `(self as u64) ^ seed` already parenthesizes
the cast by habit.

(b) Proposed change: none. Keep the flat tier.

(c) This is the deliberate fix of C's `&`-vs-`==` precedence bug at design
time (a security win: `a & mask == 0` silently mis-grouping is a classic
vulnerability shape). The cost is parentheses on mixed expressions — the
cheapest possible explicitness, with zero hidden runtime cost and zero
parser cost (it is EBNF structure, `bit_expr`, not a checker rule).

(d) Migration: `&`/`|`/`^`/`<<`/`>>` appear in only 2 `std/` files;
bitwise conformance files are a handful. Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**
(See R1 for the rejected alternative.)

## S3 — Word logic (`and`/`or`/`not`) vs symbol bitwise (adopt: keep)

(a) Current: logical ops are words (`and`/`or`/`not`, levels 8-10);
bitwise are symbols (level 7b). Samples: `if not p(x) {` (`std/mem/seq.fors`
`all`/`any`), `pre dt > 0.0 and b.len > 0` (design doc n-body). No `&&`/`||`
tokens exist, so an empty closure `||` lexes as two `|` without a munch
hazard (ch07 Lexical 7).

(b) Proposed change: none.

(c) Words make logic-vs-bitwise confusion a parse error instead of a
precedence trap, and reserving the symbols keeps the closure-bar grammar
LL(2)-clean (Disambiguation 2). Cost: verbosity (`and` vs `&&`) — trivial,
formatter-neutral.

(d) Migration: `and`/`or`/`not` appear across the corpus (contracts,
preconditions, loop conditions); keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S4 — Call-site markers `&x` / `move x` / `&out x` (adopt: keep)

(a) Current: ch01 Rule 2 — non-`let` arguments must be marked:
`&x` (inout), `move x` (sink), `&out x` (set); `let` carries no marker.
Pain example, the densest line in the samples (`std/mem/vec.fors`
`try_collect_into`): `dst.push(&a, move x)?;` — three sigils/markers plus
`?` in one statement. Lighter examples read well: `fill(&hi, 1.0);`
(ch01), `row(y, w, h, max, &band);` (design doc).

(b) Proposed change: none to the markers. (The one softening already
exists: rvalue arguments to `sink` carry no marker, and the `sink self`
receiver is unmarked — see S4b below.)

(c) The markers are the language's core readability bet: aliasing and move
points visible in diffs and greppable (`grep move` finds every move).
Parser bonus: the parser knows an argument's convention without a symbol
table (Disambiguation 4, LA 2). Cost: marker density on hot lines like
`dst.push(&a, move x)?;` — but every marker names a real cost (borrow /
move / init), so nothing is hidden; the density *is* the information.

(d) Migration: `move ` appears in 57 files, `&out` in 7 files
(counted over `tests/conformance` + `std` + `docs/spec`). Any respelling
touches all of them plus every `&x` call site (uncounted individually,
pervasive). Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S4b — Implicit `sink self` receiver move `x.finish()` (adopt: keep, with diagnostic)

(a) Current: owner decision round 4 — the receiver of `x.m(args)` never
carries a marker; when `m` is `sink self` the call moves `x` implicitly
(ch01 Rule 2, ch09 Rule 46). Pain example (`std/mem/vec.fors` comment):
"`sink self`, so the call `v.deinit(&a)` moves `v` implicitly and
discharges its cleanup obligation". A reader sees `v.deinit(&a)` — no
`move` — and must know `deinit` takes `sink self` to see the move.

(b) Considered change: require `(move v).deinit(&a)` always. Before:
`v.deinit(&a);` after: `(move v).deinit(&a);`.

(c) This is the one place the design accepts a hidden move, against the
evaluation rule's "no hidden costs" clause — and it does so deliberately:
`v.deinit(&a)`, `it.count()`, `buf.finish()` with a `move` on every
terminating call would make the common linear-cleanup and iterator-consumer
idioms (`v.iter().map(double).filter(small).take(3).count()`) markedly
noisier, and the mitigation is specified, not hand-waved: ch09 Rule 46
*requires* the use-after-move diagnostic to name the consuming call and its
`sink self` declaration. Reverting now would also churn the two most
idiomatic call shapes in `std` (every `deinit`/`close`/consumer).

(d) Migration: reverting would touch every `sink self` call site —
`deinit`, `close`, all iterator consumers — across `std` (15 files) and
dozens of conformance files (linear + adaptor suites). Keeping touches zero.

(e) **Recommendation: adopt (status quo) — the exception is contained by
a normative diagnostic. Freeze impact: none (reverting would be breaking).**

## S5 — Error triple: `raise e;` / `?` / `else |e| {}` (adopt: keep all three)

(a) Current: `raise e;` (statement, with `;`), postfix `?` (propagate),
`call else |e| { }` (handle at the call). Samples
(`tests/conformance/02-failure/`):
`let a: i64 = take(n)?;` vs `return take(n) else |e| { 0 };` vs
`if n == 0 { raise Err.empty; }`. The three shapes are visually distinct
at a glance: `?` propagates, `else` handles, `raise` creates.

(b) Proposed change: none. (Alternatives `try`/`catch` keywords: see R2.)

(c) `?` is one character at the exact point of the early exit — the
failure-ABI branch made visible. `else |e|` reuses the closure-bar form
the parser already disambiguates (Disambiguation 2/3: after a call's `)`
`else` is followed by `|`, after an `if` block by `if`/`{`; LL(2)-clean).
`raise e;` with mandatory `;` keeps raise greppable and statement-shaped.
No hidden cost: `?` converts only through the single-lookup `ErrorFrom`
impl (ch02 Rule 3), never an implicit chain.

(d) Migration: `raise ` in 46 files, `else |` in 22 files (same three
roots). Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S6 — `f()? else` does not parse (adopt: keep the rejection)

(a) Current: `?` and the `else` handler are alternatives (ch02 Rule 1);
`g()? else |e| {}` is a parse error (ch07 Disambiguation 3,
`pipe_three_roles` test). A reader never has to decide whether the
handler sees the error or the propagated value — the grammar decides.

(b) Proposed change: none; optionally sharpen the diagnostic wording
("`?` and `else` cannot combine; pick one") — diagnostic-only, additive.

(c) Combining them would create exactly the ASI-class ambiguity this
review forbids: two error paths on one call, with precedence to argue
about. The rejection costs one line of diagnostic.

(d) Migration: `else-after-question-rejected` exists; zero accepted-code
impact either way.

(e) **Recommendation: adopt (status quo + diagnostic polish).
Freeze impact: none (diagnostic text is not grammar).**

## S7 — Range spelling `..<` / `..=`; bare `..` is a lexical error (adopt: keep)

(a) Current: half-open `..<`, closed `..=`; `..` not followed by `<`/`=`
is a lexical error (ch07 Lexical 7). Samples: `for i in 0 ..< n`,
`s[0 ..< mid]`, `s[mid ..< s.len]` (ch01 `split_at`). The lexer rule
(`.` continues a number only before a digit) makes `1..<2` three tokens
with no whitespace sensitivity.

(b) Proposed change: none.

(c) Forcing the openness into the operator spelling removes the
off-by-one ambiguity class (Rust's `..` vs `..=` vs `..<` trio, where the
bare form's meaning must be memorized per position). Cost: two characters
vs one — negligible, and `..` as an error catches the typo at lex time.

(d) Migration: ranges are pervasive (loops, slices, contracts); keeping
touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S8 — `let`-in-patterns; bare names are references (adopt: keep)

(a) Current (round-3 decision): a binding inside a pattern is written
`let n`; a bare name is always a reference and an unresolved one is an
error; `fpat` shorthand (`P { x }`) was removed with the fixed diagnostic
`write "let x" to bind the field or "x: pattern"` (ch07 Disambiguation 17).
Pain example (`std/io.fors`): `some(let e) => { raise e; }` — the `let`
inside `some(...)` is noise to a Rust-trained eye. Heavier:
`P { let x, y: Q(let z) }` (grammar conformance sample).

(b) Considered change: restore bare-name binding (`some(e)`, `P { x }`).
Before: `some(let e) => { raise e; }` after: `some(e) => { raise e; }`.

(c) Rejected (see R3): the noise buys the death of the misspelt-constant
catch-all — under bare-name binding, a typo'd variant/constant name
silently becomes a binding. The `let` also makes binding sites greppable
and keeps one-token pattern disambiguation (LA 1). Cost accepted: ~4 extra
characters per binding.

(d) Migration: `some(let` in 17 files, `let <name> =>` shapes in 10 files
(same three roots). Restoring shorthand would be breaking (currently
accepted `let` code stays valid, but every diagnostic, tutorial, and the
removed-shorthand error test inverts meaning). Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**
(See R3.)

## S9 — Closure spelling `|params| body` (adopt: keep)

(a) Current: `| [cparam, ...] | (block | expr)`; conventions allowed
(`|sink x|`, `|let n|`); body `{` means block else greedy `expr`
(Disambiguation 2). Samples: `|sink x| x * 2`
(`map_sum(move xs, |sink x| x * 2, 0)`), `|let n| n * 2`, fn items passed
bare (`v.iter().map(double)`). Pain: `|a| a | b` — body greedily swallows
`a | b`; and `||` is two `|` (empty param list), which surprises on first
sight.

(b) Proposed change: none. (Alternative `fn`-literal: see R7.)

(c) Bars are the lightest possible closure delimiters and compose with the
mandatory-`?`/convention rules: `|sink x|` puts the convention exactly
where `let`-params put it. The greedy-body rule is documented with an
example and matches Rust behavior closely enough to transfer intuition.
Parser cost is contained (three `|` roles distinguished at LL(2)).

(d) Migration: `|`-closures in ~50 conformance files (over-approx: any
file containing `|`; includes bitwise-or and handler bars). Respelling
touches all of them plus `std/mem/seq.fors` adaptor examples. Keeping
touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S10 — `defer` / `errdefer` block-or-`expr;` shape (adopt: keep)

(a) Current (round-6 O2): `defer (block | expr ";")`, same for `errdefer`;
`expr ";"` means exactly `{ expr; }`. Samples:
`defer v.deinit(&a);` (one-liner, ch01 `sum_all`), `defer r.close();`
(conformance), `defer { f(); g(); }` (multi-statement). Block scope, reverse
textual order, inlined at exits — no runtime stack (ch01 Rules 23-23d).

(b) Proposed change: none. (Alternatives: function-scoped defer — see R8;
`defer(error)` modifier — rejected in ch07 for spending call syntax on a
statement keyword and needing LA 3 as a contextual word.)

(c) The two shapes cover the observed uses with no extra keyword: the
one-liner dominates linear cleanup (`defer`+`errdefer` in 67 files, nearly
all single-expression), the block covers the rest. `errdefer` running only
on error exits (ch02 Rule 16) makes `build()`-style
`errdefer v.deinit(&a); … return move v;` read correctly — cleanup on
failure, handoff on success. No hidden cost: bodies are statically inlined
at exits (Rule 23a), and what a body may contain is closed (no
`return`/`raise`/`?`, Rule 23c).

(d) Migration: `defer`/`errdefer` in 67 files. Keeping touches zero; any
shape change (modifier syntax, scoping change) is breaking to all 67.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S11 — Separate `main` parameters, supplied by type (adopt: keep)

(a) Current (round-2 decision): authority arrives as separate `main`
parameters (`fn main(inout out: io.Stdout) raises io.Error`,
`fn main(inout heap: mem.Heap)`, `fn main(inout client: net.Net, inout
out: io.Stdout)` — all attested in `04-authority/` conformance), not one
`World` value. Only root-capability types are legal parameter types.

(b) Proposed change: none. (The `World`-bundle alternative: see R6.)

(c) Separate parameters make authority usage self-documenting at the top
of every program: the signature *is* the capability manifest of `main`.
Unused capabilities are simply absent — no bundle to destructure, no
`w.stdout` projection that dies confusingly (cf. the old design-doc
`move w.stdout` example). Checker cost is flat (closed root-type list,
ch04 R2-1).

(d) Migration: every `fn main` in conformance + `std` uses this shape.
Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S12 — `scoped(p)` return prefix (adopt: keep spelling)

(a) Current: `-> (scoped(s) Slice[T], scoped(s) Slice[T])` (ch01
`split_at`), `fn at(let self: Self, let i: I) -> scoped(self) Self.Output`
(ch09 Rule 21). Pain: the prefix is noisy in tuple returns and reads
inside-out (the scope source `s` is named far from the parameter list).

(b) Considered change: rename to `borrows(s)` / `outlives(s)` / `&s`-style
suffix. Before: `-> scoped(self) Slice[T]` after (example):
`-> Slice[T] borrows self`.

(c) Any rename is pure churn: `scoped` is contextual (LA 2, prefix iff
next token is `(`), so it steals no identifier, costs the parser nothing,
and reads adequately once learned ("scoped to `s`"). A suffix form would
need new disambiguation against `raises`/contracts in the signature tail.
No readability gain justifies breaking every scoped signature in `std`
(`items`/`items_mut`/`iter`/`at`/`split_at` — the core safe-view surface).

(d) Migration: `scoped(` in 28 files (same three roots), concentrated in
the most-reviewed surface (`Vec.items`, `SliceIter`, `Index`). Renaming
touches all 28 plus prose. Keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none
(rename would be breaking).**

## S13 — `inout self` receiver shorthand (adopt: keep)

(a) Current (round-5 D1): `fn next(inout self)` means
`fn next(inout self: Self)`; legal only in trait/impl bodies, only spelled
`self` (ch07 Disambiguation 21, fixed diagnostic). Samples: `std/mem/seq.fors`
is written entirely in the shorthand (`fn map[U: Droppable](sink self, …)`,
`fn next(inout self)`, `fn len(let self: Self)` mixing both).

(b) Proposed change: none.

(c) The shorthand removes the single most-repeated token in `std`
(`: Self` on every method) while the two restrictions + fixed diagnostic
close the misuse paths (free-function `self`, non-`self` type omission).
Readability gain is large and measured in lines: ~every method in
`std/io.fors`, `std/fs.fors`, `std/mem/*` uses it.

(d) Migration: pervasive across `std` (15 files) and trait/impl
conformance files. Keeping touches zero; removing would be breaking.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

## S14 — Homogeneous operators + explicit `as` (adopt: keep; reject hetero arithmetic)

(a) Current (round-4 decision): every binary operator trait is
`Self × Self → Self`, no `Output`, no implicit conversion; `as` is
checked-and-trapping between numeric primitives. Pain example
(`std/mem/hashmap.fors`, repeated in 10 `impl Hash` blocks):
`return (self as u64) ^ seed;` — the cast is mandatory line noise, and
`mixed-width-operands-rejected` / `int-literal-to-float-rejected` show the
checker means it.

(b) Considered change: allow mixed-width arithmetic (`u8 ^ u64`,
`i32 + usize`) with "usual" promotion. Before: `(self as u64) ^ seed`
after: `self ^ seed`.

(c) Rejected (see R4): the noise is the honesty — each `as` names a real
conversion that traps or reinterprets, and homogeneous resolution is what
keeps operator typing a single left-type lookup (ch09 Rule 29) instead of
an overload set. The design already softens the common cases without
promotion: unsuffixed literals check against the other operand's type
(`0 ..< n`, `1 + x`, Rule 29 exception), so loop/index code rarely needs
`as`; only genuinely mixed *typed* values do — exactly where a reviewer
wants to see the cast.

(d) Migration: keeping touches zero. Allowing promotion would silently
change the meaning of every currently-rejected mixed expression and void
the `mixed-width-operands-rejected` suite plus the near-linear gate's
no-promotion premise.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**
(See R4.)

## S15 — `i32` literal default + `usize`-only indexing (adopt: keep + document the idiom)

(a) Current (round-4 decision): unsuffixed integer literals default to
`i32`; indexing stays `usize`-only, so an indexing loop writes
`1usize ..< 8` (ch09 Rule 22). Pain: the `usize` suffix on loop bounds
that index, and `let n = 0;` being `i32` whatever later uses need
(ch09 Rule 27: "The default never looks outward").

(b) Considered change: default literals to `usize`, or infer literal type
from later use. Before: `for i in 1usize ..< 8 { a[i] … }` after:
`for i in 1 ..< 8 { a[i] … }`.

(c) Rejected (see R4 for the inference half): `i32`-default + explicit
`usize` at the index boundary puts the width decision where it belongs —
at the indexing site, which is the trapping site. The Rule 29 literal
exception already covers literal-vs-variable mixes, so only literal-vs-
literal bounds (`1usize ..< 8`) show the suffix, and there it documents
"this range feeds an index". `usize`-default would instead sprinkle `i32`
suffixes on all arithmetic; later-use inference would break the one-pass
rule (Rule 1) and make `let n = 0;` mean different things per function.

(d) Migration: keeping touches zero. Changing the default retypes every
unsuffixed literal in 1026 files.

(e) **Recommendation: adopt (status quo); add a one-paragraph idiom note
to `fors explain`/tutorial ("suffix the bound that feeds an index").
Freeze impact: none.**

## S16 — `for p in e` takes a bare binding, `match` takes `let` patterns (adopt: keep the asymmetry)

(a) Current: loop heads bind bare (`for x in it`, `for i in 0 ..< n`,
`for (lo, hi)` tuples in destructuring position — ch07 `for_stmt` uses
`binding`, not `pattern`); `match` arms bind only via `let` (S8). A reader
may ask why `for let x in …` is not written.

(b) Proposed change: none (unifying in either direction is breaking:
`for let x` would invalidate every loop in the corpus; bare `match`
bindings reintroduce R3's catch-all).

(c) The asymmetry tracks semantics: a `for` head *always* introduces fresh
bindings (there is nothing to match against — no constant arm, no
exhaustiveness), so the bare form is unambiguous; a `match` arm chooses
between binding and comparing, so the `let` is load-bearing. Unifying
would spend syntax to equate two different operations.

(d) Migration: `for` loops are pervasive (every iterator/range sample);
keeping touches zero.

(e) **Recommendation: adopt (status quo). Freeze impact: none.**

---

## R1 — C-like bitwise precedence (reject)

(a) Current: S2's flat tier. Proposal: rank `<<`/`>>` above `&` above `^`
above `|`, C-style, so `a & mask == 0` and `a << b << c` "just work".

(b) Before: `(a & m) != 0` after: `a & m != 0`.

(c) Rejected on all three hard grounds: (i) it reinstates C's
`&`-vs-`==` mis-grouping bug the design explicitly fixed — a *security*
regression, not a style choice; (ii) mixed-tier expressions need the full
Pratt ladder in the reader's head, raising parse cost for humans while
saving two parentheses; (iii) precedence-directed overload resolution is
the thin end of overload-like resolution (which operator's trait wins in
`a & b == c` when both sides are generic?). The flat tier's hint
("parenthesize") is the better diagnostic.

(d) Migration: adopting would touch the `bitwise-*` conformance suite and
invalidate its fixed-hint contract; every currently-parenthesized
expression stays valid, but every *rejected* mix becomes newly accepted
with C semantics — a silent meaning change, the worst kind.

(e) **Recommendation: reject. Freeze impact: would be breaking
(grammar + diagnostics + the round-5 D4 owner decision).**

## R2 — `try` keyword / `catch e` handler (reject)

(a) Current: S5's `?` / `else |e|` pair. Proposal: `try take(n)` and
`take(n) catch e { 0 }` (or `catch(e)`), on the theory that words read
better than punctuation.

(b) Before: `let a: i64 = take(n)?;` /
`return take(n) else |e| { 0 };` after: `let a: i64 = try take(n);` /
`return take(n) catch e { 0 };`.

(c) Rejected: (i) keyword theft — `try`/`catch` become reserved,
unavailable as bindings/fields/members forever, against the ch07 policy of
not reserving common identifier words (cf. `set` staying contextual);
(ii) no disambiguation problem exists to solve — `?` is postfix-only and
`else |` after `)` is already LL(2)-clean, so the keywords buy nothing in
parse robustness; (iii) `?` marks the early-exit point in one character
where `try` prefixes the whole call, distancing the marker from the exit.
`else |e|` additionally composes with the closure mental model
(the handler *is* a closure over the error).

(d) Migration: `?` sites and 22 `else |` files would all churn; two new
reserved words would need a grep-migration proving no corpus identifier
collides.

(e) **Recommendation: reject. Freeze impact: would be breaking
(new reserved words + two productions).**

## R3 — Bare-name pattern bindings (reject)

(a) Current: S8's `let`-in-patterns. Proposal: `some(e)`, `P { x }` bind
implicitly; keep `let` as optional noise. Before: `some(let e) => { raise
e; }` after: `some(e) => { raise e; }`.

(b) Rejected: this is the misspelt-constant catch-all — under bare-name
binding, `some(Empyt)` (typo) binds instead of erroring, and the reviewer
cannot distinguish comparison from introduction at a glance. Round 3
already removed the `fpat` shorthand for exactly this reason, with owner
sign-off; re-litigating spends the freeze lift on a known anti-pattern.
Overload-flavored reading ("is `e` a constant or a fresh binding here?")
is precisely the resolution-like ambiguity the evaluation rule forbids.

(c) Migration: would invert the `pattern_bare_shorthand_removed` suite and
every `let`-pattern in 17+ files into deprecated style; tooling (highlight,
inlay hints) would need binding-vs-reference resolution to render patterns.

(d) **Recommendation: reject. Freeze impact: would be breaking
(pattern grammar + name-resolution diagnostics + round-3 decision).**

## R4 — Implicit numeric conversion / heterogeneous arithmetic (reject)

(a) Current: S14's homogeneous operators. Proposal: allow `u8 ^ u64`,
`i32 + usize`, int-to-float, via "usual arithmetic conversions" or a
small promotion lattice.

(b) Before: `(self as u64) ^ seed` after: `self ^ seed`.

(c) Rejected — the clearest "readable but worse" case in the batch:
(i) hidden costs: each silent conversion is a potential trap/sign-
extension/precision change invisible in the diff; (ii) inference cost: the
Rule 29 one-lookup typing becomes a ranking problem over conversion
candidates — overload-like resolution through the back door, threatening
the near-linear gate; (iii) the stdlib evidence cuts against it: the ten
`(self as u64) ^ seed` lines are *better* explicit, since `Hash` over
mixed widths is exactly where a reviewer audits widths. The literal
exception (Rule 29) already removes the gratuitous cases.

(d) Migration: adopting would void `mixed-width-operands-rejected`,
`int-literal-to-float-rejected`, and the coercion-closed-list premise of
ch09 Rule 10 across the corpus.

(e) **Recommendation: reject. Freeze impact: would be breaking
(checker + round-4 owner decision).**

## R5 — Automatic semicolon insertion (reject)

(a) Current: S1's mandatory `;`. Proposal: Go/Rust-style ASI or
expression-statement newlines, so `let a = 1` needs no `;`.

(b) Before: `let a = 1;` after: `let a = 1`.

(c) Rejected: ASI is the named instance of "ASI-style ambiguity" in the
evaluation rule. It costs the two-anchor recovery story (P3), the brace-
count declaration-boundary prepass (P1 — a token prepass cannot know
whether a newline ends a statement without parsing), and parallel chunking
hints; every future production would need a newline-interaction audit.
The formatter already inserts `;`, so the tax falls on generated code,
not humans.

(d) Migration: adopting touches all 1026 files' worth of statement
terminators and every recovery test (`recover_missing_semicolon` etc.).

(e) **Recommendation: reject. Freeze impact: would be breaking
(lexer + recovery + round-5 D4 owner decision).**

## R6 — `World`-bundle `main` (reject)

(a) Current: S11's separate parameters. Proposal: restore
`fn main(sink w: World)` and project capabilities (`move w.stdout`).

(b) Before: `fn main(inout out: io.Stdout) raises io.Error`
after: `fn main(sink w: World) raises io.Error { var out = move w.stdout; … }`.

(c) Rejected: the bundle hides authority flow — after `move w.stdout`,
the dead remainder `w` is noise every reader must track, and unused
capabilities ride along invisibly. Separate parameters make `main`'s
signature a checkable manifest and compose with the sealed-capability
model (each root type independently gated). Round 2 decided this with the
same reasoning; nothing in the samples motivates reopening.

(d) Migration: adopting rewrites every `fn main` plus the ch04 root-type
rules and their conformance suite.

(e) **Recommendation: reject. Freeze impact: would be breaking
(ch04 authority model + round-2 owner decision).**

## R7 — `fn`-literal closures replacing `| |` (reject)

(a) Current: S9's bars. Proposal: `fn(sink x) x * 2` or `fn |sink x| …`
anonymous-fn syntax, on the theory that `||`/`|` overloading is the
parse wart.

(b) Before: `map_sum(move xs, |sink x| x * 2, 0)` after:
`map_sum(move xs, fn(sink x) x * 2, 0)`.

(c) Rejected: heavier at every use for zero semantic gain — the `|`
roles are already disambiguated at LL(2) with conformance coverage
(`pipe_three_roles`), and `fn(` at expression start collides with the
`fn_type` head and `fn` items in a way bars never do (statement-sync sets
key on `fn`). The adaptor-heavy style (`it.map(f).take(3)`) already avoids
closures entirely via fn items; remaining closures are short, where bars
win most.

(d) Migration: all ~50 closure files plus grammar Disambiguation 2/3 and
their tests.

(e) **Recommendation: reject. Freeze impact: would be breaking
(primary_expr + statement sync).**

## R8 — Function-scoped `defer` with runtime stack (reject)

(a) Current: S10's block-scoped, statically-inlined bodies. Proposal:
Go-style function-scoped `defer` (runs at function exit; runtime
registration).

(b) Before: `for i in 0 ..< n { defer note("end"); … }` (runs per
iteration, Rule 23e) after (hypothetical): same text, runs once at return.

(c) Rejected — hidden-cost textbook case: a runtime deferred stack per
function, per-iteration accumulation for loop-placed defers (the exact
footgun ch01's rejected-alternatives names), and a semantic rewrite of
Rule 23e's per-iteration behavior that every one of the 67 defer files
was written against. Block scope needs no runtime state at all — the
zero-cost choice that matches the failure-ABI's no-unwinder stance.

(d) Migration: adopting redefines when 67 files' worth of bodies run —
silent behavior change on accepted code.

(e) **Recommendation: reject. Freeze impact: would be breaking
(ch01 Rules 23-23f + round-6 O2 owner decision).**

## R9 — Renaming `scoped` (reject for v0.1; see D-series for what *is* open)

(a) Current: S12. Proposal: see S12(b).

(b) Rejected as churn: no semantic or parse problem is solved by any
proposed synonym, and the rename taxes the most carefully reviewed
surface (scoped views underpin `split_at`, `items`, `iter`, `Index`).
Spelling taste is not worth a freeze lift. If a rename ever happens, it
rides a broader pre-1.0 naming pass, not this batch.

(c) **Recommendation: reject. Freeze impact: would be breaking.**

---

## D1 — `errdefer |e|` error binding (defer; additive path exists)

(a) Current: `errdefer` bodies take no error value (ch01 rejected
alternative: "`errdefer |e| { }` binding the error — nothing in v0.1
inspects the error during cleanup; liftable later without breaking
accepted code").

(b) Possible change (post-v0.1): `errdefer |e| { log(e); }` where `e`
names the in-flight error read-only. Before: cleanup blind to the error;
after: cleanup can branch/log on it.

(c) Readability gain is genuine (cleanup that reports *what* failed), and
the cost analysis is favorable: the error is already materialized on the
error exit (ch02 Rule 16 defines the exits syntactically), so binding it
read-only adds no new control flow, no conversion, no resolution — but
v0.1 has no specified use (nothing inspects the error during cleanup),
and the read-only-vs-mutation rules for `e` need a full Rule 23c-style
closure. Not worth designing under the freeze.

(d) Migration: purely additive — `errdefer { }` / `errdefer expr;` keep
parsing and meaning; only new `|e|` forms appear. 67 current defer files
unaffected by construction.

(e) **Recommendation: defer to post-v0.1. Freeze impact: additive-only
(new `errdefer_stmt` alternative; no accepted code changes meaning).**

## D2 — `?.` / `??` optional-chaining operators (defer; additive path exists)

(a) Current: deliberate non-tokens — `?.`, `??` do not exist; `?` is
postfix-only and `f()?.x` is `?` then `.` (ch07 Lexical 7, `lex_munch`).
Nested fallible access is written out: `let t = f()?; t.g()?;`.

(b) Possible change (post-v0.1): `user()?.name()?` sugar over the
desugared sequence.

(c) The spelled-out form is honest about the two early exits (each `?`
is a branch in the failure ABI), while `?.`-chains hide N exits in one
expression — mild hidden-cost flavor, though far below R4's. More
importantly, `?.` interacts with the `f()? else` rejection (S6): chaining
a handler onto a chain needs new grammar decisions, not just a token.
Real but small gain; real design work. Not for v0.1.

(d) Migration: additive — new tokens/postfix forms; no current program
contains `?.` (it is a lexical error today), so nothing accepted changes.

(e) **Recommendation: defer to post-v0.1. Freeze impact: additive-only
(new postfix production; lexer gains two longest-match tokens).**

## D3 — Match guards (defer; additive path exists)

(a) Current: deliberately absent (ch07 open question 4: "Char literals,
labelled `break`, match guards: deliberately absent"). Samples route
around with nested `if`: `if p(x) { return true; }` inside `for`
(`std/mem/seq.fors` `any`), `if self.n >= self.end { return none; }`
(`Counter2.next`).

(b) Possible change (post-v0.1): `some(let x) if x > 0 => …`.

(c) Guards would compress the `any`/`find` shapes slightly, but they cost
exhaustiveness-check complexity (a guard makes an arm non-exhaustive,
forcing the checker to reason about guard coverage or demand a wildcard —
either way new judgment surface against Rule 1's one-pass discipline).
The nested-`if` form reads at least as well and checks today.

(d) Migration: additive — new `arm` alternative; existing arms unchanged.

(e) **Recommendation: defer to post-v0.1. Freeze impact: additive-only
(`arm` gains an optional guard; exhaustiveness rules extended).**

---

## Anything else the samples showed

- **Callable-field call parens `(self.f)(move x)`** (`std/mem/seq.fors`
  comment: "never `self.f(x)`", ch09 T0043): the parens are load-bearing
  (field access vs method call are different lookups), and the comment
  teaches it once. No proposal — the syntax correctly refuses to guess.
- **`by_ref()` borrowing adaptor** (the one `inout`-taking adaptor among
  `sink self` chains): the name plus `scoped(self)` return make the
  borrow extent visible; samples (`adaptor-by-ref-on-inout-accepted`)
  confirm the idiom. No proposal.
- **`for_each`/`fold` consumer conventions** (`fn(sink B, sink Self.Item)`):
  heavy but explicit about ownership flow through the fold — the weight
  *is* the linearity story. No proposal.
- **`grain` keyword** (`parallel for y in 0 ..< h grain 8`): contextual,
  unreserved, reads as English. No proposal.
- **Contract clauses** (`pre i < self.n`, `post`, `invariant`): read well
  in `_ns` mode; no surface friction observed. No proposal.
- **`use` aliases** (`use a.b as c;`, round-3): used in `std/mem*.fors`
  headers; unobjectionable. No proposal.
- **Attribute syntax** (`@unsafe(invariant: "…")`, `@specialize`):
  label-colon form is distinct from calls; no friction observed.
  No proposal.

## Summary counts

| Verdict | Count | Proposals |
|---|---|---|
| adopt (keep frozen surface) | 14 | S1–S16 (S4 counted once incl. S4b) |
| reject | 9 | R1–R9 |
| defer (additive post-v0.1) | 3 | D1–D3 |
| **total** | **26** | |

No proposal in this batch is recommended for adoption *as a grammar
change*: all 14 adopts keep the frozen grammar byte-identical; all 3
defers are argued additive-only; all 9 rejects stay rejected. **Net
grammar-freeze impact of the recommended path: zero — no lift required.**

### Top 3 adopt recommendations

1. **S4 (+S4b) — keep call-site markers** (`&x`/`move x`/`&out x`, implicit
   `sink self` receiver contained by the Rule 46 diagnostic): the
   language's central readability mechanism; density is information.
2. **S2 — keep the flat bitwise tier**: the `(a & m) != 0` parentheses are
   a security feature (C's precedence bug, fixed at design time), not a wart.
3. **S5 — keep the error triple** (`raise e;` / `?` / `else |e|`): three
   visually distinct shapes for create/propagate/handle, LL(2)-clean,
   no keyword theft.

### Top 3 rejects with reason

1. **R4 — implicit numeric conversion**: hidden trap/sign/precision costs
   + turns one-lookup operator typing into overload-like resolution,
   threatening the near-linear gate. The `as` noise is honesty.
2. **R5 — ASI**: the named instance of forbidden ambiguity; destroys the
   `;`/`}` recovery anchors and the token-level declaration-boundary
   prepass that parallel parsing rests on.
3. **R1 — C-like bitwise precedence**: reinstates the `&`-vs-`==`
   mis-grouping vulnerability class the flat tier was designed to kill;
   saves parentheses at the price of a security regression.
