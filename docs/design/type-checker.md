# Fors design: the type checker (`fors-fir`, `fors-check`, `fors-query`)

> **Status: implementation design, 2026-09-20.** Synthesised from three
> competing architect proposals (performance/layout, spec fidelity/
> diagnostics, incrementality/query engine) after verifying their
> load-bearing claims against the code and against `docs/spec/09-types.md`.
> This is the document an implementer follows without re-deriving anything.
> Where it conflicts with `docs/spec/09-types.md`, the spec wins and this
> document is wrong; where it conflicts with `docs/PLAN.md` §4.1-4.2, the
> plan wins except for the one deviation flagged in §16 (BLAKE3).
> Nothing here re-litigates an owner decision.

Contents: §1 what was verified and corrected · §2 scores · §3 the decisions,
fork by fork · §4 crates · §5 FIR data layout · §6 the prelude · §7 the
algorithms · §8 rule-to-code table · §9 query DAG and invalidation · §10
diagnostics and recovery · §11 testing strategy · §12 CI plan · §13 ordered
increment plan · §14 open questions for Marc · §15 not covered · §16 what is
unproven.

---

## 1. What was verified against the code and the spec

Every claim below was checked with `graft skeleton`, `graft grep` or a
direct read on 2026-09-20. The proposals were written blind to each other and
to some of the code; these are the facts the design rests on.

**Confirmed (all three proposals build on these correctly):**

- `crates/fors-syntax/src/tree.rs`: `Tree` is four parallel columns
  (`kinds: Vec<NodeKind>`, `first_token`, `token_len`, `subtree_len`, all
  `u32`), flat pre-order; a subtree is the contiguous slice
  `[i, i + subtree_len[i])`; `NodeKind` is `#[repr(u8)]`. The checker builds
  no tree of its own.
- `crates/fors-index/src/ids.rs`: `DefId` exists, unused, documented as
  "the future scope / def tables". `DeclId` is a per-file row index (rows
  pushed in tree order by `build_decl_table`), so it renumbers on insertion.
- `crates/fors-index/src/decl.rs`: `DeclTable` has `sig_hash`/`body_hash`
  per row; a method in an `impl`/`trait` is its own row with `parent`; the
  test `assoc_type_def_is_signature_level_and_method_bodies_are_not`
  already pins ch09 R2 at token level.
- `crates/fors-index/src/fingerprint.rs`: two-lane FNV-1a-128 + SplitMix64,
  `0xFF` separators; `splitmix64` is private; there is no byte-string
  entry point. `docs/PLAN.md` §4.1 says BLAKE3.
- `crates/fors-index/src/interner.rs`: `Interner` has `intern(&mut self)`
  and `resolve`; no immutable `get`.
- `crates/fors-resolve/src/scope.rs::resolve_path` (L159-241) records
  exactly one `NameUseTable` entry per path node and does not record how
  many segments it consumed; `Deferred` is pushed for six different
  reasons (unresolved head already diagnosed N0014; path ends on a module;
  non-`pub` segment; `PreludeModule(_, None)` with a tail — `std` absent
  from the build; `PreludeModule` at the end; `Poisoned`). The checker must
  be silent in all six but cannot today tell them apart.
- `crates/fors-resolve/src/lib.rs::resolve_fn_sig_and_body` walks
  `Generics` (declaring), then `Params`, then the gparam *bounds*: the
  `NameUseTable` is **not** node-monotone. A sort is required.
- `crates/fors-resolve/src/lib.rs::resolve` computes the module edge list
  and hands it to `build_universe`; `ResolveOutput` does not expose it.
  ch09 R43 needs the direct edges.
- Three `Diagnostic` types exist (`fors-lex`, `fors-index` with `DiagCode`
  N-codes, `fors-resolve` with `Code::{N, A}`); `lib.rs::index_diag_rule`
  already bridges two of them.
- `crates/fors-resolve/src/target.rs`: `Entity::Item { file, decl }`,
  `Entity::Variant { file, decl, index }` (ordinal, not node),
  `PreludeType`/`PreludeValue`/`PreludeModule(sym, Option<ModuleId>)`,
  `Poisoned`; `ResolvedTarget::{Entity, Local{node}, Deferred}`.
  `crates/fors-resolve/src/prelude.rs`: `some`, `none`, `reduce` are prelude
  values; `Iterator`, the operator traits, `Copyable`, `Range`, `RangeIncl`,
  `Index`, `IndexMut` are prelude types.
- `crates/fors-resolve/tests/conformance.rs`: `PENDING_04` has seven rows
  (rules 2, 3, 10, 12, 14 "needs types"; 7, 13 "needs the manifest");
  `PENDING_08 = ["private_field_cross_module_rejected"]`;
  `ch09_types_corpus_resolver_view` asserts the resolver is clean on every
  T-/ch01-coded test and reports exactly the named N-code on the two others.
- ch08 R21 (orphan rule): `impl Tr for T` lives in the module defining `Tr`
  or the module defining `T`'s item; an inherent impl in `T`'s module. So an
  `(trait, head)` impl bucket has at most two source modules.
- ch08 R7 (round 5, D3): the module graph is exactly the explicit `use`
  edges; no body scan. Verified in `08-names.md` L147-167 and the corpus
  (`trait-method-without-edge-rejected/` is a three-module directory test).
- The receiver shorthand `fn conv(let self)` is **already in the ch09
  corpus** (`grep "self)" tests/conformance/09-types` finds it), and no ch09
  test uses `use std.<m>`.
- `const` patterns in the corpus are integer and `bool` literals only
  (`LIMIT: i32 = 10`, `YES: bool = true`); a literal-folding `constval` is
  enough for v0.1.

**Corrected (each proposal got at least one of these wrong):**

1. **Corpus counts.** All three said 68 accepted / 105 T-coded. The corpus
   holds **186 tests: 69 `check-ok`, 117 `check-error` = 106 T-coded + 9
   ch01-coded + 2 N-coded** (N0027 `assoc-type-duplicate-in-impl-rejected`,
   N0026 `constraint-entry-head-not-earlier-rejected`, both already
   passing). The task statement's "106 pending T-coded" is right.
2. **Nesting depth.** Performance and Incremental left "does the parser
   bound nesting?" unverified. It does: `fors-syntax/src/parser.rs`
   `MAX_DEPTH: u32 = 128` on every recursive production, reported as a
   diagnostic. The checker's `synth`/`check` recursion inherits it; only
   `normalise`/`holds` need their own guards, and by the spec's own
   argument those descend on strict subterms of a finite type, so a guard
   there is an internal-error assertion, not a limit a program can hit.
3. **`Entity` carries no `DefId`.** Fidelity reads `Entity(..)` as giving
   a `DefId`; it gives `(FileId, DeclId)`. A build-wide `DefTable` with a
   `def_of[file][decl]` map (Performance) must be built first.
4. **Other-chapter counts.** ch01 has 31 `check-error` files (not 30),
   ch04 has 20 (not 19), ch02 9 and ch03 13 (both right).
5. **Fidelity's assumption (iv)** that the receiver shorthand touches only
   lowering is right, but it is not future work: the corpus already uses
   it, so lowering must accept an omitted receiver annotation from the
   first signature increment.
6. **Performance's `Interner::get` argument** ("an identifier absent from
   the build-wide interner cannot name any declared member") holds only
   after signature lowering has interned every member name (field, method,
   associated type, variant). The index pass interns declaration names and
   the resolver interns field and variant names, but associated-type names
   are interned nowhere today. The signature phase (sequential, `&mut
   Interner`) closes that gap before any body is checked.
7. **`fors-fir` depending on `fors-index` transitively links the parser**
   (Performance is right: `fors-index` depends on `fors-lex` and
   `fors-syntax`). This is a dependency-direction hygiene point, not a ch05
   R2 violation (R2 forbids re-*parsing* imported source, not linking the
   parser). Extracting `fors-intern` is deferred (§3, fork 12) and replaced
   by a CI test.

---

## 2. Scores

Criteria (1-5): **F** spec fidelity (every ch09 rule has a home), **G** the
three M1 exit gates, **P** ch09 R1 single pass, **I** implementability by one
developer plus agents in green increments, **D** diagnostics quality,
**Z** zero-dependency rule.

| Proposal | F | G | P | I | D | Z | Notes |
|---|---|---|---|---|---|---|---|
| Performance | 4 | 4 | 5 | 3 | 3 | 5 | Best data layout and the best measurement plan (deterministic counters). `TypeId` bit-packing and a fifth crate (`fors-flow`) add surface for little gain; the "everything interned is normal" invariant is right but its leak modes are the top risk and it says so. |
| Fidelity | 5 | 3 | 5 | 4 | 5 | 5 | Best auditability (rules table, emission sites, CHECK-position trace, use tape with non-optional R46 fields, one-diagnostic-per-test gate). Its contextual `Param(i)` reading is the one unsound-accept hazard in all three proposals; its query layer is thin. |
| Incremental | 4 | 5 | 5 | 3 | 4 | 5 | Best query-DAG design (name-based `DeclKey`, `(trait, head)` buckets bounded by the orphan rule, `TraitWorldRevision` caches, declaration-relative diagnostics, the SigHash ⟺ mutation harness). Re-plumbing `resolve()` into queries in increment 1 is too big a first step and collides with concurrent work. |

**The single most valuable idea taken from each:** Performance — the
`flags` byte per interned type that makes `subst_norm` on monomorphic code
one load and one test, plus counters (not wall time) as the near-linearity
gate. Fidelity — every value use of a place goes on a `UseTape` whose
`Cause::ImplicitReceiver` fields are non-optional, so ch09 R46's mandatory
message cannot be forgotten and typing stays one pass. Incremental — the
dependency key is a `SigHash` over a canonical, index-free FIR encoding with
generic parameters as ordinals, layered above the existing token hash, and
impl lookup keyed `(trait, HeadKey)` so the orphan rule bounds every bucket
to two modules.

---

## 3. The decisions, fork by fork

Each fork names which architect is followed and why. Where they conflict
irreconcilably the decision and its reason are stated.

1. **In-memory type shape: interned SoA rows, `TyId(u32)`.** All three.
   Rule 9 equality is `a == b`; the repo idiom (`Tokens`, `Tree`,
   `DeclTable`, `ModuleScope`) is parallel columns with `u32` newtypes.
2. **Qualifiers: a `quals: u8` column in the intern key, NOT packed into
   the id.** Fidelity/Incremental over Performance. Packing steals four
   bits and makes every pool and memo key aware of two fields. Performance's
   real concern — R43's "qualifiers stripped for lookup" must be O(1) and
   ch01 R11 / ch05 R6a propagation must not intern — is met by a
   `unqual: Vec<TyId>` column (the same row with `quals = 0`, self when
   unqualified) filled at intern time, so stripping is one load; adding a
   qualifier is an intern (rare: field reads of `imm` values, `secret`
   propagation).
3. **Undetermined generic arguments are never interned; there is no
   `Infer` tag.** Incremental (structurally unrepresentable) over
   Performance (scratch-level `Infer`). A callee's own `Param{owner, i}`
   rows are read as *slots* only inside `type_call`, through a per-call
   `Binding` that is a stack local. Fidelity's contextual reading is
   rejected because `Param` **carries its owner `DefId`** (Performance/
   Incremental), so the rigid parameter `T` of the declaration under check
   and the slot `T` of a callee are different rows even when both are
   ordinal 0. Recursion is safe: in `f`'s own body a call `f[T](x)` reads
   `Param{f,0}` in the *callee signature* as a slot and binds it to the
   rigid `Param{f,0}` from the argument; nothing in the argument side is
   ever bound.
4. **Every interned `TyId` is normal (R20 already applied).** All three.
   Normalisation happens in `subst_norm`, at substitution time, and a
   `Proj` row is interned only with a rigid head. The `--paranoid`
   assertion (Performance) guards the invariant.
5. **Expected type is an argument of `check`, never state.** Fidelity/
   Incremental. `BodyCx` has no expectation field; ch03 R25 is enforced
   by which function the parent calls, and audited by the recorded-trace
   test over `CHECK_SITES` (with the five ch09-addendum positions listed
   separately, Incremental).
6. **Judgements return `TyId`, never `Result`.** Fidelity. `TY_ERROR` is
   absorbing; recovery continues; every `check-error` test must yield
   exactly one diagnostic.
7. **Generic calls: one-way match over the un-substituted signature type
   with a dense `Binding`; `subst_norm` returns `Option<TyId>` (None while
   a slot is unbound).** Simplification of all three: no partial type is
   ever materialised (Incremental's `Inst::Partial` is unnecessary once
   the matcher walks the original signature type against the binding).
8. **Normalisation and bound satisfaction: pure memoised functions, caches
   scoped to a `TraitWorldRevision`, not DAG nodes.** Incremental. The
   memo key for `holds` is `(TyId, TraitRefId)` — sound because `Param`
   carries its owner and a neutral projection's constraint entries are a
   function of the head's owner (Performance's observation). The method
   lookup memo is keyed `(ModuleId, TyId, Symbol)` (Fidelity's risk 2).
9. **Impl index: SoA sorted by `(trait DefId, HeadKey)` with binary search,
   one merkle key per bucket.** Performance's layout, Incremental's
   granularity. R19 overlap runs per bucket.
10. **Language-known traits and built-in impls are ordinary FIR rows.**
    All three. `IndexMut`'s prerequisite is the one hard-coded arm.
11. **Exhaustiveness: the plain algorithm only.** All three; R55 makes the
    plain count normative.
12. **Crates: `fors-fir`, `fors-check`, `fors-query`; move/liveness is
    `fors_check::flow`, not a crate; `fors-intern` is not extracted now.**
    Incremental's crate set. Against Performance's `fors-flow`: same query
    key, so a crate boundary buys nothing and costs a traversal. Against
    `fors-intern`: it moves 150 lines out of a crate under concurrent
    edit for a hygiene property a CI grep enforces just as well
    (`fors-fir` must not mention `fors_syntax` or `fors_lex`). Revisit when
    a `.fmod` reader exists (M2).
13. **Query keys are name-based `DeclKey`s; the dependency key is the
    FIR `SigHash`; token hashes are the input pre-filter.** Incremental.
    Impl disambiguator = 32-bit fold of the header tokens (edit-local,
    order-independent), not a FIR hash (which does not exist at index
    time) and not an ordinal (renumbers).
14. **Query engine: real but late.** Performance/Fidelity sequencing over
    Incremental's increment 1. `resolve()` stays whole-build in M1; its
    outputs are wrapped as hashed query values (`module_exports` uses the
    existing `export_signature`; `name_uses(DeclKey)` is a slice of the
    file table). Dependency recording (`DepSet`) is in `BodyCx` from the
    first body increment so gate (c) is testable by counting before the
    memo engine exists. Per-module incremental resolution is M2.
15. **Diagnostics: one `Code` enum in `fors-index::diag`, re-exported.**
    Incremental. Variants `N | A | T | O | F | D` (ch08, ch04, ch09, ch01,
    ch02, ch03). The letters for ch01-03 are a drafting default (§14 Q1).
16. **Auditability: `rules.rs` with 62 rows, `EMIT_SITES`, a generated
    traceability table, `site: u16` on every diagnostic.** Fidelity.
17. **Per-node results are `Vec`s indexed by `node - decl_start`.**
    Performance. 9 B/node of the declaration under check, reused.
18. **Parallel body checking is designed in, not switched on in M1.**
    Performance's three-level store (global immutable / worker-local /
    call-local) is the layout; M1 runs bodies on one thread with the
    global store frozen after signature lowering. Turning on workers is a
    measurement decision after the I3 gate (§13).
19. **Hash function: keep FNV-128 + SplitMix64 from `fors-index`.** All
    three flag the PLAN deviation; §14 Q2.
20. **`raises` is `Option<TyId>` on a `FnSig`/`FnTy` row.** Fidelity/
    Incremental; Performance's reserved `NoRaises` core is equivalent and
    less readable.
21. **Fresh brands are `(owning DeclKey, with-statement ordinal within the
    declaration)`.** Performance's ordinal (declaration-relative, stable
    under edits elsewhere) with a DeclKey owner (Incremental/Fidelity),
    and the encoder asserts a fresh brand never enters a signature (ch01
    R15(a)).

---

## 4. Crates

Zero external crates. Dependency edges (new crates in bold):

```
fors-lex ← fors-syntax ← fors-index ← fors-resolve ← fors-cli
                              ↑             ↑
                          **fors-fir** ← **fors-check** ← fors-cli
                                              ↑
                                        **fors-query** ← fors-cli
```

### 4.1 `fors-fir` — the type and signature universe

Depends on `fors-index` only (for `Symbol`, `Interner`, `DeclKind`, the id
newtypes and the fingerprint mixer). CI test: no `fors_syntax`/`fors_lex`
identifier appears in `crates/fors-fir/src`. Knows nothing about the CST,
the resolver or diagnostics; returns outcomes, never emits.

| module | contents |
|---|---|
| `ty.rs` | `TyId`, `TyTag`, `TyStore`, `Quals`, `ArgsId`, `TraitRefId`, `ProjKeyId`, `FnTyId`, `BrandId`, `ConstId`, `intern`, `flags` |
| `cons.rs` | open-addressed hash-consing table (keys `u64`, values `u32`), SplitMix64 mixing; no `std::HashMap` on the hot path |
| `sig.rs` | `SigStore`, `GenericsStore`, `FnSigStore`, `MemberStore`, `AssocStore`, `ConstraintStore`, `Conv`, `GParamKind` |
| `defpath.rs` | `DeclKey`/`DeclKeyTable` (name-based identity), `HeadKey` |
| `subst.rs` | `subst_norm(store, ty, binding) -> Option<TyId>`; `Binding`; the one-way match |
| `normalise.rs` | R20: `normalise_proj(head, trait_ref, name) -> Norm` |
| `bounds.rs` | R12: `holds(subject, trait_ref) -> Holds` |
| `impls.rs` | `ImplIndex` (sorted SoA), bucket lookup, R19 `overlap(bucket)` |
| `prelude.rs` | language-known traits, types, variants and built-in impls as ordinary rows |
| `encode.rs` | canonical byte encoding of a signature; `sig_hash -> u128`; `decode` (re-intern) |
| `display.rs` | the one place a type is rendered (post-normalisation) |
| `constval.rs` | comptime values for const arguments and const patterns: integer, `bool`, `Str` literals and the trapping integer operators over them |

### 4.2 `fors-check` — lowering and the two judgements

Depends on `fors-lex`, `fors-syntax`, `fors-index`, `fors-resolve`,
`fors-fir`.

| module | contents |
|---|---|
| `defs.rs` | `DefTable` (build-wide SoA indexed by `DefId`: `file, decl, module, kind, name, vis, parent, key: DeclKeyId, span`), `def_of[file][decl]` |
| `rules.rs` | `CH09_RULES: [RuleEntry; 62]`, `EMIT_SITES`, `CHECK_SITES`, `CHECK_SITES_CH09_ADDENDA` |
| `lower.rs` | CST + `ResolveOutput` → FIR signatures, one declaration at a time; R3-R8, R11, R13, R15, R16 (decl side), R61, R62 (static side) |
| `wf.rs` | whole-head well-formedness: R14 SCC, R17, R18, R19 (per bucket), R21 prerequisite, R23 `Copyable` impls, R24, R25, R48 |
| `body.rs` | `BodyCx`, statements (R31), locals, loop depth, `DepSet` |
| `expr.rs` | `synth`/`check`, R26-R37, R42, R47 |
| `call.rs` | `type_call` R38-R41 with steps (a)-(f) as named fns; `Binding` |
| `member.rs` | R42-R45, R47, R49 (ch08 R11 with `Code::N(11)`), `MemberUseTable` |
| `pat.rs` | R50-R52 |
| `exhaust.rs` | R53-R55, `MATCH_STEP_FACTOR = 256`, `PatStore`, bump-arena matrices |
| `tape.rs` | `UseTape`, `UseEvent`, `Cause` |
| `flow.rs` | ch01 R3, R4a(a)-(e), R8 loop-head merge, R46's message; consumes the tape |
| `diag.rs` | `Diagnostic` construction, per-node bitset, per-declaration budget |
| `facts.rs` | `BodyFacts` (typed side table: `expr_ty`, `callee`, `recv_conv`, `resolved members`), FMIR's input |
| `lib.rs` | `check_build(&ResolveOutput, ...) -> CheckOutput`; phases |

### 4.3 `fors-query` — the content-hash query DAG

Depends on `std` only for the engine (`key.rs`, `db.rs`, `cycle.rs`,
`stats.rs`); the Fors-specific query set lives in `fors-check::queries`
(so `fors-query` stays reusable and testable with synthetic queries).
`docs/PLAN.md` already names `fors-query::decl_fingerprint()` as a learning-
mode contribution point, so the crate is expected. §9.

### 4.4 Changes to existing crates (all in increment I0; all mechanical)

`fors-index`
- `diag::Code` widened: `N(u16) | A(u16) | T(u16) | O(u16) | F(u16) | D(u16)`;
  `DiagCode` folds into `Code::N`. `fors-resolve::diag` re-exports.
- `fingerprint`: `pub fn hash_bytes(&[u8]) -> u128` and `pub fn splitmix64`.
- `interner`: `pub fn get(&self, &[u8]) -> Option<Symbol>`.
- Nothing is added to `DeclTable`: the FIR hash is *derived* and lives in
  the query memo (Incremental's point: an input must not depend on a
  derived value).

`fors-resolve`
- `NameUseTable`: `consumed: Vec<u8>` (segments consumed by `resolve_path`);
  `ResolvedTarget::Deferred { reason: DeferReason }` with
  `Diagnosed | StdAbsent | Member` (member = a genuinely deferred tail);
  `finish()` sorts by node and asserts uniqueness; `target_of(node)` by
  binary search.
- `ResolveOutput.edges: Vec<(ModuleId, ModuleId)>` and
  `direct_edges_of(ModuleId) -> &[ModuleId]` (sorted).
- No change to `ModuleScope`/`Universe`: they are already the member-lookup
  substrate.

`fors-cli`
- `run_check`: after `resolve`, `fors_check::check_build`, diagnostics
  merged into the same sorted line list; `--emit=fir`, `--count`
  (deterministic counters), `--stats` (query hit/miss), `--explain T0026`,
  `--audit` (dumps the rules table).

---

## 5. FIR data layout

All declarations are concrete; field widths are the decision.

### 5.1 Types

```rust
// fors-fir/src/ty.rs
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)] pub struct TyId(pub u32);
pub const TY_ERROR: TyId = TyId(0); pub const TY_UNIT: TyId = TyId(1); pub const TY_NEVER: TyId = TyId(2);
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct ArgsId(pub u32);     // interned TyId list
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct TraitRefId(pub u32); // (trait DefId, ArgsId)
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct ProjKeyId(pub u32);  // (TraitRefId, assoc Symbol)
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct FnTyId(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct ConstId(pub u32);

#[repr(u8)] #[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyTag {
    Error, Unit, Never,
    Prim,     // a = PrimKind (i8..usize, f32, f64, bool, Str, rawptr)
    Nominal,  // a = DefId (struct/enum, prelude generic types included), b = ArgsId
    Tuple,    // b = ArgsId, len >= 1
    Fn,       // a = FnTyId
    Dyn,      // a = TraitRefId
    Param,    // a = owner DefId, b = ordinal in the owner's own gparam list (trait: Self = 0)
    Proj,     // a = head TyId (rigid: Param or Proj), b = ProjKeyId
    Brand,    // a = BrandKind (0 = param, 1 = fresh), b = index into `brands`
    ConstVal, // a = ConstId, b = TyId of its type          (R13 closed const argument)
}
pub const Q_ISO: u8 = 1; pub const Q_IMM: u8 = 2; pub const Q_SECRET: u8 = 4;
pub const F_PARAM: u8 = 1; pub const F_PROJ: u8 = 2; pub const F_BRAND: u8 = 4;
pub const F_ERROR: u8 = 8; pub const F_FRESH: u8 = 16;

pub struct TyStore {
    tag: Vec<TyTag>, a: Vec<u32>, b: Vec<u32>,   // 9 B
    quals: Vec<u8>,                              // part of the intern key (R9)
    flags: Vec<u8>,                              // OR of children at intern time
    unqual: Vec<TyId>,                           // same row with quals = 0 (self when unqualified)
    copyable: Vec<u8>,                           // 0 unknown, 1 yes, 2 no — lazy R23 cache
    args: Vec<TyId>, args_start: Vec<u32>, args_len: Vec<u16>,   // ArgsId pools
    trait_refs: Vec<(DefId, ArgsId)>,
    proj_keys: Vec<(TraitRefId, Symbol)>,
    fn_tys: FnTys,                               // conv: Vec<u8>, ty: Vec<TyId>, result, raises: Vec<TyId /*NONE*/>, per FnTyId
    brands: Vec<BrandRow>,                       // Param { owner: DefId, ordinal: u16 } | Fresh { owner: DeclKeyId, ordinal: u16 }
    consts: Vec<ConstValue>,                     // I(i128) | B(bool) | S(Symbol)
    cons: ConsTable,                             // one open-addressed table for rows, args, trait refs, proj keys, fn tys
}
```

20 bytes per distinct core type in parallel columns. `intern(row)` hashes
`(tag, a, b, quals)` with SplitMix64, probes linearly, ORs the children's
`flags` and fills `unqual` in the same step. Ids are assigned in first-intern
order; the signature phase interns in declaration order (deterministic), so
ids are reproducible within a build but never serialised (§5.4).

`Fn` rows: conventions are on parameters (R7 equality is pairwise on
conventions), `result` defaults to `TY_UNIT`, `raises` is `NONE` or a
`TyId` (R7: absent is distinct from every `raises E`; R60: it may be a
`Param`). A closure type is an `Fn` row plus a `closure: bool` bit in
`FnTys` (R7: each closure has its own type; it equals no `fn` type but
coerces to an equal one by R10(b)); the bit is set only on bodies' local
layer, never in a signature.

**Store invariants** (asserted under `cfg(paranoid)` at every intern):
every `Proj` head is `Param` or `Proj`; no `Brand::Fresh` reaches the
global layer; `flags` is exact.

### 5.2 Signatures

```rust
// fors-fir/src/sig.rs — SoA indexed by DefId
#[repr(u8)] pub enum SigKind { Fn, ExternFn, Struct, Enum, Trait, Impl, Const, Poisoned, Absent }
#[repr(u8)] pub enum Conv { Let, Inout, Sink, Set }
pub enum GParamKind { Type, Const { ty: TyId }, Brand, Callable { fn_ty: TyId } }   // R15, classified once

pub struct SigStore {
    kind: Vec<SigKind>,
    generics: Vec<GenericsId>,                 // own gparams: name, kind, bounds (TraitRefListId, SORTED), plus constraint entries
    fn_sig: Vec<FnSigId>,                      // NONE unless Fn/ExternFn
    members: Vec<MemberListId>,                // struct: fields (name, vis, TyId); enum: variants (name, payload kind, TyIds/fields); trait/impl: item DefIds
    self_ty: Vec<TyId>, trait_ref: Vec<TraitRefId>,   // impls; NONE otherwise
    assoc: Vec<AssocListId>,                   // trait: (Symbol, bounds); impl: (Symbol, rhs TyId)
    const_ty: Vec<TyId>, const_val: Vec<ConstId>,     // Const rows (value NONE when not literal-foldable)
    sig_hash: Vec<u128>,                       // canonical FIR hash (§5.4)
}
pub struct FnSigStore { // per FnSigId
    p_start: Vec<u32>, p_len: Vec<u8>,          // into params: name Symbol, conv, ty  (names are in the hash: R37)
    result: Vec<TyId>, raises: Vec<TyId>,       // NONE = non-raising
    scoped: Vec<u8>,                            // 0xFF = none; else the designated parameter index (ch01 R19)
    receiver: Vec<u8>,                          // 0xFF = associated function; else 0 and the receiver conv is params[0].conv
    contracts: Vec<(u32, u32)>,                 // CST node range of pre/post/invariant (ch02; checked in the decl's own context, R30)
}
```

`Self` inside an `impl` is replaced by the self type at lowering (R8), so an
impl method's signature has no `Self` row; `Self` inside a `trait` is
`Param{trait, 0}` whose single bound is the trait itself with its own
parameters (R8). A trait's own gparam list is `[Self, P1, ..]`.

**Members** are a flat pool with a per-head sorted index
`MemberIndex: (HeadKey, Symbol) -> MemberRef` built once (fields,
variants, inherent methods, associated functions, trait items, impl items),
which is also how R48 clashes and R43 tier 1 are answered. Member names are
`Symbol`s looked up with `Interner::get` — a name not in the interner cannot
be a member (it was never declared), and the answer is "no such member".

### 5.3 Declaration identity

```rust
// fors-fir/src/defpath.rs — SoA, interned
pub struct DeclKeyId(pub u32);
pub struct DeclKeyTable {
    parent: Vec<DeclKeyId>,     // NONE for a top-level item; the impl/trait for a method
    module: Vec<ModulePathId>,  // interned dotted segments (bytes, not Symbol values, in the hash)
    kind: Vec<DeclKind>,
    name: Vec<Symbol>,          // NONE for an impl
    disamb: Vec<u32>,           // impl: 32-bit fold of header tokens (trait path + self type); duplicates +1 in source order. Else 0.
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum HeadKey { Prim(PrimKind), Nominal(DefId), Tuple(u16), Fn, Dyn(DefId), Param, Proj, Never, Unit }
```

`DeclKey` is the query identity (§9); `DefId` is the in-build row index.
`DefTable.key[def]` maps one to the other; a map `DeclKeyId -> DefId` is
rebuilt whenever `decl_keys(file)` changes.

### 5.4 Serialisation and content hash (the binary module interface)

`encode_sig(store, names, def) -> Vec<u8>` emits a canonical, build-index-
free byte stream: a post-order stream of types, each type emitted once and
referenced afterwards by its stream position; a nominal or trait head is its
`DeclKey` bytes (module segments as length-prefixed bytes, kind byte, name
bytes, disamb); a `Param` whose owner is the declaration being encoded (or
its enclosing impl/trait) is a relative marker `(depth, ordinal)`, any other
owner is its `DeclKey` bytes plus ordinal; every list is length-prefixed;
bound lists and constraint-entry lists are sorted by their encoded bytes;
qualifier and convention bytes are single bytes; names of value parameters
are included (R37 makes labels observable); **generic-parameter names are
not** (R38(a) is positional); an impl's `type A = T;` right-hand sides are
included (R2); a `const` declaration includes its comptime value when it is
literal-foldable (R13, §14 Q4); contract clauses are included as their
token hash (ch02 R9 makes them part of the declaration). `Brand::Fresh` in a
signature is a `debug_assert!` and encodes as `Error`.

`sig_hash = fors_index::fingerprint::hash_bytes(&encoded)`; `decode`
re-interns bottom-up into the reader's store and re-establishes
hash-consing. Two hash levels per declaration, deliberately:

| hash | owner | over | role |
|---|---|---|---|
| `DeclTable.sig_hash` (exists) | fors-index | signature tokens | input pre-filter: does `signature_of` re-run |
| `DeclTable.body_hash` (exists) | fors-index | body tokens | input pre-filter: does `check_body` re-run |
| `SigStore.sig_hash` (new) | fors-fir | canonical FIR | the early-cutoff key every dependent compares |

Why both: token hashing alone is unsound as a dependency key (edit module
`a` so `use a.Shape;` in `b` names a different `Shape`: `b`'s tokens are
identical, its meaning is not) and over-eager (a bound reorder or a gparam
rename invalidates dependents). ch09 R2 says the key is a fingerprint of
the *resolved* signature.

---

## 6. The prelude

`fors_fir::prelude::build(store, interner) -> PreludeDefs` runs once per
build before any user signature is lowered and produces ordinary rows,
hashed and indexed exactly like user code, for:

- the primitive types (R3), `()`, `never`;
- the built-in generic types of R5 as `Nominal` heads with reserved
  `DefId`s: `Array[T, N: usize]`, `Slice[T]`, `vector[T, N: usize]`,
  `mask[N: usize]`, `Option[T]` (an enum with variants `some(T)`, `none`),
  `atomic[T]`, `Own[T, A: brand]`, `Ref[T, A: brand]`, `Arena[T, A: brand]`,
  `Range[T]`, `RangeIncl[T]`; the prelude values `some`/`none` are the
  variant paths;
- the traits of R21 transcribed from its code block: `Add Sub Mul Div Rem`
  (`fn op(let self, let rhs: Self) -> Self`), `Neg`, `BitAnd BitOr BitXor
  Shl Shr`, `Eq` (`eq -> bool`), `Ord` (`lt`, `le`), `Iterator { type Item;
  fn next(inout self) -> Option[Self.Item]; }`, `Index[I] { type Output; fn
  at(let self, let i: I) -> scoped(self) Self.Output; }`, `IndexMut[I] { fn
  at_mut(inout self, let i: I) -> scoped(self) Self.Output; }` (with the
  `Index[I]` prerequisite flag), the marker traits `Copyable`, `Shared`,
  and `ErrorFrom[E]` (ch02 R3; method shape fixed when ch02's std surface
  lands — v0.1 uses `fn from(sink e: E) -> Self`);
- every built-in impl of R22 as an `ImplIndex` row: all integer types ×
  {arithmetic, bitwise, `Eq`, `Ord`}, `Neg` for signed integers and floats,
  floats × {`Add Sub Mul Div Rem Neg Eq Ord`}, `bool: Eq`, `mask[N]: BitAnd
  BitOr BitXor Eq`, `Array[T,N]: Index[usize] { Output = T }` + `IndexMut`,
  `Slice[T]` and `vector[T,N]` likewise, `Arena[T,A]: Index[Ref[T,A]] {
  Output = T }`;
- the built-in `Copyable` list of R23 as impls (numeric, `bool`, `()`,
  `never`, `rawptr`, `Str`, `Ref[T,A]`, `fn` item types) plus the structural
  cases (tuples, `Array`, `vector`, `mask`, `Option` of `Copyable`) as a
  short arm in `is_copyable` that recurses on components and caches in
  `TyStore.copyable`. Never `Copyable`: `Own`, `Arena`, allocator and
  root-capability types, any `iso` type, closures, `dyn`.

A build-time assertion (`prelude_matches_corpus_shapes`) extracts every
prelude name and arity the ch09 corpus uses and asserts the prelude declares
exactly those (Performance's risk 3). An omitted receiver annotation
(`fn next(inout self)`) is rewritten to `inout self: Self` in one function
of `lower.rs`, so the concurrent syntax migration touches one place.

---

## 7. The algorithms

### 7.1 Phases of `check_build`

```
1. defs:      DefTable from every file's DeclTable; DeclKeyTable; def_of[file][decl]
2. prelude:   fors_fir::prelude::build
3. lower:     for each declaration in (module bytes, DeclKey bytes) order: lower_signature(def)
              — types interned into the GLOBAL layer; assoc-type names and member names interned
4. wf:        ImplIndex build; per bucket R19; R14 SCC; R17, R18, R21, R23, R24, R25, R48
5. freeze:    global TyStore becomes immutable; SigStore.sig_hash computed; memos reset (TraitWorldRevision := 1)
6. bodies:    for each fn/method/const/provided-method in the same order: check_body(def)
              — body-local types go to a worker-local layer; DepSet recorded; UseTape emitted; flow pass
7. output:    diagnostics concatenated in declaration order, sorted by (file bytes, offset, code)
```

### 7.2 Lowering a type (`lower.rs::lower_type`)

`lower_type(cx, node) -> TyId` over `QualType | TypeApp | TupleType | FnType
| DynType | ScopedType`. For a `TypeApp` it reads `target_of(node)` and
`consumed`:

| target | consumed vs segments | meaning |
|---|---|---|
| `Entity::Item` struct/enum, `PreludeType` | all | nominal head; args by R11 (count, kinds; `Array[T, N+1]` is T0013) |
| `Entity::Item` trait | all | only legal after `dyn`, in a bound or an impl header, else T0011 |
| `Local{GParam}` (type kind) | all | `Param{owner, ordinal}` |
| `Local{GParam}` (brand/const kind) | all | `Brand`/const argument in an argument slot; as a type: ch01 R15d / T0058 |
| `Local{GParam}` or `Self` | one deferred | projection `P.A` → R61 (exactly one bound trait declares `A`; else "no associated type" / "ambiguous"), interned `Proj` (neutral); inside `impl Tr for S`, `Self.A` is replaced by the impl's own definition, no lookup (R61(c)) |
| `Local{Binding|Param|CParam}` | — | T0011 naming the binding (R11) |
| three or more segments after the head | — | T0061(a) |
| `Deferred{Diagnosed}` / `Deferred{StdAbsent}` / `Poisoned` | — | `TY_ERROR`, silent |
| `Entity::Item` + one deferred segment (`Counter2.Item`) | one | T0061(b) "write the type itself" |

Qualifiers set `quals`; `scoped(p)` sets `FnSigStore.scoped`, not a type.
R15 classifies each `GParam` from its bounds once; R62 checks constraint
entries statically (only on a `fn`'s generics; head is an earlier type
parameter — the resolver already did the earlier-than test; traits only).

### 7.3 The two judgements (`expr.rs`)

```rust
pub(crate) fn synth(cx: &mut BodyCx, node: u32) -> TyId;
pub(crate) fn check(cx: &mut BodyCx, node: u32, expected: TyId) -> TyId;
```

`check` returns `expected` on success, `TY_NEVER` under R10(a), `TY_ERROR`
under recovery. Its dispatcher:

```
check(node, T):
  match kind[node]:
    Literal          -> unsuffixed int: T integer? ok : T0027 (float type or rigid param/proj: T0027); unsuffixed float: T float? ok : T0027; else subsume(synth)
    DotLit           -> T must be an enum head with variant `.v` (R34); payload as a call with expected T; else T0034
    ArrayLit         -> ch03 R21/R24a: T ∈ {Array[E,N], vector[E,N], mask[N]}: count == N else D0021; each element check(E)
    Closure          -> T must be Fn (R35): cparam count/conv/annotated types agree; body check(result); `?`/raise use T.raises; else T0035
    Block            -> statements; tail: check(tail, T); no tail: T == () or never
    IfExpr/MatchExpr -> every branch/arm check(T) (R32); condition synth == bool (R30); patterns check_pat (R50)
    TupleOrParen     -> T n-tuple of same arity: componentwise check; `(e)` = check(e, T)
    StructLit        -> type_call(node, Callee::Struct, expected = Some(T))
    CallExpr         -> type_call(..., expected = Some(T))
    TryExpr/Handler  -> the call with expected T (R36); handler block check(success type)
    ComptimeBlock    -> as its block
    AsmExpr          -> ch04 R27: T ∈ {(), scalar, pointer, tuple of such per `out`} else A0027
    BareOp           -> T is fn(let X, let X) -> X or -> bool with X complete (R37): denotes R21's method for X
    _                -> subsume(node, synth(node), T)

subsume(node, S, T):                                  // R10, once, outermost only
  if S == T or S == TY_ERROR or T == TY_ERROR: T
  elif S == TY_NEVER: T                               // (a)
  elif S is closure/fn-item type and T is Fn and fn_shape_eq(S, T): T   // (b); rejected if S mentions a brand or is scoped
  elif T is Dyn(tr) and holds(S, tr) != No: T          // (c); same rejection
  else: emit T0026 "expected T, found S" at node; TY_ERROR
```

`synth` is one `match kind[node]` (a jump table over `#[repr(u8)]`):

```
synth(node):
  Literal      -> suffix type | i32 | f64 | Str | bool                              (R27)
  NameExpr     -> by target_of: Local -> local_ty[node]; const -> its type; non-generic fn -> Fn row (R7);
                  generic fn / `none` with no [..] -> T0039; unit variant -> enum (R38 with zero args);
                  Entity type/trait/module -> ch08 already diagnosed or T0011; with deferred tail -> member::qualified (R45)
  AddExpr/MulExpr/BitExpr/CmpExpr/UnaryExpr -> operator(node)                        (R29, below)
  AndExpr/OrExpr/NotExpr -> operands synth == bool else T0030; bool
  RangeExpr    -> both operands same integer I (literal exception of R29); Range[I]/RangeIncl[I]
  CastExpr     -> synth operand; both numeric primitives else T0030 (ch03 R6); U
  UnaryExpr `move` -> synth(e) (mode too); `-lit` -> the literal
  Block        -> statements (R31); tail synth | () | never
  IfExpr/MatchExpr -> branches in order until a non-never R; later branches check(R); all never -> never (R32)
  TupleOrParen -> componentwise
  ArrayLit     -> ch03 R22: T from first element, rest check(T); empty -> D0022
  StructLit    -> type_call(Callee::Struct, expected None)                            (R34/R38)
  CallExpr     -> callee classification: path-to-fn/variant/assoc fn/trait fn -> type_call; FieldExpr operand -> method call (R43-46);
                  a value of Fn/callable type -> every argument check (R7)
  FieldExpr    -> synth(operand); struct head with visible field (R42, R49) -> field type substituted, quals |= recv & (IMM|SECRET);
                  `len` on Array/Slice built in; else T0042 (rigid/tuple/enum/prim have no fields)
  Bracket      -> R47: operand is a path to a generic item or a method -> instantiate (type_call with explicit args);
                  else index: operator_index(node)                                    (R29)
  TryExpr      -> operand must be a call to a raises-E fn (F0002); success type
  Handler      -> the call; `|x|` binds x: E; handler block check(success)             (R36)
  Closure      -> every cparam annotated else T0035; body synth; no `return`; non-raising; a fresh closure Fn row (local layer)
  DotLit / BareOp / AsmExpr -> T0034 / T0037 / A0027 ("CHECK only")
  ComptimeBlock -> its block
  Error        -> TY_ERROR, no diagnostic
```

Statements (`body.rs`, R31): `let p: T = e` → `check(e, T)`; `let p = e` →
`synth(e)`, `never` is T0033; tuple bindings need an n-tuple; `a = e` →
`synth(place a)` then `check(e, that)`; expression statement → `synth`,
value dropped; non-tail statement-form `if`/`match` → `check((), ..)`;
`for p in e`: `synth(e)` is `Range[I]`/`RangeIncl[I]` → `I`; `Array[T,N]`/
`Slice[T]` → `T`; else `holds(S, Iterator)` (rigid `S` needs the bound) →
element = `subst_norm(S.Item)`; else T0031; the iterable is a value use
(tape event `Move|Copy`, cause `Iterable`); bodies of `for/while/parallel/
with/attribute` blocks `check(())`; function body `check(result)`; `return
e` `check(e, result)`; `raise e` `check(e, raises)` (F0001 if no `raises`);
`break`/`continue` outside a loop T0033; `spawn e` requires a call (R37);
`grain` `check(usize)` (R30); `with` introduces a fresh brand.

Every value use of a place appends a `UseEvent` (§7.9). `local_ty` and
`local_kind` (`Value | TypeParam | ConstParam | BrandParam | Callable |
SelfOfImpl | SelfOfTrait`) are `Vec`s indexed by `node - decl_start`.

**Operators (R29):**

```
operator(node):                        // a op b, flat n-ary nodes fold left to right
  if a is an unsuffixed literal (opt. negated) and b is not: S = synth(b); check(a, S)   // literal-left exception
  else S = synth(a)
  tr = TRAIT_OF[op]
  match holds(unqual(S), tr):
    No if S rigid  -> T0057 (Rule 57: the fix is a bound)
    No             -> T0029 naming operator, trait, S
    _              -> check(b, S) (homogeneous; ch03 R25 CHECK); result: Eq/Ord -> bool, else S
  `-a`: Neg likewise; `-lit` checks the literal
  `a op= b`: statement; b checked against synth(place a); trait of op must hold
operator_index(node):                  // a[i]
  S = synth(a); range directly inside brackets -> built-in slice on Array/Slice only (ch03 R24), scoped
  cands = Index impls whose head matches S (rigid: Index bounds of S)
  0 -> T0029; 1 (Index[I]) -> check(i, I); >1 -> J = synth(i) (unsuffixed literal: T0029 "suffix the index"); require holds(S, Index[J])
  result = subst_norm(chosen impl's Output); a write or `&` use selects IndexMut with the same I (R21)
```

### 7.4 Generic calls (`call.rs`, R38-R41)

```rust
pub(crate) fn type_call(cx, call: u32, callee: Callee, explicit: Option<&[u32]>,
                        receiver: Option<(u32, TyId)>, args: &[u32], expected: Option<TyId>) -> TyId
```

`Callee` = `Fn(DefId) | Method{def, impl_or_trait: DefId} | Struct(DefId) |
Variant(DefId, ordinal) | TraitFn{trait, def}`. The *parameters to
determine* are the owner container's gparams (with `Self` = ordinal 0 for a
trait) then the callee's own; `Binding` is a stack local of `type_call`:

```rust
struct Binding { owners: [DefId; 2], slot: SmallVec<TyId /*NONE = unbound*/, 8> }
// slot index = (owner index, ordinal); Param{owner, i} is a SLOT iff owner ∈ owners
```

Steps, literally R38:

```
type_call:
  (a) explicit [..]: count must equal the callee's OWN gparam count (constraint entries take none) else T0039;
      each arg classified by the declared kind (type / const value or bare const param / brand) else T0011 or O0015d
  (b) receiver: one_way_match(self_param_ty, recv_ty, &mut b); conv marker rules are R46 (no marker; rvalue for sink)
  (c) if expected = Some(T): one_way_match(result_ty, T, &mut b) in NoFail mode — brand positions skipped (R40), mismatch binds nothing, no error
  (d) for (i, arg) in args:
        p = param_ty[i]
        if arg is a Closure and p is Fn-shaped (or Callable{fn_ty}) — R41:
            if every PARAMETER type of p is complete under b: check closure params by R35;
               if result complete: check(body, result) else r = synth(body); one_way_match(result, r, &mut b)
            else fall through to the general case (the closure will be SYNTHed and fail R35 -> T0035)
        match subst_norm(p, &b):
            Some(t) => { check(arg, t); }                                  // CHECK position (ch03 R25 + "bound-by-earlier-argument means CHECK")
            None    => { s = synth(arg); one_way_match(p, s, &mut b); pending.push((i, arg, s)); }
        argument-count and named-label (R37) and convention-marker (ch01 R2) checks are here, at the call (R39)
  (e) for (i, arg, s) in pending: t = subst_norm(param_ty[i], &b).expect_complete_or(T0039 naming the first unbound slot);
        if !(s == t || coerces(s, t)) -> T0026 at arg          // the only place a skipped projection is compared
      for each bound and constraint entry of the callee (and container): holds(subst_norm(subject), subst_norm(trait_ref)) else T0012
  (f) result = subst_norm(result_ty, &b) or T0039; in CHECK mode: subsume(call, result, expected)
  record facts.callee[call], facts.recv_conv[call]; tape events for arguments by convention
```

Nothing survives the call: `Binding` is dropped when `type_call` returns; a
nested call in an argument recurses with its own `Binding` (R38(f)).
`debug_assert!` at every statement boundary that no `Binding` is live.

**One-way match** (`fors-fir/src/subst.rs`), linear in `|P|`:

```
one_way_match(P, A, b, mode) -> Bound | Equal | Skipped | Mismatch:
  if flags[P] & F_PARAM == 0: return P == A ? Equal : Mismatch     // fast path: nothing to bind
  match tag[P]:
    Param{owner, i} where owner ∈ b.owners:
        if A == TY_NEVER: return Skipped                              // R33: never binds nothing
        if b[i] unbound: b[i] = A (quals included); Bound              // never revised
        else: b[i] == A ? Equal : Mismatch
    Proj{head, key}:
        if head (transitively) is an unbound slot: Skipped              // R38(d): projections never bind
        else: t = subst_norm(P, b).unwrap(); t == A ? Equal : Mismatch  // head bound => normalise, then compare
    Brand: in mode NoFail (step c) Skipped; else identity compare       // R40
    _ : tags and quals and heads must be equal, then args pairwise; Fn: convs, params, result, raises pairwise
  Nothing in A is ever bound; no occurs check.
```

**Substitute-and-normalise** (`subst_norm(t, b) -> Option<TyId>`), the
only place a projection collapses (R20):

```
subst_norm(t, b):
  if flags[t] & (F_PARAM | F_PROJ) == 0: return Some(t)     // one byte load for monomorphic code
  match tag[t]:
    Param{owner, i} if owner ∈ b.owners: b[i] (None if unbound)
    Param/Brand/Prim/...: Some(t)                             // rigid
    Nominal/Tuple/Dyn/Fn: map over args; re-intern (unchanged args => same id)
    Proj{head, (tr, name)}:
        h = subst_norm(head, b)?; tr' = subst args of tr
        normalise_proj(h, tr', name)                          // §7.5; NoImpl reported by the caller as T0012 at the site
```

### 7.5 Normalisation (`normalise.rs`, R20)

```
normalise_proj(h, tr, name) -> Norm { Ok(TyId) | NoImpl { h, tr } }:
  memo (h, tr, name) hit -> return                              // negative entries cached too
  if is_rigid(h) (Param, or Proj):  intern Proj{h, (tr, name)}  // neutral; equal only to the same (head, trait+args, name)
  else:
     match impl_lookup(tr, h):                                   // §7.6, at most one by R19
       None            -> NoImpl (memoised)
       Some((imp, ib)) -> rhs = assoc_def(imp, name); subst_norm(rhs, ib) — recursion is on a STRICT SUBTERM of h (R18 + R61(d))
```

Bottom-up: arguments of `h` are already normal because every interned type
is. A depth counter `NORMALISE_DEPTH_MAX = 256` turns a violated premise
into an internal-error diagnostic (`I0001`, non-T), never a hang.

### 7.6 Bound satisfaction (`bounds.rs`, R12) — memoised lookup, no search

```
holds(x, tr) -> No | ByBound(owner, bound idx) | ByImpl(impl DefId, ArgsId):
  x = unqual(x); if x == TY_ERROR: ByBound(ERROR)
  memo (x, tr) hit -> return
  match tag[x]:
    Param{owner, i}  -> scan the owner's declared bounds of gparam i (a handful); plus Index[I] when IndexMut[I] is among them (R21)
    Proj{head, key}  -> the bounds its trait declares for `name` (R16) + the constraint entries on this exact TyId in scope
                        (a sorted array (TyId -> bounds) built per declaration from R62 entries of the owner and its container); nothing from any impl (R57)
    _                -> impl_lookup(tr, x) then require the matched impl's own bounds on the subterms it bound (each a strict subterm of x by R18)
impl_lookup(tr, x):
  bucket = ImplIndex.range(tr.trait, head_key(x))                 // binary search over two u32 columns
  for imp in bucket: ib = Binding{owners: [imp]}; if one_way_match(imp.trait_ref, tr, ib) && one_way_match(imp.self_ty, x, ib) all slots bound: return (imp, ib)
  None
```

`IndexMut[As]` on an impl additionally requires `holds(S, Index[As])` at
the impl (R21, impl parameters rigid); inside `IndexMut`, `Self.Output` is
`Index[I]`'s. A budget `distinct_subterms(x) * bucket_len` exceeded is
`I0002`, an internal error.

### 7.7 Member lookup (`member.rs`, R42-R49) — no scope lookup

| node shape / target | function | rule |
|---|---|---|
| `FieldExpr` not followed by `CallExpr` | `field(recv, name)` | R42, R49 |
| `FieldExpr` followed by `CallExpr` | `method(module, recv, name)` two tiers | R43, R44, R46 |
| `NameExpr` `Entity::Item` struct/enum or `PreludeType` with deferred tail | `qualified(head, name)` | R45 |
| `NameExpr` `Entity::Item` trait with deferred tail | trait fn, `Self` a slot | R45 |
| `NameExpr` `Local{GParam}` with deferred tail | from the parameter's bounds (a value: R45; a type: R61) | R45/R61 |
| `Bracket` | index-or-instantiate by the operand's target | R47 |
| `FInit`/`FPat` | field of the head type | R34, R50 |
| `NamedArg` | label == parameter name at that position | R37 |
| `DotLit`/`PatDot` | variant of the expected/scrutinee enum | R34, R50 |
| `PatPath` one segment, no payload | unit variant of `S` or `const` of `S` (int/bool/Str) else T0050 with the `let n` hint | R50 |

`method`: strip qualifiers; tier 1 = inherent receiver methods of the head
whose self type one-way-matches `S`; tier 2 = candidate traits: rigid
`Param` → its bounds; neutral `Proj` → the trait's declared bounds for `A`
plus constraint entries; `Dyn(tr)` → `tr`; otherwise the prelude traits
plus the traits with an impl for `S`'s head located in the head's defining
module, the current module, or a module the current module has a **direct
edge** to (`ResolveOutput.direct_edges_of`). Zero candidates T0043; more
than one in the answering tier T0044 listing them. The memo key is
`(ModuleId, TyId, Symbol)`. No auto-deref/auto-ref (`no-auto-deref-own-
rejected` is T0043 because `Own[T,A]` has no `bump`). Visibility (ch08 R11)
is checked for every member resolved, with `Code::N(11)`. Every answer is
written to `MemberUseTable` (node → `ResolvedMember`), the completion of the
resolver's side table for the LSP and FMIR; a debug post-pass asserts every
`Deferred{Member}` node inside the declaration is either resolved there or
carries a diagnostic.

### 7.8 Patterns and exhaustiveness (`pat.rs`, `exhaust.rs`)

`check_pat(cx, pat, S)` is R50 verbatim (wildcard, `let n` binds `n: S`,
literals by `S`'s kind, floats T0050, tuples by arity, paths to unit
variants/consts, payloads by variant, `{}` payloads by visible fields).
Then `exhaust::check_match(arms) -> Exhaustive | Missing(witness) |
BudgetExceeded`, the plain usefulness algorithm: patterns lowered into a
`PatStore` (SoA `kind, ctor, sub_start, sub_len`); constructors `Variant
(DefId, u32) | Bool(b) | Tuple(n) | Struct(DefId) | Int(i128) | Str(Symbol)`
where a `const` pattern lowers to `Int`/`Bool`/`Str` of its comptime value
(so a constant and an equal literal collide, R53); `_` and `let n` are
wildcards; integer and string columns are never complete. For each
usefulness query (one per arm, then the all-wildcard row) specialise the
first column by each occurring constructor plus the default matrix when
those are not a complete signature; charge one step per row of every
matrix formed; no memoisation, no early exit but empty matrix / exhausted
columns; stop with T0055 past `256 × pattern-node count`. T0053 names the
witness of the all-wildcard query; T0054 at each non-useful arm.

### 7.9 The use tape and the flow pass (`tape.rs`, `flow.rs`)

```rust
pub struct UseEvent { node: u32, place: PlaceId, kind: UseKind, cause: Cause }
pub enum UseKind { Read, Copy, Move, MutBorrow, OutBorrow, Assign, Declare }
pub enum Cause { Explicit(u32), Argument{ call: u32, param: u16 }, Iterable(u32), Capture(u32),
                 ImplicitReceiver { call: u32, method: DefId, owner: DefId } }
```

`PlaceId` interns `(root local node, [Field(Symbol) | Index])`. Typing
emits: `Move` for a value use of a non-`Copyable` place, `Copy` for a
`Copyable` one (R23, via `TyStore.copyable`), `MutBorrow`/`OutBorrow` for
`&`/`&out` arguments and `inout self` receivers, `ImplicitReceiver` for a
`sink self` method on a place. `flow.rs` then runs one forward pass over the
tape following the CST's structured control flow: R3 (moves out of `let`),
R4a(a) use after move, (b) move inside a loop of an outer place unless
re-initialised on every path to the loop head (the R8 merge), (c) partial
move, (d) `let`/`inout` parameter, (e) capture; `spawn x.run()` is the
`move` capture. An event whose place has type `TY_ERROR` is skipped. Codes
are `Code::O(4)` etc. with the clause letter in the message. R46's
mandatory message is built from `Cause::ImplicitReceiver`'s non-optional
fields: "`x` was moved by the call `x.finish()` at L:C, because
`Builder.finish` takes `sink self` (declared at L:C)". `(move x).m()` and
`x.m()` produce identical tapes modulo the cause tag (a test asserts it).
Full ch01 (R6-R9 exclusivity, R12-R13 sendability, R19a scoped extents) is
M3 and consumes the same tape; it migrates into FMIR's front half then.

### 7.10 Error recovery in one paragraph

`TY_ERROR` is absorbing (`subsume` succeeds either way, `holds` answers
yes, `one_way_match` binds nothing, member lookup is silent). `synth` never
fails. A `NodeKind::Error` node, a `Poisoned` target, a `Deferred{
Diagnosed | StdAbsent}` target and a `SigKind::Poisoned` callee yield
`TY_ERROR` with no new diagnostic. `let p: T = <bad>` still binds `T`. A
signature that fails to lower keeps the arity `decl_arity` found so callers
report argument-count errors, not "unknown function". One diagnostic per
CST node (bitset), at most `MAX_DIAGS_PER_DECL = 32` then a suppression
note. Depth: `MAX_DEPTH = 128` from the parser for expressions;
`NORMALISE_DEPTH_MAX`/`HOLDS_BUDGET` as internal errors.

---

## 8. Rule-to-code table

Every ch09 rule, then the obligations inherited from other chapters.
"static" = decidable from signatures (phase 3-4); "body" = phase 6. Codes
equal rule numbers; `NoCode` rows have no diagnostic by the spec's own
statement.

| Rule | Code | Module::function | Phase | Note |
|---|---|---|---|---|
| 1 | T0001 | `body::let_stmt` (no type, no init); `expr::closure_synth` (unannotated cparam is T0035 per R35); `debug_assert` no live `Binding` | body | the rest of R1 is the architecture |
| 2 | — | `encode::sig_hash`; test `assoc_type_def_edit_is_signature_level` | static | NoCode: incremental property |
| 3 | T0003 | `prelude::build`, `lower::prim` | static | no other scalar |
| 4 | T0004 | `lower::tuple_type` (`(T)` = T), `expr::never_forms` | both | |
| 5 | T0005 | `prelude::build` | static | |
| 6 | T0006 | `ty::intern` (nominal identity by DefId) | — | |
| 7 | T0007 | `ty::fn_ty`, `expr::name_expr` (fn item value; generic needs args → T0039) | body | |
| 8 | T0008 | `lower::self_ty` (Self → S in impls; trait Self = Param 0) | static | |
| 9 | T0009 | `TyId == TyId` after `subst_norm` | — | |
| 10 | T0010 | `expr::subsume` | body | brand/scoped rejection (b)(c) |
| 11 | T0011 | `lower::type_app` (arity, kinds, head is a type-level entity, value head names the binding) | static + body | |
| 12 | T0012 | `bounds::holds`; callers: `call::check_bounds`, `wf::impl_bounds`, `normalise` NoImpl | both | |
| 13 | T0013 | `lower::const_arg` (integer/bool type; closed via `constval`; bare const param; `N + 1` rejected) | static | |
| 14 | T0014 | `wf::infinite_size` (SCC over decls + one node per `Tr.A`; edges skip Own/Ref/Arena/Slice/rawptr/fn/dyn) | static | whole-build, per-declaration summaries |
| 15 | T0015 | `lower::classify_gparam` | static | |
| 16 | T0016 | `lower::trait_decl` (assoc bounds are traits; `Self.A` neutral; receiver type is Self or omitted); provided bodies checked in `body` with Self rigid | static + body | |
| 17 | T0017 | `wf::impl_completeness` (required methods, assoc types exactly once, nothing else, no `type` in inherent impl, RHS well-formed and meets bounds, method signature equality after substitution+normalisation) | static | N0027 stays the resolver's |
| 18 | T0018 | `wf::impl_params` (trait/type positions; every param in head; bounded param in self type; no projection in head; no bare-param self) | static | |
| 19 | T0019 | `impls::overlap` per bucket (first-order unification with occurs check, bounds ignored, assoc types unread; reported at the later impl by (module bytes, disamb) order) | static | |
| 20 | T0020 | `normalise::normalise_proj`, `subst::subst_norm` | both | NoImpl → T0012 at the site |
| 21 | T0021 | `prelude::build` (trait rows); `wf::indexmut_prereq`; `holds` arm; `wf::operator_trait_no_output` → T0017 | static | |
| 22 | T0022 | `expr::and_or_not`, `range`, `cast`, `move`; built-in impls in `prelude` | body | codes T0030 for operand errors |
| 23 | T0023 | `wf::copyable_impl` (defining module; fieldwise; `P: Copyable` needed); `ty::is_copyable` cache | static + body | |
| 24 | T0024 | `wf::marker_traits` (no methods; not `dyn`) | static | |
| 25 | T0025 | `wf::dyn_capable` (no assoc type, no generic methods, receiver methods let/inout, Self only as receiver); `lower::dyn_type` | static | |
| 26 | T0026 | `expr::subsume`, `call::final_compare` | body | |
| 27 | T0027 | `expr::literal_synth`, `expr::check` Literal arm | body | |
| 28 | T0028 | `expr::name_expr` | body | T0039 for generic without args |
| 29 | T0029 | `expr::operator`, `expr::operator_index` | body | T0057 when rigid |
| 30 | T0030 | `expr::and_or_not`, `body::condition`, `expr::range`, `expr::cast`, `body::grain`, `body::contract_clause` | body | |
| 31 | T0031 | `body::stmt`, `body::for_stmt`, `body::fn_body` | body | |
| 32 | T0032 | `expr::if_match_synth`, `expr::check` IfExpr/MatchExpr arms | body | |
| 33 | T0033 | `body::let_stmt` (never), `subst::one_way_match` (never binds nothing), `body::break_continue` | body | T0039 for undetermined |
| 34 | T0034 | `call::struct_lit` (fields exactly once, visible), `expr::dot_lit` (CHECK only), variant construction | body | |
| 35 | T0035 | `expr::closure_check`, `expr::closure_synth` | body | |
| 36 | T0036 | `expr::try_expr`, `expr::handler` (raises-E callee; success type; `x: E`; handler block checked); `ErrorFrom` via `holds` | body | ch02 codes for ch02 rules |
| 37 | T0037 | `expr::comptime_block`, `body::spawn_stmt`, `expr::bare_op`, `call::named_arg` | body | |
| 38 | T0038 | `call::type_call` steps (a)-(f) | body | |
| 39 | T0039 | `call::result_ty` (unbound slot), `call::explicit_count`, `call::arg_count`, `call::conv_marker` | body | |
| 40 | T0040 | `subst::one_way_match` Brand arm; `call::match_expected` NoFail; fresh brands only to callee params | body | mismatch is T0026 |
| 41 | T0041 | `call::visit_args` closure pre-test | body | |
| 42 | T0042 | `member::field` | body | |
| 43 | T0043 | `member::method` tier search, `member::candidate_traits` (module graph) | body | |
| 44 | T0044 | `member::method` ambiguity | body | |
| 45 | T0045 | `member::qualified` | body | |
| 46 | T0046 | `call::receiver` (no marker; conv from the resolved method; rvalue for sink) + `tape::ImplicitReceiver` + `flow::render_move_error` | body | codes are ch01's |
| 47 | T0047 | `expr::bracket` reading by operand target | body | |
| 48 | T0048 | `wf::member_clashes` (inherent name twice across impls; inherent vs field; assoc fn vs variant) | static | |
| 49 | — | `member::check_visibility` with `Code::N(11)` | body | NoCode: ch08's |
| 50 | T0050 | `pat::check_pat` | body | |
| 51 | T0051 | `pat::bind_let` | body | |
| 52 | — | grammar fact | — | NoCode |
| 53 | T0053 | `exhaust::check_match` (Missing) | body | |
| 54 | T0054 | `exhaust::check_match` (arm not useful) | body | |
| 55 | T0055 | `exhaust::step_budget` | body | plain count normative |
| 56 | — | absent syntax | — | NoCode |
| 57 | T0057 | `expr::operator` (rigid, no bound), `expr::field` T0042, `member::method` T0043, literal T0027, cast T0030, pattern T0050 on rigid types; `tape` Move for non-Copyable rigid | body | |
| 58 | T0058 | `lower::brand_as_type` (ch01 R15d code), `expr::const_param_value` | both | |
| 59 | — | architecture: bodies checked once, `Binding` never inspects a concrete type; test `no_error_depends_on_instantiation` (metamorphic: instantiations do not change diagnostics) | — | NoCode |
| 60 | T0060 | `lower::raises_ty` (any type incl. Param), `ty::fn_ty` equality (raising ≠ non-raising), `one_way_match` never binds never | both | |
| 61 | T0061 | `lower::projection` (a)-(d), `member::assoc_ty` | static + body | |
| 62 | T0062 | `lower::constraint_entries` (fn-only, traits only, well-formed head), `call::check_bounds` (at use), `bounds::holds` Proj arm | both | N0026 stays the resolver's |

**Inherited obligations**

| Source | Obligation | Module::function | v0.1? |
|---|---|---|---|
| ch01 R2 | convention markers at call sites (`&x`, `move x`, `&out x`); receiver exception | `call::conv_marker` (O0002) | yes |
| ch01 R3, R4a(a)-(e), R8 (loop-head merge for moves) | moves and liveness | `flow.rs` (O0003, O0004) | yes (moves only) |
| ch01 R4, R5 | sink moved on every path; set initialised on every return | `flow.rs` | **not in v0.1 M1**: M3 (needs definite-init dataflow) |
| ch01 R6, R7, R9 | exclusivity, overlap, varying stores | FMIR race checker | not in v0.1 M1 (M3) |
| ch01 R10-R13 | `iso`/`imm` conversions, deep `imm`, `iso` extraction, sendability | `expr::field` (imm propagation); the rest FMIR | partial: R11 only |
| ch01 R14 | `secret` composes orthogonally | `lower::quals` | yes |
| ch01 R15-R15e, R16, R18 | brands, `with` fresh brand, kind misuse, `Ref`/`Arena` brand equality, `Own` brand | `lower::brand`, `body::with_stmt`, `subst::one_way_match` Brand (O0015, O0015d, O0016) | yes (equality-based ones); non-escape of arena values (15a) via the tape: M3 |
| ch01 R19, R19a, R19b | scoped results, extents | `lower::scoped` (signature form only); extents FMIR | signature form only |
| ch01 R21-R21d | `Shared` field check, `atomic` placement | `wf::shared_impl` (O0021) | yes (fieldwise, marker) |
| ch02 R1-R3, R5 | `raises` declared; call to raising fn followed by `?`/`else`; `?` on non-raises; `ErrorFrom` one hop; handler after a call only, diverges or yields | `expr::try_expr`, `expr::handler`, `body::raise_stmt` (F0001-F0005) | yes |
| ch02 R9 | contracts part of the declaration | `encode` (token hash of clauses), `body::contract_clause` (bool) | yes |
| ch02 R13 | `extern "c"` no `raises` | `lower::extern_fn` (F0013) | yes |
| ch03 R6 | `as` numeric only | `expr::cast` | yes |
| ch03 R16-R18 | monomorphise/witness decisions | FMIR/OIR | not in v0.1 M1 |
| ch03 R19-R20 | `vector`/`mask` types; `SVec` reserved | `prelude`, `lower::type_app` (D0020) | yes |
| ch03 R21-R24a | array literal typing, `.splat`, `Slice` by range index, `[x; n]` | `expr::array_lit`, `expr::operator_index` (D0021-D0024) | yes |
| ch03 R25 | CHECK positions | `rules::CHECK_SITES` + trace test | yes |
| ch04 R2, R3, R10, R12, R14 | exported requirement over the graph; sealed-op site classification; comptime purity; root-capability construction sites | extension of `fors-resolve::authority` reading `SigStore` | I10 (after M1 exit) |
| ch04 R7, R8 | root-capability opacity; `main`'s nominal parameters | `wf::main_sig`, `expr::struct_lit` (A0007, A0008) | I10 |
| ch04 R27 | `asm_expr` CHECK-only typing | `expr::asm_expr` (A0027) | yes |
| ch04 R7, R13 | manifest policy, lockfile pinning | — | not in v0.1 (needs the manifest) |
| ch05 R6a | `secret` propagation as a type rule | `expr` result quals `|= SECRET` of operands; store to non-secret T0026 | flag propagation only; CT rules FMIR |
| ch08 R11 | member visibility | `member::check_visibility` (N0011) | yes |
| ch08 R22, R23 | no scope lookup; non-names | by construction (`Interner::get`) | yes |

---

## 9. The query DAG

`fors-query` is a generic engine: `QueryKey`, `Revision`, input vs derived
values with a value hash, dependency recording, red-green early cutoff,
explicit in-flight stack for cycle detection with a caller-declared
`on_cycle` recovery value, cancellation (writes nothing), `--stats`. Memo
values are `Arc<dyn Any>`-free: each query type has its own SoA memo.

### 9.1 Node set

| Query | Key | Value hashed from | Reads |
|---|---|---|---|
| `source_text(f)` | FileId | input | — |
| `file_set()` | — | input (sorted paths) | — |
| `parse(f)` | FileId | tree + tokens (existing) | `source_text` |
| `decl_index(f)` | FileId | `DeclTable` (token hashes per row) | `parse` |
| `module_facts(f)` | FileId | header + `use` paths only | `parse` |
| `decl_keys(f)` | FileId | canonical `Vec<DeclKey>`; changes only when the SET of declarations changes | `decl_index` |
| `module_graph()` | — | edges | every `module_facts` |
| `module_exports(m)` | ModuleId | existing `export_signature` text (sorted) | `module_graph`, `decl_index` of the module's files |
| `name_uses(k)` | DeclKey | the `NameUseTable` slice of that declaration (targets rewritten to DeclKeys) | whole-build `resolve` in M1 (§3 fork 14) |
| `decl_arity(k)` | DeclKey | `(SigKind, [GParamKindTag])` from its own Generics tokens + `module_exports` row kinds | `decl_index`, `module_exports` |
| `signature_of(k)` | DeclKey | `(SigId, sig_hash, diags)` | own sig tokens, `name_uses(k)`, `decl_arity` of mentioned items, `assoc_defs`/`impls_for` for projections in its own types |
| `impl_heads(m)` | ModuleId | `(trait DeclKey, HeadKey, impl DeclKey)` triples; changes only when an impl is added/removed/re-headed | `decl_index` of `m` |
| `impls_for(tr, h)` | (trait DeclKey, HeadKey) | sorted impl DeclKeys + merkle of their `sig_hash`es | `impl_heads(module_of(tr))`, `impl_heads(module_of(h))` — two nodes by ch08 R21; prelude impls are a const table |
| `overlap_check(tr, h)` | same | diags | `impls_for`, `signature_of` of each |
| `members_of(h)` | HeadKey | member index slice | `signature_of` of the head and of its inherent impls |
| `candidate_traits(h, m)` | (HeadKey, ModuleId) | trait set | `module_graph`, `impl_heads` of head module, `m`, and `m`'s direct edges |
| `size_edges(k)` | DeclKey | the summary edge set of R14 | `signature_of(k)` |
| `infinite_size()` | — | diags | every `size_edges` (the one whole-build query, as R14 asks) |
| `check_body(k)` | DeclKey | `(BodyFacts, diags)` — a LEAF: nothing reads it | own body tokens, `name_uses(k)`, `signature_of(k)`, `signature_of` of every callee/field/head mentioned, `impls_for` of every bucket looked up, `members_of`, `candidate_traits` |

`normalise_proj` and `holds` are **not** nodes: they are caches keyed on
`TraitWorldRevision`, a `u64` bumped when any `impl_heads` or `assoc_defs`
value hash changes. A body edit never bumps it (the LSP case); an impl edit
clears both caches wholesale (cost measured at I6, §16).

`TyStore` is never invalidated, only appended: a row's meaning is content
(DeclKey bytes, ordinals), never a `DeclId`; `compact()` rebuilds from live
roots at a quiescent point.

### 9.2 What each edit invalidates (the M1 gate (c) contract)

| Edit | token pre-filter | re-executed queries | NOT re-executed |
|---|---|---|---|
| comment / whitespace | no row hash changes | `parse`, `decl_index`, `decl_keys` of the file (values unchanged → green) | everything else |
| body of `f` | `body_hash(f)` | `check_body(f)` only | every signature; every other body |
| private signature of `f` in module `m` | `sig_hash(f)` | `signature_of(f)`; then, iff `SigStore.sig_hash` changed: `check_body` of every declaration in `m` whose `DepSet` contains `f`; `size_edges(f)`, `infinite_size` | importers (`module_exports(m)` unchanged for a private row) |
| public signature of leaf-module item | as above | plus `module_exports(m)` changes → `signature_of`/`check_body` of the importers that depend on that row | bodies that never mention it |
| public signature in a core module | as above | the transitive dependents by recorded `DepSet`, exactly | unrelated modules |
| `type A = T;` in an impl | `sig_hash(impl)` | `signature_of(impl)`, `impls_for` bucket merkle → `check_body` of bodies that normalised through that bucket; `TraitWorldRevision` bump | bodies that never looked up that bucket |
| method body inside that impl | `body_hash(method)` | `check_body(method)` | the impl's `sig_hash` (unchanged) |
| adding an impl of `Tr` for head `H` | `decl_keys(f)`, `impl_heads(m)` | `impls_for(Tr, H)`, `overlap_check(Tr, H)`, `check_body` of bodies that looked up `(Tr, H)`, `candidate_traits(H, *)` for modules with an edge to `m` | bodies using `Tr` on other heads (the test that catches a global impl index) |
| reordering bounds / renaming a gparam / re-spelling a path via alias | `sig_hash(f)` | `signature_of(f)` re-lowers; `SigStore.sig_hash` unchanged → nothing else | all dependents (cutoff) |
| inserting a declaration above `f` | `decl_keys(f)` set changes; `DeclId`s renumber | `decl_keys(file)`; the new declaration's queries; nothing keyed by `DeclKey` moves | `f` and its dependents |

Cached diagnostics are stored `(DeclKey, offset − decl.range_start, code,
site, message)` and rendered at print time from `parse(f)`, so an earlier
edit in the file does not force recomputation of green declarations.
Printing is a walk over `decl_keys` in canonical order taking values from
the memo; output is byte-identical cold or after an edit-and-revert.

---

## 10. Diagnostics and recovery policy

- **One `Diagnostic`**: `{ file: FileId, start, end, code: Code, site:
  u16, message: String }`; `Code::{N, A, T, O, F, D}(u16)`; printed as
  `T0026` etc. by `run_check`'s existing sorted line list.
- **One diagnostic per root cause; exactly one per `check-error` test.**
  Poison, never cascade (§7.10). Every ch09 `check-error` test's first
  detail token must be the code emitted and the emission site's rule must
  be the cited rule.
- **Messages name what the spec requires**: T0026 "expected `T`, found
  `S`" (types rendered by `display.rs` after normalisation); T0039 "cannot
  infer `T`; write `f[T](...)`"; T0043/T0044 list candidates; T0053 names
  one uncovered value; T0055 asks for nesting; T0050 adds `to bind, write
  "let n"`; T0029 "suffix the index" for the multi-`Index` literal case.
- **ch09 R46 (normative)**: a ch01 move error whose move was an implicit
  receiver move renders "`x` was moved by the call `x.finish()` at L:C,
  because `Builder.finish` takes `sink self` (declared at L:C)" — method
  path from `DefTable.key`, both locations from `DefTable.span` and the
  call node, cross-file. `Cause::ImplicitReceiver`'s fields are
  non-optional so the message cannot be omitted; a string test pins it.
- **Bounded output**: one diagnostic per node; 32 per declaration then a
  note; deterministic order (declaration order, then offset).
- **Internal errors** (`I00nn`: normalisation depth, holds budget,
  paranoid-mode invariant) are loud, never a hang, never a silent accept.
- **Cycles** (mutually dependent signatures through a broken premise) yield
  one diagnostic at the lexicographically least `DeclKey` and `TY_ERROR`
  elsewhere; `decl_arity` depending on no other `decl_arity` is the
  acyclicity base (`trait Tr[T: Tr2]` / `trait Tr2[U: Tr]` lowers).

---

## 11. Testing strategy

**Corpus harness** (`crates/fors-check/tests/conformance.rs`, modelled on
`fors-resolve/tests/conformance.rs`): each ch09 test is classified
`Rejected(code, cited_rule)` (exactly one diagnostic whose code AND
emission-site rule match), `Accepted` (zero diagnostics AND
`nodes_typed == nodes_typable`, so an accepted test cannot pass vacuously),
or `Pending(increment)` in an explicit `PENDING_09` list whose length has a
committed upper bound that every increment lowers. The 9 ch01-coded tests
assert `Code::O(rule)` plus the clause letter in the message; the R46 test
asserts the rendered string. `ch09_types_corpus_resolver_view` is retired
when `PENDING_09` is empty. `PENDING_08` empties at I4 (`private_field_
cross_module_rejected`); `PENDING_04` shrinks to rules 7 and 13 at I10.
ch01 (31), ch02 (9), ch03 (13) `check-error` files come on as their rules
are reached, each in its own harness with its chapter letter.

**Property and differential tests that run before FMIR exists:**

| Test | Increment | What it pins |
|---|---|---|
| `intern_is_deterministic` (10k random type DAGs, fixed order → fixed ids) | I1 | store |
| `encode_decode_roundtrip` on every signature the corpus produces | I2 | binary interface |
| `sig_hash_stable_under_reformat`, `_under_bound_reorder`, `_under_gparam_rename`; `_changes_on_param_rename`, `_changes_on_assoc_type_rhs` | I2 | R2, R37, cutoff |
| `sig_hash_mutation_harness`: for every corpus declaration, single-token signature mutations; assert `sig_hash changed ⟺ cold check result of the package changed` | I2, nightly | under-/over-hashing (Incremental's risk 3) |
| `no_infer_variable_is_interned`: every row complete and normal after checking the corpus (`--paranoid`) | I3 | store invariant |
| `structurally_equal_agrees_with_id_equality` at every comparison under `--paranoid` | I3 | equality-by-id (Performance's risk 1) |
| `check_positions_match_ch03_r25`: recorded `(parent, slot, mode)` trace equals `CHECK_SITES ∪ ADDENDA` | I3 | R25 |
| `every_check_error_test_yields_exactly_one_diagnostic` | I3 | recovery |
| `every_deferred_node_is_decided` | I4 | member coverage |
| `method_lookup_memo_is_module_keyed`: three-module build checked twice in one process, both orders | I4 | Fidelity's risk 2 |
| `one_way_match_properties`: bound slots never revised; projections on unbound heads skipped; never binds nothing; `A` never mutated (random P/A) | I5 | R38 |
| `no_error_depends_on_instantiation`: adding/removing call sites of a generic changes no diagnostic inside it | I5 | R59 |
| `usefulness_vs_brute_force_oracle`: ≤3 columns over enums ≤4 variants and bools, 10k random matrices | I7 | R53 |
| `plain_step_count_matches_reference` on 20 hand-built matrices and both R55 tests | I7 | R55 |
| `implicit_and_explicit_receiver_move_produce_identical_tapes` | I8 | R46 |
| `rules_table_covers_1_to_62`, `every_emitted_code_has_a_site`, `traceability_doc_is_current` | I0 | auditability |
| metamorphic: file-order permutation, declaration-order permutation, adding an unrelated module → byte-identical diagnostics and identical `sig_hash`es | I9 | determinism |
| `check_output_identical_cold_vs_incremental` | I9 | printing walk |
| type-directed program generator (invert the typing rules over FIR; assert clean) + typed mutations with expected code and site | I11 | false rejections |

---

## 12. CI plan

**Near-linearity (M1 gate (b)) is gated on deterministic counters, wall
time is secondary.** `fors check --count` prints: nodes visited,
`subst_norm` calls and short-circuits, interns, memo probes and misses
(normalise, holds, method), one-way-match steps, usefulness rows charged,
impl-bucket scans. The generator (`crates/fors-check/tests/scale.rs`,
extending `fors-resolve/tests/scale.rs`) emits corpora at 12.5k / 25k / 50k
/ 100k / 200k lines from one fixed shape distribution that includes generic
code: iterator adaptor chains to depth 16, k ∈ {1, 2, 4, 8} impls per
`(trait, head)`, projection-heavy signatures, constraint entries, closures
into generic calls, matches of width up to 8. Gate: every counter per source
line is flat within 5% across the sizes; the log-log wall-time slope
(single thread, `--no-daemon`, 10 runs, median) is ≤ 1.05 and
`t(200k)/t(100k) ≤ 2.15`. Published per run: the fitted slope, memo sizes,
retained and peak bytes per source byte (budget ≤ 6.0 retained, ≤ 9.0 peak;
today's frontend is ~3.6).

**Single-declaration edit (M1 gate (c)) is gated on the exact re-run set.**
`crates/fors-check/tests/incremental.rs` builds a generated multi-module
package, applies each edit class of §9.2 (comment, body, private signature,
public signature on a leaf module, public signature in a core module,
`type A = T;`, add an impl, insert a declaration above), and asserts that
the set of re-executed `signature_of`/`check_body` keys **equals** the
expected dependent set computed from the recorded `DepSet`s — not a subset.
Plus `adding_an_impl_invalidates_only_its_head_bucket` and
`assoc_type_def_edit_is_signature_level` (the end-to-end twin of the
existing `fors-index` test). Cloud CI runs these (they are counts, not
timings); wall-time gates run only on the pinned M1 box.

**Gate (a)**: the 100k-line generated corpus and the whole conformance tree
check with zero unexpected diagnostics under `-D warnings`.

---

## 13. Ordered increment plan

Sizes are for one agent with the model tier per Marc's rule. Each gate is
named tests or a measurement; the workspace stays green at every step.

**I0 — plumbing (sonnet, ~300 lines, one task).** `Code` widened in
`fors-index::diag` and re-exported; `hash_bytes`, `pub splitmix64`;
`Interner::get`; `NameUseTable::{consumed, finish, target_of}` and
`DeferReason`; `ResolveOutput::{edges, direct_edges_of}`; empty
`fors-fir`/`fors-check`/`fors-query` crates; `rules.rs` with 62 rows all
`Unimplemented`, `EMIT_SITES`, `traceability` generator writing
`docs/spec/09-types-traceability.md` on demand; `fors check` calls
`check_build`, which emits nothing.
GATE: `cargo test --workspace` green with warnings denied; every existing
conformance test unchanged (`ch09_types_corpus_resolver_view` included);
`rules_table_covers_1_to_62`; a CI grep that `crates/fors-fir/src` mentions
neither `fors_syntax` nor `fors_lex`; `scale_100k_lines` re-run and its
numbers committed as the baseline.

**I1 — `fors-fir` (opus for `ty.rs`/`subst.rs`/`encode.rs`, sonnet for the
pools and tests; ~1.5k lines).** `TyStore`, `ConsTable`, pools, `SigStore`
family, `DeclKeyTable`, `HeadKey`, `encode`/`decode`/`sig_hash`,
`one_way_match`, `subst_norm` over hand-built types, `constval`.
GATE: `intern_is_deterministic`; `one_way_match_properties`;
`encode_decode_roundtrip` on 10k random signatures; `sig_hash` invariants
(reformat, bound reorder, gparam rename) and changes (param rename, assoc
RHS); a standalone spike `spikes/fir-normalise/` over synthetic FIR (adaptor
chains depth 64, k impls per head, projections on projections, mutually
recursive impls) showing `subst_norm` calls, memo misses and match steps
linear in chain depth and independent of k beyond the bucket scan — this
runs BEFORE any checker code and either validates the memo keys or changes
them while it is free.

**I2 — signatures and whole-head well-formedness (opus; ~2k lines).**
`DefTable`, prelude rows, `lower.rs`, `ImplIndex`, `wf.rs`: R3-R8, R11,
R13-R19, R21 (prerequisite, no-Output), R23 (impl check), R24, R25, R48,
R61 (static), R62 (static). No bodies.
GATE (≈52 tests): R11 (2), R13 (2), R14 (2 rejected + 2 accepted), R15 (1),
R16's `assoc-type-bound-not-a-trait-rejected` and `self-receiver-wrong-type-
rejected`, R17 (6 T0017 + `operator-trait-has-no-output-rejected`), R18 (6),
R19 (4), R21 `indexmut-without-index-rejected`, R23 `copyable-with-own-
field-rejected`, R24 (1), R25 (2), R48 (3), R61 (10), R62's three static
rejections; accepted members of those groups stay clean; `fors check` still
clean on every other test (explicit no-regression assertion).
`sig_hash_mutation_harness` on the corpus. MEASUREMENT: signature lowering
over the 100k corpus ≤ +50% time and ≤ +1.5 B/source byte over the I0
baseline.

**I3 — non-generic bodies (opus for `expr.rs`/`call.rs` skeleton, sonnet
for statement forms; ~2.5k lines).** `BodyCx`, `synth`/`check`, R26-R37,
R42 (non-generic), R47 index reading, R49, `DepSet` recording, `UseTape`
emission, calls with zero parameters to determine (non-generic fns, struct
literals of non-generic structs), operators over built-in impls,
`for` over ranges/arrays/slices, `CHECK_SITES`.
GATE (≈24 tests): R1 (2), R7 `fn-item-as-value-accepted`, R9 `nominal-
structs-distinct-rejected`, R10 `array-to-slice-rejected`, `never-coerces-
accepted`, R22 (1), R27 `int-literal-to-float-rejected`, `literal-checks-
to-u8-accepted`, R29 `literal-left-operand-accepted`, `mixed-width-operands-
rejected`, `operator-missing-impl-rejected`, R30 (1), R31 `for-over-non-
iterable-rejected`, `return-value-mismatch-rejected`, R32 (3), R33 `let-
never-rejected`, R34 `dot-lit-in-synth-rejected`, `struct-literal-missing-
field-rejected`, R35 `closure-synth-unannotated-rejected`, R36 (1), R37
`named-arg-wrong-label-rejected`, R42 (1); `check_positions_match_ch03_
r25`; `every_check_error_test_yields_exactly_one_diagnostic` over the
tests now on; `no_infer_variable_is_interned`. MEASUREMENT, first time:
the 100k non-generic corpus checks clean and the counter gate is flat over
12.5k-200k. A layout mistake surfaces here, not after generics.

**I4 — traits, impls, member lookup, no projections (opus; ~1.5k
lines).** R12 for non-projection subjects, `holds`, `impl_lookup`, R16/R17
method bodies (provided methods with `Self` rigid), R21-R23 through the
index, R43-R46 typing side, R48 use side, ch08 R11 enforcement, method memo.
GATE (≈30 tests; every projection-dependent test of these groups, such as
R20's `neutral-projection-does-not-match-concrete-impl-rejected`, is I6's):
R12 (2), R16 `provided-method-accepted`, R21
(`compound-assign-via-add-accepted`, `index-two-index-types-accepted`,
`indexmut-output-is-index-output-accepted`, `operator-via-impl-accepted`),
R23 `copyable-fieldwise-accepted`, R29 `index-literal-with-two-impls-
rejected`, `index-suffixed-with-two-impls-accepted`, R43 (`inherent-
before-trait-accepted`, `method-on-bound-accepted`, `trait-method-without-
edge-rejected`), R44 (1), R45 (1), R46's typing-only tests (`inout-
receiver-unmarked-accepted`, `let-receiver-unmarked-accepted`, `sink-
receiver-rvalue-accepted`, `explicit-move-receiver-accepted`, `no-auto-
deref-own-rejected`), R47 (1), R10 `concrete-to-dyn-accepted`; ch08's
`private_field_cross_module_rejected` (`PENDING_08` empty);
`every_deferred_node_is_decided`; `method_lookup_memo_is_module_keyed`.

**I5 — generic calls and generic bodies (opus; ~1.5k lines).** R38-R41,
R28, R35 against `fn` types, R37 `bare_op`, R57-R60, R40 brands, `with`
fresh brands, R13 const arguments at calls.
GATE (≈26 tests): R38 (`binding-never-revised-rejected`, `infer-from-
expected-type-accepted`, `infer-from-first-argument-accepted`), R39 (3),
R40 (2), R41 (`callable-bound-closure-accepted`, `closure-before-its-type-
source-rejected`), R7 `generic-fn-value-without-args-rejected`, R28 (1),
R33 `never-not-inferred-rejected`, R34 `struct-literal-args-from-expected-
accepted`, R35 `closure-checked-against-fn-type-accepted`, R9 `brand-
identity-mismatch-rejected`, R27 `literal-against-param-rejected`, R42
`field-on-type-param-rejected`, R57 (`unbounded-op-on-param-rejected`,
`copy-with-copyable-accepted`), R59 (1), R60 (2), R58 typing side;
`one_way_match` corpus assertions; `no_error_depends_on_instantiation`.

**I6 — associated types, projections, normalisation, constraint entries
(opus; ~1.2k lines).** R16 (`type A;` bounds), R17 RHS checks, R20, R61
use side, R62 use side, R12 for projection subjects, R43 on projections,
R14's associated-type nodes, R25's assoc-type exclusion.
GATE (≈40 tests): all remaining R16, R17, R20 (8), R61, R62; R14 `recursive-
through-assoc-type-rejected`, `projection-field-behind-own-accepted`,
`projection-in-struct-field-accepted`; R27 `literal-against-neutral-
projection-rejected`; R31 (`for-element-type-from-item-accepted`, `-mismatch-
rejected`, `for-over-rigid-iterator-accepted`, `for-over-rigid-non-
iterator-rejected`); R38 (`map-sum-closure-checked-accepted`, `projection-
arg-before-head-accepted`, `-final-check-rejected`, `projection-result-
against-expected-accepted`); R39 `param-only-under-projection-*`; R41
`closure-before-its-iterator-rejected`; R43 `method-on-projection-via-trait-
bound-accepted`; R57 projection tests; R25 `dyn-trait-with-assoc-type-
rejected`; R18 `impl-param-only-in-assoc-type-rejected`, `projection-in-
impl-head-rejected`; R19 `overlap-ignores-assoc-types-rejected`.
MEASUREMENT: the adversarial-shape counter suite from I1's spike, now
through the real checker; and the cost of clearing the `TraitWorldRevision`
caches on a cold 100k check (decision rule in §16).

**I7 — patterns and exhaustiveness (sonnet with an opus review of
`exhaust.rs`; ~900 lines).** R50-R56.
GATE (16 tests): R50 (4), R51 (1), R53 (6), R54 (3), R55 (2);
`usefulness_vs_brute_force_oracle`; `plain_step_count_matches_reference`
asserting the count itself on both R55 tests.

**I8 — flow pass (opus; ~800 lines).** `flow.rs` for ch01 R3, R4a(a)-(e),
R8's loop-head merge for moves, R46's message; ch01's `conv-missing-*`
marker tests.
GATE: the 9 ch01-coded ch09 tests plus `implicit-receiver-move-accepted`,
`sink-receiver-copyable-not-moved-accepted`; the R46 string assertion;
`implicit_and_explicit_receiver_move_produce_identical_tapes`; `PENDING_09`
empty — **186/186**. From ch01: the 6 `01.R2` marker tests and the two
`01.R1` tests.

**I9 — `fors-query` and the M1 exit (opus for `db.rs`, sonnet for the
query wrappers; ~1.5k lines).** The engine; the node set of §9.1 with
`resolve()` wrapped; declaration-relative cached diagnostics; the printing
walk; `--stats`.
GATE: M1 (a) 100k corpus clean; (b) the counter gate + wall slope ≤ 1.05
+ the per-declaration histogram; (c) `single_declaration_edit_rechecks_
exactly_its_dependents` over the eight edit classes of §9.2,
`adding_an_impl_invalidates_only_its_head_bucket`, `assoc_type_def_edit_
is_signature_level`, `check_output_identical_cold_vs_incremental`;
metamorphic determinism tests.

**I10 — other chapters' obligations (sonnet per chapter, opus for ch04;
~1k lines).** ch02 R1-R5, R13; ch03 R6, R19-R24a; ch04 R2, R3, R7, R8, R10,
R12, R14, R27; ch01 R14-R18, R21-R21d (equality/marker forms).
GATE: `PENDING_04` = {7, 13}; ch02's 9 and ch03's 13 `check-error` tests;
the type-dependent subset of ch01's 31 (scoped in this increment from the
rule list above, not guessed here).

**I11 — soundness at scale (sonnet for the generator, opus for triage;
ongoing).** Type-directed program generator over FIR, typed mutations with
expected code and site, 10^6 programs with zero false rejections and zero
panics; every exception triaged as generator bug or checker bug, never
waived.

Parallel body checking (§3 fork 18) is switched on only if I3's
measurement shows single-thread cost above 150 ms for 100k lines; the store
layering makes it a flag flip plus a deterministic diagnostic merge.

---

## 14. Open questions for Marc (each with a recommendation; work proceeds on the recommendation)

> **Dispositions, 2026-09-20 (orchestrator).** Questions 1, 2, 3, 7, 8, 9, 10
> and 11 are engineering calls, not owner calls: their recommendations are
> ACCEPTED as written and implementers follow them without asking again.
> Questions **4, 5 and 6 are reserved for Marc**: together they are the policy
> of `decl_fingerprint()` (PLAN §5, his learning-mode contribution point), and
> they decide what a given edit invalidates. I1 lands the function with its
> callers, its tests and a documented stub; Marc writes the body, and the three
> recommendations above are the fallback if he delegates it.



1. **Diagnostic letters for ch01/ch02/ch03.** Those chapters have no code
   scheme; ch09 R46 says "the code stays ch01's". Recommendation: `O00nn`
   (ownership), `F00nn` (failure), `D00nn` (determinism/numerics), rule
   number = code as elsewhere, clause letters in the message; the corpus
   `detail` lines keep citing `ch01 R4a(a)` and the harness matches chapter
   + number.
2. **BLAKE3.** PLAN §4.1 says BLAKE3; zero-dependency means writing it.
   Recommendation: FNV-128 + SplitMix64 for every in-process key through
   M2 (the threat model is a compiler talking to itself); write an
   in-tree BLAKE3 in `fors-hash` before M4's bit-identical-rebuild gate or
   any shared content-addressed cache, since a non-cryptographic hash is
   collision-attackable there. A birthday-bound sanity run (10^5
   signatures + 10^7 mutations, zero collisions) is in I2.
3. **`fors-intern` extraction** (so `fors-fir` does not link the parser).
   Recommendation: not now; a CI grep enforces the direction; extract when
   the `.fmod` reader lands (M2).
4. **A `const` declaration's comptime value in its signature hash.**
   Rule 2 excludes it "unless used as a const argument". Recommendation:
   include it always (over-invalidates dependents of a changed constant
   used only as a value; simpler and safe); revisit if measurement shows
   it matters.
5. **Generic-parameter names out of the hash** (alpha-equivalence).
   Recommendation: yes; nothing observable depends on them (R38(a) is
   positional); T0039's message reads the current name.
6. **Sorted bound lists in the canonical encoding** (so `T: Eq + Ord` ≡
   `T: Ord + Eq`, including for R17's "same bounds"). Recommendation: yes.
7. **`MAX_DIAGS_PER_DECL = 32`, `NORMALISE_DEPTH_MAX = 256`.**
   Recommendation: accept as drafting defaults, tune on measurement.
8. **Parallel body checking in M1 or M2.** Recommendation: M2 unless I3's
   single-thread number misses 150 ms at 100k lines.
9. **`PENDING_04` rules 7 and 13** need the manifest. Recommendation: they
   stay pending until the manifest chapter exists; not the checker's.
10. **`ErrorFrom`'s method shape** is not written anywhere. Recommendation:
    `trait ErrorFrom[E] { fn from(sink e: E) -> Self; }` as the prelude
    row until the std surface chapter says otherwise.
11. **Incremental resolution per module** (today `resolve()` is
    whole-build). Recommendation: M2, with the p95 gate; M1's gate (c)
    is about checker queries and is exact without it.

---

## 15. What this design does not cover

FMIR lowering and everything downstream (OIR, LIR, codegen, the dev and
release backends); the FMIR interpreter and comptime beyond literal
folding (`constval` handles integer/bool/Str literals and the trapping
integer operators — enough for R13/R53 in v0.1, and a richer const argument
gets a distinct `I0003 not comptime-evaluable in v0.1` diagnostic that a
test requires to be absent corpus-wide); contract proving and the
`.proved`/`.off` policies (contract clauses are only typed as `bool`);
ch01's exclusivity, region, sendability and definite-initialisation rules
(R4-R9, R12-R13, R19a-b) and the race checker; ch05's constant-time
verification beyond the `secret` flag; GPU/`spmd`/`kernel`/`simd`
region rules and ch03 R16-R18 monomorphisation decisions; `@specialize`;
the LSP protocol and the daemon process (only the `Db` API shape:
`Sync`, cancellable); incremental re-lexing/re-parsing of a file;
per-module incremental resolution; std itself (the prelude is the only
built-in surface); the manifest, lockfile and capability policy (ch04 R7,
R13); formatting.

---

## 16. What is unproven, and what would prove each wrong

The five decisions most likely to be wrong, in order:

1. **"Every interned type is normal" holds in practice.** A leak (a
   signature lowered before the impl index is complete; a body-local type
   built from a global one without `subst_norm`; a stale normalisation memo
   after an impl edit) gives a silent false T0026 or a wrong accept.
   Disproof: `--paranoid`'s `structurally_equal_agrees_with_id_equality`
   over the whole corpus and the generated ones fails. Containment already
   in the design: signatures are lowered in a fixed order and projections
   are normalised lazily on first `subst_norm` after `freeze`; the caches
   are cleared wholesale on `TraitWorldRevision` bump.
2. **The memo keys keep normalisation and bound satisfaction linear on
   real generic code.** Disproof: I1's spike or I6's adversarial suite
   shows `subst_norm` calls or memo misses growing with adaptor depth
   squared, or with k beyond the bucket scan. Fix while free: change
   `HeadKey`'s discriminator or the `(x, tr)` memo key.
3. **`TraitWorldRevision` wholesale clearing is cheap enough.** Disproof:
   at I6, clearing plus rebuilding both caches after one impl edit costs
   more than ~2 ms on the 100k corpus. Fix: promote `holds` to a DAG node
   keyed `(TyId, TraitRefId)` with recorded `impls_for` dependencies — the
   key already has the right shape.
4. **The canonical encoder includes exactly the right things.**
   Under-hashing is a stale-accept correctness bug; over-hashing eats the
   M1 gate. Disproof: `sig_hash_mutation_harness` finds an asymmetry
   (`hash changed` xor `result changed`) for any single-token signature
   mutation across the corpus. Any asymmetry is an encoder bug, never a
   test bug.
5. **Whole-file `parse`/`decl_index` above per-declaration queries is
   fine for M1.** Disproof: a 20k-line single file with a one-character
   body edit shows p95 of `parse + decl_index + decl_keys` above 3 ms,
   which would eat the M2 frame. Measured in I9 with the existing `scale.rs`
   generator; if it fails, incremental reparse moves from M2 into M1's tail.

Assumptions not verified and flagged: the frontend figures (95k lines in
48 ms, ~3.6 B/source byte) are the task's, from the `#[ignore]`d
`scale_100k_lines`, not re-run here; every per-node and per-declaration
time budget in §12 is an estimate from the data layout, not a measurement;
the prelude's `ErrorFrom` shape (§14 Q10).

---

## 17. Amendments from the I1 normalisation spike (2026-09-20)

`spikes/fir-normalise/` ran before any checker code, as §13 I1 required. It
changed one decision of this document and added two that were missing. The
counters it prints (`cargo run --release` in that directory) are the evidence.

1. **The substitution memo key of §7.5 was unsound, not merely slow.**
   `(TyId, TraitRefId)` gives a WRONG ANSWER: with
   `impl[T] Iter[C] for Vec[T] { type Item = T; }`, the queries `Vec[i32].Item`
   and `Vec[u8].Item` share one `TraitRefId` and one right-hand side
   `Param(impl, 0)`, so the second reads the first's answer. `impl_lookup`
   binds impl parameters from the **self type** as well as the trait
   arguments, so the *binding* — not the trait reference — identifies the
   question. The key is now `(TyId, BindingKey)` over an interned binding.
   The spike's witness run prints `DesignTraitRef -> WRONG ANSWER`,
   `InternedBinding -> SOUND`; `fors-fir` implements the latter.
2. **Linearity in chain depth holds only for a bounded set of trait
   arguments.** A chain asked under a widening set of arguments (spike shape
   Y) is Θ(depth²) in *distinct* questions with every memo enabled, so no
   memo can flatten it. `NORMALISE_DEPTH_MAX` does not bound it, because the
   depth of each question is fine; the count is not. **I6 must therefore
   carry a per-query work budget — memo misses per top-level normalisation —
   and report T0055-style "ask for this to be split" rather than grinding.**
3. **Impl buckets need an exact index, not only a head bucket.** Shape Z (k
   impls in one `(trait, HeadKey)` bucket, distinguished only deep in the
   self type) costs k²/2 match steps per query: 131 840 steps at k = 512.
   **I4 must consult an exact `(trait, self TyId)` map before the bucket
   scan**, which makes every concrete impl one probe and leaves the scan for
   genuinely generic heads.

Items 2 and 3 are gates on their increments, not advice: I4 and I6 are not
green until the spike's shapes Y and Z are re-run against the real
`fors-fir`/`fors-check` and stay inside the stated bounds.
