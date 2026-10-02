# ch05 conformance corpus — the IR contract

Each test cites its rule as `05.Rk`; ch05 has no diagnostic-code letter
(`UNLETTERED_CHAPTERS` in `tools/specpack/gen.py`), so `detail` is free text,
not a coded payload. Directives and expectation kinds are
`tests/conformance/README.md`'s.

The authoritative list of names is `docs/spec/05-ir-contract.md`'s
"Conformance tests" section (22 names). Every file here parses clean under
`fors parse` and is silent under `fors check` today
(`crates/fors-check/tests/conformance.rs`'s `ch05_ir_corpus_checker_view`).

ch05 is normative for the **compiler**, not the surface language: its rules
are enforced by `fors-fmir`'s verifier over lowered FMIR, a later phase than
`fors check` (parse + resolve + `fors-check` only — it never calls
`fors-lower` or `fors-fmir::verify`, by the architectural split
`docs/design/fmir-interpreter.md` section 2 states: the verifier must not
see the checker, so nothing wires the other way either). Two kinds of file
therefore both exist here as `expect: parse-ok`, not as unwritten names:

- **IR-only / lowering-reachable** (16 files): the rule is observable only
  once FMIR exists. Each file is the smallest legal Fors program whose
  eventual lowering would reach the construct the rule polices (an
  allocation, a `secret`-carrying value, a `parallel { spawn .. }` region, an
  `asm` block), and `detail` names the `crates/fors-fmir` unit test or
  `tests/negative_corpus/*.fmir` fixture that pins the rule at the IR level
  today — or, where none exists yet, says so honestly as a GAP (matching
  `docs/design/fmir-interpreter.md` section 8.1's own gap list).
- **Source-reachable, pending** (6 files): the rule's violation is a real
  Fors program (secret-derived branch/index, trapping op on secret, `secret`
  into `@device`, …), already pinned at FMIR by a `crates/fors-fmir` unit
  test, but `expect: check-error` is not yet true of `fors check` for the
  reason above. These six are listed in `PENDING_05`
  (`crates/fors-check/tests/data/pending_05.rs`), which `fors-check`'s
  harness asserts stays silent and never grows past its bound — mirroring
  `PENDING_09`'s shrinking invariant, except every row here is pending an
  architectural integration increment, not a type-checker increment.

## Present (22)

- `asm-ct-audited-enters-inventory` — IR-only
- `asm-input-pointer-unknown-alias` — IR-only
- `asm-no-reorder-across-block` — IR-only
- `asm-opaque-region-effects` — IR-only
- `asm-secret-input-taints-outputs` — pending (`PENDING_05`)
- `autovectorizer-scope-limit` — IR-only
- `backend-bitforbit-agreement` — IR-only
- `ct-denylist-rejected` — IR-only
- `ct-no-branch-or-index-on-secret` — pending (`PENDING_05`)
- `declassify-requires-unsafe` — IR-only
- `detach-capture-explicit` — IR-only
- `detach-no-use-after-sync` — IR-only
- `dwarf-companion-unsigned` — IR-only
- `ir-verify-alias-missing-rejected` — IR-only
- `ir-verify-alias-source-five-only` — IR-only
- `ir-verify-secret-fields` — IR-only
- `secret-forbidden-in-device` — pending (`PENDING_05`)
- `secret-propagates` — pending (`PENDING_05`)
- `secret-raise-condition-rejected` — pending (`PENDING_05`)
- `secret-trapping-op-rejected` — pending (`PENDING_05`)
- `serial-elision-always-legal` — IR-only
- `tile-ops-fmir-only` — IR-only

## Pending (0)

None: F0 wrote every name ch05 lists. "Pending" above describes
*enforcement*, not *existence* — see `PENDING_05` for which six files
`fors check` does not yet decide, and why.

## Change rule

A test is ground truth for the rule it cites: change or delete it only
together with that spec rule or `PENDING_05`'s own row, never to make an
implementation pass.
