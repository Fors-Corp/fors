// Generated beside the harness: the ch04 (`04-authority`) corpus tests the
// build does not yet decide, each with why. `pending_04_is_shrinking`
// asserts the bound never rises; an increment deletes rows, never adds them.
//
// I10 (half B) created this table. Design §13's I10 GATE reads "`PENDING_04`
// = {7, 13}", written against the resolver's PRE-round-5 numbering of
// chapter 4 (`fors-resolve/tests/conformance.rs`'s own `PENDING_04`: 7 =
// "needs the manifest (per-target/per-dependency policy)", 13 = "needs the
// manifest (lockfile capability pinning)") and §8's row "ch04 R7, R13 |
// manifest policy, lockfile pinning | not in v0.1 (needs the manifest)".
// Mapped onto today's chapter and corpus, that is the MANIFEST: the two
// files below that carry a `//! manifest:` directive and whose verdict is
// that manifest's (R2b, R3). No corpus file tests lockfile pinning
// (R17-R19). Two more rows are not the checker's to decide, each named
// with its owner: R14's step budget is comptime EVALUATION (FMIR F9; a
// second evaluator in the checker is exactly what R11 forbids), and one
// directory test's layout breaks ch08 R24 before ch04 is reached.
const PENDING_04_MAX: usize = 4;
const PENDING_04: &[(&str, &str)] = &[
    (
        "comptime-budget-exceeded-named",
        "ch04 R14: exceeding COMPTIME_STEP_BUDGET is a fact of EVALUATING the loop (1e8 \
         iterations), which is FMIR F9's comptime interpreter; R11 forbids a second comptime \
         path, so the checker must not count steps itself",
    ),
    (
        "policy-subset-enforced",
        "ch04 R3: `checked requirement ⊆ policy` needs the manifest's per-target policy; the \
         corpus README calls the `manifest:` directive a placeholder schema and no crate reads a \
         manifest yet (design §8: \"not in v0.1 (needs the manifest)\")",
    ),
    (
        "sealed-holder-package-must-be-named",
        "ch04 R2b: which packages may hold `ffi` is the manifest's `[capabilities.ffi]` list; \
         with no manifest model the accepted twin (`vendor` permitted) and this file are the \
         same program, so nothing can tell them apart (design §8: needs the manifest)",
    ),
    (
        "sealed-extern-reexport-needs-ffi",
        "corpus layout, ch08 R24: the directory test's `holder.fors` declares `module \
         vendor.blas;` and `main.fors` declares `module app.caller;`, so the resolver reports \
         N0001 twice, `use vendor.blas;` is N0004 and the call's path N0014 — the callee never \
         resolves, so R2a's \"a call to a pub extern from another module is a use of ffi\" has \
         no call to judge. The rule itself is implemented (A0002, `authority::authority_call`) \
         and proved by `probes.rs`'s `i10b_sealed_extern_call_needs_ffi_in_the_caller`; the \
         file needs its owner's rename",
    ),
];
