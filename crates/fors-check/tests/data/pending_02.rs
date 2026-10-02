// Generated beside the harness: the ch02 (`02-failure`) corpus tests the
// checker does not yet decide, each with why. `pending_02_is_shrinking`
// asserts the bound never rises; an increment deletes rows, never adds them.
//
// I10 (half A) created this table EMPTY. Design §13's I10 GATE turns every
// ch02 `check-error` test on, and all ten are on: R1 (four files: an
// unhandled call, `?` in a `main` with no `raises`, `raise` in a non-raising
// function, a `raise` operand of the wrong type), R2, R3, R5, R9, R10 and
// R13. The design counts nine; the tenth is R10's `.proved` contract, which
// this compiler decides too (it has no proof engine, so under `.proved` no
// contract is ever discharged and every one is the compile error R10
// requires). Of the ten, one reports a code that is NOT `F00nn`
// (`CH02_CODED_ELSEWHERE` in the harness says which and why), and one draws
// diagnostics of another chapter beside its own (`CH02_ALSO_SPEAKS`).
const PENDING_02_MAX: usize = 0;
const PENDING_02: &[(&str, &str)] = &[];
