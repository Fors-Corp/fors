// Generated beside the harness: the ch03 (`03-numerics`) corpus tests the
// checker does not yet decide, each with why. `pending_03_is_shrinking`
// asserts the bound never rises; an increment deletes rows, never adds them.
//
// I10 (half A) created this table EMPTY: design §13's I10 GATE turns all
// thirteen ch03 `check-error` tests on, and all thirteen report their code —
// R1 (D0001), R4 (D0004), R5 (D0005), R8 (D0008), R9 (D0009), R15 (D0015),
// R18 (D0018), R20 twice (D0020), R21 (D0021), R22 (D0022), R24 (D0024) and
// R25 (D0025). One of them draws a diagnostic of another chapter beside its
// own, and three accepted (`parse-ok`) files draw one too; the harness's
// `CH03_ALSO_SPEAKS` names each with the clause the FILE itself breaks.
const PENDING_03_MAX: usize = 0;
const PENDING_03: &[(&str, &str)] = &[];
