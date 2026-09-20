//! Non-terminator instructions (design §3.1: "insts: InstPool, // SoA: op, a,
//! b, c, ty, site") plus the side tables a handful of opcodes need beyond the
//! uniform `(a, b, c)` shape — exactly the way design §3.3 already gives
//! calls their own `CallRow` rather than forcing `convs`/`args` through
//! `a`/`b`/`c`. See `op.rs`'s module docs for the full per-group `a`/`b`/`c`
//! table.

use std::ops::Range;

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::Conv;
use fors_fir::ty::TyId;
use fors_index::interner::Symbol;

use crate::alias::AliasSeedPool;
use crate::ids::{BlockId, InstId, SiteId, ValId};
use crate::op::Op;

/// One non-terminator (or, inside `BlockRow::term`, exactly one terminator)
/// row. `a`/`b`/`c` are raw `u32` slots, not `ValId`, because several
/// opcodes pack a non-`ValId` index there (a place, a side-table index, a
/// block) — `op.rs`'s table is the ground truth for what each slot means for
/// a given `op`.
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct InstRow {
    pub op: Op,
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub ty: TyId,
    pub site: SiteId,
}

/// Clamps a data-carried `Range<u32>` to `0..len`, and to the empty range
/// when it is inverted. Every pool accessor whose range comes out of an
/// instruction slot or a decoded row goes through this: an out-of-range or
/// inverted range means the FMIR is malformed, which is `verify()`'s finding
/// to report, not a panic to take (design's `--verify-each` is a diagnostic
/// pass, and `encode.rs::safe_remap` fixes the same rule for `BlockId`s).
pub(crate) fn clamp_range(range: Range<u32>, len: usize) -> std::ops::Range<usize> {
    let start = (range.start as usize).min(len);
    let end = (range.end as usize).min(len).max(start);
    start..end
}

/// Which declaration a `call_direct`/`call_witness`/`call_closure`/
/// `intrinsic` invokes. The four call opcodes already discriminate *which*
/// of these shapes applies, so `Callee` itself carries no redundant tag
/// beyond what `Op` already gives; `reduce_tree`'s combining function
/// (design §3.9) is also a `Callee`, since "the shape is a pure function of
/// `(n, B, L)`" needs exactly the same "what do I call" question a
/// `call_direct`/`call_closure` already answers. [decision: `Callee` is a
/// simplified stand-in for design §4.1's checker-facing `Callee` enum (D2) —
/// `Witness` here is `{table, method}` rather than
/// `{trait_def, method: DefId, self_ty: TyId, args: ArgsId}`, since witness
/// tables are not built before the checker exists; `Intrinsic` names the
/// callee by `Symbol` with no closed-table check, since the closed intrinsic
/// table is `fors-interp::intrinsic.rs`'s (F1+), not this crate's]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Callee {
    Direct(DeclKeyId),
    Witness { table: u32, method: u16 },
    Closure(ValId),
    Intrinsic(Symbol),
}

/// design §3.3's literal `CallRow`, plus the parallel `arg_convs` table that
/// realises "`convs[i] ∈ {Let, Inout, Sink, Set}`": `args` indexes both
/// `operands` (the `ValId`s) and `arg_convs` (their conventions) in lockstep,
/// so one range does the job of the design's two (`args`, `convs`).
/// [decision: one shared range instead of two independently-lengthed ones —
/// an argument always has exactly one convention, so the ranges could never
/// legitimately differ in length]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CallRow {
    pub callee: Callee,
    pub args: Range<u32>,
}

/// `reduce_tree { op, xs, identity, b, l, site }` (design §3.9). `identity`
/// uses `ValId(ABSENT)` for "none", matching this crate's uniform absent
/// sentinel rather than a fifth `Option<ValId>` shape.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ReduceRow {
    pub op: Callee,
    pub xs: ValId,
    pub identity: ValId,
    pub b: u32,
    pub l: u32,
}

/// `switch_discr`'s arm list: `(case value, target)` pairs plus the default.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SwitchRow {
    pub discr: ValId,
    pub default: BlockId,
    pub arms: Range<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SwitchArm {
    pub value: i64,
    pub target: BlockId,
}

/// The non-terminator instruction stream plus its 1:1 `AliasSeed` column
/// (design §3.4a) and the side tables `call_direct`/`call_witness`/
/// `call_closure`/`intrinsic`, `reduce_tree` and (via [`crate::block`])
/// `switch_discr` need.
#[derive(Clone, Debug, Default)]
pub struct InstPool {
    rows: Vec<InstRow>,
    pub aliases: AliasSeedPool,
    pub operands: Vec<ValId>,
    pub arg_convs: Vec<Conv>,
    pub calls: Vec<CallRow>,
    pub reduces: Vec<ReduceRow>,
    pub switches: Vec<SwitchRow>,
    pub switch_arms: Vec<SwitchArm>,
}

impl InstPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Pushes a row and its alias seed together — the two `Vec`s must never
    /// drift out of lockstep, so there is no bare "push a row" that skips
    /// the seed.
    pub fn push(&mut self, row: InstRow, seed: crate::alias::AliasSeed) -> InstId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        self.aliases.push(seed);
        InstId(i)
    }

    pub fn row(&self, id: InstId) -> InstRow {
        self.rows[id.index()]
    }

    /// [`InstPool::row`] for an `InstId` derived from a `BlockRow`'s
    /// `first_inst`/`inst_len` (or any other row's data), which arbitrary FMIR
    /// may leave pointing past the end.
    pub fn try_row(&self, id: InstId) -> Option<InstRow> {
        self.rows.get(id.index()).copied()
    }

    /// The rows a `BlockRow`'s `first_inst`/`inst_len` names. `range` is
    /// **data**, not an index this crate's own iteration produced (a
    /// hand-written fixture, a decoded wire message or a fuzzer can put any
    /// `u32` pair in a `BlockRow`), so it is clamped to the pool rather than
    /// panicking — `verify()` and `dump()` must stay total over any
    /// `DeclFmir` these types can express (see `encode.rs::safe_remap`).
    pub fn slice(&self, range: Range<u32>) -> &[InstRow] {
        &self.rows[clamp_range(range, self.rows.len())]
    }

    pub fn push_operands(&mut self, vals: &[ValId], convs: &[Conv]) -> Range<u32> {
        debug_assert_eq!(
            vals.len(),
            convs.len(),
            "an argument always has exactly one convention"
        );
        let start = self.operands.len() as u32;
        self.operands.extend_from_slice(vals);
        self.arg_convs.extend_from_slice(convs);
        let end = self.operands.len() as u32;
        start..end
    }

    /// For opcodes (like `agg_new`) whose spilled operands carry no
    /// per-entry convention.
    pub fn push_plain_operands(&mut self, vals: &[ValId]) -> Range<u32> {
        let start = self.operands.len() as u32;
        self.operands.extend_from_slice(vals);
        let end = self.operands.len() as u32;
        start..end
    }

    /// A spilled operand list. Clamped like [`InstPool::slice`]: `range`
    /// comes from an instruction's own `a`/`b` slots, which arbitrary FMIR is
    /// not required to keep in range or even ordered.
    pub fn args(&self, range: Range<u32>) -> &[ValId] {
        &self.operands[clamp_range(range, self.operands.len())]
    }

    pub fn push_call(&mut self, row: CallRow) -> u32 {
        let i = self.calls.len() as u32;
        self.calls.push(row);
        i
    }

    pub fn push_reduce(&mut self, row: ReduceRow) -> u32 {
        let i = self.reduces.len() as u32;
        self.reduces.push(row);
        i
    }

    pub fn push_switch_arms(&mut self, arms: &[SwitchArm]) -> Range<u32> {
        let start = self.switch_arms.len() as u32;
        self.switch_arms.extend_from_slice(arms);
        let end = self.switch_arms.len() as u32;
        start..end
    }

    pub fn push_switch(&mut self, row: SwitchRow) -> u32 {
        let i = self.switches.len() as u32;
        self.switches.push(row);
        i
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (InstId, InstRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (InstId(i as u32), *r))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alias::AliasSeed;
    use crate::ids::SiteId;
    use crate::op::ArithMode;
    use fors_fir::ty::TY_UNIT;

    fn row(op: Op) -> InstRow {
        InstRow {
            op,
            a: crate::op::NO_OPERAND,
            b: crate::op::NO_OPERAND,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        }
    }

    #[test]
    fn push_keeps_rows_and_aliases_in_lockstep() {
        let mut pool = InstPool::new();
        pool.push(row(Op::Add(ArithMode::Trap)), AliasSeed::None);
        pool.push(row(Op::Alloc), AliasSeed::Own(crate::ids::PlaceId(0)));
        assert_eq!(pool.len(), 2);
        assert_eq!(pool.aliases.get(1), AliasSeed::Own(crate::ids::PlaceId(0)));
    }

    #[test]
    fn call_args_and_convs_stay_aligned() {
        let mut pool = InstPool::new();
        let range = pool.push_operands(&[ValId(1), ValId(2)], &[Conv::Let, Conv::Inout]);
        assert_eq!(pool.args(range.clone()), &[ValId(1), ValId(2)]);
        assert_eq!(
            &pool.arg_convs[range.start as usize..range.end as usize],
            &[Conv::Let, Conv::Inout]
        );
    }
}
