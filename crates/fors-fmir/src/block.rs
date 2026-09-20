//! Basic blocks (design §3.2, §3.1): "FMIR is a **CFG of basic blocks** —
//! SoA, one terminator each, reducible by construction (Fors has no
//! `goto`)". `blocks: BlockPool, // SoA: first_inst, inst_len, term, scope`
//! is reproduced field for field; `term` reuses [`crate::inst::InstRow`]'s
//! exact shape (design §3.10's operand-shape sentence covers "the
//! instruction set" as a whole, terminators included) rather than a
//! bespoke enum, which is also what makes `verify_rejects_two_terminators`
//! constructible at all: nothing stops a hand-built or hand-parsed
//! `InstPool` row inside a block's own instruction range from also
//! carrying a terminator-class [`Op`] — see `verify.rs`.

use crate::ids::{BlockId, ScopeId};
use crate::inst::InstRow;
use crate::op::Op;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BlockRow {
    pub first_inst: u32,
    pub inst_len: u32,
    pub term: InstRow,
    pub scope: ScopeId,
}

impl BlockRow {
    pub fn inst_range(&self) -> std::ops::Range<u32> {
        self.first_inst..(self.first_inst + self.inst_len)
    }

    /// design's own well-formedness expectation for `term`; `verify()`
    /// re-checks this over hand-built/parsed FMIR rather than trusting it,
    /// since the textual parser (`parse.rs`) does not enforce it at parse
    /// time (§1: the parser must stay permissive enough for the negative
    /// corpus to misuse this field on purpose).
    pub fn term_is_well_formed(&self) -> bool {
        self.term.op.is_terminator()
    }
}

#[derive(Clone, Debug, Default)]
pub struct BlockPool {
    rows: Vec<BlockRow>,
}

impl BlockPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: BlockRow) -> BlockId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        BlockId(i)
    }

    pub fn row(&self, id: BlockId) -> BlockRow {
        self.rows[id.index()]
    }

    /// [`BlockPool::row`] for a `BlockId` read out of a terminator's operand
    /// slot rather than out of this pool's own iteration — arbitrary FMIR may
    /// branch to a block that does not exist, and `verify()` must report that
    /// rather than panic on it.
    pub fn try_row(&self, id: BlockId) -> Option<BlockRow> {
        self.rows.get(id.index()).copied()
    }

    pub fn all_rows(&self) -> impl Iterator<Item = (BlockId, BlockRow)> + '_ {
        self.rows
            .iter()
            .enumerate()
            .map(|(i, r)| (BlockId(i as u32), *r))
    }

    /// A block's regular (non-terminator-slot) opcodes, for
    /// `verify_rejects_two_terminators`: a terminator-class [`Op`] found here
    /// means the block ended up with two terminators (its dedicated `term`
    /// plus this stray one) — see `block.rs`'s module docs.
    pub fn stray_terminator_indices(&self, id: BlockId, insts: &crate::inst::InstPool) -> Vec<u32> {
        let row = self.row(id);
        let range = row.inst_range();
        insts
            .slice(range.clone())
            .iter()
            .enumerate()
            .filter(|(_, inst)| inst.op.is_terminator())
            .map(|(i, _)| range.start + i as u32)
            .collect()
    }
}

/// Convenience used by both `verify.rs` and the fuzz generator: does an
/// [`Op`] belong in a block's regular instruction range at all (i.e. is it
/// *not* a terminator)? The inverse of [`Op::is_terminator`], named here
/// rather than in `op.rs` since it is specifically about block-shape, not
/// about the opcode in isolation.
pub fn is_regular_instruction(op: Op) -> bool {
    !op.is_terminator()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::alias::AliasSeed;
    use crate::ids::SiteId;
    use crate::inst::InstPool;
    use crate::op::ArithMode;
    use fors_fir::ty::TY_UNIT;

    fn plain(op: Op) -> InstRow {
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
    fn well_formed_block_has_no_stray_terminator() {
        let mut insts = InstPool::new();
        insts.push(plain(Op::Add(ArithMode::Trap)), AliasSeed::None);
        let mut blocks = BlockPool::new();
        let id = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 1,
            term: plain(Op::Ret),
            scope: ScopeId::NONE,
        });
        assert!(blocks.row(id).term_is_well_formed());
        assert!(blocks.stray_terminator_indices(id, &insts).is_empty());
    }

    #[test]
    fn a_terminator_smuggled_into_the_regular_range_is_a_stray() {
        let mut insts = InstPool::new();
        insts.push(plain(Op::Add(ArithMode::Trap)), AliasSeed::None);
        insts.push(plain(Op::Ret), AliasSeed::None); // smuggled: not the block's `term`
        let mut blocks = BlockPool::new();
        let id = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 2,
            term: plain(Op::Br),
            scope: ScopeId::NONE,
        });
        assert_eq!(blocks.stray_terminator_indices(id, &insts), vec![1]);
    }
}
