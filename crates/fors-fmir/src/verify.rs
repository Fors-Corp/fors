//! The structural verifier (design item 5 of the F0 task list): "the
//! structural verifier, returning source-located diagnostics." Every check
//! here is over ONE declaration's own pools — no cross-declaration analysis,
//! matching design §1.2's "FMIR must still represent them" scope for F0 and
//! ch05 Rule 3 ("FMIR MUST be the sole input" — the verifier does not read
//! anything this crate does not already hold).

use crate::alias::AliasSeed;
use crate::decl::DeclFmir;
use crate::diag::{Anchor, DiagCode, Diagnostic};
use crate::ids::ValId;
use crate::inst::InstRow;
use crate::op::Op;
use crate::region::RegionKind;

/// Runs every check and returns every diagnostic found (never stops at the
/// first one — a hand-written negative-corpus file may trip more than one
/// rule, and a caller deduping by [`DiagCode`] should still see every site).
pub fn verify(decl: &DeclFmir) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    check_secret_fields(decl, &mut out);
    check_terminators(decl, &mut out);
    check_tile_ops(decl, &mut out);
    check_alias_seeds(decl, &mut out);
    check_region_captures(decl, &mut out);
    check_secret_propagation(decl, &mut out);
    check_secret_rejection(decl, &mut out);
    out
}

pub fn is_ok(decl: &DeclFmir) -> bool {
    verify(decl).is_empty()
}

/// Is `v` secret? `v` comes from an instruction's raw `a`/`b`/`c` slot, which
/// arbitrary FMIR may leave dangling; a value that does not exist is not
/// secret, so the ch05 Rule 6b checks below simply find nothing to reject
/// rather than panicking (F0 has no "operand out of range" diagnostic — see
/// `check_one_secret_rejection`'s `Op::Intrinsic` arm for the same rule).
fn is_secret(decl: &DeclFmir, v: ValId) -> bool {
    decl.vals.try_row(v).is_some_and(|row| row.is_secret())
}

fn val_or_none(raw: u32) -> Option<ValId> {
    if raw == crate::op::NO_OPERAND {
        None
    } else {
        Some(ValId(raw))
    }
}

/// ch05 Rule 6: "Every FMIR/OIR/LIR value MUST carry a secret bit and
/// `ct_region` id as non-optional fields; `--verify-each` MUST reject any
/// lacking them." The safe builder can never produce a row lacking either
/// (`ValRow::new` takes both as required arguments); this check exists for
/// the textual/parsed path, which can (design §1, `flags.rs`,
/// `SECRET_UNSPECIFIED`/`CT_UNSPECIFIED`).
fn check_secret_fields(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.vals.all_rows() {
        if row.flags.is_secret_unspecified() {
            out.push(Diagnostic::new(
                DiagCode::MissingSecretField,
                Anchor::Val(id),
                "value has no secret field",
            ));
        }
        if row.ct == crate::flags::CT_UNSPECIFIED {
            out.push(Diagnostic::new(
                DiagCode::MissingCtRegion,
                Anchor::Val(id),
                "value has no ct_region field",
            ));
        }
    }
}

/// `verify_rejects_two_terminators`: a terminator-class [`Op`] found among a
/// block's *regular* instructions (i.e. anywhere other than `term`) — see
/// `block.rs`'s module docs for why this is how "two terminators" is
/// constructible at all.
fn check_terminators(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, _row) in decl.blocks.all_rows() {
        for stray in decl.blocks.stray_terminator_indices(id, &decl.insts) {
            out.push(Diagnostic::new(
                DiagCode::TwoTerminators,
                Anchor::Inst(crate::ids::InstId(stray)),
                "block has a terminator-class op outside its `term` slot (two terminators)",
            ));
        }
        let term_op = decl.blocks.row(id).term.op;
        if !term_op.is_terminator() {
            out.push(Diagnostic::new(
                DiagCode::TwoTerminators,
                Anchor::Block(id),
                "block's `term` slot does not hold a terminator opcode",
            ));
        }
    }
}

/// `verify_rejects_tile_op`: `tile.*` "MUST appear only in FMIR" (ch05 Rule
/// 12) but M1 defines no `tile.*` opcode at all (design §1.2) — any
/// [`Op::TileOp`] found anywhere is rejected uniformly, terminator slot or
/// not.
fn check_tile_ops(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        if row.op == Op::TileOp {
            out.push(Diagnostic::new(
                DiagCode::TileOpPresent,
                Anchor::Inst(id),
                "tile.* is not defined before M6",
            ));
        }
    }
    for (id, row) in decl.blocks.all_rows() {
        if row.term.op == Op::TileOp {
            out.push(Diagnostic::new(
                DiagCode::TileOpPresent,
                Anchor::Block(id),
                "tile.* is not defined before M6",
            ));
        }
    }
}

/// `alias_seed_present_on_every_memory_op` (design §3.4a, ch05 Rule 5): every
/// [`Op::is_memory_producing`] row must carry a seed other than
/// [`AliasSeed::None`].
fn check_alias_seeds(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        if row.op.is_memory_producing() && decl.insts.aliases.get(id.index()) == AliasSeed::None {
            out.push(Diagnostic::new(
                DiagCode::MemoryOpMissingAliasSeed,
                Anchor::Inst(id),
                "memory-producing instruction has no alias seed",
            ));
        }
    }
}

/// `verify_rejects_detach_without_captures` (ch05 Rule 9). See `region.rs`'s
/// module docs for why "detach" means an FMIR `spawn` region here.
fn check_region_captures(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.regions.all_rows() {
        if row.kind == RegionKind::Spawn && row.captures_absent() {
            out.push(Diagnostic::new(
                DiagCode::DetachWithoutCaptures,
                region_anchor(decl, id),
                format!("spawn region {} has no capture list", id.0),
            ));
        }
    }
}

/// Where to point a reader at a [`crate::ids::RegionId`]. A `RegionRow` has no
/// `SiteId` of its own (design §3.7 gives it none), but the `spawn`/
/// `region_enter` instruction that opens it does — that instruction carries
/// the region id in slot `a` (`op.rs`'s operand table), so the diagnostic
/// anchors to it and resolves to a real source site. `Anchor::Decl` remains
/// the fallback for a region no instruction opens, which is itself only
/// reachable in a hand-written fixture.
fn region_anchor(decl: &DeclFmir, region: crate::ids::RegionId) -> Anchor {
    decl.insts
        .all_rows()
        .find(|(_, row)| matches!(row.op, Op::Spawn | Op::RegionEnter) && row.a == region.0)
        .map(|(id, _)| Anchor::Inst(id))
        .unwrap_or(Anchor::Decl)
}

/// The value-to-value operands of `op` that ch05 Rule 6a's propagation
/// invariant applies to: "the result of any operation with a secret operand
/// is secret". Scoped to instructions whose operands are genuinely `ValId`s
/// (arithmetic, logic, conversion, aggregate construction, projection) —
/// `move_from`/`copy_from`/`init`/`borrow*`/calls read a *place* or invoke a
/// *callee*, which R6a's "local FMIR type rule" wording does not extend to
/// without a flow analysis this crate does not perform. [decision: see
/// `verify.rs`'s module docs and the `decisions` list for the full
/// rationale]
fn propagation_operands(op: Op, row: &InstRow, decl: &DeclFmir) -> Vec<ValId> {
    match op {
        Op::Add(_)
        | Op::Sub(_)
        | Op::Mul(_)
        | Op::Div(_)
        | Op::Rem(_)
        | Op::Shl(_)
        | Op::Shr(_)
        | Op::Neg(_) => [val_or_none(row.a), val_or_none(row.b)]
            .into_iter()
            .flatten()
            .collect(),
        Op::Fadd(_) | Op::Fsub(_) | Op::Fmul(_) | Op::Fdiv(_) | Op::Frem(_) | Op::Fneg(_) => {
            [val_or_none(row.a), val_or_none(row.b)]
                .into_iter()
                .flatten()
                .collect()
        }
        Op::Icmp(_) | Op::Fcmp(_) | Op::And | Op::Or | Op::Xor | Op::Not => {
            [val_or_none(row.a), val_or_none(row.b)]
                .into_iter()
                .flatten()
                .collect()
        }
        Op::ConvChecked | Op::ConvWrap | Op::ConvSat | Op::ConvTrunc => {
            [val_or_none(row.a)].into_iter().flatten().collect()
        }
        Op::Field | Op::Discr | Op::Payload => [val_or_none(row.a)].into_iter().flatten().collect(),
        Op::AggNew | Op::TupleNew => decl.insts.args(row.a..row.b).to_vec(),
        Op::VariantNew => decl.insts.args(row.a..row.b).to_vec(),
        _ => Vec::new(),
    }
}

/// `secret_propagates`: checks the ch05 Rule 6a invariant already holds,
/// rather than computing it (`fors-lower` computes it — design §3.11).
fn check_secret_propagation(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        let operands = propagation_operands(row.op, &row, decl);
        if operands.is_empty() {
            continue;
        }
        let any_secret = operands.iter().any(|v| is_secret(decl, *v));
        if !any_secret {
            continue;
        }
        // The instruction's *result* is the value whose `def` names this
        // instruction (design §3.1: "def: u32, // defining instruction").
        let result_secret = decl
            .vals
            .all_rows()
            .find(|(_, v)| matches!(v.def(), crate::value::ValDef::Inst(inst) if inst == id))
            .map(|(_, v)| v.is_secret());
        if let Some(false) = result_secret {
            out.push(Diagnostic::new(
                DiagCode::SecretPropagationViolated,
                Anchor::Inst(id),
                "result is not secret despite a secret operand (ch05 Rule 6a)",
            ));
        }
    }
}

/// ch05 Rule 6b's rejection list, as far as design §3.11 assigns it to this
/// crate: branch/index/trapping-op/contract/raise/intrinsic on secret, and
/// `declassify` outside `@unsafe(invariant:)`.
fn check_secret_rejection(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    // Regular instructions.
    for (id, row) in decl.insts.all_rows() {
        check_one_secret_rejection(decl, Anchor::Inst(id), row.op, row, out);
    }
    // Terminators (which live in `BlockRow.term`, not `InstPool` — see
    // `block.rs`).
    for (block_id, block) in decl.blocks.all_rows() {
        let row = block.term;
        check_one_secret_rejection(decl, Anchor::Block(block_id), row.op, row, out);
        if row.op == Op::CondBr
            && let Some(cond) = val_or_none(row.a)
            && is_secret(decl, cond)
        {
            let leads_to_raise = [row.b, row.c].into_iter().any(|bb| {
                bb != crate::op::NO_OPERAND
                    && decl
                        .blocks
                        .try_row(crate::ids::BlockId(bb))
                        .is_some_and(|target| target.term.op == Op::Raise)
            });
            if leads_to_raise {
                out.push(Diagnostic::new(
                    DiagCode::SecretRaiseCondition,
                    Anchor::Block(block_id),
                    "raise is reached only through a secret-derived branch",
                ));
            }
        }
    }
}

fn check_one_secret_rejection(
    decl: &DeclFmir,
    at: Anchor,
    op: Op,
    row: InstRow,
    out: &mut Vec<Diagnostic>,
) {
    match op {
        Op::CondBr | Op::SwitchDiscr => {
            if let Some(cond) = val_or_none(row.a)
                && is_secret(decl, cond)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretBranchOrIndex,
                    at,
                    "branch on a secret operand",
                ));
            }
        }
        Op::Index => {
            if let Some(idx) = val_or_none(row.b)
                && is_secret(decl, idx)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretBranchOrIndex,
                    at,
                    "index derived from secret",
                ));
            }
        }
        Op::SliceRange => {
            for bound in [row.b, row.c] {
                if let Some(v) = val_or_none(bound)
                    && is_secret(decl, v)
                {
                    out.push(Diagnostic::new(
                        DiagCode::SecretBranchOrIndex,
                        at,
                        "slice bound derived from secret",
                    ));
                }
            }
        }
        _ if op.is_secret_rejected_trapping_op() => {
            for slot in [row.a, row.b] {
                if let Some(v) = val_or_none(slot)
                    && is_secret(decl, v)
                {
                    out.push(Diagnostic::new(
                        DiagCode::SecretTrappingOp,
                        at,
                        "trapping arithmetic (or conv_checked) on a secret operand: use wrap_/sat_/unchecked_",
                    ));
                    break;
                }
            }
        }
        _ if op.is_contract_check() => {
            if let Some(cond) = val_or_none(row.a)
                && is_secret(decl, cond)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretInContractCheck,
                    at,
                    "contract check on a secret operand",
                ));
            }
        }
        Op::Raise => {
            // The payload itself MAY be secret (design §3.11: "A secret
            // error payload is accepted and stays secret"); only a
            // secret-conditioned *reachability* of this terminator is
            // rejected, checked from the upstream `cond_br` in
            // `check_secret_rejection` above.
        }
        // A `row.a` past the end of `calls` is a different malformation
        // than anything ch05 Rule 6b names; nothing else in this crate's
        // `verify()` is positioned to report it either (there is no generic
        // "side-table index out of range" diagnostic at F0), so this arm
        // simply has no secret argument to find rather than panicking —
        // consistent with `encode.rs::safe_remap`'s "stay total, don't
        // crash on a malformed `DeclFmir`" rule.
        Op::Intrinsic if (row.a as usize) >= decl.insts.calls.len() => {}
        Op::Intrinsic => {
            let call = &decl.insts.calls[row.a as usize];
            if op.is_host_intrinsic() {
                for arg in decl.insts.args(call.args.clone()) {
                    if is_secret(decl, *arg) {
                        out.push(Diagnostic::new(
                            DiagCode::SecretIntrinsicArg,
                            at,
                            "secret argument to a host-effecting intrinsic",
                        ));
                        break;
                    }
                }
            }
        }
        Op::Declassify if !decl.is_unsafe_invariant => {
            out.push(Diagnostic::new(
                DiagCode::DeclassifyRequiresUnsafe,
                at,
                "declassify outside @unsafe(invariant: ...)",
            ));
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockRow;
    use crate::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};
    use crate::inst::InstRow;
    use crate::op::ArithMode;
    use crate::value::{ValDef, ValRow};
    use fors_fir::defpath::DeclKeyId;
    use fors_fir::sig::FnSigId;
    use fors_fir::ty::TY_UNIT;

    fn plain(op: Op) -> InstRow {
        InstRow {
            op,
            a: crate::op::NO_OPERAND,
            b: crate::op::NO_OPERAND,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        }
    }

    #[test]
    fn empty_well_formed_decl_is_ok() {
        let decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn missing_secret_field_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut row = ValRow::new(TY_UNIT, false, 0, ValDef::Param(0));
        row.flags = ValFlags(SECRET_UNSPECIFIED);
        decl.push_val(row);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::MissingSecretField),
            "{diags:?}"
        );
    }

    #[test]
    fn missing_ct_region_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let row = ValRow {
            ty: TY_UNIT,
            flags: ValFlags::new(false),
            ct: CT_UNSPECIFIED,
            def: 0,
        };
        decl.push_val(row);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::MissingCtRegion),
            "{diags:?}"
        );
    }

    #[test]
    fn secret_add_rejected_unless_result_marked_secret() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
        let add = InstRow {
            op: Op::Add(ArithMode::Trap),
            a: secret.0,
            b: one.0,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        };
        let add_id = decl.push_inst(add, AliasSeed::None);
        // Result NOT marked secret: violates ch05 Rule 6a.
        decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Inst(add_id)));
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::SecretPropagationViolated),
            "{diags:?}"
        );
    }

    #[test]
    fn secret_add_accepted_when_result_is_marked_secret() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
        // `Wrap`, not the default `Trap` mode: ch05 Rule 6b rejects a
        // *trapping* op on a secret operand outright (`secret_trapping_add_
        // is_rejected_but_wrap_add_is_accepted` below covers that). This
        // test isolates Rule 6a's propagation-acceptance question alone.
        let add = InstRow {
            op: Op::Add(ArithMode::Wrap),
            a: secret.0,
            b: one.0,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        };
        let add_id = decl.push_inst(add, AliasSeed::None);
        decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Inst(add_id)));
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn secret_trapping_add_is_rejected_but_wrap_add_is_accepted() {
        for (mode, expect_ok) in [(ArithMode::Trap, false), (ArithMode::Wrap, true)] {
            let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
            let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
            let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
            let add = InstRow {
                op: Op::Add(mode),
                a: secret.0,
                b: one.0,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            };
            let add_id = decl.push_inst(add, AliasSeed::None);
            decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Inst(add_id)));
            let diags = verify(&decl);
            let has_trapping_diag = diags.iter().any(|d| d.code == DiagCode::SecretTrappingOp);
            assert_eq!(!has_trapping_diag, expect_ok, "mode {mode:?}: {diags:?}");
        }
    }

    #[test]
    fn branch_on_secret_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret_cond = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let target = decl.blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Unreachable),
            scope: crate::ids::ScopeId(0),
        });
        decl.entry = decl.blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: InstRow {
                op: Op::CondBr,
                a: secret_cond.0,
                b: target.0,
                c: target.0,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            },
            scope: crate::ids::ScopeId(0),
        });
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::SecretBranchOrIndex),
            "{diags:?}"
        );
    }

    #[test]
    fn declassify_outside_unsafe_is_rejected_but_accepted_inside_it() {
        for (is_unsafe, expect_ok) in [(false, false), (true, true)] {
            let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
            decl.is_unsafe_invariant = is_unsafe;
            let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
            let inst = InstRow {
                op: Op::Declassify,
                a: secret.0,
                b: crate::op::NO_OPERAND,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            };
            decl.push_inst(inst, AliasSeed::None);
            let diags = verify(&decl);
            let rejected = diags
                .iter()
                .any(|d| d.code == DiagCode::DeclassifyRequiresUnsafe);
            assert_eq!(!rejected, expect_ok, "is_unsafe={is_unsafe}: {diags:?}");
        }
    }

    #[test]
    fn tile_op_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.push_inst(plain(Op::TileOp), AliasSeed::None);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::TileOpPresent),
            "{diags:?}"
        );
    }

    #[test]
    fn two_terminators_in_one_block_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        // Smuggle a terminator-class op into the entry block's regular range
        // in addition to its real `term`.
        let stray = decl.insts.push(plain(Op::Ret), AliasSeed::None);
        assert_eq!(stray.0, 0);
        let mut entry = decl.blocks.row(decl.entry);
        entry.first_inst = 0;
        entry.inst_len = 1;
        // Rebuild the block pool with the corrected row (there is no
        // in-place mutator by design — pools are append-only elsewhere).
        let mut blocks = crate::block::BlockPool::new();
        let new_entry = blocks.push(entry);
        decl.blocks = blocks;
        decl.entry = new_entry;
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::TwoTerminators),
            "{diags:?}"
        );
    }

    #[test]
    fn memory_op_without_alias_seed_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.push_inst(plain(Op::Alloc), AliasSeed::None);
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::MemoryOpMissingAliasSeed),
            "{diags:?}"
        );
    }

    #[test]
    fn spawn_region_without_captures_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.regions.push(crate::region::RegionRow {
            kind: RegionKind::Spawn,
            captures: crate::region::RegionRow::ABSENT_CAPTURES,
            brand: crate::ids::BrandId::NONE,
        });
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::DetachWithoutCaptures),
            "{diags:?}"
        );
    }

    #[test]
    fn spawn_region_with_an_explicit_empty_capture_list_is_accepted() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.regions.push(crate::region::RegionRow {
            kind: RegionKind::Spawn,
            captures: 0..0,
            brand: crate::ids::BrandId::NONE,
        });
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }
}
