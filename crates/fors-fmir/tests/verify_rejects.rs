//! The task's named `verify_rejects_*` gate tests, each isolated to its own
//! function so a failing rule is unambiguous from the test name alone.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;
use fors_fir::ty::TY_UNIT;
use fors_fmir::alias::AliasSeed;
use fors_fmir::decl::DeclFmir;
use fors_fmir::diag::DiagCode;
use fors_fmir::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};
use fors_fmir::ids::{BrandId, SiteId};
use fors_fmir::inst::InstRow;
use fors_fmir::op::{NO_OPERAND, Op};
use fors_fmir::region::{RegionKind, RegionRow};
use fors_fmir::value::{ValDef, ValRow};
use fors_fmir::verify::verify;

fn plain(op: Op) -> InstRow {
    InstRow {
        op,
        a: NO_OPERAND,
        b: NO_OPERAND,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    }
}

fn rejected_with(decl: &DeclFmir, code: DiagCode) -> bool {
    verify(decl).iter().any(|d| d.code == code)
}

#[test]
fn verify_rejects_missing_secret_field() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let mut row = ValRow::new(TY_UNIT, false, 0, ValDef::Param(0));
    row.flags = ValFlags(SECRET_UNSPECIFIED);
    decl.push_val(row);
    assert!(rejected_with(&decl, DiagCode::MissingSecretField));
}

#[test]
fn verify_rejects_missing_ct_region() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    decl.push_val(ValRow {
        ty: TY_UNIT,
        flags: ValFlags::new(false),
        ct: CT_UNSPECIFIED,
        def: 0,
    });
    assert!(rejected_with(&decl, DiagCode::MissingCtRegion));
}

#[test]
fn verify_rejects_detach_without_captures() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    decl.regions.push(RegionRow {
        kind: RegionKind::Spawn,
        captures: RegionRow::ABSENT_CAPTURES,
        brand: BrandId::NONE,
    });
    assert!(rejected_with(&decl, DiagCode::DetachWithoutCaptures));

    // And the positive control: an EXPLICIT empty list is accepted (ch05
    // Rule 9 requires the list to be explicit, not non-empty).
    let mut ok = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    ok.regions.push(RegionRow {
        kind: RegionKind::Spawn,
        captures: 0..0,
        brand: BrandId::NONE,
    });
    assert!(verify(&ok).is_empty(), "{:?}", verify(&ok));
}

#[test]
fn verify_rejects_tile_op() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    decl.push_inst(plain(Op::TileOp), AliasSeed::None);
    assert!(rejected_with(&decl, DiagCode::TileOpPresent));
}

#[test]
fn verify_rejects_two_terminators() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    // Smuggle a terminator-class op into the entry block's regular
    // instruction range in addition to its real `term` — see `block.rs`'s
    // module docs for why this is the constructible shape of "two
    // terminators".
    decl.insts.push(plain(Op::Ret), AliasSeed::None);
    let mut entry = decl.blocks.row(decl.entry);
    entry.first_inst = 0;
    entry.inst_len = 1;
    let mut blocks = fors_fmir::block::BlockPool::new();
    decl.entry = blocks.push(entry);
    decl.blocks = blocks;
    assert!(rejected_with(&decl, DiagCode::TwoTerminators));
}
