//! design §3.11's exact gate names: "Gate, as `fors-fmir` unit tests ...:
//! `secret_propagates`, `secret_trapping_op_rejected`,
//! `ct_no_branch_or_index_on_secret`, `secret_raise_condition_rejected`,
//! `declassify_requires_unsafe`, `ir_verify_secret_fields`." `verify.rs`'s
//! own unit tests cover the same rules in finer-grained form; these give
//! each design-named gate a matching, independently discoverable test.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;
use fors_fir::ty::TY_UNIT;
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::BlockRow;
use fors_fmir::decl::DeclFmir;
use fors_fmir::diag::DiagCode;
use fors_fmir::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};
use fors_fmir::ids::{ScopeId, SiteId};
use fors_fmir::inst::InstRow;
use fors_fmir::op::{ArithMode, NO_OPERAND, Op};
use fors_fmir::value::{ValDef, ValRow};
use fors_fmir::verify::verify;

fn has(decl: &DeclFmir, code: DiagCode) -> bool {
    verify(decl).iter().any(|d| d.code == code)
}

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

/// `secret_propagates`: `let x: u64 = s.wrap_add(1)` with `s` secret is
/// rejected unless `x` is ALSO secret (design §3.11's own R6a wording, cast
/// as the verifier-side consistency check `fors-fmir` can run before
/// `fors-lower` exists to compute propagation itself).
#[test]
fn secret_propagates() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let s = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
    let add = InstRow {
        op: Op::Add(ArithMode::Wrap),
        a: s.0,
        b: one.0,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    let add_id = decl.push_inst(add, AliasSeed::None);
    // x NOT secret: rejected.
    decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Inst(add_id)));
    assert!(has(&decl, DiagCode::SecretPropagationViolated));

    // x IS secret: accepted.
    let mut ok = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let s = ok.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let one = ok.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
    let add = InstRow {
        op: Op::Add(ArithMode::Wrap),
        a: s.0,
        b: one.0,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    let add_id = ok.push_inst(add, AliasSeed::None);
    ok.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Inst(add_id)));
    assert!(verify(&ok).is_empty(), "{:?}", verify(&ok));
}

/// `secret_trapping_op_rejected`: `s + 1` on secret `s` is rejected at
/// FMIR; the `wrap_`/`sat_`/`unchecked_` forms are the escape.
#[test]
fn secret_trapping_op_rejected() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let s = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
    let add = InstRow {
        op: Op::Add(ArithMode::Trap),
        a: s.0,
        b: one.0,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    decl.push_inst(add, AliasSeed::None);
    assert!(has(&decl, DiagCode::SecretTrappingOp));
}

/// `ct_no_branch_or_index_on_secret`: a branch, or an address/index, derived
/// from secret is a compile error.
#[test]
fn ct_no_branch_or_index_on_secret() {
    let mut branch = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let cond = branch.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let target = branch.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: plain(Op::Unreachable),
        scope: ScopeId(0),
    });
    branch.entry = branch.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            op: Op::CondBr,
            a: cond.0,
            b: target.0,
            c: target.0,
            ty: TY_UNIT,
            site: SiteId(0),
        },
        scope: ScopeId(0),
    });
    assert!(has(&branch, DiagCode::SecretBranchOrIndex));

    let mut index = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let base = index.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)));
    let idx = index.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(1)));
    let row = InstRow {
        op: Op::Index,
        a: base.0,
        b: idx.0,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    index.push_inst(row, AliasSeed::None);
    assert!(has(&index, DiagCode::SecretBranchOrIndex));
}

/// `secret_raise_condition_rejected`: a `raise` reached only through a
/// secret-derived branch is rejected; a secret-typed error PAYLOAD is
/// accepted (branching on it in the handler is caught by the same rule,
/// exercised above as `ct_no_branch_or_index_on_secret`).
#[test]
fn secret_raise_condition_rejected() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let cond = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let payload = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(1)));
    let raise_bb = decl.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            op: Op::Raise,
            a: payload.0,
            b: NO_OPERAND,
            c: NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        },
        scope: ScopeId(0),
    });
    let ok_bb = decl.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: plain(Op::Unreachable),
        scope: ScopeId(0),
    });
    decl.entry = decl.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            op: Op::CondBr,
            a: cond.0,
            b: ok_bb.0,
            c: raise_bb.0,
            ty: TY_UNIT,
            site: SiteId(0),
        },
        scope: ScopeId(0),
    });
    assert!(has(&decl, DiagCode::SecretRaiseCondition));

    // The secret PAYLOAD alone, reached unconditionally, is accepted.
    let mut payload_ok = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let payload = payload_ok.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    payload_ok.entry = payload_ok.blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            op: Op::Raise,
            a: payload.0,
            b: NO_OPERAND,
            c: NO_OPERAND,
            ty: TY_UNIT,
            site: SiteId(0),
        },
        scope: ScopeId(0),
    });
    assert!(verify(&payload_ok).is_empty(), "{:?}", verify(&payload_ok));
}

/// `declassify_requires_unsafe`.
#[test]
fn declassify_requires_unsafe() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let s = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let row = InstRow {
        op: Op::Declassify,
        a: s.0,
        b: NO_OPERAND,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    decl.push_inst(row, AliasSeed::None);
    assert!(has(&decl, DiagCode::DeclassifyRequiresUnsafe));

    let mut ok = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    ok.is_unsafe_invariant = true;
    let s = ok.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    let row = InstRow {
        op: Op::Declassify,
        a: s.0,
        b: NO_OPERAND,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    };
    ok.push_inst(row, AliasSeed::None);
    assert!(verify(&ok).is_empty(), "{:?}", verify(&ok));
}

/// `ir_verify_secret_fields`: "construct missing secret bit/`ct_region`, or
/// a secret value spilled outside its class: rejected." The spill-class half
/// is a post-regalloc CT-verifier concern (ch05 Rule 15, LIR) outside F0's
/// scope (`fors-fmir` never reaches allocation); the field-presence half is
/// exactly `verify_rejects_missing_secret_field`/`_ct_region`, reproduced
/// here under design §3.11's own name for the same rule.
#[test]
fn ir_verify_secret_fields() {
    let mut missing_secret = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let mut row = ValRow::new(TY_UNIT, false, 0, ValDef::Param(0));
    row.flags = ValFlags(SECRET_UNSPECIFIED);
    missing_secret.push_val(row);
    assert!(has(&missing_secret, DiagCode::MissingSecretField));

    let mut missing_ct = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    missing_ct.push_val(ValRow {
        ty: TY_UNIT,
        flags: ValFlags::new(false),
        ct: CT_UNSPECIFIED,
        def: 0,
    });
    assert!(has(&missing_ct, DiagCode::MissingCtRegion));
}
