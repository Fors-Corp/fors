//! The OIR verifier (§2.1, §9): ch05 R6 (secret + ct present on every
//! value), R4/R5 (an alias class present and traceable on every slot row),
//! R12 (`tile.*` absent), plus the structural invariants the selector
//! relies on (operands defined before use, slots in range). Every violation
//! is a named [`VerifyError`] variant, never a panic.

use fors_fmir::flags::CT_UNSPECIFIED;

use crate::ir::{AliasClass, LowTy, NONE, OirFunc, OirOp};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// ch05 R6: value `v` has no `secret` field.
    MissingSecret { value: u32 },
    /// ch05 R6: value `v` has no `ct` field, or the "unspecified" sentinel.
    MissingCt { value: u32 },
    /// ch05 R4: slot row `row` carries no alias class.
    MissingAliasClass { row: u32 },
    /// ch05 R5: slot row `row`'s class does not trace to its slot's root.
    UntraceableAliasClass { row: u32 },
    /// ch05 R12: a `tile.*` op at OIR.
    TileOp { row: u32 },
    /// A row column is shorter than `op` (the SoA fell out of lockstep).
    RaggedRows,
    /// Operand of `row` is not a value defined by an earlier row.
    BadOperand { row: u32 },
    /// `row` names slot `slot`, which does not exist.
    BadSlot { row: u32 },
    /// A value's type column disagrees with its defining row's `ty`.
    TypeMismatch { row: u32 },
}

impl VerifyError {
    /// The rule-scoped name the gate tests match on.
    pub fn name(&self) -> &'static str {
        match self {
            VerifyError::MissingSecret { .. } => "missing-secret",
            VerifyError::MissingCt { .. } => "missing-ct",
            VerifyError::MissingAliasClass { .. } => "missing-alias-class",
            VerifyError::UntraceableAliasClass { .. } => "untraceable-alias-class",
            VerifyError::TileOp { .. } => "tile-op-at-oir",
            VerifyError::RaggedRows => "ragged-rows",
            VerifyError::BadOperand { .. } => "bad-operand",
            VerifyError::BadSlot { .. } => "bad-slot",
            VerifyError::TypeMismatch { .. } => "type-mismatch",
        }
    }
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "oir verify: {} ({self:?})", self.name())
    }
}

impl std::error::Error for VerifyError {}

/// Checks `f`; `Ok` or the first violation.
pub fn verify(f: &OirFunc) -> Result<(), VerifyError> {
    let n = f.values.ty.len();
    for v in 0..n {
        if v >= f.values.secret.len() {
            return Err(VerifyError::MissingSecret { value: v as u32 });
        }
        if v >= f.values.ct.len() || f.values.ct[v] == CT_UNSPECIFIED {
            return Err(VerifyError::MissingCt { value: v as u32 });
        }
    }
    let r = &f.rows;
    let len = r.op.len();
    if [
        r.a.len(),
        r.b.len(),
        r.ty.len(),
        r.mode.len(),
        r.alias.len(),
        r.site.len(),
        r.dst.len(),
    ]
    .iter()
    .any(|&l| l != len)
    {
        return Err(VerifyError::RaggedRows);
    }
    let mut defined = vec![false; n];
    for i in 0..len {
        let row = i as u32;
        let op = r.op[i];
        if op == OirOp::Tile {
            return Err(VerifyError::TileOp { row });
        }
        if op.is_slot_row() {
            let slot = r.a[i] as usize;
            let Some(s) = f.slots.get(slot) else {
                return Err(VerifyError::BadSlot { row });
            };
            match r.alias[i] {
                None => return Err(VerifyError::MissingAliasClass { row }),
                Some(AliasClass::Root { root, .. }) if root != s.root => {
                    return Err(VerifyError::UntraceableAliasClass { row });
                }
                Some(_) => {}
            }
        }
        let value_cols: &[u32] = match op {
            OirOp::ConstInt | OirOp::ConstBool | OirOp::ConstUnit | OirOp::ConstStr => &[],
            OirOp::SlotLoad => &[],
            OirOp::SlotStore => &[r.b[i]],
            OirOp::Neg
            | OirOp::Not
            | OirOp::ConvChecked
            | OirOp::ConvWrap
            | OirOp::ConvSat
            | OirOp::WriteUint
            | OirOp::WriteLine => &[r.a[i]],
            _ => &[r.a[i], r.b[i]],
        };
        for &v in value_cols {
            if v == NONE || v as usize >= n || !defined[v as usize] {
                return Err(VerifyError::BadOperand { row });
            }
        }
        if r.dst[i] != NONE {
            let d = r.dst[i] as usize;
            if d >= n || defined[d] {
                return Err(VerifyError::BadOperand { row });
            }
            if f.values.ty[d] != r.ty[i] {
                return Err(VerifyError::TypeMismatch { row });
            }
            defined[d] = true;
        } else if r.ty[i] != LowTy::Unit {
            return Err(VerifyError::TypeMismatch { row });
        }
    }
    Ok(())
}
