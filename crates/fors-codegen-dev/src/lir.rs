//! LIR-dev (§2.1): one row per stencil instance, struct-of-arrays —
//! `(stencil id, holes, secret mask, ct)`. Secret mask and `ct` are carried
//! (ch05 R6 at LIR; `lir_verify_requires_secret_and_ct` is M2-10's gate):
//! in M2-0 every secret value was refused, so every mask is 0.

use crate::stencil::Fill;

/// Where a row's literal (if any) lives: an index into the function's
/// string table.
pub const NO_LIT: u32 = u32::MAX;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lir {
    pub stencil: Vec<u32>,
    /// Slot offsets and immediates; trap/call/literal distances are filled
    /// in by `emit` once positions are known.
    pub fill: Vec<Fill>,
    pub lit: Vec<u32>,
    pub secret_mask: Vec<u8>,
    pub ct: Vec<u16>,
    /// The OIR row (or `u32::MAX` for prologue/epilogue/terminator rows).
    pub oir_row: Vec<u32>,
    /// The FMIR site of the row (trap-table rows carry it).
    pub site: Vec<u32>,
}

impl Lir {
    pub fn len(&self) -> usize {
        self.stencil.len()
    }

    pub fn is_empty(&self) -> bool {
        self.stencil.is_empty()
    }

    #[allow(clippy::too_many_arguments)]
    pub fn push(
        &mut self,
        stencil: u32,
        fill: Fill,
        lit: u32,
        secret_mask: u8,
        ct: u16,
        oir_row: u32,
        site: u32,
    ) {
        self.stencil.push(stencil);
        self.fill.push(fill);
        self.lit.push(lit);
        self.secret_mask.push(secret_mask);
        self.ct.push(ct);
        self.oir_row.push(oir_row);
        self.site.push(site);
    }
}
