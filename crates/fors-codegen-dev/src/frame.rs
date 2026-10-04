//! Frame layout (§3 "Frame"): one 8-byte slot per OIR value and per place
//! root, `sp`-relative (`[sp, #8k]`, `k < 4096`). Above 32 KiB a slot would
//! need an extra `add x17, sp, #hi, lsl #12` per access; M2-0 refuses that
//! frame instead. Every secret value is refused upstream (M2-10 adds the
//! `Secret` slot class), so there is one class here: `Plain`.

use fors_oir::OirFunc;

/// The largest frame M2-0 lays out: every slot offset fits `ldr`'s scaled
/// 12-bit immediate.
pub const MAX_FRAME: u32 = 32 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    /// Bytes below the frame record (`sub sp, sp, #size`), a multiple of 16.
    pub size: u32,
    n_values: u32,
}

impl Frame {
    /// The layout of `f`, or `None` when it exceeds [`MAX_FRAME`].
    pub fn of(f: &OirFunc) -> Option<Frame> {
        let slots = f.values.len() as u64 + f.slots.len() as u64;
        let size = (slots * 8).div_ceil(16) * 16;
        if size > u64::from(MAX_FRAME) {
            return None;
        }
        Some(Frame {
            size: size as u32,
            n_values: f.values.len() as u32,
        })
    }

    /// `sp`-relative byte offset of value `v`'s slot.
    pub fn value(&self, v: u32) -> u32 {
        8 * v
    }

    /// `sp`-relative byte offset of place slot `s`.
    pub fn place(&self, s: u32) -> u32 {
        8 * (self.n_values + s)
    }
}
