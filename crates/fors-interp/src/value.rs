//! The interpreter value model (design §5.1).
//!
//! Every FMIR scalar fits in 64 bits (ch03 R1: no 128-bit integers in v1,
//! `f64` the widest float), so a scalar slot is one [`Slot`]: the
//! zero-extended integer, `bool`, or `f32`/`f64` bit pattern plus the
//! Miri-class bookkeeping. Aggregates, `Str` bytes and struct cells live in
//! side tables and are named by a 32-bit handle in `bits`.
//!
//! Host-word-size discipline (design §5.1): program-visible widths come from
//! [`crate::program::Config`] and the callee's `TyId`, never from the host.
//! This file uses only fixed-width integers for anything a program can
//! observe.

/// A scalar slot. Aggregates never live here — they live in side tables.
#[derive(Clone, Copy, Debug)]
pub struct Slot {
    /// Zero-extended integer, `bool` (0/1), or `f32`/`f64` bit pattern. For
    /// aggregate-typed values this is a handle into the machine's cell
    /// table; for `Str` a handle into the byte table.
    pub bits: u64,
    /// Provenance tag. F6 owns real provenance; F1 carries the field so its
    /// width is fixed from day one. Always zero.
    pub prov: u32,
    /// Miri bit: is this slot initialised?
    pub init: bool,
    /// ch05 R6, carried for the verifier and dumps.
    pub secret: bool,
}

impl Slot {
    /// An initialised, non-secret scalar with the given bit pattern.
    pub fn val(bits: u64) -> Slot {
        Slot {
            bits,
            prov: 0,
            init: true,
            secret: false,
        }
    }

    /// The unit value (no information; always initialised).
    pub fn unit() -> Slot {
        Slot::val(0)
    }

    /// An uninitialised slot: any read is `ub: uninit-read` (F6 owns the
    /// report; F1 initialises every slot it creates, so this constructor
    /// only exists for the entry shim's unused-parameter slots, which are
    /// never read by lowered code).
    pub fn uninit() -> Slot {
        Slot {
            bits: 0,
            prov: 0,
            init: false,
            secret: false,
        }
    }
}
