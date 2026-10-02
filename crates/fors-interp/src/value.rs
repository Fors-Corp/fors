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
    /// Provenance: [`crate::mem::PROV_NONE`] for a non-pointer, else an index
    /// into the machine's [`crate::mem::ProvRow`] table, which names what the
    /// pointer points into and its borrow tag (design §5.1, §5.2).
    pub prov: u32,
    /// Miri bit: is this slot initialised?
    pub init: bool,
    /// Miri bit (design §5.2's first row): is this place still LIVE, or was it
    /// moved out of (`move_from`) or dropped at a scope exit? A read of a dead
    /// slot is `ub: use-after-move`, distinct from reading an *uninitialised*
    /// one, which is `ub: uninit-read`.
    pub live: bool,
    /// ch05 R6, carried for the verifier and dumps.
    pub secret: bool,
}

impl Slot {
    /// An initialised, non-secret scalar with the given bit pattern.
    pub fn val(bits: u64) -> Slot {
        Slot {
            bits,
            prov: crate::mem::PROV_NONE,
            init: true,
            live: true,
            secret: false,
        }
    }

    /// A pointer: the same scalar plus the provenance row that names what it
    /// points into (design §5.1).
    pub fn ptr(bits: u64, prov: u32) -> Slot {
        Slot {
            bits,
            prov,
            init: true,
            live: true,
            secret: false,
        }
    }

    /// The same slot with its `live` bit cleared: `move_from`'s effect on its
    /// source place, and an exit edge's drop of a non-linear binding
    /// (design §5.2, `type-checker.md` §13 I8b step 3).
    pub fn moved_out(self) -> Slot {
        Slot {
            live: false,
            ..self
        }
    }

    /// The unit value (no information; always initialised).
    pub fn unit() -> Slot {
        Slot::val(0)
    }

    /// An uninitialised slot: any read is `ub: uninit-read` (design §5.2,
    /// F6's `ub_uninit_read_through_out`). It is LIVE but uninitialised —
    /// `&out x` targets exactly such a slot (design §3.3's `borrow_out` row).
    pub fn uninit() -> Slot {
        Slot {
            bits: 0,
            prov: crate::mem::PROV_NONE,
            init: false,
            live: true,
            secret: false,
        }
    }
}
