//! TEST-ONLY seeded stencil miscompiles (design §5 "inject-miscompile"),
//! compiled only under the `inject-miscompile` feature, which only
//! `fors-oracle`'s `[dev-dependencies]` enables. A test arms one
//! [`Mutation`]; `select` then picks a deliberately WRONG stencil for the
//! matching rows, and the native differential must report `mismatch` rows
//! — the vacuity check that the runner really executes native code.
//!
//! The switch is one process-global atomic (the differential's workers are
//! threads), so a test that arms it must live in its own test binary.

use std::sync::atomic::{AtomicU8, Ordering};

use crate::stencil::int::{ArMode, BinOp, Key, LogicOp};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Mutation {
    /// `wrap_add` emitted as `wrap_sub`.
    WrapAddIsSub = 1,
    /// `xor` emitted as `or`.
    XorIsOr = 2,
}

static ARMED: AtomicU8 = AtomicU8::new(0);

/// Arms `m` (or disarms with `None`) for every later compile in this
/// process.
pub fn arm(m: Option<Mutation>) {
    ARMED.store(m.map_or(0, |m| m as u8), Ordering::SeqCst);
}

/// The stencil `select` uses instead of `key` while a mutation is armed.
pub fn mutate(key: Key) -> Key {
    match (ARMED.load(Ordering::SeqCst), key) {
        (
            1,
            Key::Bin {
                op: BinOp::Add,
                mode: ArMode::Wrap,
                ty,
            },
        ) => Key::Bin {
            op: BinOp::Sub,
            mode: ArMode::Wrap,
            ty,
        },
        (2, Key::Logic { op: LogicOp::Xor }) => Key::Logic { op: LogicOp::Or },
        _ => key,
    }
}
