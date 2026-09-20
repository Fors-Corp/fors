//! Encoding failures. Every fallible operand constructor and `encode()`
//! itself return `Result<_, EncodeError>` — this crate never panics on bad
//! input and never silently emits a wrong word for one.

use core::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EncodeError {
    /// An immediate did not fit the field it was destined for.
    ImmediateOutOfRange { what: &'static str, value: i64 },
    /// A 64-bit value has no AArch64 bitmask-immediate (N:immr:imms) encoding.
    UnencodableLogicalImmediate { value: u64, is64: bool },
    /// A PC-relative offset was not a multiple of 4 (branches/ADR family
    /// live on the instruction stream, which is word-aligned).
    MisalignedOffset { what: &'static str, value: i64 },
    /// A shift/extend amount is legal in general but not for this specific
    /// instruction form (e.g. `ROR` on ADD/SUB shifted-register, or a
    /// shift amount that doesn't fit the operand width).
    InvalidShiftForForm { what: &'static str },
    /// The two register operands disagree on width (mixed `X`/`W`) where
    /// the architecture requires them to match.
    RegisterWidthMismatch { what: &'static str },
    /// A register field that must be a specific kind (e.g. SP for the base
    /// of `LDP`/`STP`) was given something else.
    InvalidRegisterForForm { what: &'static str },
}

impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeError::ImmediateOutOfRange { what, value } => {
                write!(f, "immediate out of range for {what}: {value}")
            }
            EncodeError::UnencodableLogicalImmediate { value, is64 } => {
                let width = if *is64 { 64 } else { 32 };
                write!(
                    f,
                    "0x{value:x} has no {width}-bit bitmask-immediate encoding"
                )
            }
            EncodeError::MisalignedOffset { what, value } => {
                write!(f, "{what} offset {value} is not 4-byte aligned")
            }
            EncodeError::InvalidShiftForForm { what } => {
                write!(f, "shift/extend not valid for {what}")
            }
            EncodeError::RegisterWidthMismatch { what } => {
                write!(f, "register width mismatch in {what}")
            }
            EncodeError::InvalidRegisterForForm { what } => {
                write!(f, "invalid register for {what}")
            }
        }
    }
}

impl std::error::Error for EncodeError {}
