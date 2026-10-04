//! `fors-oir`: the dev backend's OIR (`docs/design/m2-dev-backend.md`
//! §2.1). ch05 R1 fixes the level order FMIR → OIR → LIR → atoms; this crate
//! is the OIR level: [`ir`] (the struct-of-arrays model), [`from_fmir`] (one
//! linear pass, M2-0's straight-line subset, precise refusals), [`alias`]
//! (alias classes from FMIR seeds), [`verify`] (R4/R5/R6/R12) and [`dump`].

#![deny(unsafe_code)]

pub mod alias;
pub mod dump;
pub mod from_fmir;
pub mod ir;
pub mod verify;

pub use from_fmir::{FmirInput, Refusal, from_fmir};
pub use ir::{
    AliasClass, AliasSource, CmpPred, LowTy, Mode, NONE, OirFunc, OirOp, Rows, Slot, Term,
    TrapKind, ValueId, Values,
};
pub use verify::{VerifyError, verify};
