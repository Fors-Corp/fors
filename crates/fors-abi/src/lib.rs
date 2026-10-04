//! `fors-abi`: the aarch64-apple Fors calling convention as DATA
//! (`docs/design/m2-dev-backend.md` §2.2, §3). Register numbers are plain
//! `u8`s — this crate has no `fors-asm` dependency, so it stays target data
//! that the backend, the linker and the tests all read the same way.
//!
//! M2-0 needs only the register roles ([`regs`]) and the two failure-ABI
//! constants ([`failure`]); the argument/result tables and the ch02 R4
//! classifier arrive with calls (M2-2) and the failure ABI (M2-5).

#![deny(unsafe_code)]

pub mod failure;
pub mod regs;

pub use failure::{FAILURE_INLINE_MAX, FAILURE_TAG_REG};
pub use regs::{RESERVED, SCRATCH, TRAP_BRK_BASE, TRAP_KIND_COUNT, brk_imm};
