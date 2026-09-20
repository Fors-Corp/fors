//! AArch64 instruction encoder for Fors's own dev backend (milestone M2:
//! own dev backend, own object writer — the first brick after the
//! feasibility spike at `spikes/aarch64-macho/`).
//!
//! Typed operands ([`reg::Reg`], [`reg::FpReg`], [`operand::Cond`], shifts,
//! extends, and validated immediates), one [`inst::Inst`] enum whose
//! variants match encoding shapes rather than mnemonics (aliases like
//! `CMP`/`MOV`/`CSET` are constructor functions — see `inst`'s module
//! docs), and [`encode::encode`] turning a validated `Inst` into its 32-bit
//! word. An out-of-range immediate, an unencodable logical/float
//! immediate, or a misaligned branch offset is always an `Err`, never a
//! panic and never a silently wrong encoding.
//!
//! # Oracle
//!
//! `tests/oracle.rs` (macOS aarch64 only) generates one assembly line per
//! test case, assembles it with `clang -c -x assembler`, reads the
//! `__text` bytes back with `otool -s __TEXT __text`, and compares every
//! word against `encode()`. `tests/golden.rs` replays a deterministic
//! subset of the same cases against a checked-in golden file
//! (`tests/golden/*.txt`, format `<assembly text>\t<hex word>` per line)
//! so Linux CI still exercises the encoder without an AArch64 assembler.
//!
//! To regenerate the golden files after a deliberate encoding change, on
//! an macOS aarch64 host:
//! ```text
//! cargo test -p fors-asm --test oracle -- --ignored regen_golden --exact
//! ```
//! (it panics rather than writing a golden file that disagrees with the
//! assembler, so a passing regen run is itself an oracle-verified update).
//!
//! # Overflow traps need nothing extra
//!
//! A checked add/sub is the flag-setting form (`ADDS`/`SUBS`, already in
//! this crate) followed by `B.VS` to an overflow handler — no dedicated
//! "trapping add" instruction, and the encoder needs no extra support for
//! it:
//! ```
//! # use fors_asm::inst::Inst;
//! # use fors_asm::operand::{BranchOffset, Cond, RegShift};
//! # use fors_asm::reg::Reg;
//! // adds x0, x1, x2        ; x0 = x1 + x2, sets NZCV (including V on overflow)
//! let add = Inst::adds_shifted(Reg::x(0), Reg::x(1), Reg::x(2), RegShift::none()).unwrap();
//! // b.vs <overflow_handler> ; taken iff the add overflowed
//! let branch_on_overflow = Inst::b_cond(Cond::VS, BranchOffset::new(64, 19, "b.vs").unwrap());
//! # let _ = (add, branch_on_overflow);
//! ```
//! A checked 64-bit signed multiply is `MUL` (the low 64 bits of the
//! product) plus `SMULH` (the high 64 bits) compared against the
//! sign-extension of the low half (`hi == lo >> 63` means no overflow) —
//! again just the building blocks this crate already encodes, combined
//! with `CMP`/`B.NE` (or `CSEL`) rather than any dedicated instruction:
//! ```
//! # use fors_asm::inst::Inst;
//! # use fors_asm::reg::Reg;
//! let lo = Inst::mul(Reg::x(0), Reg::x(1), Reg::x(2)).unwrap(); // low 64 bits
//! let hi = Inst::smulh(Reg::x(3), Reg::x(1), Reg::x(2)).unwrap(); // high 64 bits
//! // ... cmp x3, x0, asr #63 ; then b.ne <overflow_handler> ...
//! # let _ = (lo, hi);
//! ```

pub mod bitmask;
pub mod display;
pub mod encode;
pub mod error;
pub mod fp;
pub mod fpimm;
pub mod inst;
pub mod operand;
pub mod reg;

pub use encode::encode;
pub use error::EncodeError;
pub use inst::Inst;
pub use reg::{FpReg, Reg};
