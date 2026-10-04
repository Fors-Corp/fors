//! The output routines. Their semantics equal the interpreter's intrinsic
//! rows byte for byte (`fors-interp/src/exec.rs`): `stdout_write_uint` is
//! base 10, no locale, no newline; `stdout_write_line` is the bytes then
//! `\n`.
//!
//! `_fors_rt_write` is TEMPORARY (E10): raw `svc #0x80` with
//! `SYS_write = 4`, the spike-proven path that needs no chained-fixup bind.
//! It is the one entry of [`super::RUNTIME_SYSCALL_ATOMS`]; M2-3 replaces it
//! with an import of libSystem's `write`.

use fors_asm::Inst;
use fors_asm::Reg;
use fors_asm::inst::{AddrMode, PairIndex};
use fors_asm::operand::{BranchOffset, Cond, RegShift, SImm7Scaled, UScaledImm12, Uimm12Lsl};
use fors_obj::{Atom, Reloc};

use super::{WRITE, WRITE_LINE, WRITE_UINT, assemble};

const SYS_WRITE: u16 = 4;
const EINTR: u64 = 4;

fn x(n: u8) -> Reg {
    Reg::x(n)
}

fn br(words: i64, bits: u32) -> Result<BranchOffset, fors_asm::EncodeError> {
    BranchOffset::new(4 * words, bits, "rt branch")
}

/// `_fors_rt_write(x0 = fd, x1 = ptr, x2 = len)`: loops on short writes,
/// retries `EINTR`, stops on any other error or on a zero-byte write (never
/// spins). Leaf; clobbers `x0..x5`, `x16`.
pub fn write() -> Atom {
    let mut a = Atom::new(WRITE);
    let none = RegShift::none();
    assemble(
        &mut a,
        &[
            /* 0 */ Inst::mov_reg(x(3), x(0)),
            /* 1 */ Inst::mov_reg(x(4), x(1)),
            /* 2 */ Inst::mov_reg(x(5), x(2)),
            /* 3 loop */ br(13, 19).map(|o| Inst::cbz(x(5), o)), // -> 16 done
            /* 4 */ Inst::mov_reg(x(0), x(3)),
            /* 5 */ Inst::mov_reg(x(1), x(4)),
            /* 6 */ Inst::mov_reg(x(2), x(5)),
            /* 7 */ Inst::movz(x(16), SYS_WRITE, 0),
            /* 8 */ Ok(Inst::svc(0x80)),
            /* 9 */ br(5, 19).map(|o| Inst::b_cond(Cond::CS, o)), // -> 14 err
            /* 10 */ br(6, 19).map(|o| Inst::cbz(x(0), o)), // -> 16 done
            /* 11 */ Inst::add_shifted(x(4), x(4), x(0), none),
            /* 12 */ Inst::sub_shifted(x(5), x(5), x(0), none),
            /* 13 */ br(-10, 26).map(Inst::b), // -> 3 loop
            /* 14 err */ Uimm12Lsl::new(EINTR).and_then(|i| Inst::cmp_imm(x(0), i)),
            /* 15 */ br(-12, 19).map(|o| Inst::b_cond(Cond::EQ, o)), // -> 3 loop
            /* 16 done */ Inst::ret(x(30)),
        ],
    );
    a
}

/// `_fors_rt_write_uint(x0 = v)`: decimal into a 24-byte stack buffer
/// (`u64::MAX` has 20 digits), then one `_fors_rt_write(1, …)`.
pub fn write_uint() -> Atom {
    let mut a = Atom::new(WRITE_UINT);
    assemble(
        &mut a,
        &[
            /* 0 */
            SImm7Scaled::new(-48, 8)
                .and_then(|o| Inst::stp(x(29), x(30), Reg::sp(), o, PairIndex::PreIndex)),
            /* 1 */ Inst::mov_sp(x(29), Reg::sp()),
            /* 2 */
            Uimm12Lsl::new(40).and_then(|i| Inst::add_imm(x(4), Reg::sp(), i)), // end
            /* 3 */ Inst::mov_reg(x(5), x(4)),
            /* 4 */ Inst::movz(x(6), 10, 0),
            /* 5 loop */ Inst::udiv(x(7), x(0), x(6)),
            /* 6 */ Inst::msub(x(8), x(7), x(6), x(0)),
            /* 7 */
            Uimm12Lsl::new(u64::from(b'0')).and_then(|i| Inst::add_imm(x(8), x(8), i)),
            /* 8 */ Uimm12Lsl::new(1).and_then(|i| Inst::sub_imm(x(5), x(5), i)),
            /* 9 */
            UScaledImm12::new(0, 1)
                .and_then(|o| Inst::strb(Reg::w(8), x(5), AddrMode::UnsignedOffset(o))),
            /* 10 */ Inst::mov_reg(x(0), x(7)),
            /* 11 */ br(-6, 19).map(|o| Inst::cbnz(x(0), o)), // -> 5 loop
            /* 12 */ Inst::movz(x(0), 1, 0),
            /* 13 */ Inst::mov_reg(x(1), x(5)),
            /* 14 */ Inst::sub_shifted(x(2), x(4), x(5), RegShift::none()),
            /* 15 */ br(0, 26).map(Inst::bl),
            /* 16 */
            SImm7Scaled::new(48, 8)
                .and_then(|o| Inst::ldp(x(29), x(30), Reg::sp(), o, PairIndex::PostIndex)),
            /* 17 */ Inst::ret(x(30)),
        ],
    );
    a.relocs.push(Reloc {
        offset: 15 * 4,
        target: WRITE.to_string(),
    });
    a
}

/// `_fors_rt_write_line(x0 = ptr, x1 = len)`: the bytes, then `\n`.
pub fn write_line() -> Atom {
    let mut a = Atom::new(WRITE_LINE);
    assemble(
        &mut a,
        &[
            /* 0 */
            SImm7Scaled::new(-32, 8)
                .and_then(|o| Inst::stp(x(29), x(30), Reg::sp(), o, PairIndex::PreIndex)),
            /* 1 */ Inst::mov_sp(x(29), Reg::sp()),
            /* 2 */ Inst::mov_reg(x(2), x(1)),
            /* 3 */ Inst::mov_reg(x(1), x(0)),
            /* 4 */ Inst::movz(x(0), 1, 0),
            /* 5 */ br(0, 26).map(Inst::bl),
            /* 6 */ Inst::movz(Reg::w(3), u16::from(b'\n'), 0),
            /* 7 */
            UScaledImm12::new(16, 1)
                .and_then(|o| Inst::strb(Reg::w(3), Reg::sp(), AddrMode::UnsignedOffset(o))),
            /* 8 */ Inst::movz(x(0), 1, 0),
            /* 9 */ Uimm12Lsl::new(16).and_then(|i| Inst::add_imm(x(1), Reg::sp(), i)),
            /* 10 */ Inst::movz(x(2), 1, 0),
            /* 11 */ br(0, 26).map(Inst::bl),
            /* 12 */
            SImm7Scaled::new(32, 8)
                .and_then(|o| Inst::ldp(x(29), x(30), Reg::sp(), o, PairIndex::PostIndex)),
            /* 13 */ Inst::ret(x(30)),
        ],
    );
    for w in [5u32, 11] {
        a.relocs.push(Reloc {
            offset: 4 * w,
            target: WRITE.to_string(),
        });
    }
    a
}
