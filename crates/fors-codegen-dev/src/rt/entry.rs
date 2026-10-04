//! `_main` (§3 "Entry"): build a frame, `bl` the Fors `main`, return 0 to
//! dyld — `LC_MAIN` turns the return value into the process's `exit`
//! status. FPCR, `SIGPIPE`, the `SIGTRAP` handler, terminal detection and
//! the root capabilities join in M2-3/M2-5/M2-6.

use fors_asm::Inst;
use fors_asm::Reg;
use fors_asm::inst::PairIndex;
use fors_asm::operand::{BranchOffset, SImm7Scaled};
use fors_obj::{Atom, Reloc};

use super::{ENTRY, FORS_MAIN, assemble};

pub fn main_shim() -> Atom {
    let mut a = Atom::new(ENTRY);
    let x = Reg::x;
    assemble(
        &mut a,
        &[
            SImm7Scaled::new(-16, 8)
                .and_then(|o| Inst::stp(x(29), x(30), Reg::sp(), o, PairIndex::PreIndex)),
            Inst::mov_sp(x(29), Reg::sp()),
            BranchOffset::new(0, 26, "bl").map(Inst::bl),
            Inst::movz(Reg::w(0), 0, 0),
            SImm7Scaled::new(16, 8)
                .and_then(|o| Inst::ldp(x(29), x(30), Reg::sp(), o, PairIndex::PostIndex)),
            Inst::ret(x(30)),
        ],
    );
    a.relocs.push(Reloc {
        offset: 8,
        target: FORS_MAIN.to_string(),
    });
    a
}
