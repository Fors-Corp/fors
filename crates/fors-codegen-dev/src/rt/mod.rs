//! The runtime atoms (§2.2, ch04 R7: the shim is not Fors source): built in
//! Rust with `fors-asm`, linked into every image ahead of the Fors atoms.
//! M2-0 has the entry shim ([`entry`]) and the three output routines
//! ([`write`]); the trap handler, the buffered `Stdout` and the root
//! capabilities arrive in M2-3/M2-5.

pub mod entry;
pub mod write;

use fors_asm::{EncodeError, Inst};
use fors_obj::Atom;

/// `_main`: the `LC_MAIN` entry point (the shim).
pub const ENTRY: &str = "_main";
/// The Fors `main` atom the shim calls.
pub const FORS_MAIN: &str = "_fors_main";
/// `_fors_rt_write(fd, ptr, len)`.
pub const WRITE: &str = "_fors_rt_write";
/// `_fors_rt_write_uint(u64)`.
pub const WRITE_UINT: &str = "_fors_rt_write_uint";
/// `_fors_rt_write_line(ptr, len)`.
pub const WRITE_LINE: &str = "_fors_rt_write_line";

/// The ONLY atoms allowed to contain `svc` (E10: raw `write` for one
/// increment; M2-3 deletes this entry and turns `image_contains_no_svc`
/// strict).
pub const RUNTIME_SYSCALL_ATOMS: &[&str] = &[WRITE];

/// Every runtime atom, in placement order (the shim first).
pub fn runtime_atoms() -> Vec<Atom> {
    vec![
        entry::main_shim(),
        write::write(),
        write::write_uint(),
        write::write_line(),
    ]
}

/// Assembles `insts` into `atom`, panicking on an encoding error (the
/// runtime is fixed code: an error is a bug in this file, caught by every
/// test that builds an image).
pub(crate) fn assemble(atom: &mut Atom, insts: &[Result<Inst, EncodeError>]) {
    for (i, r) in insts.iter().enumerate() {
        let inst = match r {
            Ok(i) => i,
            Err(e) => panic!("runtime atom {} word {i}: {e:?}", atom.name),
        };
        match fors_asm::encode(inst) {
            Ok(w) => atom.push_word(w),
            Err(e) => panic!("runtime atom {} word {i}: {e:?}", atom.name),
        }
    }
}
