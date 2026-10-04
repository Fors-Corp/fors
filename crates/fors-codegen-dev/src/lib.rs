//! `fors-codegen-dev`: the dev-tier code generator
//! (`docs/design/m2-dev-backend.md` §2). Consumes OIR only (ch05 R1:
//! `codegen_dev_consumes_only_oir`), emits atoms.
//!
//! - [`stencil`]: the copy-and-patch stencils over `fors-asm` (E2) and their
//!   static table; [`stencil::int`] has the integer semantics;
//! - [`select`]: OIR → LIR-dev ([`lir`]), one row per stencil instance;
//! - [`frame`]: one 8-byte slot per value and per place root;
//! - [`trap`]: the cold tail, one `brk` per site, per-atom trap rows;
//! - [`emit`]: LIR-dev → atom;
//! - [`rt`]: the runtime atoms (entry shim, output routines).
//!
//! No hash-ordered container anywhere (determinism: `codegen_is_deterministic`
//! and the source scan `backend_src_has_no_hash_containers`).

#![deny(unsafe_code)]

pub mod emit;
pub mod frame;
pub mod lir;
pub mod rt;
pub mod select;
pub mod stencil;
pub mod trap;

#[cfg(feature = "inject-miscompile")]
pub mod inject;

use fors_obj::Atom;
use fors_oir::{OirFunc, Refusal};

pub use rt::{RUNTIME_SYSCALL_ATOMS, runtime_atoms};

/// The reason a verifier failure is reported under (the OIR handed in was
/// malformed: a compiler bug upstream, refused rather than compiled).
pub const OIR_INVALID: &str = "OIR failed verification";

/// Verifies, selects and emits `f` as the atom `name`.
pub fn compile(f: &OirFunc, name: &str) -> Result<Atom, Refusal> {
    fors_oir::verify(f).map_err(|e| Refusal {
        decl: f.decl,
        inst: None,
        op: e.name().to_string(),
        reason: format!("{OIR_INVALID}: {e}"),
    })?;
    let lir = select::select(f)?;
    emit::emit(&lir, f, name)
}
