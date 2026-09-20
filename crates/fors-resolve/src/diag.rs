//! Resolver diagnostics: a byte range plus a stable code. Ch08 rules code
//! as `N00xx` (rule number = code, per ch08's "Drafting decisions"); ch04
//! rules implemented here code as `A00xx` the same way. Append, never
//! renumber. Never a panic path.

// MARC: the type-checker design (§4.4, §3 fork 15) widens the code space
// to one enum (`N | A | T | O | F | D`) shared by every phase; that enum
// now lives in `fors-index::diag` (the crate every checking phase already
// depends on) and this module re-exports it, rather than keeping a second,
// narrower definition here. `N`/`A` and their meaning are unchanged.
pub use fors_index::diag::Code;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub start: u32,
    pub end: u32,
    pub code: Code,
    pub message: String,
}

impl Diagnostic {
    pub fn new(start: u32, end: u32, code: Code, message: String) -> Self {
        Diagnostic { start, end, code, message }
    }
}
