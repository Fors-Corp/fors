//! Index/module diagnostics: a byte offset range plus a stable `N00xx`
//! code, matching chapter 08's rule numbers (`Rule k` => `N00k`, as ch08
//! "Drafting decisions" specifies). Append, never renumber. Never a panic
//! path.

use crate::ids::FileId;

#[repr(u16)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DiagCode {
    /// Ch08 Rule 1: a `module` header's path does not equal the module
    /// name derived from the file's location.
    HeaderPathMismatch = 1,
    /// Ch08 Rule 7: the module graph has a cycle.
    ImportCycle = 7,
    /// Ch08 Rule 8: a `use` path's edge targets the module it appears in.
    SelfImport = 8,
    /// Ch08 Rule 24: an illegal source file or directory segment name.
    IllegalFileName = 24,
}

impl DiagCode {
    pub fn as_str(self) -> &'static str {
        match self {
            DiagCode::HeaderPathMismatch => "N0001",
            DiagCode::ImportCycle => "N0007",
            DiagCode::SelfImport => "N0008",
            DiagCode::IllegalFileName => "N0024",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    /// The file whose bytes `start..end` index: byte ranges alone do not
    /// identify a file (two files often have a `use` at the same offset).
    pub file: FileId,
    pub start: u32,
    pub end: u32,
    pub code: DiagCode,
    pub message: String,
}

impl Diagnostic {
    pub fn new(file: FileId, start: u32, end: u32, code: DiagCode, message: String) -> Self {
        Diagnostic { file, start, end, code, message }
    }
}

// MARC: the type-checker design (§4.4, §8) widens this crate's diagnostic
// code space to one enum shared by every phase, so `fors-resolve`'s
// `Code::{N, A}` can gain `T`/`O`/`F`/`D` letters without a third
// definition. `DiagCode` (this crate's own ch08 codes) keeps its existing
// shape — nothing here renames or removes it — and folds into `Code::N`
// via `From`, since its discriminants already equal the ch08 rule number.
/// One diagnostic code across every phase (ch08 N, ch04 A, ch09 T, ch01 O,
/// ch02 F, ch03 D — letters per the type-checker design §3 fork 15, a
/// drafting default for the non-ch08/ch09 letters per design §14 Q1). The
/// wrapped `u16` is always the rule number in that chapter, never a
/// separately-assigned code: append a chapter's obligations as they gain
/// diagnostics, never renumber one already emitted.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Code {
    /// Chapter 8 (names).
    N(u16),
    /// Chapter 4 (authority).
    A(u16),
    /// Chapter 9 (types).
    T(u16),
    /// Chapter 1 (ownership/moves/brands).
    O(u16),
    /// Chapter 2 (errors/contracts).
    F(u16),
    /// Chapter 3 (numerics/arrays/CHECK positions).
    D(u16),
}

impl Code {
    pub fn as_string(self) -> String {
        match self {
            Code::N(k) => format!("N{k:04}"),
            Code::A(k) => format!("A{k:04}"),
            Code::T(k) => format!("T{k:04}"),
            Code::O(k) => format!("O{k:04}"),
            Code::F(k) => format!("F{k:04}"),
            Code::D(k) => format!("D{k:04}"),
        }
    }
}

impl From<DiagCode> for Code {
    fn from(d: DiagCode) -> Code {
        Code::N(d as u16)
    }
}
