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
