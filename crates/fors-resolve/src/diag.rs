//! Resolver diagnostics: a byte range plus a stable code. Ch08 rules code
//! as `N00xx` (rule number = code, per ch08's "Drafting decisions"); ch04
//! rules implemented here code as `A00xx` the same way. Append, never
//! renumber. Never a panic path.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Code {
    /// Chapter 8 (names), rule number equals the code.
    N(u16),
    /// Chapter 4 (authority), rule number equals the code.
    A(u16),
}

impl Code {
    pub fn as_string(self) -> String {
        match self {
            Code::N(k) => format!("N{k:04}"),
            Code::A(k) => format!("A{k:04}"),
        }
    }
}

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
