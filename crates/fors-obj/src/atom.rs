//! An atom (§4.1): `[code][cold trap tail][literal pool]`, position
//! independent except for its `bl` relocations, plus its trap-table rows.
//! The backend emits atoms and the linker places them; the type lives here
//! so neither of those crates depends on the other.

/// A `bl <target>` whose 26-bit word offset the linker fills in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reloc {
    /// Byte offset of the `bl` word inside the atom.
    pub offset: u32,
    /// The callee atom's name.
    pub target: String,
}

/// One trap-table row (§4.1): `(pc offset u32, site ordinal u16, kind u8,
/// col u16, line relative to the declaration u32)`. M2-0 records the rows;
/// the runtime handler that reads them (and the file/line tables) is M2-3's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrapRow {
    /// Byte offset of the site's `brk` inside the atom.
    pub pc: u32,
    pub site: u16,
    pub kind: u8,
    pub col: u16,
    pub line: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Atom {
    /// The symbol other atoms' relocations name.
    pub name: String,
    /// Little-endian instruction words, then the trap tail and the literal
    /// pool. Always a multiple of 4 bytes.
    pub code: Vec<u8>,
    pub relocs: Vec<Reloc>,
    pub traps: Vec<TrapRow>,
}

impl Atom {
    pub fn new(name: impl Into<String>) -> Atom {
        Atom {
            name: name.into(),
            code: Vec::new(),
            relocs: Vec::new(),
            traps: Vec::new(),
        }
    }

    /// Appends one instruction word.
    pub fn push_word(&mut self, w: u32) {
        self.code.extend_from_slice(&w.to_le_bytes());
    }

    /// The instruction word at byte offset `off`.
    pub fn word_at(&self, off: usize) -> u32 {
        u32::from_le_bytes([
            self.code[off],
            self.code[off + 1],
            self.code[off + 2],
            self.code[off + 3],
        ])
    }

    /// Every word of the atom (the literal pool included, padded).
    pub fn words(&self) -> impl Iterator<Item = u32> + '_ {
        self.code.chunks(4).map(|c| {
            let mut b = [0u8; 4];
            b[..c.len()].copy_from_slice(c);
            u32::from_le_bytes(b)
        })
    }
}

/// Is `w` an `svc #imm16` (PLAN R9's syscall scan)?
pub fn is_svc(w: u32) -> bool {
    w & 0xFFE0_001F == 0xD400_0001
}

/// Is `w` a `brk #imm16`, and with which immediate?
pub fn brk_imm(w: u32) -> Option<u16> {
    if w & 0xFFE0_001F == 0xD420_0000 {
        Some(((w >> 5) & 0xFFFF) as u16)
    } else {
        None
    }
}
