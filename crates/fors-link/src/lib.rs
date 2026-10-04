//! `fors-link` (§4): atom placement and image building. M2-0 has only the
//! cold path, [`link_once`]: place the runtime atoms, then the Fors atoms,
//! each 16-byte aligned; resolve every `bl` to its callee directly (no stub
//! table until calls between Fors atoms exist, M2-2); build the image
//! directory; hand `__text` to `fors-obj`'s writer, which signs it. The
//! incremental relink (clonefile → patch → rehash → rename) is M2-7's.

#![deny(unsafe_code)]

use std::collections::BTreeMap;

use fors_obj::macho::{ExecSpec, Layout, layout};
use fors_obj::{Atom, sign};

/// One placed atom: name, offset inside `__text`, length.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Placed {
    pub name: String,
    pub start: u32,
    pub len: u32,
}

/// The linked, unsigned `__text` and everything the writer needs.
#[derive(Clone, Debug)]
pub struct Linked {
    pub text: Vec<u8>,
    pub entry: u32,
    pub atoms: Vec<Placed>,
    /// `__fors_dir`: `(atom start u32, atom len u32, decl_line_row u32,
    /// reserved u32)` per atom, sorted by address.
    pub dir: Vec<u8>,
    /// `__fors_lines`: the per-file declaration line tables — a zero row
    /// count in M2-0 (trap reporting, which reads them, is M2-3's).
    pub lines: Vec<u8>,
}

/// The finished image.
#[derive(Clone, Debug)]
pub struct Image {
    pub bytes: Vec<u8>,
    pub atoms: Vec<Placed>,
    /// File offset of `__text` (atom `start`s are relative to it).
    pub text_off: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LinkError {
    DuplicateSymbol(String),
    UndefinedSymbol { from: String, target: String },
    BranchOutOfRange { from: String, target: String },
    NoEntry(String),
    BadReloc { atom: String, offset: u32 },
}

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "link: {self:?}")
    }
}

impl std::error::Error for LinkError {}

/// The atom alignment inside `__text`.
pub const ATOM_ALIGN: usize = 16;

/// Places `runtime` then `fors` atoms and resolves every relocation.
/// `entry` names the `LC_MAIN` atom.
pub fn place(fors: &[Atom], runtime: &[Atom], entry: &str) -> Result<Linked, LinkError> {
    let mut text: Vec<u8> = Vec::new();
    let mut placed = Vec::new();
    let mut at: BTreeMap<&str, u32> = BTreeMap::new();
    for a in runtime.iter().chain(fors) {
        let start = text.len() as u32;
        if at.insert(a.name.as_str(), start).is_some() {
            return Err(LinkError::DuplicateSymbol(a.name.clone()));
        }
        text.extend_from_slice(&a.code);
        placed.push(Placed {
            name: a.name.clone(),
            start,
            len: a.code.len() as u32,
        });
        text.resize(text.len().div_ceil(ATOM_ALIGN) * ATOM_ALIGN, 0);
    }
    for (a, p) in runtime.iter().chain(fors).zip(&placed) {
        for r in &a.relocs {
            let Some(&target) = at.get(r.target.as_str()) else {
                return Err(LinkError::UndefinedSymbol {
                    from: a.name.clone(),
                    target: r.target.clone(),
                });
            };
            let site = p.start + r.offset;
            let i = site as usize;
            if r.offset % 4 != 0 || r.offset + 4 > p.len {
                return Err(LinkError::BadReloc {
                    atom: a.name.clone(),
                    offset: r.offset,
                });
            }
            let w = u32::from_le_bytes(text[i..i + 4].try_into().expect("4 bytes"));
            // Only `bl` (0b100101) carries a relocation in M2-0.
            if w & 0xFC00_0000 != 0x9400_0000 {
                return Err(LinkError::BadReloc {
                    atom: a.name.clone(),
                    offset: r.offset,
                });
            }
            let delta = (i64::from(target) - i64::from(site)) / 4;
            if !(-(1i64 << 25)..(1i64 << 25)).contains(&delta) {
                return Err(LinkError::BranchOutOfRange {
                    from: a.name.clone(),
                    target: r.target.clone(),
                });
            }
            let patched = (w & 0xFC00_0000) | ((delta as u32) & 0x03FF_FFFF);
            text[i..i + 4].copy_from_slice(&patched.to_le_bytes());
        }
    }
    let entry_off = *at
        .get(entry)
        .ok_or_else(|| LinkError::NoEntry(entry.to_string()))?;
    let mut dir = Vec::with_capacity(16 * placed.len());
    for p in &placed {
        dir.extend_from_slice(&p.start.to_le_bytes());
        dir.extend_from_slice(&p.len.to_le_bytes());
        dir.extend_from_slice(&0u32.to_le_bytes()); // decl_line_row (M2-3)
        dir.extend_from_slice(&0u32.to_le_bytes());
    }
    Ok(Linked {
        text,
        entry: entry_off,
        atoms: placed,
        dir,
        lines: 0u32.to_le_bytes().to_vec(),
    })
}

/// Lays out the Mach-O for `l` (unsigned; [`sign::sign`] finishes it).
pub fn image_layout(l: &Linked, identifier: &str) -> Layout {
    let starts: Vec<u32> = l.atoms.iter().map(|p| p.start).collect();
    layout(&ExecSpec {
        text: &l.text,
        entry: l.entry,
        function_starts: &starts,
        dir: &l.dir,
        lines: &l.lines,
        identifier,
    })
}

/// The cold link: place, lay out, sign. `identifier` is the output's file
/// stem (it is part of the signature).
pub fn link_once(
    fors: &[Atom],
    runtime: &[Atom],
    entry: &str,
    identifier: &str,
) -> Result<Image, LinkError> {
    let l = place(fors, runtime, entry)?;
    let lay = image_layout(&l, identifier);
    let text_off = lay.text_off;
    let bytes = sign::sign(lay, identifier);
    Ok(Image {
        bytes,
        atoms: l.atoms,
        text_off,
    })
}
