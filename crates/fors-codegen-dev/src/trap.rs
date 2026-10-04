//! Trap sites (§3 "Trap", ch02 R6/R15): every check branches to its own
//! `brk #(TRAP_BRK_BASE + kind)` in the function's COLD TAIL — one
//! instruction per site, no call, no allocation — and the site gets one
//! trap-table row. A site is one (stencil instance, trap kind) pair: a
//! stencil whose two checks can raise the same kind (e.g. `conv_checked`
//! across a sign change) shares one site.

use fors_obj::TrapRow;
use fors_oir::TrapKind;

/// One trap site of an atom, before positions are known.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Site {
    pub kind: TrapKind,
    /// The FMIR site id of the instruction that owns the check.
    pub fmir_site: u32,
}

/// The cold tail under construction.
#[derive(Clone, Debug, Default)]
pub struct Tail {
    pub sites: Vec<Site>,
}

impl Tail {
    /// Registers a site; returns its index in the tail.
    pub fn add(&mut self, kind: TrapKind, fmir_site: u32) -> usize {
        self.sites.push(Site { kind, fmir_site });
        self.sites.len() - 1
    }

    /// Byte offset of site `g`'s `brk` for a tail starting at `tail_start`.
    pub fn brk_pos(tail_start: u32, g: usize) -> u32 {
        tail_start + 4 * g as u32
    }

    /// The trap-table rows for a tail starting at `tail_start`; `lines` is
    /// the function's `(line, col)` per FMIR site id.
    pub fn rows(&self, tail_start: u32, lines: &[(u32, u32)]) -> Vec<TrapRow> {
        self.sites
            .iter()
            .enumerate()
            .map(|(g, s)| {
                let (line, col) = lines.get(s.fmir_site as usize).copied().unwrap_or((0, 0));
                TrapRow {
                    pc: Tail::brk_pos(tail_start, g),
                    site: g as u16,
                    kind: s.kind as u8,
                    col: col.min(u32::from(u16::MAX)) as u16,
                    line,
                }
            })
            .collect()
    }
}
