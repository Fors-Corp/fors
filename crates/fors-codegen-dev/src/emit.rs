//! `emit` (§2.1): LIR-dev → atom. Two linear passes: the first lays out
//! the code (stencil lengths are static), the cold trap tail (one `brk` per
//! site) and the literal pool; the second copies each stencil's words and
//! patches its holes. Calls into the runtime are left as `bl #0` plus a
//! [`fors_obj::Reloc`]: the linker resolves them.

use fors_obj::{Atom, Reloc};
use fors_oir::{OirFunc, Refusal};

use crate::lir::{Lir, NO_LIT};
use crate::stencil::int::Key;
use crate::stencil::{Field, hole_fits, table};
use crate::trap::Tail;

/// The refusal for an atom whose branches or literals outgrow their
/// encodings (a `tbnz` reaches +-32 KiB, `b.cond`/`adr` +-1 MiB).
pub const TOO_LARGE: &str = "atom too large for its branch or literal ranges";

/// Emits `lir` (selected from `f`) as the atom `name`.
pub fn emit(lir: &Lir, f: &OirFunc, name: &str) -> Result<Atom, Refusal> {
    let t = table();
    // Pass 1: code length, trap sites, literal pool.
    let mut code_words = 0u32;
    let mut tail = Tail::default();
    let mut first_site = Vec::with_capacity(lir.len());
    for i in 0..lir.len() {
        let s = &t.stencils[lir.stencil[i] as usize];
        first_site.push(tail.sites.len());
        for &k in &s.sites {
            tail.add(k, lir.site[i]);
        }
        code_words += s.words.len() as u32;
    }
    let tail_start = 4 * code_words;
    let pool_start = tail_start + 4 * tail.sites.len() as u32;
    let mut pool: Vec<u8> = Vec::new();
    let mut lit_pos: Vec<Option<u32>> = vec![None; f.strings.len()];
    for i in 0..lir.len() {
        let l = lir.lit[i];
        if l != NO_LIT && lit_pos[l as usize].is_none() {
            lit_pos[l as usize] = Some(pool_start + pool.len() as u32);
            pool.extend_from_slice(&f.strings[l as usize]);
        }
    }

    // Pass 2: copy and patch.
    let mut words: Vec<u32> = Vec::with_capacity(code_words as usize + tail.sites.len());
    let mut relocs = Vec::new();
    for i in 0..lir.len() {
        let s = &t.stencils[lir.stencil[i] as usize];
        let start = 4 * words.len() as u32;
        let mut fill = lir.fill[i];
        for (k, _) in s.sites.iter().enumerate() {
            let brk = Tail::brk_pos(tail_start, first_site[i] + k);
            fill.trap[k] = i64::from(brk) - i64::from(start);
        }
        if lir.lit[i] != NO_LIT {
            let at = lit_pos[lir.lit[i] as usize].expect("laid out in pass 1");
            fill.lit = i64::from(at) - i64::from(start);
        }
        for h in &s.holes {
            if let Field::Call(sym) = h.field {
                // `bl #0` until the linker places the callee.
                fill.call = 4 * i64::from(h.word);
                relocs.push(Reloc {
                    offset: start + 4 * u32::from(h.word),
                    target: sym.symbol().to_string(),
                });
            }
        }
        if let Some(h) = s.holes.iter().find(|h| !hole_fits(h, &fill)) {
            return Err(Refusal {
                decl: f.decl,
                inst: (lir.oir_row[i] != u32::MAX).then_some(lir.oir_row[i]),
                op: format!("{:?} ({:?} hole)", s.key, h.kind),
                reason: TOO_LARGE.to_string(),
            });
        }
        s.instantiate_into(&fill, &mut words);
    }
    debug_assert_eq!(4 * words.len() as u32, tail_start);
    for site in &tail.sites {
        let brk = t.get(Key::Brk {
            kind: site.kind as u8,
        });
        words.extend_from_slice(&brk.words);
    }
    let mut atom = Atom::new(name);
    atom.code.reserve(4 * words.len() + pool.len() + 3);
    for w in words {
        atom.push_word(w);
    }
    atom.code.extend_from_slice(&pool);
    while !atom.code.len().is_multiple_of(4) {
        atom.code.push(0);
    }
    atom.relocs = relocs;
    atom.traps = tail.rows(tail_start, &f.sites);
    Ok(atom)
}
