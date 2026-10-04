//! The stencil model (§2.1 "What copy-and-patch means here"): a stencil is a
//! short instruction sequence written ONCE in Rust with `fors-asm`
//! constructors ([`int`]), encoded once into a static table with placeholder
//! field values, and described by its HOLES — `(word, bit-field kind, which
//! field)`. Instantiation ([`Stencil::instantiate`]) is a copy of the words
//! plus one bit-field insert per hole; no encoder runs on the fast path.
//!
//! A stencil body is a function of a [`Fill`] (the concrete value of every
//! field), and every instruction that depends on a field is pushed through a
//! [`Seq`] method that records the hole as it goes. So the static table is
//! "the body run on the placeholder fill", and `stencils_match_fors_asm`
//! proves, for 1,000 random fills per stencil, that patching the table
//! equals `fors_asm::encode` of the body run on that fill: the encoder stays
//! the single source of truth and the fast path cannot drift from it.

pub mod int;

use std::collections::BTreeMap;
use std::sync::OnceLock;

use fors_asm::inst::{AddrMode, Inst};
use fors_asm::operand::{AdrOffset, BranchOffset, Cond, UScaledImm12};
use fors_asm::{EncodeError, Reg};
use fors_oir::TrapKind;

pub use int::Key;

/// The bit-field a hole patches.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HoleKind {
    /// `ldr`/`str` X, unsigned offset: bits 10..=21 = byte offset / 8.
    LdSt64,
    /// `movz`/`movk`: bits 5..=20 = imm16.
    Imm16,
    /// `b.cond`/`cbz`/`cbnz`: bits 5..=23 = signed word offset.
    Br19,
    /// `tbz`/`tbnz`: bits 5..=18 = signed word offset.
    Br14,
    /// `b`/`bl`: bits 0..=25 = signed word offset.
    Br26,
    /// `adr`: immlo bits 29..=30, immhi bits 5..=23 (signed byte offset).
    Adr21,
}

/// A runtime routine a stencil calls (`bl`, relocated by the linker).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum RtSym {
    WriteUint,
    WriteLine,
}

impl RtSym {
    pub fn symbol(self) -> &'static str {
        match self {
            RtSym::WriteUint => crate::rt::WRITE_UINT,
            RtSym::WriteLine => crate::rt::WRITE_LINE,
        }
    }
}

/// Which [`Fill`] field a hole takes its value from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Field {
    SlotA,
    SlotB,
    SlotDst,
    Imm(u8),
    /// The stencil's `i`-th trap site.
    Trap(u8),
    Call(RtSym),
    Lit,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Hole {
    pub word: u16,
    pub kind: HoleKind,
    pub field: Field,
}

/// The concrete value of every field of one stencil instance.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Fill {
    /// Byte offsets of frame slots from `sp` (multiples of 8, < 32 KiB).
    pub slot_a: u32,
    pub slot_b: u32,
    pub slot_dst: u32,
    pub imm: [u16; 4],
    /// Byte distance from the stencil's first word to trap site `i`'s `brk`.
    pub trap: [i64; 4],
    /// Byte distance from the stencil's first word to the callee.
    pub call: i64,
    /// Byte distance from the stencil's first word to the literal.
    pub lit: i64,
}

impl Fill {
    /// The table's placeholder: every field a valid, distinct value.
    pub fn placeholder() -> Fill {
        Fill {
            slot_a: 8,
            slot_b: 16,
            slot_dst: 24,
            imm: [1, 2, 3, 4],
            trap: [256, 260, 264, 268],
            call: 1024,
            lit: 512,
        }
    }
}

/// A stencil body under construction: instructions plus the holes and trap
/// sites recorded while building them.
pub struct Seq<'f> {
    fill: &'f Fill,
    pub insts: Vec<Inst>,
    pub holes: Vec<Hole>,
    pub sites: Vec<TrapKind>,
    name: String,
}

fn must(r: Result<Inst, EncodeError>, what: &str) -> Inst {
    match r {
        Ok(i) => i,
        Err(e) => panic!("stencil `{what}` does not encode: {e:?}"),
    }
}

impl<'f> Seq<'f> {
    pub fn new(fill: &'f Fill, name: String) -> Seq<'f> {
        Seq {
            fill,
            insts: Vec::new(),
            holes: Vec::new(),
            sites: Vec::new(),
            name,
        }
    }

    fn word(&self) -> u16 {
        self.insts.len() as u16
    }

    /// A fixed instruction (no hole).
    pub fn i(&mut self, r: Result<Inst, EncodeError>) {
        let i = must(r, &self.name);
        self.insts.push(i);
    }

    pub fn fixed(&mut self, i: Inst) {
        self.insts.push(i);
    }

    fn hole(&mut self, kind: HoleKind, field: Field) {
        let word = self.word();
        self.holes.push(Hole { word, kind, field });
    }

    fn slot(&self, f: Field) -> u32 {
        match f {
            Field::SlotA => self.fill.slot_a,
            Field::SlotB => self.fill.slot_b,
            Field::SlotDst => self.fill.slot_dst,
            other => panic!("not a slot field: {other:?}"),
        }
    }

    /// `ldr x<rt>, [sp, #slot]`.
    pub fn ldr_slot(&mut self, rt: u8, f: Field) {
        let off = self.slot(f);
        self.hole(HoleKind::LdSt64, f);
        let m = UScaledImm12::new(i64::from(off), 8).map(AddrMode::UnsignedOffset);
        let r = m.and_then(|m| Inst::ldr(Reg::x(rt), Reg::sp(), m));
        self.i(r);
    }

    /// `str x<rt>, [sp, #slot]`.
    pub fn str_slot(&mut self, rt: u8, f: Field) {
        let off = self.slot(f);
        self.hole(HoleKind::LdSt64, f);
        let m = UScaledImm12::new(i64::from(off), 8).map(AddrMode::UnsignedOffset);
        let r = m.and_then(|m| Inst::str_(Reg::x(rt), Reg::sp(), m));
        self.i(r);
    }

    /// `movz <rd>, #imm[i], lsl #shift` (hole on the immediate).
    pub fn movz_imm(&mut self, rd: Reg, i: u8, shift: u8) {
        self.hole(HoleKind::Imm16, Field::Imm(i));
        let v = self.fill.imm[i as usize];
        self.i(Inst::movz(rd, v, shift));
    }

    /// `movk <rd>, #imm[i], lsl #shift` (hole on the immediate).
    pub fn movk_imm(&mut self, rd: Reg, i: u8, shift: u8) {
        self.hole(HoleKind::Imm16, Field::Imm(i));
        let v = self.fill.imm[i as usize];
        self.i(Inst::movk(rd, v, shift));
    }

    /// The stencil-local site index of trap `kind` (one `brk` per site:
    /// several branches to the same kind share it).
    fn site(&mut self, kind: TrapKind) -> u8 {
        if let Some(i) = self.sites.iter().position(|&k| k == kind) {
            return i as u8;
        }
        self.sites.push(kind);
        assert!(
            self.sites.len() <= 4,
            "a stencil has at most four trap sites"
        );
        (self.sites.len() - 1) as u8
    }

    fn trap_off(&self, site: u8) -> i64 {
        self.fill.trap[site as usize] - 4 * i64::from(self.word())
    }

    /// `b.<cond>` to trap `kind`'s site.
    pub fn trap_if(&mut self, cond: Cond, kind: TrapKind) {
        let s = self.site(kind);
        let off = self.trap_off(s);
        self.hole(HoleKind::Br19, Field::Trap(s));
        let r = BranchOffset::new(off, 19, "b.cond").map(|o| Inst::b_cond(cond, o));
        self.i(r);
    }

    /// `cbz <rt>` to trap `kind`'s site.
    pub fn trap_cbz(&mut self, rt: Reg, kind: TrapKind) {
        let s = self.site(kind);
        let off = self.trap_off(s);
        self.hole(HoleKind::Br19, Field::Trap(s));
        let r = BranchOffset::new(off, 19, "cbz").map(|o| Inst::cbz(rt, o));
        self.i(r);
    }

    /// `cbnz <rt>` to trap `kind`'s site.
    pub fn trap_cbnz(&mut self, rt: Reg, kind: TrapKind) {
        let s = self.site(kind);
        let off = self.trap_off(s);
        self.hole(HoleKind::Br19, Field::Trap(s));
        let r = BranchOffset::new(off, 19, "cbnz").map(|o| Inst::cbnz(rt, o));
        self.i(r);
    }

    /// `tbnz <rt>, #bit` to trap `kind`'s site.
    pub fn trap_tbnz(&mut self, rt: Reg, bit: u8, kind: TrapKind) {
        let s = self.site(kind);
        let off = self.trap_off(s);
        self.hole(HoleKind::Br14, Field::Trap(s));
        let r = BranchOffset::new(off, 14, "tbnz").and_then(|o| Inst::tbnz(rt, bit, o));
        self.i(r);
    }

    /// An unconditional `b` to trap `kind`'s site (the explicit `trap`
    /// terminator).
    pub fn trap_always(&mut self, kind: TrapKind) {
        let s = self.site(kind);
        let off = self.trap_off(s);
        self.hole(HoleKind::Br26, Field::Trap(s));
        let r = BranchOffset::new(off, 26, "b").map(Inst::b);
        self.i(r);
    }

    /// `bl <runtime routine>` (the linker patches the offset).
    pub fn bl(&mut self, sym: RtSym) {
        let off = self.fill.call - 4 * i64::from(self.word());
        self.hole(HoleKind::Br26, Field::Call(sym));
        let r = BranchOffset::new(off, 26, "bl").map(Inst::bl);
        self.i(r);
    }

    /// `adr <rd>, <literal>`.
    pub fn adr_lit(&mut self, rd: Reg) {
        let off = self.fill.lit - 4 * i64::from(self.word());
        self.hole(HoleKind::Adr21, Field::Lit);
        let r = AdrOffset::new(off).and_then(|o| Inst::adr(rd, o));
        self.i(r);
    }

    /// A fixed forward/backward branch inside the stencil, `words` away.
    pub fn b_cond_local(&mut self, cond: Cond, words: i64) {
        let r = BranchOffset::new(4 * words, 19, "b.cond (local)").map(|o| Inst::b_cond(cond, o));
        self.i(r);
    }
}

/// One encoded stencil: the static-table entry.
#[derive(Clone, Debug)]
pub struct Stencil {
    pub key: Key,
    pub words: Vec<u32>,
    pub holes: Vec<Hole>,
    /// Trap kind of each site, by site index.
    pub sites: Vec<TrapKind>,
    /// Runtime routine called, if any.
    pub calls: Option<RtSym>,
}

fn bits(w: u32, lo: u32, len: u32, v: u32) -> u32 {
    let mask = ((1u64 << len) - 1) as u32;
    (w & !(mask << lo)) | ((v & mask) << lo)
}

/// Patches hole `h` of word `w` with the value `fill` gives it, for a
/// stencil starting at `word` 0.
pub fn patch(w: u32, h: &Hole, fill: &Fill) -> u32 {
    let word_bytes = 4 * i64::from(h.word);
    let value: i64 = match h.field {
        Field::SlotA => i64::from(fill.slot_a),
        Field::SlotB => i64::from(fill.slot_b),
        Field::SlotDst => i64::from(fill.slot_dst),
        Field::Imm(i) => i64::from(fill.imm[i as usize]),
        Field::Trap(s) => fill.trap[s as usize] - word_bytes,
        Field::Call(_) => fill.call - word_bytes,
        Field::Lit => fill.lit - word_bytes,
    };
    match h.kind {
        HoleKind::LdSt64 => bits(w, 10, 12, (value / 8) as u32),
        HoleKind::Imm16 => bits(w, 5, 16, value as u32),
        HoleKind::Br19 => bits(w, 5, 19, (value >> 2) as u32),
        HoleKind::Br14 => bits(w, 5, 14, (value >> 2) as u32),
        HoleKind::Br26 => bits(w, 0, 26, (value >> 2) as u32),
        HoleKind::Adr21 => {
            let v = value as u32;
            bits(bits(w, 29, 2, v & 3), 5, 19, v >> 2)
        }
    }
}

/// Does hole `h`'s value under `fill` fit its bit-field? (`patch` masks;
/// an out-of-range value must be refused before it is patched, never
/// silently truncated into a wrong branch.)
pub fn hole_fits(h: &Hole, fill: &Fill) -> bool {
    let word_bytes = 4 * i64::from(h.word);
    let v: i64 = match h.field {
        Field::SlotA => i64::from(fill.slot_a),
        Field::SlotB => i64::from(fill.slot_b),
        Field::SlotDst => i64::from(fill.slot_dst),
        Field::Imm(i) => i64::from(fill.imm[i as usize]),
        Field::Trap(s) => fill.trap[s as usize] - word_bytes,
        Field::Call(_) => fill.call - word_bytes,
        Field::Lit => fill.lit - word_bytes,
    };
    let signed = |bits: u32, scale: i64| {
        v % scale == 0 && {
            let q = v / scale;
            q >= -(1i64 << (bits - 1)) && q < (1i64 << (bits - 1))
        }
    };
    match h.kind {
        HoleKind::LdSt64 => v >= 0 && v % 8 == 0 && v / 8 <= 0xFFF,
        HoleKind::Imm16 => (0..=0xFFFF).contains(&v),
        HoleKind::Br19 => signed(19, 4),
        HoleKind::Br14 => signed(14, 4),
        HoleKind::Br26 => signed(26, 4),
        HoleKind::Adr21 => signed(21, 1),
    }
}

impl Stencil {
    /// Runs `body` on `fill` and encodes it: the reference path the table is
    /// built from and the golden test compares against.
    pub fn build(key: Key, fill: &Fill) -> (Vec<u32>, Seq<'_>) {
        let mut s = Seq::new(fill, format!("{key:?}"));
        int::body(key, &mut s);
        let words = s
            .insts
            .iter()
            .map(|i| match fors_asm::encode(i) {
                Ok(w) => w,
                Err(e) => panic!("stencil {key:?}: {i:?} does not encode: {e:?}"),
            })
            .collect();
        (words, s)
    }

    fn from_key(key: Key) -> Stencil {
        let fill = Fill::placeholder();
        let (words, s) = Stencil::build(key, &fill);
        let calls = s.holes.iter().find_map(|h| match h.field {
            Field::Call(c) => Some(c),
            _ => None,
        });
        Stencil {
            key,
            words,
            holes: s.holes,
            sites: s.sites,
            calls,
        }
    }

    /// Copy the words, patch every hole: the emit fast path.
    pub fn instantiate_into(&self, fill: &Fill, out: &mut Vec<u32>) {
        let base = out.len();
        out.extend_from_slice(&self.words);
        for h in &self.holes {
            let i = base + h.word as usize;
            out[i] = patch(out[i], h, fill);
        }
    }

    pub fn instantiate(&self, fill: &Fill) -> Vec<u32> {
        let mut v = Vec::with_capacity(self.words.len());
        self.instantiate_into(fill, &mut v);
        v
    }
}

/// The static stencil table, built once on first use.
pub struct Table {
    pub stencils: Vec<Stencil>,
    index: BTreeMap<Key, u32>,
}

impl Table {
    pub fn get(&self, key: Key) -> &Stencil {
        match self.index.get(&key) {
            Some(&i) => &self.stencils[i as usize],
            None => panic!("no stencil for {key:?}"),
        }
    }

    pub fn id(&self, key: Key) -> Option<u32> {
        self.index.get(&key).copied()
    }
}

pub fn table() -> &'static Table {
    static T: OnceLock<Table> = OnceLock::new();
    T.get_or_init(|| {
        let mut stencils = Vec::new();
        let mut index = BTreeMap::new();
        for key in int::all_keys() {
            index.insert(key, stencils.len() as u32);
            stencils.push(Stencil::from_key(key));
        }
        Table { stencils, index }
    })
}
