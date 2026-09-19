// Instruction encoder: turns `ir::Item` streams into arm64 machine code
// bytes. Every instruction here was verified byte-for-byte against the
// system assembler's output before use (see `difftest`/README in
// REPORT.md) — this file's constants are not hand-derived guesses.

use crate::ir::{Function, Inst, Item, SP};

pub struct RelocSite {
    /// byte offset of the instruction within the whole __text blob
    pub at: u32,
    pub label: String,
    pub kind: RelocKind,
}

#[derive(Clone, Copy)]
pub enum RelocKind {
    Page21,
    Pageoff12,
}

pub struct Encoded {
    pub text: Vec<u8>,
    /// (symbol name, byte offset into `text`, is_global)
    pub func_syms: Vec<(String, u32, bool)>,
    pub relocs: Vec<RelocSite>,
}

/// Rung 3 has no linker to apply `relocs`, so it resolves them itself
/// once final addresses are known (ADRP page-relative, ADD low-12
/// bits) and patches the bytes in place.
pub fn resolve_relocs_inplace(text: &mut [u8], relocs: &[RelocSite], text_base_vmaddr: u64, data_vmaddr: &std::collections::HashMap<String, u64>) {
    for r in relocs {
        let target = *data_vmaddr.get(&r.label).unwrap_or_else(|| panic!("undefined data symbol {}", r.label));
        let instr_addr = text_base_vmaddr + r.at as u64;
        let at = r.at as usize;
        let word = u32::from_le_bytes(text[at..at + 4].try_into().unwrap());
        let new_word = match r.kind {
            RelocKind::Page21 => {
                let page_delta = ((target as i64 & !0xFFF) - (instr_addr as i64 & !0xFFF)) >> 12;
                let imm21 = page_delta as u32;
                let immlo = imm21 & 0x3;
                let immhi = (imm21 >> 2) & 0x7FFFF;
                (word & !((0x3 << 29) | (0x7FFFF << 5))) | (immlo << 29) | (immhi << 5)
            }
            RelocKind::Pageoff12 => {
                let off = (target & 0xFFF) as u32;
                (word & !(0xFFFu32 << 10)) | (off << 10)
            }
        };
        text[at..at + 4].copy_from_slice(&new_word.to_le_bytes());
    }
}

fn u(x: i64) -> u32 {
    x as u32
}

fn enc_movz_movk(is_k: bool, rd: u8, imm16: u16, hw: u8) -> u32 {
    let opc = if is_k { 0b11u32 } else { 0b10u32 };
    (1u32 << 31) | (opc << 29) | (0b100101u32 << 23) | ((hw as u32) << 21) | ((imm16 as u32) << 5) | (rd as u32)
}

fn enc_mov_reg(rd: u8, rm: u8) -> u32 {
    (1u32 << 31) | (0b01u32 << 29) | (0b01010u32 << 24) | ((rm as u32) << 16) | (31u32 << 5) | (rd as u32)
}

fn enc_add_sub_imm(sub: bool, set_flags: bool, rd: u8, rn: u8, imm12: u16) -> u32 {
    (1u32 << 31)
        | ((sub as u32) << 30)
        | ((set_flags as u32) << 29)
        | (0b100010u32 << 23)
        | ((imm12 as u32) << 10)
        | ((rn as u32) << 5)
        | (rd as u32)
}

fn enc_add_sub_reg(sub: bool, set_flags: bool, rd: u8, rn: u8, rm: u8) -> u32 {
    (1u32 << 31)
        | ((sub as u32) << 30)
        | ((set_flags as u32) << 29)
        | (0b01011u32 << 24)
        | ((rm as u32) << 16)
        | ((rn as u32) << 5)
        | (rd as u32)
}

fn enc_data_proc_3src(rd: u8, rn: u8, rm: u8, ra: u8, sub: bool) -> u32 {
    (1u32 << 31) | (0b11011u32 << 24) | ((rm as u32) << 16) | ((sub as u32) << 15) | ((ra as u32) << 10) | ((rn as u32) << 5) | (rd as u32)
}

fn enc_sdiv(rd: u8, rn: u8, rm: u8) -> u32 {
    (1u32 << 31) | (0b11010110u32 << 21) | ((rm as u32) << 16) | (0b000011u32 << 10) | ((rn as u32) << 5) | (rd as u32)
}

fn enc_csinc(rd: u8, rn: u8, rm: u8, cond: u32) -> u32 {
    (1u32 << 31) | (0b11010100u32 << 21) | ((rm as u32) << 16) | (cond << 12) | (0b01u32 << 10) | ((rn as u32) << 5) | (rd as u32)
}

fn enc_stp_ldp_sp(is_load: bool, mode: u32, rt: u8, rt2: u8, imm7: i16) -> u32 {
    let imm7u = (imm7 as i32) & 0x7F;
    (0b10u32 << 30)
        | (0b101u32 << 27)
        | (mode << 23)
        | ((is_load as u32) << 22)
        | ((imm7u as u32) << 15)
        | ((rt2 as u32) << 10)
        | ((SP as u32) << 5)
        | (rt as u32)
}

fn enc_ldst_unsigned_imm(is_load: bool, rt: u8, rn: u8, imm12_scaled: u16) -> u32 {
    let opc = if is_load { 0b01u32 } else { 0b00u32 };
    (0b11u32 << 30) | (0b111u32 << 27) | (0b01u32 << 24) | (opc << 22) | ((imm12_scaled as u32) << 10) | ((rn as u32) << 5) | (rt as u32)
}

fn enc_ldst_unscaled(is_load: bool, rt: u8, rn: u8, imm9: i16) -> u32 {
    let opc = if is_load { 0b01u32 } else { 0b00u32 };
    let imm9u = (imm9 as i32) & 0x1FF;
    (0b11u32 << 30) | (0b111u32 << 27) | (0b00u32 << 24) | (opc << 22) | ((imm9u as u32) << 12) | ((rn as u32) << 5) | (rt as u32)
}

fn enc_adrp(rd: u8) -> u32 {
    // imm=0 placeholder; a PAGE21 relocation patches this at link time.
    (1u32 << 31) | (0b10000u32 << 24) | (rd as u32)
}

fn enc_b(imm26: i32) -> u32 {
    (0b000101u32 << 26) | (u(imm26 as i64) & 0x03FF_FFFF)
}

fn enc_bl(imm26: i32) -> u32 {
    (0b100101u32 << 26) | (u(imm26 as i64) & 0x03FF_FFFF)
}

fn enc_bcond(imm19: i32, cond: u32) -> u32 {
    (0b0101010u32 << 25) | ((u(imm19 as i64) & 0x7FFFF) << 5) | cond
}

const RET: u32 = 0xd65f03c0;

/// Encodes every function's items in order into one flat __text blob.
/// Internal branches (b/bl/b.cond) are resolved purely from relative
/// byte offsets within this blob (valid regardless of final link
/// address, since source and target are in the same section). ADRP/ADD
/// data references are left as zero immediates plus a relocation site,
/// since they cross into the __const section whose final relative
/// placement we don't want to have to guess.
pub fn encode_program(funcs: &[Function], extra_labels: &[(String, u32)]) -> Encoded {
    // Pass 1: flatten to one item list, computing each label's byte offset.
    let mut flat: Vec<&Inst> = Vec::new();
    let mut label_off: std::collections::HashMap<String, u32> = std::collections::HashMap::new();
    let mut func_syms = Vec::new();
    for f in funcs {
        func_syms.push((f.name.clone(), (flat.len() as u32) * 4, f.is_global));
        label_off.insert(format!("_{}", f.name), (flat.len() as u32) * 4);
        for item in &f.items {
            match item {
                Item::Label(l) => {
                    label_off.insert(l.clone(), (flat.len() as u32) * 4);
                }
                Item::Inst(i) => flat.push(i),
            }
        }
    }
    let code_len = (flat.len() as u32) * 4;
    for (name, off) in extra_labels {
        label_off.insert(format!("_{name}"), code_len + off);
    }

    // Pass 2: encode.
    let mut text = Vec::with_capacity(flat.len() * 4);
    let mut relocs = Vec::new();
    for (idx, inst) in flat.iter().enumerate() {
        let here = (idx as i64) * 4;
        let word = match inst {
            Inst::Movz { rd, imm16, hw } => enc_movz_movk(false, *rd, *imm16, *hw),
            Inst::Movk { rd, imm16, hw } => enc_movz_movk(true, *rd, *imm16, *hw),
            Inst::MovReg { rd, rm } => enc_mov_reg(*rd, *rm),
            Inst::MovSp { rd, rn } => enc_add_sub_imm(false, false, *rd, *rn, 0),
            Inst::AddSubReg { sub, rd, rn, rm } => enc_add_sub_reg(*sub, false, *rd, *rn, *rm),
            Inst::AddSubImm { sub, rd, rn, imm12 } => enc_add_sub_imm(*sub, false, *rd, *rn, *imm12),
            Inst::Neg { rd, rm } => enc_add_sub_reg(true, false, *rd, 31, *rm), // rn = XZR = 31
            Inst::Mul { rd, rn, rm } => enc_data_proc_3src(*rd, *rn, *rm, 31, false),
            Inst::Sdiv { rd, rn, rm } => enc_sdiv(*rd, *rn, *rm),
            Inst::Msub { rd, rn, rm, ra } => enc_data_proc_3src(*rd, *rn, *rm, *ra, true),
            Inst::CmpReg { rn, rm } => enc_add_sub_reg(true, true, 31, *rn, *rm),
            Inst::CmpImm { rn, imm12 } => enc_add_sub_imm(true, true, 31, *rn, *imm12),
            Inst::Cset { rd, cond } => enc_csinc(*rd, 31, 31, cond.inverted_code()),
            Inst::Bcond { cond, label } => {
                let target = *label_off.get(label).unwrap_or_else(|| panic!("undefined label {label}")) as i64;
                enc_bcond(((target - here) / 4) as i32, cond.code())
            }
            Inst::B { label } => {
                let target = *label_off.get(label).unwrap_or_else(|| panic!("undefined label {label}")) as i64;
                enc_b(((target - here) / 4) as i32)
            }
            Inst::Bl { func } => {
                let key = format!("_{func}");
                let target = *label_off.get(&key).unwrap_or_else(|| panic!("undefined function {func}")) as i64;
                enc_bl(((target - here) / 4) as i32)
            }
            Inst::Ret => RET,
            Inst::StpPreSp { rt1, rt2, imm } => enc_stp_ldp_sp(false, 0b11, *rt1, *rt2, imm / 8),
            Inst::LdpPostSp { rt1, rt2, imm } => enc_stp_ldp_sp(true, 0b01, *rt1, *rt2, imm / 8),
            Inst::StrSp0 { rt } => enc_ldst_unsigned_imm(false, *rt, SP, 0),
            Inst::LdrSp0 { rt } => enc_ldst_unsigned_imm(true, *rt, SP, 0),
            Inst::SturFp { rt, offset } => enc_ldst_unscaled(false, *rt, 29, -offset),
            Inst::LdurFp { rt, offset } => enc_ldst_unscaled(true, *rt, 29, -offset),
            Inst::AdrpLabel { rd, label } => {
                relocs.push(RelocSite { at: here as u32, label: label.clone(), kind: RelocKind::Page21 });
                enc_adrp(*rd)
            }
            Inst::AddPageoff { rd, rn, label } => {
                relocs.push(RelocSite { at: here as u32, label: label.clone(), kind: RelocKind::Pageoff12 });
                enc_add_sub_imm(false, false, *rd, *rn, 0)
            }
        };
        text.extend_from_slice(&word.to_le_bytes());
    }
    Encoded { text, func_syms, relocs }
}
