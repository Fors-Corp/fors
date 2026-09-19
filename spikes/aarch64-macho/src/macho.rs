// Our own Mach-O MH_OBJECT (relocatable object) writer for rung 2.
// Layout and field values were derived by building minimal reference
// objects with `cc -c` and reading them back with `otool -l`/a raw
// struct parse (see REPORT.md) rather than guessed from memory.

use crate::encode::{Encoded, RelocKind};

const MH_MAGIC_64: u32 = 0xFEEDFACF;
const CPU_TYPE_ARM64: u32 = 0x0100000C;
const CPU_SUBTYPE_ARM64_ALL: u32 = 0x0;
const MH_OBJECT: u32 = 0x1;
const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x2;
const LC_DYSYMTAB: u32 = 0xB;
const LC_BUILD_VERSION: u32 = 0x32;
const PLATFORM_MACOS: u32 = 1;

const N_SECT: u8 = 0xe;
const N_EXT: u8 = 0x01;


struct Sym {
    name: String,
    n_type: u8,
    n_sect: u8,
    n_value: u64,
}

pub fn build_object(enc: &Encoded, data: &[(String, Vec<u8>)], platform_minos_sdk: (u32, u32)) -> Vec<u8> {
    let text = &enc.text;
    let text_len = text.len() as u64;

    let mut const_bytes = Vec::new();
    let mut data_syms: Vec<(String, u64)> = Vec::new();
    for (label, bytes) in data {
        data_syms.push((label.clone(), text_len + const_bytes.len() as u64));
        const_bytes.extend_from_slice(bytes);
    }
    let has_const = !const_bytes.is_empty();
    let nsects: u32 = if has_const { 2 } else { 1 };

    // ---- symbols: locals first, then external-defined, then (none) undefined ----
    let mut locals: Vec<Sym> = Vec::new();
    let mut externs: Vec<Sym> = Vec::new();
    for (name, off, is_global) in &enc.func_syms {
        let sym = Sym { name: format!("_{name}"), n_type: N_SECT | if *is_global { N_EXT } else { 0 }, n_sect: 1, n_value: *off as u64 };
        if *is_global {
            externs.push(sym);
        } else {
            locals.push(sym);
        }
    }
    for (label, off) in &data_syms {
        locals.push(Sym { name: label.clone(), n_type: N_SECT, n_sect: if has_const { 2 } else { 1 }, n_value: *off });
    }
    let nlocal = locals.len();
    let nextdef = externs.len();
    let mut all_syms = locals;
    all_syms.extend(externs);
    let sym_index: std::collections::HashMap<String, u32> = all_syms.iter().enumerate().map(|(i, s)| (s.name.clone(), i as u32)).collect();

    // ---- string table ----
    let mut strtab = vec![0u8]; // index 0 reserved: empty string
    let mut str_off = Vec::with_capacity(all_syms.len());
    for s in &all_syms {
        str_off.push(strtab.len() as u32);
        strtab.extend_from_slice(s.name.as_bytes());
        strtab.push(0);
    }

    // ---- relocations (__text) ----
    let mut relocs = Vec::new();
    for r in &enc.relocs {
        let symnum = *sym_index.get(&r.label).unwrap_or_else(|| panic!("undefined data symbol {}", r.label));
        let (pcrel, rtype): (u32, u32) = match r.kind {
            RelocKind::Page21 => (1, 3),
            RelocKind::Pageoff12 => (0, 4),
        };
        let word = (symnum & 0x00FF_FFFF) | (pcrel << 24) | (2u32 << 25) | (1u32 << 27) | (rtype << 28);
        relocs.push((r.at as i32, word));
    }

    // ---- layout ----
    let seg_cmdsize = 72 + 80 * nsects as usize; // segment_command_64(72) + nsects*section_64(80)
    let sizeofcmds = seg_cmdsize + 24 /*build version*/ + 24 /*symtab*/ + 80 /*dysymtab*/;
    let header_size = 32usize;
    let mut off = header_size + sizeofcmds;

    let text_fileoff = off;
    off += text.len();
    let const_fileoff = off;
    off += const_bytes.len();
    let reloc_off = if relocs.is_empty() { 0 } else { off };
    off += relocs.len() * 8;
    let symoff = off;
    off += all_syms.len() * 16;
    let stroff = off;
    off += strtab.len();
    let strsize = strtab.len();

    let mut o = Vec::with_capacity(off);
    // mach_header_64
    o.extend_from_slice(&MH_MAGIC_64.to_le_bytes());
    o.extend_from_slice(&CPU_TYPE_ARM64.to_le_bytes());
    o.extend_from_slice(&CPU_SUBTYPE_ARM64_ALL.to_le_bytes());
    o.extend_from_slice(&MH_OBJECT.to_le_bytes());
    o.extend_from_slice(&4u32.to_le_bytes()); // ncmds
    o.extend_from_slice(&(sizeofcmds as u32).to_le_bytes());
    o.extend_from_slice(&0u32.to_le_bytes()); // flags
    o.extend_from_slice(&0u32.to_le_bytes()); // reserved

    // LC_SEGMENT_64
    o.extend_from_slice(&LC_SEGMENT_64.to_le_bytes());
    o.extend_from_slice(&(seg_cmdsize as u32).to_le_bytes());
    o.extend_from_slice(&[0u8; 16]); // segname "" (MH_OBJECT convention)
    o.extend_from_slice(&0u64.to_le_bytes()); // vmaddr
    o.extend_from_slice(&(text_len + const_bytes.len() as u64).to_le_bytes()); // vmsize
    o.extend_from_slice(&(text_fileoff as u64).to_le_bytes()); // fileoff
    o.extend_from_slice(&(text.len() as u64 + const_bytes.len() as u64).to_le_bytes()); // filesize
    o.extend_from_slice(&7u32.to_le_bytes()); // maxprot
    o.extend_from_slice(&7u32.to_le_bytes()); // initprot
    o.extend_from_slice(&nsects.to_le_bytes());
    o.extend_from_slice(&0u32.to_le_bytes()); // flags

    fn sectname(name: &str) -> [u8; 16] {
        let mut b = [0u8; 16];
        b[..name.len()].copy_from_slice(name.as_bytes());
        b
    }
    // __text section
    o.extend_from_slice(&sectname("__text"));
    o.extend_from_slice(&sectname("__TEXT"));
    o.extend_from_slice(&0u64.to_le_bytes()); // addr
    o.extend_from_slice(&(text.len() as u64).to_le_bytes()); // size
    o.extend_from_slice(&(text_fileoff as u32).to_le_bytes()); // offset
    o.extend_from_slice(&0u32.to_le_bytes()); // align (2^0)
    o.extend_from_slice(&(reloc_off as u32).to_le_bytes());
    o.extend_from_slice(&(relocs.len() as u32).to_le_bytes());
    o.extend_from_slice(&0x8000_0400u32.to_le_bytes()); // S_ATTR_PURE_INSTRUCTIONS|SOME_INSTRUCTIONS
    o.extend_from_slice(&0u32.to_le_bytes()); // reserved1
    o.extend_from_slice(&0u32.to_le_bytes()); // reserved2
    o.extend_from_slice(&0u32.to_le_bytes()); // reserved3 (section_64 has three)

    if has_const {
        o.extend_from_slice(&sectname("__const"));
        o.extend_from_slice(&sectname("__TEXT"));
        o.extend_from_slice(&(text_len).to_le_bytes()); // addr
        o.extend_from_slice(&(const_bytes.len() as u64).to_le_bytes());
        o.extend_from_slice(&(const_fileoff as u32).to_le_bytes());
        o.extend_from_slice(&0u32.to_le_bytes()); // align
        o.extend_from_slice(&0u32.to_le_bytes()); // reloff
        o.extend_from_slice(&0u32.to_le_bytes()); // nreloc
        o.extend_from_slice(&0u32.to_le_bytes()); // flags (regular)
        o.extend_from_slice(&0u32.to_le_bytes()); // reserved1
        o.extend_from_slice(&0u32.to_le_bytes()); // reserved2
        o.extend_from_slice(&0u32.to_le_bytes()); // reserved3
    }

    // LC_BUILD_VERSION
    o.extend_from_slice(&LC_BUILD_VERSION.to_le_bytes());
    o.extend_from_slice(&24u32.to_le_bytes());
    o.extend_from_slice(&PLATFORM_MACOS.to_le_bytes());
    o.extend_from_slice(&platform_minos_sdk.0.to_le_bytes());
    o.extend_from_slice(&platform_minos_sdk.1.to_le_bytes());
    o.extend_from_slice(&0u32.to_le_bytes()); // ntools

    // LC_SYMTAB
    o.extend_from_slice(&LC_SYMTAB.to_le_bytes());
    o.extend_from_slice(&24u32.to_le_bytes());
    o.extend_from_slice(&(symoff as u32).to_le_bytes());
    o.extend_from_slice(&(all_syms.len() as u32).to_le_bytes());
    o.extend_from_slice(&(stroff as u32).to_le_bytes());
    o.extend_from_slice(&(strsize as u32).to_le_bytes());

    // LC_DYSYMTAB
    o.extend_from_slice(&LC_DYSYMTAB.to_le_bytes());
    o.extend_from_slice(&80u32.to_le_bytes());
    o.extend_from_slice(&0u32.to_le_bytes()); // ilocalsym
    o.extend_from_slice(&(nlocal as u32).to_le_bytes()); // nlocalsym
    o.extend_from_slice(&(nlocal as u32).to_le_bytes()); // iextdefsym
    o.extend_from_slice(&(nextdef as u32).to_le_bytes()); // nextdefsym
    o.extend_from_slice(&((nlocal + nextdef) as u32).to_le_bytes()); // iundefsym
    o.extend_from_slice(&0u32.to_le_bytes()); // nundefsym
    for _ in 0..12 {
        o.extend_from_slice(&0u32.to_le_bytes()); // tocoff..nlocrel, all zero/unused
    }

    debug_assert_eq!(o.len(), header_size + sizeofcmds);
    o.extend_from_slice(text);
    o.extend_from_slice(&const_bytes);
    for (addr, word) in &relocs {
        o.extend_from_slice(&addr.to_le_bytes());
        o.extend_from_slice(&word.to_le_bytes());
    }
    for (i, s) in all_syms.iter().enumerate() {
        o.extend_from_slice(&str_off[i].to_le_bytes());
        o.push(s.n_type);
        o.push(s.n_sect);
        o.extend_from_slice(&0u16.to_le_bytes()); // n_desc
        o.extend_from_slice(&s.n_value.to_le_bytes());
    }
    o.extend_from_slice(&strtab);

    o
}
