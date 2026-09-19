// Rung 3: our own MH_EXECUTE | MH_PIE | MH_DYLDLINK | MH_TWOLEVEL writer.
// No `ld`, no `codesign`, no external process of any kind. Layout and
// every load command's field values were derived by building a rung-2
// linked specimen (`hello`) with `cc`, then reading it back load
// command by load command with `otool -l`/`otool -h`/a raw struct parse
// (see REPORT.md) — never guessed from memory.

use crate::encode::Encoded;
use crate::sha256::sha256;

const PAGEZERO_VMSIZE: u64 = 0x1_0000_0000;
const IMAGE_BASE: u64 = 0x1_0000_0000;
const PAGE: u64 = 0x4000; // __TEXT/__LINKEDIT page granularity used by ld64 for small binaries

fn align_up(x: u64, a: u64) -> u64 {
    (x + a - 1) / a * a
}

fn uleb128(buf: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut byte = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if v == 0 {
            break;
        }
    }
}

fn cstr16(name: &str) -> [u8; 16] {
    let mut b = [0u8; 16];
    b[..name.len()].copy_from_slice(name.as_bytes());
    b
}

/// A minimal exports trie holding exactly `__mh_execute_header` (address
/// 0) and `_main` (address `main_addr`, offset from the image base) —
/// what the specimen's own trie exports. Built directly (not via a
/// general trie algorithm) since the export set never varies: layout is
/// root -> "_" -> {"_mh_execute_header" -> leaf0, "main" -> leaf(main_addr)}.
fn build_exports_trie(main_addr: u64) -> Vec<u8> {
    let mut leaf1 = Vec::new(); // __mh_execute_header
    uleb128(&mut leaf1, 0); // export flags
    uleb128(&mut leaf1, 0); // address
    let mut leaf1_full = Vec::new();
    uleb128(&mut leaf1_full, leaf1.len() as u64);
    leaf1_full.extend_from_slice(&leaf1);
    leaf1_full.push(0); // num children

    let mut leaf2 = Vec::new(); // _main
    uleb128(&mut leaf2, 0);
    uleb128(&mut leaf2, main_addr);
    let mut leaf2_full = Vec::new();
    uleb128(&mut leaf2_full, leaf2.len() as u64);
    leaf2_full.extend_from_slice(&leaf2);
    leaf2_full.push(0);

    // Layout: root, then "_" node, then leaf1, then leaf2 — all forward
    // offsets, computed by construction (no patching needed).
    let root_len = {
        let mut child_off_enc = Vec::new();
        uleb128(&mut child_off_enc, 5); // placeholder length probe below
        1 + 1 + 2 + child_off_enc.len() // term_size + numchildren + "_\0" + offset
    };
    let underscore_off = root_len as u64;

    let label1 = b"_mh_execute_header\0";
    let label2 = b"main\0";
    let mut off1_enc = Vec::new();
    // leaf1 offset = underscore_off + underscore_node_len; compute underscore_node_len first
    let mut off1_probe = Vec::new();
    uleb128(&mut off1_probe, 0); // dummy, real value patched after we know leaf1_off
    let underscore_hdr_len = 1 + 1; // term_size(0) + num_children(2)
    // Assume 1-byte uleb128 offsets throughout (true for these tiny blobs).
    let underscore_len = underscore_hdr_len + label1.len() + 1 + label2.len() + 1;
    let leaf1_off = underscore_off + underscore_len as u64;
    let leaf2_off = leaf1_off + leaf1_full.len() as u64;
    assert!(underscore_off < 128 && leaf1_off < 128 && leaf2_off < 128, "trie offsets exceeded 1-byte uleb128 assumption");
    off1_enc.clear();
    uleb128(&mut off1_enc, leaf1_off);
    let mut off2_enc = Vec::new();
    uleb128(&mut off2_enc, leaf2_off);

    let mut trie = Vec::new();
    // root
    trie.push(0); // terminal_size 0
    trie.push(1); // 1 child
    trie.extend_from_slice(b"_\0");
    uleb128(&mut trie, underscore_off);
    debug_assert_eq!(trie.len() as u64, underscore_off);
    // "_" node
    trie.push(0);
    trie.push(2);
    trie.extend_from_slice(label1);
    trie.extend_from_slice(&off1_enc);
    trie.extend_from_slice(label2);
    trie.extend_from_slice(&off2_enc);
    debug_assert_eq!(trie.len() as u64, leaf1_off);
    trie.extend_from_slice(&leaf1_full);
    debug_assert_eq!(trie.len() as u64, leaf2_off);
    trie.extend_from_slice(&leaf2_full);
    trie
}

/// The chained-fixups blob is entirely address-independent: it declares
/// zero imports and one zero starts-offset per segment, i.e. "this
/// image needs no fixups at all". Reproduced structurally from the
/// specimen (dyld_chained_fixups_header + dyld_chained_starts_in_image
/// with seg_count=3, all seg_info_offset=0).
fn build_chained_fixups() -> Vec<u8> {
    let mut b = Vec::new();
    b.extend_from_slice(&0u32.to_le_bytes()); // fixups_version
    b.extend_from_slice(&32u32.to_le_bytes()); // starts_offset
    b.extend_from_slice(&48u32.to_le_bytes()); // imports_offset
    b.extend_from_slice(&48u32.to_le_bytes()); // symbols_offset
    b.extend_from_slice(&0u32.to_le_bytes()); // imports_count
    b.extend_from_slice(&1u32.to_le_bytes()); // imports_format (DYLD_CHAINED_IMPORT)
    b.extend_from_slice(&0u32.to_le_bytes()); // symbols_format
    b.extend_from_slice(&0u32.to_le_bytes()); // padding to starts_offset(32)
    // dyld_chained_starts_in_image
    b.extend_from_slice(&3u32.to_le_bytes()); // seg_count (PAGEZERO, TEXT, LINKEDIT)
    b.extend_from_slice(&0u32.to_le_bytes()); // seg_info_offset[0]
    b.extend_from_slice(&0u32.to_le_bytes()); // seg_info_offset[1]
    b.extend_from_slice(&0u32.to_le_bytes()); // seg_info_offset[2]
    b.extend_from_slice(&0u32.to_le_bytes());
    b.extend_from_slice(&0u32.to_le_bytes());
    debug_assert_eq!(b.len(), 56);
    b
}

fn build_function_starts(mut addrs: Vec<u64>) -> Vec<u8> {
    addrs.sort_unstable();
    let mut out = Vec::new();
    let mut prev = 0u64;
    for a in addrs {
        uleb128(&mut out, a - prev);
        prev = a;
    }
    out
}

struct CodeDirResult {
    superblob: Vec<u8>,
}

fn build_code_signature(file_prefix: &[u8], identifier: &str) -> CodeDirResult {
    let code_limit = file_prefix.len() as u64;
    let page_size: u64 = 4096;
    let n_slots = ((code_limit + page_size - 1) / page_size) as u32;
    let mut hashes = Vec::new();
    for i in 0..n_slots as u64 {
        let start = (i * page_size) as usize;
        let end = std::cmp::min(start + page_size as usize, file_prefix.len());
        hashes.extend_from_slice(&sha256(&file_prefix[start..end]));
    }
    let ident_bytes = {
        let mut v = identifier.as_bytes().to_vec();
        v.push(0);
        v
    };
    const HEADER_LEN: u32 = 88; // through execSegFlags, version 0x20400
    let ident_offset = HEADER_LEN;
    let hash_offset = ident_offset + ident_bytes.len() as u32;
    let cd_length = hash_offset + n_slots * 32;

    let mut cd = Vec::new();
    cd.extend_from_slice(&0xfade0c02u32.to_be_bytes()); // magic
    cd.extend_from_slice(&cd_length.to_be_bytes()); // length
    cd.extend_from_slice(&0x00020400u32.to_be_bytes()); // version
    cd.extend_from_slice(&0x00020002u32.to_be_bytes()); // flags: adhoc | linker-signed
    cd.extend_from_slice(&hash_offset.to_be_bytes());
    cd.extend_from_slice(&ident_offset.to_be_bytes());
    cd.extend_from_slice(&0u32.to_be_bytes()); // nSpecialSlots
    cd.extend_from_slice(&n_slots.to_be_bytes()); // nCodeSlots
    cd.extend_from_slice(&(code_limit as u32).to_be_bytes()); // codeLimit
    cd.push(32); // hashSize
    cd.push(2); // hashType SHA256
    cd.push(0); // platform
    cd.push(12); // pageSize log2 (4096)
    cd.extend_from_slice(&0u32.to_be_bytes()); // spare2
    cd.extend_from_slice(&0u32.to_be_bytes()); // scatterOffset
    cd.extend_from_slice(&0u32.to_be_bytes()); // teamOffset
    cd.extend_from_slice(&0u32.to_be_bytes()); // spare3
    cd.extend_from_slice(&(code_limit).to_be_bytes()); // codeLimit64
    cd.extend_from_slice(&0u64.to_be_bytes()); // execSegBase
    // execSegLimit/execSegFlags are filled in by the caller once the
    // __TEXT filesize is known (patched below via placeholders).
    cd.extend_from_slice(&0u64.to_be_bytes()); // execSegLimit (placeholder)
    cd.extend_from_slice(&1u64.to_be_bytes()); // execSegFlags: CS_EXECSEG_MAIN_BINARY
    debug_assert_eq!(cd.len() as u32, HEADER_LEN);
    cd.extend_from_slice(&ident_bytes);
    cd.extend_from_slice(&hashes);

    let mut sb = Vec::new();
    sb.extend_from_slice(&0xfade0cc0u32.to_be_bytes()); // SuperBlob magic
    let sb_length = 12 + 8 + cd.len() as u32;
    sb.extend_from_slice(&sb_length.to_be_bytes());
    sb.extend_from_slice(&1u32.to_be_bytes()); // count
    sb.extend_from_slice(&0u32.to_be_bytes()); // CSSLOT_CODEDIRECTORY
    sb.extend_from_slice(&20u32.to_be_bytes()); // offset of CD within SuperBlob
    sb.extend_from_slice(&cd);
    CodeDirResult { superblob: sb }
}

pub fn build_executable(enc: &Encoded, data: &[(String, Vec<u8>)], out_name: &str) -> Vec<u8> {
    // ---- __TEXT content: header+load commands, then __text, then __const ----
    let mut const_bytes = Vec::new();
    let mut data_addrs: Vec<(String, u64)> = Vec::new(); // filled once text_section_off known

    // Symbols: locals = non-main functions + rt_write_str/rt_write_int + data labels(section-local, not needed in symtab for exec);
    // externs = __mh_execute_header, _main.
    let mut main_off: Option<u32> = None;
    let mut local_funcs: Vec<(String, u32)> = Vec::new();
    for (name, off, is_global) in &enc.func_syms {
        if *is_global {
            main_off = Some(*off);
        } else {
            local_funcs.push((name.clone(), *off));
        }
    }
    let main_rel = main_off.expect("no _main symbol");

    // ---- layout pass 1: figure out load command sizes (fixed set) ----
    let has_const = !data.is_empty();
    let text_nsects: u32 = if has_const { 2 } else { 1 };
    let seg_pagezero_size = 72u32;
    let seg_text_size = 72 + 80 * text_nsects;
    let seg_linkedit_size = 72u32;
    let lc_chained_fixups_size = 16u32;
    let lc_exports_trie_size = 16u32;
    let lc_symtab_size = 24u32;
    let lc_dysymtab_size = 80u32;
    let dylinker_name = b"/usr/lib/dyld\0";
    let lc_dylinker_size = align_up((12 + dylinker_name.len()) as u64, 8) as u32;
    let lc_uuid_size = 24u32;
    let lc_buildversion_size = 24u32;
    let lc_sourceversion_size = 16u32;
    let lc_main_size = 24u32;
    let dylib_name = b"/usr/lib/libSystem.B.dylib\0";
    let lc_loaddylib_size = align_up((24 + dylib_name.len()) as u64, 8) as u32;
    let lc_funcstarts_size = 16u32;
    let lc_dataincode_size = 16u32;
    let lc_codesig_size = 16u32;

    let sizeofcmds = seg_pagezero_size
        + seg_text_size
        + seg_linkedit_size
        + lc_chained_fixups_size
        + lc_exports_trie_size
        + lc_symtab_size
        + lc_dysymtab_size
        + lc_dylinker_size
        + lc_uuid_size
        + lc_buildversion_size
        + lc_sourceversion_size
        + lc_main_size
        + lc_loaddylib_size
        + lc_funcstarts_size
        + lc_dataincode_size
        + lc_codesig_size;
    let ncmds = 16u32;
    let header_size = 32u32;
    let text_section_off = header_size + sizeofcmds;
    // `enc.func_syms` offsets are relative to the start of the __text
    // section's content; make them absolute file offsets (== addresses
    // minus IMAGE_BASE, since __TEXT's fileoff is 0 and there is no slide).
    let main_off = text_section_off + main_rel;
    let local_funcs: Vec<(String, u32)> = local_funcs.into_iter().map(|(n, o)| (n, text_section_off + o)).collect();
    let text_len = enc.text.len() as u32;
    for (label, bytes) in data {
        data_addrs.push((label.clone(), (text_section_off + text_len) as u64 + const_bytes.len() as u64));
        const_bytes.extend_from_slice(bytes);
    }
    let const_off = text_section_off + text_len;
    let text_content_end = const_off + const_bytes.len() as u32;
    let text_filesize = align_up(text_content_end as u64, PAGE);

    // ---- __LINKEDIT content ----
    let linkedit_start = text_filesize; // file offset AND vmaddr delta (no slide)
    let fixups_blob = build_chained_fixups();
    let fixups_off = linkedit_start;
    let trie_blob = build_exports_trie(main_off as u64);
    let trie_off = fixups_off + fixups_blob.len() as u64;
    let mut all_starts: Vec<u64> = vec![main_off as u64];
    for (_, off) in &local_funcs {
        all_starts.push(*off as u64);
    }
    let funcstarts_blob = build_function_starts(all_starts);
    let funcstarts_off = trie_off + trie_blob.len() as u64;

    // symtab: locals (non-main funcs) first, then externs (__mh_execute_header, _main)
    struct Sym {
        name: String,
        n_type: u8,
        n_desc: u16,
        n_value: u64,
    }
    let mut syms = Vec::new();
    for (name, off) in &local_funcs {
        syms.push(Sym { name: format!("_{name}"), n_type: 0xe, n_desc: 0, n_value: IMAGE_BASE + *off as u64 });
    }
    let nlocal = syms.len();
    syms.push(Sym { name: "__mh_execute_header".to_string(), n_type: 0xf, n_desc: 0x10, n_value: IMAGE_BASE });
    syms.push(Sym { name: "_main".to_string(), n_type: 0xf, n_desc: 0, n_value: IMAGE_BASE + main_off as u64 });
    let nextern = 2usize;

    let mut strtab = vec![0x20u8, 0x00u8]; // matches specimen's leading pad
    let mut str_offsets = Vec::with_capacity(syms.len());
    for s in &syms {
        str_offsets.push(strtab.len() as u32);
        strtab.extend_from_slice(s.name.as_bytes());
        strtab.push(0);
    }
    let symtab_off = funcstarts_off + funcstarts_blob.len() as u64;
    let symtab_bytes_len = syms.len() as u64 * 16;
    let stroff = symtab_off + symtab_bytes_len;
    let strsize = strtab.len() as u64;
    let dataincode_off = symtab_off; // size 0: position is a don't-care, mirrors specimen
    let after_strtab = stroff + strsize;
    let codesig_off = align_up(after_strtab, 16);

    // ---- assemble __TEXT bytes (header + load commands + code + const) ----
    let mut text_seg = Vec::with_capacity(text_filesize as usize);
    text_seg.extend_from_slice(&0xFEEDFACFu32.to_le_bytes());
    text_seg.extend_from_slice(&0x0100000Cu32.to_le_bytes()); // CPU_TYPE_ARM64
    text_seg.extend_from_slice(&0u32.to_le_bytes()); // CPU_SUBTYPE_ARM64_ALL
    text_seg.extend_from_slice(&2u32.to_le_bytes()); // MH_EXECUTE
    text_seg.extend_from_slice(&ncmds.to_le_bytes());
    text_seg.extend_from_slice(&sizeofcmds.to_le_bytes());
    text_seg.extend_from_slice(&0x00200085u32.to_le_bytes()); // NOUNDEFS|DYLDLINK|TWOLEVEL|PIE
    text_seg.extend_from_slice(&0u32.to_le_bytes());

    // LC_SEGMENT_64 __PAGEZERO
    text_seg.extend_from_slice(&0x19u32.to_le_bytes());
    text_seg.extend_from_slice(&seg_pagezero_size.to_le_bytes());
    text_seg.extend_from_slice(&cstr16("__PAGEZERO"));
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&PAGEZERO_VMSIZE.to_le_bytes());
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());

    // LC_SEGMENT_64 __TEXT
    text_seg.extend_from_slice(&0x19u32.to_le_bytes());
    text_seg.extend_from_slice(&seg_text_size.to_le_bytes());
    text_seg.extend_from_slice(&cstr16("__TEXT"));
    text_seg.extend_from_slice(&IMAGE_BASE.to_le_bytes());
    text_seg.extend_from_slice(&text_filesize.to_le_bytes());
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&text_filesize.to_le_bytes());
    text_seg.extend_from_slice(&5u32.to_le_bytes()); // maxprot r-x
    text_seg.extend_from_slice(&5u32.to_le_bytes()); // initprot r-x
    text_seg.extend_from_slice(&text_nsects.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    // section __text
    text_seg.extend_from_slice(&cstr16("__text"));
    text_seg.extend_from_slice(&cstr16("__TEXT"));
    text_seg.extend_from_slice(&(IMAGE_BASE + text_section_off as u64).to_le_bytes());
    text_seg.extend_from_slice(&(text_len as u64).to_le_bytes());
    text_seg.extend_from_slice(&text_section_off.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0x8000_0400u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    if has_const {
        text_seg.extend_from_slice(&cstr16("__const"));
        text_seg.extend_from_slice(&cstr16("__TEXT"));
        text_seg.extend_from_slice(&(IMAGE_BASE + const_off as u64).to_le_bytes());
        text_seg.extend_from_slice(&(const_bytes.len() as u64).to_le_bytes());
        text_seg.extend_from_slice(&const_off.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
        text_seg.extend_from_slice(&0u32.to_le_bytes());
    }

    // LC_SEGMENT_64 __LINKEDIT
    let linkedit_filesize = codesig_off - linkedit_start; // signature appended after, patched below
    text_seg.extend_from_slice(&0x19u32.to_le_bytes());
    text_seg.extend_from_slice(&seg_linkedit_size.to_le_bytes());
    text_seg.extend_from_slice(&cstr16("__LINKEDIT"));
    text_seg.extend_from_slice(&(IMAGE_BASE + linkedit_start).to_le_bytes());
    // vmsize/filesize patched once the signature length is known; placeholders here.
    let linkedit_vmsize_patch_pos = text_seg.len();
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&linkedit_start.to_le_bytes());
    let linkedit_filesize_patch_pos = text_seg.len();
    text_seg.extend_from_slice(&0u64.to_le_bytes());
    text_seg.extend_from_slice(&1u32.to_le_bytes());
    text_seg.extend_from_slice(&1u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());

    // LC_DYLD_CHAINED_FIXUPS
    text_seg.extend_from_slice(&0x80000034u32.to_le_bytes()); // LC_DYLD_CHAINED_FIXUPS (0x34 | LC_REQ_DYLD)
    text_seg.extend_from_slice(&lc_chained_fixups_size.to_le_bytes());
    text_seg.extend_from_slice(&(fixups_off as u32).to_le_bytes());
    text_seg.extend_from_slice(&(fixups_blob.len() as u32).to_le_bytes());

    // LC_DYLD_EXPORTS_TRIE
    text_seg.extend_from_slice(&0x80000033u32.to_le_bytes()); // LC_DYLD_EXPORTS_TRIE (0x33 | LC_REQ_DYLD)
    text_seg.extend_from_slice(&lc_exports_trie_size.to_le_bytes());
    text_seg.extend_from_slice(&(trie_off as u32).to_le_bytes());
    text_seg.extend_from_slice(&(trie_blob.len() as u32).to_le_bytes());

    // LC_SYMTAB
    text_seg.extend_from_slice(&0x2u32.to_le_bytes());
    text_seg.extend_from_slice(&lc_symtab_size.to_le_bytes());
    text_seg.extend_from_slice(&(symtab_off as u32).to_le_bytes());
    text_seg.extend_from_slice(&(syms.len() as u32).to_le_bytes());
    text_seg.extend_from_slice(&(stroff as u32).to_le_bytes());
    text_seg.extend_from_slice(&(strsize as u32).to_le_bytes());

    // LC_DYSYMTAB
    text_seg.extend_from_slice(&0xBu32.to_le_bytes());
    text_seg.extend_from_slice(&lc_dysymtab_size.to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    text_seg.extend_from_slice(&(nlocal as u32).to_le_bytes());
    text_seg.extend_from_slice(&(nlocal as u32).to_le_bytes());
    text_seg.extend_from_slice(&(nextern as u32).to_le_bytes());
    text_seg.extend_from_slice(&((nlocal + nextern) as u32).to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());
    for _ in 0..12 {
        text_seg.extend_from_slice(&0u32.to_le_bytes());
    }

    // LC_LOAD_DYLINKER
    text_seg.extend_from_slice(&0xEu32.to_le_bytes());
    text_seg.extend_from_slice(&lc_dylinker_size.to_le_bytes());
    text_seg.extend_from_slice(&12u32.to_le_bytes()); // name offset
    text_seg.extend_from_slice(dylinker_name);
    text_seg.resize(text_seg.len() + (lc_dylinker_size as usize - 12 - dylinker_name.len()), 0);

    // LC_UUID
    let uuid_seed = sha256(&enc.text);
    text_seg.extend_from_slice(&0x1Bu32.to_le_bytes());
    text_seg.extend_from_slice(&lc_uuid_size.to_le_bytes());
    text_seg.extend_from_slice(&uuid_seed[0..16]);

    // LC_BUILD_VERSION
    text_seg.extend_from_slice(&0x32u32.to_le_bytes());
    text_seg.extend_from_slice(&lc_buildversion_size.to_le_bytes());
    text_seg.extend_from_slice(&1u32.to_le_bytes()); // PLATFORM_MACOS
    text_seg.extend_from_slice(&0x001a0000u32.to_le_bytes()); // minos 26.0.0
    text_seg.extend_from_slice(&0u32.to_le_bytes()); // sdk n/a
    text_seg.extend_from_slice(&0u32.to_le_bytes()); // ntools

    // LC_SOURCE_VERSION
    text_seg.extend_from_slice(&0x2Au32.to_le_bytes());
    text_seg.extend_from_slice(&lc_sourceversion_size.to_le_bytes());
    text_seg.extend_from_slice(&0u64.to_le_bytes());

    // LC_MAIN
    text_seg.extend_from_slice(&0x80000028u32.to_le_bytes()); // LC_MAIN (0x28 | LC_REQ_DYLD)
    text_seg.extend_from_slice(&lc_main_size.to_le_bytes());
    text_seg.extend_from_slice(&(main_off as u64).to_le_bytes()); // entryoff: file offset of _main
    text_seg.extend_from_slice(&0u64.to_le_bytes()); // stacksize

    // LC_LOAD_DYLIB
    text_seg.extend_from_slice(&0xCu32.to_le_bytes());
    text_seg.extend_from_slice(&lc_loaddylib_size.to_le_bytes());
    text_seg.extend_from_slice(&24u32.to_le_bytes()); // name offset
    text_seg.extend_from_slice(&2u32.to_le_bytes()); // timestamp
    text_seg.extend_from_slice(&(1356u32 << 16).to_le_bytes()); // current_version
    text_seg.extend_from_slice(&(1u32 << 16).to_le_bytes()); // compat_version
    text_seg.extend_from_slice(dylib_name);
    text_seg.resize(text_seg.len() + (lc_loaddylib_size as usize - 24 - dylib_name.len()), 0);

    // LC_FUNCTION_STARTS
    text_seg.extend_from_slice(&0x26u32.to_le_bytes());
    text_seg.extend_from_slice(&lc_funcstarts_size.to_le_bytes());
    text_seg.extend_from_slice(&(funcstarts_off as u32).to_le_bytes());
    text_seg.extend_from_slice(&(funcstarts_blob.len() as u32).to_le_bytes());

    // LC_DATA_IN_CODE
    text_seg.extend_from_slice(&0x29u32.to_le_bytes());
    text_seg.extend_from_slice(&lc_dataincode_size.to_le_bytes());
    text_seg.extend_from_slice(&(dataincode_off as u32).to_le_bytes());
    text_seg.extend_from_slice(&0u32.to_le_bytes());

    // LC_CODE_SIGNATURE
    text_seg.extend_from_slice(&0x1Du32.to_le_bytes());
    text_seg.extend_from_slice(&lc_codesig_size.to_le_bytes());
    text_seg.extend_from_slice(&(codesig_off as u32).to_le_bytes());
    let codesig_size_patch_pos = text_seg.len();
    text_seg.extend_from_slice(&0u32.to_le_bytes()); // patched once known

    debug_assert_eq!(text_seg.len() as u32, text_section_off, "load command layout drifted from the sizes computed above");

    // No `ld` here to apply the ADRP/ADD relocations `encode_program` left
    // pending for cross-section (text -> const) data references: resolve
    // them ourselves now that final addresses are known.
    let mut patched_text = enc.text.clone();
    let data_vmaddr: std::collections::HashMap<String, u64> = data_addrs.iter().map(|(l, off)| (l.clone(), IMAGE_BASE + off)).collect();
    crate::encode::resolve_relocs_inplace(&mut patched_text, &enc.relocs, IMAGE_BASE + text_section_off as u64, &data_vmaddr);

    text_seg.extend_from_slice(&patched_text);
    text_seg.extend_from_slice(&const_bytes);
    text_seg.resize(text_filesize as usize, 0);

    // ---- __LINKEDIT bytes ----
    let mut linkedit = Vec::new();
    linkedit.extend_from_slice(&fixups_blob);
    linkedit.extend_from_slice(&trie_blob);
    linkedit.extend_from_slice(&funcstarts_blob);
    for (i, s) in syms.iter().enumerate() {
        linkedit.extend_from_slice(&str_offsets[i].to_le_bytes());
        linkedit.push(s.n_type);
        linkedit.push(1); // n_sect (__text)
        linkedit.extend_from_slice(&s.n_desc.to_le_bytes());
        linkedit.extend_from_slice(&s.n_value.to_le_bytes());
    }
    linkedit.extend_from_slice(&strtab);
    while (linkedit_start as usize + linkedit.len()) % 16 != 0 {
        linkedit.push(0);
    }
    debug_assert_eq!(linkedit_start as usize + linkedit.len(), codesig_off as usize);

    // Every load-command field the signature's hashes will cover (codesig
    // size, __LINKEDIT vmsize/filesize) must be patched into `text_seg`
    // *before* we hash page 0 — the CodeDirectory signs the bytes as
    // they exist in the final file, and those fields live in page 0.
    // Their values are all computable analytically without hashing
    // anything (the signature's total length depends only on the
    // identifier length and the number of 4K pages up to codeLimit,
    // both already known).
    let ident_len = out_name.len() + 1;
    let n_slots = ((codesig_off + 4095) / 4096) as u32;
    let cd_length = 88 + ident_len as u32 + n_slots * 32;
    let sb_len = 12 + 8 + cd_length;

    text_seg[codesig_size_patch_pos..codesig_size_patch_pos + 4].copy_from_slice(&sb_len.to_le_bytes());
    let final_linkedit_filesize = (codesig_off - linkedit_start) + sb_len as u64;
    let final_linkedit_vmsize = align_up(final_linkedit_filesize, PAGE);
    text_seg[linkedit_vmsize_patch_pos..linkedit_vmsize_patch_pos + 8].copy_from_slice(&final_linkedit_vmsize.to_le_bytes());
    text_seg[linkedit_filesize_patch_pos..linkedit_filesize_patch_pos + 8].copy_from_slice(&final_linkedit_filesize.to_le_bytes());
    let _ = linkedit_filesize; // superseded by final_linkedit_filesize above

    let mut file_prefix = text_seg;
    file_prefix.extend_from_slice(&linkedit);
    debug_assert_eq!(file_prefix.len() as u64, codesig_off);

    let sig = build_code_signature(&file_prefix, out_name);
    let mut sb = sig.superblob;
    assert_eq!(sb.len() as u32, sb_len, "signature length drifted from the analytic estimate");
    // patch CodeDirectory execSegLimit now that __TEXT filesize is fixed
    // (offset within sb: superblob header 12 + index 8 + header-up-to-execSegBase 80).
    let exec_seg_limit_off = 12 + 8 + 80;
    sb[exec_seg_limit_off..exec_seg_limit_off + 8].copy_from_slice(&text_filesize.to_be_bytes());

    let mut out = file_prefix;
    out.extend_from_slice(&sb);
    out
}

pub fn write_atomically(path: &str, bytes: &[u8]) {
    use std::os::unix::fs::PermissionsExt;
    let p = std::path::Path::new(path);
    let dir = p.parent().filter(|d| !d.as_os_str().is_empty()).unwrap_or_else(|| std::path::Path::new("."));
    let tmp = dir.join(format!(".{}.tmp{}", p.file_name().unwrap().to_string_lossy(), std::process::id()));
    std::fs::write(&tmp, bytes).expect("write temp file");
    std::fs::set_permissions(&tmp, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    std::fs::rename(&tmp, p).expect("rename over target");
}
