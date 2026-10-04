//! The `MH_EXECUTE` writer (§4.1), ported from
//! `spikes/aarch64-macho/src/exec.rs`. Layout and every load-command field
//! value were derived by the spike from an `ld64`-linked specimen read back
//! with `otool -l`; this port keeps them, minus `__DATA*` (no imports and no
//! mutable data until M2-3) and minus `LC_DATA_IN_CODE` (not in §4.1's set),
//! plus the image directory sections and a content-derived UUID.
//!
//! File layout (no slide; file offset == address - [`IMAGE_BASE`]):
//!
//! ```text
//! 0        mach_header_64, 15 load commands
//! T        __TEXT,__text        (16-aligned)   atoms, placed by fors-link
//!          __TEXT,__fors_dir    (8-aligned)    16 B per atom, by address
//!          __TEXT,__fors_lines  (4-aligned)    per-declaration line table
//! P        __LINKEDIT (P = __TEXT filesize, a 16 KiB multiple):
//!          chained fixups, exports trie, function starts, symtab, strtab,
//!          code signature (16-aligned, last)
//! ```
//!
//! [`layout`] produces every byte up to the code signature with the UUID
//! zeroed and every page-0 field (signature size, `__LINKEDIT` sizes)
//! already final — the spike's second recorded pitfall: the CodeDirectory
//! must hash the final bytes, and those fields live in page 0, so their
//! values are computed analytically first (identifier length and page count
//! are all they depend on). [`crate::sign::sign`] then derives the UUID,
//! writes it, and appends the signature.

use crate::fixups::empty_chained_fixups;
use crate::sign::signature_len;
use crate::trie::{exports_trie, uleb128};

pub const IMAGE_BASE: u64 = 0x1_0000_0000;
const PAGEZERO_VMSIZE: u64 = 0x1_0000_0000;
/// Segment alignment (the arm64 VM page).
pub const SEG_PAGE: u64 = 0x4000;
/// `LC_BUILD_VERSION` minos = 14.0 (E11; chained fixups need >= 12).
pub const MACOS_MIN: u32 = 0x000e_0000;

const MH_MAGIC_64: u32 = 0xFEED_FACF;
const CPU_TYPE_ARM64: u32 = 0x0100_000C;
const MH_EXECUTE: u32 = 2;
/// `MH_NOUNDEFS | MH_DYLDLINK | MH_TWOLEVEL | MH_PIE`.
pub const MH_FLAGS: u32 = 0x0020_0085;

pub const LC_SEGMENT_64: u32 = 0x19;
pub const LC_SYMTAB: u32 = 0x2;
pub const LC_DYSYMTAB: u32 = 0xB;
pub const LC_LOAD_DYLIB: u32 = 0xC;
pub const LC_LOAD_DYLINKER: u32 = 0xE;
pub const LC_UUID: u32 = 0x1B;
pub const LC_CODE_SIGNATURE: u32 = 0x1D;
pub const LC_FUNCTION_STARTS: u32 = 0x26;
pub const LC_MAIN: u32 = 0x8000_0028;
pub const LC_SOURCE_VERSION: u32 = 0x2A;
pub const LC_BUILD_VERSION: u32 = 0x32;
pub const LC_DYLD_EXPORTS_TRIE: u32 = 0x8000_0033;
pub const LC_DYLD_CHAINED_FIXUPS: u32 = 0x8000_0034;

const S_ATTR_CODE: u32 = 0x8000_0400; // PURE_INSTRUCTIONS | SOME_INSTRUCTIONS

const DYLINKER: &[u8] = b"/usr/lib/dyld\0";
const LIBSYSTEM: &[u8] = b"/usr/lib/libSystem.B.dylib\0";

/// What the linker hands the writer.
#[derive(Clone, Copy, Debug)]
pub struct ExecSpec<'a> {
    /// `__text`'s contents.
    pub text: &'a [u8],
    /// Offset of the entry point (`_main`) inside `text`.
    pub entry: u32,
    /// Offsets of every function start inside `text`, any order.
    pub function_starts: &'a [u32],
    /// `__fors_dir`'s contents.
    pub dir: &'a [u8],
    /// `__fors_lines`'s contents.
    pub lines: &'a [u8],
    /// The code signature's identifier: the output's file stem.
    pub identifier: &'a str,
}

/// Every byte before the code signature, plus where the signer must look.
#[derive(Clone, Debug)]
pub struct Layout {
    /// The image up to `codesig_off`, UUID zeroed, page-0 fields final.
    pub bytes: Vec<u8>,
    pub uuid_off: usize,
    pub codesig_off: usize,
    /// The analytically computed signature length (asserted by the signer).
    pub sig_len: usize,
    pub text_filesize: u64,
    /// File offset of `__text`.
    pub text_off: u32,
}

pub fn align_up(x: u64, a: u64) -> u64 {
    x.div_ceil(a) * a
}

fn name16(s: &str) -> [u8; 16] {
    let mut b = [0u8; 16];
    b[..s.len()].copy_from_slice(s.as_bytes());
    b
}

struct W(Vec<u8>);

impl W {
    fn u32(&mut self, v: u32) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.0.extend_from_slice(&v.to_le_bytes());
    }
    fn bytes(&mut self, b: &[u8]) {
        self.0.extend_from_slice(b);
    }
    fn pos(&self) -> usize {
        self.0.len()
    }
    fn pad_to(&mut self, n: usize) {
        assert!(self.0.len() <= n, "layout overran: {} > {n}", self.0.len());
        self.0.resize(n, 0);
    }
}

/// A `section_64`: 80 bytes, with THREE reserved fields — the spike's first
/// recorded pitfall (a missing `reserved3` shifts every later load command
/// by 4 bytes; `section64_has_three_reserved_fields` pins it).
#[allow(clippy::too_many_arguments)]
fn section(
    w: &mut W,
    sect: &str,
    seg: &str,
    addr: u64,
    size: u64,
    off: u32,
    align_log2: u32,
    flags: u32,
) {
    let start = w.pos();
    w.bytes(&name16(sect));
    w.bytes(&name16(seg));
    w.u64(addr);
    w.u64(size);
    w.u32(off);
    w.u32(align_log2);
    w.u32(0); // reloff
    w.u32(0); // nreloc
    w.u32(flags);
    w.u32(0); // reserved1
    w.u32(0); // reserved2
    w.u32(0); // reserved3
    debug_assert_eq!(w.pos() - start, SECTION_64_SIZE);
}

pub const SECTION_64_SIZE: usize = 80;
pub const SEGMENT_64_SIZE: usize = 72;

/// Function starts as ULEB128 deltas from the `__TEXT` base, zero
/// terminated, padded to 8.
fn function_starts(text_off: u32, starts: &[u32]) -> Vec<u8> {
    let mut addrs: Vec<u64> = starts.iter().map(|&s| u64::from(text_off + s)).collect();
    addrs.sort_unstable();
    addrs.dedup();
    let mut out = Vec::new();
    let mut prev = 0u64;
    for a in addrs {
        uleb128(&mut out, a - prev);
        prev = a;
    }
    out.push(0);
    out.resize(out.len().div_ceil(8) * 8, 0);
    out
}

const NCMDS: u32 = 15;

fn sizeofcmds() -> u32 {
    let dylinker = align_up((12 + DYLINKER.len()) as u64, 8) as u32;
    let dylib = align_up((24 + LIBSYSTEM.len()) as u64, 8) as u32;
    (SEGMENT_64_SIZE as u32) // __PAGEZERO
        + (SEGMENT_64_SIZE + 3 * SECTION_64_SIZE) as u32 // __TEXT
        + SEGMENT_64_SIZE as u32 // __LINKEDIT
        + 16 // chained fixups
        + 16 // exports trie
        + 24 // symtab
        + 80 // dysymtab
        + dylinker
        + 24 // uuid
        + 24 // build version
        + 16 // source version
        + 24 // main
        + dylib
        + 16 // function starts
        + 16 // code signature
}

/// Lays out the unsigned image of `spec` (see the module docs).
pub fn layout(spec: &ExecSpec<'_>) -> Layout {
    let cmds = sizeofcmds();
    let header_end = 32 + cmds as u64;
    let text_off = align_up(header_end, 16);
    let text_end = text_off + spec.text.len() as u64;
    let dir_off = align_up(text_end, 8);
    let lines_off = align_up(dir_off + spec.dir.len() as u64, 4);
    let content_end = lines_off + spec.lines.len() as u64;
    let text_filesize = align_up(content_end, SEG_PAGE);
    let text_off = text_off as u32;

    // __LINKEDIT
    let le = text_filesize;
    let fixups = empty_chained_fixups(3);
    let fixups_off = le;
    let main_off = u64::from(text_off + spec.entry);
    let trie = exports_trie(main_off);
    let trie_off = fixups_off + fixups.len() as u64;
    let fstarts = function_starts(text_off, spec.function_starts);
    let fstarts_off = trie_off + trie.len() as u64;
    // Symtab: exports only (§4.1): __mh_execute_header, _main.
    let syms: [(&str, u8, u16, u64); 2] = [
        ("__mh_execute_header", 0x0f, 0x0010, IMAGE_BASE),
        ("_main", 0x0f, 0, IMAGE_BASE + main_off),
    ];
    let mut strtab = vec![b' ', 0u8];
    let mut stroffs = Vec::new();
    for (name, ..) in &syms {
        stroffs.push(strtab.len() as u32);
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
    }
    strtab.resize(strtab.len().div_ceil(8) * 8, 0);
    let symtab_off = fstarts_off + fstarts.len() as u64;
    let stroff = symtab_off + 16 * syms.len() as u64;
    let codesig_off = align_up(stroff + strtab.len() as u64, 16);
    let sig_len = signature_len(codesig_off as usize, spec.identifier);
    let linkedit_filesize = codesig_off - le + sig_len as u64;
    let linkedit_vmsize = align_up(linkedit_filesize, SEG_PAGE);

    let mut w = W(Vec::with_capacity(codesig_off as usize));
    // mach_header_64
    w.u32(MH_MAGIC_64);
    w.u32(CPU_TYPE_ARM64);
    w.u32(0); // CPU_SUBTYPE_ARM64_ALL
    w.u32(MH_EXECUTE);
    w.u32(NCMDS);
    w.u32(cmds);
    w.u32(MH_FLAGS);
    w.u32(0);

    // __PAGEZERO
    w.u32(LC_SEGMENT_64);
    w.u32(SEGMENT_64_SIZE as u32);
    w.bytes(&name16("__PAGEZERO"));
    w.u64(0);
    w.u64(PAGEZERO_VMSIZE);
    w.u64(0);
    w.u64(0);
    w.u32(0);
    w.u32(0);
    w.u32(0);
    w.u32(0);

    // __TEXT
    w.u32(LC_SEGMENT_64);
    w.u32((SEGMENT_64_SIZE + 3 * SECTION_64_SIZE) as u32);
    w.bytes(&name16("__TEXT"));
    w.u64(IMAGE_BASE);
    w.u64(text_filesize);
    w.u64(0);
    w.u64(text_filesize);
    w.u32(5); // maxprot r-x
    w.u32(5); // initprot r-x
    w.u32(3); // nsects
    w.u32(0);
    section(
        &mut w,
        "__text",
        "__TEXT",
        IMAGE_BASE + u64::from(text_off),
        spec.text.len() as u64,
        text_off,
        4,
        S_ATTR_CODE,
    );
    section(
        &mut w,
        "__fors_dir",
        "__TEXT",
        IMAGE_BASE + dir_off,
        spec.dir.len() as u64,
        dir_off as u32,
        3,
        0,
    );
    section(
        &mut w,
        "__fors_lines",
        "__TEXT",
        IMAGE_BASE + lines_off,
        spec.lines.len() as u64,
        lines_off as u32,
        2,
        0,
    );

    // __LINKEDIT
    w.u32(LC_SEGMENT_64);
    w.u32(SEGMENT_64_SIZE as u32);
    w.bytes(&name16("__LINKEDIT"));
    w.u64(IMAGE_BASE + le);
    w.u64(linkedit_vmsize);
    w.u64(le);
    w.u64(linkedit_filesize);
    w.u32(1); // r
    w.u32(1);
    w.u32(0);
    w.u32(0);

    w.u32(LC_DYLD_CHAINED_FIXUPS);
    w.u32(16);
    w.u32(fixups_off as u32);
    w.u32(fixups.len() as u32);

    w.u32(LC_DYLD_EXPORTS_TRIE);
    w.u32(16);
    w.u32(trie_off as u32);
    w.u32(trie.len() as u32);

    w.u32(LC_SYMTAB);
    w.u32(24);
    w.u32(symtab_off as u32);
    w.u32(syms.len() as u32);
    w.u32(stroff as u32);
    w.u32(strtab.len() as u32);

    w.u32(LC_DYSYMTAB);
    w.u32(80);
    w.u32(0); // ilocalsym
    w.u32(0); // nlocalsym
    w.u32(0); // iextdefsym
    w.u32(syms.len() as u32); // nextdefsym
    w.u32(syms.len() as u32); // iundefsym
    w.u32(0); // nundefsym
    for _ in 0..12 {
        w.u32(0);
    }

    let dylinker_len = align_up((12 + DYLINKER.len()) as u64, 8) as usize;
    let start = w.pos();
    w.u32(LC_LOAD_DYLINKER);
    w.u32(dylinker_len as u32);
    w.u32(12);
    w.bytes(DYLINKER);
    w.pad_to(start + dylinker_len);

    w.u32(LC_UUID);
    w.u32(24);
    let uuid_off = w.pos();
    w.bytes(&[0u8; 16]);

    w.u32(LC_BUILD_VERSION);
    w.u32(24);
    w.u32(1); // PLATFORM_MACOS
    w.u32(MACOS_MIN);
    w.u32(0); // sdk
    w.u32(0); // ntools

    w.u32(LC_SOURCE_VERSION);
    w.u32(16);
    w.u64(0);

    w.u32(LC_MAIN);
    w.u32(24);
    w.u64(main_off); // entryoff
    w.u64(0); // stacksize

    let dylib_len = align_up((24 + LIBSYSTEM.len()) as u64, 8) as usize;
    let start = w.pos();
    w.u32(LC_LOAD_DYLIB);
    w.u32(dylib_len as u32);
    w.u32(24); // name offset
    w.u32(2); // timestamp: fixed at 2, as ld64 writes (never a real time)
    w.u32(1356 << 16); // current_version
    w.u32(1 << 16); // compatibility_version
    w.bytes(LIBSYSTEM);
    w.pad_to(start + dylib_len);

    w.u32(LC_FUNCTION_STARTS);
    w.u32(16);
    w.u32(fstarts_off as u32);
    w.u32(fstarts.len() as u32);

    w.u32(LC_CODE_SIGNATURE);
    w.u32(16);
    w.u32(codesig_off as u32);
    w.u32(sig_len as u32);

    assert_eq!(
        w.pos() as u64,
        header_end,
        "load commands drifted from sizeofcmds"
    );
    w.pad_to(text_off as usize);
    w.bytes(spec.text);
    w.pad_to(dir_off as usize);
    w.bytes(spec.dir);
    w.pad_to(lines_off as usize);
    w.bytes(spec.lines);
    w.pad_to(text_filesize as usize);

    w.bytes(&fixups);
    w.bytes(&trie);
    w.bytes(&fstarts);
    for (i, (_, ty, desc, value)) in syms.iter().enumerate() {
        w.u32(stroffs[i]);
        w.0.push(*ty);
        w.0.push(1); // n_sect: __text
        w.0.extend_from_slice(&desc.to_le_bytes());
        w.u64(*value);
    }
    w.bytes(&strtab);
    w.pad_to(codesig_off as usize);

    Layout {
        bytes: w.0,
        uuid_off,
        codesig_off: codesig_off as usize,
        sig_len,
        text_filesize,
        text_off,
    }
}

/// The signed executable of `spec`.
pub fn build_executable(spec: &ExecSpec<'_>) -> Vec<u8> {
    crate::sign::sign(layout(spec), spec.identifier)
}
