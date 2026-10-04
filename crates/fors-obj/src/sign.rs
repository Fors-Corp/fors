//! The ad-hoc, linker-signed code signature (§4.2): one SuperBlob holding
//! one CodeDirectory v0x20400, flags `adhoc | linker-signed`, SHA-256, page
//! size 4096, `execSeg` = `__TEXT`, no special slots, identifier = the
//! output's file stem. Ported from the spike's `build_code_signature`.
//!
//! [`verify_signature`] recomputes every slot in pure Rust, so Linux CI
//! checks the signature's internal consistency even though only macOS can
//! run `codesign --verify` (`codesign_verify_accepts_image`).

use crate::macho::Layout;
use crate::sha256::sha256;

/// CodeDirectory page size (log2 12): 4096, NOT the 16 KiB VM page
/// (`spikes/macho-resign`).
pub const CS_PAGE: usize = 4096;
const CD_HEADER: usize = 88; // through execSegFlags, version 0x20400
const SUPERBLOB_HEADER: usize = 12 + 8; // magic, length, count + one index entry

pub const CSMAGIC_EMBEDDED_SIGNATURE: u32 = 0xfade_0cc0;
pub const CSMAGIC_CODEDIRECTORY: u32 = 0xfade_0c02;
const CD_VERSION: u32 = 0x0002_0400;
/// `CS_ADHOC | CS_LINKER_SIGNED`.
pub const CD_FLAGS: u32 = 0x0002_0002;

fn n_slots(code_limit: usize) -> usize {
    code_limit.div_ceil(CS_PAGE)
}

/// The signature's total length for an image whose signed prefix is
/// `code_limit` bytes — computable before anything is hashed, which is what
/// lets every page-0 field be final before page 0 is hashed.
pub fn signature_len(code_limit: usize, identifier: &str) -> usize {
    SUPERBLOB_HEADER + CD_HEADER + identifier.len() + 1 + n_slots(code_limit) * 32
}

/// SHA-256 of every 4 KiB page of `prefix` (the last page may be short).
pub fn page_hashes(prefix: &[u8]) -> Vec<[u8; 32]> {
    prefix.chunks(CS_PAGE).map(sha256).collect()
}

fn code_directory(
    hashes: &[[u8; 32]],
    code_limit: usize,
    identifier: &str,
    exec_seg_limit: u64,
) -> Vec<u8> {
    let ident_off = CD_HEADER as u32;
    let hash_off = ident_off + identifier.len() as u32 + 1;
    let len = hash_off as usize + hashes.len() * 32;
    let mut cd = Vec::with_capacity(len);
    let be32 = |cd: &mut Vec<u8>, v: u32| cd.extend_from_slice(&v.to_be_bytes());
    be32(&mut cd, CSMAGIC_CODEDIRECTORY);
    be32(&mut cd, len as u32);
    be32(&mut cd, CD_VERSION);
    be32(&mut cd, CD_FLAGS);
    be32(&mut cd, hash_off);
    be32(&mut cd, ident_off);
    be32(&mut cd, 0); // nSpecialSlots
    be32(&mut cd, hashes.len() as u32); // nCodeSlots
    be32(&mut cd, code_limit as u32);
    cd.push(32); // hashSize
    cd.push(2); // hashType: SHA-256
    cd.push(0); // platform
    cd.push(12); // log2(pageSize)
    be32(&mut cd, 0); // spare2
    be32(&mut cd, 0); // scatterOffset
    be32(&mut cd, 0); // teamOffset
    be32(&mut cd, 0); // spare3
    cd.extend_from_slice(&0u64.to_be_bytes()); // codeLimit64 (unused: fits 32 bits)
    cd.extend_from_slice(&0u64.to_be_bytes()); // execSegBase
    cd.extend_from_slice(&exec_seg_limit.to_be_bytes());
    cd.extend_from_slice(&1u64.to_be_bytes()); // CS_EXECSEG_MAIN_BINARY
    debug_assert_eq!(cd.len(), CD_HEADER);
    cd.extend_from_slice(identifier.as_bytes());
    cd.push(0);
    for h in hashes {
        cd.extend_from_slice(h);
    }
    cd
}

/// Derives the UUID, writes it into page 0, hashes, and appends the
/// signature: the finished image.
pub fn sign(mut l: Layout, identifier: &str) -> Vec<u8> {
    assert_eq!(
        l.bytes.len(),
        l.codesig_off,
        "the layout ends where the signature starts"
    );
    let mut hashes = page_hashes(&l.bytes);
    let uuid = crate::uuid::from_page_hashes(&hashes);
    l.bytes[l.uuid_off..l.uuid_off + 16].copy_from_slice(&uuid);
    // The UUID lives in page 0 (inside the load commands): rehash it last.
    let p0 = l.uuid_off / CS_PAGE;
    let end = ((p0 + 1) * CS_PAGE).min(l.bytes.len());
    hashes[p0] = sha256(&l.bytes[p0 * CS_PAGE..end]);
    let cd = code_directory(&hashes, l.codesig_off, identifier, l.text_filesize);
    let total = SUPERBLOB_HEADER + cd.len();
    assert_eq!(
        total, l.sig_len,
        "signature length drifted from the analytic value"
    );
    let mut out = l.bytes;
    out.reserve(total);
    out.extend_from_slice(&CSMAGIC_EMBEDDED_SIGNATURE.to_be_bytes());
    out.extend_from_slice(&(total as u32).to_be_bytes());
    out.extend_from_slice(&1u32.to_be_bytes()); // count
    out.extend_from_slice(&0u32.to_be_bytes()); // CSSLOT_CODEDIRECTORY
    out.extend_from_slice(&(SUPERBLOB_HEADER as u32).to_be_bytes());
    out.extend_from_slice(&cd);
    out
}

fn be32(b: &[u8], off: usize) -> Option<u32> {
    Some(u32::from_be_bytes(b.get(off..off + 4)?.try_into().ok()?))
}

/// What [`verify_signature`] found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignatureInfo {
    pub code_limit: usize,
    pub identifier: String,
    pub slots: usize,
    pub exec_seg_limit: u64,
}

/// Recomputes the signature of `image` in pure Rust: the SuperBlob and
/// CodeDirectory are well-formed, `codeLimit` is exactly where the
/// signature starts, and every code slot equals the SHA-256 of its page.
pub fn verify_signature(image: &[u8]) -> Result<SignatureInfo, String> {
    let (off, size) = crate::scan::code_signature(image).ok_or("no LC_CODE_SIGNATURE")?;
    if off + size != image.len() {
        return Err(format!(
            "signature [{off}, +{size}) does not end the file ({})",
            image.len()
        ));
    }
    let sb = &image[off..];
    if be32(sb, 0) != Some(CSMAGIC_EMBEDDED_SIGNATURE) {
        return Err("bad SuperBlob magic".into());
    }
    if be32(sb, 4) != Some(size as u32) {
        return Err("SuperBlob length disagrees with LC_CODE_SIGNATURE".into());
    }
    if be32(sb, 8) != Some(1) || be32(sb, 12) != Some(0) {
        return Err("expected exactly one CodeDirectory slot".into());
    }
    let cd_off = be32(sb, 16).ok_or("truncated")? as usize;
    let cd = &sb[cd_off..];
    if be32(cd, 0) != Some(CSMAGIC_CODEDIRECTORY) {
        return Err("bad CodeDirectory magic".into());
    }
    if be32(cd, 8) != Some(CD_VERSION) || be32(cd, 12) != Some(CD_FLAGS) {
        return Err("unexpected CodeDirectory version or flags".into());
    }
    let hash_off = be32(cd, 16).ok_or("truncated")? as usize;
    let ident_off = be32(cd, 20).ok_or("truncated")? as usize;
    let nspecial = be32(cd, 24).ok_or("truncated")?;
    let nslots = be32(cd, 28).ok_or("truncated")? as usize;
    let code_limit = be32(cd, 32).ok_or("truncated")? as usize;
    if nspecial != 0 {
        return Err("special slots present".into());
    }
    if code_limit != off {
        return Err(format!("codeLimit {code_limit} != signature offset {off}"));
    }
    if cd.get(36..40) != Some(&[32, 2, 0, 12][..]) {
        return Err("hash size/type/page size".into());
    }
    if nslots != n_slots(code_limit) {
        return Err("slot count does not cover codeLimit".into());
    }
    let exec_seg_limit = u64::from_be_bytes(cd[72..80].try_into().map_err(|_| "truncated")?);
    let ident_end = cd[ident_off..]
        .iter()
        .position(|&b| b == 0)
        .ok_or("identifier not NUL-terminated")?;
    let identifier = String::from_utf8_lossy(&cd[ident_off..ident_off + ident_end]).into_owned();
    for (i, page) in image[..code_limit].chunks(CS_PAGE).enumerate() {
        let want = &cd[hash_off + 32 * i..hash_off + 32 * (i + 1)];
        if sha256(page) != want {
            return Err(format!("page {i} hash mismatch"));
        }
    }
    Ok(SignatureInfo {
        code_limit,
        identifier,
        slots: nslots,
        exec_seg_limit,
    })
}
