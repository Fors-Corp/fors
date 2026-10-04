//! Read-back of an image this crate wrote: load commands, sections, the
//! signature and UUID locations. Used by the gate tests (the unwind-section
//! and host-path scans, the two spike pitfalls) and by the pure-Rust
//! signature check; deliberately strict (a malformed image is `None`, never
//! a panic).

fn le32(b: &[u8], off: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(off..off + 4)?.try_into().ok()?))
}

fn le64(b: &[u8], off: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(off..off + 8)?.try_into().ok()?))
}

fn name(b: &[u8]) -> String {
    let end = b.iter().position(|&c| c == 0).unwrap_or(b.len());
    String::from_utf8_lossy(&b[..end]).into_owned()
}

/// One load command: `(cmd, file offset, cmdsize)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoadCommand {
    pub cmd: u32,
    pub off: usize,
    pub size: usize,
}

/// Every load command, checked to tile exactly `sizeofcmds`.
pub fn load_commands(image: &[u8]) -> Option<Vec<LoadCommand>> {
    if le32(image, 0)? != 0xFEED_FACF {
        return None;
    }
    let ncmds = le32(image, 16)? as usize;
    let sizeofcmds = le32(image, 20)? as usize;
    let mut off = 32;
    let mut out = Vec::new();
    for _ in 0..ncmds {
        let cmd = le32(image, off)?;
        let size = le32(image, off + 4)? as usize;
        if size < 8 || !size.is_multiple_of(8) {
            return None;
        }
        out.push(LoadCommand { cmd, off, size });
        off += size;
    }
    (off == 32 + sizeofcmds).then_some(out)
}

/// A `section_64` as read back, reserved fields included.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub segname: String,
    pub sectname: String,
    pub addr: u64,
    pub size: u64,
    pub offset: u32,
    pub align: u32,
    pub flags: u32,
    pub reserved: [u32; 3],
    /// File offset of this `section_64` record itself.
    pub record_off: usize,
}

/// A segment and its sections.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Segment {
    pub name: String,
    pub vmaddr: u64,
    pub vmsize: u64,
    pub fileoff: u64,
    pub filesize: u64,
    pub sections: Vec<Section>,
}

pub fn segments(image: &[u8]) -> Option<Vec<Segment>> {
    let mut out = Vec::new();
    for lc in load_commands(image)? {
        if lc.cmd != crate::macho::LC_SEGMENT_64 {
            continue;
        }
        let o = lc.off;
        let nsects = le32(image, o + 64)? as usize;
        if lc.size != crate::macho::SEGMENT_64_SIZE + nsects * crate::macho::SECTION_64_SIZE {
            return None;
        }
        let mut sections = Vec::new();
        for i in 0..nsects {
            let s = o + crate::macho::SEGMENT_64_SIZE + i * crate::macho::SECTION_64_SIZE;
            sections.push(Section {
                sectname: name(image.get(s..s + 16)?),
                segname: name(image.get(s + 16..s + 32)?),
                addr: le64(image, s + 32)?,
                size: le64(image, s + 40)?,
                offset: le32(image, s + 48)?,
                align: le32(image, s + 52)?,
                flags: le32(image, s + 64)?,
                reserved: [
                    le32(image, s + 68)?,
                    le32(image, s + 72)?,
                    le32(image, s + 76)?,
                ],
                record_off: s,
            });
        }
        out.push(Segment {
            name: name(image.get(o + 8..o + 24)?),
            vmaddr: le64(image, o + 24)?,
            vmsize: le64(image, o + 32)?,
            fileoff: le64(image, o + 40)?,
            filesize: le64(image, o + 48)?,
            sections,
        });
    }
    Some(out)
}

/// `(dataoff, datasize)` of `LC_CODE_SIGNATURE`.
pub fn code_signature(image: &[u8]) -> Option<(usize, usize)> {
    let lc = load_commands(image)?
        .into_iter()
        .find(|l| l.cmd == crate::macho::LC_CODE_SIGNATURE)?;
    Some((
        le32(image, lc.off + 8)? as usize,
        le32(image, lc.off + 12)? as usize,
    ))
}

/// File offset of `LC_UUID`'s 16 bytes.
pub fn uuid_offset(image: &[u8]) -> Option<usize> {
    let lc = load_commands(image)?
        .into_iter()
        .find(|l| l.cmd == crate::macho::LC_UUID)?;
    Some(lc.off + 8)
}

/// The bytes of section `seg,sect`.
pub fn section_bytes<'a>(image: &'a [u8], seg: &str, sect: &str) -> Option<&'a [u8]> {
    let s = segments(image)?
        .into_iter()
        .flat_map(|g| g.sections)
        .find(|s| s.segname == seg && s.sectname == sect)?;
    image.get(s.offset as usize..s.offset as usize + s.size as usize)
}

/// Every section name, as `segname,sectname`.
pub fn section_names(image: &[u8]) -> Option<Vec<String>> {
    Some(
        segments(image)?
            .into_iter()
            .flat_map(|g| g.sections)
            .map(|s| format!("{},{}", s.segname, s.sectname))
            .collect(),
    )
}
