//! `LC_DYLD_CHAINED_FIXUPS`'s payload. M2-0's images import nothing and
//! rebase nothing, so the blob is the spike's empty one: a
//! `dyld_chained_fixups_header` (imports format `DYLD_CHAINED_IMPORT`, zero
//! imports) and a `dyld_chained_starts_in_image` with one zero
//! `seg_info_offset` per segment ("this segment has no fixup chains").
//! Binds and rebases (`__got`, M2-3) extend this module.

/// The blob for an image with `segments` segments (`__PAGEZERO`,
/// `__TEXT`, `__LINKEDIT` in M2-0: 3). Address-independent.
pub fn empty_chained_fixups(segments: u32) -> Vec<u8> {
    let mut b = Vec::new();
    let starts_offset = 32u32;
    let starts_len = 4 + 4 * segments;
    let imports_offset = starts_offset + starts_len.div_ceil(8) * 8;
    b.extend_from_slice(&0u32.to_le_bytes()); // fixups_version
    b.extend_from_slice(&starts_offset.to_le_bytes());
    b.extend_from_slice(&imports_offset.to_le_bytes());
    b.extend_from_slice(&imports_offset.to_le_bytes()); // symbols_offset
    b.extend_from_slice(&0u32.to_le_bytes()); // imports_count
    b.extend_from_slice(&1u32.to_le_bytes()); // DYLD_CHAINED_IMPORT
    b.extend_from_slice(&0u32.to_le_bytes()); // symbols_format (uncompressed)
    b.extend_from_slice(&0u32.to_le_bytes()); // pad to starts_offset
    b.extend_from_slice(&segments.to_le_bytes()); // seg_count
    for _ in 0..segments {
        b.extend_from_slice(&0u32.to_le_bytes()); // seg_info_offset: none
    }
    // An empty symbol pool, padded as ld64 writes it (the specimen's blob,
    // and so the spike's, is 56 bytes for three segments).
    b.resize(imports_offset as usize + 8, 0);
    b
}

#[cfg(test)]
mod tests {
    #[test]
    fn three_segments_reproduce_the_spike_blob() {
        // The spike's hand-written 56-byte blob (seg_count 3).
        let b = super::empty_chained_fixups(3);
        assert_eq!(b.len(), 56);
        assert_eq!(&b[8..12], &48u32.to_le_bytes());
        assert_eq!(&b[32..36], &3u32.to_le_bytes());
        assert!(b[36..].iter().all(|&x| x == 0));
    }
}
