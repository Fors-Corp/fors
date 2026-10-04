//! The exports trie (`LC_DYLD_EXPORTS_TRIE`): exactly the two exports an
//! executable needs, `__mh_execute_header` (address 0) and `_main`. The shape
//! is fixed — root → `"_"` → {`"_mh_execute_header"`, `"main"`} — so it is
//! built directly, as the spike did, but with every ULEB128 offset sized for
//! real (the spike asserted they fit one byte).

/// Appends `v` as ULEB128.
pub fn uleb128(buf: &mut Vec<u8>, mut v: u64) {
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

fn uleb_len(v: u64) -> usize {
    let mut b = Vec::new();
    uleb128(&mut b, v);
    b.len()
}

/// A terminal node exporting `addr` (flags 0 = regular), no children.
fn leaf(addr: u64) -> Vec<u8> {
    let mut info = Vec::new();
    uleb128(&mut info, 0); // flags
    uleb128(&mut info, addr);
    let mut n = Vec::new();
    uleb128(&mut n, info.len() as u64);
    n.extend_from_slice(&info);
    n.push(0); // no children
    n
}

/// The trie for `__mh_execute_header` at 0 and `_main` at `main_addr`
/// (both offsets from the image base), padded to 8 bytes.
pub fn exports_trie(main_addr: u64) -> Vec<u8> {
    const L1: &[u8] = b"_mh_execute_header\0";
    const L2: &[u8] = b"main\0";
    let leaf1 = leaf(0);
    let leaf2 = leaf(main_addr);
    // Offsets depend on the ULEB sizes of the offsets themselves; iterate to
    // a fixed point (two rounds always suffice for a trie this small).
    let mut under_off = 0u64;
    let mut leaf1_off = 0u64;
    let mut leaf2_off = 0u64;
    for _ in 0..4 {
        let root_len = 1 + 1 + 2 + uleb_len(under_off);
        under_off = root_len as u64;
        let under_len = 1 + 1 + L1.len() + uleb_len(leaf1_off) + L2.len() + uleb_len(leaf2_off);
        leaf1_off = under_off + under_len as u64;
        leaf2_off = leaf1_off + leaf1.len() as u64;
    }
    let mut t = Vec::new();
    t.push(0); // root: not terminal
    t.push(1); // one child
    t.extend_from_slice(b"_\0");
    uleb128(&mut t, under_off);
    assert_eq!(t.len() as u64, under_off, "trie root size");
    t.push(0);
    t.push(2);
    t.extend_from_slice(L1);
    uleb128(&mut t, leaf1_off);
    t.extend_from_slice(L2);
    uleb128(&mut t, leaf2_off);
    assert_eq!(t.len() as u64, leaf1_off, "trie '_' node size");
    t.extend_from_slice(&leaf1);
    t.extend_from_slice(&leaf2);
    t.resize(t.len().div_ceil(8) * 8, 0);
    t
}

/// Looks `name` up in a trie (for tests and image scans): its address.
pub fn lookup(trie: &[u8], name: &str) -> Option<u64> {
    fn read_uleb(b: &[u8], pos: &mut usize) -> Option<u64> {
        let mut v = 0u64;
        let mut shift = 0;
        loop {
            let byte = *b.get(*pos)?;
            *pos += 1;
            v |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Some(v);
            }
            shift += 7;
            if shift > 63 {
                return None;
            }
        }
    }
    let mut node = 0usize;
    let mut rest = name.as_bytes();
    loop {
        let mut pos = node;
        let term = read_uleb(trie, &mut pos)? as usize;
        if rest.is_empty() {
            if term == 0 {
                return None;
            }
            let mut p = pos;
            let _flags = read_uleb(trie, &mut p)?;
            return read_uleb(trie, &mut p);
        }
        pos += term;
        let n = *trie.get(pos)? as usize;
        pos += 1;
        let mut next = None;
        for _ in 0..n {
            let start = pos;
            while *trie.get(pos)? != 0 {
                pos += 1;
            }
            let label = &trie[start..pos];
            pos += 1;
            let off = read_uleb(trie, &mut pos)? as usize;
            if next.is_none() && rest.starts_with(label) {
                next = Some((label.len(), off));
            }
        }
        let (used, off) = next?;
        rest = &rest[used..];
        node = off;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_exports_resolve_for_small_and_large_addresses() {
        for addr in [0x4000u64, 0x4_0000, 0x1234_5678] {
            let t = exports_trie(addr);
            assert_eq!(t.len() % 8, 0);
            assert_eq!(lookup(&t, "__mh_execute_header"), Some(0));
            assert_eq!(lookup(&t, "_main"), Some(addr));
            assert_eq!(lookup(&t, "_mai"), None);
            assert_eq!(lookup(&t, "_other"), None);
        }
    }
}
