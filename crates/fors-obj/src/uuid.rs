//! The content-derived UUID (§4.2, E7): `UUID = SHA-256(H(page₀ with the
//! UUID field zeroed and the signature fields final) ‖ H(page₁) ‖ … ‖
//! H(pageₙ))[0..16]`, RFC 4122 version nibble 8 ("custom") and variant 10.
//! The page hashes are exactly the CodeDirectory slots, so an incremental
//! relink (M2-7) recomputes the UUID in O(pages) from slots it already has.

use crate::sha256::sha256;

pub fn from_page_hashes(hashes: &[[u8; 32]]) -> [u8; 16] {
    let mut cat = Vec::with_capacity(hashes.len() * 32);
    for h in hashes {
        cat.extend_from_slice(h);
    }
    let d = sha256(&cat);
    let mut u = [0u8; 16];
    u.copy_from_slice(&d[..16]);
    u[6] = (u[6] & 0x0F) | 0x80; // version 8
    u[8] = (u[8] & 0x3F) | 0x80; // RFC 4122 variant
    u
}

/// The UUID an image's `LC_UUID` carries.
pub fn image_uuid(image: &[u8]) -> Option<[u8; 16]> {
    let off = crate::scan::uuid_offset(image)?;
    image.get(off..off + 16)?.try_into().ok()
}

#[cfg(test)]
mod tests {
    #[test]
    fn version_and_variant_bits() {
        let u = super::from_page_hashes(&[[7u8; 32], [9u8; 32]]);
        assert_eq!(u[6] >> 4, 8);
        assert_eq!(u[8] >> 6, 0b10);
    }
}
