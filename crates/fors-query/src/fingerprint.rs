//! `fors-query::decl_fingerprint()` — `docs/PLAN.md` §5's learning-mode
//! contribution point, and the policy of design §14 Q4-Q6.
//!
//! What enters a declaration's fingerprint decides what a given edit
//! invalidates. Too much is an invalidation cascade (slow); too little is a
//! stale accept (wrong). The three questions reserved for Marc, with the
//! fallback recommendations this body implements:
//!
//! - **Q4** a `const`'s comptime value: **included always**. Rule 2
//!   excludes it "unless used as a const argument"; including it
//!   over-invalidates the dependents of a constant used only as a value,
//!   which is simpler and cannot be wrong.
//! - **Q5** generic-parameter *names*: **excluded** (alpha-equivalence).
//!   Nothing observable depends on them — R38(a) is positional — so
//!   renaming `T` to `U` must not wake a single dependent.
//! - **Q6** bound lists: **order-insensitive**, so `T: Eq + Ord` and
//!   `T: Ord + Eq` are one signature.
//!
//! The function takes hashes, not syntax: the caller has already folded
//! each channel (`fors_index::fingerprint`'s token hashes for the token
//! channels, `fors_fir::encode`'s canonical encoding for the sorted bound
//! list and the comptime value). Changing the policy is changing which
//! channels this function mixes and into which of the two outputs.

use crate::key::ValueHash;

/// The channels of one declaration, each already folded to 128 bits.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeclHashes {
    /// The declaration's signature tokens (`DeclTable::sig_hash`).
    pub sig_tokens: ValueHash,
    /// Its body tokens (`DeclTable::body_hash`), or zero when it has none.
    pub body_tokens: ValueHash,
    /// A `const`'s comptime value, zero for everything else (Q4).
    pub const_value: ValueHash,
    /// Just the generic parameters' *names*, offered separately so the
    /// policy can leave them out (Q5).
    pub gparam_names: ValueHash,
    /// The bound lists, canonically sorted by the caller (Q6).
    pub bounds_sorted: ValueHash,
}

/// The two fingerprints the DAG keys on: what dependents see, and what only
/// the declaration's own body check sees.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeclFingerprint {
    /// `signature_of`'s input pre-filter: the interface ch09 R2 makes the
    /// only thing another declaration can depend on.
    pub interface: ValueHash,
    /// `check_body`'s input pre-filter.
    pub body: ValueHash,
}

/// MARC: this is the 5-to-10-line body `docs/PLAN.md` §5 reserves. Q4, Q5
/// and Q6 are the three decisions it encodes; the module docs say what each
/// alternative costs.
pub fn decl_fingerprint(h: &DeclHashes) -> DeclFingerprint {
    // Q5: `gparam_names` is deliberately NOT mixed in.
    let mut interface = mix(DOMAIN_INTERFACE, h.sig_tokens);
    interface = mix(interface, h.bounds_sorted); // Q6: already sorted.
    interface = mix(interface, h.const_value); // Q4: always.
    DeclFingerprint {
        interface,
        body: mix(DOMAIN_BODY, h.body_tokens),
    }
}

const DOMAIN_INTERFACE: ValueHash = 0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835;
const DOMAIN_BODY: ValueHash = 0xc2b2_ae3d_27d4_eb4f_1656_67b1_9e37_79b9;

/// The one-step fold the whole engine uses to combine value hashes. Not a
/// cryptographic hash: design §14 Q2 keeps FNV-128 + SplitMix64 for every
/// in-process key through M2 and defers BLAKE3 to the first
/// content-addressed cache that leaves the process.
pub fn mix(acc: ValueHash, v: ValueHash) -> ValueHash {
    let x = acc ^ v;
    let lo = splitmix64(x as u64);
    let hi = splitmix64((x >> 64) as u64 ^ lo);
    ((hi as u128) << 64) | lo as u128
}

/// Folds a sequence of hashes order-sensitively, starting from `domain`, a
/// domain-separation tag that keeps two folds of equal content apart. This is
/// a content hash for in-process memo keys (design §14 Q2: FNV/SplitMix, the
/// threat model is a compiler talking to itself), not a cryptographic salt.
pub fn mix_all(domain: ValueHash, items: impl IntoIterator<Item = ValueHash>) -> ValueHash {
    let mut acc = domain;
    for (i, v) in items.into_iter().enumerate() {
        acc = mix(acc, v ^ (i as u128));
    }
    acc
}

/// SplitMix64, the mixer `fors_index::fingerprint` already uses. Duplicated
/// rather than imported because `fors-query` depends on `std` only (design
/// §4.3) and must stay reusable with synthetic queries.
pub fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn h(sig: u128, body: u128) -> DeclHashes {
        DeclHashes {
            sig_tokens: sig,
            body_tokens: body,
            ..Default::default()
        }
    }

    #[test]
    fn renaming_a_generic_parameter_leaves_the_interface_alone() {
        let a = DeclHashes {
            gparam_names: 11,
            ..h(7, 9)
        };
        let b = DeclHashes {
            gparam_names: 22,
            ..h(7, 9)
        };
        assert_eq!(decl_fingerprint(&a), decl_fingerprint(&b));
    }

    #[test]
    fn a_body_edit_moves_only_the_body_fingerprint() {
        let a = decl_fingerprint(&h(7, 9));
        let b = decl_fingerprint(&h(7, 10));
        assert_eq!(a.interface, b.interface);
        assert_ne!(a.body, b.body);
    }

    #[test]
    fn a_const_value_edit_moves_the_interface() {
        let a = decl_fingerprint(&DeclHashes {
            const_value: 1,
            ..h(7, 0)
        });
        let b = decl_fingerprint(&DeclHashes {
            const_value: 2,
            ..h(7, 0)
        });
        assert_ne!(a.interface, b.interface);
    }

    #[test]
    fn the_two_channels_do_not_collide() {
        let f = decl_fingerprint(&h(7, 7));
        assert_ne!(f.interface, f.body);
    }

    #[test]
    fn mix_all_is_order_sensitive() {
        assert_ne!(mix_all(0, [1, 2, 3]), mix_all(0, [3, 2, 1]));
    }
}
