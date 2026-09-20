//! Declaration fingerprints: two 64-bit hash lanes folded over a
//! declaration's significant tokens, packed into a `u128`.
//!
//! Construction (hand-rolled, no crate): each lane is FNV-1a-style —
//! `h = (h ^ byte) * PRIME` — walked over `(kind_byte, text_bytes,
//! 0xFF_separator)` for every significant token in order, then finished
//! with a SplitMix64 avalanche step so a short common suffix between two
//! different declarations does not leave the hash's low bits weakly
//! mixed. The two lanes use different offset basis and prime constants
//! (`_LO`/`_HI`) so a collision in one lane is independent of the other,
//! which is what makes a 128-bit combination meaningfully wider than one
//! 64-bit lane rather than the same collisions twice. The separator byte
//! after each token's text prevents two adjacent tokens' bytes from
//! hashing the same as a different split of the same bytes (`"a","bc"`
//! vs `"ab","c"`); `kind_byte` similarly stops two different token kinds
//! that happen to share spelling from colliding (not possible today, but
//! the hash does not rely on the grammar to keep it that way). Nothing
//! here reads a token's absolute position or index: only kind and text,
//! in order, so the hash is relative to the declaration and unaffected
//! by where the declaration sits in the file. Stable across runs and
//! platforms: no `HashMap`, no `RandomState`, no pointer or address
//! ever enters the computation.

use fors_lex::Tokens;

const FNV_OFFSET_LO: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME_LO: u64 = 0x0000_0100_0000_01B3;
const FNV_OFFSET_HI: u64 = 0x84e0_2225_cbf1_9d29;
const FNV_PRIME_HI: u64 = 0x9E37_79B1_85EB_CA87;
const SEPARATOR: u8 = 0xFF;

// MARC: the type-checker design (§4.4) wants `splitmix64` public and a
// byte-string entry point (`hash_bytes`) so `fors-fir`'s cons table
// (open-addressed hash-consing over `(tag, a, b, quals)` keys, §5.1) can
// reuse this crate's exact avalanche step instead of a second copy, and so
// a canonical signature encoding (`fors-fir::encode::sig_hash`) can fold
// arbitrary byte strings the same way declaration fingerprints already do
// — one hash function for the whole compiler (design §14 Q2 keeps FNV-128
// + SplitMix64 rather than the PLAN's BLAKE3).
pub fn splitmix64(mut x: u64) -> u64 {
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^= x >> 31;
    x
}

fn fnv_step(mut h: u64, prime: u64, byte: u8) -> u64 {
    h ^= byte as u64;
    h = h.wrapping_mul(prime);
    h
}

/// The fixed body-hash constant used by every declaration kind whose
/// grammar has no separate body (struct/enum/trait/use/header clause):
/// there is nothing to hash, and this value is never produced by
/// [`hash_tokens`] hashing an actual (even empty) token run, because that
/// path always includes at least the SplitMix64 finishing step seeded
/// from the FNV offsets, which never lands on zero for these constants.
pub const NO_BODY: u128 = 0;

/// Folds the significant (non-trivia) raw tokens in `[first, end)` into a
/// 128-bit fingerprint. `first`/`end` are raw token indices into `tokens`
/// (as in [`fors_syntax::tree::Tree::token_range`]); trivia in the range
/// is skipped so whitespace and comment edits never change the result.
pub fn hash_tokens(tokens: &Tokens, source: &[u8], first: u32, end: u32) -> u128 {
    hash_tokens_excluding(tokens, source, first, end, &[])
}

/// As [`hash_tokens`], but the raw-token ranges in `holes` (sorted,
/// disjoint, inside `[first, end)`) are skipped. Used for an `impl` or
/// `trait`: its signature is its header, its associated-type items
/// (`type A = T;` is signature, ch09 Rules 2 and 59) and its members'
/// signatures, but NOT its members' bodies, which are the holes. Each
/// hole contributes one separator so two bodies cannot be merged into one
/// without a signature-level trace.
pub fn hash_tokens_excluding(
    tokens: &Tokens,
    source: &[u8],
    first: u32,
    end: u32,
    holes: &[(u32, u32)],
) -> u128 {
    let mut lo = FNV_OFFSET_LO;
    let mut hi = FNV_OFFSET_HI;
    let mut hole = 0usize;
    let mut i = first as usize;
    while i < end as usize {
        if hole < holes.len() && i >= holes[hole].0 as usize {
            i = i.max(holes[hole].1 as usize);
            hole += 1;
            lo = fnv_step(lo, FNV_PRIME_LO, SEPARATOR);
            hi = fnv_step(hi, FNV_PRIME_HI, SEPARATOR);
            continue;
        }
        let at = i;
        i += 1;
        let kind = tokens.kinds[at];
        if kind.is_trivia() {
            continue;
        }
        let text = tokens.text(at, source);
        let kind_byte = kind as u8;
        lo = fnv_step(lo, FNV_PRIME_LO, kind_byte);
        hi = fnv_step(hi, FNV_PRIME_HI, kind_byte);
        for &b in text {
            lo = fnv_step(lo, FNV_PRIME_LO, b);
            hi = fnv_step(hi, FNV_PRIME_HI, b);
        }
        lo = fnv_step(lo, FNV_PRIME_LO, SEPARATOR);
        hi = fnv_step(hi, FNV_PRIME_HI, SEPARATOR);
    }
    lo = splitmix64(lo);
    hi = splitmix64(hi ^ lo);
    ((hi as u128) << 64) | lo as u128
}

/// Folds an arbitrary byte string into the same two-lane FNV-128 +
/// SplitMix64 fingerprint as [`hash_tokens`], with no token/kind/separator
/// structure imposed on it: the caller (`fors-fir::encode`) is responsible
/// for its own unambiguous framing (length-prefixing or its own
/// separators) if it hashes more than one logical field. Used for the
/// canonical FIR signature hash (`sig_hash`, design §5.4), not for
/// declaration fingerprints (that stays [`hash_tokens`]/[`decl_fingerprint`]).
pub fn hash_bytes(bytes: &[u8]) -> u128 {
    let mut lo = FNV_OFFSET_LO;
    let mut hi = FNV_OFFSET_HI;
    for &b in bytes {
        lo = fnv_step(lo, FNV_PRIME_LO, b);
        hi = fnv_step(hi, FNV_PRIME_HI, b);
    }
    lo = splitmix64(lo);
    hi = splitmix64(hi ^ lo);
    ((hi as u128) << 64) | lo as u128
}

/// Whether raw token `i` is significant (kept out of every fingerprint
/// range boundary computation as well as the hash itself).
pub fn is_significant(tokens: &Tokens, i: usize) -> bool {
    !tokens.kinds[i].is_trivia()
}

// MARC: what enters a declaration's fingerprint decides the project's
// incremental behaviour. Too much (doc comments, attribute order, spans)
// causes invalidation cascades; too little causes stale results, which is
// a correctness bug. Doc comments are currently EXCLUDED; attributes are
// INCLUDED.
/// Computes `(sig_hash, body_hash)` for one declaration, given the raw
/// token range of its signature and, if it has a separate body, of that
/// body. Doc comments are ordinary `LineComment`/`BlockComment` tokens,
/// already excluded because [`hash_tokens`] skips all trivia; there is no
/// separate doc-comment channel to special-case. Attributes are part of
/// whatever range they precede (a declaration's `sig_range` starts at its
/// leading trivia, which includes any `@attr` tokens before it), so they
/// enter `sig_hash` like any other significant token.
pub fn decl_fingerprint(
    tokens: &Tokens,
    source: &[u8],
    sig_range: (u32, u32),
    body_range: Option<(u32, u32)>,
) -> (u128, u128) {
    let sig_hash = hash_tokens(tokens, source, sig_range.0, sig_range.1);
    let body_hash = match body_range {
        Some((s, e)) => hash_tokens(tokens, source, s, e),
        None => NO_BODY,
    };
    (sig_hash, body_hash)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_lex::lex;

    fn hash_all(src: &str) -> u128 {
        let (tokens, _) = lex(src.as_bytes());
        hash_tokens(&tokens, src.as_bytes(), 0, tokens.len() as u32)
    }

    #[test]
    fn whitespace_and_comments_do_not_change_hash() {
        assert_eq!(hash_all("fn f() {}"), hash_all("fn   f()   {  }"));
        assert_eq!(hash_all("fn f() {}"), hash_all("// hi\nfn f() {} // bye"));
    }

    #[test]
    fn different_text_changes_hash() {
        assert_ne!(hash_all("fn f() {}"), hash_all("fn g() {}"));
    }

    #[test]
    fn token_boundary_is_not_ambiguous() {
        // "ab" as one ident vs "a","b" as two must not collide even
        // though the concatenated bytes are equal.
        assert_ne!(hash_all("ab"), hash_all("a b"));
    }
}
