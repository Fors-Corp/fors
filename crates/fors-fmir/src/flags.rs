//! `ValRow.flags`: the seven per-value bits of design §3.1/§1.1.
//!
//! Mirrors `fors_fir::ty::Quals`'s convention (a `pub struct Foo(pub u8/u16)`
//! bit set with named constants, `union`, and `is_*` queries) rather than a
//! `bitflags!`-style macro, since this workspace has zero third-party
//! dependencies and already has an in-crate idiom for exactly this shape.
//! [decision: hand-rolled bit set, styled after `fors_fir::ty::Quals`]

/// `secret` — ch05 Rule 6/6a. Propagated by `fors-lower` (F1+); this crate's
/// `verify()` checks the propagation invariant already holds (§3.11) rather
/// than computing it.
pub const SECRET: u16 = 1 << 0;
/// A comptime-known value (folds into `ConstPool`, design §3.1).
pub const CONST: u16 = 1 << 1;
/// `SCOPED` — PLAN R3, ch01 R19-R19d: carries a live `sources` range into a
/// `SourcePool` (design §3.4).
pub const SCOPED: u16 = 1 << 2;
/// `LINEAR` — ch01 R22a's `lin(T)`, carried by `fors-lower` (design §3.5).
pub const LINEAR: u16 = 1 << 3;
/// Isolation-domain value (a `spawn`/`parallel` region's isolated binding).
pub const ISO: u16 = 1 << 4;
/// Immutable-only binding.
pub const IMM: u16 = 1 << 5;
/// Compiler-internal temporary (never named by source), used by dumps to
/// choose `%tN` vs a source-derived name and by the reducer to know a value
/// is safe to splice out without a user-visible rename.
pub const TMP: u16 = 1 << 6;

/// Parser-only marker: the textual form omitted the `secret`/`nosecret`
/// token entirely (as opposed to writing `nosecret`, which clears [`SECRET`]
/// normally). `verify()` rejects any row carrying it — this is how the
/// negative corpus expresses ch05 Rule 6's "missing secret field" (a lowering
/// bug that produced an incomplete row) despite the safe builder API being
/// unable to construct one (design §1: "a row without them must not be
/// constructible, or the verifier must reject it" — the builder gives the
/// first half, this bit plus `verify_rejects_missing_secret_field` gives the
/// second, for the one path that must stay expressible: hand-written FMIR
/// text, and the negative-corpus tests that build the same shape directly —
/// `ValRow`'s fields are public, so `verify()`, not the constructor, is what
/// enforces the rule for every provenance; see `value.rs`'s module docs).
/// [`ValFlags::new`] never sets it, and `dump` only ever emits it for a row
/// that already carries it. [decision: sentinel bit for "textually absent", not an
/// `Option<bool>` field, so `ValRow` itself stays the fixed 12-byte row width
/// design §3.1 specifies]
pub const SECRET_UNSPECIFIED: u16 = 1 << 15;

/// One `ValRow.flags` bit set. Newtype instead of a bare `u16` so the
/// "non-optional secret field" rule (ch05 Rule 6) has one place to enforce:
/// every constructor below takes an explicit `secret: bool`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct ValFlags(pub u16);

impl ValFlags {
    /// The only safe constructor: `secret` cannot be omitted, matching ch05
    /// Rule 6 ("non-optional field") at the type level.
    pub const fn new(secret: bool) -> Self {
        if secret {
            ValFlags(SECRET)
        } else {
            ValFlags(0)
        }
    }

    pub const fn with(self, bit: u16) -> Self {
        ValFlags(self.0 | bit)
    }

    pub const fn without(self, bit: u16) -> Self {
        ValFlags(self.0 & !bit)
    }

    pub const fn has(self, bit: u16) -> bool {
        self.0 & bit != 0
    }

    pub const fn is_secret(self) -> bool {
        self.has(SECRET)
    }

    pub const fn is_scoped(self) -> bool {
        self.has(SCOPED)
    }

    pub const fn is_linear(self) -> bool {
        self.has(LINEAR)
    }

    pub const fn is_secret_unspecified(self) -> bool {
        self.has(SECRET_UNSPECIFIED)
    }

    /// ch05 Rule 6a: "the result of any operation with a secret operand is
    /// secret". Union of every operand's flags gives that for free, since
    /// `SECRET` propagates through OR.
    pub fn union(self, other: ValFlags) -> ValFlags {
        ValFlags(self.0 | other.0)
    }
}

/// `ValRow.ct` sentinel meaning "the textual form omitted `ct=`". `0` is a
/// legal region id (design §3.11: "`0` is a legal region id, not an `Option`
/// sentinel"), so the absent-marker must live outside the legal domain; M1
/// never assigns a real region above `0` (design §3.11), so reserving the
/// top of the `u16` domain for "absent" costs nothing today and leaves
/// `0..=65534` free for M5's real grouping. [decision: `u16::MAX` sentinel
/// for "ct_region omitted", mirroring `SECRET_UNSPECIFIED` above]
pub const CT_UNSPECIFIED: u16 = u16::MAX;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn secret_cannot_be_omitted_from_the_constructor() {
        assert!(ValFlags::new(true).is_secret());
        assert!(!ValFlags::new(false).is_secret());
    }

    #[test]
    fn union_is_or_of_bits() {
        let a = ValFlags::new(true);
        let b = ValFlags::new(false).with(LINEAR);
        assert_eq!(a.union(b).0, SECRET | LINEAR);
    }

    #[test]
    fn unspecified_is_not_secret() {
        let row = ValFlags(SECRET_UNSPECIFIED);
        assert!(!row.is_secret());
        assert!(row.is_secret_unspecified());
    }
}
