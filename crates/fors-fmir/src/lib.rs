//! `fors-fmir`: the FMIR data model, canonical encoding, textual dump/parse
//! and structural verifier (design `docs/design/fmir-interpreter.md`,
//! increment F0 — "CHECKER DEPENDENCY: none... the one increment that can be
//! handed to an implementer today"). This crate reads no checker output: it
//! depends only on `fors-index` (ids, `Symbol`, the content-hash primitive)
//! and `fors-fir` (`TyId`, `DeclKeyId`, `FnSigId`) — see
//! `tests/no_checker_dependency.rs`.
//!
//! Module map:
//! - [`ids`] — every `u32` id newtype this crate's own pools use.
//! - [`flags`] — `ValRow.flags`'s bit set, plus the `?`/`ct=?` "textually
//!   absent" sentinels ch05 Rule 6's negative corpus needs.
//! - [`op`] — the 71-opcode [`op::Op`] enum and its classifications.
//! - [`value`], [`place`], [`alias`], [`region`], [`scope`], [`site`],
//!   [`constpool`], [`inst`], [`block`] — the pools design §3 names.
//! - [`decl`] — [`decl::DeclFmir`], one declaration's self-contained body.
//! - [`encode`] — canonical byte encoding, decoding, and [`encode::fmir_hash`].
//! - [`dump`] / [`parse`] — the textual form (see `dump.rs`'s module docs
//!   for its scope).
//! - [`verify`] — the structural verifier, [`verify::verify`].
//! - [`diag`] — [`diag::Diagnostic`], `verify()`'s output type.

pub mod alias;
pub mod block;
pub mod constpool;
pub mod decl;
pub mod diag;
pub mod dump;
pub mod encode;
pub mod flags;
pub mod ids;
pub mod inst;
pub mod op;
pub mod parse;
pub mod place;
pub mod region;
pub mod scope;
pub mod site;
pub mod value;
pub mod verify;

#[cfg(test)]
mod tests {
    use crate::decl::DeclFmir;
    use fors_fir::defpath::DeclKeyId;
    use fors_fir::sig::FnSigId;

    /// The one end-to-end smoke test living at the crate root: build, hash,
    /// encode, decode, dump and parse the same trivial declaration, and
    /// confirm every stage agrees with `verify()`. Every deeper case for
    /// each stage lives in that stage's own module (`verify.rs`, `encode.rs`)
    /// or in `tests/`.
    #[test]
    fn empty_decl_is_ok_hashes_encodes_and_dumps() {
        let decl = DeclFmir::empty(DeclKeyId(1), FnSigId(1));
        assert!(crate::verify::is_ok(&decl));
        let _hash = crate::encode::fmir_hash(&decl);
        let bytes = crate::encode::to_bytes(&decl);
        let decoded = crate::encode::from_bytes(&bytes).expect("decode");
        assert!(crate::verify::is_ok(&decoded));
        let text = crate::dump::dump(&decl);
        let reparsed = crate::parse::parse(&text).expect("parse");
        assert!(crate::verify::is_ok(&reparsed));
    }
}
