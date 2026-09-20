//! `fors-query`: the content-hash query DAG engine (design
//! `docs/design/type-checker.md` §4.3, §9). Depends on `std` only — the
//! engine (`key.rs`, `db.rs`, `cycle.rs`, `stats.rs`) is meant to be
//! reusable and testable with synthetic queries; the Fors-specific query
//! set (wrapping `resolve()`, `fors-check`'s per-declaration checks,
//! `decl_fingerprint`) lives in `fors_check::queries` instead, so this
//! crate never depends on `fors-index`/`fors-resolve`/`fors-check`.
//!
//! Empty in increment I0 (§13: "query engine: real but late", §3 fork
//! 14): the engine itself is I9's. This crate exists now, with no
//! dependencies to get wrong later, so `docs/PLAN.md`'s mention of
//! `fors_query::decl_fingerprint()` as a learning-mode contribution point
//! has a crate to land in when I9 builds it.

#![deny(unsafe_code)]
