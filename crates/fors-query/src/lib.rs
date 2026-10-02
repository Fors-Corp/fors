//! `fors-query`: the content-hash query DAG engine (design
//! `docs/design/type-checker.md` §4.3, §9). Depends on `std` only — the
//! engine (`key.rs`, `db.rs`, `cycle.rs`, `stats.rs`) is reusable and is
//! tested here with synthetic queries; the Fors-specific query set
//! (wrapping `resolve()` and `fors-check`'s per-declaration checks) lives in
//! `fors_check::queries` instead, so this crate never depends on
//! `fors-index`/`fors-resolve`/`fors-check`.
//!
//! Increment I9 (§13) built it: `QueryKey`, `Revision`, input versus derived
//! values with a value hash, dependency recording, red-green verification
//! with early cutoff, an explicit in-flight stack for cycle detection with a
//! caller-declared `on_cycle` recovery value, cancellation that writes
//! nothing, and `--stats`. [`fingerprint::decl_fingerprint`] is
//! `docs/PLAN.md` §5's learning-mode contribution point and lives here, as
//! the plan names it.
//!
//! The engine stores one `u128` per node and nothing else: a query's *value*
//! stays in the query set's own struct-of-arrays memo, keyed by the same
//! [`QueryKey`]. There is no `Arc<dyn Any>` in this crate, and no trait
//! object is used for a value — only for the query set itself, once per
//! execution.
//!
//! ```
//! use fors_query::{Db, Outcome, Queries, QueryKey, ValueHash, Cycle};
//!
//! struct Doubler { memo: Vec<u64> }
//! impl Queries for Doubler {
//!     fn compute(&mut self, db: &mut Db, key: QueryKey) -> Outcome {
//!         let v = match db.read(self, QueryKey::one(0, key.a)) {
//!             Ok(v) => v as u64,
//!             Err(_) => return Outcome::Cancelled,
//!         };
//!         if self.memo.len() <= key.a as usize { self.memo.resize(key.a as usize + 1, 0) }
//!         self.memo[key.a as usize] = v * 2;
//!         Outcome::Value((v * 2) as ValueHash)
//!     }
//!     fn on_cycle(&mut self, _k: QueryKey, _c: &Cycle) -> ValueHash { 0 }
//! }
//!
//! let mut db = Db::new();
//! let mut q = Doubler { memo: Vec::new() };
//! db.set_input(QueryKey::one(0, 0), 21);
//! assert_eq!(db.demand(&mut q, QueryKey::one(1, 0)), Ok(42));
//! ```

#![deny(unsafe_code)]

pub mod cycle;
pub mod db;
pub mod fingerprint;
pub mod key;
pub mod stats;

pub use cycle::{Cancelled, Cycle};
pub use db::{Answer, CancelFlag, Db, Outcome, Queries};
pub use fingerprint::{DeclFingerprint, DeclHashes, decl_fingerprint, mix, mix_all, splitmix64};
pub use key::{QueryKey, Revision, ValueHash};
pub use stats::Stats;
