//! `DeclFmir` (design §3.1): "One declaration's FMIR. Self-contained: every
//! index is relative to this struct's own pools, so a `DeclFmir` is
//! content-hashable and movable between processes without fixups."
//!
//! [decision: `operands` and the `calls`/`reduces`/`switches`/`switch_arms`/
//! `arg_convs` side tables the design does not separately enumerate all live
//! inside [`InstPool`] rather than as DeclFmir-level sibling fields — they
//! are all instruction-spill data sharing the instruction pool's lifecycle.
//! The properties §3.1 actually cares about (u32-indexed SoA pools, no host
//! pointers, deterministic iteration, per-declaration self-containment,
//! content-hashability) hold exactly the same either way; only the Rust
//! field *nesting* differs from §3.1's flat listing]

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;

use crate::alias::AliasSeed;
use crate::block::BlockPool;
use crate::constpool::ConstPool;
use crate::ids::BlockId;
use crate::inst::InstPool;
use crate::place::PlacePool;
use crate::region::RegionPool;
use crate::scope::{PlaceListPool, ScopePool};
use crate::site::SitePool;

/// One declaration's FMIR body.
#[derive(Clone, Debug)]
pub struct DeclFmir {
    pub decl: DeclKeyId,
    pub sig: FnSigId,
    pub vals: crate::value::ValPool,
    pub blocks: BlockPool,
    pub insts: InstPool,
    pub scopes: ScopePool,
    pub places: PlacePool,
    pub regions: RegionPool,
    pub sites: SitePool,
    pub consts: ConstPool,
    /// `ScopeRow.obligations` ranges resolve here (design §3.5).
    pub obligations: PlaceListPool,
    /// A `SCOPED` value's `sources` ranges resolve here (design §3.4).
    pub scoped_sources: PlaceListPool,
    pub defers: crate::scope::DeferPool,
    /// The declaration's entry block. Not named as a separate field by
    /// design §3.1 (which is silent on how a `DeclFmir` records its entry
    /// point at all), but a CFG needs one to define reachability, dominance
    /// (ch05 Rule 11) and a canonical block-numbering traversal for
    /// `fmir_hash` (design §9's "invariant under block renumbering").
    /// [decision: `entry: BlockId`, invented — not named by §3.1]
    pub entry: BlockId,
    /// Does this declaration carry `@unsafe(invariant: "...")`? `declassify`
    /// is only legal "inside a declaration carrying `@unsafe(invariant:)`"
    /// (design §3.11, ch05 Rule 6a) — a decl-level fact FMIR has nowhere
    /// else to record. [decision: `is_unsafe_invariant: bool`, invented —
    /// the design does not say where this fact lives on `DeclFmir`, only
    /// that the verifier must be able to see it]
    pub is_unsafe_invariant: bool,
    /// blake3 in the design's prose (design §3.1's own doc comment: "blake3
    /// of the canonical encoding"); this workspace's one actual hash
    /// primitive is `fors_index::fingerprint`'s hand-rolled FNV-128 +
    /// SplitMix64 (that module's own comment: "design §14 Q2 keeps FNV-128 +
    /// SplitMix64 rather than the PLAN's BLAKE3" — one hash function for the
    /// whole compiler, and zero dependencies rules out a real BLAKE3
    /// implementation or crate). `encode::fingerprint` computes this with
    /// that primitive; `fmir_hash` (§9's gate name) is the same value.
    /// [decision: "blake3" in the design's prose means "this workspace's
    /// established content-hash primitive", i.e.
    /// `fors_index::fingerprint::hash_bytes`, not literal BLAKE3]
    pub fingerprint: u128,
}

impl DeclFmir {
    /// A minimal, already-`verify()`-clean declaration: one block, no
    /// values, terminated `unreachable`. Every test and the builder both
    /// start here rather than hand-assembling all twelve pools each time.
    pub fn empty(decl: DeclKeyId, sig: FnSigId) -> Self {
        let mut blocks = BlockPool::new();
        let scope = {
            let mut scopes = ScopePool::new();
            let root = scopes.push(crate::scope::ScopeRow::root(crate::ids::BrandId::NONE));
            debug_assert_eq!(root.0, 0);
            scopes
        };
        let entry = blocks.push(crate::block::BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: crate::inst::InstRow {
                op: crate::op::Op::Unreachable,
                a: crate::op::NO_OPERAND,
                b: crate::op::NO_OPERAND,
                c: crate::op::NO_OPERAND,
                ty: fors_fir::ty::TY_UNIT,
                site: crate::ids::SiteId(0),
            },
            scope: crate::ids::ScopeId(0),
        });
        let mut sites = SitePool::new();
        sites.push(crate::site::SiteRow { line: 0, col: 0 });
        DeclFmir {
            decl,
            sig,
            vals: crate::value::ValPool::new(),
            blocks,
            insts: InstPool::new(),
            scopes: scope,
            places: PlacePool::new(),
            regions: RegionPool::new(),
            sites,
            consts: ConstPool::new(),
            obligations: PlaceListPool::new(),
            scoped_sources: PlaceListPool::new(),
            defers: crate::scope::DeferPool::new(),
            entry,
            is_unsafe_invariant: false,
            fingerprint: 0,
        }
    }

    /// A memory-producing instruction with `AliasSeed::None` — design §3.4a /
    /// ch05 Rule 5's "the verifier checks only that every memory-producing
    /// instruction has a seed row".
    pub fn first_missing_alias_seed(&self) -> Option<crate::ids::InstId> {
        let ops: Vec<_> = self.insts.all_rows().map(|(_, r)| r.op).collect();
        self.insts
            .aliases
            .missing(&ops)
            .map(|i| crate::ids::InstId(i as u32))
    }

    pub fn push_val(&mut self, row: crate::value::ValRow) -> crate::ids::ValId {
        self.vals.push(row)
    }

    pub fn push_inst(&mut self, row: crate::inst::InstRow, seed: AliasSeed) -> crate::ids::InstId {
        self.insts.push(row, seed)
    }
}
