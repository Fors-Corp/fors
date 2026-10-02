//! The memos (design §9: "memo values are `Arc<dyn Any>`-free: each query
//! type has its own SoA memo").
//!
//! `fors-query` stores one `u128` per node and the dependency edges; the
//! values live here, in struct-of-arrays columns per query type. Nothing in
//! this module is dynamically typed, nothing is boxed, and a column is
//! indexed by the same `u32` slot the node's `QueryKey` carries.

use std::collections::HashMap;

use fors_diag::Fix;
use fors_index::DeclTable;
use fors_index::diag::Code;
use fors_index::ids::{DefId, FileId};

use super::keys::StableKey;
use crate::Diagnostic;

/// One cached diagnostic, stored declaration-relative (design §9: "cached
/// diagnostics are stored `(DeclKey, offset − decl.range_start, code, site,
/// message)` and rendered at print time"). `offset` is signed because a
/// diagnostic may legitimately point at the declaration's leading trivia.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CachedDiag {
    pub offset: i64,
    pub len: u32,
    pub code: Code,
    pub site: u16,
    pub message: String,
    pub fixes: Vec<Fix>,
}

impl CachedDiag {
    pub fn of(d: &Diagnostic, origin: u32) -> CachedDiag {
        CachedDiag {
            offset: d.start as i64 - origin as i64,
            len: d.end.saturating_sub(d.start),
            code: d.code,
            site: d.site,
            message: d.message.clone(),
            fixes: d.fixes.clone(),
        }
    }

    /// Re-renders against this revision's declaration origin.
    pub fn render(&self, file: FileId, origin: u32) -> Diagnostic {
        let start = (origin as i64 + self.offset).max(0) as u32;
        Diagnostic {
            file,
            start,
            end: start + self.len,
            code: self.code,
            site: self.site,
            message: self.message.clone(),
            fixes: self.fixes.clone(),
        }
    }

    /// The part of this diagnostic that enters a value hash. The message and
    /// the fixes are included: a changed message is a changed answer.
    pub fn hash(&self) -> u128 {
        let mut b = Vec::with_capacity(self.message.len() + 24);
        b.extend_from_slice(&self.offset.to_le_bytes());
        b.extend_from_slice(&self.len.to_le_bytes());
        b.extend_from_slice(self.code.as_string().as_bytes());
        b.extend_from_slice(&self.site.to_le_bytes());
        b.push(0xFF);
        b.extend_from_slice(self.message.as_bytes());
        b.push(0xFF);
        b.extend_from_slice(&(self.fixes.len() as u32).to_le_bytes());
        for f in &self.fixes {
            b.extend_from_slice(f.title.as_bytes());
            b.push(0xFE);
        }
        fors_index::hash_bytes(&b)
    }
}

/// Where a declaration is in the CURRENT revision. Refreshed by
/// `decl_keys(f)` (the file half) and by the signature phase (the `DefId`),
/// because both move when a declaration is inserted.
#[derive(Clone, Copy, Debug)]
pub struct Site {
    pub file: FileId,
    pub decl: u32,
    /// The declaration's CST node.
    pub node: u32,
    /// The byte its first significant token starts at: the origin every
    /// cached diagnostic of this declaration is stored relative to.
    pub origin: u32,
}

/// The per-declaration memo, in `DeclKey` slots. Slots are append-only and
/// never reused, so a node key stays valid for the life of the database.
#[derive(Default)]
pub struct Decls {
    index: HashMap<StableKey, u32>,
    pub key: Vec<StableKey>,
    pub site: Vec<Option<Site>>,
    pub def: Vec<DefId>,
    pub sig_tokens: Vec<u128>,
    pub body_tokens: Vec<u128>,
    pub name_uses: Vec<u128>,
    pub arity: Vec<u128>,
    pub sig_hash: Vec<u128>,
    pub sig_diags: Vec<Vec<CachedDiag>>,
    pub body_diags: Vec<Vec<CachedDiag>>,
    /// The declarations this one's SIGNATURE mentions, as slots.
    pub sig_mentions: Vec<Vec<u32>>,
    /// The declarations this one's BODY read the signature of (its
    /// `DepSet`), as slots.
    pub body_deps: Vec<Vec<u32>>,
    /// The impl buckets this one's body probed, as interned bucket ids.
    pub body_buckets: Vec<Vec<u32>>,
}

impl Decls {
    pub fn slot(&mut self, key: StableKey) -> u32 {
        if let Some(&s) = self.index.get(&key) {
            return s;
        }
        let s = self.key.len() as u32;
        self.key.push(key);
        self.site.push(None);
        self.def.push(fors_fir::NO_DEF);
        self.sig_tokens.push(0);
        self.body_tokens.push(0);
        self.name_uses.push(0);
        self.arity.push(0);
        self.sig_hash.push(0);
        self.sig_diags.push(Vec::new());
        self.body_diags.push(Vec::new());
        self.sig_mentions.push(Vec::new());
        self.body_deps.push(Vec::new());
        self.body_buckets.push(Vec::new());
        self.index.insert(key, s);
        s
    }

    pub fn find(&self, key: StableKey) -> Option<u32> {
        self.index.get(&key).copied()
    }

    pub fn len(&self) -> usize {
        self.key.len()
    }

    pub fn is_empty(&self) -> bool {
        self.key.is_empty()
    }
}

/// Interning families for the node keys that are not a file, a module or a
/// declaration: an impl bucket, a type head, and a `(head, module)` pair.
/// `fors-query`'s `QueryKey` carries two `u32` columns, and these keys are
/// made of 64-bit stable identities, so they are interned to a `u32` slot
/// that is itself stable (append-only).
pub mod fam {
    pub const MODULE: u16 = 0;
    pub const HEAD: u16 = 1;
    pub const BUCKET: u16 = 2;
    pub const CANDIDATE: u16 = 3;
}

#[derive(Default)]
pub struct Ids {
    map: HashMap<(u16, u64, u64), u32>,
    rows: Vec<(u16, u64, u64)>,
}

impl Ids {
    pub fn intern(&mut self, family: u16, a: u64, b: u64) -> u32 {
        let k = (family, a, b);
        if let Some(&id) = self.map.get(&k) {
            return id;
        }
        let id = self.rows.len() as u32;
        self.rows.push(k);
        self.map.insert(k, id);
        id
    }

    pub fn find(&self, family: u16, a: u64, b: u64) -> Option<u32> {
        self.map.get(&(family, a, b)).copied()
    }

    pub fn row(&self, id: u32) -> (u16, u64, u64) {
        self.rows[id as usize]
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}

/// Everything the Fors query set memoises.
#[derive(Default)]
pub struct Memo {
    // ---- per file
    pub decls: Vec<Option<DeclTable>>,
    /// `decl_keys(f)`: a stable key per `DeclId`, and the slots of the
    /// declarations this file currently owns (so a re-execution can clear
    /// the ones it no longer has).
    pub file_keys: Vec<Vec<StableKey>>,
    pub file_slots: Vec<Vec<u32>>,
    // ---- per declaration
    pub decl: Decls,
    // ---- interned composite keys
    pub ids: Ids,
    /// The diagnostics the signature phase emitted that fall inside no
    /// declaration at all (`loose_diags()`).
    pub loose: Vec<Diagnostic>,
    /// R14's verdicts, owned by the whole-build `infinite_size()` node rather
    /// than by the declaration they point at: the declaration whose cycle is
    /// broken by an edit ELSEWHERE in the cycle stays green, so a diagnostic
    /// cached on it would outlive the cycle. `(slot, diagnostic)`, rendered
    /// at print time against the slot's current site.
    pub infinite: Vec<(u32, CachedDiag)>,
}

impl Memo {
    pub fn grow_files(&mut self, n: usize) {
        while self.decls.len() < n {
            self.decls.push(None);
            self.file_keys.push(Vec::new());
            self.file_slots.push(Vec::new());
        }
    }
}
