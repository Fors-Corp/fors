//! The Fors query set: design §9.1's node set over the existing passes, and
//! the M1 exit gate's machinery (`docs/PLAN.md` M1 (a), (b), (c)).
//!
//! `fors-query` is the engine and knows nothing about Fors; this module is
//! the other half — the nodes, their in-edges, their value hashes, the
//! declaration-relative cached diagnostics and the printing walk.
//!
//! # Granularity, honestly
//!
//! Design §13's I9 and §3 fork 14 allow the whole-build passes to be wrapped
//! as nodes in M1. Three of the nodes below are whole-build and are named as
//! such everywhere they appear, because reporting a coarse node as a fine one
//! is the one thing that would make the gate numbers a lie:
//!
//! - **`resolve_build()`** wraps `fors_resolve::resolve`, which is whole-build
//!   by §3 fork 14 ("`resolve()` stays whole-build in M1; per-module
//!   incremental resolution is M2"). It re-executes on every edit.
//! - **`signature_phase()`** wraps `fors_check::check_signatures` — lowering,
//!   whole-head well-formedness and the freeze. `fors-check` cannot lower one
//!   declaration's signature without the `DefTable` and `Fir` of the whole
//!   build, and carving that apart is a restructuring, not an increment. It
//!   re-executes on every edit. Both of these run *eagerly*, before the
//!   nodes that read their output, so the per-declaration nodes can be
//!   verified against their own fine-grained inputs rather than against a
//!   whole-build value that always changes.
//! - **`infinite_size()`** is whole-build *by design* (§9.1: "the one
//!   whole-build query, as R14 asks").
//!
//! What that buys, and what it does not: `parse(f)` and `decl_index(f)` are
//! genuinely per-file and are skipped for a file whose bytes did not change;
//! every per-declaration node is a real node with the in-edges §9.1 gives it,
//! verified by the red-green walk; and `check_body(k)` is executed for
//! exactly the declarations the walk found red, which is what makes an
//! incremental re-check cost one body instead of ten thousand. The two
//! whole-build passes above are not avoided in M1, and the slope measurement
//! reports their share separately so the number cannot be read as more than
//! it is.
//!
//! Named as coarser than §9.1 asks, each with the reason:
//!
//! - `name_uses(k)` is a per-declaration node, but its *value* is a slice of
//!   the whole-build `resolve` (§3 fork 14 allows exactly this), so it
//!   re-executes for every declaration on every edit and relies on the early
//!   cutoff to stop there.
//! - `signature_of(k)`'s in-edges are its own signature tokens, its
//!   `name_uses`, the `decl_arity` of the items its signature mentions, its
//!   container's `signature_of`, its members' signature tokens, and — found
//!   by I9's verification pass, each with the stale diagnostic it would
//!   otherwise have left — for an impl: the `impl_heads` of its own module
//!   and its head's (overlap, prerequisites, member clashes), the
//!   `signature_of` of the trait it implements (T0017 completeness and
//!   conformance), and the `impls_for` of every bucket its whole-head checks
//!   probed (`Wf::wf_scope`; `impl Copyable for W` asking about a field's
//!   type). §9.1's "`assoc_defs` for projections in its own types" is the
//!   container edge: a projection a signature can write is `Self.A` (its
//!   own container's) or `T.A` on a parameter (never normalised through an
//!   impl); a concrete `Rec.A` is rejected (T0061) and there are no
//!   supertraits, so no other impl can be reached from a signature.
//! - `infinite_size()` owns R14's diagnostics (`Memo::infinite`): the
//!   declaration one points at stays green when the edit that broke its
//!   cycle was elsewhere in the cycle.
//! - `check_body(k)`'s `members_of` and `candidate_traits` in-edges are
//!   *derived* from the impl-bucket probes the body recorded (every member
//!   lookup probes the receiver head's bucket first), not recorded
//!   separately.
//!
//! # The oracle
//!
//! Because the whole-build signature phase runs on every revision anyway, the
//! query set can compare every value it decided not to recompute against the
//! value the fresh phase would have produced. [`QueryBuild::set_paranoid`]
//! turns that on; the incremental test suite runs with it on, so a missing
//! in-edge is a test failure rather than a stale accept.

pub mod keys;
pub mod memo;

use std::collections::HashMap;

use fors_fir::defpath::HeadKey;
use fors_index::ids::{DefId, FileId, ModuleId};
use fors_index::{Interner, Segments};
use fors_query::{
    Cancelled, Cycle, Db, Outcome, Queries, QueryKey, Stats, ValueHash, mix, mix_all,
};
use fors_resolve::target::{Entity, ResolvedTarget};
use fors_resolve::{FileInput, ResolveOutput};
use fors_syntax::NodeKind;

use crate::diag::sort_diagnostics;
use crate::{Bodies, BodyPhase, Diagnostic, Signatures};
use keys::StableKey;
use memo::{CachedDiag, Memo, Site, fam};

/// Design §9.1's node set, one constant per row, plus the three wrappers the
/// module docs name. The numbers are the `QueryKey::kind` column and are
/// append-only: a `--stats` line is read by a human and by CI.
pub mod kind {
    pub const SOURCE_TEXT: u16 = 0;
    pub const FILE_SET: u16 = 1;
    pub const PARSE: u16 = 2;
    pub const DECL_INDEX: u16 = 3;
    pub const MODULE_FACTS: u16 = 4;
    pub const DECL_KEYS: u16 = 5;
    pub const MODULE_GRAPH: u16 = 6;
    pub const MODULE_EXPORTS: u16 = 7;
    pub const RESOLVE_BUILD: u16 = 8;
    pub const SIGNATURE_PHASE: u16 = 9;
    pub const DECL_SIG_TOKENS: u16 = 10;
    pub const DECL_BODY_TOKENS: u16 = 11;
    pub const NAME_USES: u16 = 12;
    pub const DECL_ARITY: u16 = 13;
    pub const SIGNATURE_OF: u16 = 14;
    pub const IMPL_HEADS: u16 = 15;
    pub const IMPLS_FOR: u16 = 16;
    pub const OVERLAP_CHECK: u16 = 17;
    pub const MEMBERS_OF: u16 = 18;
    pub const CANDIDATE_TRAITS: u16 = 19;
    pub const SIZE_EDGES: u16 = 20;
    pub const INFINITE_SIZE: u16 = 21;
    pub const CHECK_BODY: u16 = 22;
    pub const LOOSE_DIAGS: u16 = 23;
    pub const COUNT: usize = 24;

    /// Whether `QueryKey::a` of this kind is a declaration slot.
    pub fn is_per_declaration(kind: u16) -> bool {
        matches!(
            kind,
            DECL_SIG_TOKENS
                | DECL_BODY_TOKENS
                | NAME_USES
                | DECL_ARITY
                | SIGNATURE_OF
                | SIZE_EDGES
                | CHECK_BODY
        )
    }

    pub const NAMES: [&str; COUNT] = [
        "source_text",
        "file_set",
        "parse",
        "decl_index",
        "module_facts",
        "decl_keys",
        "module_graph",
        "module_exports",
        "resolve_build",
        "signature_phase",
        "decl_sig_tokens",
        "decl_body_tokens",
        "name_uses",
        "decl_arity",
        "signature_of",
        "impl_heads",
        "impls_for",
        "overlap_check",
        "members_of",
        "candidate_traits",
        "size_edges",
        "infinite_size",
        "check_body",
        "loose_diags",
    ];
}

/// A prelude row has no file and no declaration, so it gets a synthetic
/// stable identity: a fold of its `DefId`, which IS stable because
/// `prelude::build` runs first and in a fixed order every revision.
///
/// MARC: this is deliberately NOT a tag bit. A stable key is a 64-bit hash,
/// so half of all real keys have any given bit set; an earlier draft used the
/// top bit as "this is a prelude row" and silently dropped every
/// `signature_of` in-edge whose key happened to have it, which the private-
/// signature edit class caught. Whether a row is the prelude's is decided by
/// `DefTable::first_user`, never by looking at a hash.
fn prelude_identity(def: DefId) -> u64 {
    let mut b = [0u8; 5];
    b[0] = 0xFE;
    b[1..].copy_from_slice(&def.0.to_le_bytes());
    fors_index::hash_bytes(&b) as u64
}

/// One file of the build.
pub struct FileEntry {
    pub path: String,
    pub module: Segments,
    pub source: Vec<u8>,
    /// False once the file is removed from the build; its slot is kept so
    /// `FileId`s never renumber.
    pub live: bool,
}

/// The incremental Fors build: the engine, the inputs, and the memos.
pub struct QueryBuild {
    db: Db,
    interner: Interner,
    files: Vec<FileEntry>,
    parses: Vec<Option<fors_syntax::Parse>>,
    memo: Memo,
    root: Option<usize>,
    package: Option<Vec<u8>>,
    paranoid: bool,
    /// What the last [`QueryBuild::recheck`] did, for `--stats`.
    last_stats: Stats,
    /// Set by the oracle check; a non-empty list is a missing in-edge.
    oracle_failures: Vec<String>,
}

impl Default for QueryBuild {
    fn default() -> QueryBuild {
        QueryBuild::new()
    }
}

impl QueryBuild {
    pub fn new() -> QueryBuild {
        QueryBuild {
            db: Db::new(),
            interner: Interner::new(),
            files: Vec::new(),
            parses: Vec::new(),
            memo: Memo::default(),
            root: None,
            package: None,
            paranoid: false,
            last_stats: Stats::default(),
            oracle_failures: Vec::new(),
        }
    }

    /// Turns on the oracle: after a re-check, every value the engine decided
    /// not to recompute is compared against what the fresh whole-build
    /// signature phase would have produced. Slow; on in the gate tests.
    pub fn set_paranoid(&mut self, on: bool) {
        self.paranoid = on;
    }

    pub fn set_package(&mut self, name: Option<Vec<u8>>) {
        self.package = name;
    }

    pub fn set_root(&mut self, root: Option<usize>) {
        self.root = root;
    }

    pub fn interner(&self) -> &Interner {
        &self.interner
    }

    pub fn interner_mut(&mut self) -> &mut Interner {
        &mut self.interner
    }

    pub fn file_path(&self, file: FileId) -> &str {
        &self.files[file.index()].path
    }

    pub fn files(&self) -> &[FileEntry] {
        &self.files
    }

    pub fn source(&self, file: FileId) -> &[u8] {
        &self.files[file.index()].source
    }

    /// Adds a file. `module` is its canonical module name (ch08 R1), which
    /// only the caller can derive.
    pub fn add_file(&mut self, path: &str, module: Segments, source: Vec<u8>) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(FileEntry {
            path: path.to_string(),
            module,
            source,
            live: true,
        });
        self.parses.push(None);
        self.memo.grow_files(self.files.len());
        id
    }

    /// Replaces a file's bytes. The next [`QueryBuild::recheck`] re-parses
    /// this file and no other.
    pub fn edit_file(&mut self, file: FileId, source: Vec<u8>) {
        self.files[file.index()].source = source;
    }

    pub fn remove_file(&mut self, file: FileId) {
        self.files[file.index()].live = false;
        self.files[file.index()].source = Vec::new();
    }

    pub fn cancel_flag(&self) -> fors_query::CancelFlag {
        self.db.cancel_flag()
    }

    pub fn revision(&self) -> fors_query::Revision {
        self.db.revision()
    }

    /// Opens a counting window for the M1 gate (c) assertions.
    pub fn open_window(&mut self) {
        self.db.open_window();
    }

    /// The stable declaration keys of one kind executed since
    /// [`QueryBuild::open_window`], sorted.
    pub fn executed_decls(&self, kind: u16) -> Vec<StableKey> {
        // Only a per-declaration kind has a slot in `k.a`; for a file, module
        // or bucket kind this is the empty list rather than an index panic.
        let mut v: Vec<StableKey> = self
            .db
            .executed_of_kind(kind)
            .iter()
            .filter(|_| kind::is_per_declaration(kind))
            .filter_map(|k| self.memo.decl.key.get(k.a as usize).copied())
            .collect();
        v.sort_unstable();
        v.dedup();
        v
    }

    /// Whether a query kind executed at all since the window opened.
    pub fn executed_count(&self, kind: u16) -> usize {
        self.db.executed_of_kind(kind).len()
    }

    pub fn executed_keys(&self) -> &[QueryKey] {
        self.db.executed_keys()
    }

    pub fn stats(&self) -> Stats {
        self.db.stats()
    }

    pub fn last_stats(&self) -> &Stats {
        &self.last_stats
    }

    pub fn oracle_failures(&self) -> &[String] {
        &self.oracle_failures
    }

    /// The stable key of the declaration named `name` in `file`, for tests.
    pub fn decl_key(&self, file: FileId, name: &str) -> Option<StableKey> {
        let decls = self.memo.decls[file.index()].as_ref()?;
        let sym = self.interner.get(name.as_bytes())?;
        (0..decls.len())
            .find(|&d| decls.name[d] == Some(sym))
            .map(|d| self.memo.file_keys[file.index()][d])
    }

    /// Every stable key of `file`, in declaration order.
    pub fn decl_keys_of(&self, file: FileId) -> &[StableKey] {
        &self.memo.file_keys[file.index()]
    }

    /// Diagnosis only: the cached `sig_hash` of a declaration.
    pub fn sig_hash_of(&self, key: StableKey) -> Option<u128> {
        let slot = self.memo.decl.find(key)?;
        Some(self.memo.decl.sig_hash[slot as usize])
    }

    /// Diagnosis only: the dependency edges one node recorded.
    pub fn debug_deps(&self, k: u16, key: StableKey) -> Vec<(&'static str, Option<String>)> {
        let Some(slot) = self.memo.decl.find(key) else {
            return Vec::new();
        };
        self.db
            .deps_of(QueryKey::one(k, slot))
            .into_iter()
            .map(|d| {
                (
                    kind::NAMES[d.kind as usize],
                    self.memo
                        .decl
                        .key
                        .get(d.a as usize)
                        .and_then(|&kk| self.decl_name(kk)),
                )
            })
            .collect()
    }

    /// Diagnosis only: the dependency edges of one node whose value changed
    /// in the CURRENT revision — the edges that made the node red.
    pub fn debug_changed_deps(
        &self,
        k: u16,
        key: StableKey,
    ) -> Vec<(&'static str, Option<String>)> {
        let Some(slot) = self.memo.decl.find(key) else {
            return Vec::new();
        };
        let now = self.db.revision();
        self.db
            .deps_of(QueryKey::one(k, slot))
            .into_iter()
            .filter(|d| self.db.changed_at(*d) == Some(now))
            .map(|d| {
                let name = if kind::is_per_declaration(d.kind) {
                    self.memo
                        .decl
                        .key
                        .get(d.a as usize)
                        .and_then(|&kk| self.decl_name(kk))
                } else {
                    Some(format!("#{}", d.a))
                };
                (kind::NAMES[d.kind as usize], name)
            })
            .collect()
    }

    /// Diagnosis only: an interned composite key (`fam`) as text, with the
    /// trait's name when its stable key is a declaration of this build.
    pub fn debug_composite(&self, id: u32) -> String {
        let (family, a, b) = self.memo.ids.row(id);
        let name = |k: u64| -> String {
            self.memo
                .decl
                .find(k)
                .and_then(|_| self.decl_name(k))
                .unwrap_or_else(|| format!("{k:#018x}"))
        };
        match family {
            fam::MODULE => format!("module {a:#018x}/{b}"),
            fam::HEAD => format!("head {a:#018x}"),
            fam::BUCKET => format!("bucket ({}, head {b:#018x})", name(a)),
            fam::CANDIDATE => format!("candidates (head {a:#018x}, module {b:#018x})"),
            _ => format!("?{family} {a} {b}"),
        }
    }

    /// The name a stable key belongs to, for a test's assertion message.
    /// `None` once the declaration has left the build.
    pub fn decl_name(&self, key: StableKey) -> Option<String> {
        let slot = self.memo.decl.find(key)?;
        let site = self.memo.decl.site[slot as usize]?;
        let decls = self.memo.decls[site.file.index()].as_ref()?;
        if let Some(name) = decls.name[site.decl as usize] {
            return Some(String::from_utf8_lossy(self.interner.resolve(name)).into_owned());
        }
        // An `impl` has no name; its header reads better in an assertion than
        // a 64-bit key does.
        let src = &self.files[site.file.index()].source;
        let head = src[site.origin as usize..]
            .iter()
            .position(|&b| b == b'{')
            .map(|n| &src[site.origin as usize..site.origin as usize + n])
            .unwrap_or(&src[site.origin as usize..]);
        Some(
            String::from_utf8_lossy(head)
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "),
        )
    }

    /// The names of the declarations one query kind executed since
    /// [`QueryBuild::open_window`], sorted and deduplicated. The M1 gate (c)
    /// assertions read this, so a failure names declarations rather than
    /// 64-bit keys.
    pub fn executed_names(&self, kind: u16) -> Vec<String> {
        let mut v: Vec<String> = self
            .executed_decls(kind)
            .into_iter()
            .map(|k| {
                self.decl_name(k)
                    .unwrap_or_else(|| format!("<gone {k:#018x}>"))
            })
            .collect();
        v.sort();
        v.dedup();
        v
    }
}

// ---------------------------------------------------------------- stage A

/// The per-file half of the DAG: everything computable from the bytes alone.
struct StageA<'x> {
    files: &'x [FileEntry],
    parses: &'x mut Vec<Option<fors_syntax::Parse>>,
    interner: &'x mut Interner,
    memo: &'x mut Memo,
}

impl Queries for StageA<'_> {
    fn on_cycle(&mut self, _key: QueryKey, _c: &Cycle) -> ValueHash {
        0
    }

    fn compute(&mut self, db: &mut Db, key: QueryKey) -> Outcome {
        let f = key.a as usize;
        match key.kind {
            kind::PARSE => {
                if db
                    .read(self, QueryKey::one(kind::SOURCE_TEXT, key.a))
                    .is_err()
                {
                    return Outcome::Cancelled;
                }
                let StageA { files, parses, .. } = &mut *self;
                let entry = &files[f];
                // Every file is parsed, even an emptied one: a `FileId` never
                // renumbers, so a removed file is an empty module rather than
                // a hole in the index.
                let p = fors_syntax::parse_file(&entry.source);
                // Hashed from the significant tokens and the tree's SHAPE, so
                // a comment or whitespace edit really is green here and not
                // merely at `decl_index` (design §9.2's first row).
                let tokens =
                    fors_index::hash_tokens(&p.tokens, &entry.source, 0, p.tokens.len() as u32);
                let mut shape: Vec<u8> = Vec::with_capacity(p.tree.kinds.len() * 5);
                for (i, k) in p.tree.kinds.iter().enumerate() {
                    shape.push(*k as u8);
                    shape.extend_from_slice(&p.tree.subtree_len[i].to_le_bytes());
                }
                let mut v = mix(mix(1, tokens), fors_index::hash_bytes(&shape));
                for d in &p.diags {
                    v = mix(v, fors_index::hash_bytes(d.code.as_str().as_bytes()));
                }
                parses[f] = Some(p);
                Outcome::Value(v)
            }
            kind::MODULE_FACTS => {
                if db.read(self, QueryKey::one(kind::PARSE, key.a)).is_err() {
                    return Outcome::Cancelled;
                }
                let Some(p) = self.parses[f].as_ref() else {
                    return Outcome::Value(0);
                };
                let src = &self.files[f].source;
                let mut parts: Vec<u128> = Vec::new();
                for c in p.tree.children(0) {
                    if matches!(p.tree.kinds[c], NodeKind::ModuleHdr | NodeKind::UseDecl) {
                        let (a, b) = p.tree.token_range(c);
                        parts.push(mix(
                            p.tree.kinds[c] as u128,
                            fors_index::hash_tokens(&p.tokens, src, a, b),
                        ));
                    }
                }
                // The header is positional, the `use` list is not: sorting
                // makes reordering two imports a green edit.
                let header = parts.first().copied().unwrap_or(0);
                let mut rest: Vec<u128> = parts.into_iter().skip(1).collect();
                rest.sort_unstable();
                Outcome::Value(mix_all(mix(2, header), rest))
            }
            kind::DECL_INDEX => {
                if db.read(self, QueryKey::one(kind::PARSE, key.a)).is_err() {
                    return Outcome::Cancelled;
                }
                let StageA {
                    files,
                    parses,
                    interner,
                    memo,
                } = &mut *self;
                let Some(p) = parses[f].as_ref() else {
                    memo.decls[f] = None;
                    return Outcome::Value(0);
                };
                let src = &files[f].source;
                let t = fors_index::build_decl_table(&p.tree, &p.tokens, src, interner);
                // Positionless: the kind, the name, the visibility, the two
                // token fingerprints and the PARENT'S kind and name. A row
                // index would renumber on insertion and wake every row.
                let mut v: ValueHash = 3;
                for d in 0..t.len() {
                    let mut b: Vec<u8> = Vec::with_capacity(48);
                    b.push(t.kind[d] as u8);
                    b.push(t.vis[d] as u8);
                    b.push(t.modifiers[d]);
                    match t.name[d] {
                        Some(s) => b.extend_from_slice(interner.resolve(s)),
                        None => b.push(0),
                    }
                    b.push(0xFF);
                    let parent = t.parent[d];
                    if parent != fors_index::decl::NO_PARENT {
                        b.push(t.kind[parent as usize] as u8);
                        if let Some(s) = t.name[parent as usize] {
                            b.extend_from_slice(interner.resolve(s));
                        }
                    }
                    b.push(0xFF);
                    b.extend_from_slice(&t.sig_hash[d].to_le_bytes());
                    b.extend_from_slice(&t.body_hash[d].to_le_bytes());
                    for a in t.attr_start[d]..t.attr_end[d] {
                        b.extend_from_slice(interner.resolve(t.attr_names[a as usize]));
                        b.push(0xFE);
                    }
                    v = mix(v, fors_index::hash_bytes(&b));
                }
                memo.decls[f] = Some(t);
                Outcome::Value(v)
            }
            kind::DECL_KEYS => {
                if db
                    .read(self, QueryKey::one(kind::DECL_INDEX, key.a))
                    .is_err()
                {
                    return Outcome::Cancelled;
                }
                // Drop the sites this file used to own: a declaration it no
                // longer has must not be printed from a stale origin.
                let StageA {
                    files,
                    parses,
                    interner,
                    memo,
                } = &mut *self;
                for &s in &memo.file_slots[f] {
                    memo.decl.site[s as usize] = None;
                }
                let Some(p) = parses[f].as_ref() else {
                    memo.file_keys[f] = Vec::new();
                    memo.file_slots[f] = Vec::new();
                    return Outcome::Value(0);
                };
                let ks = {
                    let decls = memo.decls[f].as_ref().expect("decl_index ran first");
                    keys::file_decl_keys(
                        &files[f].module,
                        decls,
                        &p.tree,
                        &p.tokens,
                        &files[f].source,
                        interner,
                    )
                };
                let nodes: Vec<u32> = memo.decls[f]
                    .as_ref()
                    .map(|d| d.node.clone())
                    .unwrap_or_default();
                let mut slots = Vec::with_capacity(ks.len());
                for (d, &k) in ks.iter().enumerate() {
                    let slot = memo.decl.slot(k);
                    let node = nodes[d];
                    memo.decl.site[slot as usize] = Some(Site {
                        file: FileId(f as u32),
                        decl: d as u32,
                        node,
                        origin: keys::decl_origin(&p.tree, &p.tokens, node),
                    });
                    slots.push(slot);
                }
                // §9.1: "changes only when the SET of declarations changes",
                // so the fold is over the SORTED keys.
                let mut sorted = ks.clone();
                sorted.sort_unstable();
                let v = mix_all(5, sorted.iter().map(|&k| k as u128));
                memo.file_keys[f] = ks;
                memo.file_slots[f] = slots;
                Outcome::Value(v)
            }
            kind::DECL_SIG_TOKENS | kind::DECL_BODY_TOKENS => {
                let slot = key.a as usize;
                let Some(site) = self.memo.decl.site[slot] else {
                    return Outcome::Value(0);
                };
                if db
                    .read(self, QueryKey::one(kind::DECL_INDEX, site.file.0))
                    .is_err()
                {
                    return Outcome::Cancelled;
                }
                let decls = self.memo.decls[site.file.index()]
                    .as_ref()
                    .expect("decl_index ran first");
                let d = site.decl as usize;
                let hashes = fors_query::DeclHashes {
                    sig_tokens: decls.sig_hash[d],
                    body_tokens: decls.body_hash[d],
                    ..Default::default()
                };
                let fp = fors_query::decl_fingerprint(&hashes);
                self.memo.decl.sig_tokens[slot] = fp.interface;
                self.memo.decl.body_tokens[slot] = fp.body;
                Outcome::Value(if key.kind == kind::DECL_SIG_TOKENS {
                    fp.interface
                } else {
                    fp.body
                })
            }
            other => unreachable!("stage A cannot compute kind {other}"),
        }
    }
}

// ---------------------------------------------------------------- stage B

/// Everything that reads this revision's whole-build snapshot.
struct StageB<'x, 'a> {
    memo: &'x mut Memo,
    files: &'x [FileEntry],
    parses: &'x [Option<fors_syntax::Parse>],
    interner: &'x Interner,
    resolved: &'x ResolveOutput,
    sigs: &'x Signatures<'a>,
    /// `DefId` -> stable key, for this revision only.
    def_key: Vec<StableKey>,
    /// The builtin impl rows (`prelude::push_builtin_impls`) are declared
    /// AFTER the user declarations, so their `DefId`s renumber whenever a
    /// declaration is inserted. Their identity is their content — the
    /// prelude trait, the head and the position within that pair — never
    /// the `DefId`, or every bucket holding one would change its merkle on
    /// every insertion (I9 verification: a spurious wake of every body that
    /// had probed `(Add, i32)` when a declaration was added above it).
    builtin_key: HashMap<u32, StableKey>,
    /// Per impl row: `(trait stable key, stable head)`, computed once per
    /// revision. Without it every bucket query scans every impl row, which is
    /// quadratic in the impl count and shows up directly in the cold slope.
    row_key: Vec<(u64, u64)>,
    bucket_index: HashMap<(u64, u64), Vec<u32>>,
    head_index: HashMap<u64, Vec<u32>>,
    /// Stable module identity -> `ModuleId`, and the reverse, both computed
    /// once: `candidate_traits` would otherwise re-fold every module's path on
    /// every call.
    module_by_stable: HashMap<u64, ModuleId>,
    module_stable: Vec<u64>,
    /// Stable key -> module, and stable head -> module, for the user
    /// declarations of this revision. `impls_for(tr, h)` reads the
    /// `impl_heads` of BOTH modules (ch08 R21: an impl lives in one of the
    /// two) even when the bucket is empty, so the first impl added in the
    /// trait's module wakes the body that asked.
    key_module: HashMap<u64, ModuleId>,
    head_module: HashMap<u64, ModuleId>,
    /// `DefId` of an `impl`/`trait` -> its member declarations.
    children: HashMap<u32, Vec<DefId>>,
    /// `DefId` of an impl -> its row in the impl index.
    impl_row_of: HashMap<u32, u32>,
    /// `DefId` -> the impl buckets its whole-head checks probed
    /// (`Signatures::sig_buckets`).
    sig_buckets: HashMap<u32, Vec<(u32, u64)>>,
    /// Filled once the body phase has run, indexed by `DefId`.
    body_diags: HashMap<u32, Vec<Diagnostic>>,
    body_deps: HashMap<u32, Vec<DefId>>,
    body_buckets: HashMap<u32, Vec<(u32, u64)>>,
    /// Signature-phase diagnostics, grouped by the declaration they fall in.
    sig_diags: HashMap<u32, Vec<Diagnostic>>,
    loose: Vec<Diagnostic>,
}

impl<'x, 'a> StageB<'x, 'a> {
    /// Builds the per-revision indexes the bucket queries read. O(impl rows +
    /// modules), once, instead of a scan per query.
    fn index(mut self) -> StageB<'x, 'a> {
        self.module_stable = (0..self.resolved.modules.name.len())
            .map(|i| self.module_path_hash(ModuleId(i as u32)))
            .collect();
        for (i, &h) in self.module_stable.iter().enumerate() {
            self.module_by_stable.insert(h, ModuleId(i as u32));
        }
        let rows = self.sigs.impls.rows();
        let mut seq: HashMap<(u32, u64), u32> = HashMap::new();
        for r in rows {
            if self.sigs.defs.get(r.def).is_none() && r.def.index() >= self.def_key.len() {
                let pair = (r.trait_def.0, r.head.as_u64());
                let n = seq.entry(pair).or_insert(0);
                let mut b = [0u8; 17];
                b[0] = 0xFB;
                b[1..5].copy_from_slice(&pair.0.to_le_bytes());
                b[5..13].copy_from_slice(&pair.1.to_le_bytes());
                b[13..].copy_from_slice(&n.to_le_bytes());
                *n += 1;
                self.builtin_key
                    .insert(r.def.0, fors_index::hash_bytes(&b) as u64);
            }
        }
        self.row_key = Vec::with_capacity(rows.len());
        for r in rows {
            self.row_key
                .push((self.key_of_def(r.trait_def), self.stable_head(r.head)));
        }
        for (i, &(tr, head)) in self.row_key.iter().enumerate() {
            self.bucket_index
                .entry((tr, head))
                .or_default()
                .push(i as u32);
            self.head_index.entry(head).or_default().push(i as u32);
            self.impl_row_of.insert(rows[i].def.0, i as u32);
        }
        let user: Vec<(DefId, crate::defs::DefRow)> =
            self.sigs.defs.user_defs().map(|(d, r)| (d, *r)).collect();
        for (def, row) in user {
            let k = self.key_of_def(def);
            if k != 0 {
                self.key_module.insert(k, row.module);
            }
            match row.kind {
                fors_index::DeclKind::Struct | fors_index::DeclKind::Enum => {
                    let h = self.stable_head(HeadKey::Nominal(def));
                    self.head_module.insert(h, row.module);
                }
                fors_index::DeclKind::Trait => {
                    let h = self.stable_head(HeadKey::Nominal(def));
                    self.head_module.insert(h, row.module);
                    let h = self.stable_head(HeadKey::Dyn(def));
                    self.head_module.insert(h, row.module);
                }
                _ => {}
            }
            if row.parent != fors_fir::NO_DEF {
                self.children.entry(row.parent.0).or_default().push(def);
            }
        }
        for (d, bs) in &self.sigs.sig_buckets {
            self.sig_buckets.insert(d.0, bs.clone());
        }
        self
    }

    fn key_of_def(&self, def: DefId) -> StableKey {
        if def == fors_fir::NO_DEF {
            return 0;
        }
        if let Some(&k) = self.builtin_key.get(&def.0) {
            return k;
        }
        match self.def_key.get(def.index()).copied() {
            Some(0) | None => prelude_identity(def),
            Some(k) => k,
        }
    }

    /// The memo slot of a USER declaration. A prelude row has none, and that
    /// is decided by `DefTable::first_user`, never by a bit of the key.
    fn slot_of_def(&self, def: DefId) -> Option<u32> {
        if def == fors_fir::NO_DEF || def.index() < self.sigs.defs.first_user.index() {
            return None;
        }
        let k = self.key_of_def(def);
        if k == 0 {
            return None;
        }
        self.memo.decl.find(k)
    }

    /// A build-independent name for a type's head: `HeadKey::as_u64` carries
    /// a `DefId`, which renumbers, so the nominal and `dyn` payloads are
    /// replaced by the declaration's stable key.
    fn stable_head(&self, h: HeadKey) -> u64 {
        let (d, p): (u64, u64) = match h {
            HeadKey::Prim(k) => (1, k as u64),
            HeadKey::Nominal(x) => (2, self.key_of_def(x)),
            HeadKey::Tuple(n) => (3, n as u64),
            HeadKey::Fn => (4, 0),
            HeadKey::Dyn(x) => (5, self.key_of_def(x)),
            HeadKey::Param => (6, 0),
            HeadKey::Proj => (7, 0),
            HeadKey::Never => (8, 0),
            HeadKey::Unit => (9, 0),
            HeadKey::Error => (10, 0),
            HeadKey::ConstVal => (11, 0),
            HeadKey::Brand => (12, 0),
        };
        let mut b = [0u8; 16];
        b[..8].copy_from_slice(&d.to_le_bytes());
        b[8..].copy_from_slice(&p.to_le_bytes());
        fors_index::hash_bytes(&b) as u64
    }

    fn stable_head_raw(&self, raw: u64) -> u64 {
        // The reverse of `HeadKey::as_u64`'s packing: the discriminant is in
        // the high bits, the payload in the low 40.
        let disc = raw >> 40;
        let payload = raw & ((1 << 40) - 1);
        let p = match disc {
            2 | 5 => self.key_of_def(DefId(payload as u32)),
            _ => payload,
        };
        let mut b = [0u8; 16];
        b[..8].copy_from_slice(&disc.to_le_bytes());
        b[8..].copy_from_slice(&p.to_le_bytes());
        fors_index::hash_bytes(&b) as u64
    }

    /// The fold itself; [`StageB::module_id`] is the cached column.
    fn module_path_hash(&self, m: ModuleId) -> u64 {
        let mut b: Vec<u8> = Vec::new();
        if let Some(segs) = self.resolved.modules.name.get(m.index()) {
            for &s in segs {
                b.extend_from_slice(self.interner.resolve(s));
                b.push(0xFF);
            }
        }
        fors_index::hash_bytes(&b) as u64
    }

    fn module_id(&self, m: ModuleId) -> u64 {
        self.module_stable
            .get(m.index())
            .copied()
            .unwrap_or_else(|| self.module_path_hash(m))
    }

    fn module_of(&self, def: DefId) -> ModuleId {
        self.sigs
            .defs
            .get(def)
            .map(|r| r.module)
            .unwrap_or(ModuleId(u32::MAX))
    }

    fn module_node(&mut self, m: ModuleId) -> u32 {
        let s = self.module_id(m);
        self.memo.ids.intern(fam::MODULE, s, m.0 as u64)
    }

    fn head_node(&mut self, head: u64) -> u32 {
        self.memo.ids.intern(fam::HEAD, head, 0)
    }

    fn bucket_node(&mut self, trait_key: u64, head: u64) -> u32 {
        self.memo.ids.intern(fam::BUCKET, trait_key, head)
    }

    fn candidate_node(&mut self, head: u64, module: u64) -> u32 {
        self.memo.ids.intern(fam::CANDIDATE, head, module)
    }

    /// The `(trait DefId, HeadKey)` pair an interned bucket id names, back in
    /// this revision's numbering. `None` for a bucket whose trait or head no
    /// longer exists in this build.
    fn bucket_rows(&self, id: u32) -> Vec<fors_fir::impls::ImplRow> {
        let (_, trait_key, head) = self.memo.ids.row(id);
        self.bucket_index
            .get(&(trait_key, head))
            .map(|rs| rs.iter().map(|&i| self.sigs.impls.row(i)).collect())
            .unwrap_or_default()
    }

    /// The name-use entries inside a declaration's own subtree, split into
    /// the signature part and the whole.
    fn uses_in(&self, site: Site, signature_only: bool) -> Vec<(u32, ResolvedTarget)> {
        let Some(p) = self.parses[site.file.index()].as_ref() else {
            return Vec::new();
        };
        let node = site.node as usize;
        let (lo, hi) = if signature_only {
            // A `fn`'s signature is its `FnSig` child; for everything else
            // the whole declaration minus any body block is the signature.
            match p
                .tree
                .children(node)
                .find(|&c| p.tree.kinds[c] == NodeKind::FnSig)
            {
                Some(fs) => (fs as u32, (fs + p.tree.subtree_len[fs] as usize) as u32),
                None => {
                    let end = node + p.tree.subtree_len[node] as usize;
                    let body = p
                        .tree
                        .children(node)
                        .find(|&c| p.tree.kinds[c] == NodeKind::Block);
                    (node as u32, body.map(|b| b as u32).unwrap_or(end as u32))
                }
            }
        } else {
            (
                node as u32,
                (node + p.tree.subtree_len[node] as usize) as u32,
            )
        };
        let uses = &self.resolved.files[site.file.index()].name_uses;
        let start = uses.node.partition_point(|&n| n < lo);
        let end = uses.node.partition_point(|&n| n < hi);
        (start..end)
            .map(|i| (uses.node[i] - site.node, uses.target[i]))
            .collect()
    }

    /// A name-use target, as something stable across revisions. `base` is the
    /// declaration's own CST node, because a local binding is addressed by the
    /// node that introduced it and an ABSOLUTE node index shifts whenever any
    /// earlier declaration grows — which would wake every later body on every
    /// edit. Pass 0 for a whole-build fold, where nothing is being compared
    /// across revisions anyway.
    fn target_stable(&self, t: ResolvedTarget, base: u32) -> u64 {
        match t {
            ResolvedTarget::Entity(Entity::Item { file, decl })
            | ResolvedTarget::Entity(Entity::Variant { file, decl, .. }) => self
                .memo
                .file_keys
                .get(file.index())
                .and_then(|ks| ks.get(decl.index()))
                .copied()
                .unwrap_or(0),
            ResolvedTarget::Entity(Entity::Module(m)) => self.module_id(m),
            ResolvedTarget::Entity(Entity::PreludeType(s))
            | ResolvedTarget::Entity(Entity::PreludeValue(s))
            | ResolvedTarget::Entity(Entity::PreludeModule(s, _)) => {
                let mut b = vec![0xFDu8];
                b.extend_from_slice(self.interner.resolve(s));
                fors_index::hash_bytes(&b) as u64
            }
            ResolvedTarget::Entity(Entity::Poisoned) => 0xDEAD,
            // A local is addressed by the node that introduced it; the node
            // is already stored relative to the declaration.
            ResolvedTarget::Local { node } => 0x1_0000_0000 | node.wrapping_sub(base) as u64,
            ResolvedTarget::Deferred { reason } => 0x2_0000_0000 | reason as u64,
        }
    }

    /// §9.1's "member index slice": names, kinds and visibility, never types
    /// (a type change is already a `signature_of` change, which `members_of`
    /// depends on).
    fn push_member_index(&self, d: DefId, items: &mut Vec<u128>) {
        let ml = self.sigs.fir.sigs.members(d);
        for i in 0..self.sigs.fir.sigs.member_store.count(ml) {
            let m = self.sigs.fir.sigs.member_store.get(ml, i);
            let mut b: Vec<u8> = Vec::new();
            b.push(m.kind as u8);
            b.push(m.vis);
            b.push(m.payload as u8);
            b.extend_from_slice(self.interner.resolve(m.name));
            b.extend_from_slice(&self.key_of_def(m.def).to_le_bytes());
            items.push(fors_index::hash_bytes(&b));
        }
    }

    /// The declarations a declaration's SIGNATURE mentions, as slots.
    fn sig_mentions(&mut self, site: Site) -> Vec<u32> {
        let uses = self.uses_in(site, true);
        let mut out = Vec::new();
        for (_, t) in uses {
            if let ResolvedTarget::Entity(Entity::Item { file, decl })
            | ResolvedTarget::Entity(Entity::Variant { file, decl, .. }) = t
                && let Some(&k) = self
                    .memo
                    .file_keys
                    .get(file.index())
                    .and_then(|ks| ks.get(decl.index()))
                && let Some(s) = self.memo.decl.find(k)
            {
                out.push(s);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

impl Queries for StageB<'_, '_> {
    fn on_cycle(&mut self, _key: QueryKey, _c: &Cycle) -> ValueHash {
        // Design §10: a cycle through signatures yields one diagnostic at the
        // lexicographically least `DeclKey` and `TY_ERROR` elsewhere — the
        // signature phase already decided that, so the engine's recovery
        // value only has to be a fixed point that does not depend on which
        // node was demanded first.
        0
    }

    fn compute(&mut self, db: &mut Db, key: QueryKey) -> Outcome {
        macro_rules! read {
            ($k:expr) => {
                if db.read(self, $k).is_err() {
                    return Outcome::Cancelled;
                }
            };
        }
        match key.kind {
            kind::MODULE_GRAPH => {
                // The set of files is an input of the graph: a file added to
                // the build has no `module_facts` edge here yet.
                read!(QueryKey::unit(kind::FILE_SET));
                for f in 0..self.files.len() {
                    read!(QueryKey::one(kind::MODULE_FACTS, f as u32));
                }
                let edges: Vec<u128> = self
                    .resolved
                    .edges
                    .iter()
                    .map(|&(a, b)| mix(self.module_id(a) as u128, self.module_id(b) as u128))
                    .collect();
                Outcome::Value(mix_all(6, edges))
            }
            kind::RESOLVE_BUILD => {
                read!(QueryKey::unit(kind::FILE_SET));
                for f in 0..self.files.len() {
                    read!(QueryKey::one(kind::PARSE, f as u32));
                    read!(QueryKey::one(kind::MODULE_FACTS, f as u32));
                }
                let mut v: ValueHash = 8;
                for fr in &self.resolved.files {
                    let mut b: Vec<u8> = Vec::with_capacity(fr.name_uses.node.len() * 8);
                    for i in 0..fr.name_uses.node.len() {
                        b.extend_from_slice(&fr.name_uses.node[i].to_le_bytes());
                        b.extend_from_slice(
                            &self.target_stable(fr.name_uses.target[i], 0).to_le_bytes(),
                        );
                        b.push(fr.name_uses.consumed[i]);
                    }
                    v = mix(v, fors_index::hash_bytes(&b));
                    for d in &fr.diagnostics {
                        v = mix(
                            v,
                            fors_index::hash_bytes(
                                format!("{}:{}:{}", d.code.as_string(), d.start, d.message)
                                    .as_bytes(),
                            ),
                        );
                    }
                }
                Outcome::Value(v)
            }
            kind::SIGNATURE_PHASE => {
                read!(QueryKey::unit(kind::RESOLVE_BUILD));
                for f in 0..self.files.len() {
                    read!(QueryKey::one(kind::DECL_INDEX, f as u32));
                }
                let mut v: ValueHash = 9;
                for (d, _) in self.sigs.defs.user_defs() {
                    v = mix(v, self.sigs.fir.sigs.sig_hash(d));
                }
                // `sig_diags` is a `HashMap`: fold in sorted order, or the
                // value would depend on the iteration order of the run.
                let mut ds: Vec<u128> = self
                    .sig_diags
                    .values()
                    .flatten()
                    .map(|d| CachedDiag::of(d, 0).hash())
                    .collect();
                ds.sort_unstable();
                Outcome::Value(mix_all(v, ds))
            }
            kind::MODULE_EXPORTS => {
                read!(QueryKey::unit(kind::MODULE_GRAPH));
                let (_, _, raw) = self.memo.ids.row(key.a);
                let m = ModuleId(raw as u32);
                let file = self
                    .resolved
                    .modules
                    .file
                    .get(m.index())
                    .copied()
                    .unwrap_or(FileId(u32::MAX));
                if file.0 as usize >= self.files.len() {
                    return Outcome::Value(0);
                }
                read!(QueryKey::one(kind::DECL_INDEX, file.0));
                let lines = self.resolved.export_signature(file.index(), self.interner);
                Outcome::Value(mix_all(
                    7,
                    lines.iter().map(|l| fors_index::hash_bytes(l.as_bytes())),
                ))
            }
            kind::NAME_USES => {
                read!(QueryKey::unit(kind::RESOLVE_BUILD));
                let slot = key.a as usize;
                let Some(site) = self.memo.decl.site[slot] else {
                    return Outcome::Value(0);
                };
                read!(QueryKey::one(kind::DECL_INDEX, site.file.0));
                let uses = self.uses_in(site, false);
                let mut b: Vec<u8> = Vec::with_capacity(uses.len() * 12);
                for (rel, t) in &uses {
                    b.extend_from_slice(&rel.to_le_bytes());
                    b.extend_from_slice(&self.target_stable(*t, site.node).to_le_bytes());
                }
                let v = mix(12, fors_index::hash_bytes(&b));
                self.memo.decl.name_uses[slot] = v;
                Outcome::Value(v)
            }
            kind::DECL_ARITY => {
                let slot = key.a as usize;
                read!(QueryKey::one(kind::DECL_SIG_TOKENS, key.a));
                let def = self.memo.decl.def[slot];
                if def == fors_fir::NO_DEF {
                    return Outcome::Value(0);
                }
                let m = self.module_of(def);
                let mid = self.module_node(m);
                read!(QueryKey::one(kind::MODULE_EXPORTS, mid));
                let mut b: Vec<u8> = Vec::new();
                b.push(self.sigs.fir.sigs.kind(def) as u8);
                for g in self.sigs.shapes.gkinds(def) {
                    b.push(*g as u8);
                }
                b.push(0xFF);
                for a in self.sigs.shapes.assoc(def) {
                    b.extend_from_slice(self.interner.resolve(*a));
                    b.push(0xFE);
                }
                let v = mix(13, fors_index::hash_bytes(&b));
                self.memo.decl.arity[slot] = v;
                Outcome::Value(v)
            }
            kind::SIGNATURE_OF => {
                let slot = key.a as usize;
                read!(QueryKey::one(kind::DECL_SIG_TOKENS, key.a));
                read!(QueryKey::one(kind::NAME_USES, key.a));
                read!(QueryKey::one(kind::DECL_ARITY, key.a));
                let Some(site) = self.memo.decl.site[slot] else {
                    return Outcome::Value(0);
                };
                let mentions = self.sig_mentions(site);
                for &m in &mentions {
                    read!(QueryKey::one(kind::DECL_ARITY, m));
                }
                self.memo.decl.sig_mentions[slot] = mentions;
                let def = self.memo.decl.def[slot];
                // A member's signature can project through its container's
                // associated-type definitions (`-> Self.Key`), so the
                // container's signature is an in-edge. §9.1 writes this as
                // "`assoc_defs` for projections in its own types"; the parent
                // edge is that, for the projections whose impl is the
                // declaration's own container.
                let parent = self
                    .sigs
                    .defs
                    .get(def)
                    .map(|r| r.parent)
                    .unwrap_or(fors_fir::NO_DEF);
                if let Some(ps) = self.slot_of_def(parent) {
                    read!(QueryKey::one(kind::SIGNATURE_OF, ps));
                }
                // What the whole-head checks on this declaration read beyond
                // its own tokens — found by I9's verification pass, each
                // with the stale diagnostic it would otherwise leave:
                let mut extra: Vec<u128> = Vec::new();
                let row = self.sigs.defs.get(def).copied();
                if let Some(row) = row {
                    // Its members' signature tokens are part of its
                    // interface (an impl's completeness, a trait's
                    // `dyn`-capability).
                    let kids = self.children.get(&def.0).cloned().unwrap_or_default();
                    for c in &kids {
                        if let Some(s) = self.slot_of_def(*c) {
                            read!(QueryKey::one(kind::DECL_SIG_TOKENS, s));
                        }
                    }
                    if row.kind == fors_index::DeclKind::Trait {
                        // A trait's VALUE is its interface: the member index
                        // and each member's canonical hash, so an impl that
                        // reads it is woken by a new required method
                        // (T0017) or a changed one, and not by a re-spelling.
                        self.push_member_index(def, &mut extra);
                        for c in &kids {
                            extra.push(self.sigs.fir.sigs.sig_hash(*c));
                        }
                    }
                    if row.kind == fors_index::DeclKind::Impl {
                        // The impl world of its own module and its head's
                        // (R21: every impl of this head is in one of the
                        // two): overlap, prerequisites, member clashes.
                        let own = self.module_node(row.module);
                        read!(QueryKey::one(kind::IMPL_HEADS, own));
                        if let Some(&ri) = self.impl_row_of.get(&def.0) {
                            let r = self.sigs.impls.row(ri);
                            if let HeadKey::Nominal(h) | HeadKey::Dyn(h) = r.head {
                                let hm = self.module_of(h);
                                if hm.0 != u32::MAX && hm != row.module {
                                    let n = self.module_node(hm);
                                    read!(QueryKey::one(kind::IMPL_HEADS, n));
                                }
                            }
                            // The trait it implements: its interface is
                            // folded into this impl's value so the members
                            // (which read their parent) follow a trait edit.
                            if let Some(ts) = self.slot_of_def(r.trait_def) {
                                match db.read(self, QueryKey::one(kind::SIGNATURE_OF, ts)) {
                                    Ok(tv) => extra.push(tv),
                                    Err(_) => return Outcome::Cancelled,
                                }
                            }
                        }
                    }
                    // The impl buckets its whole-head checks probed
                    // (`impl Copyable for W` asks whether every field is
                    // `Copyable`, which may hold through another module's
                    // impl): §9.1's `impls_for` in-edge of `signature_of`.
                    let probed = self.sig_buckets.get(&def.0).cloned().unwrap_or_default();
                    for &(tr_raw, head_raw) in &probed {
                        let tr = self.key_of_def(DefId(tr_raw));
                        let head = self.stable_head_raw(head_raw);
                        let b = self.bucket_node(tr, head);
                        read!(QueryKey::one(kind::IMPLS_FOR, b));
                    }
                }
                extra.sort_unstable();
                let sig_hash = if def == fors_fir::NO_DEF {
                    0
                } else {
                    self.sigs.fir.sigs.sig_hash(def)
                };
                // R14's verdict (site 14) belongs to `infinite_size()`, not
                // to the declaration it points at.
                let cached: Vec<CachedDiag> = self
                    .sig_diags
                    .get(&def.0)
                    .map(|ds| {
                        ds.iter()
                            .filter(|d| d.site != 14)
                            .map(|d| CachedDiag::of(d, site.origin))
                            .collect()
                    })
                    .unwrap_or_default();
                let v = mix_all(mix(14, sig_hash), cached.iter().map(|d| d.hash()));
                let v = mix_all(v, extra);
                self.memo.decl.sig_hash[slot] = sig_hash;
                self.memo.decl.sig_diags[slot] = cached;
                Outcome::Value(v)
            }
            kind::IMPL_HEADS => {
                let (_, _, raw) = self.memo.ids.row(key.a);
                let m = ModuleId(raw as u32);
                let file = self
                    .resolved
                    .modules
                    .file
                    .get(m.index())
                    .copied()
                    .unwrap_or(FileId(u32::MAX));
                if file.0 as usize >= self.files.len() {
                    return Outcome::Value(0);
                }
                read!(QueryKey::one(kind::DECL_KEYS, file.0));
                let mut triples: Vec<u128> = Vec::new();
                let rows: Vec<(u32, fors_fir::impls::ImplRow)> = self
                    .sigs
                    .impls
                    .rows()
                    .iter()
                    .enumerate()
                    .filter(|(_, r)| self.module_of(r.def) == m)
                    .map(|(i, r)| (i as u32, *r))
                    .collect();
                for &(i, r) in &rows {
                    if let Some(s) = self.slot_of_def(r.def) {
                        read!(QueryKey::one(kind::DECL_SIG_TOKENS, s));
                    }
                    let (tr, head) = self.row_key[i as usize];
                    triples.push(mix(
                        mix(tr as u128, head as u128),
                        self.key_of_def(r.def) as u128,
                    ));
                }
                triples.sort_unstable();
                Outcome::Value(mix_all(15, triples))
            }
            kind::IMPLS_FOR => {
                let (_, trait_key, head) = self.memo.ids.row(key.a);
                // ch08 R21 makes the bucket a function of exactly two
                // modules: the trait's and the head's (§9.1, "two nodes").
                let mut mods: Vec<ModuleId> = Vec::new();
                for &i in self.head_index.get(&head).map(|v| &v[..]).unwrap_or(&[]) {
                    let r = self.sigs.impls.row(i);
                    if self.row_key[i as usize].0 == trait_key {
                        mods.push(self.module_of(r.trait_def));
                    }
                    if let HeadKey::Nominal(d) | HeadKey::Dyn(d) = r.head {
                        mods.push(self.module_of(d));
                    }
                }
                if let Some(rs) = self.bucket_index.get(&(trait_key, head)) {
                    for &i in rs {
                        mods.push(self.module_of(self.sigs.impls.row(i).trait_def));
                    }
                }
                // Always the trait's module and the head's, bucket empty or
                // not: R21 puts every impl of this pair in one of the two.
                if let Some(&m) = self.key_module.get(&trait_key) {
                    mods.push(m);
                }
                if let Some(&m) = self.head_module.get(&head) {
                    mods.push(m);
                }
                mods.sort_unstable_by_key(|m| m.0);
                mods.dedup();
                for m in mods {
                    if m.0 != u32::MAX {
                        let id = self.module_node(m);
                        read!(QueryKey::one(kind::IMPL_HEADS, id));
                    }
                }
                let mut rows = self.bucket_rows(key.a);
                rows.sort_unstable_by_key(|r| self.key_of_def(r.def));
                // The merkle below folds each impl's canonical `sig_hash`, so
                // the node must be red when one of them can have moved: its
                // signature tokens (a leaf, hence no cycle with the impl's
                // own `signature_of`, which reads this node for the buckets
                // its whole-head checks probed). Without this edge the
                // bucket stayed green across `type Key = i64;` -> `i32;`
                // with a stale merkle, and the next `impl_heads` change
                // flipped it — waking every body that had read it.
                for r in &rows {
                    if let Some(s) = self.slot_of_def(r.def) {
                        read!(QueryKey::one(kind::DECL_SIG_TOKENS, s));
                    }
                }
                let merkle: Vec<u128> = rows
                    .iter()
                    .map(|r| {
                        mix(
                            self.key_of_def(r.def) as u128,
                            self.sigs.fir.sigs.sig_hash(r.def),
                        )
                    })
                    .collect();
                Outcome::Value(mix_all(16, merkle))
            }
            kind::OVERLAP_CHECK => {
                read!(QueryKey::one(kind::IMPLS_FOR, key.a));
                let rows = self.bucket_rows(key.a);
                for r in &rows {
                    if let Some(s) = self.slot_of_def(r.def) {
                        read!(QueryKey::one(kind::SIGNATURE_OF, s));
                    }
                }
                // R19 per bucket, computed here rather than read off the
                // signature phase's diagnostics: the verdict is the value.
                let mut verdicts: Vec<u128> = Vec::new();
                for i in 0..rows.len() {
                    for j in (i + 1)..rows.len() {
                        let o = fors_fir::impls::overlap(
                            &self.sigs.fir.tys,
                            &self.sigs.fir.sigs,
                            &rows[i],
                            &rows[j],
                        );
                        verdicts.push(mix(
                            mix(
                                self.key_of_def(rows[i].def) as u128,
                                self.key_of_def(rows[j].def) as u128,
                            ),
                            o as u128,
                        ));
                    }
                }
                verdicts.sort_unstable();
                Outcome::Value(mix_all(17, verdicts))
            }
            kind::MEMBERS_OF => {
                let (_, head, _) = self.memo.ids.row(key.a);
                let owner = self
                    .head_index
                    .get(&head)
                    .and_then(|rs| rs.first())
                    .and_then(|&i| match self.sigs.impls.row(i).head {
                        HeadKey::Nominal(d) | HeadKey::Dyn(d) => Some(d),
                        _ => None,
                    });
                if let Some(d) = owner
                    && let Some(s) = self.slot_of_def(d)
                {
                    read!(QueryKey::one(kind::SIGNATURE_OF, s));
                }
                let inherent: Vec<DefId> = self
                    .head_index
                    .get(&head)
                    .map(|rs| {
                        rs.iter()
                            .map(|&i| self.sigs.impls.row(i))
                            .filter(|r| r.inherent)
                            .map(|r| r.def)
                            .collect()
                    })
                    .unwrap_or_default();
                for d in &inherent {
                    if let Some(s) = self.slot_of_def(*d) {
                        read!(QueryKey::one(kind::SIGNATURE_OF, s));
                    }
                }
                // The member INDEX: names, kinds and visibility, plus each
                // inherent impl's method names. The member TYPES are already
                // covered by the `signature_of` edges above.
                let mut items: Vec<u128> = Vec::new();
                if let Some(d) = owner {
                    self.push_member_index(d, &mut items);
                }
                for d in &inherent {
                    self.push_member_index(*d, &mut items);
                }
                items.sort_unstable();
                Outcome::Value(mix_all(18, items))
            }
            kind::CANDIDATE_TRAITS => {
                read!(QueryKey::unit(kind::MODULE_GRAPH));
                let (_, head, module) = self.memo.ids.row(key.a);
                let home = self.module_by_stable.get(&module).copied();
                let mut scope: Vec<ModuleId> = Vec::new();
                if let Some(m) = home {
                    scope.push(m);
                    scope.extend(self.resolved.direct_edges_of(m));
                }
                let of_head: Vec<u32> = self.head_index.get(&head).cloned().unwrap_or_default();
                for &i in &of_head {
                    scope.push(self.module_of(self.sigs.impls.row(i).def));
                }
                scope.sort_unstable_by_key(|m| m.0);
                scope.dedup();
                // §9.1: "`impl_heads` of head module, `m`, and `m`'s direct
                // edges". The head's module is an in-edge even when it has
                // no impl of this head yet.
                let mut reads = scope.clone();
                if let Some(&m) = self.head_module.get(&head) {
                    reads.push(m);
                }
                reads.sort_unstable_by_key(|m| m.0);
                reads.dedup();
                for m in &reads {
                    if m.0 != u32::MAX {
                        let id = self.module_node(*m);
                        read!(QueryKey::one(kind::IMPL_HEADS, id));
                    }
                }
                let mut traits: Vec<u128> = of_head
                    .iter()
                    .map(|&i| (i, self.sigs.impls.row(i)))
                    .filter(|(_, r)| {
                        r.trait_def != fors_fir::NO_DEF && scope.contains(&self.module_of(r.def))
                    })
                    .map(|(i, _)| self.row_key[i as usize].0 as u128)
                    .collect();
                traits.sort_unstable();
                traits.dedup();
                Outcome::Value(mix_all(19, traits))
            }
            kind::SIZE_EDGES => {
                read!(QueryKey::one(kind::SIGNATURE_OF, key.a));
                let slot = key.a as usize;
                let def = self.memo.decl.def[slot];
                if def == fors_fir::NO_DEF {
                    return Outcome::Value(0);
                }
                // R14's summary edge set, at head granularity: the heads of
                // the declaration's own members' types. Every change below
                // that granularity is already a `signature_of` change.
                let ml = self.sigs.fir.sigs.members(def);
                let mut heads: Vec<u128> = Vec::new();
                for i in 0..self.sigs.fir.sigs.member_store.count(ml) {
                    let m = self.sigs.fir.sigs.member_store.get(ml, i);
                    if m.ty != fors_fir::ty::NO_TY {
                        heads.push(self.stable_head(self.sigs.fir.tys.head_key(m.ty)) as u128);
                    }
                }
                heads.sort_unstable();
                heads.dedup();
                // `size_edges` keeps no value beyond its hash, so there is no
                // memo column for it: the engine's node IS the memo.
                Outcome::Value(mix_all(mix(20, self.memo.decl.sig_hash[slot]), heads))
            }
            kind::INFINITE_SIZE => {
                // "every `size_edges`" — including the ones that do not exist
                // yet: two mutually recursive structs added in ONE edit are
                // reachable only through the declaration sets.
                for f in 0..self.files.len() {
                    read!(QueryKey::one(kind::DECL_KEYS, f as u32));
                }
                let slots: Vec<u32> = (0..self.memo.decl.len() as u32)
                    .filter(|&s| self.memo.decl.site[s as usize].is_some())
                    .collect();
                for s in slots {
                    read!(QueryKey::one(kind::SIZE_EDGES, s));
                }
                // R14's verdicts, read off the signature phase's own
                // diagnostics at their emission site and OWNED here: the
                // declaration a verdict points at may stay green while the
                // edit that broke its cycle happened elsewhere in the cycle.
                let mut rows: Vec<(u32, CachedDiag)> = Vec::new();
                for (def, ds) in &self.sig_diags {
                    for d in ds {
                        if d.site == 14
                            && let Some(s) = self.slot_of_def(DefId(*def))
                            && let Some(site) = self.memo.decl.site[s as usize]
                        {
                            rows.push((s, CachedDiag::of(d, site.origin)));
                        }
                    }
                }
                rows.sort_by_key(|(s, d)| (*s, d.hash()));
                let v = mix_all(21, rows.iter().map(|(s, d)| mix(*s as u128, d.hash())));
                self.memo.infinite = rows;
                Outcome::Value(v)
            }
            kind::CHECK_BODY => {
                let slot = key.a as usize;
                read!(QueryKey::one(kind::DECL_BODY_TOKENS, key.a));
                read!(QueryKey::one(kind::DECL_SIG_TOKENS, key.a));
                read!(QueryKey::one(kind::NAME_USES, key.a));
                read!(QueryKey::one(kind::SIGNATURE_OF, key.a));
                let Some(site) = self.memo.decl.site[slot] else {
                    return Outcome::Value(0);
                };
                let def = self.memo.decl.def[slot];
                // The signatures this body read (ch09 R2's interface).
                let read_defs = self.body_deps.get(&def.0).cloned().unwrap_or_default();
                let mut dep_slots: Vec<u32> = Vec::new();
                for d in &read_defs {
                    if let Some(s) = self.slot_of_def(*d) {
                        dep_slots.push(s);
                    }
                }
                dep_slots.sort_unstable();
                dep_slots.dedup();
                for &s in &dep_slots {
                    read!(QueryKey::one(kind::SIGNATURE_OF, s));
                }
                // The impl buckets it probed, and the member index and
                // candidate-trait set derived from them.
                let probed = self.body_buckets.get(&def.0).cloned().unwrap_or_default();
                let home = self.module_id(self.module_of(def));
                let mut bucket_ids: Vec<u32> = Vec::new();
                for &(tr_raw, head_raw) in &probed {
                    let tr = self.key_of_def(DefId(tr_raw));
                    let head = self.stable_head_raw(head_raw);
                    let b = self.bucket_node(tr, head);
                    bucket_ids.push(b);
                    read!(QueryKey::one(kind::IMPLS_FOR, b));
                    let h = self.head_node(head);
                    read!(QueryKey::one(kind::MEMBERS_OF, h));
                    let c = self.candidate_node(head, home);
                    read!(QueryKey::one(kind::CANDIDATE_TRAITS, c));
                }
                bucket_ids.sort_unstable();
                bucket_ids.dedup();
                let cached: Vec<CachedDiag> = self
                    .body_diags
                    .get(&def.0)
                    .map(|ds| ds.iter().map(|d| CachedDiag::of(d, site.origin)).collect())
                    .unwrap_or_default();
                let v = mix_all(22, cached.iter().map(|d| d.hash()));
                self.memo.decl.body_diags[slot] = cached;
                self.memo.decl.body_deps[slot] = dep_slots;
                self.memo.decl.body_buckets[slot] = bucket_ids;
                Outcome::Value(v)
            }
            kind::LOOSE_DIAGS => {
                read!(QueryKey::unit(kind::SIGNATURE_PHASE));
                let v = mix_all(23, self.loose.iter().map(|d| CachedDiag::of(d, 0).hash()));
                self.memo.loose = self.loose.clone();
                Outcome::Value(v)
            }
            other => unreachable!("stage B cannot compute kind {other}"),
        }
    }
}

// ----------------------------------------------------------------- driver

impl QueryBuild {
    /// Brings the build up to date. Design §9's demand loop, in the order the
    /// node set forces:
    ///
    /// 1. the inputs;
    /// 2. the per-file nodes (`parse` is skipped for a file whose bytes did
    ///    not change);
    /// 3. the two whole-build passes, eagerly, then the nodes that read them;
    /// 4. the plan: which `check_body` nodes are red;
    /// 5. ONE body phase for exactly those declarations;
    /// 6. the `check_body` nodes, which record their in-edges and cache their
    ///    diagnostics.
    pub fn recheck(&mut self) -> Result<(), Cancelled> {
        self.oracle_failures.clear();
        let QueryBuild {
            db,
            interner,
            files,
            parses,
            memo,
            root,
            package,
            paranoid,
            last_stats,
            oracle_failures,
        } = self;
        memo.grow_files(files.len());

        // 1. Inputs.
        let mut paths = String::new();
        for f in files.iter().filter(|f| f.live) {
            paths.push_str(&f.path);
            paths.push('\n');
        }
        db.set_input(
            QueryKey::unit(kind::FILE_SET),
            mix(1, fors_index::hash_bytes(paths.as_bytes())),
        );
        for (i, f) in files.iter().enumerate() {
            let h = mix(
                if f.live { 1 } else { 2 },
                fors_index::hash_bytes(&f.source),
            );
            db.set_input(QueryKey::one(kind::SOURCE_TEXT, i as u32), h);
        }

        // 2. The per-file half.
        {
            let mut a = StageA {
                files,
                parses,
                interner,
                memo,
            };
            for i in 0..a.files.len() as u32 {
                db.demand(&mut a, QueryKey::one(kind::PARSE, i))?;
                db.demand(&mut a, QueryKey::one(kind::DECL_INDEX, i))?;
                db.demand(&mut a, QueryKey::one(kind::MODULE_FACTS, i))?;
                db.demand(&mut a, QueryKey::one(kind::DECL_KEYS, i))?;
            }
            // EVERY slot, including one whose declaration left the build this
            // revision (its value becomes 0): stage B's nodes still hold
            // edges to it, and a stage-A node found red inside stage B's
            // verification walk would have to be computed by stage B.
            let slots: Vec<u32> = (0..a.memo.decl.len() as u32).collect();
            for s in slots {
                db.demand(&mut a, QueryKey::one(kind::DECL_SIG_TOKENS, s))?;
                db.demand(&mut a, QueryKey::one(kind::DECL_BODY_TOKENS, s))?;
            }
        }
        if db.is_cancelled() {
            return Err(Cancelled);
        }

        // 3. The two whole-build passes (design §3 fork 14 and the module
        //    docs' stated limitation), then the snapshot's nodes.
        // Every file, in `FileId` order: `Signatures`' file indices and this
        // build's `FileId`s must be the same numbers, so a removed file stays
        // in the list as an empty module rather than shifting the rest.
        let inputs: Vec<FileInput> = files
            .iter()
            .enumerate()
            .map(|(i, f)| FileInput {
                tree: &parses[i].as_ref().expect("every file is parsed").tree,
                tokens: &parses[i].as_ref().expect("every file is parsed").tokens,
                source: &f.source,
                name: f.module.clone(),
            })
            .collect();
        let resolved =
            fors_resolve::resolve_in_package(interner, &inputs, *root, package.as_deref());
        let mut sigs = crate::check_signatures(&inputs, &resolved, interner);

        // Where every declaration is in THIS revision, and the per-declaration
        // split of the signature phase's diagnostics.
        let mut def_key = vec![0u64; sigs.defs.len()];
        for (def, row) in sigs.defs.user_defs() {
            let k = memo
                .file_keys
                .get(row.file.index())
                .and_then(|ks| ks.get(row.decl.index()))
                .copied()
                .unwrap_or(0);
            def_key[def.index()] = k;
            if k != 0 {
                let slot = memo.decl.slot(k);
                memo.decl.def[slot as usize] = def;
            }
        }
        let (sig_diags, loose) = attribute(&sigs.diagnostics, &sigs, memo);

        let mut stage = StageB {
            memo,
            files,
            parses,
            interner,
            resolved: &resolved,
            sigs: &sigs,
            def_key,
            body_diags: HashMap::new(),
            body_deps: HashMap::new(),
            body_buckets: HashMap::new(),
            sig_diags,
            loose,
            row_key: Vec::new(),
            bucket_index: HashMap::new(),
            head_index: HashMap::new(),
            module_by_stable: HashMap::new(),
            module_stable: Vec::new(),
            key_module: HashMap::new(),
            head_module: HashMap::new(),
            children: HashMap::new(),
            impl_row_of: HashMap::new(),
            sig_buckets: HashMap::new(),
            builtin_key: HashMap::new(),
        }
        .index();
        db.demand(&mut stage, QueryKey::unit(kind::MODULE_GRAPH))?;
        db.demand(&mut stage, QueryKey::unit(kind::RESOLVE_BUILD))?;
        db.demand(&mut stage, QueryKey::unit(kind::SIGNATURE_PHASE))?;
        // `loose_diags` is demanded once, after the body phase: a demand here
        // would memoise the signature half alone and the body phase's loose
        // diagnostics would never reach the memo this revision.
        let live: Vec<u32> = (0..stage.memo.decl.len() as u32)
            .filter(|&s| stage.memo.decl.site[s as usize].is_some())
            .collect();
        for &s in &live {
            db.demand(&mut stage, QueryKey::one(kind::NAME_USES, s))?;
            db.demand(&mut stage, QueryKey::one(kind::DECL_ARITY, s))?;
        }
        for &s in &live {
            db.demand(&mut stage, QueryKey::one(kind::SIGNATURE_OF, s))?;
            db.demand(&mut stage, QueryKey::one(kind::SIZE_EDGES, s))?;
        }
        // The impl world: every bucket the index has, plus every bucket some
        // body probed in an earlier revision (an EMPTY bucket is a node too —
        // adding the first impl to one must wake the body that asked).
        let mut buckets: Vec<u32> = Vec::new();
        // Sorted, so the interned bucket ids (and with them every
        // `executed_keys` listing) are the same from one process to the next.
        let mut pairs: Vec<(u64, u64)> = stage.bucket_index.keys().copied().collect();
        pairs.sort_unstable();
        for (tr, head) in pairs {
            buckets.push(stage.bucket_node(tr, head));
        }
        for s in &live {
            buckets.extend(stage.memo.decl.body_buckets[*s as usize].iter().copied());
        }
        buckets.sort_unstable();
        buckets.dedup();
        for &b in &buckets {
            db.demand(&mut stage, QueryKey::one(kind::IMPLS_FOR, b))?;
            db.demand(&mut stage, QueryKey::one(kind::OVERLAP_CHECK, b))?;
            let (_, _, head) = stage.memo.ids.row(b);
            let h = stage.head_node(head);
            db.demand(&mut stage, QueryKey::one(kind::MEMBERS_OF, h))?;
        }
        db.demand(&mut stage, QueryKey::unit(kind::INFINITE_SIZE))?;

        // 4. The plan: which bodies are red.
        let bodies: Vec<u32> = live
            .iter()
            .copied()
            .filter(|&s| {
                let def = stage.memo.decl.def[s as usize];
                def != fors_fir::NO_DEF
                    && stage
                        .sigs
                        .defs
                        .get(def)
                        // I11: a `const`'s initialiser is a body too
                        // (design §7.1 phase 6; `Wf::bodies_selected`).
                        .is_some_and(|r| {
                            matches!(
                                r.kind,
                                fors_index::DeclKind::Fn | fors_index::DeclKind::Const
                            )
                        })
            })
            .collect();
        let mut red: Vec<u32> = Vec::new();
        for &s in &bodies {
            if db.is_red(&mut stage, QueryKey::one(kind::CHECK_BODY, s))? {
                red.push(s);
            }
        }
        let red_defs: Vec<DefId> = {
            let mut v: Vec<DefId> = red
                .iter()
                .map(|&s| stage.memo.decl.def[s as usize])
                .filter(|d| *d != fors_fir::NO_DEF)
                .collect();
            v.sort_unstable_by_key(|d| d.0);
            v
        };
        drop(stage);
        if db.is_cancelled() {
            return Err(Cancelled);
        }

        // 5. ONE body phase, for exactly the red set.
        let body: BodyPhase = crate::check_bodies(
            &mut sigs,
            interner,
            if red_defs.len() == bodies.len() {
                Bodies::All
            } else {
                Bodies::Only(&red_defs)
            },
            false,
        );

        // 6. The `check_body` nodes.
        let mut def_key = vec![0u64; sigs.defs.len()];
        for (def, row) in sigs.defs.user_defs() {
            def_key[def.index()] = memo
                .file_keys
                .get(row.file.index())
                .and_then(|ks| ks.get(row.decl.index()))
                .copied()
                .unwrap_or(0);
        }
        let (sig_diags, loose) = attribute(&sigs.diagnostics, &sigs, memo);
        let mut body_diags: HashMap<u32, Vec<Diagnostic>> = HashMap::new();
        for &d in &red_defs {
            body_diags.insert(d.0, Vec::new());
        }
        let (attributed, body_loose) = attribute(&body.diagnostics, &sigs, memo);
        for (def, ds) in attributed {
            body_diags.insert(def, ds);
        }
        let mut loose = loose;
        loose.extend(body_loose);
        let mut stage = StageB {
            memo,
            files,
            parses,
            interner,
            resolved: &resolved,
            sigs: &sigs,
            def_key,
            body_diags,
            body_deps: body
                .deps
                .iter()
                .map(|(d, s)| (d.0, s.defs().to_vec()))
                .collect(),
            body_buckets: body.buckets.iter().map(|(d, b)| (d.0, b.clone())).collect(),
            sig_diags,
            loose,
            row_key: Vec::new(),
            bucket_index: HashMap::new(),
            head_index: HashMap::new(),
            module_by_stable: HashMap::new(),
            module_stable: Vec::new(),
            key_module: HashMap::new(),
            head_module: HashMap::new(),
            children: HashMap::new(),
            impl_row_of: HashMap::new(),
            sig_buckets: HashMap::new(),
            builtin_key: HashMap::new(),
        }
        .index();
        for &s in &red {
            db.demand(&mut stage, QueryKey::one(kind::CHECK_BODY, s))?;
        }
        db.demand(&mut stage, QueryKey::unit(kind::LOOSE_DIAGS))?;
        // A body may have asked about a bucket nobody had asked about before
        // (including an EMPTY one). Its `impls_for` node exists now because
        // `check_body` read it; `overlap_check` and `members_of` are demanded
        // here so the node set is closed at the end of every revision rather
        // than one revision late.
        let mut fresh: Vec<u32> = Vec::new();
        for &s in &red {
            fresh.extend(stage.memo.decl.body_buckets[s as usize].iter().copied());
        }
        fresh.sort_unstable();
        fresh.dedup();
        for &b in &fresh {
            db.demand(&mut stage, QueryKey::one(kind::OVERLAP_CHECK, b))?;
            let (_, _, head) = stage.memo.ids.row(b);
            let h = stage.head_node(head);
            db.demand(&mut stage, QueryKey::one(kind::MEMBERS_OF, h))?;
        }

        // The oracle (module docs): every green `signature_of` must still
        // agree with the fresh signature phase.
        if *paranoid {
            for &s in &live {
                let def = stage.memo.decl.def[s as usize];
                if def == fors_fir::NO_DEF {
                    continue;
                }
                let fresh = stage.sigs.fir.sigs.sig_hash(def);
                if stage.memo.decl.sig_hash[s as usize] != fresh {
                    oracle_failures.push(format!(
                        "signature_of({:#018x}) cached {:#034x}, fresh {:#034x}",
                        stage.memo.decl.key[s as usize],
                        stage.memo.decl.sig_hash[s as usize],
                        fresh
                    ));
                }
            }
        }
        drop(stage);
        *last_stats = db.stats();
        Ok(())
    }

    /// Design §9's printing walk: over `decl_keys` in canonical order, taking
    /// every diagnostic from the memo and re-rendering it against this
    /// revision's declaration origins. The result is byte-identical cold or
    /// after an edit and a revert, because nothing in it depends on which
    /// nodes happened to be recomputed.
    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        let mut out: Vec<Diagnostic> = Vec::new();
        for f in 0..self.files.len() {
            if !self.files[f].live {
                continue;
            }
            for &slot in &self.memo.file_slots[f] {
                let Some(site) = self.memo.decl.site[slot as usize] else {
                    continue;
                };
                if site.file.index() != f {
                    continue;
                }
                for d in &self.memo.decl.sig_diags[slot as usize] {
                    out.push(d.render(site.file, site.origin));
                }
                for d in &self.memo.decl.body_diags[slot as usize] {
                    out.push(d.render(site.file, site.origin));
                }
            }
        }
        for (slot, d) in &self.memo.infinite {
            if let Some(site) = self.memo.decl.site[*slot as usize]
                && self.files[site.file.index()].live
            {
                out.push(d.render(site.file, site.origin));
            }
        }
        out.extend(self.memo.loose.iter().cloned());
        sort_diagnostics(&mut out);
        out
    }

    /// The `--stats` block.
    pub fn render_stats(&self) -> String {
        self.last_stats.render(&kind::NAMES)
    }
}

/// Splits a diagnostic list by the declaration whose byte range contains it,
/// returning `(per-`DefId`, the ones inside no declaration)`.
fn attribute(
    ds: &[Diagnostic],
    sigs: &Signatures<'_>,
    memo: &Memo,
) -> (HashMap<u32, Vec<Diagnostic>>, Vec<Diagnostic>) {
    // One sorted (file, start, end, def) table per call: a diagnostic is
    // placed in the INNERMOST declaration that contains it, which for a
    // method inside an impl is the method.
    let mut spans: Vec<(u32, u32, u32, DefId)> = Vec::new();
    for (def, row) in sigs.defs.user_defs() {
        let Some(decls) = memo.decls.get(row.file.index()).and_then(|d| d.as_ref()) else {
            continue;
        };
        let f = &sigs.files[row.file.index()];
        let node = row.node as usize;
        let (a, b) = f.tree.token_range(node);
        let start = f.tokens.starts.get(a as usize).copied().unwrap_or(0);
        let end = f
            .tokens
            .starts
            .get(b as usize)
            .copied()
            .unwrap_or_else(|| f.tokens.source_len());
        let _ = decls;
        spans.push((row.file.0, start, end, def));
    }
    // Innermost wins: a longer span sorts first, so the LAST match is the
    // tightest.
    spans.sort_unstable_by_key(|&(f, s, e, d)| (f, s, std::cmp::Reverse(e), d.0));
    let mut out: HashMap<u32, Vec<Diagnostic>> = HashMap::new();
    let mut loose: Vec<Diagnostic> = Vec::new();
    for d in ds {
        let mut best: Option<DefId> = None;
        let mut best_len = u32::MAX;
        for &(f, s, e, def) in &spans {
            if f == d.file.0 && s <= d.start && d.start < e.max(s + 1) && e - s < best_len {
                best = Some(def);
                best_len = e - s;
            }
        }
        match best {
            Some(def) => out.entry(def.0).or_default().push(d.clone()),
            None => loose.push(d.clone()),
        }
    }
    (out, loose)
}
