//! What a name-use node resolves to (ch08 "Entity", "Deferred segment").

use fors_index::{DeclId, FileId, ModuleId, Symbol};

/// A module-scope (or prelude) entity: what a name denotes once resolved
/// (ch08 Definitions "Entity"). Locals/params/gparams/`Self` are not here:
/// they are [`ResolvedTarget::Local`], since they live only within one
/// file's function body, addressed by the tree node that introduced them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Entity {
    Item { file: FileId, decl: DeclId },
    Module(ModuleId),
    /// An enum variant: the enum's own `(file, decl)` plus the variant's
    /// ordinal among that enum's distinct variant names — not a tree node,
    /// so an edit elsewhere in the defining file cannot change it.
    Variant { file: FileId, decl: DeclId, index: u32 },
    /// Ch08 Rule 17 prelude type/trait (`i32`, `Str`, `Option`, ...).
    PreludeType(Symbol),
    /// Ch08 Rule 17 prelude value (`some`, `none`, `reduce`).
    PreludeValue(Symbol),
    /// A module of Ch08 Rule 17's SYNTHETIC `std` table (`io`, `fs`,
    /// `mem`, ...), bound by a `use std.<m>;` in a build that ships no
    /// `std` source (owner decision 2026-09-19, round 5, D3). The variant
    /// keeps its round-2 name so the enum stays additive; it is no longer
    /// a prelude name — nothing puts it in scope but an import. The
    /// `Option<ModuleId>` is `None` for exactly that case (a real
    /// `std.<m>` in the build binds `Entity::Module` instead), so every
    /// further segment on one is deferred to the checker (Rule 16, 22).
    PreludeModule(Symbol, Option<ModuleId>),
    /// The name of a `use` that failed (already diagnosed): using it is
    /// not a second error.
    Poisoned,
}

// MARC: the type-checker design (§4.4) asks for `ResolvedTarget::Deferred`
// to carry *why* a path was left unresolved, so the checker (ch09 Rule 22)
// can tell "already diagnosed here, say nothing" apart from "a member tail
// that genuinely needs a type" without re-deriving it from the path shape.
// This is a data-shape change to an existing variant rather than a new one
// appended at the end; every call site in this crate is updated in the
// same change (there is no third-party consumer of this pre-1.0 crate),
// and the variant's *name* is untouched. `hash_bytes`/interning-style
// "append only" applies most sharply to codes and ids that outlive one
// build (a `Code`, a `Symbol`); this is neither.
/// Why [`ResolvedTarget::Deferred`] left a name-use node unresolved.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeferReason {
    /// A diagnostic was already pushed at this node (an unresolved head,
    /// a path ending on a module, a non-`pub` segment, a poisoned name):
    /// the checker must stay silent here, not emit a second diagnostic.
    Diagnosed,
    /// The path is qualified by a `PreludeModule(_, None)` segment
    /// (`std.<m>` with no `std` in this build, round 5 D3): nothing is
    /// wrong yet, but no further segment on it can resolve either.
    StdAbsent,
    /// A genuinely deferred tail (Rule 22): a member/field/method name or
    /// a dot-literal pattern that needs a type to resolve. Never paired
    /// with a diagnostic at this node.
    Member,
}

/// What one name-use tree node resolves to: an [`Entity`], a local binding
/// (addressed by the node that introduced it), or left to the checker
/// (ch08 Rule 22) — recorded, never silently dropped, and never itself a
/// diagnostic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ResolvedTarget {
    Entity(Entity),
    /// A binding: `local` is the introducing node (`Binding`, `Param`,
    /// `GParam`, `CParam`, the `with` identifier's own token position
    /// recorded via its owning `WithStmt` node, `Handler`'s identifier via
    /// the `Handler` node, or the implicit `Self` via its `ImplDecl`/
    /// `TraitDecl` node).
    Local { node: u32 },
    /// Unresolved on purpose: a deferred segment (Rule 16) or anything
    /// Rule 22 assigns to the checker. Never paired with a diagnostic
    /// unless `reason` is [`DeferReason::Diagnosed`].
    Deferred { reason: DeferReason },
}

/// One file's name-use side table: parallel to a `Tree`'s nodes, index-
/// ordered (deterministic, no hashing) and populated only at nodes that
/// are name-use positions (Rule 14/16/25).
#[derive(Default)]
pub struct NameUseTable {
    pub node: Vec<u32>,
    pub target: Vec<ResolvedTarget>,
    // MARC: design §4.4's "segments consumed by resolve_path" (ch09 Rule
    // 43 needs to know how much of a dotted path the resolver already
    // spent before deferring the rest to member lookup). `u8` is enough:
    // the parser bounds any one path's segment count far below 255.
    /// How many of the path's segments `target` accounts for (1 once any
    /// entity/local is reached, `idx` while still walking a multi-segment
    /// path, 0 for an unresolved head). Same length and index order as
    /// [`Self::node`]/[`Self::target`].
    pub consumed: Vec<u8>,
    sorted: bool,
}

impl NameUseTable {
    /// Records `target` at `node`, having consumed `consumed` of the
    /// path's segments (1 for anything that is not a multi-segment path).
    pub fn push(&mut self, node: u32, target: ResolvedTarget, consumed: u8) {
        self.node.push(node);
        self.target.push(target);
        self.consumed.push(consumed);
        self.sorted = false;
    }

    /// Sorts the table by node (stable: within one node, insertion order
    /// is preserved) and asserts no two entries share a node — every name-
    /// use position is recorded exactly once. Call once resolution of a
    /// file's bodies is done and before [`Self::target_of`] is used.
    pub fn finish(&mut self) {
        let mut order: Vec<usize> = (0..self.node.len()).collect();
        order.sort_by_key(|&i| self.node[i]);
        for w in order.windows(2) {
            assert_ne!(self.node[w[0]], self.node[w[1]], "a name-use node was recorded twice: {}", self.node[w[0]]);
        }
        let node = order.iter().map(|&i| self.node[i]).collect();
        let target = order.iter().map(|&i| self.target[i]).collect();
        let consumed = order.iter().map(|&i| self.consumed[i]).collect();
        self.node = node;
        self.target = target;
        self.consumed = consumed;
        self.sorted = true;
    }

    /// The recorded target for `node`, by binary search. Requires
    /// [`Self::finish`] to have run (panics otherwise, since an unsorted
    /// table cannot be searched).
    pub fn target_of(&self, node: u32) -> Option<ResolvedTarget> {
        assert!(self.sorted, "NameUseTable::target_of called before finish()");
        self.node.binary_search(&node).ok().map(|i| self.target[i])
    }
}
