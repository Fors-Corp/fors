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
    /// Ch08 Rule 17 prelude module (`io`, `fs`, ...), denoting `std.<name>`.
    /// Carries the real `ModuleId` only when that `std` module is part of
    /// this build; the corpus never ships `std`, so further segments on an
    /// unbacked prelude module are left deferred (see crate docs).
    PreludeModule(Symbol, Option<ModuleId>),
    /// The name of a `use` that failed (already diagnosed): using it is
    /// not a second error.
    Poisoned,
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
    /// Rule 22 assigns to the checker. Never paired with a diagnostic.
    Deferred,
}

/// One file's name-use side table: parallel to a `Tree`'s nodes, index-
/// ordered (deterministic, no hashing) and populated only at nodes that
/// are name-use positions (Rule 14/16/25).
#[derive(Default)]
pub struct NameUseTable {
    pub node: Vec<u32>,
    pub target: Vec<ResolvedTarget>,
}

impl NameUseTable {
    pub fn push(&mut self, node: u32, target: ResolvedTarget) {
        self.node.push(node);
        self.target.push(target);
    }
}
