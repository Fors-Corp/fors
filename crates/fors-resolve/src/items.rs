//! Module-scope item/import tables (ch08 R4-R6, R9-R10, R12, R13, R15,
//! R17, R27): the whole-build linking step. A module's own item rows
//! depend only on its `DeclTable`; resolving its `use`s reads nothing of
//! another module but that module's export rows ([`ModuleScope::export`]),
//! already complete because modules are linked in dependency order (R7).
//! Body resolution sees other modules only through [`Exports`].

use std::collections::HashMap;

use fors_index::{DeclId, DeclKind, DeclTable, FileId, Interner, ModuleId, ModuleTable, Segments, Symbol, Visibility};
use fors_lex::{TokenKind, Tokens};
use fors_syntax::{NodeKind, Tree};

use crate::diag::{Code, Diagnostic};
use crate::paths::{byte_range, own_span, segments_with_ranges};
use crate::prelude;
use crate::target::Entity;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Origin {
    Item,
    Use,
}

/// What kind of entity a module-scope row denotes, as far as importers
/// may know without opening the defining file.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RowKind {
    Item(DeclKind),
    Module,
    /// A `use` that failed to resolve: the name is bound so its uses do
    /// not each report N0014 on top of the import's own diagnostic.
    Poisoned,
}

/// One row of a module scope, copied out of the columns.
#[derive(Clone, Copy)]
pub struct Row<'a> {
    pub entity: Entity,
    pub kind: RowKind,
    pub origin: Origin,
    /// Variant names when the row denotes an enum (Rule 16), in
    /// declaration order; carried along re-exports so an importer never
    /// needs the defining module's tree.
    pub variants: &'a [Symbol],
}

/// One module's name table (struct-of-arrays, rows in insertion order —
/// own items in source order, then imports in source order). A row is
/// *exported* when it is an item (whatever its visibility, so importers
/// can tell "private", Rule 10, from "absent") or a `pub use`.
#[derive(Default)]
pub struct ModuleScope {
    name: Vec<Symbol>,
    entity: Vec<Entity>,
    kind: Vec<RowKind>,
    origin: Vec<Origin>,
    vis: Vec<Visibility>,
    sig_hash: Vec<u128>,
    var_start: Vec<u32>,
    var_len: Vec<u32>,
    variant_names: Vec<Symbol>,
    /// Lookup only, never iterated.
    index: HashMap<Symbol, u32>,
    /// Last segment of every `pub use` path, resolved or not: with the
    /// `pub` item rows this decides Rule 4's module/item tie without
    /// depending on the order modules are linked in.
    pub_use_names: Vec<Symbol>,
    /// Inside package `std` the prelude module names are not provided
    /// (Rule 17).
    in_std: bool,
}

/// The result of asking a module for one of its names from outside.
pub enum Export<'a> {
    Public(Row<'a>),
    /// A non-`pub` item (Rule 10).
    Private,
}

impl ModuleScope {
    fn row(&self, i: usize) -> Row<'_> {
        let (s, l) = (self.var_start[i] as usize, self.var_len[i] as usize);
        Row { entity: self.entity[i], kind: self.kind[i], origin: self.origin[i], variants: self.variant_names.get(s..s + l).unwrap_or(&[]) }
    }

    pub fn in_std(&self) -> bool {
        self.in_std
    }

    /// Rule 14's last step, for code inside this module.
    pub fn lookup(&self, name: Symbol) -> Option<Row<'_>> {
        self.index.get(&name).map(|&i| self.row(i as usize))
    }

    /// What another module may learn about `name` (Rules 4, 5, 10, 16).
    pub fn export(&self, name: Symbol) -> Option<Export<'_>> {
        let i = *self.index.get(&name)? as usize;
        match (self.vis[i], self.origin[i]) {
            (Visibility::Public, _) => Some(Export::Public(self.row(i))),
            (_, Origin::Item) => Some(Export::Private),
            _ => None,
        }
    }

    fn push(&mut self, name: Symbol, entity: Entity, kind: RowKind, origin: Origin, vis: Visibility, sig_hash: u128, variants: &[Symbol]) {
        let i = self.name.len() as u32;
        self.name.push(name);
        self.entity.push(entity);
        self.kind.push(kind);
        self.origin.push(origin);
        self.vis.push(vis);
        self.sig_hash.push(sig_hash);
        self.var_start.push(self.variant_names.len() as u32);
        self.var_len.push(variants.len() as u32);
        self.variant_names.extend_from_slice(variants);
        self.index.insert(name, i);
    }

    /// The export table as text, one line per exported row, sorted by
    /// name: everything about this module that resolving an importer can
    /// depend on. Two builds with equal signatures for module A give
    /// identical results for every module other than A.
    pub fn export_signature(&self, interner: &Interner) -> Vec<String> {
        let mut out = Vec::new();
        for i in 0..self.name.len() {
            let public = self.vis[i] == Visibility::Public;
            if !public && self.origin[i] != Origin::Item {
                continue;
            }
            let name = String::from_utf8_lossy(interner.resolve(self.name[i])).into_owned();
            if !public {
                out.push(format!("{name} private"));
                continue;
            }
            let vars: Vec<String> = self.row(i).variants.iter().map(|&v| String::from_utf8_lossy(interner.resolve(v)).into_owned()).collect();
            out.push(format!("{name} pub {:?} {:?} sig={:032x} variants={}", self.kind[i], self.entity[i], self.sig_hash[i], vars.join(",")));
        }
        out.sort();
        out
    }
}

/// Everything the whole build's linking step produces.
#[derive(Default)]
pub struct Universe {
    scopes: Vec<ModuleScope>,
    prelude: Prelude,
    has_std: bool,
}

/// Rule 17's closed list, interned once. Lookup only, never iterated.
#[derive(Default)]
pub struct Prelude(HashMap<Symbol, Entity>);

impl Prelude {
    /// Rule 17 lookup for a name used inside `scope`'s module.
    pub fn get(&self, scope: &ModuleScope, name: Symbol) -> Option<Entity> {
        match self.0.get(&name) {
            Some(Entity::PreludeModule(..)) if scope.in_std => None,
            e => e.copied(),
        }
    }
}

/// The only view of other modules that body resolution gets: export
/// tables, never scopes, trees or bodies.
#[derive(Clone, Copy)]
pub struct Exports<'a> {
    scopes: &'a [ModuleScope],
}

impl<'a> Exports<'a> {
    pub fn get(&self, m: ModuleId, name: Symbol) -> Option<Export<'a>> {
        self.scopes.get(m.index())?.export(name)
    }
}

impl Universe {
    pub fn scope(&self, file: FileId) -> Option<&ModuleScope> {
        self.scopes.get(file.index())
    }

    pub fn exports(&self) -> Exports<'_> {
        Exports { scopes: &self.scopes }
    }

    pub fn prelude(&self) -> &Prelude {
        &self.prelude
    }
}

fn build_prelude(interner: &mut Interner, modules: &ModuleTable) -> Prelude {
    let mut out = HashMap::new();
    for n in prelude::PRELUDE_TYPES.iter().chain(&prelude::PRELUDE_TYPES2).chain(&prelude::PRELUDE_TYPES3).chain(&prelude::PRELUDE_TYPES4) {
        let s = interner.intern(n);
        out.insert(s, Entity::PreludeType(s));
    }
    for n in &prelude::PRELUDE_VALUES {
        let s = interner.intern(n);
        out.insert(s, Entity::PreludeValue(s));
    }
    let std_sym = interner.intern(b"std");
    for n in &prelude::PRELUDE_MODULES {
        let s = interner.intern(n);
        out.insert(s, Entity::PreludeModule(s, modules.find(&[std_sym, s])));
    }
    Prelude(out)
}

fn is_sig(tokens: &Tokens, i: usize) -> bool {
    !tokens.kinds[i].is_trivia()
}

/// First `Ident`/`Underscore` token a node owns directly, skipping a
/// leading contextual `set` (closure/param conventions) and any leading
/// `pub` (fields): good enough for `Param`, `CParam`, `GParam`, `Field`,
/// `EVariant` and `Binding`, whose only other leading tokens are keywords.
pub fn binder_name(
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    node: usize,
) -> Option<(Symbol, (u32, u32))> {
    let (first, end) = own_span(tree, node);
    let mut i = first as usize;
    let end = end as usize;
    let mut prev_was_set = false;
    while i < end {
        if is_sig(tokens, i) {
            if tokens.kinds[i] == TokenKind::Ident && tokens.text(i, source) == b"set" && !prev_was_set {
                prev_was_set = true;
                i += 1;
                continue;
            }
            if tokens.kinds[i] == TokenKind::Underscore {
                return None;
            }
            if tokens.kinds[i] == TokenKind::Ident {
                return Some((interner.intern(tokens.text(i, source)), tokens.range(i)));
            }
        }
        i += 1;
    }
    None
}

/// Enum variant names for one enum's `EnumDecl` node (Rule 27's duplicate
/// check, Rule 16's enum-item case).
fn collect_variants(
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    enum_node: usize,
    file: usize,
    diags: &mut Vec<(usize, Diagnostic)>,
) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    for child in tree.children(enum_node) {
        if tree.kinds[child] != NodeKind::EVariant {
            continue;
        }
        let Some((name, _range)) = binder_name(tree, tokens, source, interner, child) else { continue };
        if out.contains(&name) {
            let r = byte_range(tree, tokens, child);
            diags.push((file, Diagnostic::new(
                r.0,
                r.1,
                Code::N(27),
                "duplicate variant name in one enum".to_string(),
            )));
        } else {
            out.push(name);
        }
    }
    out
}

/// Field names of one `StructDecl`/struct-form `EVariant` (Rule 27).
fn check_field_dups(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner, node: usize, file: usize, diags: &mut Vec<(usize, Diagnostic)>) {
    let mut seen: Vec<Symbol> = Vec::new();
    for child in tree.children(node) {
        if tree.kinds[child] != NodeKind::Field {
            continue;
        }
        // Rule 11: `pub` on a field inside an `evariant` is always an error;
        // callers of this function on an `EVariant`'s fields pass that in.
        let Some((name, _)) = binder_name(tree, tokens, source, interner, child) else { continue };
        if seen.contains(&name) {
            let r = byte_range(tree, tokens, child);
            diags.push((file, Diagnostic::new(r.0, r.1, Code::N(27), "duplicate field name".to_string())));
        } else {
            seen.push(name);
        }
    }
}

/// Whether a `UseDecl` node is `pub use` (the `pub` prefixes the whole
/// comma-separated decl, ch08 R3).
fn use_decl_is_pub(tree: &Tree, tokens: &Tokens, node: usize) -> bool {
    let (first, end) = tree.token_range(node);
    for i in first as usize..end as usize {
        if is_sig(tokens, i) {
            return tokens.kinds[i] == TokenKind::KwPub;
        }
    }
    false
}

/// A `UseItem`'s `"as" ident` alias, if it has one (ch07 grammar; ch08
/// R3-6 -- owner decision 2026-09-19, round 3, D2). The `"as"` and the
/// alias identifier are tokens `UseItem` owns directly, after its one
/// `Path` child.
fn use_item_alias(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner, node: usize) -> Option<Symbol> {
    let (first, end) = tree.token_range(node);
    let mut saw_as = false;
    for i in first as usize..end as usize {
        if !is_sig(tokens, i) {
            continue;
        }
        if saw_as {
            return if tokens.kinds[i] == TokenKind::Ident { Some(interner.intern(tokens.text(i, source))) } else { None };
        }
        if tokens.kinds[i] == TokenKind::KwAs {
            saw_as = true;
        }
    }
    None
}

pub struct FileCtx<'a> {
    pub tree: &'a Tree,
    pub tokens: &'a Tokens,
    pub source: &'a [u8],
    pub decls: &'a DeclTable,
}

/// Every `TypeApp` node in a subtree (a type may nest generics, so a
/// leaked private type can sit under `Own[Hidden]` as well as bare).
fn find_type_apps(tree: &Tree, node: usize, out: &mut Vec<usize>) {
    if tree.kinds[node] == NodeKind::TypeApp {
        out.push(node);
    }
    for c in tree.children(node) {
        find_type_apps(tree, c, out);
    }
}

fn sig_type_apps(tree: &Tree, fn_node: usize, out: &mut Vec<usize>) {
    if let Some(sig) = tree.children(fn_node).find(|&c| tree.kinds[c] == NodeKind::FnSig) {
        for c in tree.children(sig) {
            if tree.kinds[c] != NodeKind::Contract {
                find_type_apps(tree, c, out);
            }
        }
    }
}

fn own_has_pub(f: &FileCtx, node: usize) -> bool {
    let (fs, fe) = own_span(f.tree, node);
    (fs as usize..fe as usize).any(|t| f.tokens.kinds.get(t) == Some(&TokenKind::KwPub))
}

/// Ch08 Rule 12: a `pub` item's signature must not name a non-`pub` item
/// of its own module. Syntactic, per the rule's own text — each
/// signature `TypeApp`'s first segment is looked up in this module's
/// (complete) item rows and its visibility inspected.
fn check_signature_leaks(interner: &mut Interner, f: &FileCtx, m: usize, scope: &ModuleScope, diags: &mut Vec<(usize, Diagnostic)>) {
    let is_pub_item = |scope: &ModuleScope, name: Symbol| {
        scope.index.get(&name).is_some_and(|&r| scope.origin[r as usize] == Origin::Item && scope.vis[r as usize] == Visibility::Public)
    };
    for i in 0..f.decls.len() {
        if f.decls.parent[i] != fors_index::decl::NO_PARENT {
            continue;
        }
        let kind = f.decls.kind[i];
        if kind != DeclKind::Impl && f.decls.vis[i] != Visibility::Public {
            continue;
        }
        let node = f.decls.node[i] as usize;
        let mut sig_types: Vec<usize> = Vec::new();
        match kind {
            DeclKind::Fn | DeclKind::ExternFn => sig_type_apps(f.tree, node, &mut sig_types),
            DeclKind::Struct => {
                for c in f.tree.children(node) {
                    match f.tree.kinds[c] {
                        NodeKind::Generics => find_type_apps(f.tree, c, &mut sig_types),
                        NodeKind::Field if own_has_pub(f, c) => find_type_apps(f.tree, c, &mut sig_types),
                        _ => {}
                    }
                }
            }
            DeclKind::Enum => {
                for c in f.tree.children(node) {
                    if matches!(f.tree.kinds[c], NodeKind::Generics | NodeKind::EVariant) {
                        find_type_apps(f.tree, c, &mut sig_types);
                    }
                }
            }
            DeclKind::Trait => {
                for c in f.tree.children(node) {
                    match f.tree.kinds[c] {
                        NodeKind::TraitItem | NodeKind::FnDecl => sig_type_apps(f.tree, c, &mut sig_types),
                        NodeKind::Attribute => {}
                        _ => find_type_apps(f.tree, c, &mut sig_types),
                    }
                }
            }
            DeclKind::Const => {
                // The type is the first non-attribute child; the rest is
                // the initialiser, which is not signature.
                if let Some(t) = f.tree.children(node).find(|&c| f.tree.kinds[c] != NodeKind::Attribute) {
                    find_type_apps(f.tree, t, &mut sig_types);
                }
            }
            DeclKind::Impl => {
                // "every `pub` method in an `impl` whose type is `pub`":
                // the implementing type is the last header type.
                let headers: Vec<usize> = f
                    .tree
                    .children(node)
                    .filter(|&c| !matches!(f.tree.kinds[c], NodeKind::Generics | NodeKind::FnDecl | NodeKind::TraitItem | NodeKind::Attribute | NodeKind::AssocTypeDef | NodeKind::AssocTypeDecl | NodeKind::Error))
                    .collect();
                let ty = headers.last().copied();
                let ty_pub = ty.filter(|&t| f.tree.kinds[t] == NodeKind::TypeApp).is_some_and(|t| {
                    segments_with_ranges(f.tree, f.tokens, f.source, interner, t).first().is_some_and(|&(n, _)| is_pub_item(scope, n))
                });
                if !ty_pub {
                    continue;
                }
                // Round 4 (Rule 12): in an impl of a `pub` trait for a
                // `pub` type, the right-hand side of every `type A = T;`
                // is signature. A prelude or imported trait is `pub`.
                let head_pub = |t: usize, interner: &mut Interner| {
                    f.tree.kinds[t] == NodeKind::TypeApp
                        && segments_with_ranges(f.tree, f.tokens, f.source, interner, t).first().is_some_and(|&(n, _)| is_pub_item(scope, n) || scope.index.get(&n).is_none_or(|&r| scope.origin[r as usize] != Origin::Item))
                };
                if headers.len() == 2 && head_pub(headers[0], interner) {
                    for c in f.tree.children(node) {
                        if f.tree.kinds[c] == NodeKind::AssocTypeDef {
                            find_type_apps(f.tree, c, &mut sig_types);
                        }
                    }
                }
                for row in 0..f.decls.len() {
                    if f.decls.parent[row] == i as u32 && f.decls.vis[row] == Visibility::Public {
                        sig_type_apps(f.tree, f.decls.node[row] as usize, &mut sig_types);
                    }
                }
            }
            _ => continue,
        }
        for tnode in sig_types {
            let segs = segments_with_ranges(f.tree, f.tokens, f.source, interner, tnode);
            let Some(&(name, range)) = segs.first() else { continue };
            let Some(&r) = scope.index.get(&name) else { continue };
            let r = r as usize;
            if scope.origin[r] == Origin::Item && scope.vis[r] == Visibility::Private {
                let leaked = String::from_utf8_lossy(interner.resolve(name)).into_owned();
                diags.push((m, Diagnostic::new(range.0, range.1, Code::N(12), format!("a `pub` item's signature names the non-`pub` item `{leaked}` of its own module"))));
            }
        }
    }
}

/// Post-order DFS over the "uses" edges: dependencies before dependents,
/// so an importer is processed only after every module it `use`s. A
/// cycle (already reported by `fors_index`) cannot stall this — a node
/// re-entered while `in_progress` just returns, and the frame that
/// started the cycle still finishes and gets pushed once its stack
/// unwinds — so the order stays a total, deterministic sequence even
/// then. Iteration itself starts from the lexicographically least module
/// name so two builds of the same files always link in the same order.
fn dependency_order(n: usize, edges: &[(ModuleId, ModuleId)], modules: &ModuleTable, interner: &Interner) -> Vec<usize> {
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(from, to) in edges {
        adj[from.index()].push(to.index());
    }
    for l in &mut adj {
        l.sort_unstable();
        l.dedup();
    }
    let name_bytes: Vec<Vec<u8>> = modules.name.iter().map(|s| fors_index::module::join_dotted(interner, s).into_bytes()).collect();
    let mut order_idx: Vec<usize> = (0..n).collect();
    order_idx.sort_by(|&a, &b| name_bytes[a].cmp(&name_bytes[b]));

    const UNSEEN: u8 = 0;
    const IN_PROGRESS: u8 = 1;
    const DONE: u8 = 2;
    let mut state = vec![UNSEEN; n];
    let mut out = Vec::with_capacity(n);

    fn visit(u: usize, adj: &[Vec<usize>], state: &mut [u8], out: &mut Vec<usize>) {
        if state[u] != UNSEEN {
            return;
        }
        state[u] = IN_PROGRESS;
        for &v in &adj[u] {
            visit(v, adj, state, out);
        }
        state[u] = DONE;
        out.push(u);
    }
    for &u in &order_idx {
        visit(u, &adj, &mut state, &mut out);
    }
    out
}

/// Builds every module's name table (Rules 4-6, 9, 10, 13, 15, 17) and
/// every enum's variant list (Rule 16, 27); also runs the field/member
/// duplicate checks (Rule 27) and the syntactic half of Rule 11 (`pub` on
/// an `evariant` field, `pub` on a trait-`impl` method).
pub fn build_universe(
    interner: &mut Interner,
    modules: &ModuleTable,
    edges: &[(ModuleId, ModuleId)],
    files: &[FileCtx],
) -> (Universe, Vec<(usize, Diagnostic)>) {
    let n = files.len();
    let mut diags = Vec::new();
    let mut universe = Universe { scopes: (0..n).map(|_| ModuleScope::default()).collect(), prelude: build_prelude(interner, modules), has_std: false };
    let std_sym = interner.intern(b"std");
    universe.has_std = modules.name.iter().any(|n| n.first() == Some(&std_sym));

    // Pass 1: per-file, order-independent — own items, member dup checks.
    for (m, f) in files.iter().enumerate() {
        let Universe { scopes, prelude, .. } = &mut universe;
        let scope = &mut scopes[m];
        scope.in_std = modules.name.get(m).and_then(|s| s.first()) == Some(&std_sym);
        for i in 0..f.decls.len() {
            if f.decls.parent[i] != fors_index::decl::NO_PARENT {
                continue;
            }
            let kind = f.decls.kind[i];
            let node = f.decls.node[i] as usize;
            match kind {
                DeclKind::Struct => check_field_dups(f.tree, f.tokens, f.source, interner, node, m, &mut diags),
                DeclKind::Enum => {
                    for child in f.tree.children(node) {
                        if f.tree.kinds[child] == NodeKind::EVariant {
                            // pub on a field inside a variant (Rule 11) is
                            // always an error, so scan directly.
                            for fld in f.tree.children(child) {
                                if f.tree.kinds[fld] != NodeKind::Field {
                                    continue;
                                }
                                let (fs, fe) = own_span(f.tree, fld);
                                for t in fs as usize..fe as usize {
                                    if is_sig(f.tokens, t) && f.tokens.kinds[t] == TokenKind::KwPub {
                                        let r = f.tokens.range(t);
                                        diags.push((m, Diagnostic::new(
                                            r.0,
                                            r.1,
                                            Code::N(11),
                                            "`pub` on a field inside an enum variant is not allowed".to_string(),
                                        )));
                                    }
                                }
                            }
                            check_field_dups(f.tree, f.tokens, f.source, interner, child, m, &mut diags);
                        }
                    }
                }
                DeclKind::Impl | DeclKind::Trait => {
                    let is_trait_impl = kind == DeclKind::Impl && {
                        // Rule 21's orphan check needs types for the general
                        // case; here we only need: does this impl have a
                        // `for` (a trait impl)? `impl T { }` has no `for`.
                        // The `for` token sits between the impl's two
                        // header-type children, so it is not in `own_span`
                        // (which stops at the first child) — scan the
                        // whole node's own range instead.
                        let (fs, fe) = f.tree.token_range(node);
                        (fs as usize..fe as usize).any(|t| is_sig(f.tokens, t) && f.tokens.kinds[t] == TokenKind::KwFor)
                    };
                    // Rule 27 (round 4): methods and associated types
                    // share ONE table per trait and per impl; the later
                    // member, in source order, is the duplicate.
                    let mut members: Vec<(u32, Symbol, (u32, u32), bool)> = Vec::new();
                    for row in 0..f.decls.len() {
                        if f.decls.parent[row] == i as u32 {
                            if let Some(name) = f.decls.name[row] {
                                members.push((f.decls.range_start[row], name, (f.decls.range_start[row], f.decls.range_end[row]), false));
                            }
                        }
                    }
                    for c in f.tree.children(node) {
                        if matches!(f.tree.kinds[c], NodeKind::AssocTypeDecl | NodeKind::AssocTypeDef) {
                            if let Some((name, _)) = binder_name(f.tree, f.tokens, f.source, interner, c) {
                                let r = byte_range(f.tree, f.tokens, c);
                                members.push((r.0, name, r, true));
                            }
                        }
                    }
                    members.sort_by_key(|&(start, ..)| start);
                    let mut seen: Vec<Symbol> = Vec::new();
                    for &(_, name, r, is_type) in &members {
                        if seen.contains(&name) {
                            let msg = if is_type { "duplicate associated-type name in one impl/trait (methods and associated types share one table)" } else { "duplicate method name in one impl/trait" };
                            diags.push((m, Diagnostic::new(r.0, r.1, Code::N(27), msg.to_string())));
                        } else {
                            seen.push(name);
                        }
                    }
                    for row in 0..f.decls.len() {
                        if f.decls.parent[row] != i as u32 {
                            continue;
                        }
                        if is_trait_impl && f.decls.vis[row] == Visibility::Public {
                            let r = (f.decls.range_start[row], f.decls.range_end[row]);
                            diags.push((m, Diagnostic::new(r.0, r.1, Code::N(11), "`pub` on a trait-impl method is not allowed: it has the trait's visibility".to_string())));
                        }
                    }
                }
                _ => {}
            }
            let Some(name) = f.decls.name[i] else { continue };
            let range = (f.decls.range_start[i], f.decls.range_end[i]);
            let shown = String::from_utf8_lossy(interner.resolve(name)).into_owned();
            if prelude.get(scope, name).is_some() {
                diags.push((m, Diagnostic::new(range.0, range.1, Code::N(13), format!("item `{shown}` has a prelude name"))));
                continue;
            }
            if scope.index.contains_key(&name) {
                diags.push((m, Diagnostic::new(range.0, range.1, Code::N(13), format!("`{shown}` is already declared by an earlier item of this module"))));
                continue;
            }
            let variants = if kind == DeclKind::Enum { collect_variants(f.tree, f.tokens, f.source, interner, node, m, &mut diags) } else { Vec::new() };
            let entity = Entity::Item { file: FileId(m as u32), decl: DeclId(i as u32) };
            scope.push(name, entity, RowKind::Item(kind), Origin::Item, f.decls.vis[i], f.decls.sig_hash[i], &variants);
        }
        if !f.tree.is_empty() {
            for use_decl in f.tree.children(0) {
                if f.tree.kinds[use_decl] == NodeKind::UseDecl && use_decl_is_pub(f.tree, f.tokens, use_decl) {
                    for use_item in f.tree.children(use_decl).filter(|&c| f.tree.kinds[c] == NodeKind::UseItem) {
                        let Some(path_node) = f.tree.children(use_item).find(|&c| f.tree.kinds[c] == NodeKind::Path) else { continue };
                        let alias = use_item_alias(f.tree, f.tokens, f.source, interner, use_item);
                        let last = alias.or_else(|| segments_with_ranges(f.tree, f.tokens, f.source, interner, path_node).last().map(|&(s, _)| s));
                        if let Some(last) = last {
                            scope.pub_use_names.push(last);
                        }
                    }
                }
            }
        }
        check_signature_leaks(interner, f, m, scope, &mut diags);
    }

    // Pass 2: `use`/`pub use`, in dependency order (Rule 7).
    let order = dependency_order(n, edges, modules, interner);
    for m in order {
        let f = &files[m];
        if f.tree.is_empty() {
            continue;
        }
        for use_decl in f.tree.children(0) {
            if f.tree.kinds[use_decl] != NodeKind::UseDecl {
                continue;
            }
            let is_pub = use_decl_is_pub(f.tree, f.tokens, use_decl);
            for use_item in f.tree.children(use_decl) {
                if f.tree.kinds[use_item] != NodeKind::UseItem {
                    continue; // an `Error` child: the parser reported it
                }
                let Some(path_node) = f.tree.children(use_item).find(|&c| f.tree.kinds[c] == NodeKind::Path) else { continue };
                let segs_ranges = segments_with_ranges(f.tree, f.tokens, f.source, interner, path_node);
                let segs: Segments = segs_ranges.iter().map(|(s, _)| *s).collect();
                let whole_range = byte_range(f.tree, f.tokens, path_node);
                let alias = use_item_alias(f.tree, f.tokens, f.source, interner, use_item);
                resolve_use_path(interner, modules, &mut universe, edges, m, &segs, alias, whole_range, is_pub, &mut diags);
            }
        }
    }

    (universe, diags)
}

/// Whether module `src` reaches module `dst` along "uses" edges. Only
/// called on an import-error path, so a plain DFS per call is fine.
fn reaches(edges: &[(ModuleId, ModuleId)], src: usize, dst: usize) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![src];
    while let Some(u) = stack.pop() {
        if u == dst {
            return true;
        }
        if !seen.insert(u) {
            continue;
        }
        stack.extend(edges.iter().filter(|(f, _)| f.index() == u).map(|(_, t)| t.index()));
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn resolve_use_path(
    interner: &mut Interner,
    modules: &ModuleTable,
    universe: &mut Universe,
    edges: &[(ModuleId, ModuleId)],
    from: usize,
    segs: &[Symbol],
    alias: Option<Symbol>,
    range: (u32, u32),
    is_pub: bool,
    diags: &mut Vec<(usize, Diagnostic)>,
) {
    let Some(&sn) = segs.last() else { return };
    let prefix = &segs[..segs.len() - 1];
    let std_sym = interner.intern(b"std");
    // ch08 R3-6, owner decision 2026-09-19 round 3 (D2): "as" c" binds c,
    // not sn; sn (and every other path segment) is used only to resolve
    // the path itself, never as the bound name once an alias is given.
    let bound_name = alias.unwrap_or(sn);
    let bind = |universe: &mut Universe, entity: Entity, kind: RowKind, sig: u128, variants: &[Symbol], diags: &mut Vec<(usize, Diagnostic)>| {
        bind_use_name(universe, from, entity, kind, sig, variants, bound_name, range, is_pub, diags);
    };

    // `use std.<name>;` for one of Rule 17's prelude modules denotes that
    // prelude module even when this build ships no `std` (package `std`
    // is in every universe, Definitions).
    if segs.len() == 2 && segs[0] == std_sym && modules.find(segs).is_none() {
        if let Some(&e @ Entity::PreludeModule(..)) = universe.prelude.0.get(&sn) {
            bind(universe, e, RowKind::Module, 0, &[], diags);
            return;
        }
    }

    // Package `std` is in every universe but not in every build (the
    // corpus ships none): its modules cannot be checked then, and are not
    // guessed at.
    if segs[0] == std_sym && !universe.has_std {
        bind(universe, Entity::Poisoned, RowKind::Poisoned, 0, &[], diags);
        return;
    }

    let whole = modules.find(segs);
    let prefix_mod = if prefix.is_empty() { None } else { modules.find(prefix) };
    let sn_str = String::from_utf8_lossy(interner.resolve(sn)).into_owned();

    if let Some(mid) = whole {
        // Rule 4: a tie only when (b) "would also succeed", i.e. the
        // prefix module really has a `pub` name `sn` — `a.fors` beside
        // `a/b.fors` (Rule 24) is not by itself a tie.
        let tie = prefix_mod.is_some_and(|p| {
            let ps = &universe.scopes[p.index()];
            ps.pub_use_names.contains(&sn) || ps.index.get(&sn).is_some_and(|&r| ps.vis[r as usize] == Visibility::Public)
        });
        if tie {
            let name = fors_index::module::join_dotted(interner, segs);
            let pname = fors_index::module::join_dotted(interner, prefix);
            diags.push((from, Diagnostic::new(range.0, range.1, Code::N(4), format!("`{name}` is both the module `{name}` and the `pub` name `{sn_str}` of module `{pname}`"))));
            bind(universe, Entity::Poisoned, RowKind::Poisoned, 0, &[], diags);
            return;
        }
        if mid.index() == from {
            return; // Rule 8, already reported by `fors_index`.
        }
        bind(universe, Entity::Module(mid), RowKind::Module, 0, &[], diags);
        return;
    }

    let Some(pm) = prefix_mod else {
        let name = fors_index::module::join_dotted(interner, segs);
        diags.push((from, Diagnostic::new(range.0, range.1, Code::N(4), format!("unresolved import `{name}`: no such module, and `{}` is not a module", fors_index::module::join_dotted(interner, prefix)))));
        bind(universe, Entity::Poisoned, RowKind::Poisoned, 0, &[], diags);
        return;
    };
    if pm.index() == from {
        return; // Rule 8, already reported by `fors_index`.
    }
    let mname = fors_index::module::join_dotted(interner, prefix);
    let absent = universe.scopes[pm.index()].export(sn).is_none();
    let found = match universe.scopes[pm.index()].export(sn) {
        Some(Export::Public(row)) => {
            let i = universe.scopes[pm.index()].index.get(&sn).map_or(0, |&i| i as usize);
            Ok((row.entity, row.kind, universe.scopes[pm.index()].sig_hash[i], row.variants.to_vec()))
        }
        Some(Export::Private) => Err((Code::N(4), format!("`{sn_str}` is not `pub` in module `{mname}`"))),
        None => Err((Code::N(4), format!("module `{mname}` has no `pub` name `{sn_str}`"))),
    };
    match found {
        Ok((entity, kind, sig, variants)) => bind(universe, entity, kind, sig, &variants, diags),
        Err((code, msg)) => {
            // Rule 7: the cycle check precedes every other rule. When the
            // target module imports (transitively) the importer, its
            // `pub use` names are not complete yet by construction -- e.g.
            // `pub use b.Y as X;` in `a` beside `pub use a.X as Y;` in `b`
            // -- so a missing name there is a consequence of the cycle
            // `fors_index` already reported, not a second error.
            if !(absent && reaches(edges, pm.index(), from)) {
                diags.push((from, Diagnostic::new(range.0, range.1, code, msg)));
            }
            bind(universe, Entity::Poisoned, RowKind::Poisoned, 0, &[], diags);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn bind_use_name(
    universe: &mut Universe,
    from: usize,
    entity: Entity,
    kind: RowKind,
    sig_hash: u128,
    variants: &[Symbol],
    bound_name: Symbol,
    range: (u32, u32),
    is_pub: bool,
    diags: &mut Vec<(usize, Diagnostic)>,
) {
    let Universe { scopes, prelude, .. } = universe;
    let scope = &mut scopes[from];
    let poisoned = entity == Entity::Poisoned;
    if let Some(pe) = prelude.get(scope, bound_name) {
        let same = match (pe, entity) {
            (Entity::PreludeModule(_, Some(pm)), Entity::Module(em)) => pm == em,
            (Entity::PreludeModule(a, _), Entity::PreludeModule(b, _)) => a == b,
            _ => false,
        };
        if !same && !poisoned {
            diags.push((from, Diagnostic::new(range.0, range.1, Code::N(13), "import binds a prelude name to a different entity".to_string())));
        }
        return;
    }
    let vis = if is_pub { Visibility::Public } else { Visibility::Private };
    match scope.index.get(&bound_name).map(|&i| i as usize) {
        Some(i) if scope.origin[i] == Origin::Item => {
            if !poisoned {
                diags.push((from, Diagnostic::new(range.0, range.1, Code::N(13), "import binds the name of an item of this module".to_string())));
            }
        }
        Some(i) => {
            if scope.entity[i] == Entity::Poisoned || poisoned {
                // One of the two already failed: that is the root cause.
            } else if scope.entity[i] != entity {
                diags.push((from, Diagnostic::new(range.0, range.1, Code::N(15), "this import and an earlier one bind the same name to different entities".to_string())));
            } else if is_pub {
                scope.vis[i] = Visibility::Public;
            }
        }
        None => scope.push(bound_name, entity, kind, Origin::Use, vis, sig_hash, variants),
    }
}
