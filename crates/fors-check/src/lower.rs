//! CST + resolver output -> FIR signatures, one declaration at a time
//! (design §4.2, §7.2). Owns R3-R8, R11, R13, R15, R16's declaration side,
//! R61's static side and R62's static side.
//!
//! Two passes. Pass A ([`shapes`]) reads only what needs no type: how many
//! generic parameters a declaration has, of what kind, and which associated
//! types a trait declares. Every question R11 and R61 ask about another
//! declaration is answered from that table, so pass B lowers declarations in
//! any order without a fixpoint (design §10: "`decl_arity` depending on no
//! other `decl_arity` is the acyclicity base").

use fors_fir::defpath::NO_DEF;
use fors_fir::prelude::{PreludeDefs, PreludeEntity, tr};
use fors_fir::sig::{
    Assoc, Conv, GParam, GParamKind, Member, NO_BOUNDS, NO_CONSTRAINTS, NO_SLOT, Param, SigKind,
    VIS_PRIVATE, VIS_PUBLIC,
};
use fors_fir::ty::{
    BrandRow, NO_ARGS, NO_TY, PrimKind, Quals, TY_ERROR, TY_UNIT, TraitRefId, TyId,
};
use fors_fir::{ConstValue, Fir};
use fors_index::decl::DeclKind;
use fors_index::ids::{DefId, FileId};
use fors_index::{Interner, Symbol};
use fors_lex::{TokenKind, Tokens};
use fors_resolve::paths::{byte_range, own_span};
use fors_resolve::target::{DeferReason, Entity, NameUseTable, ResolvedTarget};
use fors_syntax::{NodeKind, Tree};

use crate::defs::DefTable;
use crate::diag::{Sink, t};

/// Pass A's syntactic classification of a generic parameter (R15). It never
/// needs a type: `brand` is a contextual keyword, and whether a bound is a
/// trait is the resolved entity's own declaration kind.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GKind {
    Type,
    Const,
    Brand,
    Callable,
    /// The bounds did not resolve, or they mix kinds: classify as a type
    /// parameter for arity purposes and let R15 speak once, in pass B.
    Unknown,
}

/// Pass A's whole-build table, indexed by `DefId`: struct-of-arrays, with one
/// shared pool per column, so a build with 45 000 declarations holds four
/// allocations rather than ninety thousand tiny ones.
#[derive(Default)]
pub struct Shapes {
    gk_start: Vec<u32>,
    gk_len: Vec<u16>,
    as_start: Vec<u32>,
    as_len: Vec<u16>,
    /// The `Generics` node, or `u32::MAX`.
    gnode: Vec<u32>,
    gkinds: Vec<GKind>,
    assoc: Vec<Symbol>,
    /// Parallel to `gkinds`: for a `Const` parameter, the `PrimKind` byte of
    /// its declared type when that type is a prelude primitive; `0xFF`
    /// otherwise. Pass A records it so a const ARGUMENT's fit test (R13) is
    /// the same whichever declaration is lowered first.
    const_prim: Vec<u8>,
}

impl Shapes {
    fn push(
        &mut self,
        def: DefId,
        gkinds: &[GKind],
        const_prim: &[u8],
        assoc: &[Symbol],
        generics_node: u32,
    ) {
        let i = def.index();
        while self.gnode.len() <= i {
            self.gk_start.push(0);
            self.gk_len.push(0);
            self.as_start.push(0);
            self.as_len.push(0);
            self.gnode.push(u32::MAX);
        }
        self.gk_start[i] = self.gkinds.len() as u32;
        self.gk_len[i] = u16::try_from(gkinds.len()).unwrap_or(u16::MAX);
        self.gkinds.extend_from_slice(gkinds);
        debug_assert_eq!(gkinds.len(), const_prim.len());
        self.const_prim.extend_from_slice(const_prim);
        while self.const_prim.len() < self.gkinds.len() {
            self.const_prim.push(0xFF);
        }
        self.as_start[i] = self.assoc.len() as u32;
        self.as_len[i] = u16::try_from(assoc.len()).unwrap_or(u16::MAX);
        self.assoc.extend_from_slice(assoc);
        self.gnode[i] = generics_node;
    }

    /// The kinds of `def`'s own generic parameters, in declaration order (a
    /// trait's implicit `Self` is not among them: a use writes only the
    /// explicit ones).
    pub fn gkinds(&self, def: DefId) -> &[GKind] {
        let i = def.index();
        if i >= self.gnode.len() {
            return &[];
        }
        let (a, n) = (self.gk_start[i] as usize, self.gk_len[i] as usize);
        &self.gkinds[a..a + n]
    }

    /// A trait's associated-type names, in declaration order.
    /// The declared type of `def`'s `i`th generic parameter when it is a
    /// const parameter over a prelude primitive; `None` otherwise.
    pub fn const_prim(&self, def: DefId, i: usize) -> Option<PrimKind> {
        let d = def.index();
        if d >= self.gnode.len() || i >= self.gk_len[d] as usize {
            return None;
        }
        let at = self.gk_start[d] as usize + i;
        self.const_prim.get(at).and_then(|&b| PrimKind::from_u8(b))
    }

    pub fn assoc(&self, def: DefId) -> &[Symbol] {
        let i = def.index();
        if i >= self.gnode.len() {
            return &[];
        }
        let (a, n) = (self.as_start[i] as usize, self.as_len[i] as usize);
        &self.assoc[a..a + n]
    }

    /// `def`'s `Generics` node, or `u32::MAX`.
    pub fn generics_node(&self, def: DefId) -> u32 {
        self.gnode.get(def.index()).copied().unwrap_or(u32::MAX)
    }

    pub fn arity(&self, def: DefId) -> usize {
        self.gkinds(def).len()
    }

    pub fn declares_assoc(&self, def: DefId, name: Symbol) -> bool {
        self.assoc(def).contains(&name)
    }
}

/// One file's inputs.
pub struct FileCtx<'a> {
    pub file: FileId,
    pub tree: &'a Tree,
    pub tokens: &'a Tokens,
    pub source: &'a [u8],
    pub uses: &'a NameUseTable,
}

impl FileCtx<'_> {
    fn kind(&self, node: usize) -> NodeKind {
        self.tree.kinds[node]
    }
    fn target(&self, node: usize) -> Option<ResolvedTarget> {
        self.uses.target_of(node as u32)
    }
    fn consumed(&self, node: usize) -> u8 {
        match self.uses.node.binary_search(&(node as u32)) {
            Ok(i) => self.uses.consumed[i],
            Err(_) => 0,
        }
    }
    fn range(&self, node: usize) -> (u32, u32) {
        byte_range(self.tree, self.tokens, node)
    }
    /// The identifiers a node owns directly, before its first child.
    fn own_idents(&self, names: &mut Interner, node: usize) -> Vec<(Symbol, (u32, u32))> {
        let (a, b) = own_span(self.tree, node);
        let mut out = Vec::new();
        for i in a as usize..b as usize {
            if self.tokens.kinds[i] == TokenKind::Ident {
                out.push((
                    names.intern(self.tokens.text(i, self.source)),
                    self.tokens.range(i),
                ));
            }
        }
        out
    }
    /// How many identifiers a node owns directly. The hot path asks only
    /// this and, on an error path, for one of them by index, so nothing
    /// allocates per type application.
    fn own_ident_count(&self, node: usize) -> usize {
        let (a, b) = own_span(self.tree, node);
        (a as usize..b as usize)
            .filter(|&i| self.tokens.kinds[i] == TokenKind::Ident)
            .count()
    }

    fn own_ident_nth(
        &self,
        names: &mut Interner,
        node: usize,
        n: usize,
    ) -> Option<(Symbol, (u32, u32))> {
        let (a, b) = own_span(self.tree, node);
        (a as usize..b as usize)
            .filter(|&i| self.tokens.kinds[i] == TokenKind::Ident)
            .nth(n)
            .map(|i| {
                (
                    names.intern(self.tokens.text(i, self.source)),
                    self.tokens.range(i),
                )
            })
    }

    fn own_has_ident(&self, node: usize, text: &[u8]) -> bool {
        let (a, b) = own_span(self.tree, node);
        (a as usize..b as usize).any(|i| {
            self.tokens.kinds[i] == TokenKind::Ident && self.tokens.text(i, self.source) == text
        })
    }
    fn own_has_kind(&self, node: usize, k: TokenKind) -> bool {
        let (a, b) = own_span(self.tree, node);
        (a as usize..b as usize).any(|i| self.tokens.kinds[i] == k)
    }
    fn child_kinds(&self, node: usize) -> Vec<(usize, NodeKind)> {
        self.tree
            .children(node)
            .map(|c| (c, self.tree.kinds[c]))
            .collect()
    }

    /// A declaration's own header: its first significant token through the
    /// token before its first member/body child. A whole-head diagnostic
    /// underlines the head, not the body.
    pub fn header_range(&self, node: usize) -> (u32, u32) {
        let (first, end) = self.tree.token_range(node);
        let stop = self
            .tree
            .children(node)
            .find(|&c| {
                matches!(
                    self.tree.kinds[c],
                    NodeKind::Block
                        | NodeKind::Field
                        | NodeKind::EVariant
                        | NodeKind::FnDecl
                        | NodeKind::TraitItem
                        | NodeKind::AssocTypeDecl
                        | NodeKind::AssocTypeDef
                )
            })
            .map_or(end, |c| self.tree.token_range(c).0);
        let a = first as usize;
        let b = (stop.max(first) as usize).min(self.tokens.kinds.len());
        let sig = |i: &usize| !self.tokens.kinds[*i].is_trivia();
        match ((a..b).find(sig), (a..b).rev().find(sig)) {
            (Some(x), Some(y)) => (self.tokens.range(x).0, self.tokens.range(y).1),
            _ => byte_range(self.tree, self.tokens, node),
        }
    }

    /// Whether a `fn` declaration has a body (a provided trait method).
    pub fn has_block(&self, node: usize) -> bool {
        self.tree
            .children(node)
            .any(|c| self.tree.kinds[c] == NodeKind::Block)
            || self.tree.children(node).any(|c| {
                self.tree.kinds[c] == NodeKind::FnSig
                    && self
                        .tree
                        .children(c)
                        .any(|x| self.tree.kinds[x] == NodeKind::Block)
            })
    }

    /// The first `Field`/`EVariant` of a declaration, for R14's "reported on
    /// one field of the cycle".
    pub fn first_field_range(&self, node: usize) -> (u32, u32) {
        match self
            .tree
            .children(node)
            .find(|&c| matches!(self.tree.kinds[c], NodeKind::Field | NodeKind::EVariant))
        {
            Some(c) => byte_range(self.tree, self.tokens, c),
            None => self.header_range(node),
        }
    }

    /// The `i`th `type A = RHS;` of an impl.
    pub fn assoc_def_range(&self, node: usize, i: usize) -> (u32, u32) {
        match self
            .tree
            .children(node)
            .filter(|&c| self.tree.kinds[c] == NodeKind::AssocTypeDef)
            .nth(i)
        {
            Some(c) => byte_range(self.tree, self.tokens, c),
            None => self.header_range(node),
        }
    }
}

// ---------------------------------------------------------------- pass A

/// Builds the shape table. Prelude rows keep the shapes `prelude::build` gave
/// them, read back out of the `SigStore`.
pub fn shapes(
    fir: &Fir,
    defs: &DefTable,
    prelude: &PreludeDefs,
    names: &mut Interner,
    files: &[FileCtx],
) -> Shapes {
    let mut out = Shapes::default();
    for i in 0..defs.first_user.index() {
        let d = DefId(i as u32);
        let g = fir.sigs.generics(d);
        let n = fir.sigs.generics_store.count(g);
        let mut gkinds = Vec::with_capacity(n);
        let mut cprims = Vec::with_capacity(n);
        for o in 0..n {
            let kind = fir.sigs.generics_store.param(g, o).kind;
            gkinds.push(match kind {
                GParamKind::Type => GKind::Type,
                GParamKind::Const { .. } => GKind::Const,
                GParamKind::Brand => GKind::Brand,
                GParamKind::Callable { .. } => GKind::Callable,
            });
            cprims.push(match kind {
                GParamKind::Const { ty } if fir.tys.tag(ty) == fors_fir::ty::TyTag::Prim => {
                    fir.tys.a(ty) as u8
                }
                _ => 0xFF,
            });
        }
        if fir.sigs.kind(d) == SigKind::Trait && !gkinds.is_empty() {
            gkinds.remove(0); // `Self` is the subject, never an argument.
            cprims.remove(0);
        }
        let a = fir.sigs.assoc(d);
        let assoc: Vec<Symbol> = (0..fir.sigs.assocs.count(a))
            .map(|k| fir.sigs.assocs.get(a, k).name)
            .collect();
        out.push(d, &gkinds, &cprims, &assoc, u32::MAX);
    }
    for (def, row) in defs.user_defs() {
        let f = &files[row.file.index()];
        let (mut gkinds, mut assoc, mut gnode): (Vec<GKind>, Vec<Symbol>, u32) =
            (Vec::new(), Vec::new(), u32::MAX);
        let mut cprims: Vec<u8> = Vec::new();
        let node = row.node as usize;
        // A `fn`'s generics hang off its `FnSig`, not off the `FnDecl`.
        let holder = if matches!(row.kind, DeclKind::Fn | DeclKind::ExternFn) {
            f.tree
                .children(node)
                .find(|&c| f.kind(c) == NodeKind::FnSig)
                .unwrap_or(node)
        } else {
            node
        };
        for c in f.tree.children(holder) {
            if f.kind(c) == NodeKind::Generics {
                gnode = c as u32;
                for g in f.tree.children(c) {
                    if f.kind(g) == NodeKind::GParam {
                        let k = classify_gparam(f, defs, prelude, g);
                        gkinds.push(k);
                        cprims.push(if k == GKind::Const {
                            const_prim_of(f, prelude, g)
                        } else {
                            0xFF
                        });
                    }
                }
            }
        }
        for c in f.tree.children(node) {
            if f.kind(c) == NodeKind::AssocTypeDecl
                && let Some((n, _)) = f.own_ident_nth(names, c, 0)
            {
                assoc.push(n);
            }
        }
        out.push(def, &gkinds, &cprims, &assoc, gnode);
    }
    out
}

/// The `PrimKind` byte of a const parameter's declared type, read from the
/// resolver's answer for its single bound (pass A: no type is lowered), or
/// `0xFF` when that bound is not a prelude primitive (R13 then speaks in
/// pass B, at the parameter).
fn const_prim_of(f: &FileCtx, prelude: &PreludeDefs, node: usize) -> u8 {
    let Some(bd) = f.tree.children(node).next() else {
        return 0xFF;
    };
    match f.target(bd) {
        Some(ResolvedTarget::Entity(Entity::PreludeType(s))) => match prelude.lookup(s) {
            Some(PreludeEntity::Ty(ty)) => prelude
                .prims
                .iter()
                .position(|&t| t == ty)
                .map_or(0xFF, |i| i as u8),
            _ => 0xFF,
        },
        _ => 0xFF,
    }
}

/// R15 from syntax plus the resolver's answer, with no type (pass A).
fn classify_gparam(f: &FileCtx, defs: &DefTable, prelude: &PreludeDefs, node: usize) -> GKind {
    if f.own_has_ident(node, b"brand") {
        return GKind::Brand;
    }
    let bounds: Vec<usize> = f.tree.children(node).collect();
    if bounds.is_empty() {
        return GKind::Type;
    }
    let (mut traits, mut types, mut callables, mut unknown) = (0usize, 0usize, 0usize, 0usize);
    for &bd in &bounds {
        match f.kind(bd) {
            NodeKind::FnType => callables += 1,
            NodeKind::TypeApp => match head_is_trait(f, defs, prelude, bd) {
                Some(true) => traits += 1,
                Some(false) => types += 1,
                None => unknown += 1,
            },
            _ => types += 1,
        }
    }
    if unknown > 0 {
        GKind::Unknown
    } else if callables == bounds.len() && callables == 1 {
        GKind::Callable
    } else if types == 1 && bounds.len() == 1 {
        GKind::Const
    } else if traits == bounds.len() {
        GKind::Type
    } else {
        GKind::Unknown
    }
}

/// Whether a bound's head names a trait. `None` when it did not resolve.
fn head_is_trait(f: &FileCtx, defs: &DefTable, prelude: &PreludeDefs, node: usize) -> Option<bool> {
    match f.target(node)? {
        ResolvedTarget::Entity(Entity::Item { file, decl }) => {
            let def = defs.def_of(file, decl);
            defs.get(def).map(|r| r.kind == DeclKind::Trait)
        }
        ResolvedTarget::Entity(Entity::PreludeType(s)) => match prelude.lookup(s) {
            Some(PreludeEntity::Trait { .. }) => Some(true),
            Some(PreludeEntity::Ty(_)) | Some(PreludeEntity::Generic { .. }) => Some(false),
            // A prelude name with no declaration in this build (ch10 R2's std
            // types): neither answer is known, so R15 stays silent.
            Some(PreludeEntity::Opaque) | None => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------- pass B

/// Where a type is being lowered, for the positions R11 and R61 distinguish.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Pos {
    /// An ordinary type: a parameter, result, field, payload, annotation.
    Value,
    /// A bound, an impl's trait reference, or a `dyn` operand: a trait head
    /// is what belongs here.
    TraitRef,
    /// An impl's self type.
    ImplSelf,
    /// The right-hand side of `type A = RHS;` (R61(d)).
    AssocRhs,
    // MARC: appended (never reordered) for I3. A body writes annotations
    // whose head is a ch10 R2 name with no `std` in the build
    // (`var v: Vec[i32, heap];`). Its arguments are still lowered — an
    // error INSIDE one is the user's — but nothing may be decided from an
    // argument slot of a head whose parameter kinds are unknown: `heap`
    // there is a brand (ch01 R15/R16), not R11's "a binding, not a type".
    /// An argument of a head this build has no declaration for.
    OpaqueArg,
}

/// MARC: verification of I2/I3 (2026-09-20). The FIR pools keep list
/// lengths in `u8`/`u16` columns and `fors-fir`'s `push`es assert it, so a
/// 256-parameter function, a 256-parameter closure and a 65 536-element
/// tuple each PANICKED the checker (found by probe). The limits are
/// enforced here, once, with a diagnostic under the rule that governs the
/// entity (there is no `I00nn` code in `fors_index::diag::Code`, and that
/// crate is not this increment's), and the list is truncated so the pools
/// are never asked for more than they hold. The declaration is poisoned
/// by the diagnostic, so nothing downstream reads the truncated shape as
/// the program's.
pub(crate) const MAX_PARAMS: usize = u8::MAX as usize;
pub(crate) const MAX_LIST: usize = u16::MAX as usize;

fn limit_msg(what: &str, n: usize, max: usize) -> String {
    format!("implementation limit: {what} has {n} entries; at most {max} are supported")
}

/// What `Self` means in the declaration being lowered.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SelfKind {
    None,
    /// Inside `trait Tr[Ps]`: `Self` is `Param{Tr, 0}` and its bounds are
    /// `Tr[Ps]` alone (plus `Index[I]` inside `IndexMut[I]`, R21).
    Trait(DefId),
    /// Inside `impl Tr[As] for S`, or an inherent `impl S` (`trait_def` is
    /// [`NO_DEF`] then).
    Impl {
        trait_def: DefId,
    },
}

/// Per-declaration lowering state.
pub struct Cx<'f, 'a> {
    pub f: &'a FileCtx<'f>,
    /// Whose `Param` rows this declaration's own gparams produce.
    pub owner: DefId,
    /// The declaration a diagnostic is charged to.
    pub home: DefId,
    /// `gparam node -> (owner, ordinal, kind)`, own list last so a shadowing
    /// lookup finds the innermost first.
    scope: Vec<(u32, DefId, u16, GKind)>,
    self_node: u32,
    self_ty: TyId,
    self_kind: SelfKind,
    /// The enclosing impl's `type A = RHS;` definitions, for R61(c).
    impl_assoc: Vec<(Symbol, TyId)>,
    /// The impl whose parameters may head a projection inside `type A = RHS;`.
    assoc_rhs_owner: DefId,
}

impl<'f, 'a> Cx<'f, 'a> {
    pub fn new(f: &'a FileCtx<'f>, owner: DefId) -> Cx<'f, 'a> {
        Cx {
            f,
            owner,
            home: owner,
            scope: Vec::new(),
            self_node: u32::MAX,
            self_ty: NO_TY,
            self_kind: SelfKind::None,
            impl_assoc: Vec::new(),
            assoc_rhs_owner: NO_DEF,
        }
    }
    fn find(&self, node: u32) -> Option<(DefId, u16, GKind)> {
        self.scope
            .iter()
            .rev()
            .find(|&&(n, ..)| n == node)
            .map(|&(_, d, o, k)| (d, o, k))
    }
}

/// Sites a later whole-head pass must revisit once every declaration is
/// lowered: a `dyn Tr` (R25's dyn-capability test needs `Tr`'s whole item
/// list) and an `Array`/`vector`/`atomic` application (R11's linear-element
/// test needs every `impl Linear` in the build).
#[derive(Default)]
pub struct Sites {
    /// `(home declaration, file, range, trait)`.
    pub dyn_uses: Vec<(DefId, FileId, (u32, u32), DefId)>,
    /// `(home declaration, file, range, element type, container name)`.
    pub elements: Vec<(DefId, FileId, (u32, u32), TyId, Symbol)>,
}

/// The lowering pass (design §7.1 phase 3).
pub struct Lowerer<'a> {
    pub sites: Sites,
    pub fir: &'a mut Fir,
    pub names: &'a mut Interner,
    pub prelude: &'a PreludeDefs,
    pub defs: &'a DefTable,
    pub shapes: &'a Shapes,
    pub sink: &'a mut Sink,
}

/// A type-level head, once the resolver's answer has been classified.
enum Head {
    Prim(TyId),
    /// A nominal type with a known parameter list.
    Nominal(DefId),
    /// A trait: legal only after `dyn`, in a bound, or in an impl header.
    Trait(DefId),
    /// A generic parameter of some declaration in scope.
    GParam(DefId, u16, GKind),
    /// `Self`.
    SelfTy,
    /// A prelude name the build has no declaration for (ch10 R2 without a
    /// `std` in the build): nothing may be decided from it.
    Opaque,
    /// Resolved to a value: R11's "naming the binding".
    Value((u32, u32), Symbol),
    /// Already diagnosed, or deliberately deferred: silent `TY_ERROR`.
    Silent,
}

impl Lowerer<'_> {
    // ------------------------------------------------------------ types

    /// Lowers one type node (design §7.2).
    pub fn ty(&mut self, cx: &mut Cx, node: usize, pos: Pos) -> TyId {
        match cx.f.kind(node) {
            NodeKind::QualType => {
                let mut q = Quals::NONE;
                let (a, b) = own_span(cx.f.tree, node);
                for i in a as usize..b as usize {
                    match cx.f.tokens.kinds[i] {
                        TokenKind::KwIso => q = q.union(Quals::ISO),
                        TokenKind::KwImm => q = q.union(Quals::IMM),
                        TokenKind::KwSecret => q = q.union(Quals::SECRET),
                        _ => {}
                    }
                }
                let inner = match cx.f.tree.children(node).next() {
                    Some(c) => self.ty(cx, c, pos),
                    None => TY_ERROR,
                };
                if inner == TY_ERROR {
                    TY_ERROR
                } else {
                    self.fir.tys.qualified(inner, q)
                }
            }
            // `scoped(p) T` is a signature flag, not a type (design §7.2).
            NodeKind::ScopedType => match cx.f.tree.children(node).next() {
                Some(c) => self.ty(cx, c, pos),
                None => TY_ERROR,
            },
            NodeKind::TupleType => {
                let cs: Vec<usize> = cx.f.tree.children(node).collect();
                if cs.is_empty() {
                    return TY_UNIT;
                }
                // R4: `(T)` is `T`; `(T,)` is the 1-tuple. The trailing comma
                // is the only thing that tells them apart.
                if cs.len() == 1 && !self.has_trailing_comma(cx, node) {
                    return self.ty(cx, cs[0], pos);
                }
                let xs: Vec<TyId> = cs.iter().map(|&c| self.ty(cx, c, Pos::Value)).collect();
                if xs.contains(&TY_ERROR) {
                    return TY_ERROR;
                }
                if xs.len() > MAX_LIST {
                    let r = cx.f.range(node);
                    self.emit(cx, r, 4, 4, limit_msg("a tuple type", xs.len(), MAX_LIST));
                    return TY_ERROR;
                }
                self.fir.tys.tuple_of(&xs)
            }
            NodeKind::FnType => {
                let mut params: Vec<(Conv, TyId)> = Vec::new();
                let mut result = TY_UNIT;
                let mut raises = NO_TY;
                for (c, k) in cx.f.child_kinds(node) {
                    match k {
                        NodeKind::FParam => {
                            let conv = self.conv_of(cx, c);
                            let ty = match cx.f.tree.children(c).next() {
                                Some(x) => self.ty(cx, x, Pos::Value),
                                None => TY_ERROR,
                            };
                            params.push((conv, ty));
                        }
                        NodeKind::Raises => {
                            raises = match cx.f.tree.children(c).next() {
                                Some(x) => self.ty(cx, x, Pos::Value),
                                None => TY_ERROR,
                            };
                        }
                        NodeKind::Error => {}
                        _ => result = self.ty(cx, c, Pos::Value),
                    }
                }
                if params.len() > MAX_PARAMS {
                    let r = cx.f.range(node);
                    self.emit(
                        cx,
                        r,
                        7,
                        7,
                        limit_msg("a `fn` type's parameter list", params.len(), MAX_PARAMS),
                    );
                    return TY_ERROR;
                }
                let id = self.fir.tys.intern_fn_ty(&params, result, raises, false);
                self.fir.tys.fn_ty(id)
            }
            NodeKind::DynType => {
                let Some(c) = cx.f.tree.children(node).next() else {
                    return TY_ERROR;
                };
                match self.trait_ref(cx, c) {
                    Some(tref) => {
                        let (tdef, _) = self.fir.tys.trait_ref(tref);
                        let r = cx.f.range(node);
                        self.sites.dyn_uses.push((cx.home, cx.f.file, r, tdef));
                        self.fir.tys.dyn_ty(tref)
                    }
                    None => TY_ERROR,
                }
            }
            NodeKind::TypeApp => self.type_app(cx, node, pos),
            NodeKind::Error => TY_ERROR,
            // A const argument in a type-argument slot, or a garbage node.
            _ => TY_ERROR,
        }
    }

    fn has_trailing_comma(&self, cx: &Cx, node: usize) -> bool {
        let (_, end) = cx.f.tree.token_range(node);
        let mut i = (end as usize).min(cx.f.tokens.kinds.len());
        let mut seen_close = false;
        while i > 0 {
            i -= 1;
            match cx.f.tokens.kinds[i] {
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment => {
                    continue;
                }
                TokenKind::RParen if !seen_close => {
                    seen_close = true;
                    continue;
                }
                TokenKind::Comma => return seen_close,
                _ => return false,
            }
        }
        false
    }

    fn conv_of(&self, cx: &Cx, node: usize) -> Conv {
        let (a, b) = own_span(cx.f.tree, node);
        for i in a as usize..b as usize {
            match cx.f.tokens.kinds[i] {
                TokenKind::KwLet | TokenKind::KwVar => return Conv::Let,
                TokenKind::KwInout => return Conv::Inout,
                TokenKind::KwSink => return Conv::Sink,
                TokenKind::Ident if cx.f.tokens.text(i, cx.f.source) == b"set" => return Conv::Set,
                _ => {}
            }
        }
        Conv::Let
    }

    /// The head of a `TypeApp`, classified.
    fn head_of(&mut self, cx: &mut Cx, node: usize) -> Head {
        let Some(target) = cx.f.target(node) else {
            return Head::Silent;
        };
        match target {
            ResolvedTarget::Deferred {
                reason: DeferReason::Diagnosed | DeferReason::StdAbsent,
            } => Head::Silent,
            ResolvedTarget::Deferred {
                reason: DeferReason::Member,
            } => Head::Silent,
            ResolvedTarget::Local { node: n } => {
                if n == cx.self_node {
                    return Head::SelfTy;
                }
                match cx.find(n) {
                    Some((owner, ord, k)) => Head::GParam(owner, ord, k),
                    None => match cx.f.own_ident_nth(self.names, node, 0) {
                        Some((s, r)) => Head::Value(r, s),
                        None => Head::Silent,
                    },
                }
            }
            ResolvedTarget::Entity(e) => match e {
                Entity::Item { file, decl } => {
                    let def = self.defs.def_of(file, decl);
                    match self.defs.get(def).map(|r| r.kind) {
                        Some(DeclKind::Struct) | Some(DeclKind::Enum) => Head::Nominal(def),
                        Some(DeclKind::Trait) => Head::Trait(def),
                        Some(_) => match self.last_own_ident(cx, node) {
                            Some((s, r)) => Head::Value(r, s),
                            None => Head::Silent,
                        },
                        None => Head::Silent,
                    }
                }
                Entity::PreludeType(sym) => match self.prelude.lookup(sym) {
                    Some(PreludeEntity::Ty(t)) => Head::Prim(t),
                    Some(PreludeEntity::Generic { def, .. }) => Head::Nominal(def),
                    Some(PreludeEntity::Trait { def, .. }) => Head::Trait(def),
                    Some(PreludeEntity::Opaque) | None => Head::Opaque,
                },
                Entity::Variant { .. } | Entity::PreludeValue(_) => {
                    match self.last_own_ident(cx, node) {
                        Some((s, r)) => Head::Value(r, s),
                        None => Head::Silent,
                    }
                }
                Entity::Module(_) | Entity::PreludeModule(..) | Entity::Poisoned => Head::Silent,
            },
        }
    }

    fn last_own_ident(&mut self, cx: &Cx, node: usize) -> Option<(Symbol, (u32, u32))> {
        let n = cx.f.own_ident_count(node);
        if n == 0 {
            return None;
        }
        cx.f.own_ident_nth(self.names, node, n - 1)
    }

    fn type_app(&mut self, cx: &mut Cx, node: usize, pos: Pos) -> TyId {
        let nsegs = cx.f.own_ident_count(node);
        let consumed = cx.f.consumed(node) as usize;
        let tail = nsegs.saturating_sub(consumed.max(1));
        let head = self.head_of(cx, node);

        if tail > 0 {
            return self.projection(cx, node, nsegs, consumed, head, pos);
        }
        let range = cx.f.range(node);

        match head {
            Head::Silent | Head::Opaque => {
                // Still lower the arguments: an error inside them is the
                // user's, not a consequence of the unknown head.
                for (c, k) in cx.f.child_kinds(node) {
                    if is_type_node(k) {
                        self.ty(cx, c, Pos::OpaqueArg);
                    }
                }
                TY_ERROR
            }
            Head::Value(r, s) => {
                if pos == Pos::OpaqueArg {
                    return TY_ERROR;
                }
                let n = String::from_utf8_lossy(self.names.resolve(s)).into_owned();
                self.emit(cx, r, 11, 11, format!("`{n}` is a binding, not a type"));
                TY_ERROR
            }
            // MARC: `rawptr[u8]` is written in the ch08 corpus
            // (`prelude-usable-without-use-accepted`), so a primitive head
            // with arguments is NOT an arity error in v0.1: R3 gives the
            // primitives no parameters, but ch08's accepted corpus spells a
            // pointee on `rawptr`, and I2 does not get to overrule an
            // accepted test. The arguments are lowered (an error inside them
            // is still the user's) and the head is the primitive.
            Head::Prim(ty) => {
                for (c, k) in cx.f.child_kinds(node) {
                    if is_type_node(k) {
                        self.ty(cx, c, Pos::Value);
                    }
                }
                ty
            }
            Head::SelfTy => {
                if cx.self_ty == NO_TY {
                    TY_ERROR
                } else {
                    cx.self_ty
                }
            }
            Head::GParam(owner, ord, k) => self.param_ty(cx, owner, ord, k),
            Head::Trait(def) => {
                if pos == Pos::Value {
                    self.emit(
                        cx,
                        range,
                        11,
                        11,
                        "a trait is a type only after `dyn`, in a bound or in an `impl` header"
                            .to_string(),
                    );
                    return TY_ERROR;
                }
                // The caller wanted a trait reference; `trait_ref` re-reads
                // the node. Produce an error type so a stray use is inert.
                let _ = def;
                TY_ERROR
            }
            Head::Nominal(def) => {
                let args = self.type_args(cx, node, def, range);
                match args {
                    Some(xs) => {
                        // R11 (ch01 R22b): a CONCRETE `Array[X, N]`,
                        // `vector[X, N]` or `atomic[X]` whose element type is
                        // linear. Linearity is only known once every `impl
                        // Linear` is in, so the site is recorded, not decided.
                        if let Some(g) = self.prelude.generic_index(def) {
                            use fors_fir::prelude::gty;
                            if matches!(g, gty::ARRAY | gty::VECTOR | gty::ATOMIC) && !xs.is_empty()
                            {
                                let name =
                                    self.defs.get(def).and_then(|r| r.name).unwrap_or(Symbol(0));
                                self.sites
                                    .elements
                                    .push((cx.home, cx.f.file, range, xs[0], name));
                            }
                        }
                        self.fir.tys.nominal_of(def, &xs)
                    }
                    None => TY_ERROR,
                }
            }
        }
    }

    fn param_ty(&mut self, cx: &mut Cx, owner: DefId, ord: u16, k: GKind) -> TyId {
        match k {
            GKind::Brand => self.fir.tys.brand_ty(BrandRow::Param {
                owner,
                ordinal: ord,
            }),
            GKind::Const => {
                // A bare const parameter in type position is R13's "by
                // identity" case: it stays a `Param` row so R9 compares it by
                // identity, exactly as R9 requires.
                let _ = cx;
                self.fir.tys.param(owner, ord)
            }
            _ => self.fir.tys.param(owner, ord),
        }
    }

    /// R11: exactly as many arguments as the head declares, each of the
    /// declared kind; R13 for the const ones.
    fn type_args(
        &mut self,
        cx: &mut Cx,
        node: usize,
        def: DefId,
        range: (u32, u32),
    ) -> Option<Vec<TyId>> {
        let shapes = self.shapes;
        let kinds: &[GKind] = shapes.gkinds(def);
        let args: Vec<usize> = cx.f.tree.children(node).collect();
        if args.len() > MAX_LIST || kinds.len() > MAX_LIST {
            // The head's own declaration carries the limit diagnostic.
            return None;
        }
        // R11: "a generic item named with no arguments is legal only where
        // Rule 34 or 38 determines them" — which is a BODY question, so I2
        // says nothing about a bare head and leaves the type open.
        if args.is_empty() && !kinds.is_empty() {
            return None;
        }
        // MARC: the ch08 corpus writes `Own[Mine]` and `Own[Hidden]` for the
        // two-parameter `Own[T, A: brand]` (`impl-type-argument-does-not-
        // count-rejected`, `private-type-in-pub-method-rejected`), so a
        // TRAILING BRAND slot may be left out of a written type. ch01 R15/R15b
        // own brand inference; R11's arity clause is about the arguments a
        // writer must supply, and a brand is not one of them. The type is left
        // open (`TY_ERROR`) rather than invented.
        if args.len() < kinds.len() && kinds[args.len()..].iter().all(|&k| k == GKind::Brand) {
            for &c in &args {
                if is_type_node(cx.f.kind(c)) {
                    self.ty(cx, c, Pos::Value);
                }
            }
            return None;
        }
        if args.len() != kinds.len() {
            let name = self.defs.get(def).and_then(|r| r.name).or(Some(Symbol(0)));
            let n = name
                .filter(|s| s.0 != 0)
                .map(|s| format!("`{}`", String::from_utf8_lossy(self.names.resolve(s))))
                .unwrap_or_else(|| "this type".to_string());
            self.emit(
                cx,
                range,
                11,
                11,
                format!(
                    "{n} declares {} type argument(s), {} supplied",
                    kinds.len(),
                    args.len()
                ),
            );
            for &c in &args {
                if is_type_node(cx.f.kind(c)) {
                    self.ty(cx, c, Pos::Value);
                }
            }
            return None;
        }
        let mut out = Vec::with_capacity(args.len());
        for (i, &c) in args.iter().enumerate() {
            let k = kinds[i];
            match k {
                GKind::Const => out.push(self.const_arg(cx, c, def, i)),
                // MARC: a BRAND slot may name a value — `Own[i32, x]` with
                // `x: Arena` is in the ch08 corpus (`scoped-parameter-
                // accepted`), and ch01 R16 owns what a brand argument may be.
                // R11's "naming the binding" clause is about a value in a
                // TYPE slot, so a brand slot lowers silently.
                GKind::Brand => out.push(self.brand_arg(cx, c)),
                _ => out.push(self.ty(cx, c, Pos::Value)),
            }
        }
        if out.contains(&TY_ERROR) {
            return None;
        }
        Some(out)
    }

    /// A brand argument. ch01 R15/R16 own what one may be — including an
    /// `Arena`-typed VALUE parameter (`Own[i32, a]` with `let a: Arena`,
    /// which the ch08 corpus writes in an accepted test) and the omitted
    /// brand of a `with` header — so R11's "a value head names the binding"
    /// clause does not apply in this slot and I2 is silent here.
    fn brand_arg(&mut self, cx: &mut Cx, node: usize) -> TyId {
        if cx.f.kind(node) != NodeKind::TypeApp {
            return TY_ERROR;
        }
        match self.head_of(cx, node) {
            Head::GParam(owner, ord, GKind::Brand) => self.fir.tys.brand_ty(BrandRow::Param {
                owner,
                ordinal: ord,
            }),
            _ => TY_ERROR,
        }
    }

    /// R13: a const argument is a closed constant expression or a bare const
    /// parameter of the enclosing declaration. Arithmetic on one is rejected.
    /// R11: the argument must be OF THE DECLARED KIND — a type name in a
    /// const slot is "a type where a constant is expected" — and R13
    /// requires a closed value to FIT the parameter's declared type.
    fn const_arg(&mut self, cx: &mut Cx, node: usize, def: DefId, slot: usize) -> TyId {
        match cx.f.kind(node) {
            NodeKind::TypeApp => {
                let head = self.head_of(cx, node);
                match head {
                    Head::GParam(owner, ord, GKind::Const) => self.fir.tys.param(owner, ord),
                    Head::GParam(owner, ord, GKind::Unknown) => self.fir.tys.param(owner, ord),
                    // MARC: verification of I2 (2026-09-20). A TYPE in a const
                    // slot (`Array[i32, i32]`) lowered to a silent `TY_ERROR`,
                    // so the arity-correct misuse was never reported. R11's
                    // "each of the declared kind" owns it.
                    Head::Nominal(_)
                    | Head::Prim(_)
                    | Head::Trait(_)
                    | Head::SelfTy
                    | Head::GParam(_, _, GKind::Type)
                    | Head::GParam(_, _, GKind::Brand)
                    | Head::GParam(_, _, GKind::Callable) => {
                        let r = cx.f.range(node);
                        self.emit(
                            cx,
                            r,
                            11,
                            11,
                            "a type where a constant argument is expected".to_string(),
                        );
                        TY_ERROR
                    }
                    // A prelude name with no declaration in this build, or a
                    // head the resolver already diagnosed: silent.
                    Head::Opaque | Head::Silent => TY_ERROR,
                    // A `const` declaration used as a const argument: its
                    // value is the const's, which I2 folds only for literals
                    // (a closed constant expression by ch04 R11-14, left open
                    // rather than guessed). A LOCAL or parameter is not a
                    // constant expression at all (R13).
                    Head::Value(range, name) => {
                        if self.is_const_decl(cx, node) {
                            TY_ERROR
                        } else {
                            let n = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                            self.emit(cx, range, 13, 13, format!("`{n}` is a binding, not a closed constant expression or a const parameter"));
                            TY_ERROR
                        }
                    }
                }
            }
            NodeKind::Literal => match self.literal_value(cx, node) {
                Some(v) => self.fit_const(cx, node, v, def, slot),
                None => TY_ERROR,
            },
            // R13: `Array[T, N + 1]`. Its range error could surface only after
            // instantiation, which R59 forbids. A NEGATED literal (`-1`) is a
            // closed constant expression like any other and is folded here
            // (ch07 Disambiguation 8 makes it one literal in value position).
            NodeKind::AddExpr
            | NodeKind::MulExpr
            | NodeKind::BitExpr
            | NodeKind::UnaryExpr
            | NodeKind::CastExpr
            | NodeKind::CmpExpr
            | NodeKind::RangeExpr => {
                if self.mentions_const_param(cx, node) {
                    let r = cx.f.range(node);
                    self.emit(
                        cx,
                        r,
                        13,
                        13,
                        "arithmetic on a const parameter in type position; write the parameter itself".to_string(),
                    );
                    return TY_ERROR;
                }
                if cx.f.kind(node) == NodeKind::UnaryExpr
                    && let Some(v) = self.negated_literal(cx, node)
                {
                    return self.fit_const(cx, node, v, def, slot);
                }
                TY_ERROR
            }
            _ => TY_ERROR,
        }
    }

    /// Whether a value-resolved head is a `const` item (a closed constant
    /// expression by ch04 R11-14) rather than a local or a parameter.
    fn is_const_decl(&self, cx: &Cx, node: usize) -> bool {
        match cx.f.target(node) {
            Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                let d = self.defs.def_of(file, decl);
                self.defs.get(d).map(|r| r.kind) == Some(DeclKind::Const)
            }
            _ => false,
        }
    }

    /// `-lit` as one closed value: a `UnaryExpr` whose own first token is
    /// `-` and whose single operand is an integer literal.
    fn negated_literal(&mut self, cx: &mut Cx, node: usize) -> Option<ConstValue> {
        let kids: Vec<usize> = cx.f.tree.children(node).collect();
        if kids.len() != 1 || cx.f.kind(kids[0]) != NodeKind::Literal {
            return None;
        }
        // A node's token range starts at its leading trivia; `own_has_kind`
        // reads the tokens the node owns before its first child.
        if !cx.f.own_has_kind(node, TokenKind::Minus) {
            return None;
        }
        match self.literal_value(cx, kids[0])? {
            ConstValue::I(v) => Some(ConstValue::I(-v)),
            _ => None,
        }
    }

    /// R13's fit test: the closed value `v` against the declared type of the
    /// `slot`th parameter of `def`, read from pass A so the answer does not
    /// depend on which declaration was lowered first.
    fn fit_const(
        &mut self,
        cx: &mut Cx,
        node: usize,
        v: ConstValue,
        def: DefId,
        slot: usize,
    ) -> TyId {
        let declared = self.shapes.const_prim(def, slot);
        // `constval::fits` is I1's (R13's range table); I2 never called it.
        let fits = declared.is_none_or(|p| fors_fir::constval::fits(v, p));
        if !fits {
            let r = cx.f.range(node);
            let want = declared
                .map(|p| {
                    format!(
                        "`{}`",
                        String::from_utf8_lossy(fors_fir::prelude::PRIMS[p as usize].0)
                    )
                })
                .unwrap_or_else(|| "the parameter's type".to_string());
            self.emit(
                cx,
                r,
                13,
                13,
                format!("this constant does not fit {want}, the const parameter's declared type"),
            );
            return TY_ERROR;
        }
        let ty = match declared {
            Some(p) => self.fir.tys.prim(p),
            None => self.value_ty(v),
        };
        self.fir.tys.const_ty(v, ty)
    }

    fn mentions_const_param(&mut self, cx: &mut Cx, node: usize) -> bool {
        let end = cx.f.tree.subtree_end(node);
        for n in node..end {
            if matches!(cx.f.kind(n), NodeKind::TypeApp | NodeKind::NameExpr)
                && let Some(ResolvedTarget::Local { node: b }) = cx.f.target(n)
                && matches!(cx.find(b), Some((_, _, GKind::Const)))
            {
                return true;
            }
        }
        false
    }

    fn literal_value(&mut self, cx: &mut Cx, node: usize) -> Option<ConstValue> {
        let (a, b) = cx.f.tree.token_range(node);
        for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
            match cx.f.tokens.kinds[i] {
                TokenKind::Int => {
                    let txt = cx.f.tokens.text(i, cx.f.source);
                    return parse_int_literal(txt).map(ConstValue::I);
                }
                TokenKind::KwTrue => return Some(ConstValue::B(true)),
                TokenKind::KwFalse => return Some(ConstValue::B(false)),
                _ => {}
            }
        }
        None
    }

    fn value_ty(&mut self, v: ConstValue) -> TyId {
        match v {
            ConstValue::I(_) => self.fir.tys.prim(PrimKind::Usize),
            ConstValue::B(_) => self.fir.tys.prim(PrimKind::Bool),
            ConstValue::S(_) => self.fir.tys.prim(PrimKind::Str),
        }
    }

    /// R61: a projection `P.A`.
    fn projection(
        &mut self,
        cx: &mut Cx,
        node: usize,
        nsegs: usize,
        consumed: usize,
        head: Head,
        pos: Pos,
    ) -> TyId {
        let range = cx.f.range(node);
        let tail = nsegs - consumed.max(1);
        // An unresolved head was already diagnosed: R61 has nothing to add,
        // and "three segments" would be a second diagnostic for one cause.
        if matches!(head, Head::Silent | Head::Opaque) {
            return TY_ERROR;
        }
        if tail > 1 {
            self.emit(
                cx,
                range,
                61,
                61,
                "a projection has exactly two segments; write the type it normalises to"
                    .to_string(),
            );
            return TY_ERROR;
        }
        let Some((name, _)) = self.last_own_ident(cx, node) else {
            return TY_ERROR;
        };
        match head {
            Head::Silent | Head::Opaque => TY_ERROR,
            Head::Value(r, s) => {
                let n = String::from_utf8_lossy(self.names.resolve(s)).into_owned();
                self.emit(cx, r, 11, 11, format!("`{n}` is a binding, not a type"));
                TY_ERROR
            }
            // R61(b): "write the type itself".
            Head::Prim(_) | Head::Nominal(_) | Head::Trait(_) => {
                self.emit(
                    cx,
                    range,
                    61,
                    61,
                    "a projection headed by a concrete type is not writable; write the type itself"
                        .to_string(),
                );
                TY_ERROR
            }
            Head::GParam(owner, ord, k) => {
                if matches!(k, GKind::Brand | GKind::Const) {
                    self.emit(
                        cx,
                        range,
                        61,
                        61,
                        "a brand or const parameter has no bounds, so it heads no projection"
                            .to_string(),
                    );
                    return TY_ERROR;
                }
                if pos == Pos::AssocRhs
                    && cx.assoc_rhs_owner != NO_DEF
                    && owner != cx.assoc_rhs_owner
                {
                    self.emit(
                        cx,
                        range,
                        61,
                        61,
                        "inside `type A = ...;` a projection must be headed by one of the impl's own type parameters"
                            .to_string(),
                    );
                    return TY_ERROR;
                }
                let head_ty = self.fir.tys.param(owner, ord);
                let bounds = self.bounds_of(owner, ord);
                self.pick_assoc(cx, range, head_ty, &bounds, name)
            }
            Head::SelfTy => {
                if pos == Pos::AssocRhs {
                    // R61(d): `Self.B` inside `type A = RHS;` would let a
                    // cycle be written.
                    self.emit(
                        cx,
                        range,
                        61,
                        61,
                        "`Self.` may not head a projection inside `type A = ...;`".to_string(),
                    );
                    return TY_ERROR;
                }
                match cx.self_kind {
                    SelfKind::Trait(def) => {
                        let mut bounds = vec![self.own_trait_ref(def)];
                        // R21: inside `IndexMut[I]`, `Self.Output` is
                        // `Index[I]`'s.
                        if def == self.prelude.traits[tr::INDEXMUT] {
                            let i = self.fir.tys.param(def, 1);
                            let a = self.fir.tys.intern_args(&[i]);
                            bounds.push(
                                self.fir
                                    .tys
                                    .intern_trait_ref(self.prelude.traits[tr::INDEX], a),
                            );
                        }
                        let head_ty = cx.self_ty;
                        self.pick_assoc(cx, range, head_ty, &bounds, name)
                    }
                    SelfKind::Impl { trait_def } => {
                        if trait_def == NO_DEF {
                            self.emit(
                                cx,
                                range,
                                61,
                                61,
                                "an inherent impl has no trait, so `Self.` heads no projection"
                                    .to_string(),
                            );
                            return TY_ERROR;
                        }
                        // R61(c): replaced at once by the impl's own
                        // definition, with no lookup.
                        if let Some(&(_, rhs)) = cx.impl_assoc.iter().find(|&&(n, _)| n == name) {
                            return rhs;
                        }
                        let declared = self.shapes.declares_assoc(trait_def, name)
                            || (trait_def == self.prelude.traits[tr::INDEXMUT]
                                && name == self.prelude.output_name);
                        if !declared {
                            let name_s =
                                String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                            self.emit(
                                cx,
                                range,
                                61,
                                61,
                                format!("no associated type `{name_s}` on this trait"),
                            );
                        }
                        TY_ERROR
                    }
                    SelfKind::None => TY_ERROR,
                }
            }
        }
    }

    /// R61(c): exactly one trait among `bounds` declares `name`.
    fn pick_assoc(
        &mut self,
        cx: &mut Cx,
        range: (u32, u32),
        head_ty: TyId,
        bounds: &[TraitRefId],
        name: Symbol,
    ) -> TyId {
        let mut hits: Vec<TraitRefId> = Vec::new();
        for &b in bounds {
            let (def, _) = self.fir.tys.trait_ref(b);
            if self.shapes.declares_assoc(def, name) {
                hits.push(b);
            }
        }
        hits.dedup();
        match hits.len() {
            1 => {
                let key = self.fir.tys.intern_proj_key(hits[0], name);
                self.fir.tys.proj(head_ty, key)
            }
            0 => {
                let name_s = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                self.emit(
                    cx,
                    range,
                    61,
                    61,
                    format!("no bound of this parameter declares an associated type `{name_s}`"),
                );
                TY_ERROR
            }
            n => {
                let name_s = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
                self.emit(
                    cx,
                    range,
                    61,
                    61,
                    format!("ambiguous projection: {n} bounds declare `{name_s}`"),
                );
                TY_ERROR
            }
        }
    }

    fn own_trait_ref(&mut self, def: DefId) -> TraitRefId {
        let n = self.shapes.arity(def).min(MAX_LIST - 1);
        let args: Vec<TyId> = (0..n)
            .map(|o| self.fir.tys.param(def, (o + 1) as u16))
            .collect();
        let a = self.fir.tys.intern_args(&args);
        self.fir.tys.intern_trait_ref(def, a)
    }

    fn bounds_of(&self, owner: DefId, ord: u16) -> Vec<TraitRefId> {
        let g = self.fir.sigs.generics(owner);
        if g == fors_fir::sig::NO_GENERICS && self.fir.sigs.generics_store.is_empty() {
            return Vec::new();
        }
        let n = self.fir.sigs.generics_store.count(g);
        // A trait's own list is `[Self, P1 ..]` and its parameters' ordinals
        // start at 1 (`lower_generics`), so an ordinal is the row index for
        // every kind of owner.
        let idx = ord as usize;
        if idx >= n {
            return Vec::new();
        }
        let p = self.fir.sigs.generics_store.param(g, idx);
        let mut out = self.fir.sigs.bounds.get(p.bounds).to_vec();
        // R62: a constraint entry's traits are bounds of the neutral `P.A`,
        // not of `P`; they are read where a projection is the subject.
        out.dedup();
        out
    }

    /// A trait reference in a bound, an impl header or after `dyn`.
    pub fn trait_ref(&mut self, cx: &mut Cx, node: usize) -> Option<TraitRefId> {
        if cx.f.kind(node) != NodeKind::TypeApp {
            return None;
        }
        let head = self.head_of(cx, node);
        let Head::Trait(def) = head else { return None };
        let range = cx.f.range(node);
        let arity = self.shapes.arity(def);
        let args: Vec<usize> = cx.f.tree.children(node).collect();
        if args.len() != arity {
            let n = self
                .defs
                .get(def)
                .and_then(|r| r.name)
                .map(|s| format!("`{}`", String::from_utf8_lossy(self.names.resolve(s))))
                .unwrap_or_else(|| "this trait".to_string());
            self.emit(
                cx,
                range,
                11,
                11,
                format!(
                    "{n} declares {arity} type argument(s), {} supplied",
                    args.len()
                ),
            );
            return None;
        }
        let xs: Vec<TyId> = args.iter().map(|&c| self.ty(cx, c, Pos::Value)).collect();
        if xs.contains(&TY_ERROR) {
            return None;
        }
        if xs.len() > MAX_LIST {
            return None;
        }
        let a = self.fir.tys.intern_args(&xs);
        Some(self.fir.tys.intern_trait_ref(def, a))
    }

    fn emit(&mut self, cx: &Cx, range: (u32, u32), code: u16, site: u16, msg: String) {
        self.sink.emit(cx.f.file, range, t(code), site, msg);
    }
}

fn is_type_node(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::TypeApp
            | NodeKind::QualType
            | NodeKind::TupleType
            | NodeKind::FnType
            | NodeKind::DynType
            | NodeKind::ScopedType
    )
}

/// The integer value of an `Int` token's text: decimal, `0x`/`0o`/`0b`, `_`
/// separators, optional type suffix (ch07 R5). `None` when it overflows
/// `i128` or is not an integer literal at all.
pub fn parse_int_literal(txt: &[u8]) -> Option<i128> {
    let mut i = 0usize;
    let mut radix = 10u32;
    if txt.len() >= 2 && txt[0] == b'0' {
        match txt[1] | 0x20 {
            b'x' => {
                radix = 16;
                i = 2;
            }
            b'o' => {
                radix = 8;
                i = 2;
            }
            b'b' => {
                radix = 2;
                i = 2;
            }
            _ => {}
        }
    }
    let mut v: i128 = 0;
    let mut any = false;
    while i < txt.len() {
        let c = txt[i];
        if c == b'_' {
            i += 1;
            continue;
        }
        let d = (c as char).to_digit(radix);
        match d {
            Some(d) => {
                v = v.checked_mul(radix as i128)?.checked_add(d as i128)?;
                any = true;
                i += 1;
            }
            None => break, // the suffix starts here
        }
    }
    any.then_some(v)
}

// ------------------------------------------------------- declarations

/// What lowering an `impl`/`trait` head produced, for its own members to read.
#[derive(Clone)]
pub struct HeadInfo {
    pub self_ty: TyId,
    pub trait_def: DefId,
    pub trait_ref: TraitRefId,
    /// An impl's own `type A = RHS;` definitions (R61(c)).
    pub assoc: Vec<(Symbol, TyId)>,
    pub kind: SelfKind,
    /// The head's declaration node, which `Self` resolves to.
    pub node: u32,
}

/// The whole-build result of pass B.
pub struct Lowered {
    pub sites: Sites,
    /// One entry per `impl`/`trait`, in `DefId` order — not one slot per
    /// declaration: a build's declarations are mostly `fn`s, and a `Vec`
    /// indexed by `DefId` would be nine tenths empty `HeadInfo` slots.
    heads: Vec<(DefId, HeadInfo)>,
    pub impls: fors_fir::impls::ImplIndex,
    /// Per declaration: was a diagnostic already charged to it (so whole-head
    /// well-formedness stays silent about a signature it cannot trust).
    pub poisoned: Vec<bool>,
}

impl Lowered {
    /// What lowering `def`'s `impl`/`trait` head produced, if it is one.
    pub fn head(&self, def: DefId) -> Option<&HeadInfo> {
        self.heads
            .binary_search_by_key(&def.0, |&(d, _)| d.0)
            .ok()
            .map(|i| &self.heads[i].1)
    }
}

impl Lowerer<'_> {
    /// Lowers every user declaration in `(file, tree)` order (design §7.1
    /// phase 3). A declaration's parent always precedes it, because
    /// `build_decl_table` pushes rows in tree order.
    pub fn run(&mut self, files: &[FileCtx]) -> Lowered {
        let n = self.fir.sigs.len();
        let mut out = Lowered {
            sites: Sites::default(),
            heads: Vec::new(),
            impls: fors_fir::impls::ImplIndex::new(),
            poisoned: vec![false; n],
        };
        let mut order = 0u32;
        let user: Vec<DefId> = self.defs.user_defs().map(|(d, _)| d).collect();
        for def in user {
            let row = *self.defs.get(def).expect("user def has a row");
            let f = &files[row.file.index()];
            self.sink.open();
            let before = self.sink.len();
            let mut cx = Cx::new(f, def);
            cx.home = def;
            self.build_scope(&mut cx, def, &out);
            match row.kind {
                DeclKind::Struct => self.lower_struct(&mut cx, def, row.node as usize),
                DeclKind::Enum => self.lower_enum(&mut cx, def, row.node as usize),
                DeclKind::Trait => {
                    let info = self.lower_trait(&mut cx, def, row.node as usize);
                    out.heads.push((def, info));
                }
                DeclKind::Impl => {
                    let info = self.lower_impl(
                        &mut cx,
                        def,
                        row.node as usize,
                        &mut out.impls,
                        &mut order,
                    );
                    out.heads.push((def, info));
                }
                DeclKind::Fn | DeclKind::ExternFn => self.lower_fn(&mut cx, def, row.node as usize),
                DeclKind::Const => self.lower_const(&mut cx, def, row.node as usize),
                _ => {}
            }
            if self.sink.len() > before {
                out.poisoned[def.index()] = true;
            }
        }
        out.impls.finish();
        out.sites = std::mem::take(&mut self.sites);
        out
    }

    /// The generic parameters in scope for `def`: its enclosing `impl`/
    /// `trait`'s, then its own (R62's constraint entries introduce no name).
    pub(crate) fn build_scope(&mut self, cx: &mut Cx, def: DefId, out: &Lowered) {
        let row = *self.defs.get(def).expect("row");
        if row.parent != NO_DEF {
            if let Some(p) = self.defs.get(row.parent).copied() {
                self.push_gparams(cx, row.parent, p.node as usize);
            }
            if let Some(info) = out.head(row.parent) {
                cx.self_node = info.node;
                cx.self_ty = info.self_ty;
                cx.self_kind = info.kind;
                cx.impl_assoc = info.assoc.clone();
            }
        }
        self.push_gparams(cx, def, row.node as usize);
        if matches!(row.kind, DeclKind::Trait) {
            cx.self_node = row.node;
            cx.self_ty = self.fir.tys.param(def, 0);
            cx.self_kind = SelfKind::Trait(def);
        }
    }

    fn push_gparams(&mut self, cx: &mut Cx, owner: DefId, node: usize) {
        let shapes = self.shapes;
        let gnode = shapes.generics_node(owner);
        if gnode == u32::MAX {
            return;
        }
        let gkinds = shapes.gkinds(owner);
        let is_trait = self.defs.get(owner).map(|r| r.kind) == Some(DeclKind::Trait);
        let mut ordinal: u16 = if is_trait { 1 } else { 0 };
        let mut i = 0usize;
        for g in cx.f.tree.children(gnode as usize) {
            if cx.f.kind(g) != NodeKind::GParam {
                continue;
            }
            let k = gkinds.get(i).copied().unwrap_or(GKind::Type);
            cx.scope.push((g as u32, owner, ordinal, k));
            ordinal += 1;
            i += 1;
        }
        let _ = node;
    }

    /// The `GParam` rows themselves (R15's classification, R13's const type,
    /// the bounds) plus R62's constraint entries.
    ///
    /// In three steps, because a bound may read the list it is part of: a
    /// callable parameter's `fn` type and a constraint entry's subject can
    /// both mention a projection on an EARLIER parameter
    /// (`F: fn(sink I.Item) -> U`), and R61(c) answers `I.Item` from `I`'s
    /// bounds. So the row is pushed with every name and trait bound first,
    /// then the const/callable bounds, then the entries.
    fn lower_generics(&mut self, cx: &mut Cx, def: DefId, allow_constraints: bool) {
        let shapes = self.shapes;
        let gnode = shapes.generics_node(def);
        let gkinds = shapes.gkinds(def);
        let is_trait = self.defs.get(def).map(|r| r.kind) == Some(DeclKind::Trait);
        let mut params: Vec<GParam> = Vec::new();
        if is_trait {
            // R8: a trait's own list is `[Self, P1 ..]`; `Self`'s single bound
            // is the trait itself with its own parameters.
            let tr_self = self.own_trait_ref(def);
            let b = self.fir.sigs.bounds.intern(&[tr_self]);
            params.push(GParam {
                name: self.prelude.self_name,
                kind: GParamKind::Type,
                bounds: b,
            });
        }
        let base = params.len();
        let mut gparam_nodes: Vec<usize> = Vec::new();
        let mut constraint_nodes: Vec<usize> = Vec::new();
        if gnode != u32::MAX {
            for g in cx.f.tree.children(gnode as usize).collect::<Vec<_>>() {
                match cx.f.kind(g) {
                    NodeKind::GParam => gparam_nodes.push(g),
                    NodeKind::GConstraint => constraint_nodes.push(g),
                    _ => {}
                }
            }
        }
        // Step 1: names, and the trait bounds of a type parameter.
        for (i, &g) in gparam_nodes.iter().enumerate() {
            let name =
                cx.f.own_idents(self.names, g)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let kind = gkinds.get(i).copied().unwrap_or(GKind::Type);
            let bound_nodes: Vec<usize> = cx.f.tree.children(g).collect();
            let gp = match kind {
                GKind::Brand => GParam {
                    name,
                    kind: GParamKind::Brand,
                    bounds: NO_BOUNDS,
                },
                GKind::Type => {
                    let mut bs: Vec<TraitRefId> = Vec::new();
                    for &b in &bound_nodes {
                        if let Some(tr) = self.trait_ref(cx, b) {
                            bs.push(tr);
                        }
                    }
                    self.add_implied(&mut bs);
                    if bs.len() > MAX_LIST {
                        let r = cx.f.range(g);
                        self.emit(cx, r, 15, 15, limit_msg("a bound list", bs.len(), MAX_LIST));
                        bs.truncate(MAX_LIST);
                    }
                    let id = self.fir.sigs.bounds.intern(&bs);
                    GParam {
                        name,
                        kind: GParamKind::Type,
                        bounds: id,
                    }
                }
                // Filled in step 2.
                _ => GParam {
                    name,
                    kind: GParamKind::Type,
                    bounds: NO_BOUNDS,
                },
            };
            params.push(gp);
        }
        if params.len() > MAX_LIST {
            let r = if gnode != u32::MAX {
                cx.f.range(gnode as usize)
            } else {
                (0, 0)
            };
            self.emit(
                cx,
                r,
                15,
                15,
                limit_msg("a generic parameter list", params.len(), MAX_LIST),
            );
            params.truncate(MAX_LIST);
        }
        let gid = self.fir.sigs.generics_store.push(&params, NO_CONSTRAINTS);
        self.fir.sigs.set_generics(def, gid);

        // Step 2: the bound of a const, callable or ill-classified parameter.
        for (i, &g) in gparam_nodes.iter().enumerate() {
            let kind = gkinds.get(i).copied().unwrap_or(GKind::Type);
            if matches!(kind, GKind::Brand | GKind::Type) {
                continue;
            }
            let bound_nodes: Vec<usize> = cx.f.tree.children(g).collect();
            match kind {
                GKind::Const => {
                    let ty = self.ty(cx, bound_nodes[0], Pos::Value);
                    // R13: a const parameter's type MUST be an integer type
                    // or `bool`.
                    let ok = match self.fir.tys.tag(ty) {
                        fors_fir::ty::TyTag::Prim => {
                            let p = PrimKind::from_u8(self.fir.tys.a(ty) as u8);
                            p.is_some_and(|p| p.is_integer() || p == PrimKind::Bool)
                        }
                        _ => ty == TY_ERROR,
                    };
                    if !ok {
                        let r = cx.f.range(bound_nodes[0]);
                        self.emit(
                            cx,
                            r,
                            13,
                            13,
                            "a const parameter's type must be an integer type or `bool`"
                                .to_string(),
                        );
                    }
                    self.fir.sigs.generics_store.set_param(
                        gid,
                        base + i,
                        GParamKind::Const { ty },
                        NO_BOUNDS,
                    );
                }
                GKind::Callable => {
                    let fn_ty = self.ty(cx, bound_nodes[0], Pos::Value);
                    self.fir.sigs.generics_store.set_param(
                        gid,
                        base + i,
                        GParamKind::Callable { fn_ty },
                        NO_BOUNDS,
                    );
                }
                _ => {
                    // R15: bounds MUST be all traits, or exactly one non-trait
                    // type, or exactly one `fn` type. Anything else is this
                    // rule's error — unless a bound simply did not resolve, in
                    // which case the resolver already spoke.
                    if bound_nodes.iter().all(|&b| self.bound_resolved(cx, b)) {
                        let r = cx.f.range(g);
                        self.emit(cx, r, 15, 15, "bounds must be all traits, or exactly one non-trait type, or exactly one `fn` type".to_string());
                    }
                    let mut bs: Vec<TraitRefId> = Vec::new();
                    for &b in &bound_nodes {
                        if let Some(tr) = self.trait_ref(cx, b) {
                            bs.push(tr);
                        }
                    }
                    if bs.len() > MAX_LIST {
                        let r = cx.f.range(g);
                        self.emit(cx, r, 15, 15, limit_msg("a bound list", bs.len(), MAX_LIST));
                        bs.truncate(MAX_LIST);
                    }
                    let id = self.fir.sigs.bounds.intern(&bs);
                    self.fir
                        .sigs
                        .generics_store
                        .set_param(gid, base + i, GParamKind::Type, id);
                }
            }
        }

        // Step 3: R62's entries, which resolve against the rows just filled.
        let mut entries: Vec<(TyId, fors_fir::sig::TraitRefListId)> = Vec::new();
        for g in constraint_nodes {
            if let Some(e) = self.lower_constraint(cx, g, allow_constraints) {
                entries.push(e);
            }
        }
        if entries.len() > MAX_LIST {
            let r = if gnode != u32::MAX {
                cx.f.range(gnode as usize)
            } else {
                (0, 0)
            };
            self.emit(
                cx,
                r,
                62,
                62,
                limit_msg("a constraint-entry list", entries.len(), MAX_LIST),
            );
            entries.truncate(MAX_LIST);
        }
        if !entries.is_empty() {
            let cl = self.fir.sigs.constraints.push(&entries);
            self.fir.sigs.generics_store.set_constraints(gid, cl);
        }
    }

    /// R21: `P: IndexMut[I]` implies `P: Index[I]`; `P: Iterator` implies
    /// `P: Droppable`; R23: `X: Copyable` implies `X: Droppable`.
    fn add_implied(&mut self, bs: &mut Vec<TraitRefId>) {
        let mut extra: Vec<TraitRefId> = Vec::new();
        for &b in bs.iter() {
            let (def, args) = self.fir.tys.trait_ref(b);
            if def == self.prelude.traits[tr::INDEXMUT] {
                extra.push(
                    self.fir
                        .tys
                        .intern_trait_ref(self.prelude.traits[tr::INDEX], args),
                );
            }
            if def == self.prelude.traits[tr::ITERATOR] || def == self.prelude.traits[tr::COPYABLE]
            {
                extra.push(
                    self.fir
                        .tys
                        .intern_trait_ref(self.prelude.traits[tr::DROPPABLE], NO_ARGS),
                );
            }
        }
        for e in extra {
            if !bs.contains(&e) {
                bs.push(e);
            }
        }
    }

    fn bound_resolved(&mut self, cx: &mut Cx, node: usize) -> bool {
        match cx.f.kind(node) {
            NodeKind::FnType => true,
            NodeKind::TypeApp => !matches!(self.head_of(cx, node), Head::Silent | Head::Opaque),
            _ => true,
        }
    }

    /// R62 (static side).
    fn lower_constraint(
        &mut self,
        cx: &mut Cx,
        node: usize,
        allowed: bool,
    ) -> Option<(TyId, fors_fir::sig::TraitRefListId)> {
        let range = cx.f.range(node);
        if !allowed {
            self.emit(
                cx,
                range,
                62,
                62,
                "a constraint entry is legal only in the generics of a `fn`".to_string(),
            );
            return None;
        }
        let nsegs = cx.f.own_ident_count(node);
        if nsegs < 2 {
            return None;
        }
        let head = self.head_of(cx, node);
        let subject = self.projection(cx, node, nsegs, 1, head, Pos::Value);
        let bound_nodes: Vec<usize> = cx.f.tree.children(node).collect();
        let mut bs: Vec<TraitRefId> = Vec::new();
        for &b in &bound_nodes {
            match cx.f.kind(b) {
                NodeKind::TypeApp => match self.trait_ref(cx, b) {
                    Some(tr) => bs.push(tr),
                    None => {
                        if self.bound_resolved(cx, b) {
                            let r = cx.f.range(b);
                            self.emit(
                                cx,
                                r,
                                62,
                                62,
                                "every bound of a constraint entry must be a trait".to_string(),
                            );
                        }
                    }
                },
                _ => {
                    let r = cx.f.range(b);
                    self.emit(
                        cx,
                        r,
                        62,
                        62,
                        "every bound of a constraint entry must be a trait".to_string(),
                    );
                }
            }
        }
        self.add_implied(&mut bs);
        if subject == TY_ERROR {
            return None;
        }
        let id = self.fir.sigs.bounds.intern(&bs);
        Some((subject, id))
    }

    fn lower_struct(&mut self, cx: &mut Cx, def: DefId, node: usize) {
        self.lower_generics(cx, def, false);
        let mut ms: Vec<Member> = Vec::new();
        for (c, k) in cx.f.child_kinds(node) {
            if k != NodeKind::Field {
                continue;
            }
            let name =
                cx.f.own_idents(self.names, c)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let vis = if cx.f.own_has_kind(c, TokenKind::KwPub) {
                VIS_PUBLIC
            } else {
                VIS_PRIVATE
            };
            let ty = match cx.f.tree.children(c).next() {
                Some(x) => self.ty(cx, x, Pos::Value),
                None => TY_ERROR,
            };
            ms.push(Member::field(name, vis, ty));
        }
        let l = self.fir.sigs.member_store.push(&ms);
        self.fir.sigs.set_members(def, l);
        if self.defs.get(def).is_some() && cx.f.own_has_ident(node, b"soa") {
            self.fir.sigs.set_soa(def, true);
        }
    }

    fn lower_enum(&mut self, cx: &mut Cx, def: DefId, node: usize) {
        self.lower_generics(cx, def, false);
        let mut ms: Vec<Member> = Vec::new();
        for (c, k) in cx.f.child_kinds(node) {
            if k != NodeKind::EVariant {
                continue;
            }
            let name =
                cx.f.own_idents(self.names, c)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let kids: Vec<(usize, NodeKind)> = cx.f.child_kinds(c);
            if kids.is_empty() {
                ms.push(Member::unit_variant(name));
            } else if kids.iter().all(|&(_, k)| k == NodeKind::Field) {
                let mut fs: Vec<Member> = Vec::new();
                for &(fc, _) in &kids {
                    let fname =
                        cx.f.own_idents(self.names, fc)
                            .first()
                            .map(|&(s, _)| s)
                            .unwrap_or(Symbol(0));
                    let vis = if cx.f.own_has_kind(fc, TokenKind::KwPub) {
                        VIS_PUBLIC
                    } else {
                        VIS_PRIVATE
                    };
                    let ty = match cx.f.tree.children(fc).next() {
                        Some(x) => self.ty(cx, x, Pos::Value),
                        None => TY_ERROR,
                    };
                    fs.push(Member::field(fname, vis, ty));
                }
                let sub = self.fir.sigs.member_store.push(&fs);
                ms.push(Member::record_variant(name, sub));
            } else {
                let xs: Vec<TyId> = kids
                    .iter()
                    .map(|&(x, _)| self.ty(cx, x, Pos::Value))
                    .collect();
                let xs = if xs.len() > MAX_LIST {
                    let r = cx.f.range(node);
                    self.emit(
                        cx,
                        r,
                        6,
                        6,
                        limit_msg("a variant's payload", xs.len(), MAX_LIST),
                    );
                    xs[..MAX_LIST].to_vec()
                } else {
                    xs
                };
                let a = self.fir.tys.intern_args(&xs);
                ms.push(Member::tuple_variant(name, a));
            }
        }
        let l = self.fir.sigs.member_store.push(&ms);
        self.fir.sigs.set_members(def, l);
    }

    fn lower_trait(&mut self, cx: &mut Cx, def: DefId, node: usize) -> HeadInfo {
        cx.self_node = node as u32;
        cx.self_ty = self.fir.tys.param(def, 0);
        cx.self_kind = SelfKind::Trait(def);
        self.lower_generics(cx, def, false);
        // R16: `type A: Tr1 + ... + Trk;` — every `Tri` MUST be a trait.
        let mut assoc: Vec<Assoc> = Vec::new();
        for (c, k) in cx.f.child_kinds(node) {
            if k != NodeKind::AssocTypeDecl {
                continue;
            }
            let name =
                cx.f.own_idents(self.names, c)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let mut bs: Vec<TraitRefId> = Vec::new();
            for b in cx.f.tree.children(c).collect::<Vec<_>>() {
                match cx.f.kind(b) {
                    NodeKind::TypeApp => match self.trait_ref(cx, b) {
                        Some(tr) => bs.push(tr),
                        None => {
                            if self.bound_resolved(cx, b) {
                                let r = cx.f.range(b);
                                self.emit(
                                    cx,
                                    r,
                                    16,
                                    16,
                                    "every bound of an associated type must be a trait".to_string(),
                                );
                            }
                        }
                    },
                    _ => {
                        let r = cx.f.range(b);
                        self.emit(
                            cx,
                            r,
                            16,
                            16,
                            "every bound of an associated type must be a trait".to_string(),
                        );
                    }
                }
            }
            self.add_implied(&mut bs);
            if bs.len() > MAX_LIST {
                let r = cx.f.range(node);
                self.emit(
                    cx,
                    r,
                    16,
                    16,
                    limit_msg("an associated type's bound list", bs.len(), MAX_LIST),
                );
                bs.truncate(MAX_LIST);
            }
            let id = self.fir.sigs.bounds.intern(&bs);
            assoc.push(Assoc {
                name,
                bounds: id,
                rhs: NO_TY,
            });
        }
        if assoc.len() > MAX_LIST {
            let r = cx.f.range(node);
            self.emit(
                cx,
                r,
                16,
                16,
                limit_msg("a trait's associated-type list", assoc.len(), MAX_LIST),
            );
            assoc.truncate(MAX_LIST);
        }
        let a = self.fir.sigs.assocs.push(&assoc);
        self.fir.sigs.set_assoc(def, a);
        self.member_items(cx, def, node);
        HeadInfo {
            self_ty: cx.self_ty,
            trait_def: def,
            trait_ref: self.own_trait_ref(def),
            assoc: Vec::new(),
            kind: SelfKind::Trait(def),
            node: node as u32,
        }
    }

    fn lower_impl(
        &mut self,
        cx: &mut Cx,
        def: DefId,
        node: usize,
        index: &mut fors_fir::impls::ImplIndex,
        order: &mut u32,
    ) -> HeadInfo {
        self.lower_generics(cx, def, false);
        // The header types: everything that is not the generics list, a
        // member or trivia. With `for` there are two; without, one.
        let header: Vec<usize> =
            cx.f.child_kinds(node)
                .into_iter()
                .filter(|&(_, k)| {
                    !matches!(
                        k,
                        NodeKind::Generics
                            | NodeKind::FnDecl
                            | NodeKind::TraitItem
                            | NodeKind::AssocTypeDecl
                            | NodeKind::AssocTypeDef
                            | NodeKind::Attribute
                            | NodeKind::Error
                    )
                })
                .map(|(c, _)| c)
                .collect();
        let (trait_node, self_node) = match header.len() {
            0 => (None, None),
            1 => (None, Some(header[0])),
            _ => (Some(header[0]), Some(header[1])),
        };
        let mut trait_def = NO_DEF;
        let mut trait_ref = fors_fir::sig::NO_TRAIT_REF;
        if let Some(tn) = trait_node {
            // R18: the first type MUST be a trait.
            match self.head_of(cx, tn) {
                Head::Trait(d) => {
                    trait_def = d;
                    if let Some(x) = self.trait_ref(cx, tn) {
                        trait_ref = x;
                    }
                }
                Head::Silent | Head::Opaque => {}
                _ => {
                    let r = cx.f.range(tn);
                    self.emit(
                        cx,
                        r,
                        18,
                        18,
                        "the first type of an `impl ... for ...` must be a trait".to_string(),
                    );
                }
            }
        }
        let self_ty = match self_node {
            Some(sn) => {
                let ty = self.ty(cx, sn, Pos::ImplSelf);
                if trait_node.is_some()
                    && let Head::Trait(_) = self.head_of(cx, sn)
                {
                    let r = cx.f.range(sn);
                    self.emit(
                        cx,
                        r,
                        18,
                        18,
                        "the second type of an `impl ... for ...` must not be a trait".to_string(),
                    );
                }
                ty
            }
            None => TY_ERROR,
        };
        cx.self_node = node as u32;
        cx.self_ty = self_ty;
        cx.self_kind = SelfKind::Impl { trait_def };
        cx.assoc_rhs_owner = def;
        self.fir.sigs.set_self_ty(def, self_ty);
        if trait_ref != fors_fir::sig::NO_TRAIT_REF {
            self.fir.sigs.set_trait_ref(def, trait_ref);
        }
        // `type A = RHS;`
        let mut assoc: Vec<Assoc> = Vec::new();
        for (c, k) in cx.f.child_kinds(node) {
            if k != NodeKind::AssocTypeDef {
                continue;
            }
            let name =
                cx.f.own_idents(self.names, c)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let rhs = match cx.f.tree.children(c).next() {
                Some(x) => self.ty(cx, x, Pos::AssocRhs),
                None => TY_ERROR,
            };
            if !assoc.iter().any(|a| a.name == name) {
                assoc.push(Assoc {
                    name,
                    bounds: NO_BOUNDS,
                    rhs,
                });
            }
        }
        if assoc.len() > MAX_LIST {
            let r = cx.f.range(node);
            self.emit(
                cx,
                r,
                17,
                17,
                limit_msg("an impl's associated-type list", assoc.len(), MAX_LIST),
            );
            assoc.truncate(MAX_LIST);
        }
        let a = self.fir.sigs.assocs.push(&assoc);
        self.fir.sigs.set_assoc(def, a);
        cx.impl_assoc = assoc.iter().map(|a| (a.name, a.rhs)).collect();
        self.member_items(cx, def, node);
        if self_ty != TY_ERROR {
            let head = self.fir.tys.head_key(self_ty);
            let trait_args = if trait_ref == fors_fir::sig::NO_TRAIT_REF {
                NO_ARGS
            } else {
                self.fir.tys.trait_ref(trait_ref).1
            };
            index.push(fors_fir::impls::ImplRow {
                def,
                trait_def,
                inherent: trait_node.is_none(),
                trait_args,
                self_ty,
                head,
                order: *order,
            });
            *order += 1;
        }
        HeadInfo {
            self_ty,
            trait_def,
            trait_ref,
            assoc: cx.impl_assoc.clone(),
            kind: SelfKind::Impl { trait_def },
            node: node as u32,
        }
    }

    /// The `fn` members of a trait or impl, as the head's member list.
    fn member_items(&mut self, cx: &mut Cx, def: DefId, node: usize) {
        let mut ms: Vec<Member> = Vec::new();
        for (c, k) in cx.f.child_kinds(node) {
            if !matches!(k, NodeKind::FnDecl | NodeKind::TraitItem) {
                continue;
            }
            let sig =
                cx.f.tree
                    .children(c)
                    .find(|&x| cx.f.kind(x) == NodeKind::FnSig)
                    .unwrap_or(c);
            let name =
                cx.f.own_idents(self.names, sig)
                    .first()
                    .map(|&(s, _)| s)
                    .unwrap_or(Symbol(0));
            let vis = if cx.f.own_has_kind(c, TokenKind::KwPub) {
                VIS_PUBLIC
            } else {
                VIS_PRIVATE
            };
            // A `TraitItem` has no `DeclTable` row of its own unless the
            // index gave it one; `def_of` answers `NO_DEF` otherwise.
            let mdef = self.member_def(cx, c);
            ms.push(Member::item(name, vis, mdef));
        }
        let l = self.fir.sigs.member_store.push(&ms);
        self.fir.sigs.set_members(def, l);
    }

    fn member_def(&self, cx: &Cx, node: usize) -> DefId {
        self.defs.def_at(cx.f.file, node as u32)
    }

    fn lower_fn(&mut self, cx: &mut Cx, def: DefId, node: usize) {
        let sig_node =
            cx.f.tree
                .children(node)
                .find(|&c| cx.f.kind(c) == NodeKind::FnSig);
        let Some(sig_node) = sig_node else {
            self.lower_generics(cx, def, true);
            return;
        };
        self.lower_generics(cx, def, true);
        let mut params: Vec<Param> = Vec::new();
        let mut result = TY_UNIT;
        let mut raises = NO_TY;
        let mut scoped = NO_SLOT;
        let mut receiver = NO_SLOT;
        let mut seen_params = false;
        for (c, k) in cx.f.child_kinds(sig_node) {
            match k {
                NodeKind::Generics => {}
                NodeKind::Params => {
                    seen_params = true;
                    for (p, pk) in cx.f.child_kinds(c) {
                        if pk != NodeKind::Param {
                            continue;
                        }
                        let conv = self.conv_of(cx, p);
                        let idents = cx.f.own_idents(self.names, p);
                        let name = idents.first().map(|&(s, _)| s).unwrap_or(Symbol(0));
                        let is_self = self.names.resolve(name) == b"self";
                        let annot = cx.f.tree.children(p).next();
                        let ty = match annot {
                            Some(x) => self.ty(cx, x, Pos::Value),
                            // The receiver shorthand `fn next(inout self)`
                            // means exactly `self: Self` (R16, ch07 D21).
                            None if is_self => {
                                if cx.self_ty == NO_TY {
                                    TY_ERROR
                                } else {
                                    cx.self_ty
                                }
                            }
                            None => TY_ERROR,
                        };
                        if is_self && params.is_empty() {
                            receiver = 0;
                            // R16: a parameter named `self` MUST have type
                            // `Self` (in an impl: the self type).
                            if let Some(a) = annot
                                && cx.self_ty != NO_TY
                                && ty != TY_ERROR
                                && self.fir.tys.unqual(ty) != self.fir.tys.unqual(cx.self_ty)
                            {
                                let r = cx.f.range(a);
                                self.emit(
                                    cx,
                                    r,
                                    16,
                                    16,
                                    "a parameter named `self` must have the type `Self`"
                                        .to_string(),
                                );
                            }
                        }
                        params.push(Param { name, conv, ty });
                    }
                }
                NodeKind::Raises => {
                    raises = match cx.f.tree.children(c).next() {
                        Some(x) => self.ty(cx, x, Pos::Value),
                        None => TY_ERROR,
                    };
                }
                NodeKind::ScopedType => {
                    result = self.ty(cx, c, Pos::Value);
                    // MARC: verification of I2 (2026-09-20). The designated
                    // parameter was recorded as slot 0 whatever `scoped(p)`
                    // named; the corpus writes `scoped(v)`, `scoped(bytes)`
                    // and `scoped(a)` on second parameters, and ch01 R19
                    // makes the designation observable (R17 compares it;
                    // the sig hash carries it). It is the index of the
                    // parameter the identifier names; a name that matches
                    // no parameter is left to ch01/ch08 and keeps slot 0.
                    let designated = cx.f.own_idents(self.names, c).first().map(|&(s, _)| s);
                    scoped = designated
                        .and_then(|d| params.iter().position(|p| p.name == d))
                        .and_then(|i| u8::try_from(i).ok())
                        .filter(|&i| i != NO_SLOT)
                        .unwrap_or(0);
                }
                NodeKind::Contract | NodeKind::Block | NodeKind::Attribute | NodeKind::Error => {}
                _ if seen_params && is_type_node(k) => result = self.ty(cx, c, Pos::Value),
                _ => {}
            }
        }
        if params.len() > MAX_PARAMS {
            let r = cx.f.range(sig_node);
            self.emit(
                cx,
                r,
                7,
                7,
                limit_msg("a parameter list", params.len(), MAX_PARAMS),
            );
            params.truncate(MAX_PARAMS);
        }
        let id = self.fir.sigs.fn_sigs.push(
            &params,
            result,
            raises,
            scoped,
            receiver,
            (u32::MAX, u32::MAX),
            0,
        );
        self.fir.sigs.set_fn_sig(def, id);
    }

    fn lower_const(&mut self, cx: &mut Cx, def: DefId, node: usize) {
        let kids: Vec<(usize, NodeKind)> = cx.f.child_kinds(node);
        let ty = kids
            .iter()
            .find(|&&(_, k)| is_type_node(k))
            .map(|&(c, _)| self.ty(cx, c, Pos::Value))
            .unwrap_or(TY_ERROR);
        let val = kids
            .iter()
            .find(|&&(_, k)| k == NodeKind::Literal)
            .and_then(|&(c, _)| self.literal_value(cx, c))
            .map(|v| self.fir.tys.intern_const(v))
            .unwrap_or(fors_fir::ty::NO_CONST);
        self.fir.sigs.set_const(def, ty, val);
    }
}

#[cfg(test)]
mod tests {
    use super::parse_int_literal;

    #[test]
    fn integer_literals_parse_in_every_base_with_separators_and_suffixes() {
        assert_eq!(parse_int_literal(b"0"), Some(0));
        assert_eq!(parse_int_literal(b"10"), Some(10));
        assert_eq!(parse_int_literal(b"1_000"), Some(1000));
        assert_eq!(parse_int_literal(b"0xFF"), Some(255));
        assert_eq!(parse_int_literal(b"0b1011"), Some(11));
        assert_eq!(parse_int_literal(b"0o17"), Some(15));
        assert_eq!(parse_int_literal(b"16usize"), Some(16));
        assert_eq!(parse_int_literal(b"0xFFu8"), Some(255));
        // Not an integer literal at all, and an overflow: neither panics.
        assert_eq!(parse_int_literal(b"usize"), None);
        assert_eq!(
            parse_int_literal(b"999999999999999999999999999999999999999999"),
            None
        );
    }
}
