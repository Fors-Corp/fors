//! Pattern typing against the scrutinee type (design §7.8; ch09 R50-R52).
//!
//! `check_pat` is R50 verbatim: wildcard, `let n` (R51, via [`Wf::bind_let`]),
//! literals by the scrutinee's kind (floats rejected), tuples by arity,
//! paths/dot-literals to a unit variant or a `const`, payloads by variant,
//! `{}` payloads by visible fields with omitted fields matching anything.
//! Every pattern also lowers into a [`PatStore`] node, which
//! `exhaust::check_match` reads for R53-R55's usefulness algorithm — one
//! walk serves both jobs, so there is exactly one diagnostic per pattern
//! node (ch03 R25's CHECK position) and exhaustiveness never re-derives
//! what typing already decided.
//!
//! I10a adds a third consumer to the same walk: the decision is PUBLISHED
//! on [`BodyFacts::patterns`](crate::facts::BodyFacts::patterns) as a
//! [`PatShape`] tree, so FMIR lowering reads which variant, which fields in
//! which order, which literal and which binding an arm tests instead of
//! re-deriving any of it. The two trees differ in one way on purpose: the
//! [`PatStore`] shares one cached wildcard node for `_` and `let n`, which
//! the usefulness walk may, and lowering may NOT.

use fors_fir::constval::{ConstValue, fits};
use fors_fir::{
    ArgsId, Member, MemberKind, NO_ARGS, NO_TY, PayloadKind, PrimKind, SigKind, TY_ERROR, TyId,
    TyTag,
};
use fors_index::Symbol;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::target::{DeferReason, Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::{BodyCx, LocalKind};
use crate::facts::PatShape;
use crate::lower::{parse_int_literal, str_contents};
use crate::wf::Wf;
use fors_fir::sig::{Conv, VIS_PRIVATE};
use fors_index::diag::Code;

/// One constructor a lowered pattern tests (design §7.8). A `const`
/// pattern lowers to `Int`/`Bool`/`Str` of its comptime value, so an equal
/// constant and literal are the same constructor (R53/R54).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ctor {
    Variant(DefId, u32),
    Bool(bool),
    Tuple(u32),
    Struct(DefId),
    Int(i128),
    Str(Symbol),
}

#[derive(Clone, Copy, Debug)]
enum PKind {
    Wild,
    Ctor(Ctor),
}

/// An index into a [`PatStore`].
pub type PatId = u32;

/// The arena one `match`'s patterns lower into (design §7.8's `PatStore`):
/// struct-of-arrays (`kind`+`ctor` folded into [`PKind`], `sub_start`,
/// `sub_len`), every node's children a contiguous span of `subs`. `_` and
/// `let n` share one cached wildcard node, so specialising a wildcard row
/// by an arity-N constructor can splice in N copies of the same id without
/// growing the store (design §7.8: "no memoisation" governs the
/// *usefulness* walk, not this one-time lowering).
pub struct PatStore {
    kind: Vec<PKind>,
    sub_start: Vec<u32>,
    sub_len: Vec<u32>,
    subs: Vec<PatId>,
    wild_id: PatId,
    /// R55's "the match's pattern-node count": one per pattern node the
    /// SOURCE writes (every `check_pat` dispatch, plus an `{ x }` field
    /// shorthand) — independent of how many arena rows above this ends up
    /// with, since `_`/`let n` share one node there and so are NOT the
    /// count the budget is in (an implementation detail must not change
    /// where R55 fires; two `let n`s in one arm cost the budget the same
    /// as two `_`s would).
    node_count: u32,
}

impl Default for PatStore {
    fn default() -> Self {
        Self::new()
    }
}

impl PatStore {
    /// Eagerly reserves node 0 as the one cached wildcard, so `wild()`
    /// never needs mutation: a match with no `_`/`let n` anywhere (every
    /// arm a bare literal) still needs a wildcard for the exhaustiveness
    /// query's own `v`.
    pub fn new() -> Self {
        let mut s = PatStore {
            kind: Vec::new(),
            sub_start: Vec::new(),
            sub_len: Vec::new(),
            subs: Vec::new(),
            wild_id: 0,
            node_count: 0,
        };
        s.wild_id = s.push(PKind::Wild, &[]);
        s
    }

    /// Counts one more pattern node toward R55's budget (see
    /// [`Self::pattern_node_count`]'s doc).
    fn touch(&mut self) {
        self.node_count += 1;
    }

    /// R55's "the match's pattern-node count".
    pub fn pattern_node_count(&self) -> u32 {
        self.node_count
    }

    fn push(&mut self, k: PKind, subs: &[PatId]) -> PatId {
        let id = self.kind.len() as u32;
        let start = self.subs.len() as u32;
        self.subs.extend_from_slice(subs);
        self.kind.push(k);
        self.sub_start.push(start);
        self.sub_len.push(subs.len() as u32);
        id
    }

    /// The one cached wildcard node (`_`, `let n`, or a constructor's
    /// synthetic sub-pattern when a wildcard row is specialised).
    pub fn wild(&self) -> PatId {
        self.wild_id
    }

    fn ctor(&mut self, c: Ctor, subs: &[PatId]) -> PatId {
        self.push(PKind::Ctor(c), subs)
    }

    pub fn ctor_of(&self, id: PatId) -> Option<Ctor> {
        match self.kind[id as usize] {
            PKind::Ctor(c) => Some(c),
            PKind::Wild => None,
        }
    }

    pub fn subs(&self, id: PatId) -> &[PatId] {
        let s = self.sub_start[id as usize] as usize;
        let l = self.sub_len[id as usize] as usize;
        &self.subs[s..s + l]
    }
}

impl Wf<'_> {
    /// R50: checks `pat` against the scrutinee type `s`, binds every name
    /// it introduces, and lowers it into `store`. One diagnostic at most.
    pub fn check_pat(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
    ) -> PatId {
        // D5 (I10a): the same walk publishes the decision for lowering. The
        // row is opened before the dispatch and closed after it, so every
        // sub-pattern the dispatch visits registers itself as a child; its
        // shape starts [`PatShape::Undecided`] and each judgement below
        // sets its own, which leaves an error path honestly undecided.
        cx.facts.patterns.open(pat as u32, s);
        let id = self.check_pat_decided(cx, store, pat, s);
        cx.facts.patterns.close();
        id
    }

    fn check_pat_decided(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
    ) -> PatId {
        store.touch();
        // ch01 R22d(ii): destructuring discharges a linear obligation only
        // when the arm binds EVERY linear component with `let n`. A `_` or
        // a literal pattern facing a linear component is a drop, and the
        // code and the diagnostic are ch01's (ch09 R50 is the emission
        // site: "omitted fields match anything" is its clause).
        if matches!(cx.kind(pat), NodeKind::PatWild | NodeKind::PatLit)
            && s != TY_ERROR
            && s != NO_TY
            && self.is_linear(s)
        {
            let w = self.show(s);
            let what = if cx.kind(pat) == NodeKind::PatWild {
                "`_`"
            } else {
                "a literal pattern"
            };
            self.bemit_code(
                cx,
                pat,
                Code::O(22),
                50,
                format!(
                    "{what} faces the linear component type `{w}` and drops it: bind it with                      `let n` and consume it (ch01 R22d(ii))"
                ),
            );
            return store.wild();
        }
        match cx.kind(pat) {
            NodeKind::PatWild => {
                cx.facts.patterns.shape(PatShape::Wild);
                store.wild()
            }
            NodeKind::PatLet => {
                self.bind_let(cx, pat, s);
                let shape = self.bind_shape(s);
                cx.facts.patterns.shape(shape);
                store.wild()
            }
            NodeKind::PatLit => self.check_pat_lit(cx, store, pat, s),
            NodeKind::PatTuple => self.check_pat_tuple(cx, store, pat, s),
            NodeKind::PatDot | NodeKind::PatPath => self.check_pat_path(cx, store, pat, s),
            // A parse-error node: already diagnosed by the parser.
            _ => store.wild(),
        }
    }

    /// R51: a `let n` binding has the type of the component it faces, with
    /// the enum's or struct's own arguments substituted (the caller passes
    /// `s` already substituted). Whether it moves, copies or projects that
    /// component is ch01's.
    pub fn bind_let(&mut self, cx: &mut BodyCx, pat: usize, s: TyId) {
        cx.bind(pat as u32, s, LocalKind::Value);
    }

    /// D5 (I10a): the shape a `let n` binding publishes. The convention is
    /// the checker's own copy-or-move answer for the component type (ch01
    /// R4/R22d(ii)), so lowering reads it instead of asking `Copyable`
    /// again. A component whose type failed stays
    /// [`PatShape::Undecided`]: a `Bind` row with no type is nothing
    /// lowering could act on.
    pub(crate) fn bind_shape(&mut self, s: TyId) -> PatShape {
        if s == TY_ERROR || s == NO_TY {
            return PatShape::Undecided;
        }
        let conv = if self.copyable(s) {
            Conv::Let
        } else {
            Conv::Sink
        };
        PatShape::Bind { conv }
    }

    fn check_pat_lit(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
    ) -> PatId {
        let (a, b) = cx.f.tree.token_range(pat);
        let mut neg = false;
        let mut lit: Option<(usize, TokenKind)> = None;
        for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
            match cx.f.tokens.kinds[i] {
                TokenKind::Minus => neg = true,
                k @ (TokenKind::Int
                | TokenKind::Float
                | TokenKind::Str
                | TokenKind::MultilineStr
                | TokenKind::KwTrue
                | TokenKind::KwFalse) => lit = Some((i, k)),
                _ => {}
            }
        }
        let Some((i, k)) = lit else {
            return store.wild();
        };
        let known = s != TY_ERROR && s != NO_TY;
        let bare = self.fir.tys.unqual(s);
        let prim = (known && self.fir.tys.tag(bare) == TyTag::Prim)
            .then(|| PrimKind::from_u8(self.fir.tys.a(bare) as u8))
            .flatten();
        match k {
            TokenKind::Float => {
                self.bemit(
                    cx,
                    pat,
                    50,
                    50,
                    "a float literal is not a pattern".to_string(),
                );
                store.wild()
            }
            TokenKind::KwTrue | TokenKind::KwFalse => {
                let v = k == TokenKind::KwTrue;
                if known && prim != Some(PrimKind::Bool) {
                    let w = self.show(s);
                    self.bemit(
                        cx,
                        pat,
                        50,
                        50,
                        format!("a `bool` pattern does not check against `{w}`"),
                    );
                }
                cx.facts.patterns.shape(PatShape::Lit(ConstValue::B(v)));
                store.ctor(Ctor::Bool(v), &[])
            }
            TokenKind::Str | TokenKind::MultilineStr => {
                let txt = cx.f.tokens.text(i, cx.f.source);
                // The same symbol a `const` of this literal lowers to
                // (`lower::str_contents`), so the two are one constructor.
                let sym = self.names.intern(str_contents(k, txt));
                if known && prim != Some(PrimKind::Str) {
                    let w = self.show(s);
                    self.bemit(
                        cx,
                        pat,
                        50,
                        50,
                        format!("a string pattern does not check against `{w}`"),
                    );
                }
                cx.facts.patterns.shape(PatShape::Lit(ConstValue::S(sym)));
                store.ctor(Ctor::Str(sym), &[])
            }
            TokenKind::Int => {
                let txt = cx.f.tokens.text(i, cx.f.source);
                let Some(mut v) = parse_int_literal(txt) else {
                    return store.wild();
                };
                if neg {
                    v = -v;
                }
                match prim {
                    Some(p) if p.is_integer() => {
                        if !fits(ConstValue::I(v), p) {
                            let w = self.show(s);
                            self.bemit(cx, pat, 50, 50, format!("{v} does not fit `{w}`"));
                        }
                    }
                    _ if known => {
                        let w = self.show(s);
                        self.bemit(
                            cx,
                            pat,
                            50,
                            50,
                            format!("an integer pattern does not check against `{w}`"),
                        );
                    }
                    _ => {}
                }
                cx.facts.patterns.shape(PatShape::Lit(ConstValue::I(v)));
                store.ctor(Ctor::Int(v), &[])
            }
            _ => unreachable!(),
        }
    }

    fn check_pat_tuple(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
    ) -> PatId {
        let kids = cx.kids(pat);
        let known = s != TY_ERROR && s != NO_TY;
        let bare = self.fir.tys.unqual(s);
        let comps: Option<Vec<TyId>> = (known && self.fir.tys.tag(bare) == TyTag::Tuple)
            .then(|| self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec());
        let n = kids.len();
        // The stored arity is `S`'s own (what `exhaust.rs`'s `ctor_sub_tys`
        // will later recompute from the same type), never the written
        // pattern's — a parse-error's extra/missing element must not
        // desync the two (design §7.10: still visited, for its own
        // diagnostics/bindings, just outside the matrix's column).
        let arity = comps.as_ref().map(Vec::len).unwrap_or(0);
        let ok = matches!(&comps, Some(c) if c.len() == n);
        if known && !ok {
            let w = self.show(s);
            self.bemit(
                cx,
                pat,
                50,
                50,
                format!("a {n}-tuple pattern does not check against `{w}`"),
            );
        }
        let mut subs = Vec::with_capacity(arity);
        for i in 0..arity {
            let t = comps
                .as_ref()
                .and_then(|v| v.get(i))
                .copied()
                .unwrap_or(TY_ERROR);
            let id = match kids.get(i) {
                Some(&c) => self.check_pat(cx, store, c, t),
                None => {
                    // D5: a component with no written pattern still gets a
                    // child row, so the fact tree's children line up with
                    // the type's components one for one.
                    cx.facts.patterns.leaf(pat as u32, t, PatShape::Wild);
                    store.wild()
                }
            };
            cx.facts.patterns.slot_last(i as u32);
            subs.push(id);
        }
        for &c in kids.iter().skip(arity) {
            self.check_pat(cx, store, c, TY_ERROR);
        }
        cx.facts
            .patterns
            .shape(PatShape::Tuple { len: arity as u32 });
        store.ctor(Ctor::Tuple(arity as u32), &subs)
    }

    /// `PatDot`/`PatPath`, with or without a payload: R50's variant/`const`
    /// paragraph. Ch08 Rule 25 already resolved a single bare segment with
    /// no payload (or reported ITS OWN diagnostic and deferred, in which
    /// case this stays silent); a dot-literal's variant name is deferred to
    /// here (Rule 22) because it needs `s`.
    fn check_pat_path(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
    ) -> PatId {
        let payload = cx
            .kids(pat)
            .into_iter()
            .find(|&c| cx.kind(c) == NodeKind::Payload);
        match cx.f.uses.target_of(pat as u32) {
            Some(ResolvedTarget::Entity(Entity::Variant { file, decl, index })) => {
                let def = self.defs.def_of(file, decl);
                self.check_pat_variant(cx, store, pat, payload, s, def, index)
            }
            Some(ResolvedTarget::Deferred {
                reason: DeferReason::Member,
            }) => {
                let Some(name) = last_ident_sym(self, cx, pat) else {
                    return store.wild();
                };
                self.check_pat_dot(cx, store, pat, payload, s, name)
            }
            Some(ResolvedTarget::Entity(Entity::Item { file, decl })) => {
                let def = self.defs.def_of(file, decl);
                if def == fors_fir::NO_DEF {
                    return store.wild();
                }
                self.dep(def);
                match self.fir.sigs.kind(def) {
                    SigKind::Struct => self.check_pat_struct(cx, store, pat, payload, s, def),
                    SigKind::Const => self.check_pat_const(cx, store, pat, s, def),
                    other => {
                        let what = sig_kind_name(other);
                        self.bemit(
                            cx,
                            pat,
                            50,
                            50,
                            format!(
                                "a bare pattern name that resolves to {what} is not a pattern; to bind, write `let n`"
                            ),
                        );
                        store.wild()
                    }
                }
            }
            Some(ResolvedTarget::Entity(Entity::PreludeType(_))) => {
                self.bemit(
                    cx,
                    pat,
                    50,
                    50,
                    "a bare pattern name that resolves to a prelude type is not a pattern; to bind, write `let n`".to_string(),
                );
                store.wild()
            }
            // `some`/`none` are ch08 Rule 17 prelude VALUES (round 5's
            // `PRELUDE_VALUES`), not `Entity::Item`/`Entity::Variant`, so
            // they need their own branch: `Option`'s two variants (R34's
            // "a `path`/`dot_lit` with a payload MUST name a variant").
            Some(ResolvedTarget::Entity(Entity::PreludeValue(sym)))
                if matches!(self.names.resolve(sym), b"some" | b"none") =>
            {
                self.check_pat_option(cx, store, pat, payload, s, sym)
            }
            Some(ResolvedTarget::Entity(Entity::PreludeValue(_))) => {
                self.bemit(
                    cx,
                    pat,
                    50,
                    50,
                    "a bare pattern name that resolves to a prelude value is not a pattern; to bind, write `let n`".to_string(),
                );
                store.wild()
            }
            // A module, `Poisoned`, a local/parameter, or a segment ch08
            // already diagnosed and deferred: silence (design §7.10).
            _ => store.wild(),
        }
    }

    fn check_pat_const(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        s: TyId,
        def: DefId,
    ) -> PatId {
        self.dep(def);
        let ct = self.fir.sigs.const_ty(def);
        let v = self.fir.sigs.const_val(def);
        if v == fors_fir::NO_CONST {
            return store.wild();
        }
        let val = self.fir.tys.const_value(v);
        // Against the scrutinee's BARE type: an `imm i32` scrutinee still
        // matches an `i32` constant (ch01's qualifiers are not R50's).
        if s != TY_ERROR && s != NO_TY && ct != self.fir.tys.unqual(s) {
            let w = self.show(s);
            self.bemit(
                cx,
                pat,
                50,
                50,
                format!("this constant's type does not check against `{w}`"),
            );
        }
        cx.facts.patterns.shape(PatShape::Lit(val));
        match val {
            ConstValue::I(n) => store.ctor(Ctor::Int(n), &[]),
            ConstValue::B(b) => store.ctor(Ctor::Bool(b), &[]),
            ConstValue::S(sy) => store.ctor(Ctor::Str(sy), &[]),
        }
    }

    fn check_pat_variant(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        payload: Option<usize>,
        s: TyId,
        def: DefId,
        index: u32,
    ) -> PatId {
        if def == fors_fir::NO_DEF {
            return store.wild();
        }
        self.dep(def);
        self.check_scrutinee_head(cx, pat, s, def);
        let args = self.scrutinee_args(s, def);
        let Some(m) = self.nth_variant(def, index) else {
            return store.wild();
        };
        let subs = self.check_payload(cx, store, pat, payload, def, args, &m);
        cx.facts
            .patterns
            .shape(PatShape::Variant { en: def, index });
        store.ctor(Ctor::Variant(def, index), &subs)
    }

    /// `.name(...)`/`.name{...}`/`.name`: ch08 Rule 22 defers this to the
    /// checker because it needs `s` to know which enum's variants are in
    /// play.
    fn check_pat_dot(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        payload: Option<usize>,
        s: TyId,
        name: Symbol,
    ) -> PatId {
        let known = s != TY_ERROR && s != NO_TY;
        let bare = self.fir.tys.unqual(s);
        if !known || self.fir.tys.tag(bare) != TyTag::Nominal {
            if known {
                let w = self.show(s);
                self.bemit(
                    cx,
                    pat,
                    50,
                    50,
                    format!("a `.variant` pattern needs an enum type here; the scrutinee is `{w}`"),
                );
            }
            return store.wild();
        }
        let def = DefId(self.fir.tys.a(bare));
        self.dep(def);
        if self.fir.sigs.kind(def) != SigKind::Enum {
            let w = self.show(s);
            self.bemit(
                cx,
                pat,
                50,
                50,
                format!("a `.variant` pattern needs an enum type here; the scrutinee is `{w}`"),
            );
            return store.wild();
        }
        let args = ArgsId(self.fir.tys.b(bare));
        let Some((index, m)) = self.find_variant(def, name) else {
            let v = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
            let h = self.head_name(def);
            self.bemit(cx, pat, 50, 50, format!("`{h}` has no variant `{v}`"));
            return store.wild();
        };
        let subs = self.check_payload(cx, store, pat, payload, def, args, &m);
        cx.facts
            .patterns
            .shape(PatShape::Variant { en: def, index });
        store.ctor(Ctor::Variant(def, index), &subs)
    }

    /// `some`/`none`: `Option`'s own variants, resolved by name since ch08
    /// gives this one no `Entity::Variant` (it is a prelude value, not an
    /// enum-member path — call.rs's `classify_head` resolves a CALL the
    /// same way, for the same reason).
    fn check_pat_option(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        payload: Option<usize>,
        s: TyId,
        sym: Symbol,
    ) -> PatId {
        let def = self.prelude.option;
        if def == fors_fir::NO_DEF {
            return store.wild();
        }
        self.dep(def);
        self.check_scrutinee_head(cx, pat, s, def);
        let args = self.scrutinee_args(s, def);
        let Some((index, m)) = self.find_variant(def, sym) else {
            return store.wild();
        };
        let subs = self.check_payload(cx, store, pat, payload, def, args, &m);
        cx.facts
            .patterns
            .shape(PatShape::Variant { en: def, index });
        store.ctor(Ctor::Variant(def, index), &subs)
    }

    /// `def`'s variants by name, with the ordinal `Entity::Variant` and
    /// `exhaust.rs`'s signature both use (declaration order among variant
    /// members only).
    fn find_variant(&mut self, def: DefId, name: Symbol) -> Option<(u32, Member)> {
        let ms = self.fir.sigs.members(def);
        (0..self.fir.sigs.member_store.count(ms))
            .filter_map(|i| {
                let m = self.fir.sigs.member_store.get(ms, i);
                (m.kind == MemberKind::Variant).then_some(m)
            })
            .enumerate()
            .map(|(i, m)| (i as u32, m))
            .find(|(_, m)| m.name == name)
    }

    /// `def`'s Nth variant member (R53's ordinal, [`Entity::Variant`]'s
    /// "the variant's ordinal among that enum's distinct variant names").
    /// Shared with `exhaust.rs`'s signature and witness rendering.
    pub(crate) fn nth_variant(&mut self, def: DefId, index: u32) -> Option<Member> {
        let ms = self.fir.sigs.members(def);
        (0..self.fir.sigs.member_store.count(ms))
            .filter_map(|i| {
                let m = self.fir.sigs.member_store.get(ms, i);
                (m.kind == MemberKind::Variant).then_some(m)
            })
            .nth(index as usize)
    }

    fn check_pat_struct(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        payload: Option<usize>,
        s: TyId,
        def: DefId,
    ) -> PatId {
        self.check_scrutinee_head(cx, pat, s, def);
        let args = self.scrutinee_args(s, def);
        let fields = self.struct_fields(def, args);
        let subs = match payload {
            Some(p) => self.check_field_payload(cx, store, p, &fields, Some(def)),
            None => fields.iter().map(|_| store.wild()).collect(),
        };
        cx.facts.patterns.shape(PatShape::Struct { def });
        store.ctor(Ctor::Struct(def), &subs)
    }

    /// A `( )` tuple payload or a `{ }` field payload, for either a
    /// variant's own shape (`m`) or (via [`Self::check_pat_struct`]) a
    /// plain struct.
    fn check_payload(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        pat: usize,
        payload: Option<usize>,
        def: DefId,
        args: ArgsId,
        m: &Member,
    ) -> Vec<PatId> {
        match m.payload {
            PayloadKind::None => {
                if payload.is_some() {
                    let n = self.sym(m.name);
                    self.bemit(cx, pat, 50, 50, format!("variant `{n}` has no payload"));
                }
                Vec::new()
            }
            PayloadKind::Tuple => {
                let tys: Vec<TyId> = self
                    .fir
                    .tys
                    .args(m.args)
                    .to_vec()
                    .into_iter()
                    .map(|t| self.substituted(def, args, t))
                    .collect();
                match payload {
                    Some(p) => {
                        let kids = cx.kids(p);
                        if kids.len() != tys.len() {
                            let n = self.sym(m.name);
                            self.bemit(
                                cx,
                                pat,
                                50,
                                50,
                                format!(
                                    "variant `{n}` takes {} component(s), {} written",
                                    tys.len(),
                                    kids.len()
                                ),
                            );
                        }
                        // The stored arity is the VARIANT's own (what
                        // `exhaust.rs` recomputes from the signature),
                        // never the written payload's: a parse error's
                        // extra/missing component must not desync the two.
                        let subs: Vec<PatId> = tys
                            .iter()
                            .enumerate()
                            .map(|(i, &t)| {
                                let id = match kids.get(i) {
                                    Some(&c) => self.check_pat(cx, store, c, t),
                                    None => {
                                        cx.facts.patterns.leaf(pat as u32, t, PatShape::Wild);
                                        store.wild()
                                    }
                                };
                                cx.facts.patterns.slot_last(i as u32);
                                id
                            })
                            .collect();
                        for &c in kids.iter().skip(tys.len()) {
                            self.check_pat(cx, store, c, TY_ERROR);
                        }
                        subs
                    }
                    None => {
                        let n = self.sym(m.name);
                        self.bemit(cx, pat, 50, 50, format!("variant `{n}` needs a payload"));
                        tys.iter().map(|_| store.wild()).collect()
                    }
                }
            }
            PayloadKind::Record => {
                let fields: Vec<(Symbol, TyId)> = (0..self.fir.sigs.member_store.count(m.sub))
                    .map(|i| {
                        let f = self.fir.sigs.member_store.get(m.sub, i);
                        (f.name, self.substituted(def, args, f.ty))
                    })
                    .collect();
                match payload {
                    // A variant's record fields carry no `pub` of their
                    // own (ch08 N0011 rejects one): they are as visible
                    // as the variant, so no head to check them against.
                    Some(p) => self.check_field_payload(cx, store, p, &fields, None),
                    None => fields.iter().map(|_| store.wild()).collect(),
                }
            }
        }
    }

    /// A `{ }` payload's `FPat` children against `fields` (declaration
    /// order), omitted fields matching anything (R50: "a `{ }` payload
    /// names VISIBLE fields AT MOST ONCE each" — a name that is no field
    /// and a field named twice are both T0050; a struct field without
    /// `pub` used from another module is ch08 R11's N0011, exactly as
    /// `member::member_of` reports it for `p.x`, when `head` names the
    /// struct the fields belong to).
    fn check_field_payload(
        &mut self,
        cx: &mut BodyCx,
        store: &mut PatStore,
        payload: usize,
        fields: &[(Symbol, TyId)],
        head: Option<DefId>,
    ) -> Vec<PatId> {
        let mut subs: Vec<Option<PatId>> = vec![None; fields.len()];
        for c in cx.kids(payload) {
            if cx.kind(c) != NodeKind::FPat {
                continue;
            }
            let Some(fname) = last_ident_sym(self, cx, c) else {
                continue;
            };
            let slot = fields.iter().position(|&(n, _)| n == fname);
            let f = self.sym(fname);
            match slot {
                None => {
                    self.bemit(
                        cx,
                        c,
                        50,
                        50,
                        format!("there is no field `{f}` to match here"),
                    );
                }
                Some(k) if subs[k].is_some() => {
                    self.bemit(
                        cx,
                        c,
                        50,
                        50,
                        format!("the field `{f}` is named twice in this pattern"),
                    );
                }
                Some(_) => {
                    if let Some(def) = head
                        && self.field_vis(def, fname) == Some(VIS_PRIVATE)
                        && !self.same_module(def, cx.owner)
                    {
                        let h = self.head_name(def);
                        self.bemit_code(
                            cx,
                            c,
                            Code::N(11),
                            49,
                            format!("the field `{f}` of `{h}` is not `pub`"),
                        );
                    }
                }
            }
            let ty = slot.map(|k| fields[k].1).unwrap_or(TY_ERROR);
            let inner = cx.kids(c);
            let bound = if let Some(&first) = inner.first() {
                self.check_pat(cx, store, first, ty)
            } else {
                // `{ x }` shorthand binds the field name directly: counts
                // as one pattern node, like a written `let x` would.
                store.touch();
                cx.bind(c as u32, ty, LocalKind::Value);
                let shape = self.bind_shape(ty);
                cx.facts.patterns.leaf(c as u32, ty, shape);
                store.wild()
            };
            // D5: the field index this child matches. An omitted field has
            // no child at all (R50's "omitted fields match anything").
            cx.facts
                .patterns
                .slot_last(slot.map(|k| k as u32).unwrap_or(crate::facts::NO_PAT_SLOT));
            if let Some(k) = slot
                && subs[k].is_none()
            {
                subs[k] = Some(bound);
            }
        }
        // ch01 R22d(ii): an OMITTED `{ }` field matches anything, so a
        // linear one is dropped by this pattern.
        for (k, &(name, ty)) in fields.iter().enumerate() {
            if subs[k].is_some() || ty == TY_ERROR || ty == NO_TY {
                continue;
            }
            if !self.is_linear(ty) {
                continue;
            }
            let f = self.sym(name);
            let w = self.show(ty);
            self.bemit_code(
                cx,
                payload,
                Code::O(22),
                50,
                format!(
                    "the field `{f}` of linear type `{w}` is omitted from this pattern, and an                      omitted field matches anything: bind it with `let n` and consume it (ch01                      R22d(ii))"
                ),
            );
            break;
        }
        cx.facts.patterns.sort_children();
        subs.into_iter()
            .map(|o| o.unwrap_or_else(|| store.wild()))
            .collect()
    }

    /// Diagnoses `s` not being (a substitution of) `def`'s own nominal
    /// head, which every variant/struct payload branch needs once.
    fn check_scrutinee_head(&mut self, cx: &mut BodyCx, pat: usize, s: TyId, def: DefId) {
        if s == TY_ERROR || s == NO_TY {
            return;
        }
        let bare = self.fir.tys.unqual(s);
        let matches =
            self.fir.tys.tag(bare) == TyTag::Nominal && DefId(self.fir.tys.a(bare)) == def;
        if !matches {
            let w = self.show(s);
            self.bemit(
                cx,
                pat,
                50,
                50,
                format!("this pattern does not check against `{w}`"),
            );
        }
    }

    /// The declared visibility of `def`'s own field `name` (`None` when
    /// `def` has no such field).
    fn field_vis(&mut self, def: DefId, name: Symbol) -> Option<u8> {
        let ms = self.fir.sigs.members(def);
        (0..self.fir.sigs.member_store.count(ms))
            .map(|i| self.fir.sigs.member_store.get(ms, i))
            .find(|m| m.kind == MemberKind::Field && m.name == name)
            .map(|m| m.vis)
    }

    pub(crate) fn scrutinee_args(&mut self, s: TyId, def: DefId) -> ArgsId {
        let bare = self.fir.tys.unqual(s);
        if self.fir.tys.tag(bare) == TyTag::Nominal && DefId(self.fir.tys.a(bare)) == def {
            ArgsId(self.fir.tys.b(bare))
        } else {
            NO_ARGS
        }
    }

    /// `def`'s own fields (not a variant's), declaration order, substituted
    /// by `args`. Shared with `exhaust.rs`'s signature of a struct type.
    pub(crate) fn struct_fields(&mut self, def: DefId, args: ArgsId) -> Vec<(Symbol, TyId)> {
        let ms = self.fir.sigs.members(def);
        (0..self.fir.sigs.member_store.count(ms))
            .filter_map(|i| {
                let m = self.fir.sigs.member_store.get(ms, i);
                (m.kind == MemberKind::Field).then(|| (m.name, self.substituted(def, args, m.ty)))
            })
            .collect()
    }

    /// One variant's own component types (tuple or record payload shape),
    /// declaration order, substituted by `args`. Shared with `exhaust.rs`.
    pub(crate) fn variant_component_types(
        &mut self,
        def: DefId,
        args: ArgsId,
        m: &Member,
    ) -> Vec<TyId> {
        match m.payload {
            PayloadKind::None => Vec::new(),
            PayloadKind::Tuple => self
                .fir
                .tys
                .args(m.args)
                .to_vec()
                .into_iter()
                .map(|t| self.substituted(def, args, t))
                .collect(),
            PayloadKind::Record => (0..self.fir.sigs.member_store.count(m.sub))
                .map(|i| {
                    let f = self.fir.sigs.member_store.get(m.sub, i);
                    self.substituted(def, args, f.ty)
                })
                .collect(),
        }
    }
}

fn sig_kind_name(k: SigKind) -> &'static str {
    match k {
        SigKind::Fn | SigKind::ExternFn => "a fn",
        SigKind::Struct => "a struct",
        SigKind::Enum => "an enum",
        SigKind::Trait => "a trait",
        SigKind::Impl => "an impl",
        SigKind::Const => "a const",
        SigKind::Poisoned | SigKind::Absent => "an unresolved item",
    }
}

/// The last identifier of a path node's OWN tokens (excluding a `Payload`
/// child's): a `PatDot`'s variant name, or an `FPat`'s field name.
fn last_ident_sym(wf: &mut Wf<'_>, cx: &BodyCx, node: usize) -> Option<Symbol> {
    let (a, b) = fors_resolve::paths::own_span(cx.f.tree, node);
    let i = (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .rfind(|&i| cx.f.tokens.kinds[i] == TokenKind::Ident)?;
    Some(wf.names.intern(cx.f.tokens.text(i, cx.f.source)))
}
