//! Exhaustiveness and usefulness (design §7.8; ch09 R53-R55): the plain
//! usefulness algorithm over a [`crate::pat::PatStore`] matrix, charged in
//! matrix rows so the decision and the diagnostic's budget are the same
//! number (R55: "an implementation MAY compute the answer faster but MUST
//! report T0055 exactly when the plain count ... exceeds the budget" — this
//! module IS the plain algorithm, so the two can never drift apart).
//!
//! For each arm (one usefulness query per arm, then the all-wildcard row):
//! specialise the matrix's first column by each constructor occurring in
//! it, forming the default matrix instead when those are not a complete
//! signature of the column's type; charge one step per row of every
//! matrix so formed; no memoisation, no early exit other than an empty
//! matrix or an exhausted column list (budget exhaustion is a separate,
//! sanctioned abort — see [`Budget`]).

use fors_fir::{
    ArgsId, MemberKind, NO_ARGS, NO_TY, PayloadKind, PrimKind, SigKind, TY_ERROR, TyId, TyTag,
};
use fors_index::Symbol;
use fors_index::ids::DefId;

use crate::body::BodyCx;
use crate::pat::{Ctor, PatId, PatStore};
use crate::wf::Wf;

/// R55: the step budget is this many times the match's own pattern-node
/// count.
pub const MATCH_STEP_FACTOR: u64 = 256;

/// R55's running cost: one charge per matrix formed, aborting the whole
/// computation (not just one branch) the instant it crosses `limit` — the
/// only exit besides an empty matrix or an exhausted column list, and the
/// reason `check_match`'s own `exhaust_steps` counter and this budget's
/// `steps` are always the same number at the point it stops.
struct Budget {
    steps: u64,
    limit: u64,
}

impl Budget {
    fn new(limit: u64) -> Self {
        Budget { steps: 0, limit }
    }

    /// Charges `n` steps; `false` once the running total has crossed the
    /// limit (the caller then aborts immediately, via `?`).
    fn charge(&mut self, n: u64) -> bool {
        self.steps += n;
        self.steps <= self.limit
    }
}

/// A value the arm list does not cover (R53's witness), rendered to text
/// by [`Wf::render_witness`].
#[derive(Clone)]
enum Witness {
    Wild,
    Ctor(Ctor, Vec<Witness>),
}

/// The complete constructor set of a column's type, with each
/// constructor's own sub-column types — or `Infinite` for an integer or
/// `Str` column (R53: "integer and string columns are never complete") or
/// anything this increment does not recognise (conservatively never
/// complete either, so a wildcard is always demanded there too).
enum Sig {
    Finite(Vec<(Ctor, Vec<TyId>)>),
    Infinite,
}

impl Wf<'_> {
    /// R53/R54/R55 for one `match`: `arms` is `(pattern node, lowered
    /// PatId)` in source order; `store` is that match's own `PatStore`
    /// (R55's pattern-node count is `store.pattern_node_count()`); `s` is
    /// the scrutinee's type. Silent when `s` itself failed to type (error recovery, design
    /// §7.10) or the match has no arms (a parse error already spoke).
    pub fn check_match(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        arms: &[(usize, PatId)],
        store: &PatStore,
        s: TyId,
    ) {
        if s == TY_ERROR || s == NO_TY || arms.is_empty() {
            return;
        }
        let limit = MATCH_STEP_FACTOR.saturating_mul(store.pattern_node_count() as u64);
        let mut budget = Budget::new(limit);
        let mut unreachable: Vec<usize> = Vec::new();
        let mut exceeded = false;
        // R54: each arm against every arm before it, in source order.
        for i in 0..arms.len() {
            let rows: Vec<Vec<PatId>> = arms[..i].iter().map(|&(_, p)| vec![p]).collect();
            let v = [arms[i].1];
            match self.usefulness(store, &[s], &rows, &v, &mut budget) {
                None => {
                    exceeded = true;
                    break;
                }
                Some(None) => unreachable.push(arms[i].0),
                Some(Some(_)) => {}
            }
        }
        // R53: the all-wildcard row against every arm, last.
        let missing = if exceeded {
            None
        } else {
            let rows: Vec<Vec<PatId>> = arms.iter().map(|&(_, p)| vec![p]).collect();
            let v = [store.wild()];
            match self.usefulness(store, &[s], &rows, &v, &mut budget) {
                None => {
                    exceeded = true;
                    None
                }
                Some(w) => w,
            }
        };
        self.exhaust_steps += budget.steps;
        if exceeded {
            self.step_budget(cx, node, budget.steps, limit);
            return;
        }
        for pat_node in unreachable {
            self.bemit(
                cx,
                pat_node,
                54,
                54,
                "this arm is not useful: every value it matches is already covered by an earlier arm".to_string(),
            );
        }
        if let Some(w) = missing {
            let text = self.render_witness(&w[0]);
            self.bemit(
                cx,
                node,
                53,
                53,
                format!("the match is not exhaustive; for example, `{text}` is not covered"),
            );
        }
    }

    /// R55's own diagnostic site, split out of [`Self::check_match`] so
    /// `rules.rs`'s `exhaust::step_budget` emission site names a real
    /// function.
    fn step_budget(&mut self, cx: &mut BodyCx, node: usize, steps: u64, limit: u64) {
        self.bemit(
            cx,
            node,
            55,
            55,
            format!(
                "exhaustiveness checking exceeded {steps} steps ({MATCH_STEP_FACTOR} x the match's pattern-node count is {limit}); nest the match"
            ),
        );
    }

    /// The plain usefulness algorithm (design §7.8), `U(rows, v)` with a
    /// witness: `None` once `budget` is exhausted (abort); `Some(None)`
    /// when `v` is not useful; `Some(Some(w))` when it is, `w` one witness
    /// value per remaining column of `v`.
    fn usefulness(
        &mut self,
        store: &PatStore,
        col_tys: &[TyId],
        rows: &[Vec<PatId>],
        v: &[PatId],
        budget: &mut Budget,
    ) -> Option<Option<Vec<Witness>>> {
        if !budget.charge(rows.len() as u64) {
            return None;
        }
        if v.is_empty() {
            return Some(if rows.is_empty() {
                Some(Vec::new())
            } else {
                None
            });
        }
        match store.ctor_of(v[0]) {
            Some(c) => {
                let sub_tys = self.ctor_sub_tys(col_tys[0], c);
                let arity = sub_tys.len();
                let spec_rows = specialize(store, rows, c, arity);
                let mut sub_v = store.subs(v[0]).to_vec();
                sub_v.extend_from_slice(&v[1..]);
                let mut new_cols = sub_tys;
                new_cols.extend_from_slice(&col_tys[1..]);
                let r = self.usefulness(store, &new_cols, &spec_rows, &sub_v, budget)?;
                Some(r.map(|w| combine_witness(c, arity, w)))
            }
            None => match self.signature_of(col_tys[0]) {
                Sig::Finite(ctors) => {
                    let missing_idx = ctors
                        .iter()
                        .position(|(c, _)| !rows.iter().any(|r| store.ctor_of(r[0]) == Some(*c)));
                    let Some(missing_idx) = missing_idx else {
                        // Complete signature: try EVERY constructor, never
                        // stopping early once one is found useful (R55's
                        // step count must not depend on which arm order
                        // finds the gap first).
                        let mut witness: Option<Vec<Witness>> = None;
                        for (c, sub_tys) in &ctors {
                            let arity = sub_tys.len();
                            let spec_rows = specialize(store, rows, *c, arity);
                            let wild = store.wild();
                            let mut sub_v = vec![wild; arity];
                            sub_v.extend_from_slice(&v[1..]);
                            let mut new_cols = sub_tys.clone();
                            new_cols.extend_from_slice(&col_tys[1..]);
                            let r =
                                self.usefulness(store, &new_cols, &spec_rows, &sub_v, budget)?;
                            if witness.is_none()
                                && let Some(w) = r
                            {
                                witness = Some(combine_witness(*c, arity, w));
                            }
                        }
                        return Some(witness);
                    };
                    let def_rows = default_rows(store, rows);
                    let r = self.usefulness(store, &col_tys[1..], &def_rows, &v[1..], budget)?;
                    let (mc, msub) = ctors[missing_idx].clone();
                    Some(r.map(|rest| {
                        let mut out = vec![Witness::Ctor(mc, vec![Witness::Wild; msub.len()])];
                        out.extend(rest);
                        out
                    }))
                }
                Sig::Infinite => {
                    let def_rows = default_rows(store, rows);
                    let r = self.usefulness(store, &col_tys[1..], &def_rows, &v[1..], budget)?;
                    let w0 = self.missing_literal(col_tys[0], store, rows);
                    Some(r.map(|rest| {
                        let mut out = vec![w0];
                        out.extend(rest);
                        out
                    }))
                }
            },
        }
    }

    /// One already-written constructor's own sub-column types, from the
    /// column's type (not the full signature — `ctor_of` already named the
    /// constructor, so there is exactly one shape to look up).
    fn ctor_sub_tys(&mut self, ty: TyId, c: Ctor) -> Vec<TyId> {
        match c {
            Ctor::Bool(_) | Ctor::Int(_) | Ctor::Str(_) => Vec::new(),
            Ctor::Tuple(_) => {
                let bare = self.fir.tys.unqual(ty);
                if self.fir.tys.tag(bare) == TyTag::Tuple {
                    self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec()
                } else {
                    Vec::new()
                }
            }
            Ctor::Struct(def) => {
                let args = self.scrutinee_args(ty, def);
                self.struct_fields(def, args)
                    .into_iter()
                    .map(|(_, t)| t)
                    .collect()
            }
            Ctor::Variant(def, idx) => {
                let args = self.scrutinee_args(ty, def);
                match self.nth_variant(def, idx) {
                    Some(m) => self.variant_component_types(def, args, &m),
                    None => Vec::new(),
                }
            }
        }
    }

    /// The complete constructor set of `ty`'s own shape (R53's "an enum's
    /// variants ... `true`/`false`; the single constructor of a tuple or
    /// struct; integer and string literals, whose domains count as
    /// infinite").
    fn signature_of(&mut self, ty: TyId) -> Sig {
        if ty == TY_ERROR || ty == NO_TY {
            return Sig::Infinite;
        }
        let bare = self.fir.tys.unqual(ty);
        match self.fir.tys.tag(bare) {
            TyTag::Prim => match PrimKind::from_u8(self.fir.tys.a(bare) as u8) {
                Some(PrimKind::Bool) => Sig::Finite(vec![
                    (Ctor::Bool(false), Vec::new()),
                    (Ctor::Bool(true), Vec::new()),
                ]),
                _ => Sig::Infinite,
            },
            TyTag::Tuple => {
                let parts = self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec();
                let n = parts.len() as u32;
                Sig::Finite(vec![(Ctor::Tuple(n), parts)])
            }
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(bare));
                let args = ArgsId(self.fir.tys.b(bare));
                match self.fir.sigs.kind(def) {
                    SigKind::Struct => {
                        let fields: Vec<TyId> = self
                            .struct_fields(def, args)
                            .into_iter()
                            .map(|(_, t)| t)
                            .collect();
                        Sig::Finite(vec![(Ctor::Struct(def), fields)])
                    }
                    SigKind::Enum => {
                        let ms = self.fir.sigs.members(def);
                        let mut out = Vec::new();
                        let mut idx = 0u32;
                        for i in 0..self.fir.sigs.member_store.count(ms) {
                            let m = self.fir.sigs.member_store.get(ms, i);
                            if m.kind != MemberKind::Variant {
                                continue;
                            }
                            let subs = self.variant_component_types(def, args, &m);
                            out.push((Ctor::Variant(def, idx), subs));
                            idx += 1;
                        }
                        if out.is_empty() {
                            // No variant at all (ch07 requires one, so this
                            // is a parse-error declaration): never a
                            // complete signature, so a wildcard arm stays
                            // useful rather than drawing a T0054 on top of
                            // the parser's own diagnostic (design §7.10).
                            return Sig::Infinite;
                        }
                        Sig::Finite(out)
                    }
                    _ => Sig::Infinite,
                }
            }
            _ => Sig::Infinite,
        }
    }

    /// A concrete value of `ty` no row's column already uses (R53: "the
    /// diagnostic names one uncovered value"), bounded by `rows.len() + 1`
    /// candidates — enough by pigeonhole, since at most `rows.len()`
    /// distinct literals can occur.
    fn missing_literal(&mut self, ty: TyId, store: &PatStore, rows: &[Vec<PatId>]) -> Witness {
        let bare = self.fir.tys.unqual(ty);
        let is_str = ty != TY_ERROR
            && ty != NO_TY
            && self.fir.tys.tag(bare) == TyTag::Prim
            && PrimKind::from_u8(self.fir.tys.a(bare) as u8) == Some(PrimKind::Str);
        let bound = rows.len() as i128 + 1;
        if is_str {
            for n in 0..bound {
                let sym = self.names.intern(format!("other{n}").as_bytes());
                if !rows
                    .iter()
                    .any(|r| store.ctor_of(r[0]) == Some(Ctor::Str(sym)))
                {
                    return Witness::Ctor(Ctor::Str(sym), Vec::new());
                }
            }
        } else {
            for n in 0..bound {
                if !rows
                    .iter()
                    .any(|r| store.ctor_of(r[0]) == Some(Ctor::Int(n)))
                {
                    return Witness::Ctor(Ctor::Int(n), Vec::new());
                }
            }
        }
        Witness::Wild
    }

    fn render_witness(&mut self, w: &Witness) -> String {
        match w {
            Witness::Wild => "_".to_string(),
            Witness::Ctor(c, subs) => match *c {
                Ctor::Bool(b) => b.to_string(),
                Ctor::Int(n) => n.to_string(),
                Ctor::Str(s) => format!("\"{}\"", String::from_utf8_lossy(self.names.resolve(s))),
                Ctor::Tuple(_) => {
                    let parts: Vec<String> = subs.iter().map(|s| self.render_witness(s)).collect();
                    format!("({})", parts.join(", "))
                }
                // R53: "names one uncovered VALUE" — a struct's witness is
                // a struct value, field by field, not the type's name.
                Ctor::Struct(def) => {
                    let head = self.head_name(def);
                    let names: Vec<Symbol> = self
                        .struct_fields(def, NO_ARGS)
                        .into_iter()
                        .map(|(n, _)| n)
                        .collect();
                    self.render_fields(&head, &names, subs)
                }
                Ctor::Variant(def, idx) => {
                    let Some(m) = self.nth_variant(def, idx) else {
                        return String::new();
                    };
                    let name = self.sym(m.name);
                    match m.payload {
                        PayloadKind::None => name,
                        PayloadKind::Tuple => {
                            let parts: Vec<String> =
                                subs.iter().map(|s| self.render_witness(s)).collect();
                            format!("{name}({})", parts.join(", "))
                        }
                        PayloadKind::Record => {
                            let names: Vec<Symbol> = (0..self.fir.sigs.member_store.count(m.sub))
                                .map(|i| self.fir.sigs.member_store.get(m.sub, i).name)
                                .collect();
                            self.render_fields(&name, &names, subs)
                        }
                    }
                }
            },
        }
    }

    /// `Head { a: w, b: w }`, one entry per field in declaration order.
    fn render_fields(&mut self, head: &str, names: &[Symbol], subs: &[Witness]) -> String {
        let parts: Vec<String> = names
            .iter()
            .zip(subs)
            .map(|(&n, w)| {
                let f = self.sym(n);
                let v = self.render_witness(w);
                format!("{f}: {v}")
            })
            .collect();
        format!("{head} {{ {} }}", parts.join(", "))
    }
}

/// `S(c, rows)` (design §7.8): a wildcard-headed row expands into `arity`
/// copies of the store's one cached wildcard plus its own remaining
/// columns; a row headed by `c` itself contributes its own sub-patterns
/// plus its remaining columns; any other concrete head is dropped.
fn specialize(store: &PatStore, rows: &[Vec<PatId>], c: Ctor, arity: usize) -> Vec<Vec<PatId>> {
    let wild = store.wild();
    let mut out = Vec::with_capacity(rows.len());
    for r in rows {
        match store.ctor_of(r[0]) {
            None => {
                let mut nr = vec![wild; arity];
                nr.extend_from_slice(&r[1..]);
                out.push(nr);
            }
            Some(rc) if rc == c => {
                let mut nr = store.subs(r[0]).to_vec();
                nr.extend_from_slice(&r[1..]);
                out.push(nr);
            }
            _ => {}
        }
    }
    out
}

/// `D(rows)`: the wildcard-headed rows only, first column dropped.
fn default_rows(store: &PatStore, rows: &[Vec<PatId>]) -> Vec<Vec<PatId>> {
    rows.iter()
        .filter(|r| store.ctor_of(r[0]).is_none())
        .map(|r| r[1..].to_vec())
        .collect()
}

/// Reassembles one recursive step's witness: the first `arity` entries
/// become `c`'s own sub-witnesses, the rest stay the remaining columns'.
fn combine_witness(c: Ctor, arity: usize, mut w: Vec<Witness>) -> Vec<Witness> {
    let sub: Vec<Witness> = w.drain(0..arity).collect();
    let mut out = vec![Witness::Ctor(c, sub)];
    out.extend(w);
    out
}
