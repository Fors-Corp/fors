//! Whole-head well-formedness (design §4.2 `wf.rs`, §7.1 phase 4): the rules
//! that need every signature of the build, not one declaration.
//!
//! R14 (infinite size, one SCC pass), R17 (impl completeness), R18 (impl
//! parameters), R19 (overlap, per bucket), R21 (the two language-known
//! prerequisites and "an operator trait has no `Output`"), R23 (the
//! `Copyable` impl check), R24 (marker traits), R25 (dyn-capability), R48
//! (member clashes) and R11's linear-element clause.
//!
//! Every test here is DEFINITE-ONLY: a question the build cannot answer (a
//! head that did not resolve, a trait whose declaration is not in this build,
//! a type that lowered to `TY_ERROR`) is not an error, it is silence. A
//! whole-build pass that guesses would turn one unresolved name into a
//! diagnostic on every declaration that mentions it.

use std::collections::HashMap;

use fors_fir::defpath::{HeadKey, NO_DEF};
use fors_fir::impls::{self, ImplRow};
use fors_fir::prelude::{gty, tr, PreludeDefs};
use fors_fir::sig::{Conv, GParamKind, MemberKind, PayloadKind, SigKind, NO_TRAIT_REF};
use fors_fir::subst::{one_way_match, subst_norm, Binding};
use fors_fir::ty::{ArgsId, FnTyId, TraitRefId, TyId, TyTag, NO_ARGS, NO_TY, TY_ERROR};
use fors_fir::Fir;
use fors_index::decl::DeclKind;
use fors_index::ids::{DefId, FileId};
use fors_index::{Interner, Symbol};

use crate::defs::DefTable;
use crate::diag::{t, Sink};
use crate::lower::{FileCtx, Lowered};

/// Three-valued bound satisfaction: `Unknown` is the answer whenever the
/// build cannot decide, and no rule reports on it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Holds {
    Yes,
    No,
    Unknown,
}

pub struct Wf<'a> {
    pub fir: &'a mut Fir,
    pub names: &'a mut Interner,
    pub prelude: &'a PreludeDefs,
    pub defs: &'a DefTable,
    pub shapes: &'a crate::lower::Shapes,
    pub sink: &'a mut Sink,
    /// The build's impl index, moved out of lowering so `holds` can probe it
    /// while the type store is being written to.
    pub impls: fors_fir::impls::ImplIndex,
    /// The nominal heads an `impl Linear for T {}` declared linear (ch01 R22).
    linear_roots: Vec<DefId>,
    linear_memo: HashMap<TyId, bool>,
    /// Per `DefId`: has this declaration already produced a diagnostic? A
    /// body is typed only when its own signature — and its `impl`/`trait`
    /// head — came out clean (design §10: one root cause per declaration).
    pub spoke: Vec<bool>,
    // Deterministic counters (design §12). Every one of these is a count of
    // work, never of time: the near-linearity gate reads them, not a clock.
    pub synths: u64,
    pub checks: u64,
    pub body_nodes: u64,
    pub subst_calls: u64,
    pub holds_probes: u64,
    pub holds_misses: u64,
    pub impl_scans: u64,
    pub tape_events: u64,
    /// Bodies typed, and bodies skipped because their own declaration (or
    /// its `impl`/`trait` head) had already produced a diagnostic.
    pub bodies_checked: u64,
    pub bodies_skipped: u64,
    /// The distinct CHECK positions the bodies of this build used, compared
    /// against [`crate::body::CHECK_SITES`] by the ch03 R25 test.
    pub check_sites: Vec<crate::body::CheckSite>,
    /// The `Iterator` traits of this build, prelude row first. ch10 R2 lets
    /// package `std` DECLARE the prelude's names, so in a build that ships
    /// std the name `Iterator` resolves to std's own trait and the prelude
    /// row is never reached; R31's "a type that implements `Iterator`" must
    /// accept either. Computed once, on first use.
    iter_traits: Vec<DefId>,
    /// The declarations the body being typed has read so far, and the
    /// finished set for every body typed (design §9).
    pub cur_deps: crate::deps::DepSet,
    pub deps: Vec<(DefId, crate::deps::DepSet)>,
}

impl<'a> Wf<'a> {
    pub fn new(
        fir: &'a mut Fir,
        names: &'a mut Interner,
        prelude: &'a PreludeDefs,
        defs: &'a DefTable,
        shapes: &'a crate::lower::Shapes,
        sink: &'a mut Sink,
    ) -> Wf<'a> {
        Wf {
            fir,
            names,
            prelude,
            defs,
            shapes,
            sink,
            impls: fors_fir::impls::ImplIndex::new(),
            linear_roots: Vec::new(),
            linear_memo: HashMap::new(),
            spoke: Vec::new(),
            synths: 0,
            checks: 0,
            body_nodes: 0,
            subst_calls: 0,
            holds_probes: 0,
            holds_misses: 0,
            impl_scans: 0,
            tape_events: 0,
            bodies_checked: 0,
            bodies_skipped: 0,
            check_sites: Vec::new(),
            iter_traits: Vec::new(),
            cur_deps: crate::deps::DepSet::new(),
            deps: Vec::new(),
        }
    }

    /// Records that the body being typed read `def`'s signature (ch09 R2).
    pub fn dep(&mut self, def: DefId) {
        self.cur_deps.record(def);
    }

    /// R31's candidate `Iterator` traits (see [`Wf::iter_traits`]).
    pub fn iterator_traits(&mut self) -> Vec<DefId> {
        if !self.iter_traits.is_empty() {
            return self.iter_traits.clone();
        }
        let mut out = vec![self.prelude.traits[tr::ITERATOR]];
        let name = self.names.intern(b"Iterator");
        for (d, r) in self.defs.user_defs() {
            if r.kind == DeclKind::Trait && r.name == Some(name) {
                out.push(d);
            }
        }
        out.retain(|&d| d != fors_fir::NO_DEF);
        self.iter_traits = out.clone();
        out
    }

    /// Design §7.1 phase 5: every signature's canonical hash. Derived, so
    /// it is written after well-formedness and never read as an input.
    pub fn freeze(&mut self, defs: &DefTable) {
        let all: Vec<DefId> = defs.user_defs().map(|(d, _)| d).collect();
        let mut scratch = fors_fir::EncodeScratch::default();
        for d in all {
            let h = fors_fir::sig_hash_with(self.fir, self.names, d, &mut scratch);
            self.fir.sigs.set_sig_hash(d, h);
        }
    }

    /// Records that `def` has produced a diagnostic.
    pub fn spoke_at(&mut self, def: DefId) {
        if def == fors_fir::NO_DEF {
            return;
        }
        if self.spoke.len() <= def.index() {
            self.spoke.resize(def.index() + 1, false);
        }
        self.spoke[def.index()] = true;
    }

    pub fn run(&mut self, low: &Lowered, files: &[FileCtx]) {
        self.collect_linear(low);
        self.marker_traits(low, files);
        self.impl_params(low, files);
        self.overlap(low, files);
        self.impl_completeness(low, files);
        self.prerequisites(low, files);
        self.copyable_impl(low, files);
        self.dyn_capable(low, files);
        self.member_clashes(low, files);
        self.linear_elements(low, files);
        self.infinite_size(low, files);
    }

    // -------------------------------------------------------- linearity

    fn collect_linear(&mut self, _low: &Lowered) {
        let lin = self.prelude.traits[tr::LINEAR];
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in &rows {
            if r.trait_def == lin {
                if let HeadKey::Nominal(d) = r.head {
                    self.linear_roots.push(d);
                }
            }
        }
        self.linear_roots.sort_unstable_by_key(|d| d.0);
        self.linear_roots.dedup();
    }

    /// ch01 R22a: linearity propagates structurally from a declared root.
    pub fn is_linear(&mut self, ty: TyId) -> bool {
        if let Some(&v) = self.linear_memo.get(&ty) {
            return v;
        }
        self.linear_memo.insert(ty, false); // break cycles conservatively
        let v = self.is_linear_uncached(ty, 0);
        self.linear_memo.insert(ty, v);
        v
    }

    fn is_linear_uncached(&mut self, ty: TyId, depth: u32) -> bool {
        if depth > 64 || ty == TY_ERROR || ty == NO_TY {
            return false;
        }
        match self.fir.tys.tag(ty) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(ty));
                if self.linear_roots.binary_search_by_key(&def.0, |d| d.0).is_ok() {
                    return true;
                }
                // A built-in generic head stores its arguments by value only
                // for `Array`/`vector`/`atomic`/`Option`; `Own`/`Ref`/`Arena`
                // are ch01's and never linear by their argument.
                if let Some(g) = self.prelude.generic_index(def) {
                    return match g {
                        gty::ARRAY | gty::VECTOR | gty::ATOMIC | gty::OPTION => {
                            let args = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(ty)));
                            args.first().is_some_and(|&x| self.is_linear_uncached(x, depth + 1))
                        }
                        _ => false,
                    };
                }
                let ms = self.fir.sigs.members(def);
                let n = self.fir.sigs.member_store.count(ms);
                for i in 0..n {
                    let m = self.fir.sigs.member_store.get(ms, i);
                    match m.kind {
                        MemberKind::Field => {
                            if self.is_linear_uncached(m.ty, depth + 1) {
                                return true;
                            }
                        }
                        MemberKind::Variant => match m.payload {
                            PayloadKind::Tuple => {
                                let xs = self.fir.tys.args_vec(m.args);
                                if xs.iter().any(|&x| self.is_linear_uncached(x, depth + 1)) {
                                    return true;
                                }
                            }
                            PayloadKind::Record => {
                                let k = self.fir.sigs.member_store.count(m.sub);
                                for j in 0..k {
                                    let f = self.fir.sigs.member_store.get(m.sub, j);
                                    if self.is_linear_uncached(f.ty, depth + 1) {
                                        return true;
                                    }
                                }
                            }
                            PayloadKind::None => {}
                        },
                        MemberKind::Item => {}
                    }
                }
                false
            }
            TyTag::Tuple => {
                let xs = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(ty)));
                xs.iter().any(|&x| self.is_linear_uncached(x, depth + 1))
            }
            _ => false,
        }
    }

    // --------------------------------------------------- bound satisfaction

    /// R12, three-valued and definite-only. I2 answers the questions a
    /// SIGNATURE can ask: a concrete self type against the impl index (exact
    /// probe first, §17 amendment 3), a rigid parameter or a neutral
    /// projection against its declared bounds. Anything else is `Unknown`.
    pub fn holds(&mut self, subject: TyId, want: TraitRefId) -> Holds {
        self.holds_probes += 1;
        if subject == TY_ERROR || subject == NO_TY || want == NO_TRAIT_REF {
            return Holds::Unknown;
        }
        let (want_def, _) = self.fir.tys.trait_ref(want);
        let subject = self.fir.tys.unqual(subject);
        // `Droppable` is purely structural (R24): it holds exactly when the
        // subject is not linear.
        if want_def == self.prelude.traits[tr::DROPPABLE] {
            return match self.fir.tys.tag(subject) {
                TyTag::Param | TyTag::Proj => self.bound_list_holds(subject, want),
                TyTag::Error => Holds::Unknown,
                _ => {
                    if self.is_linear(subject) {
                        Holds::No
                    } else {
                        Holds::Yes
                    }
                }
            };
        }
        match self.fir.tys.tag(subject) {
            TyTag::Param | TyTag::Proj => self.bound_list_holds(subject, want),
            TyTag::Error | TyTag::Brand | TyTag::ConstVal => Holds::Unknown,
            _ => self.impl_holds(subject, want, want_def),
        }
    }

    fn bound_list_holds(&mut self, subject: TyId, want: TraitRefId) -> Holds {
        let bounds = self.declared_bounds(subject);
        if bounds.iter().any(|&b| b == want) {
            return Holds::Yes;
        }
        // A bound whose own declaration is not in this build cannot be
        // compared; stay silent rather than guess.
        if bounds.is_empty() {
            return Holds::No;
        }
        Holds::No
    }

    /// The bounds a rigid type carries: a `Param`'s declared bounds, a
    /// neutral projection's from the trait's `type A: ...` declaration.
    pub fn declared_bounds(&mut self, ty: TyId) -> Vec<TraitRefId> {
        match self.fir.tys.tag(ty) {
            TyTag::Param => {
                let owner = DefId(self.fir.tys.a(ty));
                let ord = self.fir.tys.b(ty) as usize;
                let g = self.fir.sigs.generics(owner);
                if ord >= self.fir.sigs.generics_store.count(g) {
                    return Vec::new();
                }
                let p = self.fir.sigs.generics_store.param(g, ord);
                self.fir.sigs.bounds.get(p.bounds).to_vec()
            }
            TyTag::Proj => {
                let (tref, name) = self.fir.tys.proj_key(fors_fir::ty::ProjKeyId(self.fir.tys.b(ty)));
                let (tdef, targs) = self.fir.tys.trait_ref(tref);
                let a = self.fir.sigs.assoc(tdef);
                let mut out = Vec::new();
                for i in 0..self.fir.sigs.assocs.count(a) {
                    let row = self.fir.sigs.assocs.get(a, i);
                    if row.name == name {
                        out = self.fir.sigs.bounds.get(row.bounds).to_vec();
                    }
                }
                // R62: the constraint entries in scope add bounds to this
                // neutral projection. They live on the declaration that owns
                // the projection's head.
                let head = TyId(self.fir.tys.a(ty));
                if self.fir.tys.tag(head) == TyTag::Param {
                    let owner = DefId(self.fir.tys.a(head));
                    let g = self.fir.sigs.generics(owner);
                    let cl = self.fir.sigs.generics_store.constraints(g);
                    for i in 0..self.fir.sigs.constraints.count(cl) {
                        let (subj, bl) = self.fir.sigs.constraints.entry(cl, i);
                        if subj == ty {
                            out.extend_from_slice(self.fir.sigs.bounds.get(bl));
                        }
                    }
                }
                let _ = targs;
                out.sort_unstable_by_key(|b| b.0);
                out.dedup();
                out
            }
            _ => Vec::new(),
        }
    }

    /// R12's impl lookup for a concrete subject, via the impl index.
    fn impl_holds(&mut self, subject: TyId, want: TraitRefId, want_def: DefId) -> Holds {
        let want_args = self.fir.tys.trait_ref(want).1;
        let exact: Vec<ImplRow> = self.impls.exact(want_def, subject).iter().map(|&r| self.impls.row(r)).collect();
        for row in &exact {
            if row.trait_args == want_args {
                return Holds::Yes;
            }
        }
        let head = self.fir.tys.head_key(subject);
        let bucket: Vec<ImplRow> = self.impls.bucket(want_def, head).iter().map(|&r| self.impls.row(r)).collect();
        for row in bucket {
            let arity = self.fir.sigs.generics_store.count(self.fir.sigs.generics(row.def));
            let mut b = Binding::new(&[(row.def, arity as u16)]);
            if one_way_match(&mut self.fir.tys, row.self_ty, subject, &mut b) {
                let ra = if row.trait_args == NO_ARGS { Vec::new() } else { self.fir.tys.args_vec(row.trait_args) };
                let wa = if want_args == NO_ARGS { Vec::new() } else { self.fir.tys.args_vec(want_args) };
                if ra.len() != wa.len() {
                    continue;
                }
                let mut ok = true;
                for (x, y) in ra.iter().zip(wa.iter()) {
                    if !one_way_match(&mut self.fir.tys, *x, *y, &mut b) {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    return Holds::Yes;
                }
            }
        }
        Holds::No
    }
}

// --------------------------------------------------------------- the rules

/// Whether a declaration already spent its diagnostic budget during
/// lowering. Rows created AFTER lowering (R22's built-in impls) are never
/// poisoned and are not in the vector at all.
fn poisoned(low: &Lowered, def: DefId) -> bool {
    low.poisoned.get(def.index()).copied().unwrap_or(false)
}

/// The operator traits of R21: homogeneous, so none of them has an `Output`.
fn is_operator_trait(p: &PreludeDefs, def: DefId) -> bool {
    const OPS: [usize; 13] = [
        tr::ADD,
        tr::SUB,
        tr::MUL,
        tr::DIV,
        tr::REM,
        tr::NEG,
        tr::BITAND,
        tr::BITOR,
        tr::BITXOR,
        tr::SHL,
        tr::SHR,
        tr::EQ,
        tr::ORD,
    ];
    OPS.iter().any(|&i| p.traits[i] == def)
}

fn is_marker_trait(p: &PreludeDefs, def: DefId) -> bool {
    [tr::SHARED, tr::COPYABLE, tr::LINEAR, tr::DROPPABLE].iter().any(|&i| p.traits[i] == def)
}

impl Wf<'_> {
    fn emit(&mut self, home: DefId, file: FileId, range: (u32, u32), code: u16, site: u16, msg: String) {
        self.sink.open();
        self.sink.emit(file, range, t(code), site, msg);
        self.spoke_at(home);
    }

    /// The byte range of one declaration's own header, for a diagnostic that
    /// belongs to the declaration rather than to a type inside it.
    fn head_range(&self, files: &[FileCtx], def: DefId) -> Option<(FileId, (u32, u32))> {
        let row = self.defs.get(def)?;
        let f = files.get(row.file.index())?;
        Some((row.file, f.header_range(row.node as usize)))
    }

    fn name_of(&self, def: DefId) -> String {
        self.defs
            .get(def)
            .and_then(|r| r.name)
            .map(|s| String::from_utf8_lossy(self.names.resolve(s)).into_owned())
            .unwrap_or_else(|| "this item".to_string())
    }

    fn sym(&self, s: Symbol) -> String {
        String::from_utf8_lossy(self.names.resolve(s)).into_owned()
    }

    // ----------------------------------------------------------- R24

    /// R24: `Droppable` has no impls at all; an `impl Linear` may not bound
    /// any of its parameters; a marker trait must not be used as `dyn` (that
    /// half is in `dyn_capable`).
    fn marker_traits(&mut self, low: &Lowered, files: &[FileCtx]) {
        let droppable = self.prelude.traits[tr::DROPPABLE];
        let linear = self.prelude.traits[tr::LINEAR];
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if poisoned(low, r.def) {
                continue;
            }
            let Some((file, range)) = self.head_range(files, r.def) else { continue };
            if r.trait_def == droppable {
                self.emit(
                    r.def,
                    file,
                    range,
                    24,
                    24,
                    "`Droppable` is structural: it has no impls (a type is droppable exactly when it is not linear)"
                        .to_string(),
                );
                continue;
            }
            if r.trait_def == linear {
                let g = self.fir.sigs.generics(r.def);
                let n = self.fir.sigs.generics_store.count(g);
                let bounded = (0..n).any(|o| {
                    let p = self.fir.sigs.generics_store.param(g, o);
                    !self.fir.sigs.bounds.get(p.bounds).is_empty()
                });
                if bounded {
                    self.emit(
                        r.def,
                        file,
                        range,
                        24,
                        24,
                        "an `impl Linear` must not bound any of its parameters: linearity is a fact of the constructor, never of an instantiation".to_string(),
                    );
                }
            }
        }
    }

    // ----------------------------------------------------------- R18

    fn impl_params(&mut self, low: &Lowered, files: &[FileCtx]) {
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if poisoned(low, r.def) || r.self_ty == TY_ERROR {
                continue;
            }
            let Some((file, range)) = self.head_range(files, r.def) else { continue };
            // The self type MUST NOT be a bare type parameter: blanket impls
            // do not exist.
            if self.fir.tys.tag(r.self_ty) == TyTag::Param {
                self.emit(r.def, file, range, 18, 18, "the self type of an impl must not be a bare type parameter: there are no blanket impls".to_string());
                continue;
            }
            // MARC: R18 says an impl without `for` must name "a struct or an
            // enum". Package `std` writes `impl Str { ... }` and `impl
            // Array[T, N] { ... }` — ch08 R21 explicitly permits it and ch10
            // R2 requires it, since a prelude type's inherent surface has
            // nowhere else to live. So the clause is enforced against the
            // shapes it is really aimed at — a `fn` type, a `dyn` type, a
            // tuple — and a prelude head is accepted. A bare type parameter
            // is the blanket-impl case just above, with its own message.
            if r.inherent && matches!(self.fir.tys.tag(r.self_ty), TyTag::Fn | TyTag::Dyn | TyTag::Tuple) {
                self.emit(r.def, file, range, 18, 18, "an inherent impl's type must be a struct or an enum".to_string());
                continue;
            }
            // The impl head MUST NOT contain a projection, at any depth.
            let mut head_tys = vec![r.self_ty];
            if r.trait_args != NO_ARGS {
                head_tys.extend(self.fir.tys.args_vec(r.trait_args));
            }
            if head_tys.iter().any(|&h| impls::contains_proj(&self.fir.tys, h)) {
                self.emit(r.def, file, range, 18, 18, "an impl head must not contain a projection".to_string());
                continue;
            }
            // Every parameter MUST occur in the head; a BOUNDED one must
            // moreover occur in the SELF type.
            let g = self.fir.sigs.generics(r.def);
            let n = self.fir.sigs.generics_store.count(g);
            for o in 0..n {
                let p = self.fir.sigs.generics_store.param(g, o);
                let want = match p.kind {
                    GParamKind::Brand => self.fir.tys.brand_ty(fors_fir::ty::BrandRow::Param { owner: r.def, ordinal: o as u16 }),
                    _ => self.fir.tys.param(r.def, o as u16),
                };
                let in_head = head_tys.iter().any(|&h| impls::mentions(&self.fir.tys, h, want, &mut (1 << 16)));
                if !in_head {
                    let nm = self.sym(p.name);
                    self.emit(r.def, file, range, 18, 18, format!("unconstrained impl parameter `{nm}`: it occurs in neither the self type nor the trait arguments"));
                    break;
                }
                let bounded = !self.fir.sigs.bounds.get(p.bounds).is_empty();
                if bounded && !impls::mentions(&self.fir.tys, r.self_ty, want, &mut (1 << 16)) {
                    let nm = self.sym(p.name);
                    self.emit(r.def, file, range, 18, 18, format!("bounded impl parameter `{nm}` does not occur in the self type"));
                    break;
                }
            }
        }
    }

    // ----------------------------------------------------------- R19

    fn overlap(&mut self, low: &Lowered, files: &[FileCtx]) {
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        let mut buckets: HashMap<(u32, u64), Vec<usize>> = HashMap::new();
        for (i, r) in rows.iter().enumerate() {
            if r.trait_def == NO_DEF || r.self_ty == TY_ERROR {
                continue;
            }
            buckets.entry((r.trait_def.0, r.head.as_u64())).or_default().push(i);
        }
        let mut keys: Vec<(u32, u64)> = buckets.keys().copied().collect();
        keys.sort_unstable();
        for k in keys {
            let ids = &buckets[&k];
            for a in 0..ids.len() {
                for b in a + 1..ids.len() {
                    let (x, y) = (rows[ids[a]], rows[ids[b]]);
                    if poisoned(low, x.def) || poisoned(low, y.def) {
                        continue;
                    }
                    if !impls::overlap(&self.fir.tys, &self.fir.sigs, &x, &y) {
                        continue;
                    }
                    // Reported at the LATER impl, naming the earlier.
                    let (early, late) = if x.order <= y.order { (x, y) } else { (y, x) };
                    let Some((file, range)) = self.head_range(files, late.def) else { continue };
                    let nm = self.name_of(early.trait_def);
                    self.emit(late.def, file, range, 19, 19, format!("this impl of `{nm}` overlaps an earlier one: their heads unify"));
                }
            }
        }
    }

    // ------------------------------------------------------ R17 and R21

    fn impl_completeness(&mut self, low: &Lowered, files: &[FileCtx]) {
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if poisoned(low, r.def) {
                continue;
            }
            let Some((file, range)) = self.head_range(files, r.def) else { continue };
            let assoc_defined: Vec<(Symbol, TyId)> = {
                let a = self.fir.sigs.assoc(r.def);
                (0..self.fir.sigs.assocs.count(a)).map(|i| {
                    let row = self.fir.sigs.assocs.get(a, i);
                    (row.name, row.rhs)
                }).collect()
            };
            if r.inherent {
                // An inherent impl MUST NOT contain a `type` item.
                if !assoc_defined.is_empty() {
                    self.emit(r.def, file, range, 17, 17, "an inherent impl must not contain a `type` item".to_string());
                }
                continue;
            }
            // Only a trait whose declaration is in this build can be checked
            // (`impl io.Writer for File` inside package `std` is deferred by
            // the resolver: there is no `std` module to reach `io` through).
            if r.trait_def == NO_DEF || self.fir.sigs.kind(r.trait_def) != SigKind::Trait {
                continue;
            }
            let site = if is_operator_trait(self.prelude, r.trait_def) { 21 } else { 17 };
            let declared: Vec<(Symbol, fors_fir::sig::TraitRefListId)> = {
                let a = self.fir.sigs.assoc(r.trait_def);
                (0..self.fir.sigs.assocs.count(a)).map(|i| {
                    let row = self.fir.sigs.assocs.get(a, i);
                    (row.name, row.bounds)
                }).collect()
            };
            // MUST define every associated type of the trait, exactly once.
            for &(name, _) in &declared {
                if !assoc_defined.iter().any(|&(n, _)| n == name) {
                    let nm = self.sym(name);
                    self.emit(r.def, file, range, 17, site, format!("this impl does not define the associated type `{nm}`"));
                    break;
                }
            }
            if self.sink.poisoned() {
                continue;
            }
            // MUST NOT define anything else.
            for &(name, _) in &assoc_defined {
                if !declared.iter().any(|&(n, _)| n == name) {
                    let nm = self.sym(name);
                    let tn = self.name_of(r.trait_def);
                    self.emit(r.def, file, range, 17, site, format!("`{nm}` is not an associated type of `{tn}`"));
                    break;
                }
            }
            if self.sink.poisoned() {
                continue;
            }
            // Every right-hand side MUST meet the bounds the trait declares
            // for that associated type, with the impl's parameters rigid.
            for &(name, bounds) in &declared {
                let Some(&(_, rhs)) = assoc_defined.iter().find(|&&(n, _)| n == name) else { continue };
                if rhs == TY_ERROR || rhs == NO_TY {
                    continue;
                }
                let bs = self.fir.sigs.bounds.get(bounds).to_vec();
                for b in bs {
                    if self.holds(rhs, b) == Holds::No {
                        let bn = self.name_of(self.fir.tys.trait_ref(b).0);
                        let an = self.sym(name);
                        // The violated bound's own trait decides the site:
                        // `Item: Droppable` is R21's declaration.
                        let bsite = if self.is_language_known(self.fir.tys.trait_ref(b).0) && r.trait_def == self.prelude.traits[tr::ITERATOR] { 21 } else { site };
                        let bcode = if bsite == 21 { 21 } else { 17 };
                        self.emit(r.def, file, range, bcode, bsite, format!("`type {an} = ...;` does not satisfy the trait's bound `{bn}`"));
                        break;
                    }
                }
                if self.sink.poisoned() {
                    break;
                }
            }
            if self.sink.poisoned() {
                continue;
            }
            // MUST define every REQUIRED method of the trait.
            let required = self.required_methods(r.trait_def, files);
            let defined = self.impl_method_names(r.def);
            for (name, _) in &required {
                if !defined.iter().any(|&(n, _)| n == *name) {
                    let nm = self.sym(*name);
                    self.emit(r.def, file, range, 17, site, format!("this impl does not define the required method `{nm}`"));
                    break;
                }
            }
            if self.sink.poisoned() {
                continue;
            }
            // MUST NOT define anything else.
            let all_trait_methods = self.trait_method_names(r.trait_def);
            for (name, _) in &defined {
                if !all_trait_methods.contains(name) {
                    let nm = self.sym(*name);
                    let tn = self.name_of(r.trait_def);
                    self.emit(r.def, file, range, 17, site, format!("`{nm}` is not a method of `{tn}`"));
                    break;
                }
            }
            if self.sink.poisoned() {
                continue;
            }
            // Each method's signature MUST equal the trait's after
            // substituting `Self := S`, the trait parameters by `As` and
            // `Self.B` by this impl's definition of `B`.
            self.method_signatures(&r, &defined, file, range, site);
        }
    }

    fn is_language_known(&self, def: DefId) -> bool {
        self.prelude.trait_index(def).is_some()
    }

    /// `(name, def)` for every method a trait declares without a body.
    fn required_methods(&mut self, trait_def: DefId, files: &[FileCtx]) -> Vec<(Symbol, DefId)> {
        let ms = self.fir.sigs.members(trait_def);
        let n = self.fir.sigs.member_store.count(ms);
        let mut out = Vec::new();
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            if m.kind != MemberKind::Item {
                continue;
            }
            let provided = self
                .defs
                .get(m.def)
                .and_then(|row| files.get(row.file.index()).map(|f| f.has_block(row.node as usize)))
                .unwrap_or(false);
            if !provided {
                out.push((m.name, m.def));
            }
        }
        out
    }

    fn trait_method_names(&self, trait_def: DefId) -> Vec<Symbol> {
        let ms = self.fir.sigs.members(trait_def);
        let n = self.fir.sigs.member_store.count(ms);
        (0..n)
            .map(|i| self.fir.sigs.member_store.get(ms, i))
            .filter(|m| m.kind == MemberKind::Item)
            .map(|m| m.name)
            .collect()
    }

    fn impl_method_names(&self, def: DefId) -> Vec<(Symbol, DefId)> {
        let ms = self.fir.sigs.members(def);
        let n = self.fir.sigs.member_store.count(ms);
        (0..n)
            .map(|i| self.fir.sigs.member_store.get(ms, i))
            .filter(|m| m.kind == MemberKind::Item)
            .map(|m| (m.name, m.def))
            .collect()
    }
}

impl Wf<'_> {
    /// R17's signature-equality clause. The trait's signature is substituted
    /// (`Self := S`, trait parameters by `As`, `Self.B` by this impl's `B`)
    /// and compared to the impl's by `TyId` identity, which is R9's equality.
    fn method_signatures(&mut self, r: &ImplRow, defined: &[(Symbol, DefId)], file: FileId, range: (u32, u32), site: u16) {
        let trait_ms = self.fir.sigs.members(r.trait_def);
        let n = self.fir.sigs.member_store.count(trait_ms);
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(trait_ms, i);
            if m.kind != MemberKind::Item || m.def == NO_DEF {
                continue;
            }
            let Some(&(_, idef)) = defined.iter().find(|&&(nm, _)| nm == m.name) else { continue };
            if idef == NO_DEF {
                continue;
            }
            let want = self.fir.sigs.fn_sig(m.def);
            let got = self.fir.sigs.fn_sig(idef);
            if want == fors_fir::sig::NO_FN_SIG || got == fors_fir::sig::NO_FN_SIG {
                continue;
            }
            let Some(sub) = self.trait_binding(r) else { continue };
            let wn = self.fir.sigs.fn_sigs.count(want);
            let gn = self.fir.sigs.fn_sigs.count(got);
            if wn != gn {
                let nm = self.sym(m.name);
                self.emit(r.def, file, range, 17, site, format!("`{nm}` takes {gn} parameter(s); the trait declares {wn}"));
                return;
            }
            let mut mismatch: Option<String> = None;
            // MARC: verification of I2 (2026-09-20). R17 lists "same generic
            // parameters, bounds and constraint entries, conventions,
            // parameter NAMES and types, result type (`scoped` included) and
            // `raises` type"; I2 compared conventions, parameter types and
            // the result only. Names, `scoped`, `raises` and the generic
            // list (count, kinds, bound heads and constraint-entry count)
            // are compared now. Bound ARGUMENTS and the entries' subjects
            // are not: they may mention the trait's own parameters, and
            // substituting a `TraitRef` is I4's machinery. A head-level
            // comparison already rejects `T: Eq` against `T: Ord`.
            let wg = self.fir.sigs.generics(m.def);
            let gg = self.fir.sigs.generics(idef);
            let wgn = self.fir.sigs.generics_store.count(wg);
            let ggn = self.fir.sigs.generics_store.count(gg);
            if wgn != ggn {
                mismatch = Some(format!("it declares {ggn} generic parameter(s); the trait's declares {wgn}"));
            } else {
                for i in 0..wgn {
                    let a = self.fir.sigs.generics_store.param(wg, i);
                    let b = self.fir.sigs.generics_store.param(gg, i);
                    if a.kind.tag() != b.kind.tag() {
                        mismatch = Some(format!("generic parameter {} has a different kind from the trait's", i + 1));
                        break;
                    }
                    let ab = self.fir.sigs.bounds.get(a.bounds).to_vec();
                    let bb = self.fir.sigs.bounds.get(b.bounds).to_vec();
                    let heads = |this: &Self, xs: &[TraitRefId]| -> Vec<DefId> {
                        let mut v: Vec<DefId> = xs.iter().map(|&t| this.fir.tys.trait_ref(t).0).collect();
                        v.sort();
                        v.dedup();
                        v
                    };
                    if heads(self, &ab) != heads(self, &bb) {
                        mismatch = Some(format!("generic parameter {}'s bounds are not the trait's", i + 1));
                        break;
                    }
                }
                if mismatch.is_none() {
                    let wc = self.fir.sigs.constraints.count(self.fir.sigs.generics_store.constraints(wg));
                    let gc = self.fir.sigs.constraints.count(self.fir.sigs.generics_store.constraints(gg));
                    if wc != gc {
                        mismatch = Some("its constraint entries are not the trait's".to_string());
                    }
                }
            }
            for p in 0..wn {
                if mismatch.is_some() {
                    break;
                }
                let wp = self.fir.sigs.fn_sigs.param(want, p);
                let gp = self.fir.sigs.fn_sigs.param(got, p);
                if wp.conv != gp.conv {
                    mismatch = Some(format!("parameter {} has the wrong convention", p + 1));
                    break;
                }
                if wp.name != gp.name {
                    let a = self.sym(wp.name);
                    let b = self.sym(gp.name);
                    mismatch = Some(format!("parameter {} is named `{b}`; the trait names it `{a}`", p + 1));
                    break;
                }
                let Some(wt) = self.substitute(wp.ty, &sub, r) else { continue };
                if wt != TY_ERROR && gp.ty != TY_ERROR && wt != gp.ty {
                    mismatch = Some(format!("parameter {}'s type is not the trait's", p + 1));
                    break;
                }
            }
            if mismatch.is_none() {
                let wr = self.fir.sigs.fn_sigs.result(want);
                let gr = self.fir.sigs.fn_sigs.result(got);
                if let Some(wt) = self.substitute(wr, &sub, r) {
                    if wt != TY_ERROR && gr != TY_ERROR && wt != gr {
                        mismatch = Some("the result type is not the trait's".to_string());
                    }
                }
            }
            if mismatch.is_none() && self.fir.sigs.fn_sigs.scoped(want) != self.fir.sigs.fn_sigs.scoped(got) {
                mismatch = Some("the result's `scoped` designation is not the trait's".to_string());
            }
            if mismatch.is_none() {
                let wr = self.fir.sigs.fn_sigs.raises(want);
                let gr = self.fir.sigs.fn_sigs.raises(got);
                if (wr == NO_TY) != (gr == NO_TY) {
                    mismatch = Some(if wr == NO_TY {
                        "it raises; the trait's does not".to_string()
                    } else {
                        "it does not raise; the trait's does".to_string()
                    });
                } else if wr != NO_TY {
                    if let Some(wt) = self.substitute(wr, &sub, r) {
                        if wt != TY_ERROR && gr != TY_ERROR && wt != gr {
                            mismatch = Some("the `raises` type is not the trait's".to_string());
                        }
                    }
                }
            }
            if let Some(why) = mismatch {
                let nm = self.sym(m.name);
                self.emit(r.def, file, range, 17, site, format!("`{nm}`'s signature does not equal the trait's after substitution: {why}"));
                return;
            }
        }
    }

    /// The substitution an impl induces on its trait's signatures.
    fn trait_binding(&mut self, r: &ImplRow) -> Option<Binding> {
        let arity = self.fir.sigs.generics_store.count(self.fir.sigs.generics(r.trait_def));
        let mut b = Binding::new(&[(r.trait_def, arity as u16)]);
        b.bind(r.trait_def, 0, r.self_ty);
        let args = if r.trait_args == NO_ARGS { Vec::new() } else { self.fir.tys.args_vec(r.trait_args) };
        for (i, a) in args.iter().enumerate() {
            b.bind(r.trait_def, (i + 1) as u16, *a);
        }
        Some(b)
    }

    /// `subst_norm` plus R61(c): a `Self.B` left over from the trait's own
    /// signature is this impl's definition of `B`, with no lookup.
    fn substitute(&mut self, ty: TyId, b: &Binding, r: &ImplRow) -> Option<TyId> {
        if ty == NO_TY {
            return None;
        }
        let assoc: Vec<(Symbol, TyId)> = {
            let a = self.fir.sigs.assoc(r.def);
            (0..self.fir.sigs.assocs.count(a))
                .map(|i| {
                    let row = self.fir.sigs.assocs.get(a, i);
                    (row.name, row.rhs)
                })
                .collect()
        };
        let mut solver = ImplAssoc { trait_def: r.trait_def, assoc };
        fors_fir::subst::subst_norm_with(&mut self.fir.tys, ty, b, &mut solver)
    }

    // ----------------------------------------------------------- R21

    /// The two language-known prerequisites: `impl IndexMut[As] for S`
    /// requires `S: Index[As]`, and `impl Iterator for S` requires
    /// `S: Droppable` (round 6, O1).
    fn prerequisites(&mut self, low: &Lowered, files: &[FileCtx]) {
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if poisoned(low, r.def) || r.self_ty == TY_ERROR {
                continue;
            }
            let Some((file, range)) = self.head_range(files, r.def) else { continue };
            if r.trait_def == self.prelude.traits[tr::INDEXMUT] {
                let want = self.fir.tys.intern_trait_ref(self.prelude.traits[tr::INDEX], r.trait_args);
                if self.holds(r.self_ty, want) == Holds::No {
                    self.emit(r.def, file, range, 21, 21, "`impl IndexMut[I]` requires the same type to implement `Index[I]`".to_string());
                }
            } else if r.trait_def == self.prelude.traits[tr::ITERATOR] {
                let want = self.fir.tys.intern_trait_ref(self.prelude.traits[tr::DROPPABLE], NO_ARGS);
                if self.holds(r.self_ty, want) == Holds::No {
                    self.emit(r.def, file, range, 21, 21, "`impl Iterator for T` requires `T` to be `Droppable`: v0.1 has no linear iterator".to_string());
                }
            }
        }
    }

    // ----------------------------------------------------------- R23

    /// `impl Copyable for T {}` is accepted only if every field and payload
    /// component of `T` is `Copyable`, and never when `T` is linear.
    fn copyable_impl(&mut self, low: &Lowered, files: &[FileCtx]) {
        let copyable = self.prelude.traits[tr::COPYABLE];
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if r.trait_def != copyable || poisoned(low, r.def) || r.self_ty == TY_ERROR {
                continue;
            }
            let Some((file, range)) = self.head_range(files, r.def) else { continue };
            if self.is_linear(r.self_ty) {
                self.emit(r.def, file, range, 23, 23, "a linear type is never `Copyable` (ch01 R22e)".to_string());
                continue;
            }
            if let Some(bad) = self.first_non_copyable(r.self_ty, r.def) {
                let nm = self.render(bad);
                self.emit(r.def, file, range, 23, 23, format!("`{nm}` is not `Copyable`, so this impl is rejected"));
            }
        }
    }

    /// The first component of `ty` that is definitely not `Copyable`.
    fn first_non_copyable(&mut self, ty: TyId, owner: DefId) -> Option<TyId> {
        let mut todo = vec![ty];
        let mut seen: Vec<TyId> = Vec::new();
        let mut guard = 0u32;
        while let Some(x) = todo.pop() {
            guard += 1;
            if guard > 4096 || seen.contains(&x) {
                continue;
            }
            seen.push(x);
            if x == TY_ERROR || x == NO_TY {
                continue;
            }
            if self.fir.tys.quals(x).is_iso() {
                return Some(x);
            }
            match self.fir.tys.tag(x) {
                TyTag::Prim | TyTag::Unit | TyTag::Never | TyTag::ConstVal | TyTag::Brand => {}
                TyTag::Fn => {
                    if self.fir.tys.fn_tys().is_closure(FnTyId(self.fir.tys.a(x))) {
                        return Some(x);
                    }
                }
                TyTag::Dyn => return Some(x),
                TyTag::Tuple => todo.extend(self.fir.tys.args_vec(ArgsId(self.fir.tys.b(x)))),
                TyTag::Param | TyTag::Proj => {
                    // A field mentioning a parameter `P` needs the impl to
                    // declare `P: Copyable`.
                    let want = self.fir.tys.intern_trait_ref(self.prelude.traits[tr::COPYABLE], NO_ARGS);
                    if self.holds(x, want) == Holds::No {
                        return Some(x);
                    }
                }
                TyTag::Nominal => {
                    let def = DefId(self.fir.tys.a(x));
                    let args = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(x)));
                    if let Some(g) = self.prelude.generic_index(def) {
                        match g {
                            // Never `Copyable` (R23).
                            gty::OWN | gty::ARENA | gty::ATOMIC => return Some(x),
                            gty::REF | gty::RANGE | gty::RANGEINCL | gty::SLICE => {}
                            gty::ARRAY | gty::VECTOR | gty::MASK | gty::OPTION => {
                                if let Some(&e) = args.first() {
                                    todo.push(e);
                                }
                            }
                            _ => {}
                        }
                        continue;
                    }
                    if x != ty {
                        // A nominal component is `Copyable` only through its
                        // own impl (R23: the check is fieldwise on `T` only).
                        let want = self.fir.tys.intern_trait_ref(self.prelude.traits[tr::COPYABLE], NO_ARGS);
                        if self.holds(x, want) == Holds::No {
                            return Some(x);
                        }
                        continue;
                    }
                    let ms = self.fir.sigs.members(def);
                    let n = self.fir.sigs.member_store.count(ms);
                    let mut fields: Vec<TyId> = Vec::new();
                    for i in 0..n {
                        let m = self.fir.sigs.member_store.get(ms, i);
                        match m.kind {
                            MemberKind::Field => fields.push(m.ty),
                            MemberKind::Variant => match m.payload {
                                PayloadKind::Tuple => fields.extend(self.fir.tys.args_vec(m.args)),
                                PayloadKind::Record => {
                                    let k = self.fir.sigs.member_store.count(m.sub);
                                    for j in 0..k {
                                        fields.push(self.fir.sigs.member_store.get(m.sub, j).ty);
                                    }
                                }
                                PayloadKind::None => {}
                            },
                            MemberKind::Item => {}
                        }
                    }
                    // Substitute the head's arguments into the field types.
                    let arity = self.fir.sigs.generics_store.count(self.fir.sigs.generics(def));
                    if arity > 0 && args.len() == arity {
                        let mut b = Binding::new(&[(def, arity as u16)]);
                        for (i, a) in args.iter().enumerate() {
                            b.bind(def, i as u16, *a);
                        }
                        for f in &mut fields {
                            if let Some(s) = subst_norm(&mut self.fir.tys, *f, &b) {
                                *f = s;
                            }
                        }
                    }
                    todo.extend(fields);
                }
                TyTag::Error => {}
            }
        }
        let _ = owner;
        None
    }

    /// A type as a diagnostic spells it. I2 renders only what its own
    /// messages need; `display.rs` (I3) is the general answer.
    fn render(&mut self, ty: TyId) -> String {
        match self.fir.tys.tag(ty) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(ty));
                self.name_of(def)
            }
            TyTag::Param => {
                let owner = DefId(self.fir.tys.a(ty));
                let ord = self.fir.tys.b(ty) as usize;
                let g = self.fir.sigs.generics(owner);
                if ord < self.fir.sigs.generics_store.count(g) {
                    self.sym(self.fir.sigs.generics_store.param(g, ord).name)
                } else {
                    "a type parameter".to_string()
                }
            }
            TyTag::Dyn => "dyn".to_string(),
            TyTag::Fn => "a closure".to_string(),
            TyTag::Tuple => "a tuple".to_string(),
            _ => "this type".to_string(),
        }
    }
}

/// A `ProjSolver` that answers `Self.B` from one impl's own definitions
/// (R61(c)) and leaves every other projection neutral.
struct ImplAssoc {
    trait_def: DefId,
    assoc: Vec<(Symbol, TyId)>,
}

impl fors_fir::subst::ProjSolver for ImplAssoc {
    fn solve(&mut self, store: &mut fors_fir::ty::TyStore, head: TyId, key: fors_fir::ty::ProjKeyId) -> Option<TyId> {
        let (tref, name) = store.proj_key(key);
        let (tdef, _) = store.trait_ref(tref);
        if tdef != self.trait_def {
            return None;
        }
        let _ = head;
        self.assoc.iter().find(|&&(n, _)| n == name).map(|&(_, rhs)| rhs).filter(|&r| r != NO_TY && r != TY_ERROR)
    }
}

impl Wf<'_> {
    // ----------------------------------------------------------- R25

    /// `dyn Tr` is well-formed iff `Tr` is dyn-capable: no associated type,
    /// no generic method, every method a receiver method with convention
    /// `let` or `inout`, and `Self` nowhere but the receiver's type. R24 adds
    /// that a marker trait MUST NOT be used as `dyn`.
    fn dyn_capable(&mut self, low: &Lowered, _files: &[FileCtx]) {
        for &(home, file, range, tdef) in &low.sites.dyn_uses.clone() {
            if low.poisoned.get(home.index()).copied().unwrap_or(false) {
                continue;
            }
            if is_marker_trait(self.prelude, tdef) {
                let nm = self.name_of(tdef);
                self.emit(home, file, range, 24, 24, format!("`{nm}` is a marker trait and must not be used as `dyn`"));
                continue;
            }
            if self.fir.sigs.kind(tdef) != SigKind::Trait {
                continue;
            }
            let a = self.fir.sigs.assoc(tdef);
            if self.fir.sigs.assocs.count(a) > 0 {
                let nm = self.name_of(tdef);
                self.emit(home, file, range, 25, 25, format!("`{nm}` declares an associated type, so `dyn {nm}` does not exist"));
                continue;
            }
            let ms = self.fir.sigs.members(tdef);
            let n = self.fir.sigs.member_store.count(ms);
            let self_ty = self.fir.tys.param(tdef, 0);
            let mut bad: Option<String> = None;
            for i in 0..n {
                let m = self.fir.sigs.member_store.get(ms, i);
                if m.kind != MemberKind::Item || m.def == NO_DEF {
                    continue;
                }
                if self.shapes.arity(m.def) > 0 {
                    bad = Some(format!("`{}` is a generic method", self.sym(m.name)));
                    break;
                }
                let sig = self.fir.sigs.fn_sig(m.def);
                if sig == fors_fir::sig::NO_FN_SIG {
                    continue;
                }
                if self.fir.sigs.fn_sigs.receiver(sig) == fors_fir::sig::NO_SLOT {
                    bad = Some(format!("`{}` is an associated function, not a receiver method", self.sym(m.name)));
                    break;
                }
                let count = self.fir.sigs.fn_sigs.count(sig);
                let recv = self.fir.sigs.fn_sigs.param(sig, 0);
                if !matches!(recv.conv, Conv::Let | Conv::Inout) {
                    bad = Some(format!("`{}`'s receiver is neither `let` nor `inout`", self.sym(m.name)));
                    break;
                }
                let mut others: Vec<TyId> = (1..count).map(|p| self.fir.sigs.fn_sigs.param(sig, p).ty).collect();
                others.push(self.fir.sigs.fn_sigs.result(sig));
                let raises = self.fir.sigs.fn_sigs.raises(sig);
                if raises != NO_TY {
                    others.push(raises);
                }
                if others.iter().any(|&x| x != NO_TY && impls::mentions(&self.fir.tys, x, self_ty, &mut (1 << 14))) {
                    bad = Some(format!("`Self` occurs in `{}`'s signature outside the receiver", self.sym(m.name)));
                    break;
                }
            }
            if let Some(why) = bad {
                let nm = self.name_of(tdef);
                self.emit(home, file, range, 25, 25, format!("`{nm}` is not dyn-capable: {why}"));
            }
        }
    }

    // ----------------------------------------------------------- R48

    /// Member clashes, at the LATER declaration: two inherent methods of one
    /// head with the same name; an inherent member named like a field; an
    /// inherent associated function named like a variant.
    fn member_clashes(&mut self, low: &Lowered, files: &[FileCtx]) {
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        // Inherent members, grouped by head, in source order.
        let mut per_head: HashMap<u64, Vec<(u32, Symbol, DefId)>> = HashMap::new();
        for r in &rows {
            if !r.inherent || r.self_ty == TY_ERROR {
                continue;
            }
            let HeadKey::Nominal(_) = r.head else { continue };
            for (name, _) in self.impl_method_names(r.def) {
                per_head.entry(r.head.as_u64()).or_default().push((r.order, name, r.def));
            }
        }
        let mut keys: Vec<u64> = per_head.keys().copied().collect();
        keys.sort_unstable();
        for k in keys {
            let mut items = per_head[&k].clone();
            items.sort_by_key(|&(o, _, _)| o);
            for i in 0..items.len() {
                for j in 0..i {
                    if items[i].1 != items[j].1 {
                        continue;
                    }
                    let (_, name, def) = items[i];
                    if poisoned(low, def) {
                        continue;
                    }
                    let Some((file, range)) = self.head_range(files, def) else { continue };
                    let nm = self.sym(name);
                    self.emit(def, file, range, 48, 48, format!("`{nm}` is already an inherent member of this type"));
                    break;
                }
            }
            // Against the head's own fields and variants.
            let Some(&(_, _, any)) = per_head[&k].first() else { continue };
            let self_ty = rows.iter().find(|r| r.def == any).map(|r| r.self_ty).unwrap_or(TY_ERROR);
            if self_ty == TY_ERROR || self.fir.tys.tag(self_ty) != TyTag::Nominal {
                continue;
            }
            let head_def = DefId(self.fir.tys.a(self_ty));
            let ms = self.fir.sigs.members(head_def);
            let n = self.fir.sigs.member_store.count(ms);
            let own: Vec<(Symbol, MemberKind)> =
                (0..n).map(|i| self.fir.sigs.member_store.get(ms, i)).map(|m| (m.name, m.kind)).collect();
            for &(_, name, def) in &per_head[&k] {
                if poisoned(low, def) {
                    continue;
                }
                if let Some(&(_, kind)) = own.iter().find(|&&(n2, k2)| n2 == name && k2 != MemberKind::Item) {
                    let Some((file, range)) = self.head_range(files, def) else { continue };
                    let nm = self.sym(name);
                    let what = if kind == MemberKind::Field { "field" } else { "variant" };
                    self.emit(def, file, range, 48, 48, format!("`{nm}` is already a {what} of this type"));
                }
            }
        }
    }

    // ----------------------------------------------------------- R11

    /// R11's round-6 clause (ch01 R22b): a CONCRETE `Array[X, N]`,
    /// `vector[X, N]` or `atomic[X]` whose element type is linear.
    fn linear_elements(&mut self, low: &Lowered, _files: &[FileCtx]) {
        for &(home, file, range, elem, container) in &low.sites.elements.clone() {
            if low.poisoned.get(home.index()).copied().unwrap_or(false) {
                continue;
            }
            if matches!(self.fir.tys.tag(elem), TyTag::Param | TyTag::Proj | TyTag::Error) {
                continue; // a RIGID element type is R57's, not this rule's
            }
            if self.is_linear(elem) {
                let en = self.render(elem);
                let cn = self.sym(container);
                self.emit(home, file, range, 11, 11, format!("`{cn}` may not have the linear element type `{en}`: an element could never leave it"));
            }
        }
    }

    // ----------------------------------------------------------- R14

    /// A type of infinite size. One SCC pass over the graph whose nodes are
    /// struct/enum declarations plus one per associated type `Tr.A`.
    fn infinite_size(&mut self, low: &Lowered, files: &[FileCtx]) {
        // Node numbering: 0..decls.len() are declarations, then assoc nodes.
        let decls: Vec<DefId> = self
            .defs
            .user_defs()
            .filter(|(_, r)| matches!(r.kind, DeclKind::Struct | DeclKind::Enum))
            .map(|(d, _)| d)
            .collect();
        // Every trait in the build, the prelude's included: `struct
        // S[I: Iterator] { x: Option[I.Item] }` projects on a LANGUAGE-KNOWN
        // trait, and dropping that node would lose the very cycle R14's
        // associated-type clause exists for.
        let mut assoc_nodes: Vec<(DefId, Symbol)> = Vec::new();
        for i in 0..self.fir.sigs.len() {
            let d = DefId(i as u32);
            if self.fir.sigs.kind(d) != SigKind::Trait {
                continue;
            }
            let a = self.fir.sigs.assoc(d);
            for k in 0..self.fir.sigs.assocs.count(a) {
                assoc_nodes.push((d, self.fir.sigs.assocs.get(a, k).name));
            }
        }
        let n = decls.len() + assoc_nodes.len();
        if n == 0 {
            return;
        }
        // Sorted lookup, not a scan: `by_value_mentions` asks once per
        // mention, so a linear `position()` here would make R14 quadratic in
        // the number of declarations (the 100k-line corpus has 10 000).
        let mut decl_at: Vec<(u32, usize)> = decls.iter().enumerate().map(|(i, d)| (d.0, i)).collect();
        decl_at.sort_unstable();
        let mut assoc_at: Vec<((u32, u32), usize)> =
            assoc_nodes.iter().enumerate().map(|(i, &(t, n))| ((t.0, n.0), i + decls.len())).collect();
        assoc_at.sort_unstable();
        let idx_of_decl = |d: DefId| decl_at.binary_search_by_key(&d.0, |&(k, _)| k).ok().map(|i| decl_at[i].1);
        let idx_of_assoc = |t: DefId, s: Symbol| {
            assoc_at.binary_search_by_key(&(t.0, s.0), |&(k, _)| k).ok().map(|i| assoc_at[i].1)
        };
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
        // Declaration -> what its fields store by value.
        let mut witness: Vec<Option<(FileId, (u32, u32))>> = vec![None; n];
        for (i, &d) in decls.iter().enumerate() {
            let mut out: Vec<(DefId, Symbol)> = Vec::new();
            let mut nominals: Vec<DefId> = Vec::new();
            let field_tys = self.value_fields(d);
            for ft in field_tys {
                self.by_value_mentions(ft, &mut nominals, &mut out, 0);
            }
            for m in nominals {
                if let Some(j) = idx_of_decl(m) {
                    adj[i].push(j);
                }
            }
            for (tdef, name) in out {
                if let Some(j) = idx_of_assoc(tdef, name) {
                    adj[i].push(j);
                }
            }
            if let Some(row) = self.defs.get(d) {
                if let Some(f) = files.get(row.file.index()) {
                    witness[i] = Some((row.file, f.first_field_range(row.node as usize)));
                }
            }
        }
        // `Tr.A` -> every struct/enum an impl's `type A = RHS;` stores.
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in &rows {
            if r.trait_def == NO_DEF {
                continue;
            }
            let a = self.fir.sigs.assoc(r.def);
            for i in 0..self.fir.sigs.assocs.count(a) {
                let row = self.fir.sigs.assocs.get(a, i);
                let Some(src) = idx_of_assoc(r.trait_def, row.name) else { continue };
                let mut nominals: Vec<DefId> = Vec::new();
                let mut out: Vec<(DefId, Symbol)> = Vec::new();
                self.by_value_mentions(row.rhs, &mut nominals, &mut out, 0);
                for m in nominals {
                    if let Some(j) = idx_of_decl(m) {
                        adj[src].push(j);
                    }
                }
                // R14 gives an associated-type node only the edges
                // `Tr.A -> E` for a struct or enum `E`; a projection inside a
                // right-hand side is not one of them (`type Item = I.Item;`
                // on an adaptor is the shape that would otherwise self-loop).
                let _ = out;
                if witness[src].is_none() {
                    if let Some(drow) = self.defs.get(r.def) {
                        if let Some(f) = files.get(drow.file.index()) {
                            witness[src] = Some((drow.file, f.assoc_def_range(drow.node as usize, i)));
                        }
                    }
                }
            }
        }
        for c in tarjan(&adj) {
            let cyclic = c.len() > 1 || adj[c[0]].contains(&c[0]);
            if !cyclic {
                continue;
            }
            // Reported on one node of the cycle: the least, so the answer is
            // independent of the traversal.
            let node = *c.iter().min().unwrap();
            let home = if node < decls.len() { decls[node] } else { NO_DEF };
            if home != NO_DEF && poisoned(low, home) {
                continue;
            }
            let Some((file, range)) = witness[node] else { continue };
            let what = if node < decls.len() { self.name_of(decls[node]) } else { "this associated type".to_string() };
            self.emit(home, file, range, 14, 14, format!("`{what}` has infinite size: it stores a value of a type in its own cycle"));
        }
    }

    /// Every field and payload type of a struct or enum.
    fn value_fields(&mut self, def: DefId) -> Vec<TyId> {
        let ms = self.fir.sigs.members(def);
        let n = self.fir.sigs.member_store.count(ms);
        let mut out = Vec::new();
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            match m.kind {
                MemberKind::Field => out.push(m.ty),
                MemberKind::Variant => match m.payload {
                    PayloadKind::Tuple => out.extend(self.fir.tys.args_vec(m.args)),
                    PayloadKind::Record => {
                        let k = self.fir.sigs.member_store.count(m.sub);
                        for j in 0..k {
                            out.push(self.fir.sigs.member_store.get(m.sub, j).ty);
                        }
                    }
                    PayloadKind::None => {}
                },
                MemberKind::Item => {}
            }
        }
        out
    }

    /// What `ty` stores BY VALUE: the nominal declarations and the
    /// associated types it mentions outside `Own`, `Ref`, `Arena`, `Slice`,
    /// `rawptr`, a `fn` type and `dyn`.
    fn by_value_mentions(&mut self, ty: TyId, nominals: &mut Vec<DefId>, assoc: &mut Vec<(DefId, Symbol)>, depth: u32) {
        if depth > 64 || ty == TY_ERROR || ty == NO_TY {
            return;
        }
        match self.fir.tys.tag(ty) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(ty));
                let args = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(ty)));
                if let Some(g) = self.prelude.generic_index(def) {
                    match g {
                        // The indirections R14 names.
                        gty::OWN | gty::REF | gty::ARENA | gty::SLICE => return,
                        _ => {
                            for a in args {
                                self.by_value_mentions(a, nominals, assoc, depth + 1);
                            }
                            return;
                        }
                    }
                }
                if !nominals.contains(&def) {
                    nominals.push(def);
                }
                for a in args {
                    self.by_value_mentions(a, nominals, assoc, depth + 1);
                }
            }
            TyTag::Tuple => {
                for a in self.fir.tys.args_vec(ArgsId(self.fir.tys.b(ty))) {
                    self.by_value_mentions(a, nominals, assoc, depth + 1);
                }
            }
            TyTag::Proj => {
                let (tref, name) = self.fir.tys.proj_key(fors_fir::ty::ProjKeyId(self.fir.tys.b(ty)));
                let (tdef, _) = self.fir.tys.trait_ref(tref);
                if !assoc.contains(&(tdef, name)) {
                    assoc.push((tdef, name));
                }
            }
            // `rawptr`, a `fn` type and `dyn` are indirections.
            _ => {}
        }
    }
}

/// Tarjan's strongly-connected components, iterative (no recursion depth to
/// bound), returning each component's node list.
fn tarjan(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adj.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0usize; n];
    let mut on = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut out: Vec<Vec<usize>> = Vec::new();
    let mut counter = 0usize;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut call: Vec<(usize, usize)> = vec![(root, 0)];
        while let Some(&mut (v, ref mut i)) = call.last_mut() {
            if *i == 0 {
                index[v] = counter;
                low[v] = counter;
                counter += 1;
                stack.push(v);
                on[v] = true;
            }
            if *i < adj[v].len() {
                let w = adj[v][*i];
                *i += 1;
                if index[w] == usize::MAX {
                    call.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                if low[v] == index[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = stack.pop() {
                        on[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    out.push(comp);
                }
                call.pop();
                if let Some(&mut (p, _)) = call.last_mut() {
                    low[p] = low[p].min(low[v]);
                }
            }
        }
    }
    out
}
