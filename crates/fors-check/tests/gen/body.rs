//! Function bodies, built by inverting the typing rules: `expr(goal, mode)`
//! produces an expression whose type is `goal` by construction, choosing a
//! production whose result type matches (ch09 R26's synth/check split is
//! respected: a SYNTH position only ever gets a form that synthesises to
//! exactly the goal, so a literal there carries its suffix).

use crate::ast::*;
use crate::builder::{CKind, Callable, Gen};
use crate::types::*;

/// Checker gaps the generator found (see `gaps.rs`): forms the checker types
/// `TY_ERROR` without a word. They are not emitted by default; `gaps.rs` pins
/// each with a probe that must keep reproducing until the checker is fixed.
pub const EMIT_BRACKETED_STRUCT_LIT: bool = true;
pub const EMIT_RECORD_VARIANT_LIT: bool = true;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    Check,
    Synth,
}

#[derive(Clone, Debug)]
pub struct Local {
    pub name: String,
    pub ty: Ty,
    pub mutable: bool,
    /// `Some` for a parameter.
    pub conv: Option<Conv>,
    pub moved: bool,
    pub frame: u32,
}

impl Local {
    pub fn param(name: &str, ty: Ty, conv: Conv) -> Local {
        Local {
            name: name.to_string(),
            ty,
            mutable: conv == Conv::Inout,
            conv: Some(conv),
            moved: false,
            frame: 0,
        }
    }
}

pub struct FnCx {
    pub locals: Vec<Local>,
    pub raises: Option<Ty>,
    pub frame: u32,
    pub next_frame: u32,
    pub bounds: Bounds,
    pub in_loop: bool,
    pub in_defer: bool,
    /// Locals not to mention (they are lent `inout` to the call being built).
    pub forbidden: Vec<String>,
    pub counter: u32,
    pub unsafe_ok: bool,
    pub no_move: bool,
    pub self_ty: Option<Ty>,
}

impl FnCx {
    pub fn new(raises: Option<Ty>) -> FnCx {
        FnCx {
            locals: Vec::new(),
            raises,
            frame: 0,
            next_frame: 1,
            bounds: Bounds::new(),
            in_loop: false,
            in_defer: false,
            forbidden: Vec::new(),
            counter: 0,
            unsafe_ok: false,
            no_move: false,
            self_ty: None,
        }
    }

    pub fn fresh(&mut self, prefix: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("{prefix}{n}")
    }

    fn live(&self, l: &Local) -> bool {
        !l.moved && !self.forbidden.contains(&l.name)
    }

    fn live_idx(&self) -> Vec<usize> {
        (0..self.locals.len())
            .filter(|&i| self.live(&self.locals[i]))
            .collect()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Prod {
    Local,
    Field,
    Const,
    Call,
    Method,
    BoundMethod,
    If,
    Match,
    Bin,
    Neg,
    Cast,
    NumMethod,
    Index,
    StructLit,
    Variant,
    SomeNone,
    Tuple,
    Array,
    Cmp,
    Logic,
    MoveLocal,
}

impl Gen {
    fn mk(&mut self, ty: Ty, kind: EK) -> Expr {
        Expr {
            id: self.p.id(),
            ty,
            kind,
        }
    }

    fn is_copy_in(&self, cx: &FnCx, t: &Ty) -> bool {
        self.p.is_copy(t, &cx.bounds)
    }

    // --------------------------------------------------------- producible

    pub fn producible(&self, cx: &FnCx, t: &Ty) -> bool {
        self.producible_d(cx, t, 0)
    }

    fn producible_d(&self, cx: &FnCx, t: &Ty, d: u32) -> bool {
        if d > 8 {
            return false;
        }
        match t {
            Ty::Prim(_) | Ty::Unit => true,
            Ty::Param(_) => cx
                .locals
                .iter()
                .any(|l| !l.moved && l.ty == *t && self.is_copy_in(cx, &l.ty)),
            Ty::Option(a) | Ty::Array(a, _) => self.producible_d(cx, a, d + 1),
            Ty::Tuple(ts) => ts.iter().all(|a| self.producible_d(cx, a, d + 1)),
            Ty::Adt(n, _) => {
                if self.p.struct_decl(n).is_some() {
                    self.p
                        .struct_fields(t)
                        .is_some_and(|fs| fs.iter().all(|f| self.producible_d(cx, &f.ty, d + 1)))
                } else {
                    self.p
                        .enum_variants(t)
                        .is_some_and(|vs| vs.iter().any(|v| self.variant_producible(cx, v, d)))
                }
            }
        }
    }

    /// Whether a SYNTH position can build `t`: a generic enum's variant
    /// must mention the parameter, or nothing would determine it (ch09 R39).
    pub fn synth_ok(&self, cx: &FnCx, t: &Ty) -> bool {
        self.producible(cx, t) && self.synth_ok_d(cx, t, 0)
    }

    fn synth_ok_d(&self, cx: &FnCx, t: &Ty, d: u32) -> bool {
        if d > 8 {
            return false;
        }
        match t {
            Ty::Option(a) | Ty::Array(a, _) => self.synth_ok_d(cx, a, d + 1),
            Ty::Tuple(ts) => ts.iter().all(|a| self.synth_ok_d(cx, a, d + 1)),
            Ty::Adt(n, args) => {
                if self.p.struct_decl(n).is_some() {
                    self.p
                        .struct_fields(t)
                        .is_some_and(|fs| fs.iter().all(|f| self.synth_ok_d(cx, &f.ty, d + 1)))
                } else if args.is_empty() {
                    true
                } else {
                    self.p.enum_variants(t).is_some_and(|vs| {
                        vs.iter().any(|v| {
                            self.variant_producible(cx, v, 0)
                                && variant_mentions_param(&self.p, n, &v.name)
                        })
                    })
                }
            }
            _ => true,
        }
    }

    fn variant_producible(&self, cx: &FnCx, v: &Variant, d: u32) -> bool {
        match &v.shape {
            VShape::Unit => true,
            VShape::Tuple(ts) => ts.iter().all(|a| self.producible_d(cx, a, d + 1)),
            VShape::Record(fs) => {
                EMIT_RECORD_VARIANT_LIT && fs.iter().all(|f| self.producible_d(cx, &f.ty, d + 1))
            }
        }
    }

    /// A type the body can both name and build.
    pub fn rand_ty(&mut self, cx: &FnCx, depth: u32) -> Ty {
        let names = self.adt_names();
        for _ in 0..8 {
            let has_param = cx.locals.iter().any(|l| matches!(l.ty, Ty::Param(_)));
            let t = match self.rng.weighted(&[
                10,
                if names.is_empty() { 0 } else { 6 },
                2,
                1,
                1,
                if has_param { 3 } else { 0 },
            ]) {
                0 => Ty::Prim(self.prim()),
                1 => {
                    let n = names[self.rng.below(names.len())].clone();
                    let params = self.p.adt_params(&n);
                    let args: Vec<Ty> = params.iter().map(|_| Ty::Prim(self.prim())).collect();
                    Ty::Adt(n, args)
                }
                2 if depth > 0 => Ty::opt(Ty::Prim(self.prim())),
                3 if depth > 0 => Ty::Tuple(vec![Ty::Prim(self.prim()), Ty::Prim(self.prim())]),
                4 if depth > 0 => Ty::Array(
                    Box::new(Ty::Prim(self.num_prim())),
                    self.rng.range(2, 4) as u32,
                ),
                5 => {
                    let ps: Vec<&Local> = cx
                        .locals
                        .iter()
                        .filter(|l| matches!(l.ty, Ty::Param(_)))
                        .collect();
                    ps[self.rng.below(ps.len())].ty.clone()
                }
                _ => Ty::Prim(self.prim()),
            };
            if self.producible(cx, &t) {
                return t;
            }
        }
        Ty::Prim(Prim::I32)
    }

    // -------------------------------------------------------------- leaves

    fn suffix(&self, mode: Mode, p: Prim) -> Option<Prim> {
        (mode == Mode::Synth).then_some(p)
    }

    fn lit(&mut self, p: Prim, mode: Mode) -> Expr {
        let ty = Ty::Prim(p);
        if p == Prim::Bool {
            let b = self.rng.chance(1, 2);
            return self.mk(ty, EK::Bool(b));
        }
        let suf = self.suffix(mode, p);
        if p.is_float() {
            const F: [&str; 5] = ["0.5", "1.5", "2.0", "0.25", "3.75"];
            let t = F[self.rng.below(F.len())].to_string();
            self.mk(ty, EK::Float(t, suf))
        } else {
            let v = self.rng.range(0, 30) as u64;
            self.mk(ty, EK::Int(v, suf))
        }
    }

    /// A closed, always-available expression of type `goal`.
    pub fn leaf(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode) -> Expr {
        match goal {
            Ty::Prim(p) => self.lit(*p, mode),
            Ty::Unit => self.mk(Ty::Unit, EK::UnitLit),
            Ty::Param(_) => {
                let Some(idx) = cx
                    .locals
                    .iter()
                    .position(|l| !l.moved && l.ty == *goal && self.p.is_copy(&l.ty, &cx.bounds))
                else {
                    panic!(
                        "no local for {goal:?}; locals {:?}; bounds {:?}",
                        cx.locals, cx.bounds
                    );
                };
                let name = cx.locals[idx].name.clone();
                self.mk(goal.clone(), EK::Local(name))
            }
            Ty::Option(a) => {
                if mode == Mode::Check && self.rng.chance(1, 3) {
                    self.mk(goal.clone(), EK::None)
                } else {
                    let v = self.leaf(cx, a, mode);
                    self.mk(goal.clone(), EK::Some(Box::new(v)))
                }
            }
            Ty::Tuple(ts) => {
                let es: Vec<Expr> = ts.iter().map(|t| self.leaf(cx, t, mode)).collect();
                self.mk(goal.clone(), EK::Tuple(es))
            }
            Ty::Array(a, n) => {
                let es: Vec<Expr> = (0..*n).map(|_| self.leaf(cx, a, mode)).collect();
                self.mk(goal.clone(), EK::Array(es))
            }
            Ty::Adt(name, args) => {
                if self.p.struct_decl(name).is_some() {
                    let fields = self.p.struct_fields(goal).unwrap_or_default();
                    let fs: Vec<(String, Expr)> = fields
                        .iter()
                        .map(|f| (f.name.clone(), self.leaf(cx, &f.ty, mode)))
                        .collect();
                    // A generic literal in a SYNTH position needs every
                    // parameter fixed by a field; the first field is a `T`.
                    self.mk(
                        goal.clone(),
                        EK::StructLit {
                            name: name.clone(),
                            targs: if EMIT_BRACKETED_STRUCT_LIT && !args.is_empty() {
                                args.clone()
                            } else {
                                Vec::new()
                            },
                            fields: fs,
                        },
                    )
                } else {
                    let vs = self.p.enum_variants(goal).unwrap_or_default();
                    let generic = !args.is_empty();
                    let ok: Vec<&Variant> = vs
                        .iter()
                        .filter(|v| self.variant_producible(cx, v, 0))
                        .filter(|v| {
                            !generic
                                || mode == Mode::Check
                                || variant_mentions_param(&self.p, name, &v.name)
                        })
                        .collect();
                    let v = ok[self.rng.below(ok.len())].clone();
                    self.variant_expr(cx, goal, name, &v, mode, 0, false)
                }
            }
        }
    }

    fn variant_expr(
        &mut self,
        cx: &mut FnCx,
        goal: &Ty,
        name: &str,
        v: &Variant,
        mode: Mode,
        d: u32,
        use_dot: bool,
    ) -> Expr {
        let payload = match &v.shape {
            VShape::Unit => VPayload::Unit,
            VShape::Tuple(ts) => VPayload::Tuple(
                ts.iter()
                    .map(|t| {
                        if d == 0 {
                            self.leaf(cx, t, mode)
                        } else {
                            self.expr(cx, t, mode, d - 1)
                        }
                    })
                    .collect(),
            ),
            VShape::Record(fs) => VPayload::Rec(
                fs.iter()
                    .map(|f| {
                        let e = if d == 0 {
                            self.leaf(cx, &f.ty, mode)
                        } else {
                            self.expr(cx, &f.ty, mode, d - 1)
                        };
                        (f.name.clone(), e)
                    })
                    .collect(),
            ),
        };
        self.mk(
            goal.clone(),
            EK::Variant {
                adt: name.to_string(),
                variant: v.name.clone(),
                dot: use_dot && mode == Mode::Check && !matches!(v.shape, VShape::Record(_)),
                payload,
            },
        )
    }

    // ---------------------------------------------------------- expression

    pub fn expr(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Expr {
        for _ in 0..6 {
            let prods = self.prods_for(cx, goal, d);
            if prods.is_empty() {
                break;
            }
            let ws: Vec<usize> = prods.iter().map(|p| p.1).collect();
            let k = self.rng.weighted(&ws);
            if let Some(e) = self.run_prod(cx, prods[k].0, goal, mode, d) {
                return e;
            }
        }
        self.leaf(cx, goal, mode)
    }

    fn prods_for(&mut self, cx: &FnCx, goal: &Ty, d: u32) -> Vec<(Prod, usize)> {
        let mut v: Vec<(Prod, usize)> = Vec::new();
        let copy = self.is_copy_in(cx, goal);
        let deep = d > 0;
        if copy {
            v.push((Prod::Local, 7));
            v.push((Prod::Field, 4));
        } else if !cx.no_move {
            v.push((Prod::MoveLocal, 5));
        }
        v.push((Prod::Call, 3));
        v.push((Prod::Method, 3));
        match goal {
            Ty::Prim(p) => {
                if p.is_num() && !self.consts.is_empty() {
                    v.push((Prod::Const, 2));
                }
                v.push((Prod::BoundMethod, 2));
                if d >= 2 {
                    v.push((Prod::If, 1));
                    v.push((Prod::Match, 1));
                }
                if deep {
                    if p.is_num() {
                        v.push((Prod::Bin, 5));
                        v.push((Prod::Cast, 2));
                        v.push((Prod::Index, 2));
                        if p.is_int() {
                            v.push((Prod::NumMethod, if cx.unsafe_ok { 14 } else { 3 }));
                        }
                        if p.is_signed_int() || p.is_float() {
                            v.push((Prod::Neg, 1));
                        }
                    } else {
                        v.push((Prod::Cmp, 5));
                        v.push((Prod::Logic, 3));
                    }
                }
            }
            Ty::Adt(n, _) => {
                if self.p.struct_decl(n).is_some() {
                    v.push((Prod::StructLit, 6));
                } else {
                    v.push((Prod::Variant, 6));
                }
                if d >= 2 {
                    v.push((Prod::If, 1));
                    v.push((Prod::Match, 1));
                }
            }
            Ty::Option(_) => {
                v.push((Prod::SomeNone, 6));
                if d >= 2 {
                    v.push((Prod::If, 1));
                }
            }
            Ty::Tuple(_) => v.push((Prod::Tuple, 6)),
            Ty::Array(..) => v.push((Prod::Array, 6)),
            Ty::Param(_) if deep => v.push((Prod::Bin, 4)),
            _ => {}
        }
        v
    }

    fn run_prod(&mut self, cx: &mut FnCx, p: Prod, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        match p {
            Prod::Local => self.p_local(cx, goal),
            Prod::Field => self.p_field(cx, goal),
            Prod::Const => self.p_const(goal),
            Prod::Call => self.p_call(cx, goal, mode, d),
            Prod::Method => self.p_method(cx, goal, mode, d),
            Prod::BoundMethod => self.p_bound_method(cx, goal, mode, d),
            Prod::If => self.p_if(cx, goal, mode, d),
            Prod::Match => self.p_match_expr(cx, goal, mode, d),
            Prod::Bin => self.p_bin(cx, goal, d),
            Prod::Neg => {
                let a = self.expr(cx, goal, Mode::Synth, d - 1);
                Some(self.mk(goal.clone(), EK::Unary(UnOp::Neg, Box::new(a))))
            }
            Prod::Cast => self.p_cast(cx, goal, d),
            Prod::NumMethod => self.p_num_method(cx, goal, d),
            Prod::Index => self.p_index(cx, goal),
            Prod::StructLit => self.p_struct_lit(cx, goal, mode, d),
            Prod::Variant => self.p_variant(cx, goal, mode, d),
            Prod::SomeNone => self.p_option(cx, goal, mode, d),
            Prod::Tuple => {
                let Ty::Tuple(ts) = goal else { return None };
                let es: Vec<Expr> = ts
                    .iter()
                    .map(|t| self.expr(cx, t, mode, d.saturating_sub(1)))
                    .collect();
                Some(self.mk(goal.clone(), EK::Tuple(es)))
            }
            Prod::Array => {
                let Ty::Array(a, n) = goal else { return None };
                let es: Vec<Expr> = (0..*n)
                    .map(|_| self.expr(cx, a, mode, d.saturating_sub(1)))
                    .collect();
                Some(self.mk(goal.clone(), EK::Array(es)))
            }
            Prod::Cmp => self.p_cmp(cx, d),
            Prod::Logic => self.p_logic(cx, d),
            Prod::MoveLocal => self.p_move_local(cx, goal),
        }
    }

    // ------------------------------------------------------------- places

    fn p_local(&mut self, cx: &FnCx, goal: &Ty) -> Option<Expr> {
        let c: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| cx.locals[i].ty == *goal && self.is_copy_in(cx, &cx.locals[i].ty))
            .collect();
        if c.is_empty() {
            return None;
        }
        let i = c[self.rng.below(c.len())];
        Some(self.mk(goal.clone(), EK::Local(cx.locals[i].name.clone())))
    }

    /// Every field path (at most two deep) from a live local ending in a
    /// copyable field of type `goal`; `mutable_only` keeps those a write may
    /// reach.
    fn field_paths(
        &self,
        cx: &FnCx,
        goal: &Ty,
        mutable_only: bool,
    ) -> Vec<(usize, Vec<(String, Ty)>)> {
        let mut out = Vec::new();
        for i in cx.live_idx() {
            let l = &cx.locals[i];
            if mutable_only && !l.mutable {
                continue;
            }
            self.walk_fields(cx, i, &l.ty, Vec::new(), goal, 0, &mut out);
        }
        out
    }

    fn walk_fields(
        &self,
        cx: &FnCx,
        root: usize,
        ty: &Ty,
        path: Vec<(String, Ty)>,
        goal: &Ty,
        depth: u32,
        out: &mut Vec<(usize, Vec<(String, Ty)>)>,
    ) {
        let Some(fields) = self.p.struct_fields(ty) else {
            return;
        };
        for f in fields {
            let mut np = path.clone();
            np.push((f.name.clone(), f.ty.clone()));
            if f.ty == *goal && self.is_copy_in(cx, &f.ty) {
                out.push((root, np.clone()));
            }
            if depth < 1 {
                self.walk_fields(cx, root, &f.ty, np, goal, depth + 1, out);
            }
        }
    }

    fn path_expr(&mut self, cx: &FnCx, root: usize, path: &[(String, Ty)]) -> Expr {
        let mut e = self.mk(
            cx.locals[root].ty.clone(),
            EK::Local(cx.locals[root].name.clone()),
        );
        for (n, t) in path {
            e = self.mk(t.clone(), EK::Field(Box::new(e), n.clone()));
        }
        e
    }

    fn p_field(&mut self, cx: &FnCx, goal: &Ty) -> Option<Expr> {
        let c = self.field_paths(cx, goal, false);
        if c.is_empty() {
            return None;
        }
        let (root, path) = c[self.rng.below(c.len())].clone();
        Some(self.path_expr(cx, root, &path))
    }

    fn p_const(&mut self, goal: &Ty) -> Option<Expr> {
        let c: Vec<&(String, Ty)> = self.consts.iter().filter(|(_, t)| t == goal).collect();
        if c.is_empty() {
            return None;
        }
        let n = c[self.rng.below(c.len())].0.clone();
        Some(self.mk(goal.clone(), EK::Const(n)))
    }

    /// A place of exactly type `ty` writable through `inout`: a mutable local
    /// or a field path of one.
    fn mut_place(&mut self, cx: &FnCx, ty: &Ty) -> Option<(Expr, String)> {
        let mut c: Vec<(usize, Vec<(String, Ty)>)> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| cx.locals[i].mutable && cx.locals[i].ty == *ty)
            .map(|i| (i, Vec::new()))
            .collect();
        c.extend(self.field_paths(cx, ty, true));
        if c.is_empty() {
            return None;
        }
        let (root, path) = c[self.rng.below(c.len())].clone();
        let e = self.path_expr(cx, root, &path);
        Some((e, cx.locals[root].name.clone()))
    }

    fn can_move(&self, cx: &FnCx, i: usize) -> bool {
        let l = &cx.locals[i];
        cx.live(l)
            && l.frame == cx.frame
            && !cx.in_defer
            && matches!(l.conv, None | Some(Conv::Sink))
            && !self.is_copy_in(cx, &l.ty)
    }

    fn p_move_local(&mut self, cx: &mut FnCx, goal: &Ty) -> Option<Expr> {
        let c: Vec<usize> = (0..cx.locals.len())
            .filter(|&i| cx.locals[i].ty == *goal && self.can_move(cx, i))
            .collect();
        if c.is_empty() {
            return None;
        }
        let i = c[self.rng.below(c.len())];
        cx.locals[i].moved = true;
        let name = cx.locals[i].name.clone();
        let inner = self.mk(goal.clone(), EK::Local(name));
        Some(self.mk(goal.clone(), EK::Move(Box::new(inner))))
    }

    // --------------------------------------------------------------- calls

    fn pick_inst(&mut self, cx: &FnCx, bounds: &[String]) -> Option<Ty> {
        let mut cands: Vec<Ty> = vec![
            Ty::Prim(Prim::I32),
            Ty::Prim(Prim::I64),
            Ty::Prim(Prim::U8),
            Ty::Prim(Prim::F64),
            Ty::Prim(Prim::Usize),
            Ty::Prim(Prim::Bool),
        ];
        for n in self.adt_names() {
            if self.p.adt_params(&n).is_empty() {
                cands.push(Ty::adt(&n));
            }
        }
        // A rigid parameter of the enclosing fn is a candidate argument too.
        for n in cx.bounds.keys() {
            if n != "Self" {
                cands.push(Ty::Param(n.clone()));
            }
        }
        cands.retain(|t| {
            bounds.iter().all(|b| self.p.satisfies(t, b, &cx.bounds)) && self.producible(cx, t)
        });
        if cands.is_empty() {
            return None;
        }
        Some(cands[self.rng.below(cands.len())].clone())
    }

    fn call_args(
        &mut self,
        cx: &mut FnCx,
        params: &[(Conv, String, Ty)],
        mode: Mode,
        d: u32,
        labelled: bool,
    ) -> Option<Vec<Arg>> {
        let mut slots: Vec<Option<Arg>> = vec![None; params.len()];
        let saved = cx.forbidden.len();
        for (i, (conv, _, ty)) in params.iter().enumerate() {
            if *conv == Conv::Inout {
                let Some((e, root)) = self.mut_place(cx, ty) else {
                    cx.forbidden.truncate(saved);
                    return None;
                };
                cx.forbidden.push(root);
                slots[i] = Some(Arg {
                    id: self.p.id(),
                    label: None,
                    marker: Marker::Inout,
                    e,
                });
            }
        }
        for (i, (conv, _, ty)) in params.iter().enumerate() {
            if slots[i].is_some() {
                continue;
            }
            if !self.producible(cx, ty) || (mode == Mode::Synth && !self.synth_ok(cx, ty)) {
                cx.forbidden.truncate(saved);
                return None;
            }
            let e = match conv {
                Conv::Let => self.expr_borrow(cx, ty, mode, d),
                _ => self.expr(cx, ty, mode, d),
            };
            slots[i] = Some(Arg {
                id: self.p.id(),
                label: None,
                marker: Marker::None,
                e,
            });
        }
        cx.forbidden.truncate(saved);
        let mut args: Vec<Arg> = slots.into_iter().flatten().collect();
        if labelled {
            for (a, (_, n, _)) in args.iter_mut().zip(params) {
                a.label = Some(n.clone());
            }
        }
        Some(args)
    }

    /// An argument for a `let` parameter: a non-`Copyable` place is lent,
    /// not moved.
    fn expr_borrow(&mut self, cx: &mut FnCx, ty: &Ty, mode: Mode, d: u32) -> Expr {
        if self.is_copy_in(cx, ty) {
            return self.expr(cx, ty, mode, d);
        }
        let c: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| cx.locals[i].ty == *ty)
            .collect();
        if !c.is_empty() && self.rng.chance(2, 3) {
            let i = c[self.rng.below(c.len())];
            return self.mk(ty.clone(), EK::Local(cx.locals[i].name.clone()));
        }
        let saved = cx.no_move;
        cx.no_move = true;
        let e = self.expr(cx, ty, mode, d);
        cx.no_move = saved;
        e
    }

    fn callable_ok(&self, c: &Callable, cx: &FnCx) -> bool {
        c.raises.is_none() && (!c.is_unsafe || cx.unsafe_ok) && c.kind != CKind::Method
    }

    fn p_call(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        if d == 0 || cx.in_defer {
            return None;
        }
        let cands: Vec<usize> = (0..self.calls.len())
            .filter(|&i| {
                let c = &self.calls[i];
                if !self.callable_ok(c, cx) {
                    return false;
                }
                let mut m = std::collections::HashMap::new();
                unify(&c.ret, goal, &c.vars, &mut m)
            })
            .collect();
        // A raising callable handled in place also yields a value.
        let raising: Vec<usize> = (0..self.calls.len())
            .filter(|&i| {
                let c = &self.calls[i];
                c.raises.is_some() && c.kind != CKind::Method && c.vars.is_empty() && c.ret == *goal
            })
            .collect();
        if cands.is_empty() && raising.is_empty() {
            return None;
        }
        if !raising.is_empty() && (cands.is_empty() || self.rng.chance(1, 4)) {
            let c = self.calls[raising[self.rng.below(raising.len())]].clone();
            return self.build_raising(cx, &c, goal, d);
        }
        let c = self.calls[cands[self.rng.below(cands.len())]].clone();
        self.build_call(cx, &c, Some(goal), mode, d)
    }

    /// `callee(args) else |e| { default }` or, in a function that raises the
    /// same type, `callee(args)?`.
    fn build_raising(&mut self, cx: &mut FnCx, c: &Callable, goal: &Ty, d: u32) -> Option<Expr> {
        let params = c.params.clone();
        let args = self.call_args(cx, &params, Mode::Check, d - 1, false)?;
        let flow = if cx.raises == c.raises && cx.raises.is_some() && self.rng.chance(2, 3) {
            Flow::Try
        } else {
            let binder = cx.fresh("er");
            let block = self.handler_block(cx, goal, d);
            Flow::Handler { binder, block }
        };
        let call = Call {
            callee: c.path.clone(),
            sig: c.sig(),
            targs: Vec::new(),
            args,
            flow,
        };
        Some(self.mk(goal.clone(), EK::Call(call)))
    }

    fn handler_block(&mut self, cx: &mut FnCx, goal: &Ty, d: u32) -> Block {
        let (sf, mark) = self.enter(cx);
        let tail = if *goal == Ty::Unit {
            None
        } else {
            Some(Box::new(self.expr(
                cx,
                goal,
                Mode::Check,
                d.saturating_sub(2),
            )))
        };
        self.leave(cx, sf, mark);
        Block {
            id: self.p.id(),
            stmts: Vec::new(),
            tail,
        }
    }

    pub fn enter(&mut self, cx: &mut FnCx) -> (u32, usize) {
        let saved = (cx.frame, cx.locals.len());
        cx.frame = cx.next_frame;
        cx.next_frame += 1;
        saved
    }

    pub fn leave(&mut self, cx: &mut FnCx, frame: u32, mark: usize) {
        cx.locals.truncate(mark);
        cx.frame = frame;
    }

    /// A call to `c` whose result is `goal` (`None` for a statement).
    fn build_call(
        &mut self,
        cx: &mut FnCx,
        c: &Callable,
        goal: Option<&Ty>,
        mode: Mode,
        d: u32,
    ) -> Option<Expr> {
        let mut m = std::collections::HashMap::new();
        if let Some(g) = goal
            && !unify(&c.ret, g, &c.vars, &mut m)
        {
            return None;
        }
        for v in &c.vars {
            if !m.contains_key(v) {
                let bs = c
                    .var_bounds
                    .iter()
                    .find(|(n, _)| n == v)
                    .map(|(_, b)| b.clone())
                    .unwrap_or_default();
                m.insert(v.clone(), self.pick_inst(cx, &bs)?);
            }
        }
        // Bounds of an inferred or given instantiation must hold (R12).
        for (v, bs) in &c.var_bounds {
            if let Some(t) = m.get(v)
                && !bs.iter().all(|b| self.p.satisfies(t, b, &cx.bounds))
            {
                return None;
            }
        }
        let params: Vec<(Conv, String, Ty)> = c
            .params
            .iter()
            .map(|(cv, n, t)| (*cv, n.clone(), subst(t, &m)))
            .collect();
        let explicit = !c.own.is_empty()
            && self.rng.chance(2, 5)
            && c.own.iter().all(|g| {
                m.get(&g.name)
                    .is_some_and(|t| !matches!(t, Ty::Tuple(_) | Ty::Unit))
            });
        let targs: Vec<Ty> = if explicit {
            c.own.iter().map(|g| m[&g.name].clone()).collect()
        } else {
            Vec::new()
        };
        // Without explicit arguments the generics are fixed by the first
        // arguments' synthesised types, so every argument is a SYNTH form.
        let amode = if c.vars.is_empty() || explicit {
            mode_for_args(mode, c)
        } else {
            Mode::Synth
        };
        let labelled = self.rng.chance(1, 5) && !params.is_empty();
        let args = self.call_args(cx, &params, amode, d - 1, labelled)?;
        let ret = subst(&c.ret, &m);
        let call = Call {
            callee: c.path.clone(),
            sig: c.sig(),
            targs,
            args,
            flow: Flow::Plain,
        };
        Some(self.mk(ret, EK::Call(call)))
    }

    fn method_recv_ok(&self, cx: &FnCx, i: usize, conv: Conv) -> bool {
        let l = &cx.locals[i];
        match conv {
            Conv::Let => true,
            Conv::Inout => l.mutable,
            Conv::Sink => self.is_copy_in(cx, &l.ty) || self.can_move(cx, i),
        }
    }

    fn p_method(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        if d == 0 || cx.in_defer {
            return None;
        }
        let mut cands: Vec<(usize, usize, std::collections::HashMap<String, Ty>)> = Vec::new();
        for (ci, c) in self.calls.iter().enumerate() {
            let Some((conv, recv)) = &c.recv else {
                continue;
            };
            if c.raises.is_some() || (c.is_unsafe && !cx.unsafe_ok) {
                continue;
            }
            for li in cx.live_idx() {
                if !self.method_recv_ok(cx, li, *conv) {
                    continue;
                }
                let mut m = std::collections::HashMap::new();
                if !unify(recv, &cx.locals[li].ty, &c.vars, &mut m) {
                    continue;
                }
                if subst(&c.ret, &m) != *goal {
                    continue;
                }
                if !c.var_bounds.iter().all(|(v, bs)| {
                    m.get(v)
                        .is_none_or(|t| bs.iter().all(|b| self.p.satisfies(t, b, &cx.bounds)))
                }) {
                    continue;
                }
                cands.push((ci, li, m));
            }
        }
        if cands.is_empty() {
            return None;
        }
        let (ci, li, m) = cands[self.rng.below(cands.len())].clone();
        let c = self.calls[ci].clone();
        let recv_name = cx.locals[li].name.clone();
        let recv_ty = cx.locals[li].ty.clone();
        let conv = c.recv.as_ref().map(|r| r.0)?;
        // The receiver is used first; an implicit `sink self` move is
        // recorded now so the arguments cannot mention it again.
        let mut forbid_recv = false;
        if conv == Conv::Sink && !self.is_copy_in(cx, &recv_ty) {
            cx.locals[li].moved = true;
        }
        if conv == Conv::Inout {
            cx.forbidden.push(recv_name.clone());
            forbid_recv = true;
        }
        let params: Vec<(Conv, String, Ty)> = c
            .params
            .iter()
            .map(|(cv, n, t)| (*cv, n.clone(), subst(t, &m)))
            .collect();
        let args = self.call_args(cx, &params, mode_for_args(mode, &c), d - 1, false);
        if forbid_recv {
            cx.forbidden.pop();
        }
        let args = args?;
        let recv = self.mk(recv_ty, EK::Local(recv_name));
        let call = Call {
            callee: c.path.clone(),
            sig: c.sig(),
            targs: Vec::new(),
            args,
            flow: Flow::Plain,
        };
        Some(self.mk(goal.clone(), EK::Method(Box::new(recv), call)))
    }

    /// A method of a trait the receiver's rigid type is bounded by.
    fn p_bound_method(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        if d == 0 || cx.in_defer {
            return None;
        }
        let mut cands: Vec<(usize, String, FnDecl)> = Vec::new();
        for li in cx.live_idx() {
            let Ty::Param(pn) = &cx.locals[li].ty else {
                continue;
            };
            let Some(bs) = cx.bounds.get(pn) else {
                continue;
            };
            for b in bs {
                let Some(tr) = self.p.trait_decl(b) else {
                    continue;
                };
                for m in &tr.methods {
                    if m.ret == *goal {
                        cands.push((li, b.clone(), m.clone()));
                    }
                }
            }
        }
        if cands.is_empty() {
            return None;
        }
        let (li, _tr, m) = cands[self.rng.below(cands.len())].clone();
        let name = cx.locals[li].name.clone();
        let ty = cx.locals[li].ty.clone();
        let params: Vec<(Conv, String, Ty)> = m
            .params
            .iter()
            .filter(|p| p.name != "self")
            .map(|p| (p.conv, p.name.clone(), p.ty.clone().unwrap_or(Ty::Unit)))
            .collect();
        let args = self.call_args(
            cx,
            &params,
            mode_for_args(
                mode,
                &Callable {
                    path: String::new(),
                    kind: CKind::Method,
                    vars: Vec::new(),
                    var_bounds: Vec::new(),
                    own: Vec::new(),
                    recv: None,
                    params: Vec::new(),
                    ret: Ty::Unit,
                    raises: None,
                    is_unsafe: false,
                },
            ),
            d - 1,
            false,
        )?;
        let recv = self.mk(ty, EK::Local(name));
        let call = Call {
            callee: m.name.clone(),
            sig: Sig {
                generics: Vec::new(),
                params,
                ret: m.ret.clone(),
                raises: None,
            },
            targs: Vec::new(),
            args,
            flow: Flow::Plain,
        };
        Some(self.mk(goal.clone(), EK::Method(Box::new(recv), call)))
    }

    // ------------------------------------------------------------ operators

    fn p_bin(&mut self, cx: &mut FnCx, goal: &Ty, d: u32) -> Option<Expr> {
        let op = match goal {
            Ty::Prim(p) if p.is_int() => *self.rng.pick(&[
                BinOp::Add,
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::Div,
                BinOp::Rem,
                BinOp::BitAnd,
                BinOp::BitOr,
                BinOp::BitXor,
            ]),
            Ty::Prim(p) if p.is_float() => {
                *self
                    .rng
                    .pick(&[BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div])
            }
            Ty::Param(n) => {
                let bs = cx.bounds.get(n)?;
                let ops: Vec<BinOp> = [BinOp::Add]
                    .into_iter()
                    .filter(|o| o.trait_name().is_some_and(|t| bs.iter().any(|b| b == t)))
                    .collect();
                if ops.is_empty() {
                    return None;
                }
                ops[self.rng.below(ops.len())]
            }
            _ => return None,
        };
        let a = self.expr(cx, goal, Mode::Synth, d - 1);
        let b = self.expr(cx, goal, Mode::Check, d - 1);
        Some(self.mk(goal.clone(), EK::Binary(op, Box::new(a), Box::new(b))))
    }

    fn p_cast(&mut self, cx: &mut FnCx, goal: &Ty, d: u32) -> Option<Expr> {
        let Ty::Prim(p) = goal else { return None };
        let q = loop {
            let q = self.num_prim();
            if q != *p {
                break q;
            }
        };
        let a = self.expr(cx, &Ty::Prim(q), Mode::Synth, d - 1);
        Some(self.mk(goal.clone(), EK::Cast(Box::new(a), goal.clone())))
    }

    fn p_num_method(&mut self, cx: &mut FnCx, goal: &Ty, d: u32) -> Option<Expr> {
        let Ty::Prim(p) = goal else { return None };
        if !p.is_int() {
            return None;
        }
        let sig = |g: &Ty, recv: &Ty, params: Vec<(Conv, String, Ty)>| {
            let _ = recv;
            Sig {
                generics: Vec::new(),
                params,
                ret: g.clone(),
                raises: None,
            }
        };
        if self.rng.chance(1, 3) {
            // `x.wrap_as[T]()`: a lossy conversion to a numeric primitive.
            let q = self.num_prim();
            let conv = *self.rng.pick(&["wrap_as", "sat_as", "trunc_as"]);
            // G3 (gaps.rs, fixed in I11): a `const` receiver is a value head.
            let a = self.expr(cx, &Ty::Prim(q), Mode::Synth, d - 1);
            let call = Call {
                callee: conv.to_string(),
                sig: sig(goal, &Ty::Prim(q), Vec::new()),
                targs: vec![goal.clone()],
                args: Vec::new(),
                flow: Flow::Plain,
            };
            return Some(self.mk(goal.clone(), EK::Method(Box::new(a), call)));
        }
        let modes: &[&str] = if cx.unsafe_ok {
            &["wrap", "sat", "unchecked", "unchecked", "unchecked"]
        } else {
            &["wrap", "sat"]
        };
        let md = *self.rng.pick(modes);
        let op = *self.rng.pick(&["add", "sub", "mul"]);
        let a = self.expr(cx, goal, Mode::Synth, d - 1);
        let b = self.expr(cx, goal, Mode::Check, d - 1);
        let arg = Arg {
            id: self.p.id(),
            label: None,
            marker: Marker::None,
            e: b,
        };
        let call = Call {
            callee: format!("{md}_{op}"),
            sig: sig(goal, goal, vec![(Conv::Let, "rhs".into(), goal.clone())]),
            targs: Vec::new(),
            args: vec![arg],
            flow: Flow::Plain,
        };
        Some(self.mk(goal.clone(), EK::Method(Box::new(a), call)))
    }

    fn p_index(&mut self, cx: &mut FnCx, goal: &Ty) -> Option<Expr> {
        let c: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| matches!(&cx.locals[i].ty, Ty::Array(a, _) if **a == *goal))
            .collect();
        if c.is_empty() {
            return None;
        }
        let i = c[self.rng.below(c.len())];
        let Ty::Array(_, n) = cx.locals[i].ty.clone() else {
            return None;
        };
        let arr = self.mk(
            cx.locals[i].ty.clone(),
            EK::Local(cx.locals[i].name.clone()),
        );
        let k = self.rng.below(n as usize) as u64;
        let idx = self.mk(Ty::Prim(Prim::Usize), EK::Int(k, None));
        Some(self.mk(goal.clone(), EK::Index(Box::new(arr), Box::new(idx))))
    }

    fn p_cmp(&mut self, cx: &mut FnCx, d: u32) -> Option<Expr> {
        // A rigid parameter is compared through its `Ord` / `Eq` bound.
        let rigid: Vec<(Ty, Vec<BinOp>)> = cx
            .live_idx()
            .into_iter()
            .filter_map(|i| match &cx.locals[i].ty {
                Ty::Param(n) => {
                    let bs = cx.bounds.get(n)?;
                    let mut ops = Vec::new();
                    if bs.iter().any(|b| b == "Ord") {
                        ops.extend([BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge]);
                    }
                    if bs.iter().any(|b| b == "Eq") {
                        ops.extend([BinOp::Eq, BinOp::Ne]);
                    }
                    (!ops.is_empty()).then(|| (cx.locals[i].ty.clone(), ops))
                }
                _ => None,
            })
            .collect();
        let (ty, ops) = if !rigid.is_empty() && self.rng.chance(1, 2) {
            rigid[self.rng.below(rigid.len())].clone()
        } else {
            let p = if self.rng.chance(1, 8) {
                Prim::Bool
            } else {
                self.num_prim()
            };
            let ops = if p == Prim::Bool {
                vec![BinOp::Eq, BinOp::Ne]
            } else {
                vec![
                    BinOp::Lt,
                    BinOp::Le,
                    BinOp::Gt,
                    BinOp::Ge,
                    BinOp::Eq,
                    BinOp::Ne,
                ]
            };
            (Ty::Prim(p), ops)
        };
        let op = ops[self.rng.below(ops.len())];
        let a = self.expr(cx, &ty, Mode::Synth, d - 1);
        let b = self.expr(cx, &ty, Mode::Check, d - 1);
        Some(self.mk(
            Ty::Prim(Prim::Bool),
            EK::Binary(op, Box::new(a), Box::new(b)),
        ))
    }

    fn p_logic(&mut self, cx: &mut FnCx, d: u32) -> Option<Expr> {
        let bool_ty = Ty::Prim(Prim::Bool);
        if self.rng.chance(1, 4) {
            let a = self.expr(cx, &bool_ty, Mode::Synth, d - 1);
            return Some(self.mk(bool_ty, EK::Unary(UnOp::Not, Box::new(a))));
        }
        let op = if self.rng.chance(1, 2) {
            BinOp::And
        } else {
            BinOp::Or
        };
        let a = self.expr(cx, &bool_ty, Mode::Synth, d - 1);
        // The right operand runs conditionally: a move there would not be
        // unconditional, so it is built in its own frame.
        let (sf, mark) = self.enter(cx);
        let b = self.expr(cx, &bool_ty, Mode::Synth, d - 1);
        self.leave(cx, sf, mark);
        Some(self.mk(bool_ty, EK::Binary(op, Box::new(a), Box::new(b))))
    }

    // ----------------------------------------------------------- aggregates

    fn p_struct_lit(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        let Ty::Adt(name, args) = goal else {
            return None;
        };
        let fields = self.p.struct_fields(goal)?;
        let generic = !args.is_empty();
        let explicit = EMIT_BRACKETED_STRUCT_LIT && generic && self.rng.chance(1, 3);
        let fmode = if generic && mode == Mode::Synth && !explicit {
            Mode::Synth
        } else {
            Mode::Check
        };
        if fmode == Mode::Synth && !fields.iter().all(|f| self.synth_ok(cx, &f.ty)) {
            return None;
        }
        let fs: Vec<(String, Expr)> = fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    self.expr(cx, &f.ty, fmode, d.saturating_sub(1)),
                )
            })
            .collect();
        Some(self.mk(
            goal.clone(),
            EK::StructLit {
                name: name.clone(),
                targs: if explicit { args.clone() } else { Vec::new() },
                fields: fs,
            },
        ))
    }

    fn p_variant(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        let Ty::Adt(name, args) = goal else {
            return None;
        };
        let vs = self.p.enum_variants(goal)?;
        let generic = !args.is_empty();
        let ok: Vec<&Variant> = vs
            .iter()
            .filter(|v| self.variant_producible(cx, v, 0))
            .filter(|v| {
                !generic || mode == Mode::Check || variant_mentions_param(&self.p, name, &v.name)
            })
            .collect();
        if ok.is_empty() {
            return None;
        }
        let v = ok[self.rng.below(ok.len())].clone();
        let dot = self.rng.chance(1, 3);
        Some(self.variant_expr(cx, goal, name, &v, mode, d, dot))
    }

    fn p_option(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        let Ty::Option(a) = goal else { return None };
        if mode == Mode::Check && self.rng.chance(1, 4) {
            return Some(self.mk(goal.clone(), EK::None));
        }
        let v = self.expr(cx, a, mode, d.saturating_sub(1));
        Some(self.mk(goal.clone(), EK::Some(Box::new(v))))
    }

    // ------------------------------------------------------- if and match

    pub fn tail_block(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Block {
        let (sf, mark) = self.enter(cx);
        let mut stmts = Vec::new();
        if self.rng.chance(1, 4) {
            self.s_let(cx, &mut stmts, d.saturating_sub(2));
        }
        let tail = self.expr(cx, goal, mode, d.saturating_sub(1));
        self.leave(cx, sf, mark);
        Block {
            id: self.p.id(),
            stmts,
            tail: Some(Box::new(tail)),
        }
    }

    fn p_if(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        let cond = self.expr(cx, &Ty::Prim(Prim::Bool), Mode::Synth, d - 1);
        let t = self.tail_block(cx, goal, mode, d);
        let e = self.tail_block(cx, goal, mode, d);
        Some(self.mk(
            goal.clone(),
            EK::If(Box::new(cond), Box::new(t), Box::new(e)),
        ))
    }

    /// The scrutinee candidates: copyable live locals of an enum, `Option`,
    /// `bool` or integer type.
    fn scrutinee(&mut self, cx: &FnCx) -> Option<Expr> {
        let c: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| {
                let t = &cx.locals[i].ty;
                self.is_copy_in(cx, t)
                    && match t {
                        Ty::Option(_) => true,
                        Ty::Prim(p) => *p == Prim::Bool || p.is_int(),
                        Ty::Adt(n, _) => self.p.enum_decl(n).is_some(),
                        _ => false,
                    }
            })
            .collect();
        if c.is_empty() {
            return None;
        }
        let i = c[self.rng.below(c.len())];
        Some(self.mk(
            cx.locals[i].ty.clone(),
            EK::Local(cx.locals[i].name.clone()),
        ))
    }

    /// An exhaustive pattern list for `t`, each with the binders it
    /// introduces.
    fn pats_for(&mut self, cx: &mut FnCx, t: &Ty) -> Vec<(Pat, Vec<(String, Ty)>)> {
        let mut out = Vec::new();
        match t {
            Ty::Prim(Prim::Bool) => {
                for b in [true, false] {
                    out.push((self.pat(PK::Bool(b)), Vec::new()));
                }
            }
            Ty::Prim(_) => {
                let n = self.rng.range(1, 2);
                for k in 0..n {
                    out.push((self.pat(PK::Int(k as i64)), Vec::new()));
                }
                if self.rng.chance(1, 2) {
                    let b = cx.fresh("bd");
                    out.push((self.pat(PK::Bind(b.clone())), vec![(b, t.clone())]));
                } else {
                    out.push((self.pat(PK::Wild), Vec::new()));
                }
            }
            Ty::Option(a) => {
                let (inner, binds) = self.sub_pat(cx, a);
                let some = self.pat(PK::Some(Box::new(inner)));
                out.push((some, binds));
                out.push((self.pat(PK::None), Vec::new()));
            }
            Ty::Adt(n, _) => {
                let vs = self.p.enum_variants(t).unwrap_or_default();
                let wild_last = vs.len() > 1 && self.rng.chance(1, 4);
                let dot = self.rng.chance(1, 3);
                for (k, v) in vs.iter().enumerate() {
                    if wild_last && k == vs.len() - 1 {
                        out.push((self.pat(PK::Wild), Vec::new()));
                        break;
                    }
                    let mut binds = Vec::new();
                    let sub = match &v.shape {
                        VShape::Unit => PSub::Unit,
                        VShape::Tuple(ts) => PSub::Tuple(
                            ts.iter()
                                .map(|x| {
                                    let (p, b) = self.sub_pat(cx, x);
                                    binds.extend(b);
                                    p
                                })
                                .collect(),
                        ),
                        VShape::Record(fs) => PSub::Rec(
                            fs.iter()
                                .map(|f| {
                                    let (p, b) = self.sub_pat(cx, &f.ty);
                                    binds.extend(b);
                                    (f.name.clone(), p)
                                })
                                .collect(),
                        ),
                    };
                    let p = self.pat(PK::Variant {
                        adt: n.clone(),
                        variant: v.name.clone(),
                        dot,
                        sub,
                    });
                    out.push((p, binds));
                }
            }
            _ => {}
        }
        out
    }

    fn pat(&mut self, kind: PK) -> Pat {
        Pat {
            id: self.p.id(),
            kind,
        }
    }

    /// A pattern for one payload component: a binder or `_`.
    fn sub_pat(&mut self, cx: &mut FnCx, t: &Ty) -> (Pat, Vec<(String, Ty)>) {
        if self.rng.chance(3, 5) {
            let b = cx.fresh("bd");
            (self.pat(PK::Bind(b.clone())), vec![(b, t.clone())])
        } else {
            (self.pat(PK::Wild), Vec::new())
        }
    }

    fn arm_scope<T>(
        &mut self,
        cx: &mut FnCx,
        binds: &[(String, Ty)],
        f: impl FnOnce(&mut Gen, &mut FnCx) -> T,
    ) -> T {
        let (sf, mark) = self.enter(cx);
        for (n, t) in binds {
            cx.locals.push(Local {
                name: n.clone(),
                ty: t.clone(),
                mutable: false,
                conv: None,
                moved: false,
                frame: cx.frame,
            });
        }
        let r = f(self, cx);
        self.leave(cx, sf, mark);
        r
    }

    fn p_match_expr(&mut self, cx: &mut FnCx, goal: &Ty, mode: Mode, d: u32) -> Option<Expr> {
        let scrut = self.scrutinee(cx)?;
        let pats = self.pats_for(cx, &scrut.ty);
        if pats.is_empty() {
            return None;
        }
        let mut arms = Vec::new();
        for (pat, binds) in pats {
            let body = self.arm_scope(cx, &binds, |g, cx| {
                g.expr(cx, goal, mode, d.saturating_sub(2))
            });
            arms.push(Arm {
                id: self.p.id(),
                pat,
                body: ArmBody::Expr(body),
            });
        }
        Some(self.mk(goal.clone(), EK::Match(Box::new(scrut), arms)))
    }

    // ============================================================ statements

    pub fn fn_body(&mut self, cx: &mut FnCx, ret: &Ty) -> Block {
        let id = self.p.id();
        let mut stmts = Vec::new();
        let n = self.rng.range(1, 5);
        for _ in 0..n {
            self.stmt(cx, &mut stmts, 2);
        }
        let mut tail = None;
        if *ret != Ty::Unit {
            let e = self.expr(cx, ret, Mode::Check, 2);
            if self.rng.chance(1, 3) {
                tail = Some(Box::new(e));
            } else {
                stmts.push(Stmt {
                    id: self.p.id(),
                    kind: SK::Return(Some(e)),
                });
            }
        }
        Block { id, stmts, tail }
    }

    fn push(&mut self, out: &mut Vec<Stmt>, kind: SK) {
        out.push(Stmt {
            id: self.p.id(),
            kind,
        });
    }

    pub fn stmt(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        let deep = d > 0;
        let w = [
            8,
            4,
            3,
            if deep { 2 } else { 0 },
            if deep { 2 } else { 0 },
            if deep { 2 } else { 0 },
            if deep { 1 } else { 0 },
            if cx.raises.is_some() { 5 } else { 1 },
            if cx.raises.is_some() { 2 } else { 0 },
            2,
            if cx.in_loop { 1 } else { 0 },
        ];
        let before = out.len();
        match self.rng.weighted(&w) {
            0 => self.s_let(cx, out, d),
            1 => self.s_assign(cx, out, d),
            2 => self.s_call(cx, out, d),
            3 => self.s_if(cx, out, d),
            4 => self.s_match(cx, out, d),
            5 => self.s_for(cx, out, d),
            6 => self.s_while(cx, out, d),
            7 => self.s_defer(cx, out),
            8 => self.s_raise(cx, out),
            9 => self.s_try(cx, out, d),
            _ => self.s_loop_exit(cx, out),
        }
        if out.len() == before {
            self.s_let(cx, out, d);
        }
    }

    pub fn s_let(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, _d: u32) {
        let ty = self.rand_ty(cx, 1);
        let annotate = self.rng.chance(2, 3) || !self.synth_ok(cx, &ty);
        let var = self.rng.chance(1, 2);
        let name = cx.fresh("v");
        let mode = if annotate { Mode::Check } else { Mode::Synth };
        let init = self.expr(cx, &ty, mode, 2);
        let ty_id = self.p.id();
        self.push(
            out,
            SK::Let {
                var,
                name: name.clone(),
                ty: annotate.then(|| ty.clone()),
                ty_id,
                init: Some(init),
            },
        );
        cx.locals.push(Local {
            name,
            ty,
            mutable: var,
            conv: None,
            moved: false,
            frame: cx.frame,
        });
    }

    fn s_assign(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, _d: u32) {
        let c: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| cx.locals[i].mutable)
            .collect();
        if c.is_empty() {
            return;
        }
        let i = c[self.rng.below(c.len())];
        let ty = cx.locals[i].ty.clone();
        // Either the whole local or one copyable field of it.
        let fields = self.p.struct_fields(&ty).unwrap_or_default();
        let (place, pty) = if !fields.is_empty() && self.rng.chance(1, 2) {
            let f = fields[self.rng.below(fields.len())].clone();
            if !self.is_copy_in(cx, &f.ty) {
                return;
            }
            let base = self.mk(ty.clone(), EK::Local(cx.locals[i].name.clone()));
            (
                self.mk(f.ty.clone(), EK::Field(Box::new(base), f.name)),
                f.ty,
            )
        } else {
            (
                self.mk(ty.clone(), EK::Local(cx.locals[i].name.clone())),
                ty,
            )
        };
        if !self.producible(cx, &pty) {
            return;
        }
        let root = cx.locals[i].name.clone();
        cx.forbidden.push(root);
        let op = match &pty {
            Ty::Prim(p) if p.is_num() && self.rng.chance(1, 3) => {
                *self
                    .rng
                    .pick(&[AssignOp::Add, AssignOp::Sub, AssignOp::Mul])
            }
            _ => AssignOp::Set,
        };
        let rhs = self.expr(cx, &pty, Mode::Check, 2);
        cx.forbidden.pop();
        self.push(out, SK::Assign(place, op, rhs));
    }

    fn s_call(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        if cx.in_defer {
            return;
        }
        let cands: Vec<usize> = (0..self.calls.len())
            .filter(|&i| {
                let c = &self.calls[i];
                c.raises.is_none()
                    && (!c.is_unsafe || cx.unsafe_ok)
                    && (c.ret == Ty::Unit || self.p.is_copy(&c.ret, &cx.bounds))
            })
            .collect();
        if cands.is_empty() {
            return;
        }
        // Calls that lend a place `inout` or consume a resource are the ones
        // the ownership rules are about: weight them up.
        let ws: Vec<usize> = cands
            .iter()
            .map(|&i| {
                let c = &self.calls[i];
                let mut w = 1;
                if c.params.iter().any(|(cv, _, _)| *cv == Conv::Inout) {
                    w += 4;
                }
                if c.params
                    .iter()
                    .any(|(cv, _, t)| *cv == Conv::Sink && !self.p.is_copy(t, &cx.bounds))
                {
                    w += 4;
                }
                if matches!(c.recv, Some((Conv::Inout | Conv::Sink, _))) {
                    w += 3;
                }
                w
            })
            .collect();
        let c = self.calls[cands[self.rng.weighted(&ws)]].clone();
        self.ensure_inputs(cx, out, &c);
        let e = if c.recv.is_some() {
            // A method statement: find any receiver by asking for its result.
            self.method_stmt(cx, &c, d)
        } else {
            self.build_call(cx, &c, None, Mode::Check, 2)
        };
        if let Some(e) = e {
            self.push(out, SK::Expr(e));
        }
    }

    /// Declares the places a call wants: a mutable local for each `inout`
    /// parameter and a movable one for a consumed resource, so those calls
    /// are not starved of arguments.
    fn ensure_inputs(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, c: &Callable) {
        let mut wants: Vec<(Ty, bool)> = Vec::new();
        for (cv, _, t) in &c.params {
            match cv {
                Conv::Inout => wants.push((t.clone(), true)),
                Conv::Sink if !self.p.is_copy(t, &cx.bounds) => wants.push((t.clone(), false)),
                _ => {}
            }
        }
        if let Some((cv, t)) = &c.recv {
            match cv {
                Conv::Inout => wants.push((t.clone(), true)),
                Conv::Sink if !self.p.is_copy(t, &cx.bounds) => wants.push((t.clone(), false)),
                _ => {}
            }
        }
        for (ty, mutable) in wants {
            if has_param(&ty) || !self.producible(cx, &ty) {
                continue;
            }
            let have = if mutable {
                cx.live_idx()
                    .into_iter()
                    .any(|i| cx.locals[i].mutable && cx.locals[i].ty == ty)
            } else {
                (0..cx.locals.len()).any(|i| cx.locals[i].ty == ty && self.can_move(cx, i))
            };
            if have || (!mutable && !self.rng.chance(2, 3)) {
                continue;
            }
            let name = cx.fresh("v");
            let init = self.expr(cx, &ty, Mode::Check, 1);
            let ty_id = self.p.id();
            self.push(
                out,
                SK::Let {
                    var: mutable,
                    name: name.clone(),
                    ty: Some(ty.clone()),
                    ty_id,
                    init: Some(init),
                },
            );
            cx.locals.push(Local {
                name,
                ty,
                mutable,
                conv: None,
                moved: false,
                frame: cx.frame,
            });
        }
    }

    fn method_stmt(&mut self, cx: &mut FnCx, c: &Callable, _d: u32) -> Option<Expr> {
        let goal = c.ret.clone();
        // Only calls whose result type needs no substitution are statements.
        if has_param(&goal) {
            return None;
        }
        let saved = self.calls.clone();
        self.calls = vec![c.clone()];
        let r = self.p_method(cx, &goal, Mode::Check, 2);
        self.calls = saved;
        r
    }

    pub fn block_of(&mut self, cx: &mut FnCx, d: u32, in_loop: bool, extra: Vec<Local>) -> Block {
        let (sf, mark) = self.enter(cx);
        let saved_loop = cx.in_loop;
        cx.in_loop = cx.in_loop || in_loop;
        for mut l in extra {
            l.frame = cx.frame;
            cx.locals.push(l);
        }
        let mut stmts = Vec::new();
        for _ in 0..self.rng.range(0, 2) {
            self.stmt(cx, &mut stmts, d.saturating_sub(1));
        }
        cx.in_loop = saved_loop;
        self.leave(cx, sf, mark);
        Block {
            id: self.p.id(),
            stmts,
            tail: None,
        }
    }

    fn s_if(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        let cond = self.expr(cx, &Ty::Prim(Prim::Bool), Mode::Synth, 1);
        let then = self.block_of(cx, d, false, Vec::new());
        let els = if self.rng.chance(1, 2) {
            Some(self.block_of(cx, d, false, Vec::new()))
        } else {
            None
        };
        self.push(out, SK::If { cond, then, els });
    }

    fn s_match(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        let Some(scrut) = self.scrutinee(cx) else {
            return;
        };
        let pats = self.pats_for(cx, &scrut.ty);
        let mut arms = Vec::new();
        for (pat, binds) in pats {
            let extra: Vec<Local> = binds
                .into_iter()
                .map(|(n, t)| Local {
                    name: n,
                    ty: t,
                    mutable: false,
                    conv: None,
                    moved: false,
                    frame: 0,
                })
                .collect();
            let body = self.block_of(cx, d, false, extra);
            arms.push(Arm {
                id: self.p.id(),
                pat,
                body: ArmBody::Block(body),
            });
        }
        self.push(out, SK::Match { scrut, arms });
    }

    fn s_for(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        let var = cx.fresh("lp");
        // The iterable and the loop variable's type.
        let ints: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| matches!(cx.locals[i].ty, Ty::Prim(p) if p.is_int()))
            .collect();
        let arrs: Vec<usize> = cx
            .live_idx()
            .into_iter()
            .filter(|&i| {
                matches!(&cx.locals[i].ty, Ty::Array(a, _) if self.p.is_copy(a, &cx.bounds))
                    && self.is_copy_in(cx, &cx.locals[i].ty)
            })
            .collect();
        let (iter, vty) = match self.rng.below(4) {
            0 if !arrs.is_empty() => {
                let i = arrs[self.rng.below(arrs.len())];
                let Ty::Array(a, _) = cx.locals[i].ty.clone() else {
                    return;
                };
                (
                    self.mk(
                        cx.locals[i].ty.clone(),
                        EK::Local(cx.locals[i].name.clone()),
                    ),
                    *a,
                )
            }
            1 if !ints.is_empty() => {
                // `0 ..< n`: the unsuffixed left bound takes `n`'s type.
                let i = ints[self.rng.below(ints.len())];
                let t = cx.locals[i].ty.clone();
                let lo = self.mk(t.clone(), EK::Int(0, None));
                let hi = self.mk(t.clone(), EK::Local(cx.locals[i].name.clone()));
                let r = self.mk(
                    Ty::Unit,
                    EK::Binary(BinOp::Range, Box::new(lo), Box::new(hi)),
                );
                (r, t)
            }
            2 => {
                let lo = self.mk(Ty::Prim(Prim::Usize), EK::Int(0, Some(Prim::Usize)));
                let k = self.rng.range(1, 4) as u64;
                let hi = self.mk(Ty::Prim(Prim::Usize), EK::Int(k, Some(Prim::Usize)));
                let r = self.mk(
                    Ty::Unit,
                    EK::Binary(BinOp::Range, Box::new(lo), Box::new(hi)),
                );
                (r, Ty::Prim(Prim::Usize))
            }
            _ => {
                let lo = self.mk(Ty::Prim(Prim::I32), EK::Int(0, None));
                let k = self.rng.range(1, 4) as u64;
                let hi = self.mk(Ty::Prim(Prim::I32), EK::Int(k, None));
                let r = self.mk(
                    Ty::Unit,
                    EK::Binary(BinOp::Range, Box::new(lo), Box::new(hi)),
                );
                (r, Ty::Prim(Prim::I32))
            }
        };
        let extra = vec![Local {
            name: var.clone(),
            ty: vty,
            mutable: false,
            conv: None,
            moved: false,
            frame: 0,
        }];
        let body = self.block_of(cx, d, true, extra);
        self.push(out, SK::For { var, iter, body });
    }

    fn s_while(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, d: u32) {
        let name = cx.fresh("w");
        let i32t = Ty::Prim(Prim::I32);
        let zero = self.mk(i32t.clone(), EK::Int(0, None));
        let ty_id = self.p.id();
        self.push(
            out,
            SK::Let {
                var: true,
                name: name.clone(),
                ty: Some(i32t.clone()),
                ty_id,
                init: Some(zero),
            },
        );
        let k = self.rng.range(1, 3) as u64;
        let c = self.mk(i32t.clone(), EK::Local(name.clone()));
        let lim = self.mk(i32t.clone(), EK::Int(k, None));
        let cond = self.mk(
            Ty::Prim(Prim::Bool),
            EK::Binary(BinOp::Lt, Box::new(c), Box::new(lim)),
        );
        let mut body = self.block_of(cx, d, true, Vec::new());
        let l = self.mk(i32t.clone(), EK::Local(name.clone()));
        let one = self.mk(i32t.clone(), EK::Int(1, None));
        let l2 = self.mk(i32t.clone(), EK::Local(name));
        let sum = self.mk(i32t, EK::Binary(BinOp::Add, Box::new(l2), Box::new(one)));
        body.stmts.insert(
            0,
            Stmt {
                id: self.p.id(),
                kind: SK::Assign(l, AssignOp::Set, sum),
            },
        );
        self.push(out, SK::While { cond, body });
    }

    fn s_defer(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>) {
        // A deferred body is a unit call over literals only.
        let cands: Vec<usize> = (0..self.calls.len())
            .filter(|&i| {
                let c = &self.calls[i];
                c.raises.is_none()
                    && c.recv.is_none()
                    && !c.is_unsafe
                    && c.vars.is_empty()
                    && c.ret == Ty::Unit
                    && c.params.iter().all(|(cv, _, t)| {
                        *cv == Conv::Let && self.p.is_copy(t, &cx.bounds) && !has_param(t)
                    })
            })
            .collect();
        if cands.is_empty() {
            return;
        }
        let c = self.calls[cands[self.rng.below(cands.len())]].clone();
        let mut args = Vec::new();
        for (_, _, t) in &c.params {
            let e = self.closed_leaf(t);
            args.push(Arg {
                id: self.p.id(),
                label: None,
                marker: Marker::None,
                e,
            });
        }
        let call = Call {
            callee: c.path.clone(),
            sig: c.sig(),
            targs: Vec::new(),
            args,
            flow: Flow::Plain,
        };
        let e = self.mk(Ty::Unit, EK::Call(call));
        let st = Stmt {
            id: self.p.id(),
            kind: SK::Expr(e),
        };
        let body = Block {
            id: self.p.id(),
            stmts: vec![st],
            tail: None,
        };
        // `errdefer` is the rarer form (it needs a raising fn), so a raising
        // fn takes it most of the time to keep it above the census's 1%.
        let err = cx.raises.is_some() && self.rng.chance(4, 5);
        self.push(out, SK::Defer { err, body });
    }

    /// A leaf with no locals in scope (for a deferred body).
    fn closed_leaf(&mut self, t: &Ty) -> Expr {
        let mut cx = FnCx::new(None);
        self.leaf(&mut cx, t, Mode::Check)
    }

    fn s_raise(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>) {
        let Some(Ty::Adt(en, _)) = cx.raises.clone() else {
            return;
        };
        let ety = Ty::adt(&en);
        let vs = self.p.enum_variants(&ety).unwrap_or_default();
        let v = vs[self.rng.below(vs.len())].clone();
        let cond = self.expr(cx, &Ty::Prim(Prim::Bool), Mode::Synth, 1);
        let val = self.variant_expr(cx, &ety, &en, &v, Mode::Check, 1, false);
        let raise = Stmt {
            id: self.p.id(),
            kind: SK::Raise(val),
        };
        let then = Block {
            id: self.p.id(),
            stmts: vec![raise],
            tail: None,
        };
        self.push(
            out,
            SK::If {
                cond,
                then,
                els: None,
            },
        );
    }

    /// `let v: R = raising(args)?;` / `... else |e| { default };`
    fn s_try(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>, _d: u32) {
        if cx.in_defer {
            return;
        }
        let cands: Vec<usize> = (0..self.calls.len())
            .filter(|&i| {
                let c = &self.calls[i];
                c.raises.is_some() && c.kind != CKind::Method && c.vars.is_empty()
            })
            .collect();
        if cands.is_empty() {
            return;
        }
        let c = self.calls[cands[self.rng.below(cands.len())]].clone();
        let goal = c.ret.clone();
        let Some(e) = self.build_raising(cx, &c, &goal, 2) else {
            return;
        };
        if goal == Ty::Unit {
            self.push(out, SK::Expr(e));
        } else if self.is_copy_in(cx, &goal) {
            let name = cx.fresh("v");
            let ty_id = self.p.id();
            self.push(
                out,
                SK::Let {
                    var: false,
                    name: name.clone(),
                    ty: Some(goal.clone()),
                    ty_id,
                    init: Some(e),
                },
            );
            cx.locals.push(Local {
                name,
                ty: goal,
                mutable: false,
                conv: None,
                moved: false,
                frame: cx.frame,
            });
        } else {
            self.push(out, SK::Expr(e));
        }
    }

    fn s_loop_exit(&mut self, cx: &mut FnCx, out: &mut Vec<Stmt>) {
        let cond = self.expr(cx, &Ty::Prim(Prim::Bool), Mode::Synth, 1);
        let exit = Stmt {
            id: self.p.id(),
            kind: if self.rng.chance(1, 2) {
                SK::Break
            } else {
                SK::Continue
            },
        };
        let then = Block {
            id: self.p.id(),
            stmts: vec![exit],
            tail: None,
        };
        self.push(
            out,
            SK::If {
                cond,
                then,
                els: None,
            },
        );
    }
}

fn mode_for_args(mode: Mode, _c: &Callable) -> Mode {
    mode
}

/// Whether the variant `v` of enum `en` mentions the enum's type parameter in
/// its payload (so a SYNTH use of the variant determines it).
fn variant_mentions_param(p: &Program, en: &str, v: &str) -> bool {
    let Some(e) = p.enum_decl(en) else {
        return false;
    };
    e.variants
        .iter()
        .find(|x| x.name == v)
        .is_some_and(|x| match &x.shape {
            VShape::Unit => false,
            VShape::Tuple(ts) => ts.iter().any(has_param),
            VShape::Record(fs) => fs.iter().any(|f| has_param(&f.ty)),
        })
}
