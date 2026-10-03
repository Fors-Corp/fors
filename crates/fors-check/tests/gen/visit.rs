//! Traversal of a [`Program`] for the mutation engine and the minimiser. One
//! pre-order walker drives every hook, so "count the matches, then act on the
//! k-th" (the way a mutation picks a site) is two runs of the same walk.

use crate::ast::*;
use crate::rng::Rng;

/// Where in the program a node sits.
#[derive(Clone, Debug, Default)]
pub struct Ctx {
    pub in_trait: bool,
    pub ret: Option<Ty>,
    pub raises: Option<Ty>,
    pub attrs: Vec<String>,
    pub params: Vec<(Conv, String, Ty)>,
    pub in_defer: bool,
    pub in_loop: bool,
    pub in_handler: bool,
    pub block_depth: u32,
}

/// How an expression is used, when that use is a CHECK position with a
/// known expected type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Slot {
    LetInit,
    Return,
    Arg,
    FieldInit,
    AssignRhs,
    BinRhs,
}

type Fx<'a> = &'a mut dyn FnMut(&mut Expr, &Ctx);
type Fs<'a> = &'a mut dyn FnMut(&mut Stmt, &Ctx);
type Fb<'a> = &'a mut dyn FnMut(&mut Block, &Ctx);
type Fl<'a> = &'a mut dyn FnMut(&mut Expr, Slot, &Ty, &Ctx);
type Fp<'a> = &'a mut dyn FnMut(&mut Pat, &Ctx);
type Fa<'a> = &'a mut dyn FnMut(&mut Vec<Arm>, &Ty, Id, &Ctx);
type Ff<'a> = &'a mut dyn FnMut(&mut FnDecl, &Ctx);

/// The hooks a walk calls; unset ones are skipped.
#[derive(Default)]
pub struct Hooks<'a> {
    pub expr: Option<Fx<'a>>,
    pub stmt: Option<Fs<'a>>,
    pub block: Option<Fb<'a>>,
    pub slot: Option<Fl<'a>>,
    pub pat: Option<Fp<'a>>,
    /// A `match`'s arm list with the scrutinee's type.
    pub arms: Option<Fa<'a>>,
    pub fn_decl: Option<Ff<'a>>,
}

/// Walks the body of one function declaration on its own.
pub fn walk_fn_body(f: &mut FnDecl, h: &mut Hooks) {
    let cx = fn_ctx(f, false);
    if let Some(b) = f.body.as_mut() {
        walk_block(b, &cx, h, Some((f.ret.clone(), Slot::Return)));
    }
}

pub fn walk(p: &mut Program, h: &mut Hooks) {
    for i in 0..p.items.len() {
        let mut item = std::mem::replace(
            &mut p.items[i],
            Item::Raw {
                id: 0,
                text: String::new(),
            },
        );
        match &mut item {
            Item::Fn(f) => walk_fn(f, false, h),
            Item::Impl(d) => {
                for m in &mut d.methods {
                    walk_fn(m, false, h);
                }
            }
            Item::Trait(t) => {
                for m in &mut t.methods {
                    walk_fn(m, true, h);
                }
            }
            Item::Const(c) => {
                walk_expr(&mut c.value, &Ctx::default(), h);
            }
            _ => {}
        }
        p.items[i] = item;
    }
}

fn fn_ctx(f: &FnDecl, in_trait: bool) -> Ctx {
    Ctx {
        in_trait,
        ret: Some(f.ret.clone()),
        raises: f.raises.clone(),
        attrs: f.attrs.clone(),
        params: f
            .params
            .iter()
            .map(|p| (p.conv, p.name.clone(), p.ty.clone().unwrap_or(Ty::Unit)))
            .collect(),
        ..Default::default()
    }
}

fn walk_fn(f: &mut FnDecl, in_trait: bool, h: &mut Hooks) {
    let cx = fn_ctx(f, in_trait);
    if let Some(k) = h.fn_decl.as_mut() {
        k(f, &cx);
    }
    if let Some(b) = f.body.as_mut() {
        walk_block(b, &cx, h, Some((f.ret.clone(), Slot::Return)));
    }
}

/// `tail` is the type (and slot) the block's tail expression is checked
/// against, when that is known.
fn walk_block(b: &mut Block, cx: &Ctx, h: &mut Hooks, tail: Option<(Ty, Slot)>) {
    let mut cx = cx.clone();
    cx.block_depth += 1;
    if let Some(k) = h.block.as_mut() {
        k(b, &cx);
    }
    for s in &mut b.stmts {
        walk_stmt(s, &cx, h);
    }
    if let Some(t) = b.tail.as_mut() {
        if let (Some((ty, slot)), Some(k)) = (tail, h.slot.as_mut()) {
            k(t, slot, &ty, &cx);
        }
        walk_expr(t, &cx, h);
    }
}

fn walk_stmt(s: &mut Stmt, cx: &Ctx, h: &mut Hooks) {
    if let Some(k) = h.stmt.as_mut() {
        k(s, cx);
    }
    match &mut s.kind {
        SK::Let { ty, init, .. } => {
            if let Some(e) = init {
                if let (Some(t), Some(k)) = (ty.clone(), h.slot.as_mut()) {
                    k(e, Slot::LetInit, &t, cx);
                }
                walk_expr(e, cx, h);
            }
        }
        SK::Assign(place, _, rhs) => {
            walk_expr(place, cx, h);
            if let Some(k) = h.slot.as_mut() {
                let t = place.ty.clone();
                k(rhs, Slot::AssignRhs, &t, cx);
            }
            walk_expr(rhs, cx, h);
        }
        SK::Expr(e) => walk_expr(e, cx, h),
        SK::If { cond, then, els } => {
            walk_expr(cond, cx, h);
            walk_block(then, cx, h, None);
            if let Some(e) = els {
                walk_block(e, cx, h, None);
            }
        }
        SK::Match { scrut, arms } => {
            walk_expr(scrut, cx, h);
            walk_arms(arms, &scrut.ty.clone(), s.id, cx, h, None);
        }
        SK::For { iter, body, .. } => {
            walk_expr(iter, cx, h);
            let mut c = cx.clone();
            c.in_loop = true;
            walk_block(body, &c, h, None);
        }
        SK::While { cond, body } => {
            walk_expr(cond, cx, h);
            let mut c = cx.clone();
            c.in_loop = true;
            walk_block(body, &c, h, None);
        }
        SK::Return(e) => {
            if let Some(e) = e {
                if let (Some(rt), Some(k)) = (cx.ret.clone(), h.slot.as_mut()) {
                    k(e, Slot::Return, &rt, cx);
                }
                walk_expr(e, cx, h);
            }
        }
        SK::Raise(e) => walk_expr(e, cx, h),
        SK::Defer { body, .. } => {
            let mut c = cx.clone();
            c.in_defer = true;
            walk_block(body, &c, h, None);
        }
        SK::Break | SK::Continue | SK::Raw(_) => {}
    }
}

fn walk_arms(
    arms: &mut Vec<Arm>,
    scrut_ty: &Ty,
    id: Id,
    cx: &Ctx,
    h: &mut Hooks,
    tail: Option<(Ty, Slot)>,
) {
    if let Some(k) = h.arms.as_mut() {
        k(arms, scrut_ty, id, cx);
    }
    for a in arms.iter_mut() {
        if let Some(k) = h.pat.as_mut() {
            walk_pat(&mut a.pat, cx, k);
        }
        match &mut a.body {
            ArmBody::Expr(e) => {
                if let (Some((ty, slot)), Some(k)) = (tail.clone(), h.slot.as_mut()) {
                    k(e, slot, &ty, cx);
                }
                walk_expr(e, cx, h);
            }
            ArmBody::Block(b) => walk_block(b, cx, h, None),
        }
    }
}

fn walk_pat(p: &mut Pat, cx: &Ctx, k: &mut dyn FnMut(&mut Pat, &Ctx)) {
    k(p, cx);
    match &mut p.kind {
        PK::Variant { sub, .. } => match sub {
            PSub::Unit => {}
            PSub::Tuple(ps) => {
                for q in ps {
                    walk_pat(q, cx, k);
                }
            }
            PSub::Rec(fs) => {
                for (_, q) in fs {
                    walk_pat(q, cx, k);
                }
            }
        },
        PK::Some(q) => walk_pat(q, cx, k),
        _ => {}
    }
}

fn walk_call(c: &mut Call, cx: &Ctx, h: &mut Hooks) {
    let generic = !c.sig.generics.is_empty();
    for (i, a) in c.args.iter_mut().enumerate() {
        if !generic
            && a.marker == Marker::None
            && let Some((_, _, t)) = c.sig.params.get(i)
            && !crate::types::has_param(t)
            && let Some(k) = h.slot.as_mut()
        {
            k(&mut a.e, Slot::Arg, t, cx);
        }
        walk_expr(&mut a.e, cx, h);
    }
    if let Flow::Handler { block, .. } = &mut c.flow {
        let mut hc = cx.clone();
        hc.in_handler = true;
        walk_block(block, &hc, h, Some((c.sig.ret.clone(), Slot::Return)));
    }
}

pub fn walk_expr(e: &mut Expr, cx: &Ctx, h: &mut Hooks) {
    if let Some(k) = h.expr.as_mut() {
        k(e, cx);
    }
    let ety = e.ty.clone();
    let eid = e.id;
    match &mut e.kind {
        EK::Field(r, _) => walk_expr(r, cx, h),
        EK::Index(r, i) => {
            walk_expr(r, cx, h);
            walk_expr(i, cx, h);
        }
        EK::Call(c) => walk_call(c, cx, h),
        EK::Method(r, c) => {
            walk_expr(r, cx, h);
            walk_call(c, cx, h);
        }
        EK::StructLit { fields, .. } => {
            let plain = matches!(&ety, Ty::Adt(_, a) if a.is_empty());
            for (_, v) in fields.iter_mut() {
                if plain
                    && !crate::types::has_param(&v.ty)
                    && let Some(k) = h.slot.as_mut()
                {
                    let t = v.ty.clone();
                    k(v, Slot::FieldInit, &t, cx);
                }
                walk_expr(v, cx, h);
            }
        }
        EK::Variant { payload, .. } => match payload {
            VPayload::Unit => {}
            VPayload::Tuple(es) => {
                for v in es {
                    walk_expr(v, cx, h);
                }
            }
            VPayload::Rec(fs) => {
                for (_, v) in fs {
                    walk_expr(v, cx, h);
                }
            }
        },
        EK::Some(v) | EK::Move(v) | EK::Unary(_, v) | EK::Cast(v, _) => walk_expr(v, cx, h),
        EK::Tuple(es) | EK::Array(es) => {
            for v in es {
                walk_expr(v, cx, h);
            }
        }
        EK::Binary(op, a, b) => {
            walk_expr(a, cx, h);
            if !matches!(op, BinOp::And | BinOp::Or | BinOp::Range)
                && let Some(k) = h.slot.as_mut()
            {
                let t = a.ty.clone();
                k(b, Slot::BinRhs, &t, cx);
            }
            walk_expr(b, cx, h);
        }
        EK::If(c, t, f) => {
            walk_expr(c, cx, h);
            walk_block(t, cx, h, None);
            walk_block(f, cx, h, None);
        }
        EK::Match(s, arms) => {
            walk_expr(s, cx, h);
            let st = s.ty.clone();
            walk_arms(arms, &st, eid, cx, h, None);
        }
        EK::Int(..)
        | EK::Float(..)
        | EK::Bool(_)
        | EK::UnitLit
        | EK::Local(_)
        | EK::Const(_)
        | EK::None
        | EK::Raw(_) => {}
    }
}

// ------------------------------------------------------------- the pickers

/// Counts the expressions `pred` accepts, then rewrites a random one.
pub fn pick_expr<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Expr, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Expr, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            expr: Some(&mut |e, c| {
                if pred(e, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            expr: Some(&mut |e, c| {
                if pred(e, c) {
                    if i == k && out.is_none() {
                        out = apply(e, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn pick_stmt<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Stmt, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Stmt, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            stmt: Some(&mut |s, c| {
                if pred(s, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            stmt: Some(&mut |s, c| {
                if pred(s, c) {
                    if i == k && out.is_none() {
                        out = apply(s, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn pick_block<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Block, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Block, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            block: Some(&mut |b, c| {
                if pred(b, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            block: Some(&mut |b, c| {
                if pred(b, c) {
                    if i == k && out.is_none() {
                        out = apply(b, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

/// A CHECK-position expression with a known expected type.
pub fn pick_slot<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Expr, Slot, &Ty, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Expr, Slot, &Ty, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            slot: Some(&mut |e, s, t, c| {
                if pred(e, s, t, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            slot: Some(&mut |e, s, t, c| {
                if pred(e, s, t, c) {
                    if i == k && out.is_none() {
                        out = apply(e, s, t, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn pick_fn<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&FnDecl, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut FnDecl, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            fn_decl: Some(&mut |f, c| {
                if pred(f, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            fn_decl: Some(&mut |f, c| {
                if pred(f, c) {
                    if i == k && out.is_none() {
                        out = apply(f, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn pick_pat<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Pat, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Pat, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            pat: Some(&mut |q, c| {
                if pred(q, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            pat: Some(&mut |q, c| {
                if pred(q, c) {
                    if i == k && out.is_none() {
                        out = apply(q, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

/// A `match`'s arm list (statement or expression form).
pub fn pick_arms<R>(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Vec<Arm>, &Ty, Id, &Ctx) -> bool,
    apply: &mut dyn FnMut(&mut Vec<Arm>, &Ty, Id, &Ctx, &mut Rng) -> Option<R>,
) -> Option<R> {
    let mut n = 0usize;
    walk(
        p,
        &mut Hooks {
            arms: Some(&mut |a, t, i, c| {
                if pred(a, t, i, c) {
                    n += 1;
                }
            }),
            ..Default::default()
        },
    );
    if n == 0 {
        return None;
    }
    let k = rng.below(n);
    let mut i = 0usize;
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            arms: Some(&mut |a, t, mid, c| {
                if pred(a, t, mid, c) {
                    if i == k && out.is_none() {
                        out = apply(a, t, mid, c, rng);
                    }
                    i += 1;
                }
            }),
            ..Default::default()
        },
    );
    out
}

// ------------------------------------------------------------ reading only

// ------------------------------------------------- pick-by-id conveniences

/// A random expression `pred` accepts: its id and context.
pub fn expr_id(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Expr, &Ctx) -> bool,
) -> Option<(Id, Ctx)> {
    pick_expr(p, rng, pred, &mut |e, c, _| Some((e.id, c.clone())))
}

pub fn stmt_id(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Stmt, &Ctx) -> bool,
) -> Option<(Id, Ctx)> {
    pick_stmt(p, rng, pred, &mut |s, c, _| Some((s.id, c.clone())))
}

pub fn block_id(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&Block, &Ctx) -> bool,
) -> Option<(Id, Ctx)> {
    pick_block(p, rng, pred, &mut |b, c, _| Some((b.id, c.clone())))
}

pub fn fn_id(
    p: &mut Program,
    rng: &mut Rng,
    pred: &mut dyn FnMut(&FnDecl, &Ctx) -> bool,
) -> Option<(Id, Ctx)> {
    pick_fn(p, rng, pred, &mut |f, c, _| Some((f.id, c.clone())))
}
