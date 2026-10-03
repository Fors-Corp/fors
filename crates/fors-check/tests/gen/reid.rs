//! Cloning support: shifts every node id of an item by a constant, so a
//! copy of a declaration (a duplicate impl, say) has ids of its own.

use crate::ast::*;

pub fn shift_item(it: &mut Item, d: Id) {
    match it {
        Item::Struct(s) => {
            s.id += d;
            gparams(&mut s.generics, d);
        }
        Item::Enum(e) => {
            e.id += d;
            gparams(&mut e.generics, d);
        }
        Item::Trait(t) => {
            t.id += d;
            for m in &mut t.methods {
                shift_fn(m, d);
            }
        }
        Item::Impl(i) => {
            i.id += d;
            i.head_id += d;
            gparams(&mut i.generics, d);
            for m in &mut i.methods {
                shift_fn(m, d);
            }
        }
        Item::Fn(f) => shift_fn(f, d),
        Item::Const(c) => {
            c.id += d;
            shift_expr(&mut c.value, d);
        }
        Item::Raw { id, .. } => *id += d,
    }
}

fn gparams(gs: &mut [GParam], d: Id) {
    for g in gs {
        g.id += d;
    }
}

pub fn shift_fn(f: &mut FnDecl, d: Id) {
    f.id += d;
    f.name_id += d;
    f.sig_id += d;
    f.ret_id += d;
    gparams(&mut f.generics, d);
    for p in &mut f.params {
        p.id += d;
        p.ty_id += d;
    }
    if let Some(b) = f.body.as_mut() {
        shift_block(b, d);
    }
}

pub fn shift_block(b: &mut Block, d: Id) {
    b.id += d;
    for s in &mut b.stmts {
        shift_stmt(s, d);
    }
    if let Some(t) = b.tail.as_mut() {
        shift_expr(t, d);
    }
}

pub fn shift_stmt(s: &mut Stmt, d: Id) {
    s.id += d;
    match &mut s.kind {
        SK::Let { ty_id, init, .. } => {
            *ty_id += d;
            if let Some(e) = init {
                shift_expr(e, d);
            }
        }
        SK::Assign(a, _, b) => {
            shift_expr(a, d);
            shift_expr(b, d);
        }
        SK::Expr(e) | SK::Raise(e) => shift_expr(e, d),
        SK::If { cond, then, els } => {
            shift_expr(cond, d);
            shift_block(then, d);
            if let Some(e) = els {
                shift_block(e, d);
            }
        }
        SK::Match { scrut, arms } => {
            shift_expr(scrut, d);
            shift_arms(arms, d);
        }
        SK::For { iter, body, .. } => {
            shift_expr(iter, d);
            shift_block(body, d);
        }
        SK::While { cond, body } => {
            shift_expr(cond, d);
            shift_block(body, d);
        }
        SK::Return(e) => {
            if let Some(e) = e {
                shift_expr(e, d);
            }
        }
        SK::Defer { body, .. } => shift_block(body, d),
        SK::Break | SK::Continue | SK::Raw(_) => {}
    }
}

fn shift_arms(arms: &mut [Arm], d: Id) {
    for a in arms {
        a.id += d;
        shift_pat(&mut a.pat, d);
        match &mut a.body {
            ArmBody::Expr(e) => shift_expr(e, d),
            ArmBody::Block(b) => shift_block(b, d),
        }
    }
}

fn shift_pat(p: &mut Pat, d: Id) {
    p.id += d;
    match &mut p.kind {
        PK::Variant { sub, .. } => match sub {
            PSub::Unit => {}
            PSub::Tuple(ps) => {
                for q in ps {
                    shift_pat(q, d);
                }
            }
            PSub::Rec(fs) => {
                for (_, q) in fs {
                    shift_pat(q, d);
                }
            }
        },
        PK::Some(q) => shift_pat(q, d),
        _ => {}
    }
}

fn shift_call(c: &mut Call, d: Id) {
    gparams(&mut c.sig.generics, d);
    for a in &mut c.args {
        a.id += d;
        shift_expr(&mut a.e, d);
    }
    if let Flow::Handler { block, .. } = &mut c.flow {
        shift_block(block, d);
    }
}

pub fn shift_expr(e: &mut Expr, d: Id) {
    e.id += d;
    match &mut e.kind {
        EK::Field(r, _) => shift_expr(r, d),
        EK::Index(a, b) | EK::Binary(_, a, b) => {
            shift_expr(a, d);
            shift_expr(b, d);
        }
        EK::Call(c) => shift_call(c, d),
        EK::Method(r, c) => {
            shift_expr(r, d);
            shift_call(c, d);
        }
        EK::StructLit { fields, .. } => {
            for (_, v) in fields {
                shift_expr(v, d);
            }
        }
        EK::Variant { payload, .. } => match payload {
            VPayload::Unit => {}
            VPayload::Tuple(es) => {
                for v in es {
                    shift_expr(v, d);
                }
            }
            VPayload::Rec(fs) => {
                for (_, v) in fs {
                    shift_expr(v, d);
                }
            }
        },
        EK::Some(v) | EK::Move(v) | EK::Unary(_, v) | EK::Cast(v, _) => shift_expr(v, d),
        EK::Tuple(es) | EK::Array(es) => {
            for v in es {
                shift_expr(v, d);
            }
        }
        EK::If(c, t, f) => {
            shift_expr(c, d);
            shift_block(t, d);
            shift_block(f, d);
        }
        EK::Match(s, arms) => {
            shift_expr(s, d);
            shift_arms(arms, d);
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

/// Reserves ids for a copy of something whose ids are all below `next_id`.
fn reserve(p: &mut Program) -> Id {
    let d = p.next_id;
    p.next_id = p.next_id.saturating_add(p.next_id) + 1;
    d
}

/// A copy of `f` whose ids are all fresh in `p`.
pub fn fresh_fn(p: &mut Program, f: &FnDecl) -> FnDecl {
    let mut c = f.clone();
    let d = reserve(p);
    shift_fn(&mut c, d);
    c
}

/// A copy of `e` whose ids are all fresh in `p`.
pub fn fresh_expr(p: &mut Program, e: &Expr) -> Expr {
    let mut c = e.clone();
    let d = reserve(p);
    shift_expr(&mut c, d);
    c
}

/// A copy of `it` whose ids are all fresh in `p`.
pub fn clone_fresh(p: &mut Program, it: &Item) -> Item {
    let mut c = it.clone();
    let d = reserve(p);
    shift_item(&mut c, d);
    c
}
