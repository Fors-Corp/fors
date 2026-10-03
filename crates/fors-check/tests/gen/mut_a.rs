//! Mutations of calls, names, control flow, ownership and numerics.

use crate::ast::*;
use crate::body::Mode;
use crate::mutate::*;
use crate::rng::Rng;
use crate::types::*;
use crate::visit::*;

fn is_numeric_method(n: &str) -> bool {
    n.starts_with("wrap_")
        || n.starts_with("sat_")
        || n.starts_with("unchecked_")
        || n.starts_with("trunc_as")
}

fn user_call(c: &Call) -> bool {
    !is_numeric_method(&c.callee)
}

/// Inserts the statements `make` builds into a block `ok` accepts, before
/// the block's first terminating statement; the result is the id of the
/// `target`-th inserted statement.
pub fn insert_stmts(
    p: &mut Program,
    rng: &mut Rng,
    ok: &mut dyn FnMut(&Block, &Ctx) -> bool,
    make: &mut dyn FnMut(&mut Program, &Ctx) -> Option<(Vec<Stmt>, usize)>,
) -> Option<Id> {
    let (bid, ctx) = block_id(p, rng, ok)?;
    let (sts, target) = make(p, &ctx)?;
    let tid = sts.get(target)?.id;
    let r = rng.next();
    edit_block(p, bid, move |b| {
        let end = b
            .stmts
            .iter()
            .position(|s| {
                matches!(
                    s.kind,
                    SK::Return(_) | SK::Raise(_) | SK::Break | SK::Continue
                )
            })
            .unwrap_or(b.stmts.len());
        let at = (r as usize) % (end + 1);
        for (k, st) in sts.into_iter().enumerate() {
            b.stmts.insert(at + k, st);
        }
    })?;
    Some(tid)
}

/// One statement, anywhere a function body's top block is.
pub fn insert_in_body(
    p: &mut Program,
    rng: &mut Rng,
    ok: &mut dyn FnMut(&Block, &Ctx) -> bool,
    make: &mut dyn FnMut(&mut Program, &Ctx) -> Option<Stmt>,
) -> Option<Id> {
    insert_stmts(
        p,
        rng,
        &mut |b, c| c.block_depth == 1 && ok(b, c),
        &mut |p, c| make(p, c).map(|s| (vec![s], 0)),
    )
}

pub fn raw_stmt(p: &mut Program, text: String) -> Stmt {
    Stmt {
        id: p.id(),
        kind: SK::Raw(text),
    }
}

pub fn push_raw_item(p: &mut Program, text: String) -> Id {
    let id = p.id();
    p.items.push(Item::Raw { id, text });
    id
}

fn lit_arg(p: &mut Program, rng: &mut Rng, ty: &Ty) -> Option<Arg> {
    let e = closed(p, rng, ty, Mode::Synth)?;
    Some(Arg {
        id: p.id(),
        label: None,
        marker: Marker::None,
        e,
    })
}

// ----------------------------------------------------------------- calls

/// R39 (T0039): a wrong argument count. `variant` 0 drops the last argument,
/// 1 adds one.
pub fn m_arg_count(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| match call_of(e) {
        Some(c) => {
            user_call(c) && matches!(c.flow, Flow::Plain) && (variant == 1 || !c.args.is_empty())
        }
        None => false,
    })?;
    let extra = if variant == 1 {
        Some(lit_arg(p, rng, &Ty::Prim(Prim::I32))?)
    } else {
        None
    };
    edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        for a in &mut c.args {
            a.label = None;
        }
        match extra {
            Some(x) => c.args.push(x),
            None => {
                c.args.pop();
            }
        }
        Some(())
    })??;
    ap(
        id,
        if variant == 1 {
            "an extra argument"
        } else {
            "a missing argument"
        },
    )
}

/// R37 (T0037): a named argument whose label is not its parameter's name.
pub fn m_arg_label(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| match call_of(e) {
        Some(c) => user_call(c) && !c.args.is_empty() && matches!(c.flow, Flow::Plain),
        None => false,
    })?;
    let k = rng.next() as usize;
    let aid = edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        let i = k % c.args.len();
        // Either every argument is labelled right except one, or none were.
        for (a, (_, n, _)) in c.args.iter_mut().zip(&c.sig.params) {
            a.label = Some(n.clone());
        }
        c.args[i].label = Some("zq".to_string());
        Some(c.args[i].id)
    })??;
    ap(
        aid,
        "an argument labelled with a name the parameter does not have",
    )
}

/// ch01 R2 (O0002): a call-site convention marker wrong. `variant` 0 drops
/// `&`, 1 drops `move`, 2 writes `&out x` for an `inout` parameter.
pub fn m_marker_missing(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let has = |a: &Arg| {
        if variant == 1 {
            matches!(a.e.kind, EK::Move(_)) && a.marker == Marker::None
        } else {
            a.marker == Marker::Inout
        }
    };
    let (id, _) = expr_id(p, rng, &mut |e, _| match call_of(e) {
        Some(c) => user_call(c) && c.args.iter().any(has),
        None => false,
    })?;
    let aid = edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        let a = c.args.iter_mut().find(|a| has(a))?;
        match variant {
            0 => a.marker = Marker::None,
            2 => a.marker = Marker::Set,
            _ => {
                let EK::Move(inner) = std::mem::replace(&mut a.e.kind, EK::UnitLit) else {
                    return None;
                };
                a.e = *inner;
            }
        }
        Some(a.id)
    })??;
    ap(
        aid,
        [
            "`&` removed",
            "`move` removed",
            "`&out` for an inout parameter",
        ][variant.min(2) as usize],
    )
}

/// R12 (T0012): a generic call whose argument type does not satisfy the
/// parameter's bound.
pub fn m_bound_unsatisfied(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    // A call of a function with one type parameter, every parameter of which
    // is either `T` or closed.
    let (id, _) = expr_id(p, rng, &mut |e, _| match &e.kind {
        EK::Call(c) => {
            let t = Ty::Param(
                c.sig
                    .generics
                    .first()
                    .map(|g| g.name.clone())
                    .unwrap_or_default(),
            );
            c.sig.generics.len() == 1
                && matches!(c.flow, Flow::Plain)
                && !c.args.is_empty()
                && c.sig
                    .params
                    .iter()
                    .all(|(_, _, pt)| !has_param(pt) || *pt == t)
        }
        _ => false,
    })?;
    // The bounds of the call's parameter, and the types that break one.
    let (bounds, tname) = edit_expr(p, id, |e| {
        let EK::Call(c) = &e.kind else { return None };
        Some((
            c.sig.generics[0].bounds.clone(),
            c.sig.generics[0].name.clone(),
        ))
    })??;
    let mut cands: Vec<Ty> = vec![
        Ty::Prim(Prim::Bool),
        Ty::Prim(Prim::I32),
        Ty::Prim(Prim::F64),
    ];
    for it in &p.items {
        if let Item::Struct(s) = it
            && s.generics.is_empty()
        {
            cands.push(Ty::adt(&s.name));
        }
    }
    let none = Bounds::new();
    let bad: Vec<Ty> = cands
        .into_iter()
        .filter(|t| bounds.iter().any(|b| !p.satisfies(t, b, &none)))
        .collect();
    if bad.is_empty() {
        return None;
    }
    let x = bad[rng.below(bad.len())].clone();
    // A closed argument for every parameter written `T`, in place.
    let tparam = Ty::Param(tname);
    let slots: Vec<bool> = edit_expr(p, id, |e| {
        call_of(e).map(|c| {
            c.sig
                .params
                .iter()
                .map(|(_, _, pt)| *pt == tparam)
                .collect()
        })
    })??;
    let mut news: Vec<Option<Expr>> = Vec::new();
    for &is_t in &slots {
        news.push(if is_t {
            Some(closed(p, rng, &x, Mode::Synth)?)
        } else {
            None
        });
    }
    edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        for (a, n) in c.args.iter_mut().zip(news) {
            if let Some(n) = n {
                a.e = n;
            }
        }
        // `T` is also inferred from the expected result type in a CHECK
        // position, which would turn the bad argument into a T0026: name it.
        if !c.targs.is_empty() || has_param(&c.sig.ret) {
            c.targs = vec![x.clone()];
        }
        Some(())
    })??;
    ap(
        id,
        format!(
            "`{}` for a parameter bounded {}",
            ty_name(&x),
            bounds.join(" + ")
        ),
    )
}

/// R43 (T0043): a method name that nothing declares. `variant` 1 mistypes a
/// numeric method (R43 reads the numeric prelude impls like any other).
pub fn m_method_name(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| match &e.kind {
        EK::Method(_, c) => {
            matches!(c.flow, Flow::Plain)
                && if variant == 1 {
                    c.callee.starts_with("wrap_") || c.callee.starts_with("sat_")
                } else {
                    user_call(c)
                }
        }
        _ => false,
    })?;
    edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        c.callee = if variant == 1 {
            format!("{}x", c.callee)
        } else {
            "zzmethod".to_string()
        };
        Some(())
    })??;
    ap(id, "a method that is not declared")
}

/// R42 (T0042): a field the type does not have.
pub fn m_field_name(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(
        p,
        rng,
        &mut |e, _| matches!(&e.kind, EK::Field(r, _) if matches!(r.ty, Ty::Adt(..))),
    )?;
    edit_expr(p, id, |e| {
        if let EK::Field(_, n) = &mut e.kind {
            *n = "zzfield".to_string();
        }
    })?;
    ap(id, "a field that is not declared")
}

/// R39 (T0039): explicit type arguments of the wrong count.
pub fn m_targ_count(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(
        p,
        rng,
        &mut |e, _| matches!(&e.kind, EK::Call(c) if !c.sig.generics.is_empty() && matches!(c.flow, Flow::Plain)),
    )?;
    edit_expr(p, id, |e| {
        let c = call_of_mut(e)?;
        c.targs = vec![Ty::Prim(Prim::I32); c.sig.generics.len() + 1];
        Some(())
    })??;
    ap(id, "one explicit type argument too many")
}

// -------------------------------------------------------- control flow

/// R30 (T0030): a condition that is not `bool`. `variant` 0 an `if`
/// statement, 1 a `while`, 2 an `if` expression.
pub fn m_condition(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let bad = closed(p, rng, &Ty::Prim(Prim::I32), Mode::Synth)?;
    let target = bad.id;
    let mut bad = Some(bad);
    if variant == 2 {
        let (id, _) = expr_id(p, rng, &mut |e, _| matches!(e.kind, EK::If(..)))?;
        edit_expr(p, id, |e| {
            if let EK::If(c, ..) = &mut e.kind {
                **c = bad.take()?;
            }
            Some(())
        })??;
        return ap(target, "an `if` expression whose condition is an integer");
    }
    let (id, _) = stmt_id(p, rng, &mut |s, _| match &s.kind {
        SK::If { .. } => variant == 0,
        SK::While { .. } => variant == 1,
        _ => false,
    })?;
    edit_stmt(p, id, |s| match &mut s.kind {
        SK::If { cond, .. } | SK::While { cond, .. } => {
            *cond = bad.take()?;
            Some(())
        }
        _ => None,
    })??;
    ap(target, "a condition that is an integer")
}

/// R30 (T0030): an operand of `and`, `or`, `not` that is not `bool`.
pub fn m_logic_operand(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let bad = closed(p, rng, &Ty::Prim(Prim::I32), Mode::Synth)?;
    let target = bad.id;
    let (id, _) = expr_id(p, rng, &mut |e, _| {
        matches!(
            &e.kind,
            EK::Binary(BinOp::And | BinOp::Or, ..) | EK::Unary(UnOp::Not, _)
        )
    })?;
    let mut bad = Some(bad);
    edit_expr(p, id, |e| match &mut e.kind {
        EK::Binary(_, _, b) => {
            **b = bad.take()?;
            Some(())
        }
        EK::Unary(_, a) => {
            **a = bad.take()?;
            Some(())
        }
        _ => None,
    })??;
    ap(target, "an integer where `bool` is required")
}

/// R31 (T0031): `for` over a value that is not iterable.
pub fn m_for_iter(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let bad = closed(p, rng, &Ty::Prim(Prim::I32), Mode::Synth)?;
    let target = bad.id;
    let (id, _) = stmt_id(p, rng, &mut |s, _| matches!(s.kind, SK::For { .. }))?;
    let mut bad = Some(bad);
    edit_stmt(p, id, |s| {
        if let SK::For { iter, .. } = &mut s.kind {
            *iter = bad.take()?;
        }
        Some(())
    })??;
    ap(target, "`for` over an integer")
}

/// R33 (T0033): `break` / `continue` outside a loop.
pub fn m_break_outside(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let kind = if variant == 0 {
        SK::Break
    } else {
        SK::Continue
    };
    let id = insert_in_body(
        p,
        rng,
        &mut |_, c| !c.in_loop && !c.in_defer,
        &mut |p, _| {
            Some(Stmt {
                id: p.id(),
                kind: kind.clone(),
            })
        },
    )?;
    ap(id, "a loop exit outside any loop")
}

/// R33 (T0033): `let x = die();` where `die` returns `never`.
pub fn m_never_let(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = p.id();
    push_raw_item(p, format!("fn zdie{k}() -> never {{ return zdie{k}(); }}"));
    let id = insert_in_body(p, rng, &mut |_, _| true, &mut |p, _| {
        Some(raw_stmt(p, format!("let znv{k} = zdie{k}();")))
    })?;
    ap(id, "a binding of type never")
}

/// ch01 R23c (T0033): `return` / `raise` / `break` of an enclosing loop inside
/// a deferred body. `variant` 0 `return`, 1 `raise`, 2 `break`. The `defer`
/// is injected, so every function with the exit's context qualifies.
pub fn m_defer_exit(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let id = insert_stmts(
        p,
        rng,
        &mut |_, c| {
            !c.in_defer
                && !c.in_handler
                && match variant {
                    0 => c.ret.as_ref().is_some_and(|t| !has_param(t)),
                    1 => matches!(c.raises, Some(Ty::Adt(..))),
                    _ => c.in_loop,
                }
        },
        &mut |p, c| {
            let exit = match variant {
                0 => {
                    let ret = c.ret.clone()?;
                    let v = if ret == Ty::Unit {
                        None
                    } else {
                        Some(closed(
                            p,
                            &mut Rng::new(p.next_id as u64),
                            &ret,
                            Mode::Check,
                        )?)
                    };
                    SK::Return(v)
                }
                1 => {
                    let Some(Ty::Adt(en, _)) = c.raises.clone() else {
                        return None;
                    };
                    SK::Raise(mk(p, Ty::adt(&en), EK::Raw(format!("{en}.bad"))))
                }
                _ => SK::Break,
            };
            let exit_stmt = Stmt {
                id: p.id(),
                kind: exit,
            };
            let body = Block {
                id: p.id(),
                stmts: vec![exit_stmt],
                tail: None,
            };
            let d = Stmt {
                id: p.id(),
                kind: SK::Defer { err: false, body },
            };
            Some((vec![d], 0))
        },
    )?;
    // The diagnostic sits on the forbidden exit, one level inside the defer.
    let exit = edit_stmt(p, id, |s| match &s.kind {
        SK::Defer { body, .. } => body.stmts.first().map(|x| x.id),
        _ => None,
    })??;
    ap(exit, "a forbidden exit inside a deferred body")
}

/// Declares `struct ZR<k> { a: i32 }` and `fn zsink<k>(sink x: ZR<k>)`: a value
/// that is not `Copyable` and a function that consumes one.
fn resource_kit(p: &mut Program) -> Id {
    let k = p.id();
    push_raw_item(
        p,
        format!("struct ZR{k} {{\n    a: i32,\n}}\n\nfn zsink{k}(sink x: ZR{k}) {{\n}}"),
    );
    k
}

fn new_resource(p: &mut Program, k: Id) -> Stmt {
    raw_stmt(p, format!("let zv{k} = ZR{k} {{ a: 1 }};"))
}

/// ch01 R23b (O0023): an `errdefer` that consumes a value in a function with
/// no error exit.
pub fn m_errdefer_no_error_exit(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = resource_kit(p);
    let id = insert_stmts(
        p,
        rng,
        &mut |_, c| c.raises.is_none() && !c.in_defer && !c.in_handler && c.block_depth == 1,
        &mut |p, _| {
            let v = new_resource(p, k);
            let inner = raw_stmt(p, format!("zsink{k}(move zv{k});"));
            let body = Block {
                id: p.id(),
                stmts: vec![inner],
                tail: None,
            };
            let d = Stmt {
                id: p.id(),
                kind: SK::Defer { err: true, body },
            };
            Some((vec![v, d], 1))
        },
    )?;
    ap(id, "an errdefer with no error exit after it")
}

// ------------------------------------------------------------ ch02: failure

/// ch02 R1 (F0001): `raise` in a function with no `raises`; `variant` 1 a
/// `raise` of the wrong type in one that has it.
pub fn m_raise(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    if variant == 0 {
        let k = p.id();
        push_raw_item(p, format!("enum ZE{k} {{ zbad }}"));
        let id = insert_in_body(
            p,
            rng,
            &mut |_, c| c.raises.is_none() && !c.in_defer,
            &mut |p, _| Some(raw_stmt(p, format!("raise ZE{k}.zbad;"))),
        )?;
        return ap(id, "a raise in a function that does not raise");
    }
    let v = closed(p, rng, &Ty::Prim(Prim::I32), Mode::Synth)?;
    let target = v.id;
    let mut v = Some(v);
    insert_in_body(p, rng, &mut |_, c| c.raises.is_some(), &mut |p, _| {
        Some(Stmt {
            id: p.id(),
            kind: SK::Raise(v.take()?),
        })
    })?;
    ap(target, "a raise of the wrong type")
}

/// ch02 R2 (F0002): `?` on a call that does not raise.
pub fn m_try_nonraising(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, c| match call_of(e) {
        Some(k) => {
            !c.in_defer && user_call(k) && k.sig.raises.is_none() && matches!(k.flow, Flow::Plain)
        }
        None => false,
    })?;
    edit_expr(p, id, |e| {
        call_of_mut(e)?.flow = Flow::Try;
        Some(())
    })??;
    ap(id, "`?` on a call that does not raise")
}

/// ch02 R5 (F0005): an `else |e|` handler on a call that does not raise.
pub fn m_handler_nonraising(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| match call_of(e) {
        Some(c) => {
            user_call(c)
                && c.sig.raises.is_none()
                && matches!(c.flow, Flow::Plain)
                && !has_param(&e.ty)
        }
        None => false,
    })?;
    let ret = edit_expr(p, id, |e| e.ty.clone())?;
    let tail = if ret == Ty::Unit {
        None
    } else {
        Some(Box::new(closed(p, rng, &ret, Mode::Check)?))
    };
    let bid = p.id();
    edit_expr(p, id, move |e| {
        call_of_mut(e)?.flow = Flow::Handler {
            binder: "zerr".to_string(),
            block: Block {
                id: bid,
                stmts: Vec::new(),
                tail,
            },
        };
        Some(())
    })??;
    ap(id, "a handler on a call that does not raise")
}

/// ch02 R1 (F0001): a raising call whose `?` / handler is removed.
pub fn m_raising_unhandled(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| match call_of(e) {
        Some(c) => c.sig.raises.is_some() && !matches!(c.flow, Flow::Plain),
        None => false,
    })?;
    edit_expr(p, id, |e| {
        call_of_mut(e)?.flow = Flow::Plain;
        Some(())
    })??;
    ap(id, "a raising call left unhandled")
}

/// ch02 R3 (F0003): `?` propagates an error type with no `ErrorFrom` path.
pub fn m_error_from(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = p.id();
    push_raw_item(
        p,
        format!("enum ZE{k} {{ zbad }}\nfn zr{k}() raises ZE{k} {{ raise ZE{k}.zbad; }}"),
    );
    let id = insert_in_body(
        p,
        rng,
        &mut |_, c| c.raises.is_some() && !c.in_defer,
        &mut |p, _| Some(raw_stmt(p, format!("zr{k}()?;"))),
    )?;
    ap(id, "`?` of an error type the function cannot convert")
}

// ------------------------------------------------------------- ownership

fn is_move_local(e: &Expr) -> Option<(String, Ty)> {
    if let EK::Move(inner) = &e.kind
        && let EK::Local(n) = &inner.kind
    {
        return Some((n.clone(), inner.ty.clone()));
    }
    None
}

/// The first explicit `move local` of a statement that is not under a
/// nested block (so it is unconditional).
fn top_level_move(s: &Stmt) -> Option<(String, Ty)> {
    fn expr(e: &Expr) -> Option<(String, Ty)> {
        if let Some(m) = is_move_local(e) {
            return Some(m);
        }
        match &e.kind {
            EK::Call(c) | EK::Method(_, c) => {
                if let EK::Method(r, _) = &e.kind
                    && let Some(m) = expr(r)
                {
                    return Some(m);
                }
                c.args.iter().find_map(|a| expr(&a.e))
            }
            EK::Binary(_, a, b) => expr(a).or_else(|| expr(b)),
            EK::Cast(a, _) | EK::Unary(_, a) | EK::Some(a) => expr(a),
            EK::StructLit { fields, .. } => fields.iter().find_map(|(_, v)| expr(v)),
            _ => None,
        }
    }
    match &s.kind {
        SK::Let { init: Some(e), .. } | SK::Expr(e) => expr(e),
        SK::Assign(_, _, e) => expr(e),
        _ => None,
    }
}

/// ch01 R4a(a) (O0004): a use of a value after it was moved.
pub fn m_use_after_move(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (bid, _) = block_id(p, rng, &mut |b, _| {
        b.stmts.iter().any(|s| top_level_move(s).is_some())
    })?;
    // Which statement and which local, read from the block itself.
    let (k, name, ty) = edit_block(p, bid, |b| {
        let ks: Vec<usize> = (0..b.stmts.len())
            .filter(|&i| top_level_move(&b.stmts[i]).is_some())
            .collect();
        let k = ks[0];
        let (n, t) = top_level_move(&b.stmts[k]).unwrap_or_default_pair();
        (k, n, t)
    })?;
    // A copyable field of the moved value to read afterwards.
    let field = p.struct_fields(&ty).and_then(|fs| {
        fs.into_iter()
            .find(|f| p.is_copy(&f.ty, &Bounds::new()))
            .map(|f| f.name)
    });
    let text = format!("let zuse{} = {name}.{};", p.next_id, field?);
    let st = raw_stmt(p, text);
    let sid = st.id;
    edit_block(p, bid, move |b| b.stmts.insert(k + 1, st))?;
    ap(sid, "a use after the move")
}

trait PairDefault {
    fn unwrap_or_default_pair(self) -> (String, Ty);
}

impl PairDefault for Option<(String, Ty)> {
    fn unwrap_or_default_pair(self) -> (String, Ty) {
        self.unwrap_or_else(|| (String::new(), Ty::Unit))
    }
}

/// ch01 R8 (O0008): a value consumed on one path of an `if` only.
pub fn m_merge_disagree(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = resource_kit(p);
    let cond = closed(p, rng, &Ty::Prim(Prim::Bool), Mode::Synth)?;
    let mut cond = Some(cond);
    let id = insert_stmts(
        p,
        rng,
        &mut |_, c| !c.in_defer && !c.in_handler,
        &mut |p, _| {
            let v = new_resource(p, k);
            let inner = raw_stmt(p, format!("zsink{k}(move zv{k});"));
            let then = Block {
                id: p.id(),
                stmts: vec![inner],
                tail: None,
            };
            let i = Stmt {
                id: p.id(),
                kind: SK::If {
                    cond: cond.take()?,
                    then,
                    els: None,
                },
            };
            Some((vec![v, i], 1))
        },
    )?;
    ap(id, "a value consumed on one branch only")
}

/// ch01 R4a(a) (O0004): the injected form of [`m_use_after_move`].
pub fn m_use_after_move_injected(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = resource_kit(p);
    let id = insert_stmts(p, rng, &mut |_, c| !c.in_defer, &mut |p, _| {
        let v = new_resource(p, k);
        let u = raw_stmt(p, format!("zsink{k}(move zv{k});"));
        let w = raw_stmt(p, format!("let zu{k} = zv{k}.a;"));
        Some((vec![v, u, w], 2))
    })?;
    ap(id, "a use after the move")
}

/// ch01 R2 (O0002): a `sink` argument passed without `move`.
pub fn m_marker_move_injected(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = resource_kit(p);
    let id = insert_stmts(p, rng, &mut |_, c| !c.in_defer, &mut |p, _| {
        let v = new_resource(p, k);
        let u = raw_stmt(p, format!("zsink{k}(zv{k});"));
        Some((vec![v, u], 1))
    })?;
    ap(id, "a sink argument with no `move`")
}

/// ch01 R3 (O0003): moving out of a `let` parameter.
pub fn m_move_let_param(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let none = Bounds::new();
    let resources: Vec<String> = p
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Struct(s) if s.generics.is_empty() && !p.is_copy(&Ty::adt(&s.name), &none) => {
                Some(s.name.clone())
            }
            _ => None,
        })
        .collect();
    if resources.is_empty() {
        return None;
    }
    let mut name = String::new();
    let id = insert_in_body(
        p,
        rng,
        &mut |_, c| {
            c.params.iter().any(|(cv, _, t)| {
                *cv == Conv::Let
                    && matches!(t, Ty::Adt(n, a) if a.is_empty() && resources.contains(n))
            })
        },
        &mut |p, c| {
            let (_, n, _) = c.params.iter().find(|(cv, _, t)| {
                *cv == Conv::Let
                    && matches!(t, Ty::Adt(n, a) if a.is_empty() && resources.contains(n))
            })?;
            name = n.clone();
            let k = p.next_id;
            Some(raw_stmt(p, format!("let zmv{k} = {n};")))
        },
    )?;
    let _ = name;
    ap(id, "a move out of a `let` parameter")
}

/// ch01 R4a(c) (O0004): `move place.field`, a partial move.
pub fn m_partial_move(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _, _) = pick_slot(
        p,
        rng,
        &mut |e, s, _, _| {
            !matches!(s, Slot::AssignRhs | Slot::Arg)
                && matches!(&e.kind, EK::Field(r, _) if matches!(r.kind, EK::Local(_)))
        },
        &mut |e, s, _, c, _| Some((e.id, s, c.clone())),
    )?;
    let wid = p.id();
    edit_expr(p, id, move |e| {
        let inner = std::mem::replace(
            e,
            Expr {
                id: wid,
                ty: Ty::Unit,
                kind: EK::UnitLit,
            },
        );
        let ty = inner.ty.clone();
        *e = Expr {
            id: wid,
            ty,
            kind: EK::Move(Box::new(inner)),
        };
    })?;
    // `e` now has the wrapper's id; the old id lives on the inner field.
    ap(wid, "a partial move out of an aggregate")
}

// --------------------------------------------------------------- numerics

/// ch03 R4 (D0004): an `unchecked_` operation outside an `@unsafe`
/// declaration. `variant` 0 renames a `wrap_`/`sat_` call, 1 drops the
/// attribute of a function that uses one.
pub fn m_unchecked(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    if variant == 0 {
        let (id, _) = expr_id(p, rng, &mut |e, c| {
            !c.attrs.iter().any(|a| a.starts_with("@unsafe"))
                && matches!(&e.kind, EK::Method(_, c) if matches!(c.callee.as_str(), "wrap_add" | "wrap_sub" | "wrap_mul" | "sat_add" | "sat_sub" | "sat_mul"))
        })?;
        edit_expr(p, id, |e| {
            let c = call_of_mut(e)?;
            let op = c.callee.split('_').nth(1)?.to_string();
            c.callee = format!("unchecked_{op}");
            Some(())
        })??;
        return ap(id, "an unchecked operation outside an unsafe declaration");
    }
    let (fid, _) = fn_id(p, rng, &mut |f, c| {
        c.attrs.iter().any(|a| a.starts_with("@unsafe")) && !c.in_trait && has_unchecked(f)
    })?;
    // The first `unchecked_` call of its body, in source order.
    let mut first: Option<Id> = None;
    edit_fn(p, fid, |f| {
        walk_fn_body(
            f,
            &mut Hooks {
                expr: Some(&mut |e, _| {
                    if first.is_none()
                        && let EK::Method(_, c) = &e.kind
                        && c.callee.starts_with("unchecked_")
                    {
                        first = Some(e.id);
                    }
                }),
                ..Default::default()
            },
        );
        f.attrs.clear();
    })?;
    ap(
        first?,
        "an unchecked operation in a declaration that lost its @unsafe",
    )
}

/// Whether a function's body calls an `unchecked_` operation.
fn has_unchecked(f: &FnDecl) -> bool {
    let mut f = f.clone();
    let mut found = false;
    walk_fn_body(
        &mut f,
        &mut Hooks {
            expr: Some(&mut |e, _| {
                if matches!(&e.kind, EK::Method(_, c) if c.callee.starts_with("unchecked_")) {
                    found = true;
                }
            }),
            ..Default::default()
        },
    );
    found
}

/// ch03 R6 (D0006): a lossy conversion whose target is not numeric.
pub fn m_lossy_target(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(
        p,
        rng,
        &mut |e, _| matches!(&e.kind, EK::Method(_, c) if c.callee.ends_with("_as") && c.targs.len() == 1),
    )?;
    edit_expr(p, id, |e| {
        call_of_mut(e)?.targs = vec![Ty::Prim(Prim::Bool)];
        Some(())
    })??;
    ap(id, "a lossy conversion to bool")
}

/// ch03 R1 (D0001): `i128` where a fixed-width integer was written.
pub fn m_i128(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = stmt_id(
        p,
        rng,
        &mut |s, _| matches!(&s.kind, SK::Let { ty: Some(Ty::Prim(q)), .. } if q.is_int()),
    )?;
    let tid = edit_stmt(p, id, |s| {
        if let SK::Let { ty, ty_id, .. } = &mut s.kind {
            *ty = Some(Ty::adt("i128"));
            return Some(*ty_id);
        }
        None
    })??;
    ap(tid, "an `i128` annotation")
}

/// ch03 R21 (D0021): an array literal whose count is not its type's `N`.
pub fn m_array_count(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _, _) = pick_slot(
        p,
        rng,
        &mut |e, _, t, _| matches!((&e.kind, t), (EK::Array(es), Ty::Array(_, n)) if es.len() >= 2 && es.len() as u32 == *n),
        &mut |e, s, _, _, _| Some((e.id, s, ())),
    )?;
    edit_expr(p, id, |e| {
        if let EK::Array(es) = &mut e.kind {
            es.pop();
        }
    })?;
    ap(id, "an array literal one element short")
}

/// ch03 R5 (D0005): a numeric value of the wrong width at an annotated `let`.
pub fn m_numeric_let(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, t) = pick_slot(
        p,
        rng,
        &mut |_, s, t, _| s == Slot::LetInit && matches!(t, Ty::Prim(q) if q.is_num()),
        &mut |e, _, t, _, _| Some((e.id, t.clone())),
    )?;
    let Ty::Prim(q) = t else { return None };
    let other = loop {
        let o = *rng.pick(&NUMS);
        if o != q {
            break o;
        }
    };
    let ne = closed(p, rng, &Ty::Prim(other), Mode::Synth)?;
    if !set_expr(p, id, ne) {
        return None;
    }
    ap_code(
        id,
        "D0005",
        format!("a `{}` where `{}` is expected", other.name(), q.name()),
    )
}

/// R27 (T0027): an integer literal checked against a float type, a `const`
/// initialiser included (G4, fixed in I11: design §7.1 phase 6 types it).
pub fn m_int_for_float(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let (id, _) = expr_id(p, rng, &mut |e, _| matches!(&e.kind, EK::Float(_, None)))?;
    edit_expr(p, id, |e| e.kind = EK::Int(1, None))?;
    ap(id, "an integer literal where a float is expected")
}

/// R26 (T0026): a `const` whose initialiser is a `bool` where its declared
/// numeric type is expected (G4, fixed in I11).
pub fn m_const_init(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let ids: Vec<Id> = p
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Const(c) => Some(c.value.id),
            _ => None,
        })
        .collect();
    if ids.is_empty() {
        return None;
    }
    let id = *rng.pick(&ids);
    edit_expr(p, id, |e| e.kind = EK::Bool(true))?;
    ap(id, "a `bool` initialising a numeric `const`")
}

// ---------------------------------------------- statement-level insertions

/// Inserts one fixed statement into a function body.
fn insert_text(
    p: &mut Program,
    rng: &mut Rng,
    fmt: &dyn Fn(Id) -> String,
    note: &str,
) -> Option<Applied> {
    let id = insert_in_body(p, rng, &mut |_, _| true, &mut |p, _| {
        let k = p.next_id;
        Some(raw_stmt(p, fmt(k)))
    })?;
    ap(id, note.to_string())
}

pub fn m_dot_lit_synth(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let zdl{k} = .va;"),
        "a dot literal in a SYNTH position",
    )
}

pub fn m_closure_synth(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let zcl{k} = |let zn{k}| zn{k};"),
        "a closure with an unannotated parameter in SYNTH mode",
    )
}

pub fn m_array_empty(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let zae{k} = [];"),
        "an empty array literal in SYNTH mode",
    )
}

pub fn m_array_to_slice(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let zas{k}: Slice[i32] = [1, 2, 3];"),
        "an array literal checked against a slice",
    )
}

pub fn m_array_nested(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let zan{k} = [[1, 2], [3]];"),
        "rows of different lengths",
    )
}

pub fn m_tuple_binding(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    insert_text(
        p,
        rng,
        &|k| format!("let (zta{k}, ztb{k}) = 5i32;"),
        "a tuple binding of a non-tuple",
    )
}

/// R4 (T0004): a tuple type past the implementation limit of 65535 entries.
pub fn m_tuple_limit(p: &mut Program, _rng: &mut Rng, _v: u8) -> Option<Applied> {
    let k = p.id();
    let tys = vec!["i32"; 65536].join(", ");
    let id = push_raw_item(p, format!("fn zbig{k}(let x: ({tys})) {{\n}}"));
    ap(id, "a tuple type of 65536 components")
}

pub static MUTS: &[MutDef] = &[
    md!("limit/tuple-65536", 9, 4, "T0004", 0, m_tuple_limit),
    md!("call/arg-missing", 9, 39, "T0039", 0, m_arg_count),
    md!("call/arg-extra", 9, 39, "T0039", 1, m_arg_count),
    md!("call/label-wrong", 9, 37, "T0037", 0, m_arg_label),
    md!(
        "call/marker-inout-missing",
        1,
        2,
        "O0002",
        0,
        m_marker_missing
    ),
    md!(
        "call/marker-move-missing",
        1,
        2,
        "O0002",
        1,
        m_marker_missing
    ),
    md!(
        "call/marker-set-for-inout",
        1,
        2,
        "O0002",
        2,
        m_marker_missing
    ),
    md!(
        "call/marker-move-missing-injected",
        1,
        2,
        "O0002",
        0,
        m_marker_move_injected
    ),
    md!(
        "call/bound-unsatisfied",
        9,
        12,
        "T0012",
        0,
        m_bound_unsatisfied
    ),
    md!("call/method-unknown", 9, 43, "T0043", 0, m_method_name),
    md!(
        "call/numeric-method-unknown",
        9,
        43,
        "T0043",
        1,
        m_method_name
    ),
    md!("expr/field-unknown", 9, 42, "T0042", 0, m_field_name),
    md!("call/targ-count", 9, 39, "T0039", 0, m_targ_count),
    md!("cond/if-stmt", 9, 30, "T0030", 0, m_condition),
    md!("cond/while", 9, 30, "T0030", 1, m_condition),
    md!("cond/if-expr", 9, 30, "T0030", 2, m_condition),
    md!("cond/logic-operand", 9, 30, "T0030", 0, m_logic_operand),
    md!("for/not-iterable", 9, 31, "T0031", 0, m_for_iter),
    md!("flow/break-outside", 9, 33, "T0033", 0, m_break_outside),
    md!("flow/continue-outside", 9, 33, "T0033", 1, m_break_outside),
    md!("flow/never-let", 9, 33, "T0033", 0, m_never_let),
    md!("defer/return", 9, 33, "T0033", 0, m_defer_exit),
    md!("defer/raise", 9, 33, "T0033", 1, m_defer_exit),
    md!("defer/break", 9, 33, "T0033", 2, m_defer_exit),
    md!(
        "defer/errdefer-no-error-exit",
        1,
        23,
        "O0023",
        0,
        m_errdefer_no_error_exit
    ),
    md!("failure/raise-in-non-raising", 2, 1, "F0001", 0, m_raise),
    md!("failure/raise-wrong-type", 2, 1, "F0001", 1, m_raise),
    md!(
        "failure/try-non-raising",
        2,
        2,
        "F0002",
        0,
        m_try_nonraising
    ),
    md!(
        "failure/handler-non-raising",
        2,
        5,
        "F0005",
        0,
        m_handler_nonraising
    ),
    md!(
        "failure/raising-unhandled",
        2,
        1,
        "F0001",
        0,
        m_raising_unhandled
    ),
    md!("failure/error-from-missing", 2, 3, "F0003", 0, m_error_from),
    md!("own/use-after-move", 1, 4, "O0004", 0, m_use_after_move),
    md!(
        "own/use-after-move-injected",
        1,
        4,
        "O0004",
        0,
        m_use_after_move_injected
    ),
    md!("own/merge-disagree", 1, 8, "O0008", 0, m_merge_disagree),
    md!("own/move-let-param", 1, 3, "O0003", 0, m_move_let_param),
    md!("own/partial-move", 1, 4, "O0004", 0, m_partial_move),
    md!(
        "num/unchecked-outside-unsafe",
        3,
        4,
        "D0004",
        0,
        m_unchecked
    ),
    md!("num/unchecked-attr-dropped", 3, 4, "D0004", 1, m_unchecked),
    md!(
        "num/lossy-target-not-numeric",
        3,
        6,
        "D0006",
        0,
        m_lossy_target
    ),
    md!("num/i128", 3, 1, "D0001", 0, m_i128),
    md!("num/array-count", 3, 21, "D0021", 0, m_array_count),
    md!("num/let-width", 3, 5, "D0005", 0, m_numeric_let),
    md!("expr/int-for-float", 9, 27, "T0027", 0, m_int_for_float),
    md!("decl/const-init-mismatch", 9, 26, "T0026", 0, m_const_init),
    md!("expr/dot-literal-synth", 9, 34, "T0034", 0, m_dot_lit_synth),
    md!("expr/closure-synth", 9, 35, "T0035", 0, m_closure_synth),
    md!("expr/array-empty-synth", 3, 22, "D0022", 0, m_array_empty),
    md!("expr/array-to-slice", 3, 24, "D0024", 0, m_array_to_slice),
    md!("expr/array-rows", 3, 25, "D0025", 0, m_array_nested),
    md!(
        "pat/tuple-binding-non-tuple",
        9,
        31,
        "T0031",
        0,
        m_tuple_binding
    ),
];
