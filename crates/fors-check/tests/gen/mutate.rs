//! The typed-mutation engine. Each [`MutDef`] breaks exactly one rule of the
//! checker's table on purpose and says which code is expected and which node
//! the diagnostic must land in. A mutation either rewrites a node of the
//! generated program in place (a wrong argument type, a removed arm, a
//! dropped bound) or, for a rule whose subject the generator does not
//! otherwise produce (brands, linear types, `asm`, a module header), injects
//! one small declaration whose violation is known (`inject`).

use crate::ast::*;
use crate::body::{FnCx, Mode};
use crate::builder::Gen;
use crate::rng::Rng;
use crate::types::*;
use crate::visit::*;

/// The outcome of applying a mutation: the node the diagnostic must land in
/// and, when the mutation can yield more than one code, the one it expects.
pub struct Applied {
    pub target: Id,
    pub code: Option<&'static str>,
    pub note: String,
}

pub fn ap(target: Id, note: impl Into<String>) -> Option<Applied> {
    Some(Applied {
        target,
        code: None,
        note: note.into(),
    })
}

pub fn ap_code(target: Id, code: &'static str, note: impl Into<String>) -> Option<Applied> {
    Some(Applied {
        target,
        code: Some(code),
        note: note.into(),
    })
}

pub type MutFn = fn(&mut Program, &mut Rng, u8) -> Option<Applied>;

#[derive(Clone, Copy)]
pub struct MutDef {
    pub name: &'static str,
    /// The chapter (1, 2, 3, 4 or 9; `0` for the ch01 flow checks that have
    /// no row in `rules.rs`) and rule this mutation targets.
    pub chapter: u8,
    pub rule: u16,
    /// The expected code unless the mutation says otherwise.
    pub code: &'static str,
    pub variant: u8,
    pub f: MutFn,
    /// A template injection rather than an in-place rewrite.
    pub inject: bool,
}

/// Runs `f` with a [`Gen`] over `p` (so a mutation can build closed
/// expressions with the generator's own productions) and puts `p` back.
pub fn with_gen<R>(p: &mut Program, rng: &mut Rng, f: impl FnOnce(&mut Gen) -> R) -> R {
    let prog = std::mem::replace(p, Program::new(0));
    let mut g = Gen::new(0);
    g.p = prog;
    g.rng = rng.clone();
    let r = f(&mut g);
    *p = std::mem::replace(&mut g.p, Program::new(0));
    *rng = g.rng.clone();
    r
}

/// A closed expression of type `ty` (no rigid parameters), in the given mode.
pub fn closed(p: &mut Program, rng: &mut Rng, ty: &Ty, mode: Mode) -> Option<Expr> {
    if has_param(ty) {
        return None;
    }
    with_gen(p, rng, |g| {
        let mut cx = FnCx::new(None);
        if g.producible(&cx, ty) && g.synth_ok(&cx, ty) {
            Some(g.leaf(&mut cx, ty, mode))
        } else {
            None
        }
    })
}

pub fn mk(p: &mut Program, ty: Ty, kind: EK) -> Expr {
    Expr {
        id: p.id(),
        ty,
        kind,
    }
}

/// A type a value of `ty` is wrongly given, and the code the checker reports
/// for it at an annotated `let` and elsewhere.
pub fn wrong_for(rng: &mut Rng, ty: &Ty, let_site: bool) -> Option<(Ty, &'static str)> {
    Some(match ty {
        Ty::Prim(p) if p.is_num() => {
            if rng.chance(1, 2) {
                (Ty::Prim(Prim::Bool), "T0026")
            } else {
                let q = loop {
                    let q = *rng.pick(&NUMS);
                    if q != *p {
                        break q;
                    }
                };
                (Ty::Prim(q), if let_site { "D0005" } else { "T0026" })
            }
        }
        Ty::Prim(Prim::Bool) => (Ty::Prim(Prim::I32), "T0026"),
        Ty::Unit | Ty::Param(_) => return None,
        _ => (
            if rng.chance(1, 2) {
                Ty::Prim(Prim::I32)
            } else {
                Ty::Prim(Prim::Bool)
            },
            "T0026",
        ),
    })
}

// ------------------------------------------------------------- editing by id

/// Runs `f` on the expression `id`.
pub fn edit_expr<R>(p: &mut Program, id: Id, f: impl FnOnce(&mut Expr) -> R) -> Option<R> {
    let mut f = Some(f);
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            expr: Some(&mut |e, _| {
                if e.id == id
                    && let Some(f) = f.take()
                {
                    out = Some(f(e));
                }
            }),
            ..Default::default()
        },
    );
    out
}

/// Replaces the expression `id` by `new`, which takes over the id.
pub fn set_expr(p: &mut Program, id: Id, mut new: Expr) -> bool {
    new.id = id;
    edit_expr(p, id, move |e| *e = new).is_some()
}

pub fn edit_stmt<R>(p: &mut Program, id: Id, f: impl FnOnce(&mut Stmt) -> R) -> Option<R> {
    let mut f = Some(f);
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            stmt: Some(&mut |s, _| {
                if s.id == id
                    && let Some(f) = f.take()
                {
                    out = Some(f(s));
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn edit_block<R>(p: &mut Program, id: Id, f: impl FnOnce(&mut Block) -> R) -> Option<R> {
    let mut f = Some(f);
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            block: Some(&mut |b, _| {
                if b.id == id
                    && let Some(f) = f.take()
                {
                    out = Some(f(b));
                }
            }),
            ..Default::default()
        },
    );
    out
}

pub fn edit_fn<R>(p: &mut Program, id: Id, f: impl FnOnce(&mut FnDecl) -> R) -> Option<R> {
    let mut f = Some(f);
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            fn_decl: Some(&mut |d, _| {
                if d.id == id
                    && let Some(f) = f.take()
                {
                    out = Some(f(d));
                }
            }),
            ..Default::default()
        },
    );
    out
}

/// Runs `f` on the arm list of the `match` whose statement or expression id
/// is `mid`.
pub fn edit_arms<R>(p: &mut Program, mid: Id, f: impl FnOnce(&mut Vec<Arm>) -> R) -> Option<R> {
    let mut f = Some(f);
    let mut out = None;
    walk(
        p,
        &mut Hooks {
            arms: Some(&mut |a, _, id, _| {
                if id == mid
                    && let Some(f) = f.take()
                {
                    out = Some(f(a));
                }
            }),
            ..Default::default()
        },
    );
    out
}

/// A call or method-call expression's [`Call`].
pub fn call_of(e: &Expr) -> Option<&Call> {
    match &e.kind {
        EK::Call(c) | EK::Method(_, c) => Some(c),
        _ => None,
    }
}

pub fn call_of_mut(e: &mut Expr) -> Option<&mut Call> {
    match &mut e.kind {
        EK::Call(c) | EK::Method(_, c) => Some(c),
        _ => None,
    }
}

// =================================================== family A: wrong types

/// R26 (and ch03 R5 at a `let`): replace the value in a CHECK position with
/// one of another type. `variant` selects the slot.
fn m_slot_mismatch(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let want = match variant {
        0 => Slot::LetInit,
        1 => Slot::Return,
        2 => Slot::Arg,
        3 => Slot::FieldInit,
        4 => Slot::AssignRhs,
        5 => Slot::BinRhs,
        _ => return None,
    };
    let (id, t) = pick_slot(
        p,
        rng,
        &mut |_, s, t, _| s == want && !has_param(t) && !matches!(t, Ty::Unit),
        &mut |e, _, t, _, _| Some((e.id, t.clone())),
    )?;
    let (wt, code) = wrong_for(rng, &t, want == Slot::LetInit)?;
    let newe = closed_synth(p, rng, &wt)?;
    if !set_expr(p, id, newe) {
        return None;
    }
    ap_code(
        id,
        code,
        format!("a `{}` where `{}` is expected", ty_name(&wt), ty_name(&t)),
    )
}

fn closed_synth(p: &mut Program, rng: &mut Rng, ty: &Ty) -> Option<Expr> {
    closed(p, rng, ty, Mode::Synth)
}

pub fn ty_name(t: &Ty) -> String {
    crate::render::ty_str(t)
}

pub static BASE: &[MutDef] = &[
    MutDef {
        name: "slot-mismatch/let-init",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 0,
        f: m_slot_mismatch,
        inject: false,
    },
    MutDef {
        name: "slot-mismatch/return",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 1,
        f: m_slot_mismatch,
        inject: false,
    },
    MutDef {
        name: "slot-mismatch/arg",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 2,
        f: m_slot_mismatch,
        inject: false,
    },
    MutDef {
        name: "slot-mismatch/field-init",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 3,
        f: m_slot_mismatch,
        inject: false,
    },
    MutDef {
        name: "slot-mismatch/assign-rhs",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 4,
        f: m_slot_mismatch,
        inject: false,
    },
    MutDef {
        name: "slot-mismatch/bin-rhs",
        chapter: 9,
        rule: 26,
        code: "T0026",
        variant: 5,
        f: m_slot_mismatch,
        inject: false,
    },
];

/// The whole catalogue, every family in one slice (indexes are stable for a
/// build, which is all the runner needs).
pub fn catalogue() -> &'static [MutDef] {
    static ALL: std::sync::OnceLock<Vec<MutDef>> = std::sync::OnceLock::new();
    ALL.get_or_init(|| {
        let mut v = BASE.to_vec();
        v.extend_from_slice(crate::mut_a::MUTS);
        v.extend_from_slice(crate::mut_decls::MUTS);
        v.extend(crate::mut_corpus::defs());
        v
    })
}
