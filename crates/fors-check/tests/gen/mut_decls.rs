//! Mutations of declarations and patterns: impls against their traits,
//! member-name clashes, bounds a body depends on, `match` arms, patterns and
//! struct literals.

use crate::ast::*;
use crate::body::Mode;
use crate::mutate::*;
use crate::reid::{clone_fresh, fresh_expr, fresh_fn};
use crate::rng::Rng;
use crate::visit::*;

// ------------------------------------------------------------------ match

/// The arms whose removal leaves a hole: no other arm is a wildcard or a
/// binder, so what the removed arm covered is covered by nothing.
fn removable(arms: &[Arm]) -> Vec<usize> {
    if arms.len() < 2 {
        return Vec::new();
    }
    (0..arms.len())
        .filter(|&i| {
            arms.iter()
                .enumerate()
                .all(|(j, a)| j == i || !matches!(a.pat.kind, PK::Wild | PK::Bind(_)))
        })
        .collect()
}

/// R53 (T0053): an arm removed from a `match` that was exhaustive by
/// construction. The diagnostic is the `match`'s.
pub fn m_arm_removed(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let mid = pick_arms(
        p,
        rng,
        &mut |arms, _, _, _| !removable(arms).is_empty(),
        &mut |arms, _, mid, _, rng| {
            let c = removable(arms);
            let i = c[rng.below(c.len())];
            arms.remove(i);
            Some(mid)
        },
    )?;
    ap(mid, "an arm removed from an exhaustive match")
}

/// R54 (T0054): a `_` arm after arms that already cover everything.
pub fn m_arm_unreachable(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    // The type the new arm's body must have: `None` for a statement arm.
    let (mid, want) = pick_arms(
        p,
        rng,
        &mut |arms, _, _, _| !arms.is_empty(),
        &mut |arms, _, mid, _, _| {
            let want = match &arms[0].body {
                ArmBody::Expr(e) if e.ty != Ty::Unit => Some(e.ty.clone()),
                ArmBody::Block(b) => b.tail.as_ref().map(|t| t.ty.clone()),
                _ => None,
            };
            Some((mid, want))
        },
    )?;
    let body = match want {
        None => ArmBody::Block(Block {
            id: p.id(),
            stmts: Vec::new(),
            tail: None,
        }),
        Some(ty) => ArmBody::Expr(closed(p, rng, &ty, Mode::Check)?),
    };
    let arm = Arm {
        id: p.id(),
        pat: Pat {
            id: p.id(),
            kind: PK::Wild,
        },
        body,
    };
    let aid = arm.id;
    edit_arms(p, mid, move |arms| arms.push(arm))?;
    ap(aid, "a wildcard arm after an exhaustive set")
}

// --------------------------------------------------------------- patterns

fn fn_names(p: &Program) -> Vec<String> {
    p.items
        .iter()
        .filter_map(|i| match i {
            Item::Fn(f) => Some(f.name.clone()),
            _ => None,
        })
        .collect()
}

/// R50 (T0050): `variant` 0 a `_` replaced by a bare function name, 1 a
/// payload pattern with one component too many.
pub fn m_pattern(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let names = fn_names(p);
    let extra = p.id();
    let id = pick_pat(
        p,
        rng,
        &mut |q, _| match variant {
            0 => !names.is_empty() && matches!(q.kind, PK::Wild),
            _ => matches!(
                &q.kind,
                PK::Variant {
                    sub: PSub::Tuple(_),
                    ..
                }
            ),
        },
        &mut |q, _, rng| {
            if variant == 0 {
                q.kind = PK::Bare(names[rng.below(names.len())].clone());
            } else if let PK::Variant {
                sub: PSub::Tuple(ps),
                ..
            } = &mut q.kind
            {
                ps.push(Pat {
                    id: extra,
                    kind: PK::Wild,
                });
            }
            Some(q.id)
        },
    )?;
    ap(
        id,
        if variant == 0 {
            "a bare function name as a pattern"
        } else {
            "a payload pattern with an extra component"
        },
    )
}

// ---------------------------------------------------------- struct literals

/// R34 (T0034): `variant` 0 a field missing from a struct literal, 1 a field
/// given twice, 2 a field the struct does not have.
pub fn m_struct_lit(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let (id, _) = expr_id(
        p,
        rng,
        &mut |e, _| matches!(&e.kind, EK::StructLit { fields, .. } if !fields.is_empty()),
    )?;
    let k = rng.next() as usize;
    match variant {
        0 => {
            edit_expr(p, id, |e| {
                if let EK::StructLit { fields, .. } = &mut e.kind {
                    let n = fields.len();
                    fields.remove(k % n);
                }
            })?;
        }
        1 => {
            let dup = edit_expr(p, id, |e| match &e.kind {
                EK::StructLit { fields, .. } => {
                    let (n, v) = &fields[k % fields.len()];
                    Some((n.clone(), v.clone()))
                }
                _ => None,
            })??;
            let fresh = fresh_expr(p, &dup.1);
            edit_expr(p, id, move |e| {
                if let EK::StructLit { fields, .. } = &mut e.kind {
                    fields.push((dup.0, fresh));
                }
            })?;
        }
        _ => {
            let v = mk(p, Ty::Prim(Prim::I32), EK::Int(1, Some(Prim::I32)));
            edit_expr(p, id, move |e| {
                if let EK::StructLit { fields, .. } = &mut e.kind {
                    fields.push(("zzfield".to_string(), v));
                }
            })?;
        }
    }
    ap(
        id,
        [
            "a field missing",
            "a field given twice",
            "a field that is not declared",
        ][variant.min(2) as usize],
    )
}

// -------------------------------------------------------------------- impls

/// Indices of the items an impl-level mutation may take: impls of a user
/// trait (`Tr<n>`).
fn trait_impls(p: &Program) -> Vec<usize> {
    p.items
        .iter()
        .enumerate()
        .filter(|(_, i)| matches!(i, Item::Impl(d) if d.trait_name.as_deref().is_some_and(|t| t.starts_with("Tr"))))
        .map(|(k, _)| k)
        .collect()
}

fn impl_mut(p: &mut Program, k: usize) -> &mut ImplDecl {
    match &mut p.items[k] {
        Item::Impl(d) => d,
        _ => unreachable!("an impl index"),
    }
}

/// R17 (T0017): `variant` 0 a required method missing from an impl, 1 a
/// method the trait does not declare, 2 a method whose signature is not the
/// trait's.
pub fn m_impl_method(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let cands: Vec<usize> = trait_impls(p)
        .into_iter()
        .filter(|&k| match &p.items[k] {
            Item::Impl(d) => d.methods.iter().any(|m| m.name.starts_with('m')),
            _ => false,
        })
        .collect();
    if cands.is_empty() {
        return None;
    }
    let k = cands[rng.below(cands.len())];
    let which = rng.next() as usize;
    let required: Vec<usize> = match &p.items[k] {
        Item::Impl(d) => (0..d.methods.len())
            .filter(|&i| d.methods[i].name.starts_with('m'))
            .collect(),
        _ => return None,
    };
    let at = required[which % required.len()];
    match variant {
        0 => {
            let head = impl_mut(p, k).head_id;
            impl_mut(p, k).methods.remove(at);
            ap(head, "a required method missing from the impl")
        }
        1 => {
            let src = impl_mut(p, k).methods[at].clone();
            let mut extra = fresh_fn(p, &src);
            extra.name = "zextra".to_string();
            let head = impl_mut(p, k).head_id;
            impl_mut(p, k).methods.push(extra);
            ap(head, "a method the trait does not declare")
        }
        _ => {
            let d = impl_mut(p, k);
            let m = &mut d.methods[at];
            m.ret = if m.ret == Ty::Prim(Prim::Bool) {
                Ty::Prim(Prim::I32)
            } else {
                Ty::Prim(Prim::Bool)
            };
            let head = d.head_id;
            ap(head, "a method whose return type is not the trait's")
        }
    }
}

/// R19 (T0019): an impl written twice.
pub fn m_impl_duplicate(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let cands: Vec<usize> = p
        .items
        .iter()
        .enumerate()
        .filter(|(_, i)| matches!(i, Item::Impl(d) if d.trait_name.is_some()))
        .map(|(k, _)| k)
        .collect();
    if cands.is_empty() {
        return None;
    }
    let k = cands[rng.below(cands.len())];
    let src = p.items[k].clone();
    let copy = clone_fresh(p, &src);
    let head = match &copy {
        Item::Impl(d) => d.head_id,
        _ => return None,
    };
    p.items.insert(k + 1, copy);
    ap(head, "an impl written twice")
}

/// R18 (T0018): an impl parameter that no part of the head mentions.
pub fn m_impl_unconstrained(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let cands: Vec<usize> = p
        .items
        .iter()
        .enumerate()
        // An impl with methods would turn its callers' inference into a second
        // diagnostic (`cannot infer ZP`): a marker impl has no callers.
        .filter(|(_, i)| matches!(i, Item::Impl(d) if d.methods.is_empty()))
        .map(|(k, _)| k)
        .collect();
    if cands.is_empty() {
        return None;
    }
    let k = cands[rng.below(cands.len())];
    let id = p.id();
    let d = impl_mut(p, k);
    d.generics.push(GParam {
        id,
        name: "ZP".to_string(),
        bounds: Vec::new(),
    });
    let head = d.head_id;
    ap(head, "an impl parameter the head never mentions")
}

/// R48 (T0048): `variant` 0 an inherent method named like a field of its
/// struct, 1 an inherent method that another impl block of the same head
/// already declares.
pub fn m_member_clash(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let called = called_names(p);
    let cands: Vec<usize> = p
        .items
        .iter()
        .enumerate()
        .filter(|(_, i)| {
            let Item::Impl(d) = i else { return false };
            if d.trait_name.is_some() || d.methods.is_empty() {
                return false;
            }
            let Ty::Adt(n, _) = &d.self_ty else {
                return false;
            };
            if variant == 0 {
                return p.struct_decl(n).is_some_and(|s| !s.fields.is_empty());
            }
            // A duplicate of a method somebody calls makes the call
            // ambiguous (T0044) as well: only an uncalled one is clean.
            d.methods.iter().any(|m| !called.contains(&m.name))
        })
        .map(|(k, _)| k)
        .collect();
    if cands.is_empty() {
        return None;
    }
    let k = cands[rng.below(cands.len())];
    let (src, self_ty, generics, trait_args) = match &p.items[k] {
        Item::Impl(d) => {
            let pool: Vec<&FnDecl> = d
                .methods
                .iter()
                .filter(|m| variant == 0 || !called.contains(&m.name))
                .collect();
            let m = pool[rng.below(pool.len())].clone();
            (
                m,
                d.self_ty.clone(),
                d.generics.clone(),
                d.trait_args.clone(),
            )
        }
        _ => return None,
    };
    let mut m = fresh_fn(p, &src);
    if variant == 0 {
        let Ty::Adt(n, _) = &self_ty else { return None };
        let fields = p.struct_decl(n)?.fields.clone();
        m.name = fields[rng.below(fields.len())].name.clone();
        let d = impl_mut(p, k);
        d.methods.push(m);
        let head = d.head_id;
        return ap(head, "an inherent method named like a field");
    }
    let gs: Vec<GParam> = generics
        .iter()
        .map(|g| GParam {
            id: p.id(),
            name: g.name.clone(),
            bounds: g.bounds.clone(),
        })
        .collect();
    let (id, head_id) = (p.id(), p.id());
    p.items.insert(
        k + 1,
        Item::Impl(ImplDecl {
            id,
            head_id,
            generics: gs,
            trait_name: None,
            trait_args,
            self_ty,
            assoc: Vec::new(),
            methods: vec![m],
        }),
    );
    ap(head_id, "an inherent method declared in two impl blocks")
}

/// The simple names of every function and method the program calls.
fn called_names(p: &mut Program) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    walk(
        p,
        &mut Hooks {
            expr: Some(&mut |e, _| {
                if let Some(c) = call_of(e) {
                    out.insert(c.callee.rsplit('.').next().unwrap_or("").to_string());
                }
            }),
            ..Default::default()
        },
    );
    out
}

// ------------------------------------------------------------------ bounds

/// Every use of the capability a generic parameter's bound grants: the
/// expression, the code its removal makes the checker report there, and the
/// node whose end marks the moment it reports: a method is looked up once its
/// receiver is typed, before its arguments; an operator once its left operand
/// is, before its right one; a call once its arguments are.
fn uses(
    f: &FnDecl,
    tparam: &str,
    bound: &str,
    trait_methods: &[String],
) -> Vec<(Id, &'static str, Id)> {
    let mut f = f.clone();
    let mut found: Vec<(Id, &'static str, Id)> = Vec::new();
    let want = Ty::Param(tparam.to_string());
    walk_fn_body(
        &mut f,
        &mut Hooks {
            expr: Some(&mut |e, _| match &e.kind {
                EK::Binary(op, a, _) if a.ty == want && op.trait_name() == Some(bound) => {
                    found.push((e.id, "T0057", a.id))
                }
                EK::Method(r, c) if r.ty == want && trait_methods.contains(&c.callee) => {
                    found.push((e.id, "T0043", r.id))
                }
                EK::Call(c)
                    if c.sig
                        .generics
                        .iter()
                        .any(|g| g.bounds.iter().any(|b| b == bound))
                        && c.args.iter().any(|a| a.e.ty == want) =>
                {
                    found.push((e.id, "T0012", e.id))
                }
                _ => {}
            }),
            ..Default::default()
        },
    );
    found
}

/// R57 / R43 / R12: a bound removed from a generic function whose body uses
/// what the bound granted. The code depends on the use typed first: an operator is
/// T0057, a method of the bounding trait is T0043, a call that needs the
/// bound of its own is T0012.
pub fn m_bound_removed(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    // The checker reports the use it types FIRST: operands and arguments
    // before the operator or call that takes them, left to right. That is
    // the use whose reporting moment (see `uses`) comes first in the text;
    // of two at one moment, the inner one (the shorter) first.
    let spans = crate::render::render(p).spans;
    let key = |id: Id, at: Id| {
        let (lo, hi) = spans.get(&id).copied().unwrap_or((0, u32::MAX));
        (spans.get(&at).map_or(u32::MAX, |s| s.1), hi - lo)
    };
    let mut cands: Vec<(usize, usize, usize, Id, &'static str)> = Vec::new();
    for (ii, it) in p.items.iter().enumerate() {
        let Item::Fn(f) = it else { continue };
        for (gi, g) in f.generics.iter().enumerate() {
            for (bi, b) in g.bounds.iter().enumerate() {
                if b == "Copyable" {
                    continue;
                }
                let tm: Vec<String> = p
                    .trait_decl(b)
                    .map(|t| t.methods.iter().map(|m| m.name.clone()).collect())
                    .unwrap_or_default();
                let all = uses(f, &g.name, b, &tm);
                // Uses of different kinds (an operator on the parameter next to
                // a call that needs the same bound) are not ordered by anything
                // but the checker's own sequence of phases: only a function
                // whose uses all give one code is a mutation with one answer.
                if all.iter().any(|u| u.1 != all[0].1) {
                    continue;
                }
                let first = all.into_iter().min_by_key(|(id, _, at)| key(*id, *at));
                if let Some((id, code, _)) = first {
                    cands.push((ii, gi, bi, id, code));
                }
            }
        }
    }
    if cands.is_empty() {
        return None;
    }
    let (ii, gi, bi, id, code) = cands[rng.below(cands.len())];
    let Item::Fn(f) = &mut p.items[ii] else {
        return None;
    };
    let b = f.generics[gi].bounds.remove(bi);
    ap_code(
        id,
        code,
        format!("the bound `{b}` removed from a parameter the body uses it on"),
    )
}

/// R23 (T0023): a `Copyable` impl of a generic type whose parameter's
/// `Copyable` bound is removed, so a field of that parameter is not copyable.
pub fn m_copyable_bound_removed(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let cands: Vec<(usize, usize)> = p
        .items
        .iter()
        .enumerate()
        .filter_map(|(k, i)| match i {
            Item::Impl(d) if d.trait_name.as_deref() == Some("Copyable") => match &d.self_ty {
                Ty::Adt(n, args) if !args.is_empty() => {
                    let fields = p
                        .struct_decl(n)
                        .map(|s| s.fields.clone())
                        .unwrap_or_default();
                    let g = d.generics.iter().position(|g| {
                        g.bounds.iter().any(|b| b == "Copyable")
                            && fields.iter().any(|f| mentions(&f.ty, &g.name))
                    })?;
                    Some((k, g))
                }
                _ => None,
            },
            _ => None,
        })
        .collect();
    if cands.is_empty() {
        return None;
    }
    let (k, g) = cands[rng.below(cands.len())];
    let d = impl_mut(p, k);
    d.generics[g].bounds.retain(|b| b != "Copyable");
    let head = d.head_id;
    ap(
        head,
        "a Copyable impl whose parameter is no longer Copyable",
    )
}

fn mentions(t: &Ty, name: &str) -> bool {
    match t {
        Ty::Param(n) => n == name,
        Ty::Adt(_, a) | Ty::Tuple(a) => a.iter().any(|x| mentions(x, name)),
        Ty::Option(a) | Ty::Array(a, _) => mentions(a, name),
        _ => false,
    }
}

/// R16 (T0016): a trait method's `self` given a type other than `Self`.
pub fn m_trait_self_typed(p: &mut Program, rng: &mut Rng, _v: u8) -> Option<Applied> {
    let called = called_names(p);
    let cands: Vec<(usize, usize)> = p
        .items
        .iter()
        .enumerate()
        .filter_map(|(k, i)| match i {
            // A trait that has impls would also fail them (T0017): only a trait
            // nobody implements gives the one diagnostic.
            Item::Trait(t)
                if !p.items.iter().any(|j| matches!(j, Item::Impl(d) if d.trait_name.as_deref() == Some(t.name.as_str())))
                    && t.methods.iter().all(|m| !called.contains(&m.name)) =>
            {
                Some(
                    t.methods
                        .iter()
                        .enumerate()
                        .filter(|(_, m)| m.params.first().is_some_and(|q| q.ty.is_none()))
                        .map(move |(j, _)| (k, j)),
                )
            }
            _ => None,
        })
        .flatten()
        .collect();
    if cands.is_empty() {
        return None;
    }
    let (k, j) = cands[rng.below(cands.len())];
    let Item::Trait(t) = &mut p.items[k] else {
        return None;
    };
    let q = &mut t.methods[j].params[0];
    q.ty = Some(Ty::Prim(Prim::I32));
    ap(q.id, "a trait method's `self` typed `i32`")
}

pub static MUTS: &[MutDef] = &[
    md!("match/arm-removed", 9, 53, "T0053", 0, m_arm_removed),
    md!(
        "match/arm-unreachable",
        9,
        54,
        "T0054",
        0,
        m_arm_unreachable
    ),
    md!("pattern/bare-fn-name", 9, 50, "T0050", 0, m_pattern),
    md!("pattern/payload-arity", 9, 50, "T0050", 1, m_pattern),
    md!("struct-lit/field-missing", 9, 34, "T0034", 0, m_struct_lit),
    md!("struct-lit/field-twice", 9, 34, "T0034", 1, m_struct_lit),
    md!("struct-lit/field-unknown", 9, 34, "T0034", 2, m_struct_lit),
    md!("impl/method-missing", 9, 17, "T0017", 0, m_impl_method),
    md!("impl/method-extra", 9, 17, "T0017", 1, m_impl_method),
    md!("impl/method-signature", 9, 17, "T0017", 2, m_impl_method),
    md!("impl/duplicate", 9, 19, "T0019", 0, m_impl_duplicate),
    md!(
        "impl/unconstrained-param",
        9,
        18,
        "T0018",
        0,
        m_impl_unconstrained
    ),
    md!(
        "member/method-named-as-field",
        9,
        48,
        "T0048",
        0,
        m_member_clash
    ),
    md!(
        "member/method-in-two-impls",
        9,
        48,
        "T0048",
        1,
        m_member_clash
    ),
    md!(
        "bound/removed-where-used",
        9,
        57,
        "T0057",
        0,
        m_bound_removed
    ),
    md!(
        "bound/copyable-impl-param",
        9,
        23,
        "T0023",
        0,
        m_copyable_bound_removed
    ),
    md!("trait/self-typed", 9, 16, "T0016", 0, m_trait_self_typed),
];
