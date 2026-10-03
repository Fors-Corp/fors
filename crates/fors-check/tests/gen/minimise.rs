//! The minimiser: given a program whose verdict is not a good one, removes
//! declarations, statements, match arms and methods, and replaces
//! expressions by plain literals of their type, for as long as the verdict
//! (the class and the diagnostic codes behind it) stays the same. What is
//! left is the program a person reads.

use crate::ast::*;
use crate::body::Mode;
use crate::classify::*;
use crate::mutate::{closed, set_expr};
use crate::render::render;
use crate::rng::Rng;
use crate::run;
use crate::types::has_param;
use crate::visit::*;

/// How a verdict is told from another: the class plus what the checker said.
fn signature(v: &Verdict, res: &run::CheckResult) -> String {
    let mut codes: Vec<&str> = res.diags.iter().map(|d| d.code.as_str()).collect();
    codes.sort_unstable();
    codes.dedup();
    match v.class {
        Class::Panic => format!(
            "{} {}",
            v.class.label(),
            v.detail
                .chars()
                .filter(|c| !c.is_ascii_digit())
                .take(60)
                .collect::<String>()
        ),
        Class::QueryDisagree | Class::SilentTyError | Class::Missed => v.class.label().to_string(),
        _ => format!("{} {codes:?}", v.class.label()),
    }
}

/// Renders and checks `p`; `None` when it cannot be evaluated at all.
pub fn evaluate(p: &Program, expect: Option<&Expect>, query: bool) -> Option<(Verdict, String)> {
    let r = run::guarded(|| render(p)).ok()?;
    let res = run::check(&r.text, true);
    let mut v = classify(&res, &r.text, &r.spans, expect);
    if query
        && matches!(
            v.class,
            Class::AcceptedAsExpected | Class::RejectedAsExpected
        )
        && let Some(d) = crate::runner::query_disagreement(&r.text, &res)
    {
        v = d;
    }
    let sig = signature(&v, &res);
    Some((v, sig))
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Item,
    Stmt,
    Arm,
    Method,
    Expr,
}

const KINDS: [Kind; 5] = [Kind::Item, Kind::Stmt, Kind::Arm, Kind::Method, Kind::Expr];

fn replaceable(e: &Expr) -> bool {
    !matches!(
        e.kind,
        EK::Int(..)
            | EK::Float(..)
            | EK::Bool(_)
            | EK::UnitLit
            | EK::Local(_)
            | EK::Const(_)
            | EK::None
            | EK::Raw(_)
    ) && !has_param(&e.ty)
        && !matches!(e.ty, Ty::Unit)
}

fn count(p: &mut Program, k: Kind) -> usize {
    match k {
        Kind::Item => p.items.len(),
        Kind::Method => p
            .items
            .iter()
            .map(|i| match i {
                Item::Impl(d) => d.methods.len(),
                Item::Trait(t) => t.methods.len(),
                _ => 0,
            })
            .sum(),
        Kind::Stmt => {
            let mut n = 0;
            walk(
                p,
                &mut Hooks {
                    block: Some(&mut |b, _| n += b.stmts.len()),
                    ..Default::default()
                },
            );
            n
        }
        Kind::Arm => {
            let mut n = 0;
            walk(
                p,
                &mut Hooks {
                    arms: Some(&mut |a, _, _, _| {
                        if a.len() > 1 {
                            n += a.len();
                        }
                    }),
                    ..Default::default()
                },
            );
            n
        }
        Kind::Expr => {
            let mut n = 0;
            walk(
                p,
                &mut Hooks {
                    expr: Some(&mut |e, _| {
                        if replaceable(e) {
                            n += 1;
                        }
                    }),
                    ..Default::default()
                },
            );
            n
        }
    }
}

/// Applies the `idx`-th removal / replacement of kind `k`; `false` when it
/// does not apply.
fn apply(p: &mut Program, k: Kind, idx: usize) -> bool {
    match k {
        Kind::Item => {
            if idx < p.items.len() {
                p.items.remove(idx);
                true
            } else {
                false
            }
        }
        Kind::Method => {
            let mut i = idx;
            for it in &mut p.items {
                let ms = match it {
                    Item::Impl(d) => &mut d.methods,
                    Item::Trait(t) => &mut t.methods,
                    _ => continue,
                };
                if i < ms.len() {
                    ms.remove(i);
                    return true;
                }
                i -= ms.len();
            }
            false
        }
        Kind::Stmt => {
            let mut i = idx;
            let mut done = false;
            walk(
                p,
                &mut Hooks {
                    block: Some(&mut |b, _| {
                        if !done && i < b.stmts.len() {
                            b.stmts.remove(i);
                            done = true;
                        } else if !done {
                            i -= b.stmts.len();
                        }
                    }),
                    ..Default::default()
                },
            );
            done
        }
        Kind::Arm => {
            let mut i = idx;
            let mut done = false;
            walk(
                p,
                &mut Hooks {
                    arms: Some(&mut |a, _, _, _| {
                        if done || a.len() <= 1 {
                            return;
                        }
                        if i < a.len() {
                            a.remove(i);
                            done = true;
                        } else {
                            i -= a.len();
                        }
                    }),
                    ..Default::default()
                },
            );
            done
        }
        Kind::Expr => {
            let mut i = idx;
            let mut target: Option<(Id, Ty)> = None;
            walk(
                p,
                &mut Hooks {
                    expr: Some(&mut |e, _| {
                        if target.is_none() && replaceable(e) {
                            if i == 0 {
                                target = Some((e.id, e.ty.clone()));
                            } else {
                                i -= 1;
                            }
                        }
                    }),
                    ..Default::default()
                },
            );
            let Some((id, ty)) = target else { return false };
            let mut rng = Rng::new(7);
            match closed(p, &mut rng, &ty, Mode::Check) {
                Some(e) => set_expr(p, id, e),
                None => false,
            }
        }
    }
}

/// The smallest program found whose verdict has the signature of `p`'s.
/// `budget` caps the number of check runs.
pub fn minimise(p: &Program, expect: Option<&Expect>, query: bool, budget: usize) -> Program {
    let Some((_, want)) = evaluate(p, expect, query) else {
        return p.clone();
    };
    let mut cur = p.clone();
    let mut runs = 0usize;
    loop {
        let mut progress = false;
        for k in KINDS {
            let mut idx = 0usize;
            while idx < count(&mut cur, k) {
                if runs >= budget {
                    return cur;
                }
                let mut q = cur.clone();
                if !apply(&mut q, k, idx) {
                    idx += 1;
                    continue;
                }
                runs += 1;
                match evaluate(&q, expect, query) {
                    Some((_, sig)) if sig == want => {
                        cur = q;
                        progress = true;
                    }
                    _ => idx += 1,
                }
            }
        }
        if !progress {
            return cur;
        }
    }
}
