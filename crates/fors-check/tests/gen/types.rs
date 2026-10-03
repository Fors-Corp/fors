//! The generator's type theory: substitution, one-way matching, `Copyable`
//! (ch09 R23) and operator/trait satisfaction (ch09 R12, R21, R22) over its
//! own [`Ty`], read off the declarations of the [`Program`] being built.

use std::collections::{BTreeMap, HashMap};

use crate::ast::*;

pub type Bounds = BTreeMap<String, Vec<String>>;

pub fn subst(t: &Ty, m: &HashMap<String, Ty>) -> Ty {
    match t {
        Ty::Param(n) => m.get(n).cloned().unwrap_or_else(|| t.clone()),
        Ty::Adt(n, args) => Ty::Adt(n.clone(), args.iter().map(|a| subst(a, m)).collect()),
        Ty::Option(a) => Ty::Option(Box::new(subst(a, m))),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|a| subst(a, m)).collect()),
        Ty::Array(a, n) => Ty::Array(Box::new(subst(a, m)), *n),
        _ => t.clone(),
    }
}

/// Whether `t` mentions a generic parameter.
pub fn has_param(t: &Ty) -> bool {
    match t {
        Ty::Param(_) => true,
        Ty::Adt(_, args) => args.iter().any(has_param),
        Ty::Option(a) | Ty::Array(a, _) => has_param(a),
        Ty::Tuple(ts) => ts.iter().any(has_param),
        _ => false,
    }
}

/// One-way match of the pattern `pat` (whose `Param`s named in `vars` are
/// variables) against the closed type `actual`.
pub fn unify(pat: &Ty, actual: &Ty, vars: &[String], m: &mut HashMap<String, Ty>) -> bool {
    match (pat, actual) {
        (Ty::Param(n), _) if vars.contains(n) => match m.get(n) {
            Some(bound) => bound == actual,
            None => {
                m.insert(n.clone(), actual.clone());
                true
            }
        },
        (Ty::Adt(a, xs), Ty::Adt(b, ys)) => {
            a == b && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| unify(x, y, vars, m))
        }
        (Ty::Option(x), Ty::Option(y)) => unify(x, y, vars, m),
        (Ty::Tuple(xs), Ty::Tuple(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| unify(x, y, vars, m))
        }
        (Ty::Array(x, n), Ty::Array(y, k)) => n == k && unify(x, y, vars, m),
        _ => pat == actual,
    }
}

impl Program {
    /// The generic parameter names of the struct or enum `name`.
    pub fn adt_params(&self, name: &str) -> Vec<String> {
        if let Some(s) = self.struct_decl(name) {
            return s.generics.iter().map(|g| g.name.clone()).collect();
        }
        if let Some(e) = self.enum_decl(name) {
            return e.generics.iter().map(|g| g.name.clone()).collect();
        }
        Vec::new()
    }

    fn adt_map(&self, name: &str, args: &[Ty]) -> HashMap<String, Ty> {
        self.adt_params(name)
            .into_iter()
            .zip(args.iter().cloned())
            .collect()
    }

    /// The fields of a struct type with its arguments substituted.
    pub fn struct_fields(&self, t: &Ty) -> Option<Vec<Field>> {
        let Ty::Adt(n, args) = t else { return None };
        let s = self.struct_decl(n)?;
        let m = self.adt_map(n, args);
        Some(
            s.fields
                .iter()
                .map(|f| Field {
                    name: f.name.clone(),
                    ty: subst(&f.ty, &m),
                })
                .collect(),
        )
    }

    /// The variants of an enum type with its arguments substituted.
    pub fn enum_variants(&self, t: &Ty) -> Option<Vec<Variant>> {
        let Ty::Adt(n, args) = t else { return None };
        let e = self.enum_decl(n)?;
        let m = self.adt_map(n, args);
        Some(
            e.variants
                .iter()
                .map(|v| Variant {
                    name: v.name.clone(),
                    shape: match &v.shape {
                        VShape::Unit => VShape::Unit,
                        VShape::Tuple(ts) => {
                            VShape::Tuple(ts.iter().map(|x| subst(x, &m)).collect())
                        }
                        VShape::Record(fs) => VShape::Record(
                            fs.iter()
                                .map(|f| Field {
                                    name: f.name.clone(),
                                    ty: subst(&f.ty, &m),
                                })
                                .collect(),
                        ),
                    },
                })
                .collect(),
        )
    }

    /// The `impl Copyable for N[..]` item of `name`, if there is one.
    fn copyable_impl(&self, name: &str) -> Option<&ImplDecl> {
        self.items.iter().find_map(|i| match i {
            Item::Impl(d)
                if d.trait_name.as_deref() == Some("Copyable")
                    && matches!(&d.self_ty, Ty::Adt(n, _) if n == name) =>
            {
                Some(d)
            }
            _ => None,
        })
    }

    /// ch09 R23: whether a place of type `t` is copied (rather than moved).
    pub fn is_copy(&self, t: &Ty, b: &Bounds) -> bool {
        match t {
            Ty::Prim(_) | Ty::Unit => true,
            Ty::Option(a) | Ty::Array(a, _) => self.is_copy(a, b),
            Ty::Tuple(ts) => ts.iter().all(|a| self.is_copy(a, b)),
            Ty::Param(n) => b
                .get(n)
                .is_some_and(|bs| bs.iter().any(|x| x == "Copyable")),
            Ty::Adt(n, args) => {
                let Some(imp) = self.copyable_impl(n) else {
                    return false;
                };
                // `impl[T: Copyable] Copyable for N[T]`: the arguments must be
                // copyable too.
                let needs: Vec<&GParam> = imp
                    .generics
                    .iter()
                    .filter(|g| g.bounds.iter().any(|x| x == "Copyable"))
                    .collect();
                needs.is_empty() && args.iter().all(|a| self.is_copy(a, b)) || {
                    // generic impl: every argument position must be copyable
                    args.iter().all(|a| self.is_copy(a, b))
                }
            }
        }
    }

    /// Whether `t` implements the trait `tr` (ch09 R12), for the traits the
    /// generator uses: `Copyable`, the operator traits, and user traits.
    pub fn satisfies(&self, t: &Ty, tr: &str, b: &Bounds) -> bool {
        if tr == "Copyable" {
            return self.is_copy(t, b);
        }
        match t {
            Ty::Param(n) => b.get(n).is_some_and(|bs| bs.iter().any(|x| x == tr)),
            Ty::Prim(p) => match tr {
                "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Eq" | "Ord" => p.is_num() || (tr == "Eq"),
                "BitAnd" | "BitOr" | "BitXor" => p.is_int(),
                _ => self.user_impl(t, tr, b),
            },
            _ => self.user_impl(t, tr, b),
        }
    }

    /// An `impl tr for t'` in the program whose head matches `t` and whose
    /// parameter bounds hold.
    pub fn user_impl(&self, t: &Ty, tr: &str, b: &Bounds) -> bool {
        self.items.iter().any(|i| match i {
            Item::Impl(d) if d.trait_name.as_deref() == Some(tr) => {
                let vars: Vec<String> = d.generics.iter().map(|g| g.name.clone()).collect();
                let mut m = HashMap::new();
                if !unify(&d.self_ty, t, &vars, &mut m) {
                    return false;
                }
                d.generics.iter().all(|g| {
                    g.bounds.iter().all(|bound| match m.get(&g.name) {
                        Some(arg) => self.satisfies(arg, bound, b),
                        None => false,
                    })
                })
            }
            _ => false,
        })
    }
}
