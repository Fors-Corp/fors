//! ch02 R17's `render` (design §5.4 step 4): the text of the ONE line an
//! error leaving `main` writes to the standard error descriptor.
//!
//! `render` is defined on the STATIC type `E`, recursively, and "is the
//! whole of v0.1's error reporting". [`render`] is a direct reading of R17's
//! clause list, one arm per clause and in R17's order:
//!
//! 1. an enum value: the type's fully-qualified path, `.`, the variant name,
//!    and for a payload `(` the components separated by `, ` `)`, or `{ `
//!    `name: ` component `, ` ... ` }` for a struct-form variant;
//! 2. a struct value: its path followed by `{ name: rendered, ... }` over
//!    its fields in declaration order;
//! 3. a tuple: `(` components `)`;
//! 4. an integer: base 10, a leading `-` when negative, no grouping and no
//!    padding;
//! 5. `bool`: `true` / `false`;
//! 6. `()`: `()`;
//! 7. a `Str`: its text between double quotes with `\`, `"`, newline,
//!    carriage return and tab escaped as `\\`, `\"`, `\n`, `\r`, `\t`, so
//!    the line stays ONE line;
//! 8. every other type — `Own`, `Slice`, a `fn` type, a `dyn` type, a
//!    root-capability or allocator type, a rigid type parameter — as `..`.
//!
//! No locale, no width, no colour, no backtrace. The names clauses 1 and 2
//! need come from [`fors_fmir::names::TypeNames`], which lowering writes
//! (the interpreter reads no checker output); a nominal type with no row
//! there is clause 8's `..` — which is exactly how lowering marks an opaque
//! type.
//!
//! [decision: R17 spells the struct-form clauses as concatenated tokens —
//! "the variant name, and ... `{ ` `name: ` rendered `, ` ... ` }`" and "its
//! path followed by `{ name: rendered, ... }`" — so no space is inserted
//! between the name and `{`: `app.E.bad{ code: 1 }`, `app.P{ x: 1 }`. No
//! corpus test pins either form; this is the literal reading.]

use fors_fir::ty::{PrimKind, TyId, TyStore, TyTag};
use fors_fmir::names::{TypeName, TypeNames, VariantPayload};

use crate::arith::IntKind;
use crate::value::Slot;

/// What `render` reads of a running machine: aggregate cells and `Str`
/// bytes, by the handle a [`Slot`] carries. Implemented by the dispatch
/// loop's machine, so this module never sees its private tables.
pub trait ValueSource {
    /// The slots of the aggregate cell `handle` names.
    fn cell(&self, handle: u64) -> Option<&[Slot]>;
    /// The bytes of the `Str` handle `handle`.
    fn str_bytes(&self, handle: u64) -> Option<&[u8]>;
}

/// The recursion guard: R17's recursion follows the STATIC type, and a
/// nominal type can only contain itself through an opaque (`..`) type, so
/// any real error type is far shallower. Reaching this is a malformed
/// table, reported, never a stack overflow.
const RENDER_DEPTH_MAX: u32 = 64;

/// ch02 R17(b)'s whole line: `error: ` + `render(e)` + `\n`.
pub fn error_line(
    v: Slot,
    ty: TyId,
    tys: &TyStore,
    names: &TypeNames,
    src: &dyn ValueSource,
) -> Result<Vec<u8>, String> {
    let mut out = b"error: ".to_vec();
    render_into(&mut out, v, ty, tys, names, src, 0)?;
    out.push(b'\n');
    Ok(out)
}

/// `render(v)` at the static type `ty`.
pub fn render(
    v: Slot,
    ty: TyId,
    tys: &TyStore,
    names: &TypeNames,
    src: &dyn ValueSource,
) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    render_into(&mut out, v, ty, tys, names, src, 0)?;
    Ok(out)
}

fn render_into(
    out: &mut Vec<u8>,
    v: Slot,
    ty: TyId,
    tys: &TyStore,
    names: &TypeNames,
    src: &dyn ValueSource,
    depth: u32,
) -> Result<(), String> {
    if depth > RENDER_DEPTH_MAX {
        return Err(format!(
            "render recursed past {RENDER_DEPTH_MAX} levels of static type"
        ));
    }
    let bare = tys.unqual(ty);
    let tag = if (bare.0 as usize) < tys.len() {
        tys.tag(bare)
    } else {
        return Err(format!("render: type {} is not in the type store", ty.0));
    };
    // Clauses 1 and 2: a nominal type lowering named.
    if tag == TyTag::Nominal
        && let Some(name) = names.get(bare).or_else(|| names.get(ty))
    {
        return match name {
            TypeName::Enum { path, variants } => {
                let cell = src
                    .cell(v.bits)
                    .ok_or_else(|| format!("render: `{path}` value is not a variant cell"))?;
                let discr = cell
                    .first()
                    .ok_or_else(|| format!("render: `{path}` value has no discriminant"))?
                    .bits;
                let variant = variants
                    .iter()
                    .find(|w| w.discr == discr)
                    .ok_or_else(|| format!("render: `{path}` has no variant {discr}"))?;
                out.extend_from_slice(path.as_bytes());
                out.push(b'.');
                out.extend_from_slice(variant.name.as_bytes());
                let comp = |i: usize| -> Result<Slot, String> {
                    cell.get(i + 1)
                        .copied()
                        .ok_or_else(|| format!("render: `{path}` payload {i} is missing"))
                };
                match &variant.payload {
                    VariantPayload::Unit => {}
                    VariantPayload::Tuple(parts) => {
                        out.push(b'(');
                        for (i, t) in parts.iter().enumerate() {
                            if i > 0 {
                                out.extend_from_slice(b", ");
                            }
                            render_into(out, comp(i)?, *t, tys, names, src, depth + 1)?;
                        }
                        out.push(b')');
                    }
                    VariantPayload::Fields(fields) => {
                        out.extend_from_slice(b"{ ");
                        for (i, (n, t)) in fields.iter().enumerate() {
                            if i > 0 {
                                out.extend_from_slice(b", ");
                            }
                            out.extend_from_slice(n.as_bytes());
                            out.extend_from_slice(b": ");
                            render_into(out, comp(i)?, *t, tys, names, src, depth + 1)?;
                        }
                        out.extend_from_slice(b" }");
                    }
                }
                Ok(())
            }
            TypeName::Struct { path, fields } => {
                let cell = src
                    .cell(v.bits)
                    .ok_or_else(|| format!("render: `{path}` value is not a struct cell"))?;
                out.extend_from_slice(path.as_bytes());
                out.extend_from_slice(b"{ ");
                for (i, (n, t)) in fields.iter().enumerate() {
                    if i > 0 {
                        out.extend_from_slice(b", ");
                    }
                    let s = cell
                        .get(i)
                        .copied()
                        .ok_or_else(|| format!("render: `{path}` field {i} is missing"))?;
                    out.extend_from_slice(n.as_bytes());
                    out.extend_from_slice(b": ");
                    render_into(out, s, *t, tys, names, src, depth + 1)?;
                }
                out.extend_from_slice(b" }");
                Ok(())
            }
        };
    }
    match tag {
        // Clause 3: a tuple.
        TyTag::Tuple => {
            let parts = tys.args_vec(fors_fir::ty::ArgsId(tys.b(bare)));
            let cell = src
                .cell(v.bits)
                .ok_or_else(|| "render: a tuple value is not a cell".to_string())?;
            out.push(b'(');
            for (i, t) in parts.iter().enumerate() {
                if i > 0 {
                    out.extend_from_slice(b", ");
                }
                let s = cell
                    .get(i)
                    .copied()
                    .ok_or_else(|| format!("render: tuple component {i} is missing"))?;
                render_into(out, s, *t, tys, names, src, depth + 1)?;
            }
            out.push(b')');
            Ok(())
        }
        TyTag::Prim => {
            let p = PrimKind::from_u8(tys.a(bare) as u8)
                .ok_or_else(|| "render: bad primitive kind".to_string())?;
            match p {
                // Clause 5: `bool`.
                PrimKind::Bool => {
                    out.extend_from_slice(if v.bits != 0 { b"true" } else { b"false" });
                }
                // Clause 7: a `Str`.
                PrimKind::Str => {
                    let bytes = src
                        .str_bytes(v.bits)
                        .ok_or_else(|| format!("render: `Str` handle {} is dangling", v.bits))?;
                    out.push(b'"');
                    for &b in bytes {
                        match b {
                            b'\\' => out.extend_from_slice(b"\\\\"),
                            b'"' => out.extend_from_slice(b"\\\""),
                            b'\n' => out.extend_from_slice(b"\\n"),
                            b'\r' => out.extend_from_slice(b"\\r"),
                            b'\t' => out.extend_from_slice(b"\\t"),
                            _ => out.push(b),
                        }
                    }
                    out.push(b'"');
                }
                // Clause 4: an integer, base 10.
                _ => match IntKind::from_prim(p) {
                    Some(k) => {
                        let text = if k.signed() {
                            k.as_signed(v.bits).to_string()
                        } else {
                            k.as_unsigned(v.bits).to_string()
                        };
                        out.extend_from_slice(text.as_bytes());
                    }
                    // A float or a raw pointer: clause 8.
                    None => out.extend_from_slice(b".."),
                },
            }
            Ok(())
        }
        // Clause 6: `()`.
        TyTag::Unit => {
            out.extend_from_slice(b"()");
            Ok(())
        }
        // Clause 8: every other type.
        _ => {
            out.extend_from_slice(b"..");
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fmir::names::VariantName;

    struct Src {
        cells: Vec<Vec<Slot>>,
        strs: Vec<Vec<u8>>,
    }

    impl ValueSource for Src {
        fn cell(&self, handle: u64) -> Option<&[Slot]> {
            self.cells.get(handle as usize).map(|c| c.as_slice())
        }
        fn str_bytes(&self, handle: u64) -> Option<&[u8]> {
            self.strs.get(handle as usize).map(|s| s.as_slice())
        }
    }

    fn prim(tys: &mut TyStore, p: PrimKind) -> TyId {
        tys.prim(p)
    }

    #[test]
    fn str_escapes_keep_the_line_one_line() {
        let mut tys = TyStore::new();
        let s = prim(&mut tys, PrimKind::Str);
        let src = Src {
            cells: vec![],
            strs: vec![b"a\\b\"c\nd\re\tf".to_vec()],
        };
        let got = render(Slot::val(0), s, &tys, &TypeNames::default(), &src).unwrap();
        assert_eq!(got, b"\"a\\\\b\\\"c\\nd\\re\\tf\"".to_vec());
    }

    #[test]
    fn integers_are_base_10_with_a_sign_and_no_padding() {
        let mut tys = TyStore::new();
        let i8t = prim(&mut tys, PrimKind::I8);
        let u64t = prim(&mut tys, PrimKind::U64);
        let src = Src {
            cells: vec![],
            strs: vec![],
        };
        let n = TypeNames::default();
        assert_eq!(render(Slot::val(0xFF), i8t, &tys, &n, &src).unwrap(), b"-1");
        assert_eq!(
            render(Slot::val(u64::MAX), u64t, &tys, &n, &src).unwrap(),
            b"18446744073709551615"
        );
    }

    #[test]
    fn unit_bool_tuple_and_opaque() {
        let mut tys = TyStore::new();
        let b = prim(&mut tys, PrimKind::Bool);
        let f = prim(&mut tys, PrimKind::F64);
        let i = prim(&mut tys, PrimKind::I32);
        let args = tys.intern_args(&[b, i]);
        let tup = tys.tuple(args);
        let src = Src {
            cells: vec![vec![Slot::val(1), Slot::val(5)]],
            strs: vec![],
        };
        let n = TypeNames::default();
        let unit = fors_fir::ty::TY_UNIT;
        assert_eq!(render(Slot::unit(), unit, &tys, &n, &src).unwrap(), b"()");
        assert_eq!(render(Slot::val(0), b, &tys, &n, &src).unwrap(), b"false");
        assert_eq!(
            render(Slot::val(0), tup, &tys, &n, &src).unwrap(),
            b"(true, 5)"
        );
        assert_eq!(render(Slot::val(0), f, &tys, &n, &src).unwrap(), b"..");
    }

    #[test]
    fn enum_variants_unit_tuple_and_struct_form() {
        let mut tys = TyStore::new();
        let i = prim(&mut tys, PrimKind::I32);
        let s = prim(&mut tys, PrimKind::Str);
        let e = tys.nominal(fors_index::ids::DefId(7), fors_fir::ty::NO_ARGS);
        let mut names = TypeNames::default();
        names.insert(
            e,
            TypeName::Enum {
                path: "app.Error".into(),
                variants: vec![
                    VariantName {
                        discr: 0,
                        name: "boom".into(),
                        payload: VariantPayload::Unit,
                    },
                    VariantName {
                        discr: 1,
                        name: "code".into(),
                        payload: VariantPayload::Tuple(vec![i, s]),
                    },
                    VariantName {
                        discr: 2,
                        name: "bad".into(),
                        payload: VariantPayload::Fields(vec![("n".into(), i)]),
                    },
                ],
            },
        );
        let src = Src {
            cells: vec![
                vec![Slot::val(0)],
                vec![Slot::val(1), Slot::val(3), Slot::val(0)],
                vec![Slot::val(2), Slot::val(9)],
            ],
            strs: vec![b"host".to_vec()],
        };
        let line = error_line(Slot::val(0), e, &tys, &names, &src).unwrap();
        assert_eq!(line, b"error: app.Error.boom\n");
        let got = render(Slot::val(1), e, &tys, &names, &src).unwrap();
        assert_eq!(got, b"app.Error.code(3, \"host\")");
        let got = render(Slot::val(2), e, &tys, &names, &src).unwrap();
        assert_eq!(got, b"app.Error.bad{ n: 9 }");
    }
}
