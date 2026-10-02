//! The prelude as ordinary FIR rows (design §6): the primitive types, the
//! built-in generic types of R5, the language-known traits of R21/R23/R24, and
//! the built-in impls of R22/R23 — all hashed, indexed and looked up exactly
//! like user code, so no later rule needs a special case for "is this one of
//! the built-ins".
//!
//! The rows live in a synthetic module whose single path segment is the byte
//! string `#prelude`. It is not a legal Fors identifier, so no user module can
//! collide with it and the canonical encoding (§5.4) of a prelude head is
//! stable across builds without reserving numeric `DefId`s.

use fors_index::Symbol;
use fors_index::decl::DeclKind;
use fors_index::ids::DefId;
use fors_index::interner::Interner;

use crate::Fir;
use crate::defpath::{DeclKey, NO_DECL_KEY, NO_DEF};
use crate::sig::{
    Assoc, Conv, GParam, GParamKind, Member, NO_BOUNDS, NO_CONSTRAINTS, NO_SLOT, Param, SigKind,
};
use crate::ty::{NO_ARGS, NO_TY, PrimKind, TY_NEVER, TY_UNIT, TraitRefId, TyId};

/// The synthetic module segment every prelude declaration lives in.
pub const PRELUDE_MODULE: &[u8] = b"#prelude";

/// The built-in generic types of R5, in the order [`PreludeDefs::generics`]
/// stores them. The `u8` is the declared parameter count.
pub const GENERIC_TYPES: [(&[u8], u8); 11] = [
    (b"Array", 2),
    (b"Slice", 1),
    (b"vector", 2),
    (b"mask", 1),
    (b"Option", 1),
    (b"atomic", 1),
    (b"Own", 2),
    (b"Ref", 2),
    (b"Arena", 2),
    (b"Range", 1),
    (b"RangeIncl", 1),
];

/// The language-known traits of R21, R23 and R24, with their own parameter
/// count (excluding `Self`, which is always ordinal 0).
pub const TRAITS: [(&[u8], u8); 22] = [
    (b"Add", 0),
    (b"Sub", 0),
    (b"Mul", 0),
    (b"Div", 0),
    (b"Rem", 0),
    (b"Neg", 0),
    (b"BitAnd", 0),
    (b"BitOr", 0),
    (b"BitXor", 0),
    (b"Shl", 0),
    (b"Shr", 0),
    (b"Eq", 0),
    (b"Ord", 0),
    (b"Iterator", 0),
    (b"Index", 1),
    (b"IndexMut", 1),
    (b"Copyable", 0),
    (b"Shared", 0),
    (b"Linear", 0),
    (b"Droppable", 0),
    (b"ErrorFrom", 1),
    (b"Sized2Reserved", 0),
];

/// The 15 primitive scalars of R3, in [`PrimKind`] order.
pub const PRIMS: [(&[u8], PrimKind); 15] = [
    (b"i8", PrimKind::I8),
    (b"i16", PrimKind::I16),
    (b"i32", PrimKind::I32),
    (b"i64", PrimKind::I64),
    (b"isize", PrimKind::Isize),
    (b"u8", PrimKind::U8),
    (b"u16", PrimKind::U16),
    (b"u32", PrimKind::U32),
    (b"u64", PrimKind::U64),
    (b"usize", PrimKind::Usize),
    (b"f32", PrimKind::F32),
    (b"f64", PrimKind::F64),
    (b"bool", PrimKind::Bool),
    (b"Str", PrimKind::Str),
    (b"rawptr", PrimKind::RawPtr),
];

/// What a prelude name denotes, as [`PreludeDefs::lookup`] answers it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PreludeEntity {
    /// A primitive scalar (R3) or `never`/`()`: already a type, arity 0.
    Ty(TyId),
    /// A built-in generic type (R5): a nominal head with `arity` parameters.
    Generic { def: DefId, arity: u8 },
    /// A language-known trait (R21/R23/R24): `arity` excludes `Self`.
    Trait { def: DefId, arity: u8 },
    /// A std type the prelude names (ch10 R2) in a build with no `std`
    /// source: its declaration is not in this build, so its arity and its
    /// members are unknown and every rule that would need them stays silent.
    Opaque,
    /// I10 (ch03 R1): a name that spells an integer width v1 does not have
    /// (`i128`, `u128`). It is known so that the checker can say WHY it is
    /// not a type (D0001) instead of the generic unresolved-name error.
    RejectedWidth,
}

/// I10 (ch03 R1): the widths "no 128-bit in v1" rejects, known by name so
/// that the rejection cites the rule.
pub const REJECTED_WIDTHS: [&[u8]; 2] = [b"i128", b"u128"];

/// I10 (ch03 Rules 4 and 6): one of the language-known numeric methods a
/// primitive's prelude inherent impl declares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NumericMethodKind {
    /// `wrap_<op>`, `sat_<op>`, `unchecked_<op>`: `mode` is 0, 1, 2; `op`
    /// indexes [`NUMERIC_OPS`].
    Arith { mode: u8, op: u8 },
    /// `wrap_as[U]`, `sat_as[U]`, `trunc_as[U]`: 0, 1, 2.
    Conv(u8),
}

/// ch03 Rule 4's mode prefixes, in [`NumericMethodKind::Arith`]'s `mode`
/// order.
pub const NUMERIC_MODES: [&[u8]; 3] = [b"wrap_", b"sat_", b"unchecked_"];
/// ch03 Rule 2's trapping operators, by their method suffix, in
/// [`NumericMethodKind::Arith`]'s `op` order. `neg` is unary and declared
/// only on the signed types.
pub const NUMERIC_OPS: [&[u8]; 8] = [
    b"add", b"sub", b"mul", b"div", b"rem", b"shl", b"shr", b"neg",
];
/// ch03 Rule 6's lossy conversions, in [`NumericMethodKind::Conv`] order.
pub const NUMERIC_CONVS: [&[u8]; 3] = [b"wrap_as", b"sat_as", b"trunc_as"];

/// Which ch03 method `name` spells, if any.
pub fn numeric_method_kind(name: &[u8]) -> Option<NumericMethodKind> {
    if let Some(i) = NUMERIC_CONVS.iter().position(|&n| n == name) {
        return Some(NumericMethodKind::Conv(i as u8));
    }
    for (m, prefix) in NUMERIC_MODES.iter().enumerate() {
        if let Some(rest) = name.strip_prefix(*prefix)
            && let Some(o) = NUMERIC_OPS.iter().position(|&n| n == rest)
        {
            return Some(NumericMethodKind::Arith {
                mode: m as u8,
                op: o as u8,
            });
        }
    }
    None
}

/// Every prelude row, built once per build before any user signature is
/// lowered.
pub struct PreludeDefs {
    module: crate::defpath::ModulePathId,
    names: Vec<(Symbol, PreludeEntity)>,
    /// `PRIMS` order.
    pub prims: [TyId; 15],
    /// `GENERIC_TYPES` order.
    pub generics: [DefId; 11],
    /// `TRAITS` order.
    pub traits: [DefId; 22],
    /// `Option`'s `some`/`none` variant ordinals, for the prelude values.
    pub option: DefId,
    pub item_name: Symbol,
    pub output_name: Symbol,
    pub self_name: Symbol,
    /// I10 (ch03 R9): the comptime-only arbitrary-precision types. Nominal
    /// heads with no parameters and no members; a value of one exists only
    /// at compile time.
    pub comptime_int: DefId,
    pub comptime_float: DefId,
    /// I10 (ch03 R20): the reserved scalable vector `SVec[T]`.
    pub svec: DefId,
    /// I10 (ch03 Rules 4 and 6): each numeric primitive's inherent impl
    /// declaring its explicit-arithmetic and conversion methods, as `(self
    /// type, impl)`. The impl rows join the index in
    /// [`push_builtin_impls`]; the declarations are made in [`build`] so
    /// their `DefId`s are the prelude's (stable across revisions).
    pub numeric_impls: Vec<(TyId, DefId)>,
}

/// Index into [`PreludeDefs::traits`] for each language-known trait.
pub mod tr {
    pub const ADD: usize = 0;
    pub const SUB: usize = 1;
    pub const MUL: usize = 2;
    pub const DIV: usize = 3;
    pub const REM: usize = 4;
    pub const NEG: usize = 5;
    pub const BITAND: usize = 6;
    pub const BITOR: usize = 7;
    pub const BITXOR: usize = 8;
    pub const SHL: usize = 9;
    pub const SHR: usize = 10;
    pub const EQ: usize = 11;
    pub const ORD: usize = 12;
    pub const ITERATOR: usize = 13;
    pub const INDEX: usize = 14;
    pub const INDEXMUT: usize = 15;
    pub const COPYABLE: usize = 16;
    pub const SHARED: usize = 17;
    pub const LINEAR: usize = 18;
    pub const DROPPABLE: usize = 19;
    pub const ERRORFROM: usize = 20;
}

/// Index into [`PreludeDefs::generics`].
pub mod gty {
    pub const ARRAY: usize = 0;
    pub const SLICE: usize = 1;
    pub const VECTOR: usize = 2;
    pub const MASK: usize = 3;
    pub const OPTION: usize = 4;
    pub const ATOMIC: usize = 5;
    pub const OWN: usize = 6;
    pub const REF: usize = 7;
    pub const ARENA: usize = 8;
    pub const RANGE: usize = 9;
    pub const RANGEINCL: usize = 10;
}

/// The std types ch10 R2 puts in the prelude. They are declared in package
/// `std`; in a build without it they are [`PreludeEntity::Opaque`].
const OPAQUE: [&[u8]; 8] = [
    b"Allocator",
    b"AllocError",
    b"PageAllocator",
    b"Buffer",
    b"Vec",
    b"Map",
    b"String",
    b"Utf8Error",
];

impl PreludeDefs {
    /// What `name` denotes, or `None` when it is not a prelude name.
    pub fn lookup(&self, name: Symbol) -> Option<PreludeEntity> {
        self.names
            .binary_search_by_key(&name.0, |&(s, _)| s.0)
            .ok()
            .map(|i| self.names[i].1)
    }

    /// Whether `def` is one of the language-known traits, and which.
    pub fn trait_index(&self, def: DefId) -> Option<usize> {
        self.traits.iter().position(|&d| d == def)
    }

    /// Whether `def` is one of the built-in generic types, and which.
    pub fn generic_index(&self, def: DefId) -> Option<usize> {
        self.generics.iter().position(|&d| d == def)
    }

    /// The trait reference `Tr` with no arguments of its own (`Self` is not an
    /// argument: it is the subject).
    pub fn trait_ref(&self, fir: &mut Fir, which: usize) -> TraitRefId {
        fir.tys.intern_trait_ref(self.traits[which], NO_ARGS)
    }

    /// The module every prelude declaration lives in.
    pub fn module(&self) -> crate::defpath::ModulePathId {
        self.module
    }
}

fn decl(
    fir: &mut Fir,
    module: crate::defpath::ModulePathId,
    kind: DeclKind,
    name: Symbol,
    sig: SigKind,
) -> DefId {
    let key = fir.keys.intern(DeclKey {
        parent: NO_DECL_KEY,
        module,
        kind,
        name: Some(name),
        disamb: 0,
    });
    fir.declare(key, sig)
}

fn method(
    fir: &mut Fir,
    module: crate::defpath::ModulePathId,
    owner: DefId,
    owner_key: crate::defpath::DeclKeyId,
    name: Symbol,
    params: &[Param],
    result: TyId,
    receiver: bool,
    // MARC: verification of I2 (2026-09-20). R21's language-known `at` and
    // `at_mut` return `scoped(self) Self.Output`; the rows said nothing, so
    // once R17 compared the `scoped` designation every user `Index` impl
    // failed against its own trait. The designated slot is passed in.
    scoped: u8,
) -> DefId {
    let key = fir.keys.intern(DeclKey {
        parent: owner_key,
        module,
        kind: DeclKind::Fn,
        name: Some(name),
        disamb: 0,
    });
    let def = fir.declare(key, SigKind::Fn);
    let sig = fir.sigs.fn_sigs.push(
        params,
        result,
        NO_TY,
        scoped,
        if receiver { 0 } else { NO_SLOT },
        (u32::MAX, u32::MAX),
        0,
    );
    fir.sigs.set_fn_sig(def, sig);
    let _ = owner;
    def
}

/// Builds every prelude row into `fir` (design §6). Runs once per build,
/// before any user signature is lowered, so prelude `DefId`s are the lowest
/// rows and are reproducible.
pub fn build(fir: &mut Fir, names: &mut Interner) -> PreludeDefs {
    let seg = names.intern(PRELUDE_MODULE);
    let module = fir.keys.paths.intern(&[seg]);
    let mut table: Vec<(Symbol, PreludeEntity)> = Vec::new();

    // R3: the primitives. `never` and `()` are R4's and are already interned.
    let mut prims = [TY_UNIT; 15];
    for (i, (n, k)) in PRIMS.iter().enumerate() {
        let t = fir.tys.prim(*k);
        prims[i] = t;
        let s = names.intern(n);
        table.push((s, PreludeEntity::Ty(t)));
    }
    let never = names.intern(b"never");
    table.push((never, PreludeEntity::Ty(TY_NEVER)));

    // R5: the built-in generic types. `Option` is an enum with `some(T)` and
    // `none`; the rest are opaque heads whose arguments are all this rule
    // gives them.
    let mut generics = [NO_DEF; 11];
    for (i, (n, arity)) in GENERIC_TYPES.iter().enumerate() {
        let s = names.intern(n);
        let kind = if *n == b"Option" {
            DeclKind::Enum
        } else {
            DeclKind::Struct
        };
        let sig = if *n == b"Option" {
            SigKind::Enum
        } else {
            SigKind::Struct
        };
        let def = decl(fir, module, kind, s, sig);
        generics[i] = def;
        table.push((s, PreludeEntity::Generic { def, arity: *arity }));
    }
    // Their generic parameters: a type parameter unless the name says
    // otherwise (`N: usize` on Array/vector/mask, `A: brand` on Own/Ref/Arena).
    let usize_ty = prims[9];
    for (i, (n, arity)) in GENERIC_TYPES.iter().enumerate() {
        let mut ps: Vec<GParam> = Vec::new();
        for o in 0..*arity {
            let pname = names.intern(if o == 0 { b"T" } else { b"N" });
            let kind = match (*n, o) {
                (b"Array", 1) | (b"vector", 1) => GParamKind::Const { ty: usize_ty },
                (b"mask", 0) => GParamKind::Const { ty: usize_ty },
                (b"Own", 1) | (b"Ref", 1) | (b"Arena", 1) => GParamKind::Brand,
                _ => GParamKind::Type,
            };
            ps.push(GParam {
                name: pname,
                kind,
                bounds: NO_BOUNDS,
            });
        }
        let g = fir.sigs.generics_store.push(&ps, NO_CONSTRAINTS);
        fir.sigs.set_generics(generics[i], g);
    }
    // `Option[T]`'s variants.
    let option = generics[gty::OPTION];
    let t0 = fir.tys.param(option, 0);
    let some = names.intern(b"some");
    let none = names.intern(b"none");
    let args = fir.tys.intern_args(&[t0]);
    let vs = fir.sigs.member_store.push(&[
        Member::tuple_variant(some, args),
        Member::unit_variant(none),
    ]);
    fir.sigs.set_members(option, vs);

    // R21/R23/R24: the language-known traits.
    let item_name = names.intern(b"Item");
    let output_name = names.intern(b"Output");
    let self_name = names.intern(b"Self");
    // MARC: verification of I2 (2026-09-20). The language-known receivers
    // were named `Self` (the TYPE's name); every user signature names its
    // receiver `self`, and R17 compares parameter names, so the prelude's
    // rows must say `self` too.
    let recv_name = names.intern(b"self");
    let rhs_name = names.intern(b"rhs");
    let i_name = names.intern(b"i");
    let e_name = names.intern(b"e");
    let mut traits = [NO_DEF; 22];
    for (i, (n, arity)) in TRAITS.iter().enumerate() {
        if *n == b"Sized2Reserved" {
            continue;
        }
        let s = names.intern(n);
        let def = decl(fir, module, DeclKind::Trait, s, SigKind::Trait);
        traits[i] = def;
        table.push((s, PreludeEntity::Trait { def, arity: *arity }));
    }
    // A trait's own gparam list is `[Self, P1, ..]` (§5.2): `Self`'s one bound
    // is the trait itself with its own parameters (R8).
    for (i, (n, arity)) in TRAITS.iter().enumerate() {
        if *n == b"Sized2Reserved" {
            continue;
        }
        let def = traits[i];
        let own_args: Vec<TyId> = (0..*arity)
            .map(|o| fir.tys.param(def, (o + 1) as u16))
            .collect();
        let a = fir.tys.intern_args(&own_args);
        let tr = fir.tys.intern_trait_ref(def, a);
        let self_bounds = fir.sigs.bounds.intern(&[tr]);
        let mut ps = vec![GParam {
            name: recv_name,
            kind: GParamKind::Type,
            bounds: self_bounds,
        }];
        for o in 0..*arity {
            let pname = names.intern(if o == 0 { b"I" } else { b"J" });
            ps.push(GParam {
                name: pname,
                kind: GParamKind::Type,
                bounds: NO_BOUNDS,
            });
        }
        let g = fir.sigs.generics_store.push(&ps, NO_CONSTRAINTS);
        fir.sigs.set_generics(def, g);
    }

    // The trait items. `Self` inside a trait is `Param{trait, 0}` (R8).
    let mut items: Vec<(usize, Vec<Member>)> = Vec::new();
    for (i, (n, _)) in TRAITS.iter().enumerate() {
        if traits[i] == NO_DEF {
            continue;
        }
        let def = traits[i];
        let key = fir.defs.key_of(def);
        let self_ty = fir.tys.param(def, 0);
        let bool_ty = prims[12];
        let mut ms: Vec<Member> = Vec::new();
        let binary: Option<&[u8]> = match *n {
            b"Add" => Some(b"add"),
            b"Sub" => Some(b"sub"),
            b"Mul" => Some(b"mul"),
            b"Div" => Some(b"div"),
            b"Rem" => Some(b"rem"),
            b"BitAnd" => Some(b"bitand"),
            b"BitOr" => Some(b"bitor"),
            b"BitXor" => Some(b"bitxor"),
            b"Shl" => Some(b"shl"),
            b"Shr" => Some(b"shr"),
            _ => None,
        };
        if let Some(m) = binary {
            let mn = names.intern(m);
            let ps = [
                Param {
                    name: recv_name,
                    conv: Conv::Let,
                    ty: self_ty,
                },
                Param {
                    name: rhs_name,
                    conv: Conv::Let,
                    ty: self_ty,
                },
            ];
            let d = method(fir, module, def, key, mn, &ps, self_ty, true, NO_SLOT);
            ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
        }
        match *n {
            b"Neg" => {
                let mn = names.intern(b"neg");
                let ps = [Param {
                    name: recv_name,
                    conv: Conv::Let,
                    ty: self_ty,
                }];
                let d = method(fir, module, def, key, mn, &ps, self_ty, true, NO_SLOT);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            b"Eq" => {
                let mn = names.intern(b"eq");
                let ps = [
                    Param {
                        name: recv_name,
                        conv: Conv::Let,
                        ty: self_ty,
                    },
                    Param {
                        name: rhs_name,
                        conv: Conv::Let,
                        ty: self_ty,
                    },
                ];
                let d = method(fir, module, def, key, mn, &ps, bool_ty, true, NO_SLOT);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            b"Ord" => {
                for m in [b"lt".as_slice(), b"le".as_slice()] {
                    let mn = names.intern(m);
                    let ps = [
                        Param {
                            name: recv_name,
                            conv: Conv::Let,
                            ty: self_ty,
                        },
                        Param {
                            name: rhs_name,
                            conv: Conv::Let,
                            ty: self_ty,
                        },
                    ];
                    let d = method(fir, module, def, key, mn, &ps, bool_ty, true, NO_SLOT);
                    ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
                }
            }
            b"Iterator" => {
                // `type Item: Droppable; fn next(inout self) -> Option[Self.Item];`
                let dr = fir.tys.intern_trait_ref(traits[tr::DROPPABLE], NO_ARGS);
                let bounds = fir.sigs.bounds.intern(&[dr]);
                let a = fir.sigs.assocs.push(&[Assoc {
                    name: item_name,
                    bounds,
                    rhs: NO_TY,
                }]);
                fir.sigs.set_assoc(def, a);
                let own = fir.tys.intern_trait_ref(def, NO_ARGS);
                let pk = fir.tys.intern_proj_key(own, item_name);
                let item = fir.tys.proj(self_ty, pk);
                let opt = fir.tys.nominal_of(option, &[item]);
                let mn = names.intern(b"next");
                let ps = [Param {
                    name: recv_name,
                    conv: Conv::Inout,
                    ty: self_ty,
                }];
                let d = method(fir, module, def, key, mn, &ps, opt, true, NO_SLOT);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            b"Index" => {
                let a = fir.sigs.assocs.push(&[Assoc {
                    name: output_name,
                    bounds: NO_BOUNDS,
                    rhs: NO_TY,
                }]);
                fir.sigs.set_assoc(def, a);
                let i_ty = fir.tys.param(def, 1);
                let iargs = fir.tys.intern_args(&[i_ty]);
                let own = fir.tys.intern_trait_ref(def, iargs);
                let pk = fir.tys.intern_proj_key(own, output_name);
                let out = fir.tys.proj(self_ty, pk);
                let mn = names.intern(b"at");
                let ps = [
                    Param {
                        name: recv_name,
                        conv: Conv::Let,
                        ty: self_ty,
                    },
                    Param {
                        name: i_name,
                        conv: Conv::Let,
                        ty: i_ty,
                    },
                ];
                let d = method(fir, module, def, key, mn, &ps, out, true, 0);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            b"IndexMut" => {
                // R21: `IndexMut[I]` declares no `Output`; inside it
                // `Self.Output` denotes `Index[I]`'s.
                let i_ty = fir.tys.param(def, 1);
                let iargs = fir.tys.intern_args(&[i_ty]);
                let index_ref = fir.tys.intern_trait_ref(traits[tr::INDEX], iargs);
                let pk = fir.tys.intern_proj_key(index_ref, output_name);
                let out = fir.tys.proj(self_ty, pk);
                let mn = names.intern(b"at_mut");
                let ps = [
                    Param {
                        name: recv_name,
                        conv: Conv::Inout,
                        ty: self_ty,
                    },
                    Param {
                        name: i_name,
                        conv: Conv::Let,
                        ty: i_ty,
                    },
                ];
                let d = method(fir, module, def, key, mn, &ps, out, true, 0);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            // MARC: design §6 writes `fn from(sink e: E) -> Self` and says the
            // shape is "fixed when ch02's std surface lands". It has: the ch02
            // corpus (`error-from-single-hop-accepted`,
            // `error-from-two-hops-rejected`) writes `fn from(let e: E) ->
            // Self`, and an accepted corpus test outranks a provisional line
            // in the design. `let` it is.
            b"ErrorFrom" => {
                let e_ty = fir.tys.param(def, 1);
                let mn = names.intern(b"from");
                let ps = [Param {
                    name: e_name,
                    conv: Conv::Let,
                    ty: e_ty,
                }];
                let d = method(fir, module, def, key, mn, &ps, self_ty, false, NO_SLOT);
                ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
            }
            _ => {}
        }
        items.push((i, ms));
    }
    for (i, ms) in items {
        if !ms.is_empty() {
            let l = fir.sigs.member_store.push(&ms);
            fir.sigs.set_members(traits[i], l);
        }
    }

    // ch10 R2's prelude-named std types: opaque unless package `std` is in
    // the build, in which case the resolver binds them to real items and this
    // row is never consulted.
    for n in OPAQUE {
        let s = names.intern(n);
        table.push((s, PreludeEntity::Opaque));
    }

    // I10 (ch03 R9, R20): `comptime_int`, `comptime_float` and `SVec[T]`.
    let mut ch03_head = |fir: &mut Fir, name: &[u8], arity: u8| -> DefId {
        let s = names.intern(name);
        let def = decl(fir, module, DeclKind::Struct, s, SigKind::Struct);
        let mut ps: Vec<GParam> = Vec::new();
        for _ in 0..arity {
            ps.push(GParam {
                name: names.intern(b"T"),
                kind: GParamKind::Type,
                bounds: NO_BOUNDS,
            });
        }
        let g = fir.sigs.generics_store.push(&ps, NO_CONSTRAINTS);
        fir.sigs.set_generics(def, g);
        let l = fir.sigs.member_store.push(&[]);
        fir.sigs.set_members(def, l);
        table.push((s, PreludeEntity::Generic { def, arity }));
        def
    };
    let comptime_int = ch03_head(fir, b"comptime_int", 0);
    let comptime_float = ch03_head(fir, b"comptime_float", 0);
    let svec = ch03_head(fir, b"SVec", 1);
    for n in REJECTED_WIDTHS {
        let s = names.intern(n);
        table.push((s, PreludeEntity::RejectedWidth));
    }

    // I10 (ch03 Rules 4 and 6): every numeric primitive's inherent impl.
    // Rule 4's `wrap_`/`sat_`/`unchecked_<op>` exist for the INTEGER types
    // (Rule 2's trapping operators are theirs; a float never traps), `neg`
    // on the signed ones; Rule 6's three conversions on every numeric type,
    // generic in the target `U` (whose numeric-ness the checker enforces at
    // the call, D0006: no prelude trait says "numeric").
    let rhs_name2 = names.intern(b"rhs");
    let recv_name2 = names.intern(b"self");
    let u_name = names.intern(b"U");
    let mut numeric_impls: Vec<(TyId, DefId)> = Vec::new();
    for (i, &(_, k)) in PRIMS.iter().enumerate() {
        if !(k.is_integer() || k.is_float()) {
            continue;
        }
        let t = prims[i];
        let ikey = fir.keys.intern(DeclKey {
            parent: NO_DECL_KEY,
            module,
            kind: DeclKind::Impl,
            name: None,
            // Distinct from `push_builtin_impls`' `0..` range.
            disamb: 0x4000_0000 + i as u32,
        });
        let imp = fir.declare(ikey, SigKind::Impl);
        fir.sigs.set_self_ty(imp, t);
        let mut ms: Vec<Member> = Vec::new();
        if k.is_integer() {
            let signed = matches!(
                k,
                PrimKind::I8 | PrimKind::I16 | PrimKind::I32 | PrimKind::I64 | PrimKind::Isize
            );
            for mode in NUMERIC_MODES {
                for op in NUMERIC_OPS {
                    let unary = op == b"neg";
                    if unary && !signed {
                        continue;
                    }
                    let mut full = mode.to_vec();
                    full.extend_from_slice(op);
                    let mn = names.intern(&full);
                    let recv = Param {
                        name: recv_name2,
                        conv: Conv::Let,
                        ty: t,
                    };
                    let rhs = Param {
                        name: rhs_name2,
                        conv: Conv::Let,
                        ty: t,
                    };
                    let ps: &[Param] = if unary { &[recv] } else { &[recv, rhs] };
                    let d = method(fir, module, imp, ikey, mn, ps, t, true, NO_SLOT);
                    ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
                }
            }
        }
        for conv in NUMERIC_CONVS {
            let mn = names.intern(conv);
            let key = fir.keys.intern(DeclKey {
                parent: ikey,
                module,
                kind: DeclKind::Fn,
                name: Some(mn),
                disamb: 0,
            });
            let d = fir.declare(key, SigKind::Fn);
            let g = fir.sigs.generics_store.push(
                &[GParam {
                    name: u_name,
                    kind: GParamKind::Type,
                    bounds: NO_BOUNDS,
                }],
                NO_CONSTRAINTS,
            );
            fir.sigs.set_generics(d, g);
            let u = fir.tys.param(d, 0);
            let sig = fir.sigs.fn_sigs.push(
                &[Param {
                    name: recv_name2,
                    conv: Conv::Let,
                    ty: t,
                }],
                u,
                NO_TY,
                NO_SLOT,
                0,
                (u32::MAX, u32::MAX),
                0,
            );
            fir.sigs.set_fn_sig(d, sig);
            ms.push(Member::item(mn, crate::sig::VIS_PUBLIC, d));
        }
        let l = fir.sigs.member_store.push(&ms);
        fir.sigs.set_members(imp, l);
        numeric_impls.push((t, imp));
    }

    table.sort_by_key(|&(s, _)| s.0);
    table.dedup_by_key(|&mut (s, _)| s.0);
    PreludeDefs {
        module,
        names: table,
        prims,
        generics,
        traits,
        option,
        item_name,
        output_name,
        self_name,
        comptime_int,
        comptime_float,
        svec,
        numeric_impls,
    }
}

/// R22's built-in impls, as ordinary `ImplIndex` rows. They are what makes
/// `holds(i32, Add)` and `holds(f64, Ord)` a probe rather than a special case.
///
/// MARC: the built-in impls over the GENERIC heads (`Array[T, N]: Index[usize]`
/// and its siblings) need a generics row per synthetic impl and a `type Output
/// = T;` the normaliser will read; they are the first thing I4 adds, and no
/// I2 rule asks a question they answer (`indexmut-without-index-rejected` asks
/// whether a USER struct implements `Index`, which is a bucket miss either
/// way). Adding them here without their associated-type rows would make R17's
/// completeness check see an impl of `Index` that defines no `Output`.
pub fn push_builtin_impls(fir: &mut Fir, p: &PreludeDefs, index: &mut crate::impls::ImplIndex) {
    let ints = [
        PrimKind::I8,
        PrimKind::I16,
        PrimKind::I32,
        PrimKind::I64,
        PrimKind::Isize,
        PrimKind::U8,
        PrimKind::U16,
        PrimKind::U32,
        PrimKind::U64,
        PrimKind::Usize,
    ];
    let signed = [
        PrimKind::I8,
        PrimKind::I16,
        PrimKind::I32,
        PrimKind::I64,
        PrimKind::Isize,
    ];
    let floats = [PrimKind::F32, PrimKind::F64];
    let arith = [tr::ADD, tr::SUB, tr::MUL, tr::DIV, tr::REM];
    let bitwise = [tr::BITAND, tr::BITOR, tr::BITXOR, tr::SHL, tr::SHR];
    let mut order = 0u32;
    let mut add =
        |fir: &mut Fir, index: &mut crate::impls::ImplIndex, self_ty: TyId, which: usize| {
            let key = fir.keys.intern(DeclKey {
                parent: NO_DECL_KEY,
                module: p.module,
                kind: DeclKind::Impl,
                name: None,
                disamb: order,
            });
            let def = fir.declare(key, SigKind::Impl);
            fir.sigs.set_self_ty(def, self_ty);
            let tref = fir.tys.intern_trait_ref(p.traits[which], NO_ARGS);
            fir.sigs.set_trait_ref(def, tref);
            let head = fir.tys.head_key(self_ty);
            index.push(crate::impls::ImplRow {
                def,
                trait_def: p.traits[which],
                inherent: false,
                trait_args: NO_ARGS,
                self_ty,
                head,
                order,
            });
            order += 1;
        };
    for k in ints {
        let t = fir.tys.prim(k);
        for w in arith
            .iter()
            .chain(bitwise.iter())
            .chain([tr::EQ, tr::ORD, tr::COPYABLE].iter())
        {
            add(fir, index, t, *w);
        }
    }
    for k in signed {
        let t = fir.tys.prim(k);
        add(fir, index, t, tr::NEG);
    }
    for k in floats {
        let t = fir.tys.prim(k);
        for w in arith
            .iter()
            .chain([tr::NEG, tr::EQ, tr::ORD, tr::COPYABLE].iter())
        {
            add(fir, index, t, *w);
        }
    }
    let b = fir.tys.prim(PrimKind::Bool);
    add(fir, index, b, tr::EQ);
    add(fir, index, b, tr::COPYABLE);
    for k in [PrimKind::Str, PrimKind::RawPtr] {
        let t = fir.tys.prim(k);
        add(fir, index, t, tr::COPYABLE);
        add(fir, index, t, tr::EQ);
    }
    add(fir, index, TY_UNIT, tr::COPYABLE);
    add(fir, index, TY_NEVER, tr::COPYABLE);
    // I10 (ch03 R9): the comptime types compute like the scalars they stand
    // for (arbitrary precision, at compile time), and are copied.
    for def in [p.comptime_int, p.comptime_float] {
        let t = fir.tys.nominal(def, NO_ARGS);
        for w in arith
            .iter()
            .chain([tr::NEG, tr::EQ, tr::ORD, tr::COPYABLE].iter())
        {
            add(fir, index, t, *w);
        }
    }
    // I10 (ch03 Rules 4 and 6): the numeric primitives' inherent impls,
    // declared by `build`.
    for &(self_ty, def) in &p.numeric_impls {
        let head = fir.tys.head_key(self_ty);
        index.push(crate::impls::ImplRow {
            def,
            trait_def: NO_DEF,
            inherent: true,
            trait_args: NO_ARGS,
            self_ty,
            head,
            order,
        });
        order += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_prelude_name_resolves_to_one_row() {
        let mut names = Interner::new();
        let mut fir = Fir::new();
        let p = build(&mut fir, &mut names);
        for (n, _) in PRIMS {
            let s = names.intern(n);
            assert!(
                matches!(p.lookup(s), Some(PreludeEntity::Ty(_))),
                "{}",
                String::from_utf8_lossy(n)
            );
        }
        for (n, arity) in GENERIC_TYPES {
            let s = names.intern(n);
            match p.lookup(s) {
                Some(PreludeEntity::Generic { def, arity: a }) => {
                    assert_eq!(a, arity);
                    assert_eq!(
                        fir.sigs.generics_store.count(fir.sigs.generics(def)),
                        arity as usize
                    );
                }
                other => panic!("{}: {other:?}", String::from_utf8_lossy(n)),
            }
        }
        for (n, arity) in TRAITS {
            if n == b"Sized2Reserved" {
                continue;
            }
            let s = names.intern(n);
            match p.lookup(s) {
                // A trait's own list is `[Self, P1..]`, so the count is arity + 1.
                Some(PreludeEntity::Trait { def, arity: a }) => {
                    assert_eq!(a, arity);
                    assert_eq!(
                        fir.sigs.generics_store.count(fir.sigs.generics(def)),
                        arity as usize + 1
                    );
                }
                other => panic!("{}: {other:?}", String::from_utf8_lossy(n)),
            }
        }
    }

    #[test]
    fn iterator_declares_item_bounded_by_droppable() {
        let mut names = Interner::new();
        let mut fir = Fir::new();
        let p = build(&mut fir, &mut names);
        let it = p.traits[tr::ITERATOR];
        let a = fir.sigs.assoc(it);
        assert_eq!(fir.sigs.assocs.count(a), 1);
        let row = fir.sigs.assocs.get(a, 0);
        assert_eq!(row.name, p.item_name);
        let bounds = fir.sigs.bounds.get(row.bounds);
        assert_eq!(bounds.len(), 1);
        assert_eq!(fir.tys.trait_ref(bounds[0]).0, p.traits[tr::DROPPABLE]);
    }
}
