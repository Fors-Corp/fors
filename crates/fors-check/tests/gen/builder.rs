//! The program builder: plans the declarations (structs, enums, traits,
//! impls, fns) of one program and registers every callable so later bodies
//! can call earlier ones. Bodies themselves are built by `body.rs`.

use std::collections::HashMap;

use crate::ast::*;
use crate::body::{FnCx, Local};
use crate::rng::Rng;
use crate::types::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CKind {
    Free,
    Assoc,
    Method,
}

/// One callable the generator may emit a call to.
#[derive(Clone, Debug)]
pub struct Callable {
    pub path: String,
    pub kind: CKind,
    /// Variables a call must instantiate: the fn's own generics, plus the
    /// impl's for a method.
    pub vars: Vec<String>,
    pub var_bounds: Vec<(String, Vec<String>)>,
    /// The fn's own generics (the explicit `[..]` arguments), in order.
    pub own: Vec<GParam>,
    /// The receiver's convention and declared type, for a method.
    pub recv: Option<(Conv, Ty)>,
    pub params: Vec<(Conv, String, Ty)>,
    pub ret: Ty,
    pub raises: Option<Ty>,
    pub is_unsafe: bool,
}

impl Callable {
    pub fn sig(&self) -> Sig {
        Sig {
            generics: self.own.clone(),
            params: self.params.clone(),
            ret: self.ret.clone(),
            raises: self.raises.clone(),
        }
    }
}

pub struct Gen {
    pub rng: Rng,
    pub p: Program,
    pub calls: Vec<Callable>,
    pub consts: Vec<(String, Ty)>,
    /// The error enums, by name.
    pub errs: Vec<String>,
    /// Struct names that may appear in a generated signature as a plain type.
    pub n_fns: usize,
}

const PRIM_WEIGHTS: [(Prim, usize); 12] = [
    (Prim::I32, 6),
    (Prim::I64, 4),
    (Prim::U8, 2),
    (Prim::U32, 2),
    (Prim::Usize, 3),
    (Prim::F64, 3),
    (Prim::F32, 1),
    (Prim::Bool, 4),
    (Prim::I8, 1),
    (Prim::I16, 1),
    (Prim::U16, 1),
    (Prim::U64, 1),
];

impl Gen {
    pub fn new(seed: u64) -> Gen {
        Gen {
            rng: Rng::new(seed),
            p: Program::new(seed),
            calls: Vec::new(),
            consts: Vec::new(),
            errs: Vec::new(),
            n_fns: 0,
        }
    }

    pub fn prim(&mut self) -> Prim {
        let w: Vec<usize> = PRIM_WEIGHTS.iter().map(|x| x.1).collect();
        PRIM_WEIGHTS[self.rng.weighted(&w)].0
    }

    pub fn num_prim(&mut self) -> Prim {
        loop {
            let p = self.prim();
            if p.is_num() {
                return p;
            }
        }
    }

    pub fn int_prim(&mut self) -> Prim {
        loop {
            let p = self.prim();
            if p.is_int() {
                return p;
            }
        }
    }

    pub fn gparam(&mut self, name: &str, bounds: &[&str]) -> GParam {
        GParam {
            id: self.p.id(),
            name: name.to_string(),
            bounds: bounds.iter().map(|s| s.to_string()).collect(),
        }
    }

    // ------------------------------------------------------------ planning

    pub fn plan(&mut self) {
        self.plan_consts();
        self.plan_adts();
        self.plan_traits();
        self.plan_impls();
        self.plan_fns();
    }

    fn plan_consts(&mut self) {
        for i in 0..self.rng.range(0, 2) {
            let p = self.num_prim();
            let ty = Ty::Prim(p);
            let id = self.p.id();
            let eid = self.p.id();
            let value = if p.is_float() {
                Expr {
                    id: eid,
                    ty: ty.clone(),
                    kind: EK::Float("2.5".into(), None),
                }
            } else {
                Expr {
                    id: eid,
                    ty: ty.clone(),
                    kind: EK::Int(self.rng.range(1, 20) as u64, None),
                }
            };
            let name = format!("K{i}");
            self.consts.push((name.clone(), ty.clone()));
            self.p.items.push(Item::Const(ConstDecl {
                id,
                name,
                ty,
                value,
            }));
        }
    }

    /// A field or payload type for a declaration with the given generic
    /// parameters: always copyable, never recursive.
    fn field_ty(&mut self, params: &[String], copy_structs: &[String]) -> Ty {
        match self.rng.weighted(&[10, 1, 1, 1, 3, 3]) {
            0 => Ty::Prim(self.prim()),
            1 => Ty::opt(Ty::Prim(self.prim())),
            2 => Ty::Tuple(vec![Ty::Prim(self.prim()), Ty::Prim(self.prim())]),
            3 => Ty::Array(
                Box::new(Ty::Prim(self.num_prim())),
                self.rng.range(2, 4) as u32,
            ),
            4 if !copy_structs.is_empty() => {
                Ty::adt(&copy_structs[self.rng.below(copy_structs.len())])
            }
            5 if !params.is_empty() => Ty::Param(params[self.rng.below(params.len())].clone()),
            _ => Ty::Prim(self.prim()),
        }
    }

    fn marker_impl(&mut self, name: &str, generics: &[GParam]) {
        let gs: Vec<GParam> = generics
            .iter()
            .map(|g| GParam {
                id: self.p.id(),
                name: g.name.clone(),
                bounds: vec!["Copyable".into()],
            })
            .collect();
        let args: Vec<Ty> = generics.iter().map(|g| Ty::Param(g.name.clone())).collect();
        let id = self.p.id();
        let head_id = self.p.id();
        self.p.items.push(Item::Impl(ImplDecl {
            id,
            head_id,
            generics: gs,
            trait_name: Some("Copyable".into()),
            trait_args: Vec::new(),
            self_ty: Ty::Adt(name.to_string(), args),
            assoc: Vec::new(),
            methods: Vec::new(),
        }));
    }

    fn plan_adts(&mut self) {
        let mut copy_plain: Vec<String> = Vec::new();
        for i in 0..self.rng.range(1, 3) {
            let name = format!("S{i}");
            let generic = self.rng.chance(1, 4);
            let generics = if generic {
                vec![self.gparam("T", &[])]
            } else {
                Vec::new()
            };
            let params: Vec<String> = generics.iter().map(|g| g.name.clone()).collect();
            let nf = self.rng.range(1, 4);
            let mut fields = Vec::new();
            for j in 0..nf {
                let ty = if generic && j == 0 {
                    Ty::Param("T".into())
                } else {
                    self.field_ty(&params, &copy_plain)
                };
                fields.push(Field {
                    name: format!("f{j}"),
                    ty,
                });
            }
            let id = self.p.id();
            self.p.items.push(Item::Struct(StructDecl {
                id,
                name: name.clone(),
                generics: generics.clone(),
                fields,
            }));
            // Two thirds of the structs are `Copyable`; the rest are the
            // resource-like types whose values are moved.
            if self.rng.chance(2, 3) {
                self.marker_impl(&name, &generics);
                if !generic {
                    copy_plain.push(name);
                }
            }
        }
        for i in 0..self.rng.range(0, 2) {
            let name = format!("E{i}");
            let generic = self.rng.chance(1, 4);
            let generics = if generic {
                vec![self.gparam("T", &[])]
            } else {
                Vec::new()
            };
            let params: Vec<String> = generics.iter().map(|g| g.name.clone()).collect();
            let nv = self.rng.range(2, 4);
            let mut variants = Vec::new();
            for j in 0..nv {
                let vname = format!("v{}", (b'a' + j as u8) as char);
                let shape = match if j == 0 {
                    self.rng.below(2)
                } else {
                    self.rng.below(3)
                } {
                    0 => VShape::Unit,
                    1 => {
                        let n = self.rng.range(1, 2);
                        let mut ts: Vec<Ty> = (0..n)
                            .map(|_| self.field_ty(&params, &copy_plain))
                            .collect();
                        if generic && j == 1 {
                            ts[0] = Ty::Param("T".into());
                        }
                        VShape::Tuple(ts)
                    }
                    _ => {
                        let n = self.rng.range(1, 2);
                        VShape::Record(
                            (0..n)
                                .map(|k| Field {
                                    name: format!("x{k}"),
                                    ty: self.field_ty(&params, &copy_plain),
                                })
                                .collect(),
                        )
                    }
                };
                variants.push(Variant { name: vname, shape });
            }
            let id = self.p.id();
            self.p.items.push(Item::Enum(EnumDecl {
                id,
                name: name.clone(),
                generics: generics.clone(),
                variants,
            }));
            if self.rng.chance(2, 3) {
                self.marker_impl(&name, &generics);
            }
        }
        // One error enum, for the raising functions.
        if self.rng.chance(2, 3) {
            let name = "Err0".to_string();
            let id = self.p.id();
            let payload = Ty::Prim(self.int_prim());
            self.p.items.push(Item::Enum(EnumDecl {
                id,
                name: name.clone(),
                generics: Vec::new(),
                variants: vec![
                    Variant {
                        name: "bad".into(),
                        shape: VShape::Unit,
                    },
                    Variant {
                        name: "code".into(),
                        shape: VShape::Tuple(vec![payload]),
                    },
                ],
            }));
            self.errs.push(name);
        }
    }

    pub fn struct_names(&self) -> Vec<String> {
        self.p
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Struct(s) => Some(s.name.clone()),
                _ => None,
            })
            .collect()
    }

    pub fn adt_names(&self) -> Vec<String> {
        self.p
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Struct(s) => Some(s.name.clone()),
                Item::Enum(e) if !self.errs.contains(&e.name) => Some(e.name.clone()),
                _ => None,
            })
            .collect()
    }

    /// A `Copyable` closed type usable as a generic argument or a field.
    pub fn closed_copy_ty(&mut self, depth: u32) -> Ty {
        let names = self.adt_names();
        let b = Bounds::new();
        for _ in 0..4 {
            let t = match self.rng.weighted(&[12, 3, 2, 2]) {
                0 => Ty::Prim(self.prim()),
                1 if depth > 0 && !names.is_empty() => {
                    let n = names[self.rng.below(names.len())].clone();
                    let params = self.p.adt_params(&n);
                    let args: Vec<Ty> = params.iter().map(|_| Ty::Prim(self.prim())).collect();
                    Ty::Adt(n, args)
                }
                2 => Ty::opt(Ty::Prim(self.prim())),
                _ => Ty::Prim(self.prim()),
            };
            if self.p.is_copy(&t, &b) {
                return t;
            }
        }
        Ty::Prim(Prim::I32)
    }

    // ------------------------------------------------------------- traits

    fn plan_traits(&mut self) {
        for i in 0..self.rng.range(0, 2) {
            let name = format!("Tr{i}");
            let mut methods = Vec::new();
            for j in 0..self.rng.range(1, 2) {
                let ret = Ty::Prim(self.num_prim());
                let mut params = vec![self.self_param(Conv::Let, None)];
                if self.rng.chance(1, 3) {
                    let ty = Ty::Prim(self.prim());
                    params.push(self.plain_param(Conv::Let, "k", ty));
                }
                methods.push(self.fn_shell(&format!("m{i}_{j}"), params, ret, None, None));
            }
            let id = self.p.id();
            self.p.items.push(Item::Trait(TraitDecl {
                id,
                name: name.clone(),
                methods,
            }));
            // A provided method over the required ones, built with `Self`
            // rigid and only the trait's own methods in scope.
            if self.rng.chance(1, 2) {
                self.add_provided(&name);
            }
        }
    }

    pub fn self_param(&mut self, conv: Conv, ty: Option<Ty>) -> Param {
        Param {
            id: self.p.id(),
            conv,
            name: "self".into(),
            ty,
            ty_id: self.p.id(),
        }
    }

    pub fn plain_param(&mut self, conv: Conv, name: &str, ty: Ty) -> Param {
        Param {
            id: self.p.id(),
            conv,
            name: name.to_string(),
            ty: Some(ty),
            ty_id: self.p.id(),
        }
    }

    pub fn fn_shell(
        &mut self,
        name: &str,
        params: Vec<Param>,
        ret: Ty,
        raises: Option<Ty>,
        body: Option<Block>,
    ) -> FnDecl {
        FnDecl {
            id: self.p.id(),
            name: name.to_string(),
            name_id: self.p.id(),
            sig_id: self.p.id(),
            attrs: Vec::new(),
            generics: Vec::new(),
            params,
            ret,
            ret_id: self.p.id(),
            raises,
            body,
        }
    }

    fn add_provided(&mut self, trait_name: &str) {
        let Some(tr) = self.p.trait_decl(trait_name).cloned() else {
            return;
        };
        let ret = Ty::Prim(self.num_prim());
        let mut cx = FnCx::new(None);
        cx.bounds
            .insert("Self".into(), vec![trait_name.to_string()]);
        cx.locals
            .push(Local::param("self", Ty::Param("Self".into()), Conv::Let));
        let mut params = vec![self.self_param(Conv::Let, None)];
        if self.rng.chance(1, 2) {
            let ty = Ty::Prim(self.prim());
            cx.locals.push(Local::param("n", ty.clone(), Conv::Let));
            params.push(self.plain_param(Conv::Let, "n", ty));
        }
        let body = self.fn_body(&mut cx, &ret);
        let name = format!(
            "p{}_{}",
            trait_name.trim_start_matches("Tr"),
            tr.methods.len()
        );
        let m = self.fn_shell(&name, params, ret, None, Some(body));
        if let Some(Item::Trait(t)) = self
            .p
            .items
            .iter_mut()
            .find(|i| matches!(i, Item::Trait(t) if t.name == trait_name))
        {
            t.methods.push(m);
        }
    }

    // --------------------------------------------------------------- impls

    fn register_method(
        &mut self,
        impl_generics: &[GParam],
        self_ty: &Ty,
        m: &FnDecl,
        sig_self: &Ty,
    ) {
        let (conv, params) = split_receiver(m, sig_self);
        let mut vars: Vec<String> = impl_generics.iter().map(|g| g.name.clone()).collect();
        vars.extend(m.generics.iter().map(|g| g.name.clone()));
        let var_bounds = impl_generics
            .iter()
            .chain(m.generics.iter())
            .map(|g| (g.name.clone(), g.bounds.clone()))
            .collect();
        let path = match (&conv, self_ty) {
            (None, Ty::Adt(n, _)) => format!("{n}.{}", m.name),
            _ => m.name.clone(),
        };
        self.calls.push(Callable {
            path,
            kind: if conv.is_some() {
                CKind::Method
            } else {
                CKind::Assoc
            },
            vars,
            var_bounds,
            own: m.generics.clone(),
            recv: conv.map(|c| (c, sig_self.clone())),
            params,
            ret: m.ret.clone(),
            raises: m.raises.clone(),
            is_unsafe: m.attrs.iter().any(|a| a.starts_with("@unsafe")),
        });
    }

    fn plan_impls(&mut self) {
        let adts = self.adt_names();
        let traits: Vec<String> = self
            .p
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Trait(t) => Some(t.name.clone()),
                _ => None,
            })
            .collect();
        for name in adts {
            let params = self.p.adt_params(&name);
            let generics: Vec<GParam> = params
                .iter()
                .map(|n| GParam {
                    id: self.p.id(),
                    name: n.clone(),
                    bounds: vec!["Copyable".into()],
                })
                .collect();
            let self_ty = Ty::Adt(
                name.clone(),
                params.iter().map(|n| Ty::Param(n.clone())).collect(),
            );
            // The inherent impl.
            if self.rng.chance(3, 4) {
                self.inherent_impl(&generics, &self_ty);
            }
            // Trait impls.
            for tr in &traits {
                if self.rng.chance(1, 2) {
                    self.trait_impl(&generics, &self_ty, tr);
                }
            }
        }
    }

    fn new_cx_for(&self, generics: &[GParam], raises: Option<Ty>) -> FnCx {
        let mut cx = FnCx::new(raises);
        for g in generics {
            cx.bounds.insert(g.name.clone(), g.bounds.clone());
        }
        cx
    }

    fn inherent_impl(&mut self, generics: &[GParam], self_ty: &Ty) {
        let n = self.rng.range(1, 2);
        let mut methods = Vec::new();
        let shown_self = self_ty.clone();
        for j in 0..n {
            let kind = self.rng.weighted(&[5, 3, 2, 2]);
            let name = format!("n{j}");
            let typed_self = self.rng.chance(1, 2);
            let mk_self = |g: &mut Gen, conv: Conv| -> Param {
                let ty = if typed_self {
                    Some(shown_self.clone())
                } else {
                    None
                };
                g.self_param(conv, ty)
            };
            let copy_self = self.p.is_copy(self_ty, &generic_bounds(generics));
            let (conv, assoc) = match kind {
                0 => (Conv::Let, false),
                1 => (Conv::Inout, false),
                2 if !copy_self => (Conv::Sink, false),
                2 => (Conv::Let, false),
                _ => (Conv::Let, true),
            };
            let mut params = Vec::new();
            let mut cx_locals: Vec<Local> = Vec::new();
            if !assoc {
                params.push(mk_self(self, conv));
                cx_locals.push(Local::param("self", self_ty.clone(), conv));
            }
            for k in 0..self.rng.range(0, 2) {
                let pt = self.closed_copy_ty(1);
                let pn = format!("p{k}");
                cx_locals.push(Local::param(&pn, pt.clone(), Conv::Let));
                params.push(self.plain_param(Conv::Let, &pn, pt));
            }
            let ret = if assoc {
                self_ty.clone()
            } else if conv == Conv::Inout && self.rng.chance(1, 2) {
                Ty::Unit
            } else {
                self.closed_copy_ty(1)
            };
            // An associated function constructing `Self` must be able to
            // produce it; a generic one needs a `T` it can copy.
            let mut cx = self.new_cx_for(generics, None);
            cx.self_ty = Some(self_ty.clone());
            cx.locals = cx_locals;
            if assoc
                && has_param(self_ty)
                && !cx.locals.iter().any(|l| matches!(l.ty, Ty::Param(_)))
            {
                // No `T` in scope to build a `Self[T]` from: take one.
                let pt = Ty::Param("T".into());
                cx.locals.push(Local::param("tv", pt.clone(), Conv::Let));
                params.push(self.plain_param(Conv::Let, "tv", pt));
            }
            if !self.producible(&cx, &ret) {
                continue;
            }
            let body = self.fn_body(&mut cx, &ret);
            let m = self.fn_shell(&name, params, ret, None, Some(body));
            methods.push(m);
        }
        if methods.is_empty() {
            return;
        }
        let id = self.p.id();
        let head_id = self.p.id();
        let gs: Vec<GParam> = generics
            .iter()
            .map(|g| GParam {
                id: self.p.id(),
                name: g.name.clone(),
                bounds: g.bounds.clone(),
            })
            .collect();
        // Register after the whole impl is built so a method never calls a
        // sibling that is not yet defined (order is irrelevant to Fors, but
        // the generator keeps its table in definition order).
        for m in &methods {
            self.register_method(generics, self_ty, m, self_ty);
        }
        self.p.items.push(Item::Impl(ImplDecl {
            id,
            head_id,
            generics: gs,
            trait_name: None,
            trait_args: Vec::new(),
            self_ty: self_ty.clone(),
            assoc: Vec::new(),
            methods,
        }));
    }

    fn trait_impl(&mut self, generics: &[GParam], self_ty: &Ty, tr: &str) {
        let Some(decl) = self.p.trait_decl(tr).cloned() else {
            return;
        };
        let mut methods = Vec::new();
        for tm in &decl.methods {
            // Provided methods are inherited; override about a third.
            if tm.body.is_some() && !self.rng.chance(1, 3) {
                continue;
            }
            let typed_self = self.rng.chance(1, 2);
            let mut params = Vec::new();
            let mut cx = self.new_cx_for(generics, None);
            cx.self_ty = Some(self_ty.clone());
            for p in &tm.params {
                if p.name == "self" {
                    let ty = if typed_self {
                        Some(self_ty.clone())
                    } else {
                        None
                    };
                    params.push(self.self_param(p.conv, ty));
                    cx.locals
                        .push(Local::param("self", self_ty.clone(), p.conv));
                } else {
                    let ty = p.ty.clone().unwrap_or(Ty::Unit);
                    cx.locals.push(Local::param(&p.name, ty.clone(), p.conv));
                    params.push(self.plain_param(p.conv, &p.name, ty));
                }
            }
            let body = self.fn_body(&mut cx, &tm.ret);
            methods.push(self.fn_shell(&tm.name, params, tm.ret.clone(), None, Some(body)));
        }
        // Required methods must all be present: add any that were skipped as
        // "provided" (none are, by construction) -- nothing to do.
        for m in &decl.methods {
            if m.body.is_none() && !methods.iter().any(|x| x.name == m.name) {
                return;
            }
        }
        let id = self.p.id();
        let head_id = self.p.id();
        let gs: Vec<GParam> = generics
            .iter()
            .map(|g| GParam {
                id: self.p.id(),
                name: g.name.clone(),
                bounds: g.bounds.clone(),
            })
            .collect();
        for m in &methods {
            self.register_method(generics, self_ty, m, self_ty);
        }
        // Provided methods the impl does not override are callable too.
        for tm in &decl.methods {
            if tm.body.is_some() && !methods.iter().any(|x| x.name == tm.name) {
                let (conv, params) = split_receiver(tm, self_ty);
                let vars: Vec<String> = generics.iter().map(|g| g.name.clone()).collect();
                let var_bounds = generics
                    .iter()
                    .map(|g| (g.name.clone(), g.bounds.clone()))
                    .collect();
                self.calls.push(Callable {
                    path: tm.name.clone(),
                    kind: CKind::Method,
                    vars,
                    var_bounds,
                    own: Vec::new(),
                    recv: conv.map(|c| (c, self_ty.clone())),
                    params,
                    ret: tm.ret.clone(),
                    raises: None,
                    is_unsafe: false,
                });
            }
        }
        self.p.items.push(Item::Impl(ImplDecl {
            id,
            head_id,
            generics: gs,
            trait_name: Some(tr.to_string()),
            trait_args: Vec::new(),
            self_ty: self_ty.clone(),
            assoc: Vec::new(),
            methods,
        }));
    }

    // ------------------------------------------------------------ free fns

    fn plan_fns(&mut self) {
        let n = self.rng.range(3, 6);
        for i in 0..n {
            self.free_fn(i);
        }
    }

    fn free_fn(&mut self, i: usize) {
        let name = format!("g{i}");
        // Shape: plain, generic, raising, or unsafe-numeric.
        let shape = self.rng.weighted(&[10, 4, 3, 1]);
        let mut generics: Vec<GParam> = Vec::new();
        let mut params: Vec<Param> = Vec::new();
        let mut locals: Vec<Local> = Vec::new();
        let mut attrs: Vec<String> = Vec::new();
        let mut raises: Option<Ty> = None;
        let tr_names: Vec<String> = self
            .p
            .items
            .iter()
            .filter_map(|it| match it {
                Item::Trait(t) => Some(t.name.clone()),
                _ => None,
            })
            .collect();
        if shape == 1 {
            // `fn g[T: Copyable + ..](let a: T, let b: T, ..)`.
            let mut bounds = vec!["Copyable"];
            let extra = self.rng.below(4);
            let user: Vec<&String> = tr_names
                .iter()
                .filter(|t| self.p.items.iter().any(|it| matches!(it, Item::Impl(d) if d.trait_name.as_deref() == Some(t.as_str()))))
                .collect();
            let owned_user: Vec<String> = user.iter().map(|s| s.to_string()).collect();
            match extra {
                0 => bounds.push("Add"),
                1 => bounds.push("Ord"),
                2 if !owned_user.is_empty() => {
                    let t = owned_user[self.rng.below(owned_user.len())].clone();
                    generics.push(GParam {
                        id: self.p.id(),
                        name: "T".into(),
                        bounds: vec!["Copyable".into(), t],
                    });
                }
                _ => {}
            }
            if generics.is_empty() {
                generics.push(self.gparam("T", &bounds));
            }
        }
        if shape == 2 && !self.errs.is_empty() {
            raises = Some(Ty::adt(&self.errs[0].clone()));
        }
        let nparams = self.rng.range(1, 4);
        let tpar = Ty::Param("T".into());
        for k in 0..nparams {
            let pname = format!("p{k}");
            if !generics.is_empty() && k < 2 {
                locals.push(Local::param(&pname, tpar.clone(), Conv::Let));
                params.push(self.plain_param(Conv::Let, &pname, tpar.clone()));
                continue;
            }
            let ty = self.closed_copy_ty(1);
            let copy = true;
            let conv = if copy {
                match self.rng.weighted(&[6, 2, 1]) {
                    0 => Conv::Let,
                    1 => Conv::Inout,
                    _ => Conv::Sink,
                }
            } else {
                Conv::Let
            };
            locals.push(Local::param(&pname, ty.clone(), conv));
            params.push(self.plain_param(conv, &pname, ty));
        }
        // A resource-like (non-`Copyable`) parameter now and then: it is
        // borrowed, mutated or consumed, never copied.
        if generics.is_empty() && self.rng.chance(1, 3) {
            let nc: Vec<String> = self
                .struct_names()
                .into_iter()
                .filter(|s| {
                    self.p.adt_params(s).is_empty() && !self.p.is_copy(&Ty::adt(s), &Bounds::new())
                })
                .collect();
            if !nc.is_empty() {
                let s = nc[self.rng.below(nc.len())].clone();
                let conv = match self.rng.weighted(&[3, 2, 3]) {
                    0 => Conv::Let,
                    1 => Conv::Inout,
                    _ => Conv::Sink,
                };
                let k = params.len();
                let pname = format!("p{k}");
                locals.push(Local::param(&pname, Ty::adt(&s), conv));
                params.push(self.plain_param(conv, &pname, Ty::adt(&s)));
            }
        }
        let ret = if !generics.is_empty() && self.rng.chance(2, 3) {
            tpar.clone()
        } else if self.rng.chance(1, 4) {
            Ty::Unit
        } else {
            self.closed_copy_ty(1)
        };
        if shape == 3 {
            attrs.push("@unsafe(invariant: \"the operands never overflow\")".to_string());
        }
        let mut cx = self.new_cx_for(&generics, raises.clone());
        cx.locals = locals;
        cx.unsafe_ok = shape == 3;
        if !self.producible(&cx, &ret) {
            return;
        }
        let body = self.fn_body(&mut cx, &ret);
        let mut f = self.fn_shell(&name, params, ret.clone(), raises.clone(), Some(body));
        f.generics = generics.clone();
        f.attrs = attrs;
        let vars: Vec<String> = generics.iter().map(|g| g.name.clone()).collect();
        let var_bounds = generics
            .iter()
            .map(|g| (g.name.clone(), g.bounds.clone()))
            .collect();
        self.calls.push(Callable {
            path: name,
            kind: CKind::Free,
            vars,
            var_bounds,
            own: generics,
            recv: None,
            params: f
                .params
                .iter()
                .map(|p| (p.conv, p.name.clone(), p.ty.clone().unwrap_or(Ty::Unit)))
                .collect(),
            ret,
            raises,
            is_unsafe: shape == 3,
        });
        self.p.items.push(Item::Fn(f));
        self.n_fns += 1;
    }
}

fn generic_bounds(gs: &[GParam]) -> Bounds {
    gs.iter()
        .map(|g| (g.name.clone(), g.bounds.clone()))
        .collect()
}

/// A method's receiver convention (if its first parameter is `self`) and
/// its remaining parameters.
pub fn split_receiver(m: &FnDecl, self_ty: &Ty) -> (Option<Conv>, Vec<(Conv, String, Ty)>) {
    let mut conv = None;
    let mut params = Vec::new();
    for p in &m.params {
        if p.name == "self" {
            conv = Some(p.conv);
        } else {
            params.push((
                p.conv,
                p.name.clone(),
                p.ty.clone().unwrap_or(self_ty.clone()),
            ));
        }
    }
    (conv, params)
}

/// Builds one program from `seed`.
pub fn generate(seed: u64) -> (Program, Vec<Callable>) {
    let mut g = Gen::new(seed);
    g.plan();
    let calls = std::mem::take(&mut g.calls);
    (g.p, calls)
}

#[allow(dead_code)]
fn _unused(_: HashMap<String, Ty>) {}
