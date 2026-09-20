//! Rendering a [`TyId`] back into source-like text for a diagnostic
//! (design §4.1's `display.rs`, placed in `fors-check` because printing a
//! nominal head's name needs the build's `DefTable` and `Interner`, neither
//! of which `fors-fir` may depend on).
//!
//! Nothing here decides anything: the text is for the reader.

use fors_fir::prelude::{GENERIC_TYPES, PRIMS, TRAITS};
use fors_fir::ty::{
    ArgsId, BrandKind, PrimKind, ProjKeyId, Quals, TY_ERROR, TY_NEVER, TY_UNIT, TyId, TyTag,
};
use fors_index::ids::DefId;

use crate::wf::Wf;

/// How deep a rendered type may nest before it is elided. A diagnostic that
/// prints a 40-deep type has already failed the reader.
const SHOW_DEPTH_MAX: u32 = 8;

impl Wf<'_> {
    /// `t` as the programmer would write it.
    pub fn show(&self, t: TyId) -> String {
        let mut s = String::new();
        self.show_into(t, 0, &mut s);
        s
    }

    fn show_into(&self, t: TyId, depth: u32, out: &mut String) {
        if depth > SHOW_DEPTH_MAX {
            out.push_str("...");
            return;
        }
        if t == fors_fir::ty::NO_TY {
            out.push_str("<none>");
            return;
        }
        let q = self.fir.tys.quals(t);
        if !q.is_none() {
            if q.is_iso() {
                out.push_str("iso ");
            }
            if q.is_imm() {
                out.push_str("imm ");
            }
            if q.is_secret() {
                out.push_str("secret ");
            }
        }
        let _ = Quals::NONE;
        match t {
            TY_ERROR => {
                out.push_str("<error>");
                return;
            }
            TY_UNIT => {
                out.push_str("()");
                return;
            }
            TY_NEVER => {
                out.push_str("never");
                return;
            }
            _ => {}
        }
        match self.fir.tys.tag(t) {
            TyTag::Error => out.push_str("<error>"),
            TyTag::Unit => out.push_str("()"),
            TyTag::Never => out.push_str("never"),
            TyTag::Prim => {
                let k = PrimKind::from_u8(self.fir.tys.a(t) as u8);
                let name = k
                    .and_then(|k| PRIMS.iter().find(|&&(_, p)| p == k).map(|&(n, _)| n))
                    .unwrap_or(b"<prim>".as_slice());
                out.push_str(&String::from_utf8_lossy(name));
            }
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(t));
                out.push_str(&self.head_name(def));
                self.show_args(ArgsId(self.fir.tys.b(t)), depth, out);
            }
            TyTag::Tuple => {
                let args = self.fir.tys.args(ArgsId(self.fir.tys.b(t))).to_vec();
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    self.show_into(*a, depth + 1, out);
                }
                if args.len() == 1 {
                    out.push(',');
                }
                out.push(')');
            }
            TyTag::Fn => {
                let id = fors_fir::ty::FnTyId(self.fir.tys.a(t));
                let (convs, ps) = self.fir.tys.fn_tys().params(id);
                let (convs, ps) = (convs.to_vec(), ps.to_vec());
                out.push_str(if self.fir.tys.fn_tys().is_closure(id) {
                    "closure("
                } else {
                    "fn("
                });
                for (i, p) in ps.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(match convs[i] {
                        fors_fir::sig::Conv::Let => "let ",
                        fors_fir::sig::Conv::Inout => "inout ",
                        fors_fir::sig::Conv::Sink => "sink ",
                        fors_fir::sig::Conv::Set => "set ",
                    });
                    self.show_into(*p, depth + 1, out);
                }
                out.push(')');
                let r = self.fir.tys.fn_tys().result(id);
                if r != TY_UNIT {
                    out.push_str(" -> ");
                    self.show_into(r, depth + 1, out);
                }
                let e = self.fir.tys.fn_tys().raises(id);
                if e != fors_fir::ty::NO_TY {
                    out.push_str(" raises ");
                    self.show_into(e, depth + 1, out);
                }
            }
            TyTag::Dyn => {
                let (def, args) = self
                    .fir
                    .tys
                    .trait_ref(fors_fir::ty::TraitRefId(self.fir.tys.a(t)));
                out.push_str("dyn ");
                out.push_str(&self.head_name(def));
                self.show_args(args, depth, out);
            }
            TyTag::Param => {
                let owner = DefId(self.fir.tys.a(t));
                let ord = self.fir.tys.b(t) as usize;
                let g = self.fir.sigs.generics(owner);
                if ord < self.fir.sigs.generics_store.count(g) {
                    let p = self.fir.sigs.generics_store.param(g, ord);
                    out.push_str(&String::from_utf8_lossy(self.names.resolve(p.name)));
                } else {
                    out.push_str("<param>");
                }
            }
            TyTag::Proj => {
                let head = TyId(self.fir.tys.a(t));
                let (_, name) = self.fir.tys.proj_key(ProjKeyId(self.fir.tys.b(t)));
                self.show_into(head, depth + 1, out);
                out.push('.');
                out.push_str(&String::from_utf8_lossy(self.names.resolve(name)));
            }
            TyTag::Brand => {
                let row = self.fir.tys.brand(fors_fir::ty::BrandId(self.fir.tys.b(t)));
                out.push_str(match row.kind() {
                    BrandKind::Fresh => "<fresh brand>",
                    BrandKind::Param => "<brand parameter>",
                });
            }
            TyTag::ConstVal => {
                let v = self
                    .fir
                    .tys
                    .const_value(fors_fir::ty::ConstId(self.fir.tys.a(t)));
                match v {
                    fors_fir::ConstValue::I(i) => out.push_str(&i.to_string()),
                    fors_fir::ConstValue::B(b) => out.push_str(if b { "true" } else { "false" }),
                    fors_fir::ConstValue::S(s) => {
                        out.push('"');
                        out.push_str(&String::from_utf8_lossy(self.names.resolve(s)));
                        out.push('"');
                    }
                }
            }
        }
    }

    fn show_args(&self, args: ArgsId, depth: u32, out: &mut String) {
        let xs = self.fir.tys.args(args).to_vec();
        if xs.is_empty() {
            return;
        }
        out.push('[');
        for (i, a) in xs.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            self.show_into(*a, depth + 1, out);
        }
        out.push(']');
    }

    /// The written name of a nominal or trait head: the declaration's own
    /// name, or the prelude's spelling for a prelude row.
    pub fn head_name(&self, def: DefId) -> String {
        if let Some(r) = self.defs.get(def)
            && let Some(n) = r.name
        {
            return String::from_utf8_lossy(self.names.resolve(n)).into_owned();
        }
        if let Some(i) = self.prelude.generic_index(def) {
            return String::from_utf8_lossy(GENERIC_TYPES[i].0).into_owned();
        }
        if let Some(i) = self.prelude.trait_index(def) {
            return String::from_utf8_lossy(TRAITS[i].0).into_owned();
        }
        // A prelude row that is neither (a built-in impl, a prelude method):
        // the key still holds its name.
        let key = self.fir.defs.key_of(def);
        if key != fors_fir::NO_DECL_KEY
            && let Some(n) = self.fir.keys.row(key).name
        {
            return String::from_utf8_lossy(self.names.resolve(n)).into_owned();
        }
        "<item>".to_string()
    }
}
