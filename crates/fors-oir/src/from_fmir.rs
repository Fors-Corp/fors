//! `from_fmir` (§2.1): one linear pass, no optimisation. M2-0's subset only
//! (§10 M2-0 "FMIR surface covered"); everything else is a [`Refusal`] that
//! names the declaration, the instruction, the op and the reason — never a
//! miscompile.
//!
//! One OIR row per FMIR row: constants, arithmetic, logic, comparisons and
//! conversions map to their OIR op; `CopyFrom`/`Init` on a scalar root place
//! become `SlotLoad`/`SlotStore` on that root's frame slot with its alias
//! class; the two output intrinsics become `WriteUint`/`WriteLine`.

use std::collections::BTreeMap;

use fors_fir::ty::{PrimKind, TyId, TyStore, TyTag};
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{InstId, ValId};
use fors_fmir::inst::Callee;
use fors_fmir::op::{ArithMode, NO_OPERAND, Op};
use fors_fmir::value::ValDef;

use crate::alias::class_of_root;
use crate::ir::{LowTy, Mode, NONE, OirFunc, OirOp, Rows, Slot, Term, ValueId, Values};

/// The refusal reasons, by name (`refuses_out_of_subset_by_name` matches on
/// these exact strings).
pub mod reason {
    pub const OP: &str = "op not in the M2-0 subset";
    pub const UNCHECKED: &str = "unchecked mode";
    pub const NEG_UNSIGNED: &str = "neg in trap or sat mode on an unsigned type (owner Q6)";
    pub const TYPE: &str = "type not in the M2-0 subset";
    pub const SECRET: &str = "secret values need the spill class (M2-10)";
    pub const PROJECTION: &str = "place with a projection";
    pub const BLOCKS: &str = "more than one block";
    pub const PARAM: &str = "function parameters";
    pub const FRAME: &str = "frame over 32 KiB";
    pub const INTRINSIC: &str = "intrinsic other than stdout_write_uint / stdout_write_line";
    pub const STR_USE: &str = "a string constant used other than as write_line's text";
    pub const OPERAND: &str = "operand not defined earlier in the block";
    pub const ALIAS: &str = "alias seed M2-0 cannot carry";
    pub const RETURN: &str = "non-unit return";
    pub const STRING: &str = "string constant missing from the string table";
}

/// A precise refusal: which declaration, which FMIR instruction (`None` for
/// a declaration-level reason or the terminator), which op, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refusal {
    pub decl: u32,
    pub inst: Option<u32>,
    pub op: String,
    pub reason: String,
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inst {
            Some(i) => write!(
                f,
                "refused: decl {} inst {} `{}`: {}",
                self.decl, i, self.op, self.reason
            ),
            None => write!(
                f,
                "refused: decl {} `{}`: {}",
                self.decl, self.op, self.reason
            ),
        }
    }
}

impl std::error::Error for Refusal {}

/// What `from_fmir` reads: the declaration, the type store its `TyId`s
/// index, and the function's string and intrinsic side tables (the
/// interpreter's `ProgFn` shape).
pub struct FmirInput<'a> {
    pub decl: &'a DeclFmir,
    pub tys: &'a TyStore,
    pub strings: &'a [(u32, Vec<u8>)],
    pub intrinsics: &'a [(u32, String)],
}

struct Cx<'a> {
    inp: &'a FmirInput<'a>,
    decl: u32,
    values: Values,
    rows: Rows,
    slots: Vec<Slot>,
    slot_of_root: BTreeMap<u32, u32>,
    strings: Vec<Vec<u8>>,
    /// FMIR `ValId` -> OIR value (or [`NONE`] while undefined).
    map: Vec<u32>,
    /// FMIR inst index -> the FMIR value it defines.
    def_of: BTreeMap<u32, u32>,
}

fn op_name(op: Op) -> String {
    format!("{op:?}")
}

/// The low type of a FMIR type, or `None` outside M2-0's set (no
/// `isize`/`usize`, no floats, no aggregates).
pub fn low_ty(tys: &TyStore, ty: TyId) -> Option<LowTy> {
    if tys.quals(ty).is_secret() {
        return None;
    }
    let t = tys.unqual(ty);
    match tys.tag(t) {
        TyTag::Unit => Some(LowTy::Unit),
        TyTag::Prim => Some(match PrimKind::from_u8(tys.a(t) as u8)? {
            PrimKind::I8 => LowTy::I8,
            PrimKind::I16 => LowTy::I16,
            PrimKind::I32 => LowTy::I32,
            PrimKind::I64 => LowTy::I64,
            PrimKind::U8 => LowTy::U8,
            PrimKind::U16 => LowTy::U16,
            PrimKind::U32 => LowTy::U32,
            PrimKind::U64 => LowTy::U64,
            PrimKind::Bool => LowTy::Bool,
            PrimKind::Str => LowTy::Str,
            _ => return None,
        }),
        _ => None,
    }
}

impl<'a> Cx<'a> {
    fn refuse(&self, inst: Option<u32>, op: Op, reason: &str) -> Refusal {
        Refusal {
            decl: self.decl,
            inst,
            op: op_name(op),
            reason: reason.to_string(),
        }
    }

    fn ty_of(&self, inst: u32, op: Op, ty: TyId) -> Result<LowTy, Refusal> {
        if self.inp.tys.quals(ty).is_secret() {
            return Err(self.refuse(Some(inst), op, reason::SECRET));
        }
        low_ty(self.inp.tys, ty).ok_or_else(|| self.refuse(Some(inst), op, reason::TYPE))
    }

    /// The OIR value for FMIR operand `raw`.
    fn operand(&self, inst: u32, op: Op, raw: u32) -> Result<ValueId, Refusal> {
        match self.map.get(raw as usize) {
            Some(&v) if v != NONE => Ok(ValueId(v)),
            _ => Err(self.refuse(Some(inst), op, reason::OPERAND)),
        }
    }

    /// Defines the FMIR value of row `inst` (if any) as a new OIR value.
    fn define(&mut self, inst: u32, op: Op, ty: LowTy) -> Result<u32, Refusal> {
        let Some(&fv) = self.def_of.get(&inst) else {
            return Ok(NONE);
        };
        let row = self.inp.decl.vals.row(ValId(fv));
        if row.is_secret() {
            return Err(self.refuse(Some(inst), op, reason::SECRET));
        }
        let v = self.values.push(ty, row.is_secret(), row.ct, fv);
        self.map[fv as usize] = v.0;
        Ok(v.0)
    }

    fn slot_for(&mut self, root: u32, ty: LowTy) -> u32 {
        if let Some(&s) = self.slot_of_root.get(&root) {
            return s;
        }
        let s = self.slots.len() as u32;
        self.slots.push(Slot { root, ty });
        self.slot_of_root.insert(root, s);
        s
    }

    fn lower_row(&mut self, inst: u32) -> Result<(), Refusal> {
        let d = self.inp.decl;
        let r = d.insts.row(InstId(inst));
        let op = r.op;
        let site = r.site.0;
        let mode_of = |m: ArithMode| match m {
            ArithMode::Trap => Some(Mode::Trap),
            ArithMode::Wrap => Some(Mode::Wrap),
            ArithMode::Sat => Some(Mode::Sat),
            ArithMode::Unchecked => None,
        };
        match op {
            Op::ConstInt => {
                let ty = self.ty_of(inst, op, r.ty)?;
                if !ty.is_int() {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let dst = self.define(inst, op, ty)?;
                self.rows
                    .push(OirOp::ConstInt, r.a, r.b, ty, Mode::None, None, site, dst);
            }
            Op::ConstBool => {
                let dst = self.define(inst, op, LowTy::Bool)?;
                self.rows.push(
                    OirOp::ConstBool,
                    (r.a != 0) as u32,
                    NONE,
                    LowTy::Bool,
                    Mode::None,
                    None,
                    site,
                    dst,
                );
            }
            Op::ConstUnit => {
                let dst = self.define(inst, op, LowTy::Unit)?;
                self.rows.push(
                    OirOp::ConstUnit,
                    NONE,
                    NONE,
                    LowTy::Unit,
                    Mode::None,
                    None,
                    site,
                    dst,
                );
            }
            Op::ConstStr => {
                let Some((_, bytes)) = self.inp.strings.iter().find(|(id, _)| *id == r.a) else {
                    return Err(self.refuse(Some(inst), op, reason::STRING));
                };
                let idx = self.strings.len() as u32;
                self.strings.push(bytes.clone());
                let dst = self.define(inst, op, LowTy::Str)?;
                self.rows.push(
                    OirOp::ConstStr,
                    idx,
                    NONE,
                    LowTy::Str,
                    Mode::None,
                    None,
                    site,
                    dst,
                );
            }
            Op::Add(m)
            | Op::Sub(m)
            | Op::Mul(m)
            | Op::Div(m)
            | Op::Rem(m)
            | Op::Shl(m)
            | Op::Shr(m)
            | Op::Neg(m) => {
                let Some(mode) = mode_of(m) else {
                    return Err(self.refuse(Some(inst), op, reason::UNCHECKED));
                };
                let ty = self.ty_of(inst, op, r.ty)?;
                let a = self.operand(inst, op, r.a)?;
                if !ty.is_int() || self.values.ty[a.0 as usize] != ty {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let b = if matches!(op, Op::Neg(_)) {
                    if !ty.signed() && mode != Mode::Wrap {
                        return Err(self.refuse(Some(inst), op, reason::NEG_UNSIGNED));
                    }
                    NONE
                } else {
                    let b = self.operand(inst, op, r.b)?;
                    let bt = self.values.ty[b.0 as usize];
                    let shift = matches!(op, Op::Shl(_) | Op::Shr(_));
                    // A shift count is any integer type (its raw low bits
                    // are the count, `arith.rs::trap_shl`); every other
                    // binary op takes two operands of the result type.
                    if (shift && !bt.is_int()) || (!shift && bt != ty) {
                        return Err(self.refuse(Some(inst), op, reason::TYPE));
                    }
                    b.0
                };
                let oop = match op {
                    Op::Add(_) => OirOp::Add,
                    Op::Sub(_) => OirOp::Sub,
                    Op::Mul(_) => OirOp::Mul,
                    Op::Div(_) => OirOp::Div,
                    Op::Rem(_) => OirOp::Rem,
                    Op::Shl(_) => OirOp::Shl,
                    Op::Shr(_) => OirOp::Shr,
                    _ => OirOp::Neg,
                };
                let dst = self.define(inst, op, ty)?;
                self.rows.push(oop, a.0, b, ty, mode, None, site, dst);
            }
            Op::And | Op::Or | Op::Xor | Op::Not => {
                let ty = self.ty_of(inst, op, r.ty)?;
                let a = self.operand(inst, op, r.a)?;
                if !ty.is_scalar() || self.values.ty[a.0 as usize] != ty {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let b = if op == Op::Not {
                    NONE
                } else {
                    let b = self.operand(inst, op, r.b)?;
                    if self.values.ty[b.0 as usize] != ty {
                        return Err(self.refuse(Some(inst), op, reason::TYPE));
                    }
                    b.0
                };
                let oop = match op {
                    Op::And => OirOp::And,
                    Op::Or => OirOp::Or,
                    Op::Xor => OirOp::Xor,
                    _ => OirOp::Not,
                };
                let dst = self.define(inst, op, ty)?;
                self.rows.push(oop, a.0, b, ty, Mode::None, None, site, dst);
            }
            Op::Icmp(pred) => {
                let a = self.operand(inst, op, r.a)?;
                let b = self.operand(inst, op, r.b)?;
                let at = self.values.ty[a.0 as usize];
                if !at.is_scalar() || self.values.ty[b.0 as usize] != at {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let ty = self.ty_of(inst, op, r.ty)?;
                if ty != LowTy::Bool {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let dst = self.define(inst, op, ty)?;
                self.rows
                    .push(OirOp::Icmp(pred), a.0, b.0, ty, Mode::None, None, site, dst);
            }
            Op::ConvChecked | Op::ConvWrap | Op::ConvSat => {
                let ty = self.ty_of(inst, op, r.ty)?;
                let a = self.operand(inst, op, r.a)?;
                if !ty.is_int() || !self.values.ty[a.0 as usize].is_int() {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let oop = match op {
                    Op::ConvChecked => OirOp::ConvChecked,
                    Op::ConvWrap => OirOp::ConvWrap,
                    _ => OirOp::ConvSat,
                };
                let dst = self.define(inst, op, ty)?;
                self.rows
                    .push(oop, a.0, NONE, ty, Mode::None, None, site, dst);
            }
            Op::CopyFrom | Op::Init => {
                let place = fors_fmir::ids::PlaceId(r.a);
                if r.a as usize >= d.places.len() {
                    return Err(self.refuse(Some(inst), op, reason::OPERAND));
                }
                let pr = d.places.row(place);
                if !d.places.segs(place).is_empty() {
                    return Err(self.refuse(Some(inst), op, reason::PROJECTION));
                }
                let ty = self.ty_of(inst, op, pr.ty)?;
                if !ty.is_scalar() {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let class = class_of_root(pr.root, 0, d.insts.aliases.get(inst as usize))
                    .map_err(|_| self.refuse(Some(inst), op, reason::ALIAS))?;
                let slot = self.slot_for(pr.root, ty);
                if op == Op::CopyFrom {
                    let dst = self.define(inst, op, ty)?;
                    self.rows.push(
                        OirOp::SlotLoad,
                        slot,
                        NONE,
                        ty,
                        Mode::None,
                        Some(class),
                        site,
                        dst,
                    );
                } else {
                    let v = self.operand(inst, op, r.b)?;
                    if self.values.ty[v.0 as usize] != ty {
                        return Err(self.refuse(Some(inst), op, reason::TYPE));
                    }
                    self.rows.push(
                        OirOp::SlotStore,
                        slot,
                        v.0,
                        LowTy::Unit,
                        Mode::None,
                        Some(class),
                        site,
                        NONE,
                    );
                }
            }
            Op::Intrinsic => {
                let call = d.insts.calls.get(r.a as usize).cloned();
                let Some(call) = call else {
                    return Err(self.refuse(Some(inst), op, reason::INTRINSIC));
                };
                let Callee::Intrinsic(sym) = call.callee else {
                    return Err(self.refuse(Some(inst), op, reason::INTRINSIC));
                };
                let name = self
                    .inp
                    .intrinsics
                    .iter()
                    .find(|(s, _)| *s == sym.0)
                    .map(|(_, n)| n.as_str());
                let args = d.insts.args(call.args.clone()).to_vec();
                let (oop, want) = match name {
                    Some("stdout_write_uint") => (OirOp::WriteUint, None),
                    Some("stdout_write_line") => (OirOp::WriteLine, Some(LowTy::Str)),
                    _ => return Err(self.refuse(Some(inst), op, reason::INTRINSIC)),
                };
                // `(receiver, value)`: the receiver is the shim-fabricated
                // `Stdout`, a unit value here.
                if args.len() != 2 {
                    return Err(self.refuse(Some(inst), op, reason::INTRINSIC));
                }
                let recv = self.operand(inst, op, args[0].0)?;
                if self.values.ty[recv.0 as usize] != LowTy::Unit {
                    return Err(self.refuse(Some(inst), op, reason::TYPE));
                }
                let v = self.operand(inst, op, args[1].0)?;
                let vt = self.values.ty[v.0 as usize];
                match want {
                    Some(t) if vt != t => {
                        return Err(self.refuse(Some(inst), op, reason::TYPE));
                    }
                    None if !vt.is_scalar() => {
                        return Err(self.refuse(Some(inst), op, reason::TYPE));
                    }
                    _ => {}
                }
                let dst = self.define(inst, op, LowTy::Unit)?;
                self.rows
                    .push(oop, v.0, NONE, LowTy::Unit, Mode::None, None, site, dst);
            }
            _ => return Err(self.refuse(Some(inst), op, reason::OP)),
        }
        Ok(())
    }
}

/// FMIR -> OIR for M2-0's subset, or the first [`Refusal`].
pub fn from_fmir(inp: &FmirInput<'_>) -> Result<OirFunc, Refusal> {
    let d = inp.decl;
    let decl = d.decl.0;
    let mut cx = Cx {
        inp,
        decl,
        values: Values::default(),
        rows: Rows::default(),
        slots: Vec::new(),
        slot_of_root: BTreeMap::new(),
        strings: Vec::new(),
        map: vec![NONE; d.vals.len()],
        def_of: BTreeMap::new(),
    };
    let decl_refusal = |op: Op, why: &str| Refusal {
        decl,
        inst: None,
        op: op_name(op),
        reason: why.to_string(),
    };
    if d.blocks.len() != 1 {
        return Err(decl_refusal(Op::Br, reason::BLOCKS));
    }
    for (vid, row) in d.vals.all_rows() {
        match row.def() {
            ValDef::Param(_) => return Err(decl_refusal(Op::ConstUnit, reason::PARAM)),
            ValDef::Inst(i) => {
                cx.def_of.insert(i.0, vid.0);
            }
        }
    }
    let block = d.blocks.row(d.entry);
    for inst in block.first_inst..block.first_inst + block.inst_len {
        cx.lower_row(inst)?;
    }
    // `ConstStr` is only ever `write_line`'s text (§10 M2-0).
    for i in 0..cx.rows.len() {
        let op = cx.rows.op[i];
        for (col, raw) in [(0, cx.rows.a[i]), (1, cx.rows.b[i])] {
            let reads_value = match op {
                OirOp::ConstInt | OirOp::ConstBool | OirOp::ConstStr | OirOp::ConstUnit => false,
                OirOp::SlotLoad => false,
                OirOp::SlotStore => col == 1,
                _ => true,
            };
            if !reads_value || raw == NONE {
                continue;
            }
            if cx.values.ty[raw as usize] == LowTy::Str && op != OirOp::WriteLine {
                return Err(Refusal {
                    decl,
                    inst: Some(block.first_inst + i as u32),
                    op: op.name().to_string(),
                    reason: reason::STR_USE.to_string(),
                });
            }
        }
    }
    let t = block.term;
    let term = match t.op {
        Op::Ret => {
            if t.a != NO_OPERAND {
                let v = cx.operand(u32::MAX, t.op, t.a).map_err(|mut r| {
                    r.inst = None;
                    r
                })?;
                if cx.values.ty[v.0 as usize] != LowTy::Unit {
                    return Err(decl_refusal(t.op, reason::RETURN));
                }
            }
            Term::Ret
        }
        Op::Trap => match fors_fmir::op::TrapKind::from_u32(t.a) {
            Some(k) => Term::Trap(k),
            None => return Err(decl_refusal(t.op, reason::OP)),
        },
        other => return Err(decl_refusal(other, reason::OP)),
    };
    Ok(OirFunc {
        decl,
        values: cx.values,
        rows: cx.rows,
        slots: cx.slots,
        strings: cx.strings,
        term,
        term_site: t.site.0,
        sites: (0..d.sites.len())
            .map(|i| {
                let s = d.sites.row(fors_fmir::ids::SiteId(i as u32));
                (s.line, s.col)
            })
            .collect(),
    })
}
