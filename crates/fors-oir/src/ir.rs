//! The OIR data model (§2.1): struct-of-arrays like FMIR. Values keep FMIR's
//! SSA shape and carry `ty`, `secret` and `ct` as non-optional, fixed-width
//! columns (ch05 R6, §8: "copied, never recomputed"); rows carry `op, a, b,
//! ty, mode, alias, site` plus the value they define; every place root is a
//! frame slot and every slot row names its alias class (ch05 R4/R5).

pub use fors_fmir::op::{CmpPred, TrapKind};

/// "No operand / no value" in an `a`/`b`/`dst` column.
pub const NONE: u32 = u32::MAX;

/// A value id: an index into [`Values`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct ValueId(pub u32);

/// OIR's low types for M2-0's scalar surface. Integers keep their
/// signedness: a stencil's semantics depend on it, and FMIR's ops are not
/// split by sign.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum LowTy {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Bool,
    Unit,
    /// A string literal: only ever the text operand of `write_line`.
    Str,
}

impl LowTy {
    pub const INTS: [LowTy; 8] = [
        LowTy::I8,
        LowTy::I16,
        LowTy::I32,
        LowTy::I64,
        LowTy::U8,
        LowTy::U16,
        LowTy::U32,
        LowTy::U64,
    ];

    pub fn is_int(self) -> bool {
        Self::INTS.contains(&self)
    }

    /// Integers and `bool`: the types a frame slot can hold.
    pub fn is_scalar(self) -> bool {
        self.is_int() || self == LowTy::Bool
    }

    pub fn signed(self) -> bool {
        matches!(self, LowTy::I8 | LowTy::I16 | LowTy::I32 | LowTy::I64)
    }

    /// Bit width (`bool` is 1, `unit`/`str` are 0).
    pub fn width(self) -> u32 {
        match self {
            LowTy::I8 | LowTy::U8 => 8,
            LowTy::I16 | LowTy::U16 => 16,
            LowTy::I32 | LowTy::U32 => 32,
            LowTy::I64 | LowTy::U64 => 64,
            LowTy::Bool => 1,
            LowTy::Unit | LowTy::Str => 0,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            LowTy::I8 => "i8",
            LowTy::I16 => "i16",
            LowTy::I32 => "i32",
            LowTy::I64 => "i64",
            LowTy::U8 => "u8",
            LowTy::U16 => "u16",
            LowTy::U32 => "u32",
            LowTy::U64 => "u64",
            LowTy::Bool => "bool",
            LowTy::Unit => "unit",
            LowTy::Str => "str",
        }
    }
}

/// The arithmetic mode column. `Unchecked` never reaches OIR in M2-0 (it is
/// refused by name).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Mode {
    None,
    Trap,
    Wrap,
    Sat,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::None => "",
            Mode::Trap => "trap",
            Mode::Wrap => "wrap",
            Mode::Sat => "sat",
        }
    }
}

/// OIR opcodes of M2-0. `a`/`b` are value ids unless noted.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OirOp {
    /// `a` = low 32 bits, `b` = high 32 bits of the FMIR constant's raw
    /// slot bits (the low `width` bits).
    ConstInt,
    /// `a` = 0 or 1.
    ConstBool,
    ConstUnit,
    /// `a` = index into [`OirFunc::strings`].
    ConstStr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    Neg,
    And,
    Or,
    Xor,
    Not,
    Icmp(CmpPred),
    ConvChecked,
    ConvWrap,
    ConvSat,
    /// `a` = slot index; defines `dst`.
    SlotLoad,
    /// `a` = slot index, `b` = the stored value.
    SlotStore,
    /// `a` = the value printed (`stdout_write_uint`).
    WriteUint,
    /// `a` = a `ConstStr` value (`stdout_write_line`).
    WriteLine,
    /// A `tile.*` op: ch05 R12 confines these to FMIR. `from_fmir` never
    /// produces one; it exists so the verifier's rejection is testable.
    Tile,
}

impl OirOp {
    pub fn name(self) -> &'static str {
        match self {
            OirOp::ConstInt => "const_int",
            OirOp::ConstBool => "const_bool",
            OirOp::ConstUnit => "const_unit",
            OirOp::ConstStr => "const_str",
            OirOp::Add => "add",
            OirOp::Sub => "sub",
            OirOp::Mul => "mul",
            OirOp::Div => "div",
            OirOp::Rem => "rem",
            OirOp::Shl => "shl",
            OirOp::Shr => "shr",
            OirOp::Neg => "neg",
            OirOp::And => "and",
            OirOp::Or => "or",
            OirOp::Xor => "xor",
            OirOp::Not => "not",
            OirOp::Icmp(_) => "icmp",
            OirOp::ConvChecked => "conv_checked",
            OirOp::ConvWrap => "conv_wrap",
            OirOp::ConvSat => "conv_sat",
            OirOp::SlotLoad => "slot_load",
            OirOp::SlotStore => "slot_store",
            OirOp::WriteUint => "write_uint",
            OirOp::WriteLine => "write_line",
            OirOp::Tile => "tile",
        }
    }

    /// Rows that read or write a frame slot: each must carry an alias class.
    pub fn is_slot_row(self) -> bool {
        matches!(self, OirOp::SlotLoad | OirOp::SlotStore)
    }
}

/// Where a slot's alias class comes from (ch05 R5's sources that can reach
/// a scalar root place).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum AliasSource {
    /// A parameter's convention.
    Convention,
    /// An affine local (the root owns its storage).
    Affine,
}

/// A slot row's alias class (§2.1, `alias.rs`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum AliasClass {
    Root { root: u32, source: AliasSource },
}

/// The value columns.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Values {
    pub ty: Vec<LowTy>,
    pub secret: Vec<bool>,
    pub ct: Vec<u16>,
    /// The FMIR `ValId` each value came from (for diagnostics and dumps).
    pub fmir: Vec<u32>,
}

impl Values {
    pub fn len(&self) -> usize {
        self.ty.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ty.is_empty()
    }

    pub fn push(&mut self, ty: LowTy, secret: bool, ct: u16, fmir: u32) -> ValueId {
        let id = ValueId(self.ty.len() as u32);
        self.ty.push(ty);
        self.secret.push(secret);
        self.ct.push(ct);
        self.fmir.push(fmir);
        id
    }
}

/// The row columns.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Rows {
    pub op: Vec<OirOp>,
    pub a: Vec<u32>,
    pub b: Vec<u32>,
    /// The result type (`unit` for a row that defines nothing).
    pub ty: Vec<LowTy>,
    pub mode: Vec<Mode>,
    /// Present on every slot row, absent elsewhere.
    pub alias: Vec<Option<AliasClass>>,
    /// The FMIR `SiteId` (trap reporting reads it from M2-3 on).
    pub site: Vec<u32>,
    /// The value this row defines, or [`NONE`].
    pub dst: Vec<u32>,
}

impl Rows {
    pub fn len(&self) -> usize {
        self.op.len()
    }

    pub fn is_empty(&self) -> bool {
        self.op.is_empty()
    }

    #[allow(clippy::too_many_arguments)]
    pub fn push(
        &mut self,
        op: OirOp,
        a: u32,
        b: u32,
        ty: LowTy,
        mode: Mode,
        alias: Option<AliasClass>,
        site: u32,
        dst: u32,
    ) {
        self.op.push(op);
        self.a.push(a);
        self.b.push(b);
        self.ty.push(ty);
        self.mode.push(mode);
        self.alias.push(alias);
        self.site.push(site);
        self.dst.push(dst);
    }
}

/// A frame slot: one per place root.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Slot {
    pub root: u32,
    pub ty: LowTy,
}

/// The block terminator (M2-0: one block).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Term {
    Ret,
    Trap(TrapKind),
}

/// One function in OIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OirFunc {
    /// The FMIR declaration key.
    pub decl: u32,
    pub values: Values,
    pub rows: Rows,
    pub slots: Vec<Slot>,
    pub strings: Vec<Vec<u8>>,
    pub term: Term,
    pub term_site: u32,
    /// `(line, col)` of every FMIR site id (the declaration's `SitePool`),
    /// indexed by the `site` column; trap-table rows read it.
    pub sites: Vec<(u32, u32)>,
}
