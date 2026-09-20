//! The `Inst` enum: one variant per AArch64 *encoding shape*, not per
//! mnemonic. Aliases (`CMP`, `MOV`, `TST`, `MVN`, `NEG`, `CSET`, `CSETM`,
//! `CINC`, `CINV`, `CNEG`, `SXTB`/.../`UXTH`, `LSL`/`LSR`/`ASR` immediate)
//! are provided as constructor **functions** that build the canonical
//! variant (e.g. `Inst::cmp_imm` builds a `SubsImm` with `rd = XZR`) rather
//! than as separate enum cases. Two reasons:
//!
//! 1. It matches the spike (`enc_csinc`, `enc_add_sub_imm` with a `set_flags`
//!    bool, etc. — the spike already treated CMP/NEG this way): grouping by
//!    encoding shape is what let a ~20-variant IR cover a real program.
//! 2. `Display` only has to print the base mnemonic to get assembly text
//!    the system assembler accepts (`subs xzr, x1, #4` is exactly as valid
//!    as `cmp x1, #4`, and encodes identically) — the oracle test doesn't
//!    need `Display` to reproduce the alias spelling, only *some* valid
//!    spelling that assembles to the same bytes `encode()` produces. Where
//!    printing the alias is essentially free (`cmp`/`mov`/`tst`/`neg`/
//!    `mvn`/`cset*`), the constructors record which alias made them so
//!    `Display` uses it — better test-failure output, and it's what a
//!    human reading generated assembly wants to see.
//!
//! Every field an instruction needs is a type from `operand`/`reg` that
//! already validated its own range at construction; `encode()`
//! (`encode.rs`) still returns `Result` because a handful of checks are
//! only meaningful once two operands are seen together (matching
//! register widths, SP-vs-ZR legality for a given field).

use crate::error::EncodeError;
use crate::operand::*;
use crate::reg::Reg;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MovWideOp {
    Movz,
    Movn,
    Movk,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AddSubOp {
    Add,
    Sub,
}

/// Which alias (if any) built an `AddSubImm`/`AddSubShiftedReg`/
/// `AddSubExtendedReg`, purely for `Display`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AddSubAlias {
    None,
    Cmp,
    Cmn,
    Neg,
    Negs,
    Mov,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LogicalShiftOp {
    And,
    Bic,
    Orr,
    Orn,
    Eor,
    Eon,
    Ands,
    Bics,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LogicalImmOp {
    And,
    Orr,
    Eor,
    Ands,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LogicalAlias {
    None,
    Mvn,
    Tst,
    Mov,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BitfieldOp {
    Sbfm,
    Bfm,
    Ubfm,
}

/// Which alias built a `Bitfield`, for `Display` (the raw `sbfm`/`ubfm`/
/// `bfm` spelling is always also valid input to the assembler, so this is
/// purely cosmetic, same rationale as `AddSubAlias`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BitfieldAlias {
    None,
    Lsl,
    Lsr,
    Asr,
    Sxtb,
    Sxth,
    Sxtw,
    Uxtb,
    Uxth,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DataProc2Op {
    Udiv,
    Sdiv,
    Lslv,
    Lsrv,
    Asrv,
    Rorv,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DataProc3Op {
    Madd,
    Msub,
    Smulh,
    Umulh,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DataProc1Op {
    Rbit,
    Clz,
    Rev,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CondSelectOp {
    Csel,
    Csinc,
    Csinv,
    Csneg,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CondSelectAlias {
    None,
    Cset,
    Csetm,
    Cinc,
    Cinv,
    Cneg,
}

/// GP load/store operation: which mnemonic, which maps to a `(size, opc)`
/// field pair (see `encode.rs`) and the destination width.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LdStOp {
    StrB,
    LdrB,
    LdrSb { is64: bool },
    StrH,
    LdrH,
    LdrSh { is64: bool },
    StrW,
    LdrW,
    LdrSw,
    StrX,
    LdrX,
}

impl LdStOp {
    pub(crate) fn size_opc(self) -> (u32, u32) {
        use LdStOp::*;
        match self {
            StrB => (0b00, 0b00),
            LdrB => (0b00, 0b01),
            LdrSb { is64: true } => (0b00, 0b10),
            LdrSb { is64: false } => (0b00, 0b11),
            StrH => (0b01, 0b00),
            LdrH => (0b01, 0b01),
            LdrSh { is64: true } => (0b01, 0b10),
            LdrSh { is64: false } => (0b01, 0b11),
            StrW => (0b10, 0b00),
            LdrW => (0b10, 0b01),
            LdrSw => (0b10, 0b10),
            StrX => (0b11, 0b00),
            LdrX => (0b11, 0b01),
        }
    }

    pub(crate) fn access_size(self) -> u32 {
        use LdStOp::*;
        match self {
            StrB | LdrB | LdrSb { .. } => 1,
            StrH | LdrH | LdrSh { .. } => 2,
            StrW | LdrW | LdrSw => 4,
            StrX | LdrX => 8,
        }
    }

    pub(crate) fn rt_is64(self) -> bool {
        use LdStOp::*;
        match self {
            LdrSb { is64 } | LdrSh { is64 } => is64,
            LdrSw | StrX | LdrX => true,
            _ => false,
        }
    }

    pub(crate) fn mnemonic(self) -> &'static str {
        use LdStOp::*;
        match self {
            StrB => "strb",
            LdrB => "ldrb",
            LdrSb { .. } => "ldrsb",
            StrH => "strh",
            LdrH => "ldrh",
            LdrSh { .. } => "ldrsh",
            StrW => "str",
            LdrW => "ldr",
            LdrSw => "ldrsw",
            StrX => "str",
            LdrX => "ldr",
        }
    }

    /// The mnemonic for the *unscaled-immediate* encoding (`LDUR` family).
    /// Needed only for `AddrMode::Unscaled`: unlike pre/post-index (whose
    /// `!`/postfix-comma syntax is unambiguous on its own), a plain
    /// `ldrb w0, [x1, #0]` is legal input for the *unsigned-offset*
    /// encoding too whenever the unscaled offset also happens to be a
    /// non-negative multiple of the access size — the system assembler
    /// picks unsigned-offset in that case regardless of which encoding
    /// the operand type says (verified: it re-derives from the value, not
    /// from a fixed choice this crate could name in the text; oracle
    /// finding, see crate docs / report). Naming the `U` form explicitly
    /// removes the ambiguity instead of relying on the offset happening to
    /// be negative or unaligned.
    pub(crate) fn unscaled_mnemonic(self) -> &'static str {
        use LdStOp::*;
        match self {
            StrB => "sturb",
            LdrB => "ldurb",
            LdrSb { .. } => "ldursb",
            StrH => "sturh",
            LdrH => "ldurh",
            LdrSh { .. } => "ldursh",
            StrW => "stur",
            LdrW => "ldur",
            LdrSw => "ldursw",
            StrX => "stur",
            LdrX => "ldur",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AddrMode {
    UnsignedOffset(UScaledImm12),
    Unscaled(Simm9),
    PreIndex(Simm9),
    PostIndex(Simm9),
    RegOffset(RegOffset),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LdStExtend {
    Uxtw,
    Lsl,
    Sxtw,
    Sxtx,
}

impl LdStExtend {
    pub(crate) fn option(self) -> u32 {
        match self {
            LdStExtend::Uxtw => 0b010,
            LdStExtend::Lsl => 0b011,
            LdStExtend::Sxtw => 0b110,
            LdStExtend::Sxtx => 0b111,
        }
    }

    pub(crate) fn rm_is64(self) -> bool {
        matches!(self, LdStExtend::Lsl | LdStExtend::Sxtx)
    }

    pub(crate) const fn mnemonic(self) -> Option<&'static str> {
        match self {
            LdStExtend::Uxtw => Some("uxtw"),
            LdStExtend::Lsl => None, // plain register offset prints with no keyword
            LdStExtend::Sxtw => Some("sxtw"),
            LdStExtend::Sxtx => Some("sxtx"),
        }
    }
}

/// Register-offset addressing (`[Xn, Xm]` / `[Xn, Wm, UXTW #n]` / ...).
/// `shifted` selects the *implicit* amount (0, or `log2(access_size)` —
/// this addressing mode has no arbitrary shift amount, only "on"/"off",
/// hence a `bool` rather than a `RegShift`/`RegExtend`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegOffset {
    pub(crate) rm: Reg,
    pub(crate) extend: LdStExtend,
    pub(crate) shifted: bool,
}

impl RegOffset {
    pub fn new(rm: Reg, extend: LdStExtend, shifted: bool) -> Result<RegOffset, EncodeError> {
        if rm.is64() != extend.rm_is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "load/store register offset",
            });
        }
        Ok(RegOffset {
            rm,
            extend,
            shifted,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SysOp {
    Nop,
    Brk(u16),
    Svc(u16),
    Udf(u16),
}

/// One AArch64 instruction, already fully validated: every field either
/// came from a `Reg`/`FpReg` (whose width/SP-vs-ZR flavor is part of its
/// type) or from an `operand` wrapper type whose constructor already
/// range-checked it. See the module docs for why this is one variant per
/// *encoding*, with aliases as constructor functions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Inst {
    MovWide {
        op: MovWideOp,
        rd: Reg,
        imm16: u16,
        shift: u8,
    },
    AddSubImm {
        op: AddSubOp,
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        imm: Uimm12Lsl,
        alias: AddSubAlias,
    },
    AddSubShiftedReg {
        op: AddSubOp,
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        shift: RegShift,
        alias: AddSubAlias,
    },
    AddSubExtendedReg {
        op: AddSubOp,
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        extend: RegExtend,
        alias: AddSubAlias,
    },
    LogicalImmInst {
        op: LogicalImmOp,
        rd: Reg,
        rn: Reg,
        imm: LogicalImm,
        alias: LogicalAlias,
    },
    LogicalShiftedReg {
        op: LogicalShiftOp,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        shift: RegShift,
        alias: LogicalAlias,
    },
    Bitfield {
        op: BitfieldOp,
        rd: Reg,
        rn: Reg,
        immr: u8,
        imms: u8,
        alias: BitfieldAlias,
    },
    DataProc2Source {
        op: DataProc2Op,
        rd: Reg,
        rn: Reg,
        rm: Reg,
    },
    DataProc3Source {
        op: DataProc3Op,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        ra: Reg,
        is_mul_alias: bool,
    },
    DataProc1Source {
        op: DataProc1Op,
        rd: Reg,
        rn: Reg,
    },
    CondSelect {
        op: CondSelectOp,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        cond: Cond,
        alias: CondSelectAlias,
    },
    Adr {
        rd: Reg,
        offset: AdrOffset,
    },
    Adrp {
        rd: Reg,
        offset: AdrpOffset,
    },
    Branch {
        link: bool,
        offset: BranchOffset,
    },
    BranchCond {
        cond: Cond,
        offset: BranchOffset,
    },
    CompareBranch {
        is64: bool,
        is_nonzero: bool,
        rt: Reg,
        offset: BranchOffset,
    },
    TestBranch {
        is_nonzero: bool,
        rt: Reg,
        bit: u8,
        offset: BranchOffset,
    },
    BranchReg {
        rn: Reg,
    },
    BranchLinkReg {
        rn: Reg,
    },
    Ret {
        rn: Reg,
    },
    LoadStoreImm {
        op: LdStOp,
        rt: Reg,
        rn: Reg,
        mode: AddrMode,
    },
    LoadStorePair {
        is_load: bool,
        is64: bool,
        rt1: Reg,
        rt2: Reg,
        rn: Reg,
        imm: SImm7Scaled,
        index: PairIndex,
    },
    FpLoadStoreImm {
        is_load: bool,
        rt: crate::reg::FpReg,
        rn: Reg,
        mode: AddrMode,
    },
    System(SysOp),
    // FP variants live here too (one enum), constructed from `fp.rs`.
    FpDataProc1 {
        op: FpUnaryOp,
        rd: crate::reg::FpReg,
        rn: crate::reg::FpReg,
    },
    FpConvert {
        rd: crate::reg::FpReg,
        rn: crate::reg::FpReg,
    },
    FpDataProc2 {
        op: FpBinOp,
        rd: crate::reg::FpReg,
        rn: crate::reg::FpReg,
        rm: crate::reg::FpReg,
    },
    FpCompare {
        rn: crate::reg::FpReg,
        rm: crate::reg::FpReg,
    },
    FpCondSelect {
        rd: crate::reg::FpReg,
        rn: crate::reg::FpReg,
        rm: crate::reg::FpReg,
        cond: Cond,
    },
    FpImmMove {
        rd: crate::reg::FpReg,
        imm: crate::fpimm::FpImm8,
    },
    FpToGp {
        rd: Reg,
        rn: crate::reg::FpReg,
    },
    GpToFp {
        rd: crate::reg::FpReg,
        rn: Reg,
    },
    FpIntConvert {
        op: FpIntConvertOp,
        gp: Reg,
        fp: crate::reg::FpReg,
    },
    FpMadd {
        rd: crate::reg::FpReg,
        rn: crate::reg::FpReg,
        rm: crate::reg::FpReg,
        ra: crate::reg::FpReg,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PairIndex {
    Offset,
    PreIndex,
    PostIndex,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FpUnaryOp {
    Fmov,
    Fabs,
    Fneg,
    Fsqrt,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FpBinOp {
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FpIntConvertOp {
    Scvtf,
    Ucvtf,
    Fcvtzs,
    Fcvtzu,
}

fn check_same_width(a: Reg, b: Reg, what: &'static str) -> Result<(), EncodeError> {
    if a.is64() != b.is64() {
        Err(EncodeError::RegisterWidthMismatch { what })
    } else {
        Ok(())
    }
}

impl Inst {
    // ---------------- MOVZ/MOVN/MOVK ----------------

    fn mov_wide(op: MovWideOp, rd: Reg, imm16: u16, shift: u8) -> Result<Inst, EncodeError> {
        let max_shift = if rd.is64() { 48 } else { 16 };
        if shift > max_shift || !shift.is_multiple_of(16) {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "MOVZ/MOVN/MOVK shift",
                value: shift as i64,
            });
        }
        Ok(Inst::MovWide {
            op,
            rd,
            imm16,
            shift,
        })
    }

    pub fn movz(rd: Reg, imm16: u16, shift: u8) -> Result<Inst, EncodeError> {
        Self::mov_wide(MovWideOp::Movz, rd, imm16, shift)
    }

    pub fn movn(rd: Reg, imm16: u16, shift: u8) -> Result<Inst, EncodeError> {
        Self::mov_wide(MovWideOp::Movn, rd, imm16, shift)
    }

    pub fn movk(rd: Reg, imm16: u16, shift: u8) -> Result<Inst, EncodeError> {
        Self::mov_wide(MovWideOp::Movk, rd, imm16, shift)
    }

    // ---------------- ADD/SUB (immediate / shifted-reg / extended-reg) ----------------

    /// The field-31-meaning check shared by every ADD/SUB (immediate)
    /// form (`ADD`, `ADDS`, `SUB`, `SUBS`, and the `CMP`/`CMN`/`MOV(SP)`
    /// aliases): `Rn`'s field 31 can only ever mean `SP` in this
    /// instruction class — there is no bit pattern for "immediate op
    /// against XZR" — so a caller-supplied `Rn` of `XZR`/`WZR` is
    /// rejected rather than silently re-encoded as `SP` (which is what
    /// `encode()` would otherwise do, since the field is identical either
    /// way: `Reg::encoding()` can't see the difference once it's just a
    /// bit pattern). `Rd` follows the same rule for the non-flag-setting
    /// forms (`ADD`/`SUB`/`MOV(SP)`: field 31 is always `SP`); the
    /// flag-setting forms (`ADDS`/`SUBS`, and their `CMP`/`CMN` aliases)
    /// instead allow `Rd = ZR` (that IS `CMP`/`CMN`) and disallow `SP`.
    fn add_sub_imm_common(
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        what: &'static str,
    ) -> Result<(), EncodeError> {
        check_same_width(rd, rn, what)?;
        if rn.is_zr() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "ADD/SUB immediate Rn (field 31 is always SP here, never XZR/WZR)",
            });
        }
        if set_flags {
            if rd.is_sp() {
                return Err(EncodeError::InvalidRegisterForForm {
                    what: "ADDS/SUBS Rd (field 31 is always XZR/WZR here, never SP; use ADD/SUB for an SP destination)",
                });
            }
        } else if rd.is_zr() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "ADD/SUB Rd (field 31 is always SP here, never XZR/WZR; use ADDS/SUBS for a discarded/flags-only result)",
            });
        }
        Ok(())
    }

    pub fn add_imm(rd: Reg, rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        Self::add_sub_imm_common(false, rd, rn, "ADD (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Add,
            set_flags: false,
            rd,
            rn,
            imm,
            alias: AddSubAlias::None,
        })
    }

    pub fn adds_imm(rd: Reg, rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        Self::add_sub_imm_common(true, rd, rn, "ADDS (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Add,
            set_flags: true,
            rd,
            rn,
            imm,
            alias: AddSubAlias::None,
        })
    }

    pub fn sub_imm(rd: Reg, rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        Self::add_sub_imm_common(false, rd, rn, "SUB (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Sub,
            set_flags: false,
            rd,
            rn,
            imm,
            alias: AddSubAlias::None,
        })
    }

    pub fn subs_imm(rd: Reg, rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        Self::add_sub_imm_common(true, rd, rn, "SUBS (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Sub,
            set_flags: true,
            rd,
            rn,
            imm,
            alias: AddSubAlias::None,
        })
    }

    /// `CMP <Rn>, #imm` — alias of `SUBS XZR/WZR, Rn, #imm`.
    pub fn cmp_imm(rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_imm_common(true, rd, rn, "CMP (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Sub,
            set_flags: true,
            rd,
            rn,
            imm,
            alias: AddSubAlias::Cmp,
        })
    }

    /// `CMN <Rn>, #imm` — alias of `ADDS XZR/WZR, Rn, #imm`.
    pub fn cmn_imm(rn: Reg, imm: Uimm12Lsl) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_imm_common(true, rd, rn, "CMN (immediate)")?;
        Ok(Inst::AddSubImm {
            op: AddSubOp::Add,
            set_flags: true,
            rd,
            rn,
            imm,
            alias: AddSubAlias::Cmn,
        })
    }

    pub fn add_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::add_sub_shifted(AddSubOp::Add, false, rd, rn, rm, shift, AddSubAlias::None)
    }

    pub fn adds_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::add_sub_shifted(AddSubOp::Add, true, rd, rn, rm, shift, AddSubAlias::None)
    }

    pub fn sub_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::add_sub_shifted(AddSubOp::Sub, false, rd, rn, rm, shift, AddSubAlias::None)
    }

    pub fn subs_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::add_sub_shifted(AddSubOp::Sub, true, rd, rn, rm, shift, AddSubAlias::None)
    }

    /// `CMP <Rn>, <Rm>{, shift}` — alias of `SUBS XZR/WZR, Rn, Rm{, shift}`.
    pub fn cmp_shifted(rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_shifted(AddSubOp::Sub, true, rd, rn, rm, shift, AddSubAlias::Cmp)
    }

    pub fn cmn_shifted(rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_shifted(AddSubOp::Add, true, rd, rn, rm, shift, AddSubAlias::Cmn)
    }

    /// `NEG <Rd>, <Rm>{, shift}` — alias of `SUB Rd, XZR/WZR, Rm{, shift}`.
    pub fn neg(rd: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rn = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_shifted(AddSubOp::Sub, false, rd, rn, rm, shift, AddSubAlias::Neg)
    }

    pub fn negs(rd: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rn = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_shifted(AddSubOp::Sub, true, rd, rn, rm, shift, AddSubAlias::Negs)
    }

    fn add_sub_shifted(
        op: AddSubOp,
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        shift: RegShift,
        alias: AddSubAlias,
    ) -> Result<Inst, EncodeError> {
        if matches!(shift.kind(), ShiftKind::Ror) {
            return Err(EncodeError::InvalidShiftForForm {
                what: "ADD/SUB shifted-register (ROR is not legal here)",
            });
        }
        check_same_width(rd, rn, "ADD/SUB shifted-register")?;
        check_same_width(rd, rm, "ADD/SUB shifted-register")?;
        if rd.is_sp() || rn.is_sp() || rm.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "ADD/SUB shifted-register (no SP operand; use extended-register form)",
            });
        }
        Ok(Inst::AddSubShiftedReg {
            op,
            set_flags,
            rd,
            rn,
            rm,
            shift,
            alias,
        })
    }

    pub fn add_extended(rd: Reg, rn: Reg, rm: Reg, extend: RegExtend) -> Result<Inst, EncodeError> {
        Self::add_sub_extended(AddSubOp::Add, false, rd, rn, rm, extend, AddSubAlias::None)
    }

    pub fn adds_extended(
        rd: Reg,
        rn: Reg,
        rm: Reg,
        extend: RegExtend,
    ) -> Result<Inst, EncodeError> {
        Self::add_sub_extended(AddSubOp::Add, true, rd, rn, rm, extend, AddSubAlias::None)
    }

    pub fn sub_extended(rd: Reg, rn: Reg, rm: Reg, extend: RegExtend) -> Result<Inst, EncodeError> {
        Self::add_sub_extended(AddSubOp::Sub, false, rd, rn, rm, extend, AddSubAlias::None)
    }

    pub fn subs_extended(
        rd: Reg,
        rn: Reg,
        rm: Reg,
        extend: RegExtend,
    ) -> Result<Inst, EncodeError> {
        Self::add_sub_extended(AddSubOp::Sub, true, rd, rn, rm, extend, AddSubAlias::None)
    }

    pub fn cmp_extended(rn: Reg, rm: Reg, extend: RegExtend) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_extended(AddSubOp::Sub, true, rd, rn, rm, extend, AddSubAlias::Cmp)
    }

    pub fn cmn_extended(rn: Reg, rm: Reg, extend: RegExtend) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::add_sub_extended(AddSubOp::Add, true, rd, rn, rm, extend, AddSubAlias::Cmn)
    }

    fn add_sub_extended(
        op: AddSubOp,
        set_flags: bool,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        extend: RegExtend,
        alias: AddSubAlias,
    ) -> Result<Inst, EncodeError> {
        // rd/rn may be SP (this is the form that allows it); rm may not.
        if rm.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "ADD/SUB extended-register Rm",
            });
        }
        if rd.is64() != rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "ADD/SUB extended-register",
            });
        }
        // `Rm`'s WIDTH is dictated by the extend kind, independently of
        // the destination's width: UXTB/UXTH/UXTW/SXTB/SXTH/SXTW extend
        // *from* a 32-bit value (Rm must be Wm), UXTX/SXTX/plain LSL
        // extend *from* a 64-bit value (Rm must be Xm). Mismatching these
        // is invalid assembly, not just a style choice — verified against
        // the system assembler, which rejects e.g. `add x0, x1, x2, uxtb`
        // (`x2`, not `w2`) with "expected 'sxtx' 'uxtx' or 'lsl'".
        let rm_must_be_64 = matches!(extend.kind(), ExtendKind::Uxtx | ExtendKind::Sxtx);
        if rm.is64() != rm_must_be_64 {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "ADD/SUB extended-register Rm width vs extend kind (UXTB/UXTH/UXTW/SXTB/SXTH/SXTW need Wm; UXTX/SXTX need Xm)",
            });
        }
        // UXTX/SXTX (extending *from* a 64-bit value) additionally require
        // a 64-bit destination: there is no 32-bit form that takes a
        // 64-bit source to truncate from. Verified against the system
        // assembler, which rejects `add w0, w1, x2, uxtx` outright (it
        // doesn't even recognize `x2` as a legal operand there).
        if rm_must_be_64 && !rd.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "ADD/SUB extended-register: UXTX/SXTX require a 64-bit (X) destination",
            });
        }
        Ok(Inst::AddSubExtendedReg {
            op,
            set_flags,
            rd,
            rn,
            rm,
            extend,
            alias,
        })
    }

    /// `MOV <Rd>, <Rn>` between SP and a GP register — alias of
    /// `ADD Rd, Rn, #0` (the only alias that needs an ADD/SUB *immediate*
    /// encoding rather than shifted/extended-register); both operands
    /// follow the same "field 31 is always SP" rule as plain `ADD`.
    pub fn mov_sp(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::add_sub_imm_common(false, rd, rn, "MOV (to/from SP)")?;
        let imm = Uimm12Lsl::new(0).expect("0 always encodes");
        Ok(Inst::AddSubImm {
            op: AddSubOp::Add,
            set_flags: false,
            rd,
            rn,
            imm,
            alias: AddSubAlias::Mov,
        })
    }

    // ---------------- Logical (immediate / shifted-register) ----------------

    pub fn and_imm(rd: Reg, rn: Reg, imm: LogicalImm) -> Result<Inst, EncodeError> {
        Self::logical_imm(LogicalImmOp::And, rd, rn, imm, LogicalAlias::None)
    }

    pub fn orr_imm(rd: Reg, rn: Reg, imm: LogicalImm) -> Result<Inst, EncodeError> {
        Self::logical_imm(LogicalImmOp::Orr, rd, rn, imm, LogicalAlias::None)
    }

    pub fn eor_imm(rd: Reg, rn: Reg, imm: LogicalImm) -> Result<Inst, EncodeError> {
        Self::logical_imm(LogicalImmOp::Eor, rd, rn, imm, LogicalAlias::None)
    }

    pub fn ands_imm(rd: Reg, rn: Reg, imm: LogicalImm) -> Result<Inst, EncodeError> {
        Self::logical_imm(LogicalImmOp::Ands, rd, rn, imm, LogicalAlias::None)
    }

    /// `TST <Rn>, #imm` — alias of `ANDS XZR/WZR, Rn, #imm`.
    pub fn tst_imm(rn: Reg, imm: LogicalImm) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::logical_imm(LogicalImmOp::Ands, rd, rn, imm, LogicalAlias::Tst)
    }

    fn logical_imm(
        op: LogicalImmOp,
        rd: Reg,
        rn: Reg,
        imm: LogicalImm,
        alias: LogicalAlias,
    ) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "AND/ORR/EOR/ANDS (immediate)")?;
        if rd.is64() != imm.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "logical immediate width vs register width",
            });
        }
        if rn.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "AND/ORR/EOR/ANDS (immediate) Rn (no SP)",
            });
        }
        if matches!(op, LogicalImmOp::Ands) && rd.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "ANDS (immediate) Rd (no SP; flag-setting form)",
            });
        }
        Ok(Inst::LogicalImmInst {
            op,
            rd,
            rn,
            imm,
            alias,
        })
    }

    pub fn and_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::And, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn orr_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Orr, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn eor_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Eor, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn ands_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Ands, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn bic_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Bic, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn orn_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Orn, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn eon_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Eon, rd, rn, rm, shift, LogicalAlias::None)
    }

    pub fn bics_shifted(rd: Reg, rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        Self::logical_shifted(LogicalShiftOp::Bics, rd, rn, rm, shift, LogicalAlias::None)
    }

    /// `MVN <Rd>, <Rm>{, shift}` — alias of `ORN Rd, XZR/WZR, Rm{, shift}`.
    pub fn mvn(rd: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rn = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::logical_shifted(LogicalShiftOp::Orn, rd, rn, rm, shift, LogicalAlias::Mvn)
    }

    /// `TST <Rn>, <Rm>{, shift}` — alias of `ANDS XZR/WZR, Rn, Rm{, shift}`.
    pub fn tst_reg(rn: Reg, rm: Reg, shift: RegShift) -> Result<Inst, EncodeError> {
        let rd = if rn.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::logical_shifted(LogicalShiftOp::Ands, rd, rn, rm, shift, LogicalAlias::Tst)
    }

    /// `MOV <Rd>, <Rm>` (no SP involved) — alias of `ORR Rd, XZR/WZR, Rm`.
    pub fn mov_reg(rd: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        let rn = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::logical_shifted(
            LogicalShiftOp::Orr,
            rd,
            rn,
            rm,
            RegShift::none(),
            LogicalAlias::Mov,
        )
    }

    fn logical_shifted(
        op: LogicalShiftOp,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        shift: RegShift,
        alias: LogicalAlias,
    ) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "logical shifted-register")?;
        check_same_width(rd, rm, "logical shifted-register")?;
        if rd.is_sp() || rn.is_sp() || rm.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "logical shifted-register (no SP operand)",
            });
        }
        Ok(Inst::LogicalShiftedReg {
            op,
            rd,
            rn,
            rm,
            shift,
            alias,
        })
    }

    // ---------------- Bitfield: UBFM/SBFM/BFM + shift/extend aliases ----------------

    fn bitfield_raw(
        op: BitfieldOp,
        rd: Reg,
        rn: Reg,
        immr: u8,
        imms: u8,
        alias: BitfieldAlias,
    ) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "UBFM/SBFM/BFM")?;
        let max = if rd.is64() { 63 } else { 31 };
        if immr > max {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "immr",
                value: immr as i64,
            });
        }
        if imms > max {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "imms",
                value: imms as i64,
            });
        }
        if rd.is_sp() || rn.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "UBFM/SBFM/BFM (no SP operand)",
            });
        }
        Ok(Inst::Bitfield {
            op,
            rd,
            rn,
            immr,
            imms,
            alias,
        })
    }

    pub fn ubfm(rd: Reg, rn: Reg, immr: u8, imms: u8) -> Result<Inst, EncodeError> {
        Self::bitfield_raw(BitfieldOp::Ubfm, rd, rn, immr, imms, BitfieldAlias::None)
    }

    pub fn sbfm(rd: Reg, rn: Reg, immr: u8, imms: u8) -> Result<Inst, EncodeError> {
        Self::bitfield_raw(BitfieldOp::Sbfm, rd, rn, immr, imms, BitfieldAlias::None)
    }

    pub fn bfm(rd: Reg, rn: Reg, immr: u8, imms: u8) -> Result<Inst, EncodeError> {
        Self::bitfield_raw(BitfieldOp::Bfm, rd, rn, immr, imms, BitfieldAlias::None)
    }

    /// `LSL <Rd>, <Rn>, #shift` — alias of `UBFM Rd, Rn, #(-shift MOD width), #(width-1-shift)`.
    pub fn lsl_imm(rd: Reg, rn: Reg, shift: u8) -> Result<Inst, EncodeError> {
        let width = if rd.is64() { 64u32 } else { 32 };
        if shift as u32 >= width {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "LSL immediate shift",
                value: shift as i64,
            });
        }
        let immr = ((width - shift as u32) % width) as u8;
        let imms = (width - 1 - shift as u32) as u8;
        Self::bitfield_raw(BitfieldOp::Ubfm, rd, rn, immr, imms, BitfieldAlias::Lsl)
    }

    /// `LSR <Rd>, <Rn>, #shift` — alias of `UBFM Rd, Rn, #shift, #(width-1)`.
    pub fn lsr_imm(rd: Reg, rn: Reg, shift: u8) -> Result<Inst, EncodeError> {
        let width = if rd.is64() { 64u32 } else { 32 };
        if shift as u32 >= width {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "LSR immediate shift",
                value: shift as i64,
            });
        }
        Self::bitfield_raw(
            BitfieldOp::Ubfm,
            rd,
            rn,
            shift,
            (width - 1) as u8,
            BitfieldAlias::Lsr,
        )
    }

    /// `ASR <Rd>, <Rn>, #shift` — alias of `SBFM Rd, Rn, #shift, #(width-1)`.
    pub fn asr_imm(rd: Reg, rn: Reg, shift: u8) -> Result<Inst, EncodeError> {
        let width = if rd.is64() { 64u32 } else { 32 };
        if shift as u32 >= width {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "ASR immediate shift",
                value: shift as i64,
            });
        }
        Self::bitfield_raw(
            BitfieldOp::Sbfm,
            rd,
            rn,
            shift,
            (width - 1) as u8,
            BitfieldAlias::Asr,
        )
    }

    pub fn sxtb(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::bitfield_raw(BitfieldOp::Sbfm, rd, rn, 0, 7, BitfieldAlias::Sxtb)
    }

    pub fn sxth(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::bitfield_raw(BitfieldOp::Sbfm, rd, rn, 0, 15, BitfieldAlias::Sxth)
    }

    /// `SXTW <Xd>, <Wn>` — the one sign-extend alias that changes width
    /// (32-bit source, 64-bit destination): encoded as `SBFM Xd, Xn, #0,
    /// #31` where `Xn` is `Wn` viewed as the bottom half of a 64-bit
    /// register (same physical register number, `sf`/`N` forced to 1 by
    /// `Rd` being 64-bit).
    pub fn sxtw(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        if !rd.is64() || rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "SXTW (Xd, Wn)",
            });
        }
        let rn64 = rn.with64(true);
        Self::bitfield_raw(BitfieldOp::Sbfm, rd, rn64, 0, 31, BitfieldAlias::Sxtw)
    }

    pub fn uxtb(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        if rd.is64() || rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "UXTB is a 32-bit-only alias",
            });
        }
        Self::bitfield_raw(BitfieldOp::Ubfm, rd, rn, 0, 7, BitfieldAlias::Uxtb)
    }

    pub fn uxth(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        if rd.is64() || rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "UXTH is a 32-bit-only alias",
            });
        }
        Self::bitfield_raw(BitfieldOp::Ubfm, rd, rn, 0, 15, BitfieldAlias::Uxth)
    }

    // ---------------- Data-processing (2-source): shifts, DIV ----------------

    fn data_proc_2(op: DataProc2Op, rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "data-processing (2 source)")?;
        check_same_width(rd, rm, "data-processing (2 source)")?;
        if rd.is_sp() || rn.is_sp() || rm.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "data-processing (2 source), no SP operand",
            });
        }
        Ok(Inst::DataProc2Source { op, rd, rn, rm })
    }

    pub fn udiv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Udiv, rd, rn, rm)
    }

    pub fn sdiv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Sdiv, rd, rn, rm)
    }

    pub fn lslv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Lslv, rd, rn, rm)
    }

    pub fn lsrv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Lsrv, rd, rn, rm)
    }

    pub fn asrv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Asrv, rd, rn, rm)
    }

    pub fn rorv(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_2(DataProc2Op::Rorv, rd, rn, rm)
    }

    // ---------------- Data-processing (3-source): MADD/MSUB/MUL/S|UMULH ----------------

    pub fn madd(rd: Reg, rn: Reg, rm: Reg, ra: Reg) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "MADD")?;
        check_same_width(rd, rm, "MADD")?;
        check_same_width(rd, ra, "MADD")?;
        if [rd, rn, rm, ra].iter().any(|r| r.is_sp()) {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "MADD (no SP operand)",
            });
        }
        Ok(Inst::DataProc3Source {
            op: DataProc3Op::Madd,
            rd,
            rn,
            rm,
            ra,
            is_mul_alias: false,
        })
    }

    pub fn msub(rd: Reg, rn: Reg, rm: Reg, ra: Reg) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "MSUB")?;
        check_same_width(rd, rm, "MSUB")?;
        check_same_width(rd, ra, "MSUB")?;
        if [rd, rn, rm, ra].iter().any(|r| r.is_sp()) {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "MSUB (no SP operand)",
            });
        }
        Ok(Inst::DataProc3Source {
            op: DataProc3Op::Msub,
            rd,
            rn,
            rm,
            ra,
            is_mul_alias: false,
        })
    }

    /// `MUL <Rd>, <Rn>, <Rm>` — alias of `MADD Rd, Rn, Rm, XZR/WZR`.
    pub fn mul(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        let ra = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        check_same_width(rd, rn, "MUL")?;
        check_same_width(rd, rm, "MUL")?;
        Ok(Inst::DataProc3Source {
            op: DataProc3Op::Madd,
            rd,
            rn,
            rm,
            ra,
            is_mul_alias: true,
        })
    }

    /// `SMULH`/`UMULH` are architecturally 64-bit-only (there is no 32-bit
    /// encoding — trying to build one from `W` registers is a genuine
    /// construction error, not a range check, so it errors here).
    pub fn smulh(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::mulh(DataProc3Op::Smulh, rd, rn, rm)
    }

    pub fn umulh(rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        Self::mulh(DataProc3Op::Umulh, rd, rn, rm)
    }

    fn mulh(op: DataProc3Op, rd: Reg, rn: Reg, rm: Reg) -> Result<Inst, EncodeError> {
        if !rd.is64() || !rn.is64() || !rm.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "SMULH/UMULH is 64-bit only",
            });
        }
        let ra = Reg::xzr();
        Ok(Inst::DataProc3Source {
            op,
            rd,
            rn,
            rm,
            ra,
            is_mul_alias: false,
        })
    }

    // ---------------- Data-processing (1-source): CLZ/RBIT/REV ----------------

    fn data_proc_1(op: DataProc1Op, rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "CLZ/RBIT/REV")?;
        if rd.is_sp() || rn.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "CLZ/RBIT/REV (no SP operand)",
            });
        }
        Ok(Inst::DataProc1Source { op, rd, rn })
    }

    pub fn clz(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_1(DataProc1Op::Clz, rd, rn)
    }

    pub fn rbit(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_1(DataProc1Op::Rbit, rd, rn)
    }

    pub fn rev(rd: Reg, rn: Reg) -> Result<Inst, EncodeError> {
        Self::data_proc_1(DataProc1Op::Rev, rd, rn)
    }

    // ---------------- Conditional select + CSET/CSETM/CINC/CINV/CNEG ----------------

    fn cond_select(
        op: CondSelectOp,
        rd: Reg,
        rn: Reg,
        rm: Reg,
        cond: Cond,
        alias: CondSelectAlias,
    ) -> Result<Inst, EncodeError> {
        check_same_width(rd, rn, "CSEL/CSINC/CSINV/CSNEG")?;
        check_same_width(rd, rm, "CSEL/CSINC/CSINV/CSNEG")?;
        if rd.is_sp() || rn.is_sp() || rm.is_sp() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "CSEL/CSINC/CSINV/CSNEG (no SP operand)",
            });
        }
        Ok(Inst::CondSelect {
            op,
            rd,
            rn,
            rm,
            cond,
            alias,
        })
    }

    pub fn csel(rd: Reg, rn: Reg, rm: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::cond_select(CondSelectOp::Csel, rd, rn, rm, cond, CondSelectAlias::None)
    }

    pub fn csinc(rd: Reg, rn: Reg, rm: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::cond_select(CondSelectOp::Csinc, rd, rn, rm, cond, CondSelectAlias::None)
    }

    pub fn csinv(rd: Reg, rn: Reg, rm: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::cond_select(CondSelectOp::Csinv, rd, rn, rm, cond, CondSelectAlias::None)
    }

    pub fn csneg(rd: Reg, rn: Reg, rm: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::cond_select(CondSelectOp::Csneg, rd, rn, rm, cond, CondSelectAlias::None)
    }

    /// `CSET <Rd>, <cond>` — alias of `CSINC Rd, ZR, ZR, invert(cond)`.
    /// `cond` must not be `AL`/`NV` (the assembler rejects those for this
    /// alias, since it would just be a very roundabout `MOV Rd, #1`/`#0`
    /// with no conditional meaning); enforced here rather than left to
    /// silently emit a technically-valid-but-nonsensical encoding.
    pub fn cset(rd: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::require_conditional(cond, "CSET")?;
        let z = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::cond_select(
            CondSelectOp::Csinc,
            rd,
            z,
            z,
            cond.inverted(),
            CondSelectAlias::Cset,
        )
    }

    pub fn csetm(rd: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::require_conditional(cond, "CSETM")?;
        let z = if rd.is64() { Reg::xzr() } else { Reg::wzr() };
        Self::cond_select(
            CondSelectOp::Csinv,
            rd,
            z,
            z,
            cond.inverted(),
            CondSelectAlias::Csetm,
        )
    }

    pub fn cinc(rd: Reg, rn: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::require_conditional(cond, "CINC")?;
        Self::cond_select(
            CondSelectOp::Csinc,
            rd,
            rn,
            rn,
            cond.inverted(),
            CondSelectAlias::Cinc,
        )
    }

    pub fn cinv(rd: Reg, rn: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::require_conditional(cond, "CINV")?;
        Self::cond_select(
            CondSelectOp::Csinv,
            rd,
            rn,
            rn,
            cond.inverted(),
            CondSelectAlias::Cinv,
        )
    }

    pub fn cneg(rd: Reg, rn: Reg, cond: Cond) -> Result<Inst, EncodeError> {
        Self::require_conditional(cond, "CNEG")?;
        Self::cond_select(
            CondSelectOp::Csneg,
            rd,
            rn,
            rn,
            cond.inverted(),
            CondSelectAlias::Cneg,
        )
    }

    fn require_conditional(cond: Cond, what: &'static str) -> Result<(), EncodeError> {
        if cond == Cond::AL || cond == Cond::NV {
            Err(EncodeError::InvalidShiftForForm { what })
        } else {
            Ok(())
        }
    }

    // ---------------- PC-relative address ----------------

    pub fn adr(rd: Reg, offset: AdrOffset) -> Result<Inst, EncodeError> {
        if !rd.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "ADR destination is always 64-bit",
            });
        }
        Ok(Inst::Adr { rd, offset })
    }

    pub fn adrp(rd: Reg, offset: AdrpOffset) -> Result<Inst, EncodeError> {
        if !rd.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "ADRP destination is always 64-bit",
            });
        }
        Ok(Inst::Adrp { rd, offset })
    }

    // ---------------- Branches ----------------

    pub fn b(offset: BranchOffset) -> Inst {
        Inst::Branch {
            link: false,
            offset,
        }
    }

    pub fn bl(offset: BranchOffset) -> Inst {
        Inst::Branch { link: true, offset }
    }

    pub fn b_cond(cond: Cond, offset: BranchOffset) -> Inst {
        Inst::BranchCond { cond, offset }
    }

    pub fn cbz(rt: Reg, offset: BranchOffset) -> Inst {
        Inst::CompareBranch {
            is64: rt.is64(),
            is_nonzero: false,
            rt,
            offset,
        }
    }

    pub fn cbnz(rt: Reg, offset: BranchOffset) -> Inst {
        Inst::CompareBranch {
            is64: rt.is64(),
            is_nonzero: true,
            rt,
            offset,
        }
    }

    pub fn tbz(rt: Reg, bit: u8, offset: BranchOffset) -> Result<Inst, EncodeError> {
        Self::test_branch(false, rt, bit, offset)
    }

    pub fn tbnz(rt: Reg, bit: u8, offset: BranchOffset) -> Result<Inst, EncodeError> {
        Self::test_branch(true, rt, bit, offset)
    }

    fn test_branch(
        is_nonzero: bool,
        rt: Reg,
        bit: u8,
        offset: BranchOffset,
    ) -> Result<Inst, EncodeError> {
        let max_bit = if rt.is64() { 63 } else { 31 };
        if bit > max_bit {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "TBZ/TBNZ bit index",
                value: bit as i64,
            });
        }
        Ok(Inst::TestBranch {
            is_nonzero,
            rt,
            bit,
            offset,
        })
    }

    pub fn br(rn: Reg) -> Result<Inst, EncodeError> {
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "BR target is always 64-bit",
            });
        }
        Ok(Inst::BranchReg { rn })
    }

    pub fn blr(rn: Reg) -> Result<Inst, EncodeError> {
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "BLR target is always 64-bit",
            });
        }
        Ok(Inst::BranchLinkReg { rn })
    }

    pub fn ret(rn: Reg) -> Result<Inst, EncodeError> {
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "RET target is always 64-bit",
            });
        }
        Ok(Inst::Ret { rn })
    }

    // ---------------- Loads/stores ----------------

    fn load_store(op: LdStOp, rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        if rt.is64() != op.rt_is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "load/store Rt width vs mnemonic",
            });
        }
        if !rn.is_sp() && rn.is_zr() {
            // XZR is legal as a base in the encoding (it just means "base
            // address 0"), but every real backend use is a stack/frame
            // pointer, so requiring a real GP-or-SP base here catches a
            // near-certain bug rather than a real use case.
            return Err(EncodeError::InvalidRegisterForForm {
                what: "load/store base register (XZR is not a real base; use an explicit address)",
            });
        }
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "load/store base register is always 64-bit",
            });
        }
        // Pre/post-indexed forms write the new address back into Rn; if Rt
        // is the same register (by number — a 32-bit Wt still names the
        // same physical register as its 64-bit Xn base), the load's
        // result and the writeback race, which the ARM ARM calls
        // UNPREDICTABLE and the system assembler rejects outright
        // (verified: `ldrsb w1, [x1, #0]!` -> "unpredictable LDR
        // instruction, writeback base is also a source").
        let has_writeback = matches!(mode, AddrMode::PreIndex(_) | AddrMode::PostIndex(_));
        if has_writeback && rt.encoding() == rn.encoding() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "load/store writeback: Rt and Rn name the same register",
            });
        }
        Ok(Inst::LoadStoreImm { op, rt, rn, mode })
    }

    pub fn ldr(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        let op = if rt.is64() {
            LdStOp::LdrX
        } else {
            LdStOp::LdrW
        };
        Self::load_store(op, rt, rn, mode)
    }

    pub fn str_(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        let op = if rt.is64() {
            LdStOp::StrX
        } else {
            LdStOp::StrW
        };
        Self::load_store(op, rt, rn, mode)
    }

    pub fn ldrb(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::LdrB, rt, rn, mode)
    }

    pub fn strb(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::StrB, rt, rn, mode)
    }

    pub fn ldrh(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::LdrH, rt, rn, mode)
    }

    pub fn strh(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::StrH, rt, rn, mode)
    }

    pub fn ldrsb(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::LdrSb { is64: rt.is64() }, rt, rn, mode)
    }

    pub fn ldrsh(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::LdrSh { is64: rt.is64() }, rt, rn, mode)
    }

    pub fn ldrsw(rt: Reg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        Self::load_store(LdStOp::LdrSw, rt, rn, mode)
    }

    pub fn ldp(
        rt1: Reg,
        rt2: Reg,
        rn: Reg,
        imm: SImm7Scaled,
        index: PairIndex,
    ) -> Result<Inst, EncodeError> {
        Self::load_store_pair(true, rt1, rt2, rn, imm, index)
    }

    pub fn stp(
        rt1: Reg,
        rt2: Reg,
        rn: Reg,
        imm: SImm7Scaled,
        index: PairIndex,
    ) -> Result<Inst, EncodeError> {
        Self::load_store_pair(false, rt1, rt2, rn, imm, index)
    }

    fn load_store_pair(
        is_load: bool,
        rt1: Reg,
        rt2: Reg,
        rn: Reg,
        imm: SImm7Scaled,
        index: PairIndex,
    ) -> Result<Inst, EncodeError> {
        check_same_width(rt1, rt2, "LDP/STP")?;
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "LDP/STP base register is always 64-bit",
            });
        }
        let has_writeback = matches!(index, PairIndex::PreIndex | PairIndex::PostIndex);
        if has_writeback && (rt1.encoding() == rn.encoding() || rt2.encoding() == rn.encoding()) {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "LDP/STP writeback: Rt1/Rt2 and Rn name the same register",
            });
        }
        if is_load && rt1.encoding() == rt2.encoding() {
            return Err(EncodeError::InvalidRegisterForForm {
                what: "LDP Rt1 and Rt2 name the same register",
            });
        }
        Ok(Inst::LoadStorePair {
            is_load,
            is64: rt1.is64(),
            rt1,
            rt2,
            rn,
            imm,
            index,
        })
    }

    // ---------------- System ----------------

    pub fn nop() -> Inst {
        Inst::System(SysOp::Nop)
    }

    pub fn brk(imm16: u16) -> Inst {
        Inst::System(SysOp::Brk(imm16))
    }

    pub fn svc(imm16: u16) -> Inst {
        Inst::System(SysOp::Svc(imm16))
    }

    pub fn udf(imm16: u16) -> Inst {
        Inst::System(SysOp::Udf(imm16))
    }
}
