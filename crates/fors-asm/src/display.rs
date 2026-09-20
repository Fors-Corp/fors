//! `Display for Inst`: prints the exact assembly text the oracle test
//! feeds to the system assembler (`tests/`), and doubles as debug output.
//! Where an instruction was built through an alias constructor
//! (`Inst::cmp_imm`, `Inst::cset`, `Inst::lsl_imm`, ...), this prints the
//! alias spelling; see `inst.rs`'s module docs for why that's a `Display`
//! choice rather than a coverage requirement (the non-alias spelling is
//! equally valid input to the assembler and encodes identically).

use crate::inst::AddrMode;
use crate::inst::*;
use core::fmt;

/// `access_size` (bytes: 1/2/4/8) is needed only to print the `#n` after
/// `lsl`/`uxtw`/... for a *shifted* register-offset — the instruction
/// encoding itself stores just an on/off bit (the amount is always
/// `log2(access_size)`), so printing recovers the value from the size the
/// caller (an `Inst` variant, which knows its own access width) passes in,
/// rather than guessing it from the addressing mode alone.
fn fmt_addr(
    f: &mut fmt::Formatter<'_>,
    rn: crate::reg::Reg,
    mode: &AddrMode,
    access_size: u32,
) -> fmt::Result {
    match mode {
        AddrMode::UnsignedOffset(imm) => {
            if imm.bytes() == 0 {
                write!(f, "[{rn}]")
            } else {
                write!(f, "[{rn}, #{}]", imm.bytes())
            }
        }
        AddrMode::Unscaled(imm) => {
            if imm.value() == 0 {
                write!(f, "[{rn}]")
            } else {
                write!(f, "[{rn}, #{}]", imm.value())
            }
        }
        AddrMode::PreIndex(imm) => write!(f, "[{rn}, #{}]!", imm.value()),
        AddrMode::PostIndex(imm) => write!(f, "[{rn}], #{}", imm.value()),
        AddrMode::RegOffset(ro) => {
            let log2 = access_size.trailing_zeros();
            match ro.extend.mnemonic() {
                Some(name) => {
                    if ro.shifted {
                        write!(f, "[{rn}, {}, {name} #{log2}]", ro.rm)
                    } else {
                        write!(f, "[{rn}, {}, {name}]", ro.rm)
                    }
                }
                None => {
                    if ro.shifted {
                        write!(f, "[{rn}, {}, lsl #{log2}]", ro.rm)
                    } else {
                        write!(f, "[{rn}, {}]", ro.rm)
                    }
                }
            }
        }
    }
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Inst::MovWide {
                op,
                rd,
                imm16,
                shift,
            } => {
                let mnem = match op {
                    MovWideOp::Movz => "movz",
                    MovWideOp::Movn => "movn",
                    MovWideOp::Movk => "movk",
                };
                if shift == 0 {
                    write!(f, "{mnem} {rd}, #{imm16}")
                } else {
                    write!(f, "{mnem} {rd}, #{imm16}, lsl #{shift}")
                }
            }

            Inst::AddSubImm {
                op,
                set_flags,
                rd,
                rn,
                imm,
                alias,
            } => match alias {
                AddSubAlias::Cmp => write!(f, "cmp {rn}, {imm}"),
                AddSubAlias::Cmn => write!(f, "cmn {rn}, {imm}"),
                AddSubAlias::Mov => write!(f, "mov {rd}, {rn}"),
                _ => {
                    let mnem = match (op, set_flags) {
                        (AddSubOp::Add, false) => "add",
                        (AddSubOp::Add, true) => "adds",
                        (AddSubOp::Sub, false) => "sub",
                        (AddSubOp::Sub, true) => "subs",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {imm}")
                }
            },

            Inst::AddSubShiftedReg {
                op,
                set_flags,
                rd,
                rn,
                rm,
                shift,
                alias,
            } => match alias {
                AddSubAlias::Cmp => write!(f, "cmp {rn}, {rm}{shift}"),
                AddSubAlias::Cmn => write!(f, "cmn {rn}, {rm}{shift}"),
                AddSubAlias::Neg => write!(f, "neg {rd}, {rm}{shift}"),
                AddSubAlias::Negs => write!(f, "negs {rd}, {rm}{shift}"),
                _ => {
                    let mnem = match (op, set_flags) {
                        (AddSubOp::Add, false) => "add",
                        (AddSubOp::Add, true) => "adds",
                        (AddSubOp::Sub, false) => "sub",
                        (AddSubOp::Sub, true) => "subs",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {rm}{shift}")
                }
            },

            Inst::AddSubExtendedReg {
                op,
                set_flags,
                rd,
                rn,
                rm,
                extend,
                alias,
            } => match alias {
                AddSubAlias::Cmp => write!(f, "cmp {rn}, {rm}{extend}"),
                AddSubAlias::Cmn => write!(f, "cmn {rn}, {rm}{extend}"),
                _ => {
                    let mnem = match (op, set_flags) {
                        (AddSubOp::Add, false) => "add",
                        (AddSubOp::Add, true) => "adds",
                        (AddSubOp::Sub, false) => "sub",
                        (AddSubOp::Sub, true) => "subs",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {rm}{extend}")
                }
            },

            Inst::LogicalImmInst {
                op,
                rd,
                rn,
                imm,
                alias,
            } => match alias {
                LogicalAlias::Tst => write!(f, "tst {rn}, {imm}"),
                _ => {
                    let mnem = match op {
                        LogicalImmOp::And => "and",
                        LogicalImmOp::Orr => "orr",
                        LogicalImmOp::Eor => "eor",
                        LogicalImmOp::Ands => "ands",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {imm}")
                }
            },

            Inst::LogicalShiftedReg {
                op,
                rd,
                rn,
                rm,
                shift,
                alias,
            } => match alias {
                LogicalAlias::Mvn => write!(f, "mvn {rd}, {rm}{shift}"),
                LogicalAlias::Tst => write!(f, "tst {rn}, {rm}{shift}"),
                LogicalAlias::Mov => write!(f, "mov {rd}, {rm}"),
                LogicalAlias::None => {
                    let mnem = match op {
                        LogicalShiftOp::And => "and",
                        LogicalShiftOp::Bic => "bic",
                        LogicalShiftOp::Orr => "orr",
                        LogicalShiftOp::Orn => "orn",
                        LogicalShiftOp::Eor => "eor",
                        LogicalShiftOp::Eon => "eon",
                        LogicalShiftOp::Ands => "ands",
                        LogicalShiftOp::Bics => "bics",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {rm}{shift}")
                }
            },

            Inst::Bitfield {
                op,
                rd,
                rn,
                immr,
                imms,
                alias,
            } => match alias {
                BitfieldAlias::Lsl => write!(
                    f,
                    "lsl {rd}, {rn}, #{}",
                    (if rd.is64() { 64u32 } else { 32u32 }) - imms as u32 - 1
                ),
                BitfieldAlias::Lsr => write!(f, "lsr {rd}, {rn}, #{immr}"),
                BitfieldAlias::Asr => write!(f, "asr {rd}, {rn}, #{immr}"),
                BitfieldAlias::Sxtb => write!(f, "sxtb {rd}, {rn}"),
                BitfieldAlias::Sxth => write!(f, "sxth {rd}, {rn}"),
                BitfieldAlias::Sxtw => write!(f, "sxtw {rd}, {rn}"),
                BitfieldAlias::Uxtb => write!(f, "uxtb {rd}, {rn}"),
                BitfieldAlias::Uxth => write!(f, "uxth {rd}, {rn}"),
                BitfieldAlias::None => {
                    let mnem = match op {
                        BitfieldOp::Sbfm => "sbfm",
                        BitfieldOp::Bfm => "bfm",
                        BitfieldOp::Ubfm => "ubfm",
                    };
                    write!(f, "{mnem} {rd}, {rn}, #{immr}, #{imms}")
                }
            },

            Inst::DataProc2Source { op, rd, rn, rm } => {
                let mnem = match op {
                    DataProc2Op::Udiv => "udiv",
                    DataProc2Op::Sdiv => "sdiv",
                    DataProc2Op::Lslv => "lsl",
                    DataProc2Op::Lsrv => "lsr",
                    DataProc2Op::Asrv => "asr",
                    DataProc2Op::Rorv => "ror",
                };
                write!(f, "{mnem} {rd}, {rn}, {rm}")
            }

            Inst::DataProc3Source {
                op,
                rd,
                rn,
                rm,
                ra,
                is_mul_alias,
            } => {
                if is_mul_alias {
                    write!(f, "mul {rd}, {rn}, {rm}")
                } else {
                    let mnem = match op {
                        DataProc3Op::Madd => "madd",
                        DataProc3Op::Msub => "msub",
                        DataProc3Op::Smulh => "smulh",
                        DataProc3Op::Umulh => "umulh",
                    };
                    if matches!(op, DataProc3Op::Smulh | DataProc3Op::Umulh) {
                        write!(f, "{mnem} {rd}, {rn}, {rm}")
                    } else {
                        write!(f, "{mnem} {rd}, {rn}, {rm}, {ra}")
                    }
                }
            }

            Inst::DataProc1Source { op, rd, rn } => {
                let mnem = match op {
                    DataProc1Op::Rbit => "rbit",
                    DataProc1Op::Clz => "clz",
                    DataProc1Op::Rev => "rev",
                };
                write!(f, "{mnem} {rd}, {rn}")
            }

            Inst::CondSelect {
                op,
                rd,
                rn,
                rm,
                cond,
                alias,
            } => match alias {
                CondSelectAlias::Cset => write!(f, "cset {rd}, {}", cond.inverted()),
                CondSelectAlias::Csetm => write!(f, "csetm {rd}, {}", cond.inverted()),
                CondSelectAlias::Cinc => write!(f, "cinc {rd}, {rn}, {}", cond.inverted()),
                CondSelectAlias::Cinv => write!(f, "cinv {rd}, {rn}, {}", cond.inverted()),
                CondSelectAlias::Cneg => write!(f, "cneg {rd}, {rn}, {}", cond.inverted()),
                CondSelectAlias::None => {
                    let mnem = match op {
                        CondSelectOp::Csel => "csel",
                        CondSelectOp::Csinc => "csinc",
                        CondSelectOp::Csinv => "csinv",
                        CondSelectOp::Csneg => "csneg",
                    };
                    write!(f, "{mnem} {rd}, {rn}, {rm}, {cond}")
                }
            },

            Inst::Adr { rd, offset } => write!(f, "adr {rd}, {offset}"),
            Inst::Adrp { rd, offset } => write!(f, "adrp {rd}, {offset}"),

            Inst::Branch { link, offset } => {
                write!(f, "{} #{}", if link { "bl" } else { "b" }, offset.bytes())
            }
            Inst::BranchCond { cond, offset } => write!(f, "b.{cond} #{}", offset.bytes()),
            Inst::CompareBranch {
                is_nonzero,
                rt,
                offset,
                ..
            } => write!(
                f,
                "{} {rt}, #{}",
                if is_nonzero { "cbnz" } else { "cbz" },
                offset.bytes()
            ),
            Inst::TestBranch {
                is_nonzero,
                rt,
                bit,
                offset,
            } => write!(
                f,
                "{} {rt}, #{bit}, #{}",
                if is_nonzero { "tbnz" } else { "tbz" },
                offset.bytes()
            ),
            Inst::BranchReg { rn } => write!(f, "br {rn}"),
            Inst::BranchLinkReg { rn } => write!(f, "blr {rn}"),
            Inst::Ret { rn } => {
                if rn == crate::reg::Reg::x(30) {
                    write!(f, "ret")
                } else {
                    write!(f, "ret {rn}")
                }
            }

            Inst::LoadStoreImm { op, rt, rn, mode } => {
                let mnem = if matches!(mode, AddrMode::Unscaled(_)) {
                    op.unscaled_mnemonic()
                } else {
                    op.mnemonic()
                };
                write!(f, "{mnem} {rt}, ")?;
                fmt_addr(f, rn, &mode, op.access_size())
            }

            Inst::FpLoadStoreImm {
                is_load,
                rt,
                rn,
                mode,
            } => {
                let is_unscaled = matches!(mode, AddrMode::Unscaled(_));
                let mnem = match (is_load, is_unscaled) {
                    (true, false) => "ldr",
                    (true, true) => "ldur",
                    (false, false) => "str",
                    (false, true) => "stur",
                };
                write!(f, "{mnem} {rt}, ")?;
                let access_size = if rt.is_double() { 8 } else { 4 };
                fmt_addr(f, rn, &mode, access_size)
            }

            Inst::LoadStorePair {
                is_load,
                rt1,
                rt2,
                rn,
                imm,
                index,
                ..
            } => {
                let mnem = if is_load { "ldp" } else { "stp" };
                match index {
                    PairIndex::Offset => {
                        if imm.bytes() == 0 {
                            write!(f, "{mnem} {rt1}, {rt2}, [{rn}]")
                        } else {
                            write!(f, "{mnem} {rt1}, {rt2}, [{rn}, #{}]", imm.bytes())
                        }
                    }
                    PairIndex::PreIndex => {
                        write!(f, "{mnem} {rt1}, {rt2}, [{rn}, #{}]!", imm.bytes())
                    }
                    PairIndex::PostIndex => {
                        write!(f, "{mnem} {rt1}, {rt2}, [{rn}], #{}", imm.bytes())
                    }
                }
            }

            Inst::System(op) => match op {
                SysOp::Nop => write!(f, "nop"),
                SysOp::Brk(imm) => write!(f, "brk #{imm}"),
                SysOp::Svc(imm) => write!(f, "svc #{imm}"),
                SysOp::Udf(imm) => write!(f, "udf #{imm}"),
            },

            Inst::FpDataProc1 { op, rd, rn } => {
                let mnem = match op {
                    FpUnaryOp::Fmov => "fmov",
                    FpUnaryOp::Fabs => "fabs",
                    FpUnaryOp::Fneg => "fneg",
                    FpUnaryOp::Fsqrt => "fsqrt",
                };
                write!(f, "{mnem} {rd}, {rn}")
            }
            Inst::FpConvert { rd, rn } => write!(f, "fcvt {rd}, {rn}"),
            Inst::FpDataProc2 { op, rd, rn, rm } => {
                let mnem = match op {
                    FpBinOp::Fadd => "fadd",
                    FpBinOp::Fsub => "fsub",
                    FpBinOp::Fmul => "fmul",
                    FpBinOp::Fdiv => "fdiv",
                };
                write!(f, "{mnem} {rd}, {rn}, {rm}")
            }
            Inst::FpCompare { rn, rm } => write!(f, "fcmp {rn}, {rm}"),
            Inst::FpCondSelect { rd, rn, rm, cond } => write!(f, "fcsel {rd}, {rn}, {rm}, {cond}"),
            Inst::FpImmMove { rd, imm } => write!(f, "fmov {rd}, {imm}"),
            Inst::FpToGp { rd, rn } => write!(f, "fmov {rd}, {rn}"),
            Inst::GpToFp { rd, rn } => write!(f, "fmov {rd}, {rn}"),
            Inst::FpIntConvert { op, gp, fp } => {
                let mnem = match op {
                    FpIntConvertOp::Scvtf => "scvtf",
                    FpIntConvertOp::Ucvtf => "ucvtf",
                    FpIntConvertOp::Fcvtzs => "fcvtzs",
                    FpIntConvertOp::Fcvtzu => "fcvtzu",
                };
                match op {
                    FpIntConvertOp::Scvtf | FpIntConvertOp::Ucvtf => write!(f, "{mnem} {fp}, {gp}"),
                    FpIntConvertOp::Fcvtzs | FpIntConvertOp::Fcvtzu => {
                        write!(f, "{mnem} {gp}, {fp}")
                    }
                }
            }
            Inst::FpMadd { rd, rn, rm, ra } => write!(f, "fmadd {rd}, {rn}, {rm}, {ra}"),
        }
    }
}
