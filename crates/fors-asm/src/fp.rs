//! Scalar floating-point instruction constructors (`impl Inst`, continued
//! from `inst.rs` — same enum, split here purely for file size). Covers
//! the subset a strict-IEEE, no-contraction dev backend needs: `FMADD` is
//! included (the ISA has no separate "no-fuse" multiply-add — leaving it
//! out would mean the encoder itself couldn't represent a real
//! instruction), but this crate's own docs below say the codegen this
//! serves must never emit it by default, exactly like the task brief:
//! Fors is strict IEEE-754 with no FP contraction, so `a*b+c` always
//! lowers to a separate `FMUL`+`FADD`, never `FMADD` — `FMADD` would round
//! once instead of twice and silently change results.
//!
//! ```
//! # use fors_asm::inst::Inst;
//! # use fors_asm::reg::FpReg;
//! // What Fors's codegen emits for `a * b + c` (two roundings, matching
//! // the source language's semantics exactly):
//! let mul = Inst::fmul(FpReg::d(3), FpReg::d(0), FpReg::d(1)).unwrap();
//! let add = Inst::fadd(FpReg::d(3), FpReg::d(3), FpReg::d(2)).unwrap();
//! // NOT this, even though it's one instruction instead of two — FMADD
//! // computes the product at infinite precision before the one rounding,
//! // which is a different (if often "more accurate") answer:
//! let _fused_never_emitted_by_default = Inst::fmadd(FpReg::d(3), FpReg::d(0), FpReg::d(1), FpReg::d(2)).unwrap();
//! # let _ = (mul, add);
//! ```

use crate::error::EncodeError;
use crate::fpimm::FpImm8;
use crate::inst::AddrMode;
use crate::inst::{FpBinOp, FpIntConvertOp, FpUnaryOp, Inst};
use crate::operand::Cond;
use crate::reg::{FpReg, Reg};

fn check_same_fp_width(a: FpReg, b: FpReg, what: &'static str) -> Result<(), EncodeError> {
    if a.is_double() != b.is_double() {
        Err(EncodeError::RegisterWidthMismatch { what })
    } else {
        Ok(())
    }
}

impl Inst {
    pub fn fmov_reg(rd: FpReg, rn: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FMOV (register)")?;
        Ok(Inst::FpDataProc1 {
            op: FpUnaryOp::Fmov,
            rd,
            rn,
        })
    }

    pub fn fabs(rd: FpReg, rn: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FABS")?;
        Ok(Inst::FpDataProc1 {
            op: FpUnaryOp::Fabs,
            rd,
            rn,
        })
    }

    pub fn fneg(rd: FpReg, rn: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FNEG")?;
        Ok(Inst::FpDataProc1 {
            op: FpUnaryOp::Fneg,
            rd,
            rn,
        })
    }

    pub fn fsqrt(rd: FpReg, rn: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FSQRT")?;
        Ok(Inst::FpDataProc1 {
            op: FpUnaryOp::Fsqrt,
            rd,
            rn,
        })
    }

    /// `FCVT <Dd>, <Sn>` or `FCVT <Sd>, <Dn>` — the two widths must differ
    /// (that's the entire point of this instruction; same-width would be
    /// `FMOV`).
    pub fn fcvt(rd: FpReg, rn: FpReg) -> Result<Inst, EncodeError> {
        if rd.is_double() == rn.is_double() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "FCVT requires differing S/D widths (use FMOV for same-width)",
            });
        }
        Ok(Inst::FpConvert { rd, rn })
    }

    pub fn fadd(rd: FpReg, rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        Self::fp_binop(FpBinOp::Fadd, rd, rn, rm)
    }

    pub fn fsub(rd: FpReg, rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        Self::fp_binop(FpBinOp::Fsub, rd, rn, rm)
    }

    pub fn fmul(rd: FpReg, rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        Self::fp_binop(FpBinOp::Fmul, rd, rn, rm)
    }

    pub fn fdiv(rd: FpReg, rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        Self::fp_binop(FpBinOp::Fdiv, rd, rn, rm)
    }

    fn fp_binop(op: FpBinOp, rd: FpReg, rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FADD/FSUB/FMUL/FDIV")?;
        check_same_fp_width(rd, rm, "FADD/FSUB/FMUL/FDIV")?;
        Ok(Inst::FpDataProc2 { op, rd, rn, rm })
    }

    /// `FMADD`, deliberately included for completeness (see module docs):
    /// never emitted by Fors's own codegen, which is strict IEEE with no
    /// FP contraction.
    pub fn fmadd(rd: FpReg, rn: FpReg, rm: FpReg, ra: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FMADD")?;
        check_same_fp_width(rd, rm, "FMADD")?;
        check_same_fp_width(rd, ra, "FMADD")?;
        Ok(Inst::FpMadd { rd, rn, rm, ra })
    }

    pub fn fcmp(rn: FpReg, rm: FpReg) -> Result<Inst, EncodeError> {
        check_same_fp_width(rn, rm, "FCMP")?;
        Ok(Inst::FpCompare { rn, rm })
    }

    pub fn fcsel(rd: FpReg, rn: FpReg, rm: FpReg, cond: Cond) -> Result<Inst, EncodeError> {
        check_same_fp_width(rd, rn, "FCSEL")?;
        check_same_fp_width(rd, rm, "FCSEL")?;
        Ok(Inst::FpCondSelect { rd, rn, rm, cond })
    }

    pub fn fmov_imm(rd: FpReg, imm: FpImm8) -> Result<Inst, EncodeError> {
        if rd.is_double() != imm.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "FMOV immediate width vs destination register",
            });
        }
        Ok(Inst::FpImmMove { rd, imm })
    }

    /// `FMOV <Xd|Wd>, <Dn|Sn>` — GP destination, FP source; widths must
    /// match (`X`<->`D`, `W`<->`S`).
    pub fn fmov_to_gp(rd: Reg, rn: FpReg) -> Result<Inst, EncodeError> {
        if rd.is64() != rn.is_double() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "FMOV Xd/Wd, Dn/Sn width mismatch",
            });
        }
        Ok(Inst::FpToGp { rd, rn })
    }

    /// `FMOV <Dd|Sd>, <Xn|Wn>` — FP destination, GP source.
    pub fn fmov_from_gp(rd: FpReg, rn: Reg) -> Result<Inst, EncodeError> {
        if rd.is_double() != rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "FMOV Dd/Sd, Xn/Wn width mismatch",
            });
        }
        Ok(Inst::GpToFp { rd, rn })
    }

    pub fn scvtf(rd: FpReg, rn: Reg) -> Result<Inst, EncodeError> {
        Ok(Inst::FpIntConvert {
            op: FpIntConvertOp::Scvtf,
            gp: rn,
            fp: rd,
        })
    }

    pub fn ucvtf(rd: FpReg, rn: Reg) -> Result<Inst, EncodeError> {
        Ok(Inst::FpIntConvert {
            op: FpIntConvertOp::Ucvtf,
            gp: rn,
            fp: rd,
        })
    }

    pub fn fcvtzs(rd: Reg, rn: FpReg) -> Result<Inst, EncodeError> {
        Ok(Inst::FpIntConvert {
            op: FpIntConvertOp::Fcvtzs,
            gp: rd,
            fp: rn,
        })
    }

    pub fn fcvtzu(rd: Reg, rn: FpReg) -> Result<Inst, EncodeError> {
        Ok(Inst::FpIntConvert {
            op: FpIntConvertOp::Fcvtzu,
            gp: rd,
            fp: rn,
        })
    }

    pub fn ldr_fp(rt: FpReg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "load/store base register is always 64-bit",
            });
        }
        Ok(Inst::FpLoadStoreImm {
            is_load: true,
            rt,
            rn,
            mode,
        })
    }

    pub fn str_fp(rt: FpReg, rn: Reg, mode: AddrMode) -> Result<Inst, EncodeError> {
        if !rn.is64() {
            return Err(EncodeError::RegisterWidthMismatch {
                what: "load/store base register is always 64-bit",
            });
        }
        Ok(Inst::FpLoadStoreImm {
            is_load: false,
            rt,
            rn,
            mode,
        })
    }
}
