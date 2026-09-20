//! `encode(&Inst) -> Result<u32, EncodeError>`: turns a validated `Inst`
//! into its 32-bit little-endian-on-the-wire word (as a native `u32`; the
//! caller's object writer decides byte order when it serializes). Every
//! field read here already went through a validating constructor in
//! `inst.rs`/`fp.rs`, so this function is pure bit-packing — the `Result`
//! exists for the handful of cross-operand checks (register width
//! agreement) that can only be caught once both operands are in hand, not
//! at a single operand's construction.

use crate::error::EncodeError;
use crate::inst::AddrMode;
use crate::inst::*;
use crate::reg::Reg;

fn sf(r: Reg) -> u32 {
    r.is64() as u32
}

pub fn encode(inst: &Inst) -> Result<u32, EncodeError> {
    Ok(match *inst {
        Inst::MovWide {
            op,
            rd,
            imm16,
            shift,
        } => {
            let opc = match op {
                MovWideOp::Movn => 0b00,
                MovWideOp::Movz => 0b10,
                MovWideOp::Movk => 0b11,
            };
            let hw = (shift / 16) as u32;
            (sf(rd) << 31)
                | (opc << 29)
                | (0b100101 << 23)
                | (hw << 21)
                | ((imm16 as u32) << 5)
                | rd.encoding()
        }

        Inst::AddSubImm {
            op,
            set_flags,
            rd,
            rn,
            imm,
            ..
        } => {
            let opbit = matches!(op, AddSubOp::Sub) as u32;
            (sf(rd) << 31)
                | (opbit << 30)
                | (set_flags as u32) << 29
                | (0b100010 << 23)
                | ((imm.shift12() as u32) << 22)
                | (imm.raw() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::AddSubShiftedReg {
            op,
            set_flags,
            rd,
            rn,
            rm,
            shift,
            ..
        } => {
            let opbit = matches!(op, AddSubOp::Sub) as u32;
            (sf(rd) << 31)
                | (opbit << 30)
                | ((set_flags as u32) << 29)
                | (0b01011 << 24)
                | (shift.kind().encoding() << 22)
                | (rm.encoding() << 16)
                | (shift.amount() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::AddSubExtendedReg {
            op,
            set_flags,
            rd,
            rn,
            rm,
            extend,
            ..
        } => {
            let opbit = matches!(op, AddSubOp::Sub) as u32;
            // bits[23:22] (the "opt" field) are always 0 for this form.
            (sf(rd) << 31)
                | (opbit << 30)
                | ((set_flags as u32) << 29)
                | (0b01011 << 24)
                | (1 << 21)
                | (rm.encoding() << 16)
                | (extend.kind().encoding() << 13)
                | (extend.amount() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::LogicalImmInst {
            op, rd, rn, imm, ..
        } => {
            let opc = match op {
                LogicalImmOp::And => 0b00,
                LogicalImmOp::Orr => 0b01,
                LogicalImmOp::Eor => 0b10,
                LogicalImmOp::Ands => 0b11,
            };
            (sf(rd) << 31)
                | (opc << 29)
                | (0b100100 << 23)
                | (imm.n() << 22)
                | (imm.immr() << 16)
                | (imm.imms() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::LogicalShiftedReg {
            op,
            rd,
            rn,
            rm,
            shift,
            ..
        } => {
            let (opc, n) = match op {
                LogicalShiftOp::And => (0b00, 0),
                LogicalShiftOp::Bic => (0b00, 1),
                LogicalShiftOp::Orr => (0b01, 0),
                LogicalShiftOp::Orn => (0b01, 1),
                LogicalShiftOp::Eor => (0b10, 0),
                LogicalShiftOp::Eon => (0b10, 1),
                LogicalShiftOp::Ands => (0b11, 0),
                LogicalShiftOp::Bics => (0b11, 1),
            };
            (sf(rd) << 31)
                | (opc << 29)
                | (0b01010 << 24)
                | (shift.kind().encoding() << 22)
                | (n << 21)
                | (rm.encoding() << 16)
                | (shift.amount() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::Bitfield {
            op,
            rd,
            rn,
            immr,
            imms,
            ..
        } => {
            let opc = match op {
                BitfieldOp::Sbfm => 0b00,
                BitfieldOp::Bfm => 0b01,
                BitfieldOp::Ubfm => 0b10,
            };
            let n = sf(rd); // N tracks sf for these three forms.
            (sf(rd) << 31)
                | (opc << 29)
                | (0b100110 << 23)
                | (n << 22)
                | ((immr as u32) << 16)
                | ((imms as u32) << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::DataProc2Source { op, rd, rn, rm } => {
            let opcode = match op {
                DataProc2Op::Udiv => 0b000010,
                DataProc2Op::Sdiv => 0b000011,
                DataProc2Op::Lslv => 0b001000,
                DataProc2Op::Lsrv => 0b001001,
                DataProc2Op::Asrv => 0b001010,
                DataProc2Op::Rorv => 0b001011,
            };
            (sf(rd) << 31)
                | (0b11010110 << 21)
                | (rm.encoding() << 16)
                | (opcode << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::DataProc3Source {
            op, rd, rn, rm, ra, ..
        } => {
            let (op31, o0) = match op {
                DataProc3Op::Madd => (0b000, 0),
                DataProc3Op::Msub => (0b000, 1),
                DataProc3Op::Smulh => (0b010, 0),
                DataProc3Op::Umulh => (0b110, 0),
            };
            // bits[30:29] (op54, fixed 00) and bits[23:22] (the low two
            // bits of what op31 extends) are always 0 for this subset.
            (sf(rd) << 31)
                | (0b11011 << 24)
                | (op31 << 21)
                | (rm.encoding() << 16)
                | (o0 << 15)
                | (ra.encoding() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::DataProc1Source { op, rd, rn } => {
            let opcode = match op {
                DataProc1Op::Rbit => 0b000000,
                DataProc1Op::Clz => 0b000100,
                DataProc1Op::Rev => {
                    if rd.is64() {
                        0b000011
                    } else {
                        0b000010
                    }
                }
            };
            (sf(rd) << 31)
                | (1 << 30)
                | (0b11010110 << 21)
                | (opcode << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::CondSelect {
            op,
            rd,
            rn,
            rm,
            cond,
            ..
        } => {
            let (opbit, op2) = match op {
                CondSelectOp::Csel => (0, 0b00),
                CondSelectOp::Csinc => (0, 0b01),
                CondSelectOp::Csinv => (1, 0b00),
                CondSelectOp::Csneg => (1, 0b01),
            };
            (sf(rd) << 31)
                | (opbit << 30)
                | (0b11010100 << 21)
                | (rm.encoding() << 16)
                | (cond.code() << 12)
                | (op2 << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::Adr { rd, offset } => {
            // op=0 (ADR) contributes nothing at bit 31; left implicit.
            let (immlo, immhi) = offset.encoding();
            (immlo << 29) | (0b10000 << 24) | (immhi << 5) | rd.encoding()
        }

        Inst::Adrp { rd, offset } => {
            let (immlo, immhi) = offset.encoding();
            (1 << 31) | (immlo << 29) | (0b10000 << 24) | (immhi << 5) | rd.encoding()
        }

        Inst::Branch { link, offset } => {
            ((link as u32) << 31) | (0b00101 << 26) | offset.encoding()
        }

        Inst::BranchCond { cond, offset } => {
            (0b0101010 << 25) | (offset.encoding() << 5) | cond.code()
        }

        Inst::CompareBranch {
            is64,
            is_nonzero,
            rt,
            offset,
        } => {
            ((is64 as u32) << 31)
                | (0b011010 << 25)
                | ((is_nonzero as u32) << 24)
                | (offset.encoding() << 5)
                | rt.encoding()
        }

        Inst::TestBranch {
            is_nonzero,
            rt,
            bit,
            offset,
        } => {
            let b5 = (bit >> 5) as u32 & 1;
            let b40 = (bit as u32) & 0x1F;
            (b5 << 31)
                | (0b011011 << 25)
                | ((is_nonzero as u32) << 24)
                | (b40 << 19)
                | (offset.encoding() << 5)
                | rt.encoding()
        }

        Inst::BranchReg { rn } => 0xD61F_0000 | (rn.encoding() << 5),
        Inst::BranchLinkReg { rn } => 0xD63F_0000 | (rn.encoding() << 5),
        Inst::Ret { rn } => 0xD65F_0000 | (rn.encoding() << 5),

        Inst::LoadStoreImm { op, rt, rn, mode } => encode_load_store_gp(op, rt, rn, mode),
        Inst::FpLoadStoreImm {
            is_load,
            rt,
            rn,
            mode,
        } => encode_load_store_fp(is_load, rt, rn, mode),

        Inst::LoadStorePair {
            is_load,
            is64,
            rt1,
            rt2,
            rn,
            imm,
            index,
        } => {
            let opc = if is64 { 0b10 } else { 0b00 };
            let mode = match index {
                PairIndex::PostIndex => 0b01,
                PairIndex::Offset => 0b10,
                PairIndex::PreIndex => 0b11,
            };
            (opc << 30)
                | (0b101 << 27)
                | (mode << 23)
                | ((is_load as u32) << 22)
                | (imm.encoding() << 15)
                | (rt2.encoding() << 10)
                | (rn.encoding() << 5)
                | rt1.encoding()
        }

        Inst::System(op) => match op {
            SysOp::Nop => 0xD503_201F,
            SysOp::Brk(imm16) => 0xD420_0000 | ((imm16 as u32) << 5),
            SysOp::Svc(imm16) => 0xD400_0001 | ((imm16 as u32) << 5),
            SysOp::Udf(imm16) => imm16 as u32,
        },

        Inst::FpDataProc1 { op, rd, rn } => {
            let opcode = match op {
                FpUnaryOp::Fmov => 0b000000,
                FpUnaryOp::Fabs => 0b000001,
                FpUnaryOp::Fneg => 0b000010,
                FpUnaryOp::Fsqrt => 0b000011,
            };
            let ty = rd.is_double() as u32;
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (opcode << 15)
                | (0b10000 << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::FpConvert { rd, rn } => {
            // Source type in the `type` field; opcode says the target.
            let (ty, opcode) = if rd.is_double() {
                (0u32, 0b000101u32)
            } else {
                (1u32, 0b000100u32)
            };
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (opcode << 15)
                | (0b10000 << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::FpDataProc2 { op, rd, rn, rm } => {
            let opcode = match op {
                FpBinOp::Fmul => 0b0000,
                FpBinOp::Fdiv => 0b0001,
                FpBinOp::Fadd => 0b0010,
                FpBinOp::Fsub => 0b0011,
            };
            let ty = rd.is_double() as u32;
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (rm.encoding() << 16)
                | (opcode << 12)
                | (0b10 << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::FpCompare { rn, rm } => {
            let ty = rn.is_double() as u32;
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (rm.encoding() << 16)
                | (0b1000 << 10)
                | (rn.encoding() << 5)
        }

        Inst::FpCondSelect { rd, rn, rm, cond } => {
            let ty = rd.is_double() as u32;
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (rm.encoding() << 16)
                | (cond.code() << 12)
                | (0b11 << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::FpImmMove { rd, imm } => {
            let ty = rd.is_double() as u32;
            // bits[9:5] (an unused imm5 field in this encoding) are 0.
            (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (imm.encoding() << 13)
                | (0b100 << 10)
                | rd.encoding()
        }

        Inst::FpToGp { rd, rn } => {
            let ty = rn.is_double() as u32;
            (sf(rd) << 31)
                | (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (0b110 << 16)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::GpToFp { rd, rn } => {
            let ty = rd.is_double() as u32;
            (sf(rn) << 31)
                | (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (0b111 << 16)
                | (rn.encoding() << 5)
                | rd.encoding()
        }

        Inst::FpIntConvert { op, gp, fp } => {
            let ty = fp.is_double() as u32;
            let (rmode, opcode) = match op {
                FpIntConvertOp::Scvtf => (0b00, 0b010),
                FpIntConvertOp::Ucvtf => (0b00, 0b011),
                FpIntConvertOp::Fcvtzs => (0b11, 0b000),
                FpIntConvertOp::Fcvtzu => (0b11, 0b001),
            };
            let is_int_to_fp = matches!(op, FpIntConvertOp::Scvtf | FpIntConvertOp::Ucvtf);
            let (rn_enc, rd_enc, sf_bit) = if is_int_to_fp {
                (gp.encoding(), fp.encoding(), sf(gp))
            } else {
                (fp.encoding(), gp.encoding(), sf(gp))
            };
            (sf_bit << 31)
                | (0b11110 << 24)
                | (ty << 22)
                | (1 << 21)
                | (rmode << 19)
                | (opcode << 16)
                | (rn_enc << 5)
                | rd_enc
        }

        Inst::FpMadd { rd, rn, rm, ra } => {
            let ty = rd.is_double() as u32;
            (0b11111 << 24)
                | (ty << 22)
                | (rm.encoding() << 16)
                | (ra.encoding() << 10)
                | (rn.encoding() << 5)
                | rd.encoding()
        }
    })
}

fn encode_load_store_gp(op: LdStOp, rt: Reg, rn: Reg, mode: AddrMode) -> u32 {
    let (size, opc) = op.size_opc();
    encode_load_store_common(size, 0, opc, rt.encoding(), rn, mode)
}

fn encode_load_store_fp(is_load: bool, rt: crate::reg::FpReg, rn: Reg, mode: AddrMode) -> u32 {
    // Scalar FP load/store: size encodes access width (S=10,D=11 -- note
    // this differs from the GP `size` field meaning), V=1, opc bit0 = L.
    let size = if rt.is_double() { 0b11 } else { 0b10 };
    let opc = if is_load { 0b01 } else { 0b00 };
    encode_load_store_common(size, 1, opc, rt.encoding(), rn, mode)
}

fn encode_load_store_common(size: u32, v: u32, opc: u32, rt: u32, rn: Reg, mode: AddrMode) -> u32 {
    // bits[25:24] select unsigned-offset (01) vs the immediate/register
    // sub-group (00); within that sub-group, bits[11:10] pick unscaled
    // (00, left implicit below — clippy's identity_op correctly flags
    // `| 0`), post-index (01) or pre-index (11).
    match mode {
        AddrMode::UnsignedOffset(imm) => {
            (size << 30)
                | (0b111 << 27)
                | (v << 26)
                | (0b01 << 24)
                | (opc << 22)
                | (imm.encoding() << 10)
                | (rn.encoding() << 5)
                | rt
        }
        AddrMode::Unscaled(imm) => {
            (size << 30)
                | (0b111 << 27)
                | (v << 26)
                | (opc << 22)
                | (imm.encoding() << 12)
                | (rn.encoding() << 5)
                | rt
        }
        AddrMode::PostIndex(imm) => {
            (size << 30)
                | (0b111 << 27)
                | (v << 26)
                | (opc << 22)
                | (imm.encoding() << 12)
                | (0b01 << 10)
                | (rn.encoding() << 5)
                | rt
        }
        AddrMode::PreIndex(imm) => {
            (size << 30)
                | (0b111 << 27)
                | (v << 26)
                | (opc << 22)
                | (imm.encoding() << 12)
                | (0b11 << 10)
                | (rn.encoding() << 5)
                | rt
        }
        AddrMode::RegOffset(ro) => {
            (size << 30)
                | (0b111 << 27)
                | (v << 26)
                | (opc << 22)
                | (1 << 21)
                | (ro.rm.encoding() << 16)
                | (ro.extend.option() << 13)
                | ((ro.shifted as u32) << 12)
                | (0b10 << 10)
                | (rn.encoding() << 5)
                | rt
        }
    }
}
