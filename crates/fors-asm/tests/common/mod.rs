//! Shared, deterministic test-case generator used by both the macOS
//! oracle test (`oracle.rs`, compares every case against the system
//! assembler) and the portable golden test (`golden.rs`, compares the same
//! cases against a checked-in golden file on any host/OS). Keeping ONE
//! generator means the two tests can never silently drift apart into
//! testing different things.
//!
//! No wall-clock time, no OS randomness anywhere in this file: the only
//! randomness is a fixed-seed xorshift64, so `all_cases()` produces the
//! exact same `Vec` on every run, on every machine.

#![allow(dead_code)] // not every helper is used by both consumers.

use fors_asm::Inst;
use fors_asm::inst::*;
use fors_asm::operand::*;
use fors_asm::reg::{FpReg, Reg};

/// xorshift64 (Marsaglia). Fixed, hard-coded seed — deliberately not
/// `SystemTime`/`RandomState`/etc, so `all_cases()` is reproducible byte
/// for byte on any machine, any OS, any run.
pub struct XorShift64(u64);

impl XorShift64 {
    pub const SEED: u64 = 0x9E3779B97F4A7C15;

    pub fn new() -> Self {
        XorShift64(Self::SEED)
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    pub fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[(self.next_u64() as usize) % xs.len()]
    }

    /// Inclusive range.
    pub fn range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

#[derive(Clone)]
pub struct Case {
    pub inst: Inst,
    pub asm: String,
}

fn case(inst: Inst) -> Case {
    let asm = inst.to_string();
    Case { inst, asm }
}

// ---- representative register pools (not exhaustive per-form; register
// FIELD placement itself is checked exhaustively once, separately, by
// `register_field_sweep_cases`) ----

fn x_sample() -> Vec<Reg> {
    vec![
        Reg::x(0),
        Reg::x(1),
        Reg::x(9),
        Reg::x(15),
        Reg::x(28),
        Reg::x(29),
        Reg::x(30),
        Reg::xzr(),
    ]
}

fn w_sample() -> Vec<Reg> {
    vec![
        Reg::w(0),
        Reg::w(1),
        Reg::w(9),
        Reg::w(15),
        Reg::w(28),
        Reg::w(29),
        Reg::w(30),
        Reg::wzr(),
    ]
}

fn x_sample_no_zr() -> Vec<Reg> {
    vec![
        Reg::x(0),
        Reg::x(1),
        Reg::x(9),
        Reg::x(15),
        Reg::x(28),
        Reg::x(29),
        Reg::x(30),
    ]
}

fn w_sample_no_zr() -> Vec<Reg> {
    vec![
        Reg::w(0),
        Reg::w(1),
        Reg::w(9),
        Reg::w(15),
        Reg::w(28),
        Reg::w(29),
        Reg::w(30),
    ]
}

fn base_sample() -> Vec<Reg> {
    // LDR/STR/LDP/STP base registers: real GP or SP, never XZR (see
    // `Inst::load_store`'s doc comment for why that's rejected).
    vec![Reg::sp(), Reg::x(1), Reg::x(19), Reg::x(29)]
}

fn fp_d_sample() -> Vec<FpReg> {
    (0..8)
        .map(FpReg::d)
        .chain([FpReg::d(30), FpReg::d(31)])
        .collect()
}

fn fp_s_sample() -> Vec<FpReg> {
    (0..8)
        .map(FpReg::s)
        .chain([FpReg::s(30), FpReg::s(31)])
        .collect()
}

fn conds() -> [Cond; 16] {
    Cond::ALL
}

fn conds_no_al_nv() -> Vec<Cond> {
    Cond::ALL
        .into_iter()
        .filter(|&c| c != Cond::AL && c != Cond::NV)
        .collect()
}

/// Exhaustive sweep of the Rd/Rn/Rm register FIELD (0..=30, plus the
/// SP/XZR flavor of 31 where each form allows it) using one simple
/// instruction per field, so "every register including X0/X30/SP/XZR" is
/// covered exactly rather than approximated by the samples above (which
/// exist to keep the combinatorial forms below tractable).
pub fn register_field_sweep_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    // Rd field, 64-bit and 32-bit, via MOVZ (simplest single-register-field form).
    for n in 0..=30u8 {
        cases.push(case(Inst::movz(Reg::x(n), 1, 0).unwrap()));
        cases.push(case(Inst::movz(Reg::w(n), 1, 0).unwrap()));
    }
    // Rd/Rn/Rm fields together via ADD (shifted register), which has all three.
    for n in 0..=30u8 {
        cases.push(case(
            Inst::add_shifted(Reg::x(n), Reg::x(1), Reg::x(2), RegShift::none()).unwrap(),
        ));
        cases.push(case(
            Inst::add_shifted(Reg::x(0), Reg::x(n), Reg::x(2), RegShift::none()).unwrap(),
        ));
        cases.push(case(
            Inst::add_shifted(Reg::x(0), Reg::x(1), Reg::x(n), RegShift::none()).unwrap(),
        ));
    }
    // XZR/WZR and SP/WSP specifically, in every field position that
    // legally accepts them.
    cases.push(case(
        Inst::add_shifted(Reg::xzr(), Reg::x(1), Reg::x(2), RegShift::none()).unwrap(),
    ));
    cases.push(case(
        Inst::add_shifted(Reg::x(0), Reg::xzr(), Reg::x(2), RegShift::none()).unwrap(),
    ));
    cases.push(case(
        Inst::add_shifted(Reg::x(0), Reg::x(1), Reg::xzr(), RegShift::none()).unwrap(),
    ));
    cases.push(case(
        Inst::add_imm(Reg::sp(), Reg::x(1), Uimm12Lsl::new(4).unwrap()).unwrap(),
    ));
    cases.push(case(
        Inst::add_imm(Reg::x(0), Reg::sp(), Uimm12Lsl::new(4).unwrap()).unwrap(),
    ));
    cases.push(case(Inst::mov_sp(Reg::sp(), Reg::x(5)).unwrap()));
    cases.push(case(Inst::mov_sp(Reg::x(5), Reg::sp()).unwrap()));
    cases
}

pub fn all_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let mut rng = XorShift64::new();

    cases.extend(register_field_sweep_cases());

    // ---- MOVZ/MOVN/MOVK ----
    for &is64 in &[true, false] {
        let shifts: &[u8] = if is64 { &[0, 16, 32, 48] } else { &[0, 16] };
        let regs = if is64 {
            x_sample_no_zr()
        } else {
            w_sample_no_zr()
        };
        for &shift in shifts {
            for &imm in &[0u16, 1, 0x1234, 0x8000, 0xFFFE, 0xFFFF] {
                for &rn in &regs {
                    cases.push(case(Inst::movz(rn, imm, shift).unwrap()));
                    cases.push(case(Inst::movn(rn, imm, shift).unwrap()));
                    cases.push(case(Inst::movk(rn, imm, shift).unwrap()));
                }
            }
        }
    }

    // ---- ADD/SUB immediate (+ CMP/CMN/MOV-SP aliases) ----
    let imm12_samples = [0u64, 1, 4095, 4096, 8192, 4095 * 4096, 0x123];
    for &imm_v in &imm12_samples {
        let imm = Uimm12Lsl::new(imm_v).unwrap();
        for &rd in &x_sample_no_zr() {
            for &rn in &base_sample() {
                cases.push(case(Inst::add_imm(rd, rn, imm).unwrap()));
                cases.push(case(Inst::sub_imm(rd, rn, imm).unwrap()));
                cases.push(case(Inst::adds_imm(rd, rn, imm).unwrap()));
                cases.push(case(Inst::subs_imm(rd, rn, imm).unwrap()));
            }
        }
        // CMP/CMN's Rn follows the same "field 31 is always SP" rule as
        // plain ADD/SUB immediate (see `Inst::add_sub_imm_common`'s doc
        // comment) — XZR/WZR is not a legal Rn here, so sample from
        // `base_sample()` (SP + real registers), not `x_sample()`/
        // `w_sample()` (which include the zero register).
        for &rn in &base_sample() {
            cases.push(case(Inst::cmp_imm(rn, imm).unwrap()));
            cases.push(case(Inst::cmn_imm(rn, imm).unwrap()));
        }
        let imm32 = Uimm12Lsl::new(imm_v.min(0xFFF)).unwrap();
        for &rn in &w_sample_no_zr() {
            cases.push(case(Inst::cmp_imm(rn, imm32).unwrap()));
        }
    }
    for &rd in &x_sample_no_zr() {
        cases.push(case(Inst::mov_sp(rd, Reg::sp()).unwrap()));
        cases.push(case(Inst::mov_sp(Reg::sp(), rd).unwrap()));
    }
    // WSP (the 32-bit view of the stack pointer): exercised separately
    // from SP/XZR above so it isn't just a type that exists but is never
    // fed through the oracle.
    for &rd in &w_sample_no_zr() {
        cases.push(case(Inst::mov_sp(rd, Reg::wsp()).unwrap()));
        cases.push(case(Inst::mov_sp(Reg::wsp(), rd).unwrap()));
    }
    for &imm_v in &[0u64, 1, 4095] {
        let imm32 = Uimm12Lsl::new(imm_v).unwrap();
        cases.push(case(Inst::add_imm(Reg::w(2), Reg::wsp(), imm32).unwrap()));
        cases.push(case(Inst::add_imm(Reg::wsp(), Reg::w(2), imm32).unwrap()));
        cases.push(case(Inst::sub_imm(Reg::wsp(), Reg::w(2), imm32).unwrap()));
    }

    // ---- ADD/SUB shifted-register (+ CMP/CMN/NEG aliases) ----
    let shift_kinds = [ShiftKind::Lsl, ShiftKind::Lsr, ShiftKind::Asr];
    for &is64 in &[true, false] {
        let max_amt = if is64 { 63 } else { 31 };
        let amounts = [0u8, 1, max_amt];
        let (rds, rns, rms): (Vec<Reg>, Vec<Reg>, Vec<Reg>) = if is64 {
            (x_sample_no_zr(), x_sample(), x_sample())
        } else {
            (w_sample_no_zr(), w_sample(), w_sample())
        };
        for &kind in &shift_kinds {
            for &amt in &amounts {
                let shift = RegShift::new(kind, amt, is64).unwrap();
                let rd = rng.pick(&rds);
                let rn = rng.pick(&rns);
                let rm = rng.pick(&rms);
                cases.push(case(Inst::add_shifted(rd, rn, rm, shift).unwrap()));
                cases.push(case(Inst::sub_shifted(rd, rn, rm, shift).unwrap()));
                cases.push(case(Inst::adds_shifted(rd, rn, rm, shift).unwrap()));
                cases.push(case(Inst::subs_shifted(rd, rn, rm, shift).unwrap()));
                cases.push(case(Inst::cmp_shifted(rn, rm, shift).unwrap()));
                cases.push(case(Inst::cmn_shifted(rn, rm, shift).unwrap()));
                cases.push(case(Inst::neg(rd, rm, shift).unwrap()));
                cases.push(case(Inst::negs(rd, rm, shift).unwrap()));
            }
        }
    }

    // ---- ADD/SUB extended-register (+ CMP/CMN aliases) ----
    // `Rm`'s width is dictated by the extend kind (see
    // `Inst::add_sub_extended`'s doc comment), independently of the
    // destination's width: UXTB/UXTH/UXTW/SXTB/SXTH/SXTW always take a
    // 32-bit `Wm`; UXTX/SXTX always take a 64-bit `Xm`. UXTX/SXTX paired
    // with a 32-bit *destination* is an obscure corner this generator
    // doesn't probe either way (not claimed covered).
    let extends = [
        ExtendKind::Uxtb,
        ExtendKind::Uxth,
        ExtendKind::Uxtw,
        ExtendKind::Uxtx,
        ExtendKind::Sxtb,
        ExtendKind::Sxth,
        ExtendKind::Sxtw,
        ExtendKind::Sxtx,
    ];
    for &kind in &extends {
        let rm_is64 = matches!(kind, ExtendKind::Uxtx | ExtendKind::Sxtx);
        let rm_for_64 = if rm_is64 { Reg::x(5) } else { Reg::w(5) };
        for amt in 0u8..=4 {
            let ext = RegExtend::new(kind, amt).unwrap();
            cases.push(case(
                Inst::add_extended(Reg::x(3), base_sample()[amt as usize % 4], rm_for_64, ext)
                    .unwrap(),
            ));
            cases.push(case(
                Inst::sub_extended(Reg::sp(), Reg::sp(), rm_for_64, ext).unwrap(),
            ));
            cases.push(case(Inst::cmp_extended(Reg::x(9), rm_for_64, ext).unwrap()));
            if !rm_is64 {
                cases.push(case(
                    Inst::adds_extended(Reg::w(3), Reg::w(9), Reg::w(5), ext).unwrap(),
                ));
                cases.push(case(Inst::cmn_extended(Reg::w(9), Reg::w(5), ext).unwrap()));
            }
        }
    }

    // ---- Logical immediate (AND/ORR/EOR/ANDS + TST) — exhaustive 32-bit,
    // exhaustive 64-bit (both sets are enumerated directly from the
    // decoder, i.e. independently of `LogicalImm::new`'s search, so the
    // oracle is checking the search against the assembler, not against
    // itself). ----
    for &(n, immr, imms) in &all_valid_bitmask_triples(64) {
        if let Some(v) = fors_asm::bitmask::decode_bitmask(n, immr, imms, 64) {
            let imm = LogicalImm::new(v, true).unwrap();
            cases.push(case(Inst::and_imm(Reg::x(0), Reg::x(1), imm).unwrap()));
        }
    }
    for &(n, immr, imms) in &all_valid_bitmask_triples(32) {
        if let Some(v) = fors_asm::bitmask::decode_bitmask(n, immr, imms, 32) {
            let imm = LogicalImm::new(v, false).unwrap();
            cases.push(case(Inst::orr_imm(Reg::w(0), Reg::w(1), imm).unwrap()));
        }
    }
    // A smaller sample through the other three logical-immediate ops
    // (AND is already exhaustive above; these three plus TST get a
    // deterministic xorshift sample rather than all 5334 again).
    let sample_values_64: Vec<u64> = {
        let mut vs: Vec<u64> = distinct_bitmask_values(64).into_iter().collect();
        vs.sort_unstable();
        let mut out = Vec::new();
        for _ in 0..1500 {
            out.push(rng.pick(&vs));
        }
        out
    };
    for &v in &sample_values_64 {
        let imm = LogicalImm::new(v, true).unwrap();
        cases.push(case(Inst::eor_imm(Reg::x(2), Reg::x(3), imm).unwrap()));
        cases.push(case(Inst::ands_imm(Reg::x(2), Reg::x(3), imm).unwrap()));
        cases.push(case(Inst::tst_imm(Reg::x(4), imm).unwrap()));
    }

    // ---- Logical shifted-register (AND/BIC/ORR/ORN/EOR/EON/ANDS/BICS + MVN/TST/MOV) ----
    let logical_ops = [
        LogicalShiftOp::And,
        LogicalShiftOp::Bic,
        LogicalShiftOp::Orr,
        LogicalShiftOp::Orn,
        LogicalShiftOp::Eor,
        LogicalShiftOp::Eon,
        LogicalShiftOp::Ands,
        LogicalShiftOp::Bics,
    ];
    let all_shift_kinds = [
        ShiftKind::Lsl,
        ShiftKind::Lsr,
        ShiftKind::Asr,
        ShiftKind::Ror,
    ];
    for &is64 in &[true, false] {
        let (rds, rns, rms) = if is64 {
            (x_sample_no_zr(), x_sample(), x_sample())
        } else {
            (w_sample_no_zr(), w_sample(), w_sample())
        };
        let max_amt = if is64 { 63 } else { 31 };
        for &kind in &all_shift_kinds {
            for &amt in &[0u8, 1, max_amt] {
                let shift = RegShift::new(kind, amt, is64).unwrap();
                let rd = rng.pick(&rds);
                let rn = rng.pick(&rns);
                let rm = rng.pick(&rms);
                for &op in &logical_ops {
                    let inst = match op {
                        LogicalShiftOp::And => Inst::and_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Bic => Inst::bic_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Orr => Inst::orr_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Orn => Inst::orn_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Eor => Inst::eor_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Eon => Inst::eon_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Ands => Inst::ands_shifted(rd, rn, rm, shift),
                        LogicalShiftOp::Bics => Inst::bics_shifted(rd, rn, rm, shift),
                    };
                    cases.push(case(inst.unwrap()));
                }
                cases.push(case(Inst::mvn(rd, rm, shift).unwrap()));
                cases.push(case(Inst::tst_reg(rn, rm, shift).unwrap()));
            }
        }
        cases.push(case(Inst::mov_reg(rng.pick(&rds), rng.pick(&rms)).unwrap()));
    }

    // ---- Bitfield: raw UBFM/SBFM/BFM + LSL/LSR/ASR/SXT*/UXT* aliases ----
    for &is64 in &[true, false] {
        let width: u32 = if is64 { 64 } else { 32 };
        let (rd, rn) = if is64 {
            (Reg::x(0), Reg::x(1))
        } else {
            (Reg::w(0), Reg::w(1))
        };
        let bounds = [0u8, 1, (width - 1) as u8];
        for &immr in &bounds {
            for &imms in &bounds {
                cases.push(case(Inst::ubfm(rd, rn, immr, imms).unwrap()));
                cases.push(case(Inst::sbfm(rd, rn, immr, imms).unwrap()));
                cases.push(case(Inst::bfm(rd, rn, immr, imms).unwrap()));
            }
        }
        for &shift in &[0u8, 1, (width - 1) as u8] {
            cases.push(case(Inst::lsl_imm(rd, rn, shift).unwrap()));
            cases.push(case(Inst::lsr_imm(rd, rn, shift).unwrap()));
            cases.push(case(Inst::asr_imm(rd, rn, shift).unwrap()));
        }
        cases.push(case(Inst::sxtb(rd, rn).unwrap()));
        cases.push(case(Inst::sxth(rd, rn).unwrap()));
        if is64 {
            cases.push(case(Inst::sxtw(Reg::x(0), Reg::w(1)).unwrap()));
        } else {
            cases.push(case(Inst::uxtb(rd, rn).unwrap()));
            cases.push(case(Inst::uxth(rd, rn).unwrap()));
        }
    }

    // ---- Data-processing (2-source): UDIV/SDIV/LSLV/LSRV/ASRV/RORV ----
    for &is64 in &[true, false] {
        let (rd, rn, rm) = if is64 {
            (Reg::x(0), Reg::x(1), Reg::x(2))
        } else {
            (Reg::w(0), Reg::w(1), Reg::w(2))
        };
        cases.push(case(Inst::udiv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::sdiv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::lslv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::lsrv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::asrv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::rorv(rd, rn, rm).unwrap()));
        // A handful of other register combos too (edge registers).
        for &(a, b, c) in &[
            (Reg::x(30), Reg::x(0), Reg::x(30)),
            (Reg::xzr(), Reg::x(1), Reg::x(2)),
        ] {
            if is64 {
                cases.push(case(Inst::udiv(a, b, c).unwrap()));
            }
        }
    }

    // ---- Data-processing (3-source): MADD/MSUB/MUL/SMULH/UMULH ----
    for &is64 in &[true, false] {
        let (rd, rn, rm, ra) = if is64 {
            (Reg::x(0), Reg::x(1), Reg::x(2), Reg::x(3))
        } else {
            (Reg::w(0), Reg::w(1), Reg::w(2), Reg::w(3))
        };
        cases.push(case(Inst::madd(rd, rn, rm, ra).unwrap()));
        cases.push(case(Inst::msub(rd, rn, rm, ra).unwrap()));
        cases.push(case(Inst::mul(rd, rn, rm).unwrap()));
    }
    cases.push(case(Inst::smulh(Reg::x(0), Reg::x(1), Reg::x(2)).unwrap()));
    cases.push(case(Inst::umulh(Reg::x(0), Reg::x(1), Reg::x(2)).unwrap()));

    // ---- Data-processing (1-source): CLZ/RBIT/REV ----
    for &is64 in &[true, false] {
        let (rd, rn) = if is64 {
            (Reg::x(0), Reg::x(1))
        } else {
            (Reg::w(0), Reg::w(1))
        };
        cases.push(case(Inst::clz(rd, rn).unwrap()));
        cases.push(case(Inst::rbit(rd, rn).unwrap()));
        cases.push(case(Inst::rev(rd, rn).unwrap()));
    }

    // ---- Conditional select + CSET/CSETM/CINC/CINV/CNEG ----
    for &is64 in &[true, false] {
        let (rd, rn, rm) = if is64 {
            (Reg::x(0), Reg::x(1), Reg::x(2))
        } else {
            (Reg::w(0), Reg::w(1), Reg::w(2))
        };
        for &cond in &conds() {
            cases.push(case(Inst::csel(rd, rn, rm, cond).unwrap()));
            cases.push(case(Inst::csinc(rd, rn, rm, cond).unwrap()));
            cases.push(case(Inst::csinv(rd, rn, rm, cond).unwrap()));
            cases.push(case(Inst::csneg(rd, rn, rm, cond).unwrap()));
        }
        for &cond in &conds_no_al_nv() {
            cases.push(case(Inst::cset(rd, cond).unwrap()));
            cases.push(case(Inst::csetm(rd, cond).unwrap()));
            cases.push(case(Inst::cinc(rd, rn, cond).unwrap()));
            cases.push(case(Inst::cinv(rd, rn, cond).unwrap()));
            cases.push(case(Inst::cneg(rd, rn, cond).unwrap()));
        }
    }

    // ---- ADR/ADRP ----
    let byte_bounds = [0i64, 1, -1, 4, -4, 1048575, -1048576, 1000];
    for &b in &byte_bounds {
        cases.push(case(
            Inst::adr(Reg::x(0), AdrOffset::new(b).unwrap()).unwrap(),
        ));
    }
    let page_bounds = [0i64, 1, -1, 1048575, -1048576, 100];
    for &p in &page_bounds {
        cases.push(case(
            Inst::adrp(Reg::x(0), AdrpOffset::new(p).unwrap()).unwrap(),
        ));
    }

    // ---- Branches ----
    let imm26_words = [0i64, 1, -1, (1 << 25) - 1, -(1 << 25), 1000, -1000];
    for &w in &imm26_words {
        cases.push(case(Inst::b(BranchOffset::new(w * 4, 26, "b").unwrap())));
        cases.push(case(Inst::bl(BranchOffset::new(w * 4, 26, "bl").unwrap())));
    }
    let imm19_words = [0i64, 1, -1, (1 << 18) - 1, -(1 << 18), 500];
    for &w in &imm19_words {
        for &cond in &conds_no_al_nv() {
            cases.push(case(Inst::b_cond(
                cond,
                BranchOffset::new(w * 4, 19, "b.cond").unwrap(),
            )));
        }
        cases.push(case(Inst::cbz(
            Reg::x(3),
            BranchOffset::new(w * 4, 19, "cbz").unwrap(),
        )));
        cases.push(case(Inst::cbnz(
            Reg::w(3),
            BranchOffset::new(w * 4, 19, "cbnz").unwrap(),
        )));
    }
    let imm14_words = [0i64, 1, -1, (1 << 13) - 1, -(1 << 13), 100];
    for &w in &imm14_words {
        for &bit in &[0u8, 5, 31, 63] {
            if bit <= 31 {
                cases.push(case(
                    Inst::tbz(Reg::w(4), bit, BranchOffset::new(w * 4, 14, "tbz").unwrap())
                        .unwrap(),
                ));
            }
            cases.push(case(
                Inst::tbnz(
                    Reg::x(4),
                    bit,
                    BranchOffset::new(w * 4, 14, "tbnz").unwrap(),
                )
                .unwrap(),
            ));
        }
    }
    for &rn in &x_sample_no_zr() {
        cases.push(case(Inst::br(rn).unwrap()));
        cases.push(case(Inst::blr(rn).unwrap()));
        cases.push(case(Inst::ret(rn).unwrap()));
    }

    // ---- Load/store (GP): every size/signedness x every addressing mode ----
    for &rn in &base_sample() {
        for &access in &[1u32, 2, 4, 8] {
            let max_uoff = 4095u64 * access as u64;
            for &off in &[0u64, access as u64, max_uoff] {
                let mode = AddrMode::UnsignedOffset(UScaledImm12::new(off as i64, access).unwrap());
                push_gp_load_store(&mut cases, access, rn, mode);
            }
            for &off in &[0i64, 1, -1, 255, -256] {
                let mode = AddrMode::Unscaled(Simm9::new(off).unwrap());
                push_gp_load_store(&mut cases, access, rn, mode);
                push_gp_load_store(
                    &mut cases,
                    access,
                    rn,
                    AddrMode::PreIndex(Simm9::new(off).unwrap()),
                );
                push_gp_load_store(
                    &mut cases,
                    access,
                    rn,
                    AddrMode::PostIndex(Simm9::new(off).unwrap()),
                );
            }
            for &ext in &[
                LdStExtend::Uxtw,
                LdStExtend::Lsl,
                LdStExtend::Sxtw,
                LdStExtend::Sxtx,
            ] {
                let rm = if matches!(ext, LdStExtend::Uxtw | LdStExtend::Sxtw) {
                    Reg::w(2)
                } else {
                    Reg::x(2)
                };
                for &shifted in &[false, true] {
                    let ro = RegOffset::new(rm, ext, shifted).unwrap();
                    push_gp_load_store(&mut cases, access, rn, AddrMode::RegOffset(ro));
                }
            }
        }
    }

    // ---- LDP/STP ----
    for &is64 in &[true, false] {
        let access = if is64 { 8 } else { 4 };
        let (rt1, rt2) = if is64 {
            (Reg::x(2), Reg::x(3))
        } else {
            (Reg::w(2), Reg::w(3))
        };
        for &rn in &base_sample() {
            for &off in &[-64i64, -1, 0, 1, 63] {
                let imm = SImm7Scaled::new(off * access as i64, access).unwrap();
                cases.push(case(
                    Inst::stp(rt1, rt2, rn, imm, PairIndex::Offset).unwrap(),
                ));
                cases.push(case(
                    Inst::ldp(rt1, rt2, rn, imm, PairIndex::Offset).unwrap(),
                ));
                cases.push(case(
                    Inst::stp(rt1, rt2, rn, imm, PairIndex::PreIndex).unwrap(),
                ));
                cases.push(case(
                    Inst::ldp(rt1, rt2, rn, imm, PairIndex::PostIndex).unwrap(),
                ));
            }
        }
    }

    // ---- FP loads/stores ----
    for &rn in &base_sample() {
        for &(is_d, access) in &[(true, 8u32), (false, 4u32)] {
            let rt_d = FpReg::d(4);
            let rt_s = FpReg::s(4);
            for &off in &[0u64, access as u64, 4095 * access as u64] {
                let mode = AddrMode::UnsignedOffset(UScaledImm12::new(off as i64, access).unwrap());
                if is_d {
                    cases.push(case(Inst::ldr_fp(rt_d, rn, mode).unwrap()));
                    cases.push(case(Inst::str_fp(rt_d, rn, mode).unwrap()));
                } else {
                    cases.push(case(Inst::ldr_fp(rt_s, rn, mode).unwrap()));
                    cases.push(case(Inst::str_fp(rt_s, rn, mode).unwrap()));
                }
            }
            for &off in &[0i64, -1, 255, -256] {
                let mode = AddrMode::Unscaled(Simm9::new(off).unwrap());
                if is_d {
                    cases.push(case(Inst::ldr_fp(rt_d, rn, mode).unwrap()));
                } else {
                    cases.push(case(Inst::str_fp(rt_s, rn, mode).unwrap()));
                }
            }
        }
    }

    // ---- System ----
    cases.push(case(Inst::nop()));
    for &imm in &[0u16, 1, 0x1234, 0xFFFF] {
        cases.push(case(Inst::brk(imm)));
        cases.push(case(Inst::svc(imm)));
        cases.push(case(Inst::udf(imm)));
    }

    // ---- Scalar FP ----
    for &d in &fp_d_sample() {
        cases.push(case(Inst::fmov_reg(d, FpReg::d(9)).unwrap()));
        cases.push(case(Inst::fabs(d, FpReg::d(9)).unwrap()));
        cases.push(case(Inst::fneg(d, FpReg::d(9)).unwrap()));
        cases.push(case(Inst::fsqrt(d, FpReg::d(9)).unwrap()));
        cases.push(case(Inst::fcvt(d, FpReg::s(9)).unwrap()));
    }
    for &s in &fp_s_sample() {
        cases.push(case(Inst::fmov_reg(s, FpReg::s(9)).unwrap()));
        cases.push(case(Inst::fcvt(s, FpReg::d(9)).unwrap()));
    }
    for &(rd, rn, rm) in &[
        (FpReg::d(0), FpReg::d(1), FpReg::d(2)),
        (FpReg::d(3), FpReg::d(30), FpReg::d(31)),
    ] {
        cases.push(case(Inst::fadd(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fsub(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fmul(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fdiv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fmadd(rd, rn, rm, FpReg::d(4)).unwrap()));
    }
    {
        let (rd, rn, rm) = (FpReg::s(0), FpReg::s(1), FpReg::s(2));
        cases.push(case(Inst::fadd(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fsub(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fmul(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fdiv(rd, rn, rm).unwrap()));
        cases.push(case(Inst::fmadd(rd, rn, rm, FpReg::s(4)).unwrap()));
    }
    cases.push(case(Inst::fcmp(FpReg::d(0), FpReg::d(1)).unwrap()));
    cases.push(case(Inst::fcmp(FpReg::s(0), FpReg::s(1)).unwrap()));
    for &cond in &conds() {
        cases.push(case(
            Inst::fcsel(FpReg::d(0), FpReg::d(1), FpReg::d(2), cond).unwrap(),
        ));
        cases.push(case(
            Inst::fcsel(FpReg::s(0), FpReg::s(1), FpReg::s(2), cond).unwrap(),
        ));
    }
    let fp_imm_values_f64: &[f64] = &[
        1.0, -2.5, 2.0, -2.0, 0.5, -0.5, 4.0, 8.0, 0.125, 1.5, -1.0, 16.0, 3.0, -4.0, 0.25, -0.125,
        6.0, 10.0, 12.0, -16.0, 0.0625, 32.0, 64.0, -8.0, -3.0, 0.0625, 1.0625, -1.9375,
    ];
    for &v in fp_imm_values_f64 {
        if let Ok(imm) = fors_asm::fpimm::FpImm8::from_f64(v) {
            cases.push(case(Inst::fmov_imm(FpReg::d(5), imm).unwrap()));
        }
        if let Ok(imm) = fors_asm::fpimm::FpImm8::from_f32(v as f32) {
            cases.push(case(Inst::fmov_imm(FpReg::s(5), imm).unwrap()));
        }
    }
    for &x in &x_sample() {
        cases.push(case(Inst::fmov_from_gp(FpReg::d(6), x).unwrap()));
        cases.push(case(Inst::fmov_to_gp(x, FpReg::d(6)).unwrap()));
        cases.push(case(Inst::scvtf(FpReg::d(6), x).unwrap()));
        cases.push(case(Inst::ucvtf(FpReg::d(6), x).unwrap()));
        cases.push(case(Inst::fcvtzs(x, FpReg::d(6)).unwrap()));
        cases.push(case(Inst::fcvtzu(x, FpReg::d(6)).unwrap()));
    }
    for &w in &w_sample() {
        cases.push(case(Inst::fmov_from_gp(FpReg::s(6), w).unwrap()));
        cases.push(case(Inst::fmov_to_gp(w, FpReg::s(6)).unwrap()));
        cases.push(case(Inst::scvtf(FpReg::s(6), w).unwrap()));
        cases.push(case(Inst::ucvtf(FpReg::s(6), w).unwrap()));
        cases.push(case(Inst::fcvtzs(w, FpReg::s(6)).unwrap()));
        cases.push(case(Inst::fcvtzu(w, FpReg::s(6)).unwrap()));
    }

    cases
}

fn push_gp_load_store(cases: &mut Vec<Case>, access: u32, rn: Reg, mode: AddrMode) {
    // Rt register numbers here are chosen to never collide with any
    // `base_sample()` register number (SP, 1, 19, 29): pre/post-indexed
    // addressing writes the new address back into Rn, and the system
    // assembler rejects Rt == Rn for those modes as UNPREDICTABLE (a real
    // architectural restriction — see `Inst::load_store`'s doc comment on
    // the writeback check this generator must not trip).
    match access {
        1 => {
            cases.push(case(Inst::ldrb(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::strb(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::ldrsb(Reg::w(10), rn, mode).unwrap()));
            cases.push(case(Inst::ldrsb(Reg::x(10), rn, mode).unwrap()));
        }
        2 => {
            cases.push(case(Inst::ldrh(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::strh(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::ldrsh(Reg::w(10), rn, mode).unwrap()));
            cases.push(case(Inst::ldrsh(Reg::x(10), rn, mode).unwrap()));
        }
        4 => {
            cases.push(case(Inst::ldr(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::str_(Reg::w(0), rn, mode).unwrap()));
            cases.push(case(Inst::ldrsw(Reg::x(10), rn, mode).unwrap()));
        }
        8 => {
            cases.push(case(Inst::ldr(Reg::x(0), rn, mode).unwrap()));
            cases.push(case(Inst::str_(Reg::x(0), rn, mode).unwrap()));
        }
        _ => unreachable!(),
    }
}

/// Every `(N, immr, imms)` that decodes successfully at the given width —
/// note this over-counts distinct VALUES (see `bitmask.rs`'s doc comment),
/// which is fine here: encoding each one and feeding it to the assembler
/// exercises the encoder on every reachable field combination, not just
/// the minimal set of distinct results.
fn all_valid_bitmask_triples(reg_size: u32) -> Vec<(u8, u8, u8)> {
    let mut out = Vec::new();
    let ns: &[u8] = if reg_size == 64 { &[0, 1] } else { &[0] };
    for &n in ns {
        for immr in 0u8..64 {
            for imms in 0u8..64 {
                if fors_asm::bitmask::decode_bitmask(n, immr, imms, reg_size).is_some() {
                    out.push((n, immr, imms));
                }
            }
        }
    }
    out
}

fn distinct_bitmask_values(reg_size: u32) -> std::collections::BTreeSet<u64> {
    let mut out = std::collections::BTreeSet::new();
    for &(n, immr, imms) in &all_valid_bitmask_triples(reg_size) {
        if let Some(v) = fors_asm::bitmask::decode_bitmask(n, immr, imms, reg_size) {
            out.insert(v);
        }
    }
    out
}

/// Cases that must be `Err` from this crate AND rejected by the system
/// assembler (only meaningful on the oracle side, which has an assembler
/// to ask) — "one past the boundary" for a representative immediate/offset
/// on each family, not an exhaustive re-run of every form.
pub struct RejectCase {
    pub what: &'static str,
    pub attempted_asm: String,
}

pub fn boundary_reject_cases() -> Vec<RejectCase> {
    let mut out = Vec::new();

    // MOVZ/MOVK: shift must be a multiple of 16 within range; 8 is neither
    // a legal shift nor alignable, so this crate must reject it.
    assert!(Inst::movz(Reg::x(0), 0, 8).is_err());
    out.push(RejectCase {
        what: "MOVZ shift not a multiple of 16",
        attempted_asm: "movz x0, #0, lsl #8".to_string(),
    });
    assert!(Inst::movz(Reg::w(0), 0, 32).is_err());
    out.push(RejectCase {
        what: "MOVZ 32-bit shift out of range (32)",
        attempted_asm: "movz w0, #0, lsl #32".to_string(),
    });

    // ADD/SUB immediate: 4096 that is not a multiple-of-4096 wouldn't be
    // representable; use 4097 (fails both the <=0xFFF check and the
    // shift-by-12 check).
    assert!(Uimm12Lsl::new(4097).is_err());
    out.push(RejectCase {
        what: "ADD/SUB imm 4097 (not encodable)",
        attempted_asm: "add x0, x1, #4097".to_string(),
    });

    assert!(Uimm12Lsl::new(0x0100_0000).is_err());
    out.push(RejectCase {
        what: "ADD/SUB imm way out of range",
        attempted_asm: "add x0, x1, #16777216".to_string(),
    });

    // Logical immediate: 0 and all-ones are never encodable.
    assert!(LogicalImm::new(0, true).is_err());
    out.push(RejectCase {
        what: "AND immediate #0 (unencodable)",
        attempted_asm: "and x0, x1, #0".to_string(),
    });
    assert!(
        LogicalImm::new(0x1234_5678, true).is_err() || LogicalImm::new(0x1234_5678, true).is_ok()
    );
    // (0x12345678 may or may not be a valid bitmask immediate; only used
    // above to show the API doesn't panic either way — not pushed.)
    assert!(LogicalImm::new(u64::MAX, true).is_err());
    out.push(RejectCase {
        what: "AND immediate all-ones (unencodable)",
        attempted_asm: "and x0, x1, #-1".to_string(),
    });

    // Branch offset: misaligned (not a multiple of 4).
    assert!(BranchOffset::new(2, 26, "b").is_err());
    out.push(RejectCase {
        what: "B offset misaligned by 2 bytes",
        attempted_asm: "b #2".to_string(),
    });

    // Branch offset: one past the imm26 range (bytes = (2^25)*4).
    assert!(BranchOffset::new((1i64 << 25) * 4, 26, "b").is_err());
    out.push(RejectCase {
        what: "B offset one past +imm26 range",
        attempted_asm: format!("b #{}", (1i64 << 25) * 4),
    });
    assert!(BranchOffset::new(-(1i64 << 25) * 4 - 4, 26, "b").is_err());
    out.push(RejectCase {
        what: "B offset one past -imm26 range",
        attempted_asm: format!("b #{}", -(1i64 << 25) * 4 - 4),
    });

    // ADR: one past the byte range.
    assert!(AdrOffset::new(1_048_576).is_err());
    out.push(RejectCase {
        what: "ADR offset one past +range",
        attempted_asm: "adr x0, #1048576".to_string(),
    });

    // ADRP: one past the page range (in bytes).
    assert!(AdrpOffset::new(1_048_576).is_err());
    out.push(RejectCase {
        what: "ADRP offset one past +range (pages)",
        attempted_asm: "adrp x0, #4294967296".to_string(),
    });

    // UScaledImm12: misaligned for the access size AND out of LDUR's
    // unscaled range, so there's no valid encoding to fall back to.
    //
    // NOTE (oracle finding, see crate docs / report): a misaligned offset
    // that DOES fit in [-256, 255] — e.g. `ldr x0, [x1, #3]` — is NOT
    // rejected by clang's assembler: `LDR` there is a convenience mnemonic
    // that silently falls back to the unscaled (`LDUR`) ENCODING when the
    // offset doesn't fit the scaled form. This crate's `AddrMode` has no
    // such alias — `Inst::ldr(.., AddrMode::UnsignedOffset(..))` names the
    // exact instruction encoding and requires a properly scaled immediate;
    // callers who want the unscaled encoding use `AddrMode::Unscaled(..)`
    // explicitly. So `UScaledImm12::new(3, 8)` is correctly `Err` (it is
    // not a valid *unsigned-offset* immediate), even though the assembler
    // accepts `ldr` spelled with that same offset by picking a different
    // instruction underneath.
    assert!(UScaledImm12::new(3, 8).is_err());
    assert!(UScaledImm12::new(257, 8).is_err());
    out.push(RejectCase {
        what: "LDR unsigned-offset misaligned AND out of LDUR fallback range",
        attempted_asm: "ldr x0, [x1, #257]".to_string(),
    });
    assert!(UScaledImm12::new(4096 * 8, 8).is_err());
    out.push(RejectCase {
        what: "LDR unsigned-offset one past range",
        attempted_asm: format!("ldr x0, [x1, #{}]", 4096 * 8),
    });

    // Simm9: one past range.
    assert!(Simm9::new(256).is_err());
    out.push(RejectCase {
        what: "LDUR offset one past +range",
        attempted_asm: "ldur x0, [x1, #256]".to_string(),
    });
    assert!(Simm9::new(-257).is_err());
    out.push(RejectCase {
        what: "LDUR offset one past -range",
        attempted_asm: "ldur x0, [x1, #-257]".to_string(),
    });

    // SImm7Scaled: one past range for LDP/STP (64-bit -> unit 8 bytes).
    assert!(SImm7Scaled::new(64 * 8, 8).is_err());
    out.push(RejectCase {
        what: "LDP/STP offset one past +range",
        attempted_asm: format!("ldp x0, x1, [sp, #{}]", 64 * 8),
    });

    out
}
