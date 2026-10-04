//! Hand-written integer edge cases with expectations derived from the SPEC
//! (`docs/spec/03-numerics-determinism.md` R2/R4/R6 and the owner decisions
//! the design records: Q4 `MIN / -1`, `MIN % -1` trap `overflow`, a shift
//! traps exactly when `count >= width`; `sat_*` clamps the true result to
//! the type's bounds; `wrap_as` keeps the value's residue mod 2^w; `as`
//! traps unless exactly representable) — NOT from `arith.rs`. Both engines
//! must print these bytes; `native_edge.rs` then pins the two engines to
//! each other over every pair of interesting values.
//!
//! The interpreter half runs everywhere; the native half on macOS/aarch64.
//! Every expected value is the raw low-`width` bits in decimal, which is
//! what `stdout_write_uint` prints for every integer type.

mod native_support;

use fors_fmir::op::{ArithMode, CmpPred, Op, TrapKind};
use fors_interp::arith::IntKind;
use fors_oracle::Candidate;
use native_support::Builder;

use ArithMode::{Sat, Trap, Wrap};
use IntKind::{I8, I16, I32, I64, U8, U16, U32, U64};

/// One operation on constant operands (raw low-width bits).
#[derive(Clone, Copy, Debug)]
enum Case {
    Bin(Op, IntKind, u64, u64),
    /// A shift whose count operand has its own type.
    ShiftBy(Op, IntKind, u64, IntKind, u64),
    Un(Op, IntKind, u64),
    Conv(Op, IntKind, u64, IntKind),
    Cmp(CmpPred, IntKind, u64, u64),
}

fn build(b: &mut Builder, c: Case) -> fors_fmir::ids::ValId {
    match c {
        Case::Bin(op, k, x, y) => {
            let a = b.const_int(x, k);
            let v = b.const_int(y, k);
            b.bin(op, a, v, k)
        }
        Case::ShiftBy(op, k, x, ck, y) => {
            let a = b.const_int(x, k);
            let v = b.const_int(y, ck);
            b.bin(op, a, v, k)
        }
        Case::Un(op, k, x) => {
            let a = b.const_int(x, k);
            b.un(op, a, k)
        }
        Case::Conv(op, from, x, to) => {
            let a = b.const_int(x, from);
            b.conv(op, a, to)
        }
        Case::Cmp(p, k, x, y) => {
            let a = b.const_int(x, k);
            let v = b.const_int(y, k);
            b.icmp(p, a, v)
        }
    }
}

const I8_MIN: u64 = 0x80;
const I8_M1: u64 = 0xFF;
const I32_MIN: u64 = 1 << 31;
const I32_M1: u64 = 0xFFFF_FFFF;
const I64_MIN: u64 = 1 << 63;
const I64_MAX: u64 = i64::MAX as u64;
const M1: u64 = u64::MAX;

/// Non-trapping cases: `(name, case, printed value)`.
fn value_cases() -> Vec<(&'static str, Case, u64)> {
    use Case::*;
    vec![
        // -- MIN / -1, MIN % -1, neg MIN in the non-trapping modes ---------
        (
            "i8 MIN wrap/ -1",
            Bin(Op::Div(Wrap), I8, I8_MIN, I8_M1),
            128,
        ),
        ("i8 MIN sat/ -1", Bin(Op::Div(Sat), I8, I8_MIN, I8_M1), 127),
        ("i8 MIN wrap% -1", Bin(Op::Rem(Wrap), I8, I8_MIN, I8_M1), 0),
        ("i8 MIN sat% -1", Bin(Op::Rem(Sat), I8, I8_MIN, I8_M1), 0),
        ("i8 wrap_neg MIN", Un(Op::Neg(Wrap), I8, I8_MIN), 128),
        ("i8 sat_neg MIN", Un(Op::Neg(Sat), I8, I8_MIN), 127),
        ("u8 wrap_neg 1", Un(Op::Neg(Wrap), U8, 1), 255),
        (
            "i64 MIN sat/ -1",
            Bin(Op::Div(Sat), I64, I64_MIN, M1),
            I64_MAX,
        ),
        (
            "i64 MIN wrap/ -1",
            Bin(Op::Div(Wrap), I64, I64_MIN, M1),
            I64_MIN,
        ),
        ("i64 MIN sat% -1", Bin(Op::Rem(Sat), I64, I64_MIN, M1), 0),
        ("i64 MIN wrap% -1", Bin(Op::Rem(Wrap), I64, I64_MIN, M1), 0),
        (
            "i64 MAX / MIN",
            Bin(Op::Div(Trap), I64, I64_MAX, I64_MIN),
            0,
        ),
        (
            "i64 MIN / MAX",
            Bin(Op::Div(Trap), I64, I64_MIN, I64_MAX),
            M1,
        ),
        (
            "i64 MIN % MAX",
            Bin(Op::Rem(Trap), I64, I64_MIN, I64_MAX),
            M1,
        ),
        ("u64 MAX / MAX", Bin(Op::Div(Trap), U64, M1, M1), 1),
        // -- division and remainder truncate toward zero -------------------
        ("i8 -7 / 2", Bin(Op::Div(Trap), I8, 249, 2), 253),
        ("i8 7 / -2", Bin(Op::Div(Trap), I8, 7, 254), 253),
        (
            "i8 -7 % 3 (sign of the dividend)",
            Bin(Op::Rem(Trap), I8, 249, 3),
            255,
        ),
        ("i8 7 % -3", Bin(Op::Rem(Trap), I8, 7, 253), 1),
        ("i64 -7 % 3", Bin(Op::Rem(Trap), I64, (-7i64) as u64, 3), M1),
        // -- shifts: arithmetic vs logical by signedness, counts, sat ------
        (
            "i8 MIN >> 7 (arithmetic)",
            Bin(Op::Shr(Trap), I8, I8_MIN, 7),
            255,
        ),
        ("u8 128 >> 7 (logical)", Bin(Op::Shr(Trap), U8, 128, 7), 1),
        ("i32 -1 >> 31", Bin(Op::Shr(Trap), I32, I32_M1, 31), I32_M1),
        ("u32 2^31 >> 31", Bin(Op::Shr(Trap), U32, I32_MIN, 31), 1),
        ("i64 MIN >> 63", Bin(Op::Shr(Wrap), I64, I64_MIN, 63), M1),
        ("u64 MAX >> 63", Bin(Op::Shr(Wrap), U64, M1, 63), 1),
        ("i8 -1 sat>> 3", Bin(Op::Shr(Sat), I8, I8_M1, 3), 255),
        (
            "i16 0x4000 sat<< 1",
            Bin(Op::Shl(Sat), I16, 0x4000, 1),
            32767,
        ),
        (
            "i16 -0x4000 sat<< 2",
            Bin(Op::Shl(Sat), I16, 0xC000, 2),
            32768,
        ),
        ("i16 1 sat<< 15", Bin(Op::Shl(Sat), I16, 1, 15), 32767),
        (
            "u16 0x8000 sat<< 1",
            Bin(Op::Shl(Sat), U16, 0x8000, 1),
            65535,
        ),
        ("u16 0x8000 wrap<< 1", Bin(Op::Shl(Wrap), U16, 0x8000, 1), 0),
        (
            "u16 0x8000 << 1 (Q4: only the count traps)",
            Bin(Op::Shl(Trap), U16, 0x8000, 1),
            0,
        ),
        ("i32 1 wrap<< 31", Bin(Op::Shl(Wrap), I32, 1, 31), I32_MIN),
        ("i32 1 sat<< 31", Bin(Op::Shl(Sat), I32, 1, 31), 0x7FFF_FFFF),
        ("i32 7 sat<< 31", Bin(Op::Shl(Sat), I32, 7, 31), 0x7FFF_FFFF),
        ("u8 128 sat<< 1", Bin(Op::Shl(Sat), U8, 128, 1), 255),
        ("u8 0x81 wrap<< 1", Bin(Op::Shl(Wrap), U8, 0x81, 1), 2),
        ("i64 1 sat<< 63", Bin(Op::Shl(Sat), I64, 1, 63), I64_MAX),
        (
            "i64 -1 sat<< 63 (exact)",
            Bin(Op::Shl(Sat), I64, M1, 63),
            I64_MIN,
        ),
        ("i64 3 sat<< 62", Bin(Op::Shl(Sat), I64, 3, 62), I64_MAX),
        (
            "i64 -3 sat<< 62",
            Bin(Op::Shl(Sat), I64, (-3i64) as u64, 62),
            I64_MIN,
        ),
        (
            "u64 1 sat<< 63 (exact)",
            Bin(Op::Shl(Sat), U64, 1, 63),
            I64_MIN,
        ),
        ("u64 3 sat<< 63", Bin(Op::Shl(Sat), U64, 3, 63), M1),
        (
            "u64 1 << i8(3): the count has its own type",
            ShiftBy(Op::Shl(Trap), U64, 1, I8, 3),
            8,
        ),
        (
            "i8 MIN >> u64(7)",
            ShiftBy(Op::Shr(Trap), I8, I8_MIN, U64, 7),
            255,
        ),
        // -- add / sub / mul: trap-mode fits, wrap, sat at every width -----
        (
            "i64 MAX + MIN",
            Bin(Op::Add(Trap), I64, I64_MAX, I64_MIN),
            M1,
        ),
        ("u64 MAX wrap+ 1", Bin(Op::Add(Wrap), U64, M1, 1), 0),
        ("u64 0 wrap- 1", Bin(Op::Sub(Wrap), U64, 0, 1), M1),
        ("i8 127 wrap+ 1", Bin(Op::Add(Wrap), I8, 127, 1), 128),
        ("u8 255 sat+ 1", Bin(Op::Add(Sat), U8, 255, 1), 255),
        ("u8 0 sat- 1", Bin(Op::Sub(Sat), U8, 0, 1), 0),
        ("i8 MIN sat+ -1", Bin(Op::Add(Sat), I8, I8_MIN, I8_M1), 128),
        ("i8 MAX sat- -1", Bin(Op::Sub(Sat), I8, 127, I8_M1), 127),
        (
            "i32 MIN sat- 1",
            Bin(Op::Sub(Sat), I32, I32_MIN, 1),
            I32_MIN,
        ),
        ("u32 0 sat- 1", Bin(Op::Sub(Sat), U32, 0, 1), 0),
        (
            "u32 MAX sat+ MAX",
            Bin(Op::Add(Sat), U32, I32_M1, I32_M1),
            I32_M1,
        ),
        (
            "u32 65535 * 65537 (fits)",
            Bin(Op::Mul(Trap), U32, 65535, 65537),
            I32_M1,
        ),
        (
            "i32 MIN sat* -1",
            Bin(Op::Mul(Sat), I32, I32_MIN, I32_M1),
            0x7FFF_FFFF,
        ),
        (
            "i32 MIN wrap* -1",
            Bin(Op::Mul(Wrap), I32, I32_MIN, I32_M1),
            I32_MIN,
        ),
        (
            "i8 MIN sat* MIN",
            Bin(Op::Mul(Sat), I8, I8_MIN, I8_MIN),
            127,
        ),
        ("i8 127 sat* -2", Bin(Op::Mul(Sat), I8, 127, 254), 128),
        ("u8 16 sat* 16", Bin(Op::Mul(Sat), U8, 16, 16), 255),
        ("i16 -1 * -1", Bin(Op::Mul(Trap), I16, 0xFFFF, 0xFFFF), 1),
        (
            "u16 0xFFFF wrap* 0xFFFF",
            Bin(Op::Mul(Wrap), U16, 0xFFFF, 0xFFFF),
            1,
        ),
        (
            "u64 (2^32-1) * (2^32+1) (fits)",
            Bin(Op::Mul(Trap), U64, (1 << 32) - 1, (1 << 32) + 1),
            M1,
        ),
        ("u64 2^63 sat* 2", Bin(Op::Mul(Sat), U64, I64_MIN, 2), M1),
        (
            "i64 MIN sat* -1",
            Bin(Op::Mul(Sat), I64, I64_MIN, M1),
            I64_MAX,
        ),
        (
            "i64 MIN sat* 1",
            Bin(Op::Mul(Sat), I64, I64_MIN, 1),
            I64_MIN,
        ),
        (
            "i64 -1 sat* MIN",
            Bin(Op::Mul(Sat), I64, M1, I64_MIN),
            I64_MAX,
        ),
        (
            "i64 MAX sat* MAX",
            Bin(Op::Mul(Sat), I64, I64_MAX, I64_MAX),
            I64_MAX,
        ),
        (
            "i64 MIN sat* MIN",
            Bin(Op::Mul(Sat), I64, I64_MIN, I64_MIN),
            I64_MAX,
        ),
        (
            "i64 -2 sat* MAX",
            Bin(Op::Mul(Sat), I64, (-2i64) as u64, I64_MAX),
            I64_MIN,
        ),
        // -- not ------------------------------------------------------------
        ("not i8 0", Un(Op::Not, I8, 0), 255),
        ("not u8 0", Un(Op::Not, U8, 0), 255),
        ("not u64 0", Un(Op::Not, U64, 0), M1),
        ("not i64 5", Un(Op::Not, I64, 5), (-6i64) as u64),
        // -- conversions ----------------------------------------------------
        ("sat_as i8(-1) -> u8", Conv(Op::ConvSat, I8, I8_M1, U8), 0),
        ("sat_as i64(-1) -> u64", Conv(Op::ConvSat, I64, M1, U64), 0),
        (
            "sat_as u64(MAX) -> i64",
            Conv(Op::ConvSat, U64, M1, I64),
            I64_MAX,
        ),
        ("sat_as u8(200) -> i8", Conv(Op::ConvSat, U8, 200, I8), 127),
        (
            "sat_as i16(-200) -> u8",
            Conv(Op::ConvSat, I16, (-200i16) as u16 as u64, U8),
            0,
        ),
        (
            "sat_as i16(300) -> u8",
            Conv(Op::ConvSat, I16, 300, U8),
            255,
        ),
        (
            "sat_as u32(MAX) -> i32",
            Conv(Op::ConvSat, U32, I32_M1, I32),
            0x7FFF_FFFF,
        ),
        (
            "sat_as u8(255) -> i16",
            Conv(Op::ConvSat, U8, 255, I16),
            255,
        ),
        (
            "sat_as i8(MIN) -> i16",
            Conv(Op::ConvSat, I8, I8_MIN, I16),
            65408,
        ),
        (
            "as i32(-1) -> i64",
            Conv(Op::ConvChecked, I32, I32_M1, I64),
            M1,
        ),
        (
            "as i64(-128) -> i8",
            Conv(Op::ConvChecked, I64, (-128i64) as u64, I8),
            128,
        ),
        ("as u8(127) -> i8", Conv(Op::ConvChecked, U8, 127, I8), 127),
        (
            "as u64(2^63-1) -> i64",
            Conv(Op::ConvChecked, U64, I64_MAX, I64),
            I64_MAX,
        ),
        (
            "as i8(-1) -> i64",
            Conv(Op::ConvChecked, I8, I8_M1, I64),
            M1,
        ),
        (
            "wrap_as i8(-1) -> u64",
            Conv(Op::ConvWrap, I8, I8_M1, U64),
            M1,
        ),
        (
            "wrap_as i8(-1) -> i32",
            Conv(Op::ConvWrap, I8, I8_M1, I32),
            I32_M1,
        ),
        (
            "wrap_as u64(0x1FF) -> u8",
            Conv(Op::ConvWrap, U64, 0x1FF, U8),
            255,
        ),
        (
            "wrap_as i32(-1) -> u16",
            Conv(Op::ConvWrap, I32, I32_M1, U16),
            65535,
        ),
        (
            "wrap_as u16(0xFFFF) -> i8",
            Conv(Op::ConvWrap, U16, 0xFFFF, I8),
            255,
        ),
        // -- comparisons by signedness --------------------------------------
        ("i8 -1 < 1", Cmp(CmpPred::Lt, I8, I8_M1, 1), 1),
        ("u8 255 < 1", Cmp(CmpPred::Lt, U8, 255, 1), 0),
        ("i8 MIN < MAX", Cmp(CmpPred::Lt, I8, I8_MIN, 127), 1),
        ("u64 2^63 > 1", Cmp(CmpPred::Gt, U64, I64_MIN, 1), 1),
        ("i64 MIN > 1", Cmp(CmpPred::Gt, I64, I64_MIN, 1), 0),
        ("i64 MIN <= -1", Cmp(CmpPred::Le, I64, I64_MIN, M1), 1),
        ("u32 MAX >= 0", Cmp(CmpPred::Ge, U32, I32_M1, 0), 1),
        (
            "i32 MAX != MIN",
            Cmp(CmpPred::Ne, I32, 0x7FFF_FFFF, I32_MIN),
            1,
        ),
    ]
}

/// Trapping cases: `(name, case, kind)`.
fn trap_cases() -> Vec<(&'static str, Case, TrapKind)> {
    use Case::*;
    use TrapKind::{CheckedConversion, DivZero, Overflow, Shift};
    vec![
        (
            "i8 MIN / -1",
            Bin(Op::Div(Trap), I8, I8_MIN, I8_M1),
            Overflow,
        ),
        (
            "i8 MIN % -1",
            Bin(Op::Rem(Trap), I8, I8_MIN, I8_M1),
            Overflow,
        ),
        ("i8 neg MIN", Un(Op::Neg(Trap), I8, I8_MIN), Overflow),
        (
            "i8 MIN * -1",
            Bin(Op::Mul(Trap), I8, I8_MIN, I8_M1),
            Overflow,
        ),
        ("u8 255 + 1", Bin(Op::Add(Trap), U8, 255, 1), Overflow),
        ("u8 0 - 1", Bin(Op::Sub(Trap), U8, 0, 1), Overflow),
        (
            "u32 65536 * 65536",
            Bin(Op::Mul(Trap), U32, 65536, 65536),
            Overflow,
        ),
        (
            "i32 MIN * -1",
            Bin(Op::Mul(Trap), I32, I32_MIN, I32_M1),
            Overflow,
        ),
        (
            "u64 (2^63+1) * MAX",
            Bin(Op::Mul(Trap), U64, I64_MIN + 1, M1),
            Overflow,
        ),
        ("i64 MIN - 1", Bin(Op::Sub(Trap), I64, I64_MIN, 1), Overflow),
        (
            "i64 MIN / -1",
            Bin(Op::Div(Trap), I64, I64_MIN, M1),
            Overflow,
        ),
        (
            "i64 MIN % -1",
            Bin(Op::Rem(Trap), I64, I64_MIN, M1),
            Overflow,
        ),
        ("i64 neg MIN", Un(Op::Neg(Trap), I64, I64_MIN), Overflow),
        ("i64 sat/ 0", Bin(Op::Div(Sat), I64, 5, 0), DivZero),
        ("u8 wrap% 0", Bin(Op::Rem(Wrap), U8, 5, 0), DivZero),
        ("i8 1 wrap<< 8", Bin(Op::Shl(Wrap), I8, 1, 8), Shift),
        ("u8 2 sat>> 8", Bin(Op::Shr(Sat), U8, 2, 8), Shift),
        ("i16 1 sat<< 16", Bin(Op::Shl(Sat), I16, 1, 16), Shift),
        (
            "u64 1 << i8(-1): raw count 255",
            ShiftBy(Op::Shl(Trap), U64, 1, I8, I8_M1),
            Shift,
        ),
        (
            "as i8(-1) -> u64",
            Conv(Op::ConvChecked, I8, I8_M1, U64),
            CheckedConversion,
        ),
        (
            "as u8(255) -> i8",
            Conv(Op::ConvChecked, U8, 255, I8),
            CheckedConversion,
        ),
        (
            "as u64(2^63) -> i64",
            Conv(Op::ConvChecked, U64, I64_MIN, I64),
            CheckedConversion,
        ),
        (
            "as i64(-129) -> i8",
            Conv(Op::ConvChecked, I64, (-129i64) as u64, I8),
            CheckedConversion,
        ),
        (
            "as i32(-1) -> u32",
            Conv(Op::ConvChecked, I32, I32_M1, U32),
            CheckedConversion,
        ),
        (
            "as u32(2^31) -> i32",
            Conv(Op::ConvChecked, U32, I32_MIN, I32),
            CheckedConversion,
        ),
        (
            "as i16(128) -> i8",
            Conv(Op::ConvChecked, I16, 128, I8),
            CheckedConversion,
        ),
    ]
}

/// The type of a case's result (`None` for a `bool`).
fn result_kind(c: Case) -> Option<IntKind> {
    match c {
        Case::Bin(_, k, ..) | Case::ShiftBy(_, k, ..) | Case::Un(_, k, _) => Some(k),
        Case::Conv(_, _, _, to) => Some(to),
        Case::Cmp(..) => None,
    }
}

/// All value cases in one program, and the bytes they must print: each
/// case's raw result, then (integers) its canonical 64-bit slot form via
/// `wrap_as` to the 64-bit type of its signedness — so a result with the
/// right low bits but a non-canonical upper half (design E5) fails here.
fn value_program() -> (Candidate, Vec<u8>) {
    let mut b = Builder::new();
    let mut want = Vec::new();
    for (_, c, v) in value_cases() {
        let r = build(&mut b, c);
        b.write_uint(r);
        b.newline();
        want.extend_from_slice(format!("{v}\n").as_bytes());
        if let Some(k) = result_kind(c) {
            let w = b.conv(Op::ConvWrap, r, native_support::wide(k));
            b.write_uint(w);
            b.newline();
            let canon = native_support::canonical(v, k);
            want.extend_from_slice(format!("{canon}\n").as_bytes());
        }
    }
    (b.ret(), want)
}

/// The case (and whether it was the canonical-form line) behind printed
/// line `k`.
fn case_of_line(k: usize) -> (usize, bool) {
    let mut base = 0;
    for (i, (_, c, _)) in value_cases().into_iter().enumerate() {
        let lines = if result_kind(c).is_some() { 2 } else { 1 };
        if k < base + lines {
            return (i, k - base == 1);
        }
        base += lines;
    }
    (usize::MAX, false)
}

fn trap_program(c: Case) -> Candidate {
    let mut b = Builder::new();
    b.write_line(b"before");
    let r = build(&mut b, c);
    b.write_uint(r);
    b.write_line(b"after");
    b.ret()
}

fn first_bad(got: &[u8], want: &[u8]) -> String {
    let g = String::from_utf8_lossy(got);
    let w = String::from_utf8_lossy(want);
    let cases = value_cases();
    match g.lines().zip(w.lines()).position(|(a, b)| a != b) {
        Some(k) => {
            let (i, canon) = case_of_line(k);
            format!(
                "case {i} `{}`{}: got {:?} want {:?}",
                cases.get(i).map_or("?", |c| c.0),
                if canon {
                    " (canonical 64-bit form)"
                } else {
                    ""
                },
                g.lines().nth(k),
                w.lines().nth(k)
            )
        }
        None => format!("{} lines, want {}", g.lines().count(), w.lines().count()),
    }
}

#[test]
fn hand_edges_interp_matches_spec() {
    let (c, want) = value_program();
    match fors_oracle::run_candidate(&c) {
        fors_oracle::RunResult::Record(r) => {
            assert_eq!(r.exit, fors_interp::RecordExit::Status(0));
            assert!(
                r.stdout == want,
                "interpreter: {}",
                first_bad(&r.stdout, &want)
            );
        }
        other => panic!("{other:?}"),
    }
    for (name, c, kind) in trap_cases() {
        match fors_oracle::run_candidate(&trap_program(c)) {
            fors_oracle::RunResult::Record(r) => {
                assert!(
                    matches!(r.exit, fors_interp::RecordExit::Trap { kind: k, .. } if k == kind),
                    "{name}: interpreter {:?}, want {kind:?}",
                    r.exit
                );
                assert_eq!(r.stdout, b"before\n", "{name}");
            }
            other => panic!("{name}: {other:?}"),
        }
    }
    println!(
        "{} value cases, {} trap cases",
        value_cases().len(),
        trap_cases().len()
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn hand_edges_native_matches_spec() {
    use fors_oracle::native::{NativeExit, Runner, SIGTRAP, compile};
    let runner = Runner::new().unwrap();
    let (c, want) = value_program();
    let img = compile(&c).expect("compiles");
    let (rec, _) = runner.run(&img.image).expect("runs");
    assert_eq!(rec.exit, NativeExit::Status(0));
    assert!(
        rec.stdout == want,
        "native: {}",
        first_bad(&rec.stdout, &want)
    );
    let mut bad = Vec::new();
    for (name, c, kind) in trap_cases() {
        let img = compile(&trap_program(c)).expect("compiles");
        let (rec, _) = runner.run(&img.image).expect("runs");
        if rec.exit != NativeExit::Signal(SIGTRAP) || rec.stdout != b"before\n" {
            bad.push(format!(
                "{name}: want {kind:?}; native {:?} stdout {:?}",
                rec.exit,
                String::from_utf8_lossy(&rec.stdout)
            ));
        }
    }
    assert!(bad.is_empty(), "{bad:#?}");
}
