//! M2-0's `fors-codegen-dev` gates (`docs/design/m2-dev-backend.md` §10):
//! `refuses_out_of_subset_by_name`, `trap_sites_have_one_brk_each`,
//! `codegen_is_deterministic`, plus the ch05 R1 layering scan
//! (`codegen_dev_consumes_only_oir`) and the determinism source scan.

mod common;

use common::B;
use fors_codegen_dev::compile;
use fors_fir::ty::{PrimKind, TY_UNIT};
use fors_fmir::op::{ArithMode, CmpPred, NO_OPERAND, Op, TrapKind};
use fors_fmir::place::Seg;
use fors_obj::Atom;
use fors_obj::atom::brk_imm;
use fors_oir::from_fmir::reason;

fn refusal(b: B) -> fors_oir::Refusal {
    match b.lower() {
        Err(r) => r,
        Ok(f) => compile(&f, "_fors_main").expect_err("must be refused"),
    }
}

/// One case per refusal row of §10 M2-0 "Refusals".
#[test]
fn refuses_out_of_subset_by_name() {
    // Any op not listed.
    let mut b = B::new();
    let f = b.t(PrimKind::F64);
    let x = b.row(Op::ConstFloat, 0, 0, f);
    b.row(Op::Fadd(Default::default()), x.0, x.0, f);
    let r = refusal(b);
    assert_eq!(r.reason, reason::OP);
    assert_eq!((r.op.as_str(), r.inst), ("ConstFloat", Some(0)));

    // `Unchecked` mode.
    let mut b = B::new();
    let x = b.int(PrimKind::I32, 1);
    let t = b.t(PrimKind::I32);
    b.row(Op::Add(ArithMode::Unchecked), x.0, x.0, t);
    let r = refusal(b);
    assert_eq!(
        (r.reason.as_str(), r.op.as_str()),
        (reason::UNCHECKED, "Add(Unchecked)")
    );

    // `Neg` in Trap or Sat mode on an unsigned type (owner Q6).
    for m in [ArithMode::Trap, ArithMode::Sat] {
        let mut b = B::new();
        let x = b.int(PrimKind::U16, 1);
        let t = b.t(PrimKind::U16);
        b.row(Op::Neg(m), x.0, NO_OPERAND, t);
        assert_eq!(refusal(b).reason, reason::NEG_UNSIGNED, "{m:?}");
    }

    // Any type not listed: usize, f32, an aggregate-free `isize` too.
    for p in [PrimKind::Usize, PrimKind::Isize, PrimKind::F32] {
        let mut b = B::new();
        b.int(p, 1);
        assert_eq!(refusal(b).reason, reason::TYPE, "{p:?}");
    }

    // Any secret-flagged value.
    let mut b = B::new();
    let t = b.t(PrimKind::U64);
    b.val(Op::ConstInt, 7, 0, t, true);
    let r = refusal(b);
    assert_eq!(r.reason, reason::SECRET);
    assert_eq!(r.reason, "secret values need the spill class (M2-10)");

    // A place with a projection.
    let mut b = B::new();
    let x = b.int(PrimKind::U8, 1);
    let t = b.t(PrimKind::U8);
    b.init(0, x, t, &[Seg::Field(0)]);
    assert_eq!(refusal(b).reason, reason::PROJECTION);

    // More than one block.
    let mut b = B::new();
    b.int(PrimKind::U8, 1);
    b.extra_block();
    let r = refusal(b);
    assert_eq!((r.reason.as_str(), r.inst), (reason::BLOCKS, None));

    // Any parameter.
    let mut b = B::new();
    b.param(PrimKind::I64);
    assert_eq!(refusal(b).reason, reason::PARAM);

    // A frame over 32 KiB: 4,097 values need 32,776 bytes.
    let mut b = B::new();
    for i in 0..4_097u64 {
        b.int(PrimKind::U32, i);
    }
    let r = refusal(b);
    assert_eq!((r.reason.as_str(), r.op.as_str()), (reason::FRAME, "frame"));
    // ... and 4,096 values (exactly 32 KiB) still compile.
    let mut b = B::new();
    for i in 0..4_096u64 {
        b.int(PrimKind::U32, i);
    }
    compile(&b.lower().unwrap(), "_fors_main").expect("a 32 KiB frame is in range");

    // An intrinsic other than the two output rows.
    let mut b = B::new();
    let u = b.unit();
    b.intrinsic(3, &[u, u]);
    assert_eq!(refusal(b).reason, reason::INTRINSIC);
}

/// A body with a trap check of every kind M2-0 can raise, on every type,
/// plus an explicit `trap` terminator.
fn trapping_body() -> B {
    let mut b = B::new();
    for p in [
        PrimKind::I8,
        PrimKind::I16,
        PrimKind::I32,
        PrimKind::I64,
        PrimKind::U8,
        PrimKind::U16,
        PrimKind::U32,
        PrimKind::U64,
    ] {
        let t = b.t(p);
        let x = b.int(p, 5);
        let y = b.int(p, 3);
        for op in [
            Op::Add(ArithMode::Trap),
            Op::Sub(ArithMode::Trap),
            Op::Mul(ArithMode::Trap),
            Op::Div(ArithMode::Trap),
            Op::Rem(ArithMode::Trap),
            Op::Div(ArithMode::Wrap),
            Op::Shl(ArithMode::Sat),
            Op::Shr(ArithMode::Trap),
        ] {
            b.row(op, x.0, y.0, t);
        }
        let u64t = b.t(PrimKind::U64);
        let i8t = b.t(PrimKind::I8);
        b.row(Op::ConvChecked, x.0, NO_OPERAND, u64t);
        b.row(Op::ConvChecked, x.0, NO_OPERAND, i8t);
        let bt = b.t(PrimKind::Bool);
        b.row(Op::Icmp(CmpPred::Lt), x.0, y.0, bt);
    }
    let x = b.int(PrimKind::I64, 9);
    let t = b.t(PrimKind::I64);
    b.row(Op::Neg(ArithMode::Trap), x.0, NO_OPERAND, t);
    b.write_line(b"done");
    b.trap(TrapKind::Contract);
    b
}

/// The target of a branch word at byte `pc`, if it is one.
fn branch_target(w: u32, pc: u32) -> Option<u32> {
    let sext = |v: u32, bits: u32| ((v << (32 - bits)) as i32) >> (32 - bits);
    let off = if w & 0xFF00_0010 == 0x5400_0000 || w & 0x7E00_0000 == 0x3400_0000 {
        sext((w >> 5) & 0x7FFFF, 19)
    } else if w & 0x7E00_0000 == 0x3600_0000 {
        sext((w >> 5) & 0x3FFF, 14)
    } else if w & 0xFC00_0000 == 0x1400_0000 {
        sext(w & 0x3FF_FFFF, 26)
    } else {
        return None;
    };
    Some((pc as i64 + 4 * off as i64) as u32)
}

#[test]
fn trap_sites_have_one_brk_each() {
    let f = trapping_body().lower().unwrap();
    let atom = compile(&f, "_fors_main").unwrap();
    let tail_start = atom.traps.iter().map(|r| r.pc).min().expect("sites");
    // Every trap row's pc is a brk of its own kind; no two rows share one.
    let mut pcs: Vec<u32> = atom.traps.iter().map(|r| r.pc).collect();
    pcs.sort_unstable();
    pcs.dedup();
    assert_eq!(pcs.len(), atom.traps.len(), "one row per brk");
    for r in &atom.traps {
        assert_eq!(
            brk_imm(atom.word_at(r.pc as usize)),
            Some(fors_abi::TRAP_BRK_BASE + u16::from(r.kind)),
            "row at {:#x}",
            r.pc
        );
    }
    // The tail is exactly the brks: one per row, contiguous.
    let tail_end = tail_start + 4 * atom.traps.len() as u32;
    let n_brk = (tail_start..tail_end)
        .step_by(4)
        .filter(|&pc| brk_imm(atom.word_at(pc as usize)).is_some())
        .count();
    assert_eq!(n_brk, atom.traps.len());
    // No brk in the hot code; every branch into the tail hits a row's brk,
    // and every row's brk is the target of at least one branch.
    let mut hit = vec![0usize; atom.traps.len()];
    for pc in (0..tail_start).step_by(4) {
        let w = atom.word_at(pc as usize);
        assert!(brk_imm(w).is_none(), "brk in the hot path at {pc:#x}");
        if let Some(t) = branch_target(w, pc)
            && t >= tail_start
        {
            let i = atom
                .traps
                .iter()
                .position(|r| r.pc == t)
                .expect("branch lands on a site");
            hit[i] += 1;
        }
    }
    assert!(
        hit.iter().all(|&h| h >= 1),
        "every site is reached: {hit:?}"
    );
    let kinds: std::collections::BTreeSet<u8> = atom.traps.iter().map(|r| r.kind).collect();
    for k in [
        TrapKind::Overflow,
        TrapKind::DivZero,
        TrapKind::Shift,
        TrapKind::CheckedConversion,
        TrapKind::Contract,
    ] {
        assert!(kinds.contains(&(k as u8)), "{k:?} site present");
    }
}

fn atom_digest(a: &Atom) -> [u8; 32] {
    let mut b = a.code.clone();
    for r in &a.relocs {
        b.extend_from_slice(&r.offset.to_le_bytes());
        b.extend_from_slice(r.target.as_bytes());
    }
    for t in &a.traps {
        b.extend_from_slice(&t.pc.to_le_bytes());
        b.push(t.kind);
    }
    fors_obj::sha256::sha256(&b)
}

fn every_shape() -> B {
    let mut b = trapping_body();
    let t = b.t(PrimKind::U32);
    let x = b.int(PrimKind::U32, 77);
    b.init(3, x, t, &[]);
    let p = b.d.places.intern(3, &[], t);
    let y = b.row(Op::CopyFrom, p.0, NO_OPERAND, t);
    b.write_uint(y);
    let _ = TY_UNIT;
    b
}

/// §5 determinism (1): the same OIR compiled twice in this process, and
/// once more in a child process, gives the same atom bytes.
#[test]
fn codegen_is_deterministic() {
    let f = every_shape().lower().unwrap();
    let a = compile(&f, "_fors_main").unwrap();
    let b = compile(&f, "_fors_main").unwrap();
    assert_eq!(a, b, "two compiles, one process");
    let digest: String = atom_digest(&a).iter().map(|x| format!("{x:02x}")).collect();
    if std::env::var_os("FORS_DETERMINISM_CHILD").is_some() {
        println!("ATOM-DIGEST {digest}");
        return;
    }
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "codegen_is_deterministic",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("FORS_DETERMINISM_CHILD", "1")
        .output()
        .expect("re-run this test binary");
    let text = String::from_utf8_lossy(&out.stdout);
    let child = text
        .lines()
        .find_map(|l| l.split("ATOM-DIGEST ").nth(1))
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_else(|| panic!("child printed no digest: {text}"));
    assert_eq!(child, digest, "two processes, same atom");
}

fn src_files(krate: &str) -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join(krate)
        .join("src");
    let mut out = Vec::new();
    let mut stack = vec![dir];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().is_some_and(|x| x == "rs") {
                out.push((
                    p.display().to_string(),
                    std::fs::read_to_string(&p).unwrap(),
                ));
            }
        }
    }
    out.sort();
    assert!(!out.is_empty(), "{krate} has sources");
    out
}

/// ch05 R1 (§9 "level order"): the code generator sees OIR only — never
/// FMIR, the checker, the syntax tree or the interpreter. And the other
/// backend crates never see the source or the oracle.
#[test]
fn codegen_dev_consumes_only_oir() {
    for (path, text) in src_files("fors-codegen-dev") {
        for banned in [
            "fors_fmir",
            "fors_check",
            "fors_syntax",
            "fors_interp",
            "fors_lower",
        ] {
            assert!(!text.contains(banned), "{path} mentions {banned}");
        }
    }
    for krate in ["fors-oir", "fors-link", "fors-obj", "fors-abi"] {
        for (path, text) in src_files(krate) {
            for banned in ["fors_check", "fors_syntax", "fors_interp"] {
                assert!(!text.contains(banned), "{path} mentions {banned}");
            }
        }
    }
    let manifest =
        std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml")).unwrap();
    let deps = manifest
        .split("[dependencies]")
        .nth(1)
        .and_then(|s| s.split("\n[").next())
        .unwrap();
    assert!(
        !deps.contains("fors-fmir"),
        "fors-codegen-dev depends on FMIR"
    );
}

/// Determinism by construction (§2.2): no hash containers in any backend
/// `src/` (iteration order would leak into the bytes).
#[test]
fn backend_src_has_no_hash_containers() {
    for krate in [
        "fors-abi",
        "fors-oir",
        "fors-codegen-dev",
        "fors-obj",
        "fors-link",
    ] {
        for (path, text) in src_files(krate) {
            for banned in ["HashMap", "HashSet", "RandomState"] {
                assert!(!text.contains(banned), "{path} uses {banned}");
            }
        }
    }
}
