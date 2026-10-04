//! M2-0's native gates (`docs/design/m2-dev-backend.md` §10 M2-0 gate
//! table), macOS/aarch64 only — the only target that can execute the image.
//! Linux CI compiles this file to nothing and runs the non-native gates in
//! `fors-oir`, `fors-codegen-dev`, `fors-obj`, `fors-link` instead.
//!
//! Native execs are the cost here (~0.35 s each, serialised by macOS's
//! first-exec check, whatever the worker count), so the default suite runs
//! the design's 200-seed gate and the 10³ / 10⁴ runs are ignored; run and
//! report them with
//!
//! ```text
//! cargo test --release -p fors-oracle --test native -- --ignored --nocapture
//! ```

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod native_support;

use fors_interp::RecordExit;
use fors_oracle::generate::Profile;
use fors_oracle::native::{NativeExit, Runner, SIGTRAP, compile};
use fors_oracle::native_diff::{NativeVerdict, Tally, check_with, compare, run_seeds};
use fors_oracle::{RunResult, run_candidate};
use native_support::{Builder, KINDS};

use fors_fmir::op::{ArithMode, Op, TrapKind};
use fors_interp::arith::IntKind;

fn interp(c: &fors_oracle::Candidate) -> fors_interp::OracleRecord {
    match run_candidate(c) {
        RunResult::Record(r) => r,
        other => panic!("interpreter: {other:?}"),
    }
}

fn native(c: &fors_oracle::Candidate) -> fors_oracle::native::NativeRecord {
    let img = compile(c).expect("compiles");
    Runner::new().unwrap().run(&img.image).expect("runs").0
}

#[test]
fn native_empty_main_exits_zero() {
    let c = Builder::new().ret();
    let n = native(&c);
    assert_eq!(n.exit, NativeExit::Status(0));
    assert!(n.stdout.is_empty() && n.stderr.is_empty());
    assert_eq!(compare(&interp(&c), &n), NativeVerdict::Ok);
}

#[test]
fn native_write_uint_edges() {
    let mut b = Builder::new();
    let vals = [0u64, 1, 9, 10, 99, 100, 1 << 32, u64::MAX];
    for v in vals {
        let x = b.const_int(v, IntKind::U64);
        b.write_uint(x);
        b.write_line(b"");
    }
    // Narrow and signed operands print their RAW slot bits (the
    // interpreter's `stdout_write_uint` reads `Slot::bits`): -1i8 is 255.
    for k in KINDS {
        let x = b.const_int(u64::MAX, k);
        b.write_uint(x);
        b.write_line(b" <- all ones");
    }
    b.write_line(b"text with bytes \x01\xff and no newline inside");
    let c = b.ret();
    let i = interp(&c);
    let n = native(&c);
    let want: String = vals.iter().map(|v| format!("{v}\n")).collect();
    assert!(
        n.stdout.starts_with(want.as_bytes()),
        "{:?}",
        String::from_utf8_lossy(&n.stdout)
    );
    assert_eq!(n.stdout, i.stdout, "byte-identical to the interpreter");
    assert_eq!(compare(&i, &n), NativeVerdict::Ok);
}

/// Hand-built programs tripping each M2-0 trap kind (the FMIR text format
/// has no constants, so the fixtures use the pool API — see
/// `native_support`): native dies by `SIGTRAP`, the interpreter records
/// `Trap{kind}`, and everything printed before the trap agrees.
#[test]
fn native_trap_exits_by_sigtrap_per_kind() {
    let cases: Vec<(TrapKind, fors_oracle::Candidate)> = vec![
        (TrapKind::Overflow, {
            let mut b = Builder::new();
            b.write_line(b"before");
            let x = b.const_int(i32::MAX as u64, IntKind::I32);
            let y = b.const_int(1, IntKind::I32);
            let r = b.bin(Op::Add(ArithMode::Trap), x, y, IntKind::I32);
            b.write_uint(r);
            b.ret()
        }),
        (TrapKind::DivZero, {
            let mut b = Builder::new();
            b.write_line(b"before");
            let x = b.const_int(7, IntKind::U64);
            let y = b.const_int(0, IntKind::U64);
            let r = b.bin(Op::Div(ArithMode::Wrap), x, y, IntKind::U64);
            b.write_uint(r);
            b.ret()
        }),
        (TrapKind::Shift, {
            let mut b = Builder::new();
            b.write_line(b"before");
            let x = b.const_int(1, IntKind::I16);
            let y = b.const_int(16, IntKind::I16);
            let r = b.bin(Op::Shl(ArithMode::Sat), x, y, IntKind::I16);
            b.write_uint(r);
            b.ret()
        }),
        (TrapKind::CheckedConversion, {
            let mut b = Builder::new();
            b.write_line(b"before");
            let x = b.const_int(u64::MAX, IntKind::I64);
            let r = b.conv(Op::ConvChecked, x, IntKind::U64);
            b.write_uint(r);
            b.ret()
        }),
        // The explicit `trap` terminator.
        (TrapKind::Contract, {
            let mut b = Builder::new();
            b.write_line(b"before");
            b.trap(TrapKind::Contract)
        }),
    ];
    for (kind, c) in cases {
        let i = interp(&c);
        assert!(
            matches!(i.exit, RecordExit::Trap { kind: k, .. } if k == kind),
            "{kind:?}: interpreter {:?}",
            i.exit
        );
        let n = native(&c);
        assert_eq!(n.exit, NativeExit::Signal(SIGTRAP), "{kind:?}");
        assert_eq!(n.stdout, b"before\n");
        assert_eq!(compare(&i, &n), NativeVerdict::Ok, "{kind:?}");
    }
}

fn report(label: &str, t: &Tally, secs: f64) {
    println!("{label}: {} | wall {secs:.1}s", t.line());
    println!(
        "  interp {:.1}s | compile {:.1}s | native spawn+run {:.1}s (summed over workers)",
        t.interp_us as f64 / 1e6,
        t.compile_us as f64 / 1e6,
        t.native_us as f64 / 1e6
    );
    if let Some((seed, n, ph, size)) = &t.largest {
        println!(
            "  largest seed {seed} ({n} FMIR insts, image {size} B): {}",
            ph.line()
        );
    }
    for (seed, v) in &t.failures {
        println!("  seed {seed}: {} {v:?}", v.class());
    }
}

fn assert_clean(t: &Tally, n: u64) {
    assert_eq!(t.total(), n, "every program classified exactly once");
    assert_eq!(t.mismatch, 0, "mismatches");
    assert_eq!(t.refused, 0, "refusals");
    assert_eq!(t.compile_panic, 0, "compile panics");
    assert_eq!(t.spawn_fail, 0, "spawn failures");
    assert_eq!(t.signal, 0, "signals");
    assert_eq!(t.timeout, 0, "timeouts");
    assert_eq!(t.oracle_fail, 0, "oracle failures");
    assert_eq!(t.ok, n);
}

#[test]
fn straight_line_native_diff_200() {
    let start = std::time::Instant::now();
    let t = run_seeds(0..200, &Profile::STRAIGHT_LINE);
    report("straight-line 200", &t, start.elapsed().as_secs_f64());
    assert_clean(&t, 200);
}

/// The 10³ run (seeds 200..1000, the ones the default gate does not
/// cover). Ignored by default: every native exec costs ~0.35 s of
/// serialised first-exec checking on macOS, so 800 of them are ~4.5 min.
///
/// ```text
/// cargo test -p fors-oracle --test native straight_line_native_diff_1k -- --ignored --nocapture
/// ```
#[test]
#[ignore = "800 native execs (~4.5 min on macOS): run on demand, see the doc comment"]
fn straight_line_native_diff_1k() {
    let start = std::time::Instant::now();
    let t = run_seeds(200..1_000, &Profile::STRAIGHT_LINE);
    report("straight-line 200..1000", &t, start.elapsed().as_secs_f64());
    assert_clean(&t, 800);
}

#[test]
#[ignore = "the 10^4 gate: run in a release build (see the module docs)"]
fn straight_line_native_diff_10k() {
    let start = std::time::Instant::now();
    let t = run_seeds(0..10_000, &Profile::STRAIGHT_LINE);
    report("straight-line 10^4", &t, start.elapsed().as_secs_f64());
    assert_clean(&t, 10_000);
}

/// Determinism (§5 (1) and (3)): two compiles of the same program give
/// byte-identical images (SHA-256 equal), and two runs identical records.
#[test]
fn native_build_and_run_twice_identical() {
    for seed in [0u64, 7, 123, 4242] {
        let g = fors_oracle::generate::generate_with(seed, &Profile::STRAIGHT_LINE);
        let c = fors_oracle::Candidate {
            prog: g.prog,
            tys: g.tys,
        };
        let a = compile(&c).unwrap().image;
        let b = compile(&c).unwrap().image;
        assert_eq!(
            fors_obj::sha256::sha256(&a),
            fors_obj::sha256::sha256(&b),
            "seed {seed}: image bytes differ between builds"
        );
        let r1 = Runner::new().unwrap();
        let r2 = Runner::new().unwrap();
        let (x, _) = r1.run(&a).unwrap();
        let (y, _) = r2.run(&b).unwrap();
        assert_eq!(x, y, "seed {seed}: records differ between runs");
        assert_eq!(x.exit, NativeExit::Status(0));
        let (v, _) = check_with(&c, &r1);
        assert_eq!(v, NativeVerdict::Ok);
    }
}

/// A real compiled program's image (runtime atoms + stencil code + literal
/// pool) passes `codesign --verify --strict`, its signature recomputes in
/// pure Rust, `otool -l` shows the load commands §4.1 promises (LC_MAIN,
/// a content-derived LC_UUID, chained fixups, 16 KiB-aligned segments,
/// `__LINKEDIT` starting where `__TEXT` ends), `otool -tv` disassembles
/// the text (every `brk` carries one of the eight trap immediates), the
/// file is `0o755`, and the bytes name no host path.
#[test]
fn compiled_image_is_signed_and_hermetic() {
    let g = fors_oracle::generate::generate_with(3, &Profile::STRAIGHT_LINE);
    let c = fors_oracle::Candidate {
        prog: g.prog,
        tys: g.tys,
    };
    let img = compile(&c).unwrap().image;
    fors_obj::sign::verify_signature(&img).expect("signature recomputes");
    let dir = std::env::temp_dir().join(format!("fors-native-sign-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let p = fors_obj::write::write_executable(&dir, "prog", &img).unwrap();
    {
        use std::os::unix::fs::PermissionsExt;
        let mode = std::fs::metadata(&p).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o755, "file mode");
    }
    let tool = |args: &[&str]| {
        let out = std::process::Command::new(args[0])
            .args(&args[1..])
            .arg(&p)
            .output()
            .unwrap_or_else(|e| panic!("{}: {e}", args[0]));
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).into_owned()
                + &String::from_utf8_lossy(&out.stderr),
        )
    };
    let (ok, text) = tool(&["codesign", "--verify", "--strict", "-vv"]);
    let (otool_ok, lcs) = tool(&["otool", "-l"]);
    let (tv_ok, asm) = tool(&["otool", "-tv"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        ok,
        "codesign --verify --strict rejected a compiled image:\n{text}"
    );
    assert!(otool_ok, "otool -l failed:\n{lcs}");
    for want in [
        "cmd LC_MAIN",
        "cmd LC_UUID",
        "cmd LC_DYLD_CHAINED_FIXUPS",
        "cmd LC_DYLD_EXPORTS_TRIE",
        "cmd LC_CODE_SIGNATURE",
        "cmd LC_FUNCTION_STARTS",
        "segname __PAGEZERO",
        "segname __TEXT",
        "segname __LINKEDIT",
        "sectname __text",
        "sectname __fors_dir",
        "sectname __fors_lines",
    ] {
        assert!(lcs.contains(want), "otool -l lacks {want:?}:\n{lcs}");
    }
    for bad in [
        "__DATA",
        "__eh_frame",
        "__unwind_info",
        "LC_LOAD_WEAK_DYLIB",
    ] {
        assert!(!lcs.contains(bad), "otool -l shows {bad:?}");
    }
    // The UUID otool prints is the content-derived one in the bytes.
    let uuid = fors_obj::uuid::image_uuid(&img).unwrap();
    let hex: String = uuid.iter().map(|b| format!("{b:02X}")).collect();
    let dashed = format!(
        "{}-{}-{}-{}-{}",
        &hex[..8],
        &hex[8..12],
        &hex[12..16],
        &hex[16..20],
        &hex[20..]
    );
    assert!(
        lcs.contains(&format!("uuid {dashed}")),
        "LC_UUID {dashed} not in:\n{lcs}"
    );
    // Segments: __TEXT at the image base, a 16 KiB multiple long, and
    // __LINKEDIT's file offset exactly where __TEXT ends.
    let field = |seg: &str, name: &str| -> u64 {
        let i = lcs.find(&format!("segname {seg}")).expect(seg);
        let rest = &lcs[i..];
        let line = rest
            .lines()
            .find(|l| l.trim_start().starts_with(name))
            .unwrap_or_else(|| panic!("{seg} {name}"));
        let v = line.split_whitespace().nth(1).unwrap();
        u64::from_str_radix(
            v.trim_start_matches("0x"),
            if v.starts_with("0x") { 16 } else { 10 },
        )
        .unwrap()
    };
    assert_eq!(field("__TEXT", "vmaddr"), fors_obj::macho::IMAGE_BASE);
    assert_eq!(field("__TEXT", "fileoff"), 0);
    let text_size = field("__TEXT", "filesize");
    assert_eq!(text_size % 0x4000, 0, "__TEXT filesize is 16 KiB aligned");
    assert_eq!(field("__TEXT", "vmsize"), text_size);
    assert_eq!(field("__LINKEDIT", "fileoff"), text_size);
    assert_eq!(field("__LINKEDIT", "vmsize") % 0x4000, 0);
    // The disassembly: it decodes, holds brk sites of the eight kinds only,
    // and exactly one svc (the allowlisted write).
    assert!(tv_ok, "otool -tv failed:\n{asm}");
    let mut brks = 0;
    let mut svcs = 0;
    for l in asm.lines() {
        let mut it = l.split_whitespace().skip(1);
        match (it.next(), it.next()) {
            (Some("brk"), Some(imm)) => {
                let v = u16::from_str_radix(imm.trim_start_matches("#0x"), 16).unwrap();
                // `fors_abi::TRAP_BRK_BASE + kind`, kind < 8 (ch02 R15).
                assert!(
                    (0x4600..0x4608).contains(&v),
                    "brk {imm} is not a trap kind"
                );
                brks += 1;
            }
            (Some("svc"), _) => svcs += 1,
            _ => {}
        }
    }
    assert!(brks >= 1, "no trap site in:\n{asm}");
    assert_eq!(svcs, 1, "exactly the one write syscall");
    for needle in [
        &b"/Users/"[..],
        b"/home/",
        b"/tmp",
        b"/private/",
        b"/var/folders",
    ] {
        assert!(!img.windows(needle.len()).any(|w| w == needle));
    }
}

/// §5 (1) across processes: the same seed compiled in a child process
/// gives the same image bytes (SHA-256 equal) as in this one — nothing
/// about the image depends on process state, addresses or time.
#[test]
fn image_is_identical_across_processes() {
    let digest = |seed: u64| {
        let g = fors_oracle::generate::generate_with(seed, &Profile::STRAIGHT_LINE);
        let c = fors_oracle::Candidate {
            prog: g.prog,
            tys: g.tys,
        };
        let h = fors_obj::sha256::sha256(&compile(&c).unwrap().image);
        h.iter().map(|b| format!("{b:02x}")).collect::<String>()
    };
    let mine: Vec<String> = [0u64, 7, 123, 4242].iter().map(|&s| digest(s)).collect();
    if std::env::var_os("FORS_IMAGE_DETERMINISM_CHILD").is_some() {
        for d in &mine {
            println!("IMAGE-SHA256 {d}");
        }
        return;
    }
    let out = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "image_is_identical_across_processes",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("FORS_IMAGE_DETERMINISM_CHILD", "1")
        .output()
        .expect("re-run this test binary");
    let text = String::from_utf8_lossy(&out.stdout);
    let theirs: Vec<&str> = text
        .lines()
        .filter_map(|l| l.split("IMAGE-SHA256 ").nth(1))
        .map(|r| r.split_whitespace().next().unwrap())
        .collect();
    assert_eq!(theirs, mine, "image bytes differ across processes:\n{text}");
}
