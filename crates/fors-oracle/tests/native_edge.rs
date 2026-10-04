//! M2-0's arithmetic edge table (`docs/design/m2-dev-backend.md` §10 M2-0,
//! §5 "The corpora", §9 ch03 R2/R4): for every (type, op, mode) of the
//! straight-line surface, one program over all pairs of the generator's
//! interesting values whose `arith.rs` result is not a trap, every result
//! printed. The interpreter half runs everywhere (it pins the table to
//! `arith.rs` before any stencil existed); the native half runs on
//! macOS/aarch64 only.

mod native_support;

use native_support::{edge_cases, edge_program};

/// The table is written against `arith.rs` and the interpreter agrees with
/// it byte for byte: the oracle side of `edge_table_matches_arith_rs`.
#[test]
fn edge_table_interp_matches_arith_rs() {
    let cases = edge_cases();
    let mut pairs = 0;
    for case in &cases {
        let (c, want, n) = edge_program(case);
        pairs += n;
        match fors_oracle::run_candidate(&c) {
            fors_oracle::RunResult::Record(r) => {
                assert_eq!(
                    r.exit,
                    fors_interp::RecordExit::Status(0),
                    "{}",
                    case.name()
                );
                assert!(
                    r.stdout == want,
                    "{}: interpreter disagrees with arith.rs",
                    case.name()
                );
            }
            other => panic!("{}: {other:?}", case.name()),
        }
    }
    println!(
        "edge table: {} programs, {pairs} non-trapping pairs",
        cases.len()
    );
    assert!(cases.len() >= 400, "every (type, op, mode) is present");
}

/// The batched form of the table covers every case exactly once (checked
/// conversions travel in their own, smaller batches, so not in table
/// order) and prints exactly what the per-case programs print, so the
/// native gate below loses nothing by batching.
#[test]
fn edge_batches_cover_every_case() {
    let mut names: Vec<String> = edge_cases().iter().map(|c| c.name()).collect();
    let batches = native_support::edge_batches();
    let mut seen = Vec::new();
    for b in &batches {
        assert!(!b.cases.is_empty());
        let mut want = Vec::new();
        for &(case, n) in &b.cases {
            let (_, w, m) = edge_program(&case);
            assert_eq!(n, m, "{}", case.name());
            want.extend_from_slice(&w);
            seen.push(case.name());
        }
        assert_eq!(b.want, want);
        // And the interpreter agrees with the batched program too.
        match fors_oracle::run_candidate(&b.candidate) {
            fors_oracle::RunResult::Record(r) => {
                assert_eq!(r.exit, fors_interp::RecordExit::Status(0));
                assert!(r.stdout == b.want, "interpreter disagrees on a batch");
            }
            other => panic!("{other:?}"),
        }
    }
    names.sort();
    seen.sort();
    assert_eq!(seen, names, "every case batched exactly once");
    println!("{} cases in {} batches", names.len(), batches.len());
    assert!(
        batches.len() <= 80,
        "{} batches: too many native execs",
        batches.len()
    );
}

/// `edge_table_matches_arith_rs` (§10 M2-0): every (type, op, mode)'s
/// NATIVE stdout equals both `arith.rs` and the interpreter. The cases run
/// batched (`edge_batches`); a failure is still reported per case and pair.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn edge_table_matches_arith_rs() {
    use fors_oracle::native::{NativeExit, Runner, compile};
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let batches = native_support::edge_batches();
    let next = AtomicUsize::new(0);
    let bad: Mutex<Vec<String>> = Mutex::new(Vec::new());
    let pairs = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..8 {
            s.spawn(|| {
                let runner = Runner::new().expect("scratch dir");
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(batch) = batches.get(i) else { break };
                    let names = || {
                        batch
                            .cases
                            .iter()
                            .map(|(c, _)| c.name())
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    pairs.fetch_add(batch.cases.iter().map(|c| c.1).sum(), Ordering::Relaxed);
                    let img = match compile(&batch.candidate) {
                        Ok(x) => x,
                        Err(e) => {
                            bad.lock()
                                .unwrap()
                                .push(format!("batch {i} [{}]: compile {e:?}", names()));
                            continue;
                        }
                    };
                    let (rec, _) = runner.run(&img.image).expect("spawn");
                    let interp = match fors_oracle::run_candidate(&batch.candidate) {
                        fors_oracle::RunResult::Record(r) => r.stdout,
                        other => panic!("{other:?}"),
                    };
                    if rec.exit != NativeExit::Status(0)
                        || rec.stdout != batch.want
                        || rec.stdout != interp
                    {
                        let got = String::from_utf8_lossy(&rec.stdout).into_owned();
                        let exp = String::from_utf8_lossy(&batch.want).into_owned();
                        let first = got
                            .lines()
                            .zip(exp.lines())
                            .position(|(a, b)| a != b)
                            .or_else(|| {
                                (got.lines().count() != exp.lines().count())
                                    .then(|| got.lines().count())
                            });
                        let where_ = first.and_then(|k| batch.locate(k));
                        bad.lock().unwrap().push(format!(
                            "batch {i}: exit {:?}, first differing line {first:?} at {}: got {:?} want {:?}",
                            rec.exit,
                            match where_ {
                                Some((case, pair, canon)) => format!(
                                    "{} pair {pair:?}{}",
                                    case.name(),
                                    if canon { " (canonical 64-bit form)" } else { "" }
                                ),
                                None => format!("end of output [{}]", names()),
                            },
                            first.and_then(|k| got.lines().nth(k)),
                            first.and_then(|k| exp.lines().nth(k)),
                        ));
                    }
                }
            });
        }
    });
    let bad = bad.into_inner().unwrap();
    println!(
        "native edge table: {} cases in {} programs, {} pairs, {} failing",
        batches.iter().map(|b| b.cases.len()).sum::<usize>(),
        batches.len(),
        pairs.load(Ordering::Relaxed),
        bad.len()
    );
    for b in bad.iter().take(40) {
        println!("  {b}");
    }
    assert!(bad.is_empty(), "{} edge batches disagree", bad.len());
}

/// The trap half of the edge table: for every (type, op, mode) with a
/// trapping input pair, one program executing exactly that instance after a
/// marker line. Native must die by `SIGTRAP` after printing the marker, the
/// interpreter must record the `arith.rs` trap kind. Ignored by default:
/// each crash costs a crash-report round trip on macOS (~0.5 s).
///
/// ```text
/// cargo test -p fors-oracle --test native_edge -- --ignored --nocapture
/// ```
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
#[ignore = "one SIGTRAP process per trapping edge case: slow on macOS"]
fn trap_edges_native() {
    use fors_oracle::native::{NativeExit, Runner, SIGTRAP, compile};
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let cases: Vec<_> = edge_cases()
        .into_iter()
        .filter_map(|c| native_support::trap_program(&c).map(|p| (c, p)))
        .collect();
    let next = AtomicUsize::new(0);
    let bad: Mutex<Vec<String>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..8 {
            s.spawn(|| {
                let runner = Runner::new().expect("scratch dir");
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some((case, (c, kind))) = cases.get(i) else {
                        break;
                    };
                    let interp = match fors_oracle::run_candidate(c) {
                        fors_oracle::RunResult::Record(r) => r,
                        other => panic!("{other:?}"),
                    };
                    let interp_ok = matches!(interp.exit,
                        fors_interp::RecordExit::Trap { kind: k, .. } if k == *kind);
                    let img = compile(c).expect("compiles");
                    let (rec, _) = runner.run(&img.image).expect("spawn");
                    if !interp_ok
                        || rec.exit != NativeExit::Signal(SIGTRAP)
                        || rec.stdout != b"before\n"
                    {
                        bad.lock().unwrap().push(format!(
                            "{}: want {kind:?}; interp {:?}; native {:?} stdout {:?}",
                            case.name(),
                            interp.exit,
                            rec.exit,
                            String::from_utf8_lossy(&rec.stdout)
                        ));
                    }
                }
            });
        }
    });
    let bad = bad.into_inner().unwrap();
    println!(
        "trap edges: {} programs, {} failing",
        cases.len(),
        bad.len()
    );
    for b in bad.iter().take(40) {
        println!("  {b}");
    }
    assert!(bad.is_empty());
}
