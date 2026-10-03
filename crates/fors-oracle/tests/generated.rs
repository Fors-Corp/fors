//! design §9 F10's generator gate: generated programs through the
//! differential runner with ZERO interpreter panics and ZERO `ub:` reports.
//! The generator is UB-free and trap-free by construction (`generate.rs`),
//! so every other class must be zero too; each one is counted and printed,
//! never waived. 10³ programs run in the default suite; the 10⁵ gate is an
//! ignored test meant for a release build:
//!
//! ```text
//! cargo test --release -p fors-oracle --test generated -- --ignored --nocapture
//! ```

use fors_oracle::diff::{Tally, run_seeds};
use fors_oracle::generate::generate;

fn assert_all_ok(label: &str, t: &Tally, n: u64, secs: f64) {
    println!("{label}: {} | wall {secs:.1}s", t.line());
    for (seed, v) in &t.failures {
        println!("  seed {seed}: {} {v:?}", v.class());
    }
    assert_eq!(t.total(), n, "every program is classified exactly once");
    assert_eq!(t.panic, 0, "interpreter panics");
    assert_eq!(t.ub, 0, "ub: reports");
    assert_eq!(t.record_mismatch, 0, "record mismatches under replay");
    assert_eq!(t.trap, 0, "traps (impossible by construction)");
    assert_eq!(t.interp_error, 0, "interpreter refusals");
    assert_eq!(t.verify_reject, 0, "generated FMIR that does not verify");
    assert_eq!(t.ok, n);
}

#[test]
fn generated_programs_sample_of_1000_are_clean() {
    let start = std::time::Instant::now();
    let t = run_seeds(0..1_000);
    assert_all_ok("10^3 sample", &t, 1_000, start.elapsed().as_secs_f64());
}

#[test]
#[ignore = "the 10^5 gate: run in a release build (see the module docs)"]
fn generated_programs_100k_are_clean() {
    let start = std::time::Instant::now();
    let t = run_seeds(0..100_000);
    assert_all_ok("10^5 gate", &t, 100_000, start.elapsed().as_secs_f64());
}

/// The generator is a pure function of its seed: the same seed gives the
/// same FMIR bytes, and different seeds give different programs.
#[test]
fn generation_is_deterministic_per_seed() {
    let enc = |seed: u64| -> Vec<Vec<u8>> {
        generate(seed)
            .prog
            .fns
            .iter()
            .map(|f| fors_fmir::encode::to_bytes(&f.decl))
            .collect()
    };
    for seed in [0u64, 1, 7, 12345, u64::MAX] {
        assert_eq!(enc(seed), enc(seed), "seed {seed}");
    }
    assert_ne!(enc(1), enc(2));
}

/// The sample is not vacuous: it exercises loops, calls, every arithmetic
/// mode the generator emits, and prints a checksum every time.
#[test]
fn the_sample_covers_the_generators_shapes() {
    use fors_fmir::op::{ArithMode, Op};
    let mut seen = std::collections::BTreeSet::new();
    let mut calls = 0;
    let mut loops = 0;
    for seed in 0..200 {
        let g = generate(seed);
        for f in &g.prog.fns {
            for (_, r) in f.decl.insts.all_rows() {
                let tag = match r.op {
                    Op::Add(m) | Op::Sub(m) | Op::Mul(m) | Op::Div(m) | Op::Rem(m) => {
                        format!("{:?}", m)
                    }
                    Op::CallDirect => {
                        calls += 1;
                        "call".into()
                    }
                    other => format!("{other:?}"),
                };
                seen.insert(tag);
            }
            for (_, b) in f.decl.blocks.all_rows() {
                if b.term.op == Op::CondBr {
                    loops += 1;
                }
            }
        }
    }
    for m in [ArithMode::Trap, ArithMode::Wrap, ArithMode::Sat] {
        assert!(seen.contains(&format!("{m:?}")), "{m:?} never generated");
    }
    for op in [
        "call",
        "ConvChecked",
        "ConvWrap",
        "ConvSat",
        "Not",
        "Xor",
        "Intrinsic",
    ] {
        assert!(seen.contains(op), "{op} never generated: {seen:?}");
    }
    assert!(calls > 0 && loops > 0);
}
