//! The minimiser under its two other predicates (design §7.3; the F10 task:
//! "a miscompile, a panic or a ub report"): a `ub:` report injected into a
//! GENERATED program is shrunk at the FMIR and value levels to the handful
//! of instructions that still read the uninitialised place, and the panic
//! predicate is false over the whole generated sample (the interpreter does
//! not panic on any of it; `generated.rs` counts that at 10³ and 10⁵).

use fors_fmir::op::Op;
use fors_interp::UbClass;
use fors_oracle::Candidate;
use fors_oracle::generate::generate;
use fors_oracle::reduce::{delete_insts, fmir_size, minimise_fmir, panics, ub_of_class};

/// Generated program `seed` with the entry block's FIRST `init` (the
/// checksum's initialisation, which `generate` always emits first) removed:
/// the final `write_uint` of the checksum then reads an uninitialised local.
fn with_uninit_checksum(seed: u64) -> Candidate {
    let g = generate(seed);
    let mut c = Candidate {
        prog: g.prog,
        tys: g.tys,
    };
    let main = &mut c.prog.fns[c.prog.entry].decl;
    let first_init = main
        .insts
        .all_rows()
        .find(|(_, r)| r.op == Op::Init)
        .map(|(i, _)| i.index())
        .expect("the checksum init");
    let mut del = vec![false; main.insts.len()];
    del[first_init] = true;
    *main = delete_insts(main, &del).expect("no try_br names an init");
    c
}

#[test]
fn a_ub_report_reduces_to_the_read_that_shows_it() {
    for seed in [3u64, 11, 42] {
        let c = with_uninit_checksum(seed);
        let mut pred = |c: &Candidate| ub_of_class(c, UbClass::UninitRead);
        assert!(pred(&c), "seed {seed}: the injected read is reported");
        let before = fmir_size(&c);
        let (reduced, reports) = minimise_fmir(&c, &mut pred, 7).expect("reduces");
        let after = fmir_size(&reduced);
        println!("seed {seed}: uninit-read {before} -> {after} FMIR instructions");
        for r in &reports {
            println!("  {}", r.line());
        }
        assert!(pred(&reduced));
        assert!(after < 10, "seed {seed}: {after}");
    }
}

#[test]
fn the_panic_predicate_holds_of_no_generated_program() {
    for seed in 0..100 {
        let g = generate(seed);
        let c = Candidate {
            prog: g.prog,
            tys: g.tys,
        };
        assert!(!panics(&c), "seed {seed}");
    }
}

/// Same input, predicate and seed: the same reduction, byte for byte; a
/// different seed may take a different path but must also satisfy the
/// predicate.
#[test]
fn an_fmir_reduction_is_reproducible_from_its_seed() {
    let c = with_uninit_checksum(5);
    let mut pred = |c: &Candidate| ub_of_class(c, UbClass::UninitRead);
    let enc = |c: &Candidate| -> Vec<Vec<u8>> {
        c.prog
            .fns
            .iter()
            .map(|f| fors_fmir::encode::to_bytes(&f.decl))
            .collect()
    };
    let (a, ra) = minimise_fmir(&c, &mut pred, 99).unwrap();
    let (b, rb) = minimise_fmir(&c, &mut pred, 99).unwrap();
    assert_eq!(enc(&a), enc(&b));
    assert_eq!(ra, rb);
    let (other, _) = minimise_fmir(&c, &mut pred, 100).unwrap();
    assert!(pred(&other));
}
