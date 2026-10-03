//! design §9 F10's reducer gate: "the reducer shrinks a seeded miscompile to
//! < 30 FMIR instructions" (design §7.3; `compiler-architecture.md` C3).
//!
//! Each of the seven canned miscompiles of `fors_lower::seeded` (a test-only
//! LOWERING hook, behind the `seeded-miscompile` feature this crate enables
//! only from `[dev-dependencies]`) is injected into the lowering of one seed
//! program (`tests/data/seeded.fors`, 135 FMIR instructions), and the
//! three-stage minimiser shrinks it under the miscompile predicate:
//!
//! - source stage: "the correct lowering and the miscompiled lowering of
//!   this source both build, the correct one runs cleanly, and their runs'
//!   observable records (exit, stdout, stderr) differ";
//! - FMIR and value stages: the same question asked of an FMIR candidate,
//!   with the miscompile applied to the candidate as the other engine
//!   (`fors_lower::seeded::apply` is the very rewrite the hooked lowering
//!   runs last, which `the_hooked_lowering_is_the_rewrite_of_the_correct_one`
//!   pins).

use fors_lower::seeded::{Miscompile, apply, lower_build_miscompiled};
use fors_oracle::Candidate;
use fors_oracle::build::build_source;
use fors_oracle::reduce::{clean_record, differs_under, fmir_size, minimise};

const SEED_PROGRAM: &str = include_str!("data/seeded.fors");
/// The minimiser's seed for every reduction below.
const SEED: u64 = 0x05ee_df10;

fn build_ok(src: &str) -> Result<Candidate, String> {
    build_source(src, &fors_lower::lower_build)
}

fn build_bad(src: &str, m: Miscompile) -> Result<Candidate, String> {
    build_source(src, &|i, o, n| lower_build_miscompiled(i, o, n, m))
}

fn src_pred(m: Miscompile) -> impl FnMut(&str) -> bool {
    move |src: &str| {
        let (Ok(good), Ok(bad)) = (build_ok(src), build_bad(src, m)) else {
            return false;
        };
        let Some(g) = clean_record(&good) else {
            return false;
        };
        match fors_oracle::run_capped(&bad, None, fors_oracle::REDUCE_STEP_CAP) {
            fors_oracle::RunResult::Record(b) => {
                b.exit != g.exit || b.stdout != g.stdout || b.stderr != g.stderr
            }
            _ => true,
        }
    }
}

fn fmir_pred(m: Miscompile) -> impl FnMut(&Candidate) -> bool {
    move |c: &Candidate| {
        differs_under(c, &|d| {
            apply(m, d);
        })
    }
}

#[test]
fn the_hooked_lowering_is_the_rewrite_of_the_correct_one() {
    for m in Miscompile::ALL {
        let mut good = build_ok(SEED_PROGRAM).expect("the seed program builds");
        let bad = build_bad(SEED_PROGRAM, m).expect("the miscompiled build builds");
        let mut rewritten = 0;
        for f in &mut good.prog.fns {
            rewritten += apply(m, &mut f.decl);
        }
        assert!(rewritten > 0, "{}: the seed program exercises it", m.name());
        assert_eq!(
            fors_interp::program_digest(&good.prog),
            fors_interp::program_digest(&bad.prog),
            "{}",
            m.name()
        );
    }
}

#[test]
fn every_seeded_miscompile_is_observable_on_the_seed_program() {
    for m in Miscompile::ALL {
        assert!(src_pred(m)(SEED_PROGRAM), "{}", m.name());
    }
}

#[test]
fn the_reducer_shrinks_each_seeded_miscompile_below_30_fmir_instructions() {
    let start = build_ok(SEED_PROGRAM).expect("builds");
    let input = fmir_size(&start);
    println!("seed program: {input} FMIR instructions");
    let mut sizes = Vec::new();
    for m in Miscompile::ALL {
        let t = std::time::Instant::now();
        let r = minimise(
            SEED_PROGRAM,
            &build_ok,
            &mut src_pred(m),
            &mut fmir_pred(m),
            SEED,
        )
        .unwrap_or_else(|e| panic!("{}: {e}", m.name()));
        let size = fmir_size(&r.candidate);
        println!(
            "{}: {} -> {} FMIR instructions in {:.1}s",
            m.name(),
            input,
            size,
            t.elapsed().as_secs_f64()
        );
        for rep in &r.reports {
            println!("  {}", rep.line());
        }
        println!("  reduced source:\n{}", indent(&r.source));
        // The predicate still holds of the result: a real, reduced miscompile.
        assert!(fmir_pred(m)(&r.candidate), "{}", m.name());
        assert!(size < 30, "{}: {size} FMIR instructions", m.name());
        assert!(size < input);
        sizes.push((m.name(), size));
    }
    println!("sizes: {sizes:?}");
    // The exact sizes, reproducible from `SEED`: a change to the minimiser
    // or the lowering that moves one is seen here, not absorbed by `< 30`.
    assert_eq!(
        sizes,
        [
            ("sub-operand-swap", 20),
            ("lt-as-le", 26),
            ("big-const-off-by-one", 22),
            ("xor-as-or", 22),
            ("wrap-add-as-sat", 11),
            ("lt-operand-swap", 20),
            ("field-one-as-zero", 6),
        ]
    );
}

fn indent(s: &str) -> String {
    s.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| format!("    | {l}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// design §7.3 / the F10 task: "the result reproducible from a seed".
#[test]
fn a_reduction_is_reproducible_from_its_seed() {
    let m = Miscompile::SubOperandSwap;
    let run = || {
        let r = minimise(
            SEED_PROGRAM,
            &build_ok,
            &mut src_pred(m),
            &mut fmir_pred(m),
            SEED,
        )
        .expect("reduces");
        let bytes: Vec<Vec<u8>> = r
            .candidate
            .prog
            .fns
            .iter()
            .map(|f| fors_fmir::encode::to_bytes(&f.decl))
            .collect();
        (r.source, bytes, r.reports)
    };
    assert_eq!(run(), run());
}

/// The hook is unreachable from a real build: the `seeded-miscompile`
/// feature is declared by `fors-lower`, OFF by default, and enabled by no
/// workspace manifest except this crate's `[dev-dependencies]` — so no
/// build of `fors-cli` (or of anything a `fors` binary links) can compile
/// it in. Read from the manifests themselves, so a new enabling line fails
/// here.
#[test]
fn the_miscompile_hook_is_unreachable_from_a_real_build() {
    let crates = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut enabling = Vec::new();
    for e in std::fs::read_dir(&crates).expect("crates dir") {
        let dir = e.expect("entry").path();
        let Ok(toml) = std::fs::read_to_string(dir.join("Cargo.toml")) else {
            continue;
        };
        let name = dir.file_name().unwrap().to_string_lossy().into_owned();
        let mut section = String::new();
        for line in toml.lines() {
            let t = line.trim();
            if t.starts_with('[') {
                section = t.to_string();
                continue;
            }
            if t.starts_with('#') || !t.contains("seeded-miscompile") {
                continue;
            }
            match (name.as_str(), section.as_str()) {
                // The declaration itself, not enabled by default.
                ("fors-lower", "[features]") => {
                    assert!(
                        t.starts_with("seeded-miscompile = []"),
                        "the feature enables nothing else: {t}"
                    );
                }
                _ => enabling.push((name.clone(), section.clone(), t.to_string())),
            }
        }
        if name == "fors-lower" {
            let default = toml
                .lines()
                .find(|l| l.trim_start().starts_with("default"))
                .expect("an explicit default feature set");
            assert_eq!(default.trim(), "default = []");
        }
    }
    assert_eq!(
        enabling,
        vec![(
            "fors-oracle".to_string(),
            "[dev-dependencies]".to_string(),
            "fors-lower = { path = \"../fors-lower\", features = [\"seeded-miscompile\"] }"
                .to_string()
        )],
        "only fors-oracle's tests may enable the hook"
    );
    let cli = std::fs::read_to_string(crates.join("fors-cli/Cargo.toml")).expect("fors-cli");
    assert!(!cli.contains("seeded-miscompile") && !cli.contains("fors-oracle"));
}
