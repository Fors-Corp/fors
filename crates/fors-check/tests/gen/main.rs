//! I11, the generator half of the type checker's soundness test
//! (`docs/design/type-checker.md` section 13).
//!
//! * `builder`, `body`, `types`: a type-directed generator. It inverts the
//!   typing rules (every production carries the type its node must have), so
//!   a program is accepted BY CONSTRUCTION; any diagnostic on a clean
//!   program is a false rejection, and any `TY_ERROR` node without one is a
//!   silent failure.
//! * `render`: prints the typed AST and records the byte span of every node,
//!   which is what lets a mutation say WHERE its diagnostic must land.
//! * `mutate`, `mut_a`, `mut_corpus`: the typed-mutation engine. Each
//!   catalogue row targets one rule of `rules.rs`, breaks it in one place and
//!   records the code and the site it expects.
//! * `runner`, `classify`, `run`: one clean program and one mutant per seed
//!   through `check_build` (and every 16th through the query DAG), classified
//!   as accepted-as-expected, rejected-with-expected-code-at-site, FALSE
//!   REJECTION, WRONG CODE, WRONG SITE, CASCADE, MISSED, PANIC, SILENT
//!   TY_ERROR or QUERY DISAGREES.
//! * `minimise`, `report`: a failure is shrunk (declarations, statements,
//!   arms and expressions) while its verdict holds and printed with the seed
//!   that reproduces it.
//! * `coverage`: the per-rule table; a rule no mutation flips is listed with
//!   the reason or fails the run.
//! * `gaps`: findings pinned until the checker changes.
//!
//! Run it: `cargo test -p fors-check --test gen` (10^4 seeds, about half a
//! minute); `cargo test --release -p fors-check --test gen -- --ignored
//! million` (10^6). `GEN_SEEDS=<n>` and `GEN_START=<seed>` move either run;
//! `GEN_EXPLAIN=<seed>` (and `GEN_CLEAN=1`) replays one seed's program, and
//! `GEN_FILE=<path>` checks one file and prints every row of the result.

/// One catalogue row of an in-place rewrite.
macro_rules! md {
    ($name:expr, $ch:expr, $rule:expr, $code:expr, $var:expr, $f:expr) => {
        $crate::mutate::MutDef {
            name: $name,
            chapter: $ch,
            rule: $rule,
            code: $code,
            variant: $var,
            f: $f,
            inject: false,
        }
    };
}

mod ast;
mod body;
mod builder;
mod classify;
mod coverage;
mod gaps;
mod minimise;
mod mut_a;
mod mut_corpus;
mod mut_decls;
mod mutate;
mod reid;
mod render;
mod report;
mod rng;
mod run;
mod runner;
mod types;
mod visit;

use classify::Class;

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// Prints and saves the report, then enforces the gate: every class but the
/// two good ones is zero (so no panic, no false rejection, no silent
/// `TY_ERROR`, no wrong code or site, no missed mutant), the query DAG
/// agreed on its sample, and the coverage table has no vacuous rule.
fn gate(t: &runner::Tally, label: &str) {
    let text = report::full(t, label, 3);
    eprintln!("{text}");
    let saved = report::save(&format!("{}.txt", label.replace(' ', "-")), &text);
    if let Some(p) = &saved {
        eprintln!("report saved to {}", p.display());
    }
    assert_eq!(
        t.count(Class::Panic),
        0,
        "check_build or the query DAG panicked; see the report above"
    );
    for c in Class::ALL {
        if !c.is_good() {
            assert_eq!(
                t.count(c),
                0,
                "{} cases of `{}`; see the minimised programs in the report above",
                t.count(c),
                c.label()
            );
        }
    }
    assert!(t.query_checked > 0, "the query DAG was never compared");
    assert_eq!(
        t.unmutated, 0,
        "{} seeds had no applicable mutation",
        t.unmutated
    );
    let rows = coverage::rows(t);
    let v = coverage::violations(&rows);
    assert!(v.is_empty(), "vacuous coverage:\n{}", v.join("\n"));
}

/// The gate's run: 10^4 programs, each clean and mutated.
#[test]
fn ten_thousand_programs_are_accepted_and_their_mutants_rejected() {
    let n = env_u64("GEN_SEEDS", 10_000);
    let start = env_u64("GEN_START", 0);
    let t = runner::run_range(start, n, runner::threads());
    gate(&t, &format!("{n} seeds from {start}"));
}

/// The long run, for a release build:
/// `cargo test --release -p fors-check --test gen -- --ignored million`.
#[test]
#[ignore]
fn million_programs_are_accepted_and_their_mutants_rejected() {
    let n = env_u64("GEN_SEEDS", 1_000_000);
    let start = env_u64("GEN_START", 1_000_000);
    let t = runner::run_range(start, n, runner::threads());
    gate(&t, &format!("{n} seeds from {start}"));
}

/// A seed is the whole input: the same seeds give the same tally on one
/// thread and on several, and the same program text twice.
#[test]
fn runs_are_deterministic_in_the_seed() {
    let one = runner::run_range(500, 200, 1);
    let many = runner::run_range(500, 200, 4);
    assert_eq!(one.clean, many.clean);
    assert_eq!(one.mutant, many.mutant);
    assert_eq!(one.per_rule.len(), many.per_rule.len());
    for (k, v) in &one.per_rule {
        let w = &many.per_rule[k];
        assert_eq!(
            (v.targeted, v.flipped),
            (w.targeted, w.flipped),
            "rule {k:?}"
        );
    }
    for seed in [3u64, 77, 1234] {
        let a = render::render(&runner::generate_guarded(seed).expect("generates")).text;
        let b = render::render(&runner::generate_guarded(seed).expect("generates")).text;
        assert_eq!(a, b, "seed {seed}");
        let p = runner::generate_guarded(seed).expect("generates");
        let ma = runner::mutate_seed(&p, seed).map(|(i, q, _)| (i, render::render(&q).text));
        let mb = runner::mutate_seed(&p, seed).map(|(i, q, _)| (i, render::render(&q).text));
        assert_eq!(ma, mb, "mutant of seed {seed}");
    }
}

/// The generator is not vacuous: over the first thousand programs every
/// feature of the grammar it claims shows up, and every one of them checks.
#[test]
fn the_generator_exercises_the_grammar() {
    let feats: [(&str, &str); 26] = [
        ("generic fn", "fn g"),
        ("bounded generic", "[T: "),
        ("trait declaration", "trait Tr"),
        ("trait impl", " for "),
        ("provided method", "fn p"),
        ("move argument", "move "),
        ("inout marker", "(&"),
        ("inout parameter", "inout p"),
        ("sink parameter", "sink p"),
        ("raises", "raises"),
        ("postfix ?", ")?"),
        ("else |e| handler", "else |"),
        ("defer", "defer"),
        ("errdefer", "errdefer"),
        ("match", "match "),
        ("for loop", "for lp"),
        ("while loop", "while "),
        ("wrap_/sat_", ".wrap_"),
        ("unchecked_", "unchecked_"),
        ("as cast", " as "),
        ("Array", "Array["),
        ("Option", "Option["),
        ("some pattern", "some("),
        ("dot variant", ".va"),
        ("@unsafe", "@unsafe"),
        ("enum", "enum E"),
    ];
    let n = 1000u64;
    let mut counts = vec![0usize; feats.len()];
    for seed in 0..n {
        let text = render::render(&runner::generate_guarded(seed).expect("generates")).text;
        for (i, (_, pat)) in feats.iter().enumerate() {
            if text.contains(pat) {
                counts[i] += 1;
            }
        }
    }
    let mut missing = Vec::new();
    for (i, (name, _)) in feats.iter().enumerate() {
        eprintln!(
            "{name:<20} {:>5.1}% of programs",
            100.0 * counts[i] as f64 / n as f64
        );
        if counts[i] < (n as usize) / 100 {
            missing.push(*name);
        }
    }
    assert!(
        missing.is_empty(),
        "features in fewer than 1% of programs: {missing:?}"
    );
}

/// The corpus-derived templates are really there, and the hand-written ones
/// (rules the corpus has no std-free rejected program for) all validate.
#[test]
fn corpus_templates_are_injectable() {
    let h = mut_corpus::harvest();
    assert!(
        h.usable.len() >= 150,
        "only {} corpus templates are usable",
        h.usable.len()
    );
    let hand: Vec<&String> = h
        .unusable
        .iter()
        .map(|(f, _)| f)
        .filter(|f| f.starts_with("hand/"))
        .collect();
    assert!(
        hand.is_empty(),
        "hand templates that do not validate: {hand:?}"
    );
}

/// The minimiser shrinks a failing program and keeps its verdict: a
/// mutation is given an expectation the checker can never meet (WRONG CODE),
/// and what is left must still be WRONG CODE with the same diagnostics.
#[test]
fn the_minimiser_shrinks_a_failure_and_keeps_its_verdict() {
    let seed = 3;
    let prog = runner::generate_guarded(seed).expect("generates");
    let idx = mutate::catalogue()
        .iter()
        .position(|d| d.name == "slot-mismatch/let-init")
        .expect("in the catalogue");
    let (q, mut e) = runner::apply(&mutate::catalogue()[idx], &prog, seed).expect("applies");
    e.code = "T9999".to_string();
    let (v0, sig0) = minimise::evaluate(&q, Some(&e), false).expect("evaluates");
    assert_eq!(v0.class, Class::WrongCode);
    let small = minimise::minimise(&q, Some(&e), false, 4000);
    let (v1, sig1) = minimise::evaluate(&small, Some(&e), false).expect("evaluates");
    assert_eq!(v1.class, Class::WrongCode);
    assert_eq!(sig0, sig1);
    let (before, after) = (
        render::render(&q).text.lines().count(),
        render::render(&small).text.lines().count(),
    );
    assert!(
        after * 4 < before,
        "minimised from {before} to {after} lines"
    );
}

/// A report for a seed whose verdict is fine still prints the program with
/// line numbers (what `GEN_EXPLAIN` shows).
#[test]
fn explain_prints_the_program() {
    let text = runner::explain(9, true);
    assert!(text.starts_with("seed 9 ["), "{text}");
    assert!(text.contains("module m;"), "{text}");
}

/// `GEN_EXPLAIN=<seed> cargo test --test gen replay -- --nocapture`.
#[test]
fn replay() {
    if let Ok(s) = std::env::var("GEN_EXPLAIN") {
        let seed: u64 = s.parse().unwrap_or(0);
        eprintln!(
            "{}",
            runner::explain(seed, std::env::var("GEN_CLEAN").is_err())
        );
    }
}

fn lc(src: &str, at: u32) -> (usize, usize, String) {
    let at = (at as usize).min(src.len());
    let line = src[..at].matches('\n').count() + 1;
    let bol = src[..at].rfind('\n').map_or(0, |i| i + 1);
    let eol = src[at..].find('\n').map_or(src.len(), |i| at + i);
    (line, at - bol + 1, src[bol..eol].trim().to_string())
}

/// `GEN_FILE=<path> cargo test --test gen probe_file -- --nocapture` checks
/// one source file and prints every row of the result.
#[test]
fn probe_file() {
    let Ok(path) = std::env::var("GEN_FILE") else {
        return;
    };
    let src = std::fs::read_to_string(&path).expect("GEN_FILE reads");
    let res = run::check(&src, true);
    for x in &res.parse {
        eprintln!("PARSE {x}");
    }
    for x in &res.resolve {
        eprintln!("RESOLVE {x}");
    }
    for d in &res.diags {
        let (l, c, t) = lc(&src, d.start);
        eprintln!(
            "DIAG {} {l}:{c}..{} site {} {} | {t}",
            d.code,
            d.end,
            d.site,
            d.msg.chars().take(110).collect::<String>()
        );
    }
    for x in &res.silent {
        eprintln!("SILENT {x}");
    }
    if let Some(p) = &res.panic {
        eprintln!("PANIC {p}");
    }
    eprintln!("-- done");
}
