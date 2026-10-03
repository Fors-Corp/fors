//! The report of a run: every class counted, the coverage table, every
//! mutation's applications, and each failure as a minimised program with the
//! seed that reproduces it (`GEN_EXPLAIN=<seed>` replays one).

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::ast::Program;
use crate::classify::*;
use crate::coverage;
use crate::minimise::minimise;
use crate::mut_corpus;
use crate::mutate::catalogue;
use crate::render::render;
use crate::runner::{self, Case, Tally};

/// The program of `case`, regenerated from its seed (and mutated again).
pub fn reproduce(case: &Case) -> Option<(Program, Option<Expect>)> {
    let prog = runner::generate_guarded(case.seed).ok()?;
    match case.mutation {
        None => Some((prog, None)),
        Some(i) => {
            let (q, e) = runner::apply(&catalogue()[i], &prog, case.seed)?;
            Some((q, Some(e)))
        }
    }
}

/// `case` as the report prints it: what happened, then the minimised program.
pub fn failure(case: &Case) -> String {
    let mut s = String::new();
    let name = case.mutation.map_or("clean", |i| catalogue()[i].name);
    let _ = writeln!(s, "--- seed {} [{name}] {}", case.seed, case.class.label());
    let _ = writeln!(s, "{}", case.detail);
    if let Some(code) = &case.expect {
        let _ = writeln!(s, "expected code {code}");
    }
    let Some((prog, expect)) = reproduce(case) else {
        let _ = writeln!(s, "(the case could not be regenerated from its seed)");
        return s;
    };
    debug_assert_eq!(
        prog.seed, case.seed,
        "a case regenerates the program of its own seed"
    );
    if let Some(e) = &expect {
        let _ = writeln!(s, "mutation: expects {} ({})", e.code, e.note);
    }
    let before = render(&prog).text.lines().count();
    let small = minimise(
        &prog,
        expect.as_ref(),
        case.class == Class::QueryDisagree,
        4000,
    );
    let r = render(&small);
    let _ = writeln!(
        s,
        "minimised from {before} to {} lines:",
        r.text.lines().count()
    );
    for (i, l) in r.text.lines().enumerate() {
        let _ = writeln!(s, "{:4} | {l}", i + 1);
    }
    let res = crate::run::check(&r.text, true);
    for d in &res.diags {
        let (l, c) = line_col(&r.text, d.start);
        let _ = writeln!(
            s,
            "     {} at {l}:{c}: {}",
            d.code,
            d.msg.chars().take(140).collect::<String>()
        );
    }
    for x in &res.silent {
        let _ = writeln!(s, "     silent TY_ERROR at {x}");
    }
    if let Some(p) = &res.panic {
        let _ = writeln!(s, "     panic: {}", p.lines().next().unwrap_or(""));
    }
    s
}

/// The whole report. `show` caps how many distinct failures are printed
/// minimised (per class and mutation).
pub fn full(t: &Tally, label: &str, show: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "=== I11 soundness run: {label} ===");
    let _ = writeln!(
        s,
        "seeds {}  mean program {} lines  query DAG compared on {} programs  seeds without an applicable mutation {}",
        t.seeds,
        t.lines / t.seeds.max(1),
        t.query_checked,
        t.unmutated
    );
    let _ = writeln!(s, "{:<42} {:>10} {:>10}", "class", "clean", "mutant");
    for c in Class::ALL {
        let _ = writeln!(
            s,
            "{:<42} {:>10} {:>10}",
            c.label(),
            t.clean.get(&c).unwrap_or(&0),
            t.mutant.get(&c).unwrap_or(&0)
        );
    }
    let _ = writeln!(s);
    let rows = coverage::rows(t);
    s.push_str(&coverage::render(&rows, t));
    let v = coverage::violations(&rows);
    let _ = writeln!(s, "non-vacuity violations: {}", v.len());
    for x in &v {
        let _ = writeln!(s, "  {x}");
    }
    // Every catalogue row and what became of its applications.
    let _ = writeln!(s);
    let _ = writeln!(
        s,
        "mutations ({} rows; `inject` = a template dropped in, else an in-place rewrite):",
        catalogue().len()
    );
    let mut never = Vec::new();
    for (i, d) in catalogue().iter().enumerate() {
        let row = t.per_mut.get(&i);
        let n: usize = row.map_or(0, |r| r.values().sum());
        if n == 0 {
            never.push(d.name);
            continue;
        }
        let off: Vec<String> = row
            .map(|r| {
                r.iter()
                    .filter(|(k, _)| **k != Class::RejectedAsExpected)
                    .map(|(k, v)| format!("{}={v}", k.label()))
                    .collect()
            })
            .unwrap_or_default();
        let _ = writeln!(
            s,
            "  {:<58} ch{:02} R{:<3} {:<6} {:<6} applied {:>5}{}",
            d.name,
            d.chapter,
            d.rule,
            d.code,
            if d.inject { "inject" } else { "rewrite" },
            n,
            if off.is_empty() {
                String::new()
            } else {
                format!("  NOT AS EXPECTED: {}", off.join(", "))
            }
        );
    }
    let _ = writeln!(s, "mutations never applicable in this run: {}", never.len());
    for n in &never {
        let _ = writeln!(s, "  {n}");
    }
    let h = mut_corpus::harvest();
    let _ = writeln!(
        s,
        "\nconformance corpus: {} check-error tests used as injected templates, {} not injectable:",
        h.usable.len(),
        h.unusable.len()
    );
    for (f, why) in &h.unusable {
        let _ = writeln!(s, "  {f}: {why}");
    }
    // Failures, minimised.
    let bad: Vec<&Case> = t.failures.iter().collect();
    let _ = writeln!(s, "\nfailures: {} recorded (cap {})", bad.len(), 400);
    let mut seen: BTreeMap<(Class, Option<usize>), usize> = BTreeMap::new();
    for c in bad {
        let n = seen.entry((c.class, c.mutation)).or_default();
        *n += 1;
        if *n <= show {
            s.push_str(&failure(c));
        }
    }
    for ((class, m), n) in &seen {
        if *n > show {
            let name = m.map_or("clean", |i| catalogue()[i].name);
            let _ = writeln!(
                s,
                "... {} more of {} [{name}] not printed",
                n - show,
                class.label()
            );
        }
    }
    s
}

/// Writes `text` under the target directory and returns the path.
pub fn save(name: &str, text: &str) -> Option<std::path::PathBuf> {
    let dir = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("i11-gen");
    std::fs::create_dir_all(&dir).ok()?;
    let p = dir.join(name);
    std::fs::write(&p, text).ok()?;
    Some(p)
}
