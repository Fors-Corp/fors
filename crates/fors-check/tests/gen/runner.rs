//! The soundness runner: for each seed, one clean program (must be accepted)
//! and one mutated program (must be rejected with the mutation's code at the
//! mutation's site), classified, tallied, and reproducible from the seed.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::ast::Program;
use crate::builder;
use crate::classify::*;
use crate::mutate::{MutDef, catalogue};
use crate::render::{Rendered, render};
use crate::rng::Rng;
use crate::run;

#[derive(Clone, Debug)]
pub struct Case {
    pub seed: u64,
    /// `None` for the clean program, else the catalogue index.
    pub mutation: Option<usize>,
    pub class: Class,
    pub detail: String,
    pub expect: Option<String>,
}

#[derive(Default, Clone, Debug)]
pub struct CodeTally {
    pub targeted: usize,
    pub flipped: usize,
}

#[derive(Default, Clone, Debug)]
pub struct Tally {
    pub seeds: usize,
    pub clean: BTreeMap<Class, usize>,
    pub mutant: BTreeMap<Class, usize>,
    pub per_mut: BTreeMap<usize, BTreeMap<Class, usize>>,
    pub per_code: BTreeMap<String, CodeTally>,
    /// By (chapter, rule) of the mutation's catalogue row.
    pub per_rule: BTreeMap<(u8, u16), CodeTally>,
    /// Seeds for which no mutation of the catalogue applied.
    pub unmutated: usize,
    pub query_checked: usize,
    pub failures: Vec<Case>,
    /// Source length statistics, for the report.
    pub lines: usize,
}

const MAX_FAILURES: usize = 400;

impl Tally {
    pub fn merge(&mut self, o: Tally) {
        self.seeds += o.seeds;
        for (k, v) in o.clean {
            *self.clean.entry(k).or_default() += v;
        }
        for (k, v) in o.mutant {
            *self.mutant.entry(k).or_default() += v;
        }
        for (m, row) in o.per_mut {
            for (k, v) in row {
                *self.per_mut.entry(m).or_default().entry(k).or_default() += v;
            }
        }
        for (c, t) in o.per_code {
            let e = self.per_code.entry(c).or_default();
            e.targeted += t.targeted;
            e.flipped += t.flipped;
        }
        for (c, t) in o.per_rule {
            let e = self.per_rule.entry(c).or_default();
            e.targeted += t.targeted;
            e.flipped += t.flipped;
        }
        self.unmutated += o.unmutated;
        self.query_checked += o.query_checked;
        self.lines += o.lines;
        for f in o.failures {
            if self.failures.len() < MAX_FAILURES {
                self.failures.push(f);
            }
        }
    }

    pub fn count(&self, c: Class) -> usize {
        self.clean.get(&c).copied().unwrap_or(0) + self.mutant.get(&c).copied().unwrap_or(0)
    }
}

fn fnv(s: &str) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

/// Applies the catalogue entry `def` to a copy of `prog`.
pub fn apply(def: &MutDef, prog: &Program, seed: u64) -> Option<(Program, Expect)> {
    let mut q = prog.clone();
    let mut rng = Rng::new(seed ^ fnv(def.name));
    let a = (def.f)(&mut q, &mut rng, def.variant)?;
    let code = a.code.unwrap_or(def.code).to_string();
    Some((
        q,
        Expect {
            code,
            target: a.target,
            note: a.note,
        },
    ))
}

/// The catalogue index tried first for `seed`: round-robin, so every
/// mutation is attempted on an equal share of the seeds.
fn first_kind(seed: u64) -> usize {
    (seed as usize) % catalogue().len()
}

/// The mutated program of `seed`: the first applicable catalogue entry from
/// the round-robin position on.
pub fn mutate_seed(prog: &Program, seed: u64) -> Option<(usize, Program, Expect)> {
    let n = catalogue().len();
    let start = first_kind(seed);
    for k in 0..n {
        let idx = (start + k) % n;
        if let Some((q, e)) = apply(&catalogue()[idx], prog, seed) {
            return Some((idx, q, e));
        }
    }
    None
}

/// Generates the program of `seed`, catching a generator panic.
pub fn generate_guarded(seed: u64) -> Result<Program, String> {
    run::guarded(|| builder::generate(seed).0)
}

/// How many seeds in this many also go through the query DAG.
const QUERY_EVERY: u64 = 16;

/// The verdict of the query-DAG comparison when it is not an agreement: a
/// panic of the query path, or rows that differ from `check_build`'s.
pub fn query_disagreement(text: &str, res: &run::CheckResult) -> Option<Verdict> {
    if res.panic.is_some() || !res.parse.is_empty() {
        return None;
    }
    match run::query_rows(text) {
        Err(msg) => Some(Verdict {
            class: Class::Panic,
            detail: format!("query DAG: {msg}"),
        }),
        Ok(q) => {
            let b = run::build_rows(res);
            if q == b {
                None
            } else {
                Some(Verdict {
                    class: Class::QueryDisagree,
                    detail: format!("check_build: {b:?}; query DAG: {q:?}"),
                })
            }
        }
    }
}

/// Compares the query DAG with `check_build` on every `QUERY_EVERY`-th seed.
fn compare_query(
    t: &mut Tally,
    seed: u64,
    mutation: Option<usize>,
    text: &str,
    res: &run::CheckResult,
    code: Option<String>,
) {
    if !seed.is_multiple_of(QUERY_EVERY) || res.panic.is_some() || !res.parse.is_empty() {
        return;
    }
    t.query_checked += 1;
    if let Some(v) = query_disagreement(text, res) {
        record(t, seed, mutation, v, code);
    }
}

pub fn run_seed(seed: u64, t: &mut Tally) {
    t.seeds += 1;
    let prog = match generate_guarded(seed) {
        Ok(p) => p,
        Err(msg) => {
            *t.clean.entry(Class::GenPanic).or_default() += 1;
            push_failure(t, seed, None, Class::GenPanic, msg, None);
            return;
        }
    };
    let r = render(&prog);
    t.lines += r.text.lines().count();
    let res = run::check(&r.text, true);
    let v = classify(&res, &r.text, &r.spans, None);
    record(t, seed, None, v, None);
    compare_query(t, seed, None, &r.text, &res, None);
    // The mutant.
    let mutated = run::guarded(|| mutate_seed(&prog, seed));
    let (idx, q, expect) = match mutated {
        Ok(Some(x)) => x,
        Ok(None) => {
            t.unmutated += 1;
            return;
        }
        Err(msg) => {
            // A mutation that panics is a bug of the engine, counted like a
            // generator panic.
            *t.mutant.entry(Class::GenPanic).or_default() += 1;
            push_failure(
                t,
                seed,
                None,
                Class::GenPanic,
                format!("mutation: {msg}"),
                None,
            );
            return;
        }
    };
    let rm: Rendered = render(&q);
    let res = run::check(&rm.text, false);
    let v = classify(&res, &rm.text, &rm.spans, Some(&expect));
    let code = expect.code.clone();
    let def = &catalogue()[idx];
    let flipped = v.class == Class::RejectedAsExpected;
    for ct in [
        t.per_code.entry(code.clone()).or_default(),
        t.per_rule.entry((def.chapter, def.rule)).or_default(),
    ] {
        ct.targeted += 1;
        if flipped {
            ct.flipped += 1;
        }
    }
    // A mutant that was accepted deserves the silent sweep too.
    let v = if v.class == Class::Missed {
        let res2 = run::check(&rm.text, true);
        classify(&res2, &rm.text, &rm.spans, Some(&expect))
    } else {
        v
    };
    record(t, seed, Some(idx), v, Some(code.clone()));
    compare_query(t, seed, Some(idx), &rm.text, &res, Some(code));
}

fn push_failure(
    t: &mut Tally,
    seed: u64,
    mutation: Option<usize>,
    class: Class,
    detail: String,
    expect: Option<String>,
) {
    if t.failures.len() < MAX_FAILURES {
        t.failures.push(Case {
            seed,
            mutation,
            class,
            detail,
            expect,
        });
    }
}

fn record(t: &mut Tally, seed: u64, mutation: Option<usize>, v: Verdict, expect: Option<String>) {
    let map = if mutation.is_some() {
        &mut t.mutant
    } else {
        &mut t.clean
    };
    *map.entry(v.class).or_default() += 1;
    if let Some(m) = mutation {
        *t.per_mut.entry(m).or_default().entry(v.class).or_default() += 1;
    }
    if !v.class.is_good() {
        push_failure(t, seed, mutation, v.class, v.detail, expect);
    }
}

/// Runs seeds `start..start + n` on `threads` workers.
pub fn run_range(start: u64, n: u64, threads: usize) -> Tally {
    let next = AtomicU64::new(0);
    let mut total = Tally::default();
    std::thread::scope(|s| {
        let mut hs = Vec::new();
        for _ in 0..threads.max(1) {
            hs.push(s.spawn(|| {
                let mut t = Tally::default();
                loop {
                    // Seeds are handed out in chunks so the workers do not
                    // fight over the counter.
                    let k = next.fetch_add(64, Ordering::Relaxed);
                    if k >= n {
                        break;
                    }
                    for i in k..(k + 64).min(n) {
                        run_seed(start + i, &mut t);
                    }
                }
                t
            }));
        }
        for h in hs {
            total.merge(
                h.join()
                    .expect("a worker never panics: every check is guarded"),
            );
        }
    });
    total.failures.sort_by_key(|c| (c.seed, c.mutation));
    total
}

pub fn threads() -> usize {
    std::thread::available_parallelism()
        .map_or(2, |n| n.get())
        .min(16)
}

#[allow(dead_code)]
pub fn by_class(m: &BTreeMap<Class, usize>) -> HashMap<&'static str, usize> {
    m.iter().map(|(k, v)| (k.label(), *v)).collect()
}

/// The full story of one seed, for a human: the mutation, what it promised,
/// what the checker said, and the mutated program with line numbers.
pub fn explain(seed: u64, mutated: bool) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let prog = match generate_guarded(seed) {
        Ok(p) => p,
        Err(m) => return format!("seed {seed}: generator panic: {m}\n"),
    };
    let (text, spans, expect, name) = if mutated {
        match mutate_seed(&prog, seed) {
            Some((i, q, e)) => {
                let r = render(&q);
                (r.text, r.spans, Some(e), catalogue()[i].name)
            }
            None => return format!("seed {seed}: no mutation applies\n"),
        }
    } else {
        let r = render(&prog);
        (r.text, r.spans, None, "clean")
    };
    let res = run::check(&text, true);
    let v = classify(&res, &text, &spans, expect.as_ref());
    let _ = writeln!(out, "seed {seed} [{name}] {}", v.class.label());
    if let Some(e) = &expect {
        let (lo, hi) = spans.get(&e.target).copied().unwrap_or((0, 0));
        let (l, c) = line_col(&text, lo);
        let _ = writeln!(
            out,
            "expected {} at {l}:{c} ({}): {}",
            e.code,
            hi - lo,
            e.note
        );
    }
    if !v.detail.is_empty() {
        let _ = writeln!(out, "{}", v.detail);
    }
    for (i, l) in text.lines().enumerate() {
        let _ = writeln!(out, "{:4} {l}", i + 1);
    }
    out
}
