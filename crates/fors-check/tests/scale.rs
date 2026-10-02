//! I2's scale measurement (ignored by default), design §13's MEASUREMENT for
//! this increment: signature lowering over the ~100k-line generated corpus,
//! within +50% time and +1.5 bytes per source byte of the I0 baseline
//! (43-44 ms index+resolve, 3.1-3.6 B/source byte).
//!
//! `cargo test --release -p fors-check --test scale -- --ignored --nocapture`
//!
//! The generator is `fors-resolve`'s `scale.rs` shape, copied rather than
//! shared because a `tests/` target cannot be imported from another crate and
//! `tests/conformance/**` is not this increment's to restructure. Design §12
//! makes `crates/fors-check/tests/scale.rs` the home of the generator that
//! adds generic shapes (adaptor chains, k impls per head, projection-heavy
//! signatures); I2 adds the signature-level ones it can measure without a
//! body checker.

use std::alloc::{GlobalAlloc, Layout, System};
use std::fmt::Write as _;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use fors_index::{Interner, Segments};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

struct Counting;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let now = LIVE.fetch_add(l.size(), Ordering::Relaxed) + l.size();
        PEAK.fetch_max(now, Ordering::Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static A: Counting = Counting;

// MARC: verification of I2/I3 (2026-09-20). `LIVE`/`PEAK` are process-wide,
// so the three measurements run in parallel test threads corrupted each
// other (a negative "retained", non-monotonic walls). They take this lock
// in turn; `--test-threads=1` is no longer needed for the numbers to mean
// anything.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The I0 baseline's generator, verbatim in shape: no traits, no impls, no
/// projections. The design's "+50% time, +1.5 B/source byte over the I0
/// baseline" is stated against THIS corpus, so it is measured against this
/// one as well as against the richer shape below.
fn module_source_i0(m: usize, items: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "module pkg.m{m};");
    if m > 0 {
        let _ = writeln!(s, "use pkg.m{p}, pkg.m{p}.Shape{p}_0;", p = m - 1);
    }
    for i in 0..items {
        let _ = writeln!(
            s,
            "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}"
        );
        let _ = writeln!(
            s,
            "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}"
        );
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        let _ = writeln!(
            s,
            "pub fn work{m}_{i}[T](let x: i32, let item: T, let sh: Shape{m}_{i}) -> i32 {{"
        );
        let _ = writeln!(s, "    let base: i32 = x + LIMIT{m}_{i};");
        let _ = writeln!(s, "    let scale = |k: i32| k * base;");
        let _ = writeln!(s, "    var total: i32 = 0;");
        let _ = writeln!(s, "    for j in 0..<base {{");
        let _ = writeln!(s, "        total = total + scale(j);");
        let _ = writeln!(s, "    }}");
        let _ = writeln!(s, "    let picked: i32 = match sh {{");
        let _ = writeln!(s, "        Shape{m}_{i}.dot => 0,");
        let _ = writeln!(s, "        Shape{m}_{i}.line(let len) => len,");
        let _ = writeln!(s, "        let other => total,");
        let _ = writeln!(s, "    }};");
        if m > 0 {
            let _ = writeln!(
                s,
                "    let prev: i32 = m{p}.work{p}_{i}(x, item, m{p}.Shape{p}_{i}.dot);",
                p = m - 1
            );
        } else {
            let _ = writeln!(s, "    let prev: i32 = 0;");
        }
        let _ = writeln!(s, "    return picked + prev + total;");
        let _ = writeln!(s, "}}");
    }
    s
}

fn module_source(m: usize, items: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "module pkg.m{m};");
    if m > 0 {
        let _ = writeln!(s, "use pkg.m{p}, pkg.m{p}.Shape{p}_0;", p = m - 1);
    }
    for i in 0..items {
        let _ = writeln!(
            s,
            "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}"
        );
        let _ = writeln!(
            s,
            "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}"
        );
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        // A trait with an associated type, an impl of it, and a signature
        // that projects on a bound: the shapes I2's lowering actually costs
        // something on (R61's bound search, R17's substitution, R19's bucket).
        let _ = writeln!(
            s,
            "pub trait Keyed{m}_{i} {{ type Key: Eq + Ord; fn key(let self) -> Self.Key; }}"
        );
        let _ = writeln!(s, "impl Keyed{m}_{i} for Rec{m}_{i} {{");
        let _ = writeln!(s, "    type Key = i64;");
        let _ = writeln!(
            s,
            "    fn key(let self: Rec{m}_{i}) -> i64 {{ return self.b; }}"
        );
        let _ = writeln!(s, "}}");
        let _ = writeln!(
            s,
            "pub struct Wrap{m}_{i}[K: Keyed{m}_{i}] {{ inner: K, seen: Option[K.Key] }}"
        );
        let _ = writeln!(
            s,
            "pub fn work{m}_{i}[T](let x: i32, let item: T, let sh: Shape{m}_{i}) -> i32 {{"
        );
        let _ = writeln!(s, "    let base: i32 = x + LIMIT{m}_{i};");
        let _ = writeln!(s, "    let scale = |k: i32| k * base;");
        let _ = writeln!(s, "    var total: i32 = 0;");
        let _ = writeln!(s, "    for j in 0..<base {{");
        let _ = writeln!(s, "        total = total + scale(j);");
        let _ = writeln!(s, "    }}");
        let _ = writeln!(s, "    let picked: i32 = match sh {{");
        let _ = writeln!(s, "        Shape{m}_{i}.dot => 0,");
        let _ = writeln!(s, "        Shape{m}_{i}.line(let len) => len,");
        let _ = writeln!(s, "        let other => total,");
        let _ = writeln!(s, "    }};");
        if m > 0 {
            let _ = writeln!(
                s,
                "    let prev: i32 = m{p}.work{p}_{i}(x, item, m{p}.Shape{p}_{i}.dot);",
                p = m - 1
            );
        } else {
            let _ = writeln!(s, "    let prev: i32 = 0;");
        }
        let _ = writeln!(s, "    return picked + prev + total;");
        let _ = writeln!(s, "}}");
    }
    s
}

/// I3's corpus: the I0 shape with every generic parameter removed, so
/// EVERY body is typed end to end (a generic call has parameters to
/// determine and is I5's, which would leave most of the work unvisited and
/// the measurement meaningless).
fn module_source_nongeneric(m: usize, items: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "module pkg.m{m};");
    if m > 0 {
        let _ = writeln!(s, "use pkg.m{p}, pkg.m{p}.Shape{p}_0;", p = m - 1);
    }
    for i in 0..items {
        let _ = writeln!(
            s,
            "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}"
        );
        let _ = writeln!(
            s,
            "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}"
        );
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        let _ = writeln!(
            s,
            "pub fn work{m}_{i}(let x: i32, let sh: Shape{m}_{i}) -> i32 {{"
        );
        let _ = writeln!(s, "    let base: i32 = x + LIMIT{m}_{i};");
        let _ = writeln!(s, "    let scale = |let k: i32| k * base;");
        let _ = writeln!(s, "    var total: i32 = 0;");
        let _ = writeln!(s, "    for j in 0 ..< base {{");
        let _ = writeln!(s, "        total = total + scale(j);");
        let _ = writeln!(s, "    }}");
        let _ = writeln!(s, "    let picked: i32 = match sh {{");
        let _ = writeln!(s, "        Shape{m}_{i}.dot => 0,");
        let _ = writeln!(s, "        Shape{m}_{i}.line(let len) => len,");
        let _ = writeln!(s, "        let other => total,");
        let _ = writeln!(s, "    }};");
        let _ = writeln!(
            s,
            "    let made: Rec{m}_{i} = Rec{m}_{i} {{ a: 1, b: 2, tag: Shape{m}_{i}.dot }};"
        );
        let _ = writeln!(s, "    let sum: i64 = made.b + 3i64;");
        if m > 0 {
            let _ = writeln!(
                s,
                "    let prev: i32 = m{p}.work{p}_{i}(x, m{p}.Shape{p}_{i}.dot);",
                p = m - 1
            );
        } else {
            let _ = writeln!(s, "    let prev: i32 = 0;");
        }
        let _ = writeln!(
            s,
            "    return picked + prev + total + made.a + (sum as i32);"
        );
        let _ = writeln!(s, "}}");
    }
    s
}

/// Design §12's near-linearity gate, first real run (design §13's I3
/// MEASUREMENT): every deterministic counter per source line is flat
/// within 5% from 12.5k to 200k lines. A layout mistake — a per-node
/// allocation, a scan that is linear in the build rather than in the
/// declaration — shows up here as a counter that grows.
#[test]
#[ignore]
fn scale_counters_are_flat() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let sizes = [31usize, 62, 125, 250, 500];
    let mut rows: Vec<(usize, fors_check::Counters, f64)> = Vec::new();
    for modules in sizes {
        let sources: Vec<String> = (0..modules)
            .map(|m| module_source_nongeneric(m, 20))
            .collect();
        let lines: usize = sources.iter().map(|s| s.lines().count()).sum();
        let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
        assert!(
            parsed.iter().all(|p| p.diags.is_empty()),
            "generated source must parse"
        );
        let mut interner = Interner::new();
        let names: Vec<Segments> = (0..modules)
            .map(|m| {
                vec![
                    interner.intern(b"pkg"),
                    interner.intern(format!("m{m}").as_bytes()),
                ]
            })
            .collect();
        let inputs: Vec<FileInput> = parsed
            .iter()
            .zip(&sources)
            .zip(&names)
            .map(|((p, s), n)| FileInput {
                tree: &p.tree,
                tokens: &p.tokens,
                source: s.as_bytes(),
                name: n.clone(),
            })
            .collect();
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        assert!(
            resolved.files.iter().all(|f| f.diagnostics.is_empty()),
            "generated package must resolve cleanly"
        );
        let t = Instant::now();
        let out = fors_check::check_build(&inputs, &resolved, &mut interner);
        let wall = t.elapsed().as_secs_f64();
        assert!(
            out.diagnostics.is_empty(),
            "the non-generic corpus must check CLEAN, got {:?}",
            out.diagnostics.iter().take(4).collect::<Vec<_>>()
        );
        assert_eq!(
            out.counters.bodies_skipped, 0,
            "no body may be skipped in a clean build"
        );
        rows.push((lines, out.counters, wall));
    }
    let names: [(&str, fn(&fors_check::Counters) -> u64); 8] = [
        ("nodes_visited", |c| c.nodes_visited),
        ("synths", |c| c.synths),
        ("checks", |c| c.checks),
        ("subst_norm_calls", |c| c.subst_norm_calls),
        ("holds_probes", |c| c.holds_probes),
        ("impl_scans", |c| c.impl_scans),
        ("tape_events", |c| c.tape_events),
        ("types_interned", |c| c.types_interned),
    ];
    eprintln!(
        "lines      wall      bodies  {}",
        names
            .iter()
            .map(|&(n, _)| format!("{n:>17}"))
            .collect::<String>()
    );
    for (lines, c, wall) in &rows {
        eprintln!(
            "{lines:<10} {:>7.1}ms {:>7}  {}",
            wall * 1000.0,
            c.bodies_checked,
            names
                .iter()
                .map(|&(_, f)| format!("{:>17.4}", f(c) as f64 / *lines as f64))
                .collect::<String>()
        );
    }
    let mut bad = Vec::new();
    for (name, f) in names {
        let per: Vec<f64> = rows
            .iter()
            .map(|(l, c, _)| f(c) as f64 / *l as f64)
            .collect();
        let (lo, hi) = per
            .iter()
            .fold((f64::MAX, 0.0f64), |(a, b), &x| (a.min(x), b.max(x)));
        if lo > 0.0 && hi / lo > 1.05 {
            bad.push(format!(
                "{name}: per-line {lo:.4}..{hi:.4} (x{:.3})",
                hi / lo
            ));
        }
    }
    assert!(
        bad.is_empty(),
        "counters are not flat across 12.5k-200k lines:\n{}",
        bad.join("\n")
    );
}

#[test]
#[ignore]
fn scale_100k_lines_signatures_i0_shape() {
    run(true);
}

#[test]
#[ignore]
fn scale_100k_lines_signatures() {
    run(false);
}

fn run(i0_shape: bool) {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (modules, items) = (250, 20);
    let shape = if i0_shape {
        module_source_i0
    } else {
        module_source
    };
    let sources: Vec<String> = (0..modules).map(|m| shape(m, items)).collect();
    let bytes: usize = sources.iter().map(|s| s.len()).sum();
    let lines: usize = sources.iter().map(|s| s.lines().count()).sum();

    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
    assert!(
        parsed.iter().all(|p| p.diags.is_empty()),
        "generated source must parse"
    );

    let mut interner = Interner::new();
    let names: Vec<Segments> = (0..modules)
        .map(|m| {
            vec![
                interner.intern(b"pkg"),
                interner.intern(format!("m{m}").as_bytes()),
            ]
        })
        .collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(&sources)
        .zip(&names)
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s.as_bytes(),
            name: n.clone(),
        })
        .collect();

    let before = LIVE.load(Ordering::Relaxed);
    PEAK.store(before, Ordering::Relaxed);
    let t1 = Instant::now();
    let out = fors_resolve::resolve(&mut interner, &inputs, None);
    let resolve_time = t1.elapsed();
    let resolve_retained = LIVE.load(Ordering::Relaxed) - before;
    let resolve_peak = PEAK.load(Ordering::Relaxed) - before;
    if let Some(d) = out.files.iter().flat_map(|f| &f.diagnostics).next() {
        panic!("generated package must resolve cleanly, got {d:?}");
    }

    let before = LIVE.load(Ordering::Relaxed);
    PEAK.store(before, Ordering::Relaxed);
    let t2 = Instant::now();
    let checked = fors_check::check_build(&inputs, &out, &mut interner);
    let check_time = t2.elapsed();
    let check_retained = LIVE.load(Ordering::Relaxed) - before;
    let check_peak = PEAK.load(Ordering::Relaxed) - before;
    assert!(
        checked.diagnostics.is_empty(),
        "generated package must check cleanly, got {:?}",
        checked.diagnostics.iter().take(4).collect::<Vec<_>>()
    );

    let total_time = resolve_time + check_time;
    let total_retained = resolve_retained + check_retained;
    let total_peak = resolve_peak.max(resolve_retained + check_peak);
    eprintln!(
        "shape: {}",
        if i0_shape {
            "I0 baseline (no traits/impls/projections)"
        } else {
            "I2 (traits, impls, projections)"
        }
    );
    eprintln!("{modules} modules, {lines} lines, {bytes} bytes");
    eprintln!(
        "{} declarations lowered, {} types interned",
        checked.decls_lowered, checked.types_interned
    );
    eprintln!("index+resolve: {resolve_time:?}");
    eprintln!("signature lowering + wf: {check_time:?}");
    eprintln!(
        "total: {total_time:?}  (+{:.0}% over index+resolve alone)",
        check_time.as_secs_f64() / resolve_time.as_secs_f64() * 100.0
    );
    eprintln!(
        "index+resolve heap: retained {resolve_retained} B ({:.2} B/byte), peak {resolve_peak} B ({:.2} B/byte)",
        resolve_retained as f64 / bytes as f64,
        resolve_peak as f64 / bytes as f64
    );
    eprintln!(
        "checker heap: retained {check_retained} B (+{:.2} B/byte), peak {check_peak} B (+{:.2} B/byte)",
        check_retained as f64 / bytes as f64,
        check_peak as f64 / bytes as f64
    );
    eprintln!(
        "combined: retained {total_retained} B ({:.2} B/byte), peak {total_peak} B ({:.2} B/byte)",
        total_retained as f64 / bytes as f64,
        total_peak as f64 / bytes as f64
    );
}

// ---------------------------------------------------------------- I6 (§13)
//
// The two MEASUREMENTs design §13's I6 paragraph names:
//
// 1. the adversarial-shape counter suite from the I1 spike
//    (`spikes/fir-normalise`), now run THROUGH THE REAL CHECKER: the
//    normalisation counters must be linear in chain depth and independent of
//    `k`, the number of impls in one `(trait, HeadKey)` bucket, beyond the
//    bucket scan itself (§17 amendments 2 and 3);
// 2. the cost of clearing the `TraitWorldRevision` caches on a cold 100k
//    check, against §16 point 3's decision rule ("more than ~2 ms ⇒ promote
//    `holds` to a DAG node keyed `(TyId, TraitRefId)`").
//
// `cargo test --release -p fors-check --test scale -- --ignored --nocapture`

/// The spike's shapes as real Fors: `k` concrete impls of `Iterator` in one
/// `(Iterator, HeadKey(Cell))` bucket (the exact probe's case), and a chain
/// of `depth` generic adaptors above one of them whose `type Item = I.Item`
/// forces `depth` structural descents per query.
fn adaptor_chain_source(depth: usize, k: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "module pkg.chain;");
    for j in 0..k {
        let _ = writeln!(s, "struct Mk{j} {{ z: i64 }}");
    }
    let _ = writeln!(s, "struct Cell[T] {{ t: T, n: i64 }}");
    for j in 0..k {
        let _ = writeln!(s, "impl Iterator for Cell[Mk{j}] {{");
        let _ = writeln!(s, "    type Item = i64;");
        let _ = writeln!(
            s,
            "    fn next(inout self: Cell[Mk{j}]) -> Option[i64] {{ return none; }}"
        );
        let _ = writeln!(s, "}}");
    }
    for a in 0..3 {
        let _ = writeln!(s, "struct Ad{a}[I] {{ inner: I }}");
        let _ = writeln!(s, "impl[I: Iterator] Iterator for Ad{a}[I] {{");
        let _ = writeln!(s, "    type Item = I.Item;");
        let _ = writeln!(
            s,
            "    fn next(inout self: Ad{a}[I]) -> Option[I.Item] {{ return self.inner.next(); }}"
        );
        let _ = writeln!(s, "}}");
    }
    let _ = writeln!(
        s,
        "fn first[I: Iterator](inout it: I) -> Option[I.Item] {{ return it.next(); }}"
    );
    let mut deep = String::from("Cell[Mk0]");
    for d in 0..depth {
        deep = format!("Ad{}[{deep}]", d % 3);
    }
    let _ = writeln!(s, "fn probe(inout it: {deep}) -> i64 {{");
    let _ = writeln!(s, "    let got: Option[i64] = first(&it);");
    let _ = writeln!(s, "    match got {{");
    let _ = writeln!(s, "        some(let v) => v,");
    let _ = writeln!(s, "        none => 0,");
    let _ = writeln!(s, "    }}");
    let _ = writeln!(s, "}}");
    s
}

fn check_one(src: &str) -> fors_check::CheckOutput {
    let p = parse_file(src.as_bytes());
    assert!(
        p.diags.is_empty(),
        "generated source must parse: {:?}",
        p.diags.first()
    );
    let mut interner = Interner::new();
    let name: Segments = vec![interner.intern(b"pkg"), interner.intern(b"chain")];
    let inputs = [FileInput {
        tree: &p.tree,
        tokens: &p.tokens,
        source: src.as_bytes(),
        name,
    }];
    let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
    assert!(
        resolved.files.iter().all(|f| f.diagnostics.is_empty()),
        "generated source must resolve: {:?}",
        resolved.files.iter().flat_map(|f| &f.diagnostics).next()
    );
    fors_check::check_build(&inputs, &resolved, &mut interner)
}

#[test]
#[ignore]
fn i6_normalisation_counters_are_linear_in_depth_and_flat_in_k() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let mut failures: Vec<String> = Vec::new();

    eprintln!("\nTable 1 — adaptor chain, k = 8 impls in the (Iterator, Cell) bucket");
    eprintln!(
        "{:<10}{:>12}{:>14}{:>14}{:>14}{:>14}",
        "depth", "subst_norm", "proj_queries", "memo_misses", "match_steps", "budget_peak"
    );
    let mut depth_rows: Vec<(usize, fors_check::Counters)> = Vec::new();
    for &d in &[1usize, 2, 4, 8, 16, 32, 64] {
        let out = check_one(&adaptor_chain_source(d, 8));
        if !out.diagnostics.is_empty() {
            failures.push(format!(
                "depth {d}: the chain must check clean, got {:?}",
                out.diagnostics.first()
            ));
        }
        let c = out.counters;
        eprintln!(
            "{d:<10}{:>12}{:>14}{:>14}{:>14}{:>14}",
            c.subst_norm_calls,
            c.norm_queries,
            c.norm_memo_misses,
            c.norm_match_steps,
            c.norm_budget_peak
        );
        depth_rows.push((d, c));
    }
    // Linear: doubling the depth may at most roughly double the work. The
    // spike's own gate is x2.6 per doubling; the same number here.
    for w in depth_rows.windows(2) {
        let (d0, c0) = w[0];
        let (d1, c1) = w[1];
        if d1 != 2 * d0 {
            continue;
        }
        for (name, a, b) in [
            ("subst_norm_calls", c0.subst_norm_calls, c1.subst_norm_calls),
            ("norm_queries", c0.norm_queries, c1.norm_queries),
            ("norm_memo_misses", c0.norm_memo_misses, c1.norm_memo_misses),
        ] {
            if a == 0 {
                continue;
            }
            let ratio = b as f64 / a as f64;
            if ratio > 2.6 {
                failures.push(format!(
                    "{name} superlinear from depth {d0} to {d1}: x{ratio:.2}"
                ));
            }
        }
    }

    eprintln!("\nTable 2 — depth 32 chain, k impls in ONE (Iterator, Cell) bucket");
    eprintln!(
        "{:<10}{:>12}{:>14}{:>14}{:>14}",
        "k", "subst_norm", "proj_queries", "memo_misses", "match_steps"
    );
    let mut k_rows: Vec<(usize, fors_check::Counters)> = Vec::new();
    for &k in &[1usize, 8, 64, 256] {
        let out = check_one(&adaptor_chain_source(32, k));
        if !out.diagnostics.is_empty() {
            failures.push(format!(
                "k = {k}: the chain must check clean, got {:?}",
                out.diagnostics.first()
            ));
        }
        let c = out.counters;
        eprintln!(
            "{k:<10}{:>12}{:>14}{:>14}{:>14}",
            c.subst_norm_calls, c.norm_queries, c.norm_memo_misses, c.norm_match_steps
        );
        k_rows.push((k, c));
    }
    // §17 amendment 3: the exact `(trait, self TyId)` probe answers every
    // concrete impl in one binary search, so NOTHING about normalisation
    // moves with the bucket's size — not the queries, not the misses, and
    // not the match steps (which are spent only on genuinely generic heads).
    let base = k_rows[0].1;
    for &(k, c) in &k_rows {
        for (name, a, b) in [
            ("norm_queries", base.norm_queries, c.norm_queries),
            (
                "norm_memo_misses",
                base.norm_memo_misses,
                c.norm_memo_misses,
            ),
            (
                "norm_match_steps",
                base.norm_match_steps,
                c.norm_match_steps,
            ),
        ] {
            if a != b {
                failures.push(format!("k = {k}: {name} moved with k ({a} -> {b})"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "I6 normalisation measurement ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// I6's corpus: `module_source`'s shape with the trait work moved into the
/// BODIES, which is where the two trait-world caches are filled. Every item
/// declares an iterator, a generic adaptor over it whose `type Item =
/// I.Item`, and a body that calls a generic function on a two-deep chain —
/// one member lookup and one projection normalisation per body, which is
/// the traffic a `TraitWorldRevision` bump throws away.
fn module_source_i6(m: usize, items: usize) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "module pkg.m{m};");
    for i in 0..items {
        let _ = writeln!(s, "\npub struct Base{m}_{i} {{ n: i64, end: i64 }}");
        let _ = writeln!(s, "impl Iterator for Base{m}_{i} {{");
        let _ = writeln!(s, "    type Item = i64;");
        let _ = writeln!(s, "    fn next(inout self: Base{m}_{i}) -> Option[i64] {{");
        let _ = writeln!(s, "        if self.n >= self.end {{ return none; }}");
        let _ = writeln!(s, "        self.n = self.n + 1;");
        let _ = writeln!(s, "        return some(self.n);");
        let _ = writeln!(s, "    }}");
        let _ = writeln!(s, "}}");
        let _ = writeln!(s, "pub struct Wrap{m}_{i}[I] {{ inner: I }}");
        let _ = writeln!(s, "impl[I: Iterator] Iterator for Wrap{m}_{i}[I] {{");
        let _ = writeln!(s, "    type Item = I.Item;");
        let _ = writeln!(
            s,
            "    fn next(inout self: Wrap{m}_{i}[I]) -> Option[I.Item] {{ return self.inner.next(); }}"
        );
        let _ = writeln!(s, "}}");
        let _ = writeln!(
            s,
            "pub fn first{m}_{i}[I: Iterator](inout it: I) -> Option[I.Item] {{ return it.next(); }}"
        );
        let _ = writeln!(
            s,
            "pub fn run{m}_{i}(inout w: Wrap{m}_{i}[Wrap{m}_{i}[Base{m}_{i}]]) -> i64 {{"
        );
        let _ = writeln!(s, "    let got: Option[i64] = first{m}_{i}(&w);");
        let _ = writeln!(s, "    match got {{");
        let _ = writeln!(s, "        some(let v) => v,");
        let _ = writeln!(s, "        none => 0,");
        let _ = writeln!(s, "    }}");
        let _ = writeln!(s, "}}");
    }
    s
}

#[test]
#[ignore]
fn i6_trait_world_cache_clearing_is_cheap_on_a_cold_100k_check() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (modules, items) = (250, 20);
    let sources: Vec<String> = (0..modules).map(|m| module_source_i6(m, items)).collect();
    let lines: usize = sources.iter().map(|s| s.lines().count()).sum();
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
    assert!(
        parsed.iter().all(|p| p.diags.is_empty()),
        "generated source must parse"
    );
    let mut interner = Interner::new();
    let names: Vec<Segments> = (0..modules)
        .map(|m| {
            vec![
                interner.intern(b"pkg"),
                interner.intern(format!("m{m}").as_bytes()),
            ]
        })
        .collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(&sources)
        .zip(&names)
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s.as_bytes(),
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
    assert!(
        resolved.files.iter().all(|f| f.diagnostics.is_empty()),
        "generated package must resolve cleanly"
    );
    let out = fors_check::check_build_measuring_caches(&inputs, &resolved, &mut interner);
    assert!(
        out.diagnostics.is_empty(),
        "the I6 corpus must check CLEAN or the rebuild measures skipped bodies, got {:?}",
        out.diagnostics.first()
    );
    let r = out
        .cache_rebuild
        .expect("the measuring entry point fills this in");
    let clear_ms = r.clear_ns as f64 / 1e6;
    let rebuild_ms = r.rebuild_ns as f64 / 1e6;
    let refill_ms = clear_ms + (r.rebuild_ns as f64 - r.warm_rebuild_ns as f64).max(0.0) / 1e6;
    eprintln!(
        "\n100k corpus: {lines} lines, {} bodies\n  \
         method-lookup memo rows: {}\n  \
         normalisation memo rows: {}\n  \
         cold body phase:         {:.3} ms\n  \
         clear both caches:       {clear_ms:.4} ms\n  \
         rebuild (bodies, cold):  {rebuild_ms:.3} ms\n  \
         rebuild (bodies, warm):  {warm_ms:.3} ms\n  \
         CACHE refill only:       {refill_ms:.3} ms   = clear + (cold rebuild - warm rebuild)\n  \
         §16 point 3's rule: > ~2 ms  =>  promote `holds` to a DAG node keyed (TyId, TraitRefId)\n  \
         verdict:                 {verdict}",
        out.counters.bodies_checked,
        r.method_memo_rows,
        r.norm_memo_rows,
        r.cold_bodies_ns as f64 / 1e6,
        warm_ms = r.warm_rebuild_ns as f64 / 1e6,
        refill_ms = refill_ms,
        verdict = if refill_ms > 2.0 {
            "OVER the rule - the fix in §16 point 3 is due"
        } else {
            "within the rule - wholesale clearing stays"
        }
    );
    // The clear itself is what §9.1 calls "wholesale": two `HashMap::clear`s.
    // The decision rule is about clear PLUS rebuild, which is reported above
    // and judged in the increment's write-up; the only thing asserted here is
    // that the measurement ran and the caches were actually populated, so a
    // future refactor that silently stops memoising fails loudly.
    assert!(
        r.norm_memo_rows > 0 && r.method_memo_rows > 0,
        "both trait-world caches must be populated by a 100k check \
         (method {}, normalisation {})",
        r.method_memo_rows,
        r.norm_memo_rows
    );
}

// ============================================================ I9: the M1 exit
//
// `docs/PLAN.md` M1's exit gates (a) and (b), and design §16 point 5's
// disproof, measured through the query DAG (`fors_check::queries`).
//
// Everything here is `#[ignore]`d: these are wall-clock numbers and belong on
// the pinned M1 box, never in cloud CI (design §12). The DETERMINISTIC half of
// gate (b) is `tests/incremental.rs`'s
// `the_reexecution_count_per_edit_class_is_independent_of_corpus_size`, which
// is not ignored.
//
// `cargo test --release -p fors-check --test scale -- --ignored --nocapture`

/// Builds a `QueryBuild` over a generated package.
fn query_build(
    sources: &[String],
) -> (
    fors_check::queries::QueryBuild,
    Vec<fors_index::ids::FileId>,
) {
    let mut qb = fors_check::queries::QueryBuild::new();
    let mut ids = Vec::new();
    for (m, src) in sources.iter().enumerate() {
        let segs: Vec<fors_index::Symbol> = {
            let i = qb.interner_mut();
            vec![i.intern(b"pkg"), i.intern(format!("m{m}").as_bytes())]
        };
        ids.push(qb.add_file(&format!("pkg/m{m}.fors"), segs, src.clone().into_bytes()));
    }
    (qb, ids)
}

fn corpus(modules: usize, items: usize) -> (Vec<String>, usize) {
    let sources: Vec<String> = (0..modules)
        .map(|m| module_source_nongeneric(m, items))
        .collect();
    let lines = sources.iter().map(|s| s.lines().count()).sum();
    (sources, lines)
}

/// M1 exit gate (a): a ~100k-line corpus checks CLEAN, cold, through the DAG.
#[test]
#[ignore]
fn m1_exit_100k_corpus_checks_clean_cold() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (sources, lines) = corpus(250, 20);
    let (mut qb, _) = query_build(&sources);
    let t = Instant::now();
    qb.recheck().expect("never cancelled");
    let wall = t.elapsed();
    let ds = qb.diagnostics();
    let s = qb.stats();
    eprintln!("gate (a): {lines} lines, {:?} cold", wall);
    eprintln!(
        "          {} nodes, {} dependency edges, {} executed",
        s.nodes, s.dep_edges, s.executed
    );
    eprintln!("{}", qb.render_stats());
    assert!(
        ds.is_empty(),
        "the 100k corpus must check clean, got {} diagnostics, first {:?}",
        ds.len(),
        ds.first()
    );
    assert!(lines > 95_000, "the corpus is only {lines} lines");
}

/// M1 exit gate (b), the MEASUREMENT half: the log-log wall slope of a cold
/// check over 12.5k / 25k / 50k / 100k lines (target <= 1.05), the cost of one
/// incremental re-check after a one-line body edit, and the per-declaration
/// cost histogram.
///
/// The machine state is printed with the numbers. Another agent may be running
/// on this box; design §12 puts the wall-clock gate on the pinned M1 box and
/// nowhere else, so treat these as a measurement to be re-taken on a quiet
/// machine, and the counter gate in `tests/incremental.rs` as the CI gate.
#[test]
#[ignore]
fn m1_exit_wall_slope_and_per_declaration_histogram() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    eprintln!(
        "machine: {} logical cpus, release={}",
        std::thread::available_parallelism().map_or(0, |n| n.get()),
        !cfg!(debug_assertions)
    );
    let sizes = [31usize, 62, 125, 250];
    let mut rows: Vec<(usize, f64)> = Vec::new();
    for modules in sizes {
        let (sources, lines) = corpus(modules, 20);
        // Median of three cold builds.
        let mut walls: Vec<f64> = (0..3)
            .map(|_| {
                let (mut qb, _) = query_build(&sources);
                let t = Instant::now();
                qb.recheck().expect("never cancelled");
                let w = t.elapsed().as_secs_f64();
                assert!(
                    qb.diagnostics().is_empty(),
                    "generated corpus must be clean"
                );
                w
            })
            .collect();
        walls.sort_by(f64::total_cmp);
        rows.push((lines, walls[1]));
        eprintln!("cold  {lines:>7} lines  {:>8.1} ms", walls[1] * 1000.0);
    }
    // Least-squares log-log slope.
    let n = rows.len() as f64;
    let xs: Vec<f64> = rows.iter().map(|&(l, _)| (l as f64).ln()).collect();
    let ys: Vec<f64> = rows.iter().map(|&(_, w)| w.ln()).collect();
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let num: f64 = xs.iter().zip(&ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let den: f64 = xs.iter().map(|x| (x - mx) * (x - mx)).sum();
    let slope = num / den;
    eprintln!("gate (b) MEASUREMENT: log-log cold slope = {slope:.4} (target <= 1.05)");

    // The incremental half: one body edit on the 100k corpus, repeated over a
    // sample of declarations, as a histogram.
    let (sources, lines) = corpus(250, 20);
    let (mut qb, ids) = query_build(&sources);
    let t = Instant::now();
    qb.recheck().expect("never cancelled");
    let cold = t.elapsed().as_secs_f64();
    let mut samples: Vec<f64> = Vec::new();
    let mut edited = sources.clone();
    for (k, m) in (0..250usize).step_by(5).enumerate() {
        let needle = format!("pub fn work{m}_0(let x: i32, let sh: Shape{m}_0) -> i32 {{");
        if !edited[m].contains(&needle) {
            continue;
        }
        let with = format!("{needle}\n    let probe{k}: i32 = {k};");
        edited[m] = edited[m].replacen(&needle, &with, 1);
        qb.edit_file(ids[m], edited[m].clone().into_bytes());
        let t = Instant::now();
        qb.recheck().expect("never cancelled");
        samples.push(t.elapsed().as_secs_f64());
        assert!(
            qb.diagnostics().is_empty(),
            "an added `let` must not break the corpus: {:?}",
            qb.diagnostics().first()
        );
    }
    samples.sort_by(f64::total_cmp);
    let pick = |q: f64| samples[((samples.len() - 1) as f64 * q) as usize] * 1000.0;
    eprintln!(
        "per-declaration edit histogram over {} edits of the {lines}-line corpus:",
        samples.len()
    );
    eprintln!("  cold   {:>8.1} ms", cold * 1000.0);
    eprintln!("  p50    {:>8.1} ms", pick(0.50));
    eprintln!("  p95    {:>8.1} ms", pick(0.95));
    eprintln!("  max    {:>8.1} ms", samples[samples.len() - 1] * 1000.0);
    eprintln!(
        "  speedup over cold: p50 x{:.2}, p95 x{:.2}",
        cold / (pick(0.50) / 1000.0),
        cold / (pick(0.95) / 1000.0)
    );

    // What the incremental number is MADE of. The two whole-build passes run
    // on every revision in M1 (design §3 fork 14 for `resolve`; the signature
    // phase because `fors-check` cannot lower one declaration's signature
    // alone), so they are the floor the body-level incrementality sits on.
    // Reporting them separately is what keeps the speedup above from being
    // read as more than it is.
    {
        let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
        let mut interner = Interner::new();
        let names: Vec<Segments> = (0..sources.len())
            .map(|m| {
                vec![
                    interner.intern(b"pkg"),
                    interner.intern(format!("m{m}").as_bytes()),
                ]
            })
            .collect();
        let inputs: Vec<FileInput> = parsed
            .iter()
            .zip(&sources)
            .zip(&names)
            .map(|((p, s), n)| FileInput {
                tree: &p.tree,
                tokens: &p.tokens,
                source: s.as_bytes(),
                name: n.clone(),
            })
            .collect();
        let t = Instant::now();
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        let resolve_ns = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let mut sigs = fors_check::check_signatures(&inputs, &resolved, &mut interner);
        let sig_ns = t.elapsed().as_secs_f64();
        let t = Instant::now();
        let _ = fors_check::check_bodies(&mut sigs, &mut interner, fors_check::Bodies::All, false);
        let bodies_ns = t.elapsed().as_secs_f64();
        eprintln!(
            "  floor: resolve {:>7.1} ms + signature phase {:>7.1} ms = {:>7.1} ms \
             (all bodies would add {:>7.1} ms)",
            resolve_ns * 1000.0,
            sig_ns * 1000.0,
            (resolve_ns + sig_ns) * 1000.0,
            bodies_ns * 1000.0
        );
    }
    eprintln!("{}", qb.render_stats());
    assert!(
        slope <= 1.30,
        "the cold slope is {slope:.4}: far enough past 1.05 that it is a defect, \
         not machine noise"
    );
}

/// Design §16 point 5's disproof: "a 20k-line single file with a one-character
/// body edit shows p95 of `parse + decl_index + decl_keys` above 3 ms, which
/// would eat the M2 frame". Measured here, as §16 assigns it to I9.
#[test]
#[ignore]
fn m1_exit_one_big_file_reparse_cost() {
    let _serial = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    // ~20k lines in ONE module.
    let src = module_source_nongeneric(0, 1_300);
    let lines = src.lines().count();
    let (mut qb, ids) = query_build(std::slice::from_ref(&src));
    qb.recheck().expect("never cancelled");
    assert!(qb.diagnostics().is_empty(), "the big file must check clean");
    let mut samples: Vec<f64> = Vec::new();
    let mut cur = src;
    for k in 0..20 {
        let needle = format!("pub fn work0_{k}(let x: i32, let sh: Shape0_{k}) -> i32 {{");
        if !cur.contains(&needle) {
            continue;
        }
        cur = cur.replacen(
            &needle,
            &format!("{needle}\n    let probe{k}: i32 = {k};"),
            1,
        );
        qb.edit_file(ids[0], cur.clone().into_bytes());
        let t = Instant::now();
        qb.recheck().expect("never cancelled");
        samples.push(t.elapsed().as_secs_f64());
    }
    samples.sort_by(f64::total_cmp);
    let p95 = samples[((samples.len() - 1) as f64 * 0.95) as usize] * 1000.0;
    eprintln!(
        "§16 point 5: {lines} lines in one file, {} one-line body edits",
        samples.len()
    );
    eprintln!(
        "  whole re-check p50 {:>8.2} ms",
        samples[samples.len() / 2] * 1000.0
    );
    eprintln!("  whole re-check p95 {p95:>8.2} ms");

    // §16 point 5 is specifically about `parse + decl_index + decl_keys`,
    // which are the three nodes a one-character body edit forces on a big
    // file. Measured on their own, since the whole re-check above also carries
    // the whole-build `resolve` and signature phase.
    let mut three: Vec<f64> = Vec::new();
    let mut interner = Interner::new();
    let module = vec![interner.intern(b"pkg"), interner.intern(b"m0")];
    for _ in 0..10 {
        let t = Instant::now();
        let p = parse_file(cur.as_bytes());
        let decls = fors_index::build_decl_table(&p.tree, &p.tokens, cur.as_bytes(), &mut interner);
        let _ = fors_check::queries::keys::file_decl_keys(
            &module,
            &decls,
            &p.tree,
            &p.tokens,
            cur.as_bytes(),
            &interner,
        );
        three.push(t.elapsed().as_secs_f64());
    }
    three.sort_by(f64::total_cmp);
    let three_p95 = three[((three.len() - 1) as f64 * 0.95) as usize] * 1000.0;
    eprintln!(
        "  parse + decl_index + decl_keys p50 {:>8.2} ms, p95 {three_p95:>8.2} ms",
        three[three.len() / 2] * 1000.0
    );
    eprintln!(
        "  §16's disproof threshold is 3 ms at 20k lines; this file is {lines} lines, \
         so the scaled threshold is {:.2} ms",
        3.0 * lines as f64 / 20_000.0
    );
    eprintln!("{}", qb.render_stats());
}
