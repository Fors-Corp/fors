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
        let _ = writeln!(s, "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}");
        let _ = writeln!(s, "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}");
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        let _ = writeln!(s, "pub fn work{m}_{i}[T](let x: i32, let item: T, let sh: Shape{m}_{i}) -> i32 {{");
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
            let _ = writeln!(s, "    let prev: i32 = m{p}.work{p}_{i}(x, item, Shape{p}_0.dot);", p = m - 1);
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
        let _ = writeln!(s, "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}");
        let _ = writeln!(s, "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}");
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        // A trait with an associated type, an impl of it, and a signature
        // that projects on a bound: the shapes I2's lowering actually costs
        // something on (R61's bound search, R17's substitution, R19's bucket).
        let _ = writeln!(s, "pub trait Keyed{m}_{i} {{ type Key: Eq + Ord; fn key(let self) -> Self.Key; }}");
        let _ = writeln!(s, "impl Keyed{m}_{i} for Rec{m}_{i} {{");
        let _ = writeln!(s, "    type Key = i64;");
        let _ = writeln!(s, "    fn key(let self: Rec{m}_{i}) -> i64 {{ return self.b; }}");
        let _ = writeln!(s, "}}");
        let _ = writeln!(s, "pub struct Wrap{m}_{i}[K: Keyed{m}_{i}] {{ inner: K, seen: Option[K.Key] }}");
        let _ = writeln!(s, "pub fn work{m}_{i}[T](let x: i32, let item: T, let sh: Shape{m}_{i}) -> i32 {{");
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
            let _ = writeln!(s, "    let prev: i32 = m{p}.work{p}_{i}(x, item, Shape{p}_0.dot);", p = m - 1);
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
        let _ = writeln!(s, "\npub struct Rec{m}_{i} {{ pub a: i32, pub b: i64, tag: Shape{m}_{i} }}");
        let _ = writeln!(s, "pub enum Shape{m}_{i} {{ dot, line(i32), box {{ w: i32, h: i32 }} }}");
        let _ = writeln!(s, "const LIMIT{m}_{i}: i32 = {i};");
        let _ = writeln!(s, "pub fn work{m}_{i}(let x: i32, let sh: Shape{m}_{i}) -> i32 {{");
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
        let _ = writeln!(s, "    let made: Rec{m}_{i} = Rec{m}_{i} {{ a: 1, b: 2, tag: Shape{m}_{i}.dot }};");
        let _ = writeln!(s, "    let sum: i64 = made.b + 3i64;");
        if m > 0 {
            let _ = writeln!(s, "    let prev: i32 = m{p}.work{p}_{i}(x, m{p}.Shape{p}_{i}.dot);", p = m - 1);
        } else {
            let _ = writeln!(s, "    let prev: i32 = 0;");
        }
        let _ = writeln!(s, "    return picked + prev + total + made.a + (sum as i32);");
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
        let sources: Vec<String> = (0..modules).map(|m| module_source_nongeneric(m, 20)).collect();
        let lines: usize = sources.iter().map(|s| s.lines().count()).sum();
        let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
        assert!(parsed.iter().all(|p| p.diags.is_empty()), "generated source must parse");
        let mut interner = Interner::new();
        let names: Vec<Segments> = (0..modules)
            .map(|m| vec![interner.intern(b"pkg"), interner.intern(format!("m{m}").as_bytes())])
            .collect();
        let inputs: Vec<FileInput> = parsed
            .iter()
            .zip(&sources)
            .zip(&names)
            .map(|((p, s), n)| FileInput { tree: &p.tree, tokens: &p.tokens, source: s.as_bytes(), name: n.clone() })
            .collect();
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        assert!(resolved.files.iter().all(|f| f.diagnostics.is_empty()), "generated package must resolve cleanly");
        let t = Instant::now();
        let out = fors_check::check_build(&inputs, &resolved, &mut interner);
        let wall = t.elapsed().as_secs_f64();
        assert!(
            out.diagnostics.is_empty(),
            "the non-generic corpus must check CLEAN, got {:?}",
            out.diagnostics.iter().take(4).collect::<Vec<_>>()
        );
        assert_eq!(out.counters.bodies_skipped, 0, "no body may be skipped in a clean build");
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
    eprintln!("lines      wall      bodies  {}", names.iter().map(|&(n, _)| format!("{n:>17}")).collect::<String>());
    for (lines, c, wall) in &rows {
        eprintln!(
            "{lines:<10} {:>7.1}ms {:>7}  {}",
            wall * 1000.0,
            c.bodies_checked,
            names.iter().map(|&(_, f)| format!("{:>17.4}", f(c) as f64 / *lines as f64)).collect::<String>()
        );
    }
    let mut bad = Vec::new();
    for (name, f) in names {
        let per: Vec<f64> = rows.iter().map(|(l, c, _)| f(c) as f64 / *l as f64).collect();
        let (lo, hi) = per.iter().fold((f64::MAX, 0.0f64), |(a, b), &x| (a.min(x), b.max(x)));
        if lo > 0.0 && hi / lo > 1.05 {
            bad.push(format!("{name}: per-line {lo:.4}..{hi:.4} (x{:.3})", hi / lo));
        }
    }
    assert!(bad.is_empty(), "counters are not flat across 12.5k-200k lines:\n{}", bad.join("\n"));
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
    let shape = if i0_shape { module_source_i0 } else { module_source };
    let sources: Vec<String> = (0..modules).map(|m| shape(m, items)).collect();
    let bytes: usize = sources.iter().map(|s| s.len()).sum();
    let lines: usize = sources.iter().map(|s| s.lines().count()).sum();

    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
    assert!(parsed.iter().all(|p| p.diags.is_empty()), "generated source must parse");

    let mut interner = Interner::new();
    let names: Vec<Segments> =
        (0..modules).map(|m| vec![interner.intern(b"pkg"), interner.intern(format!("m{m}").as_bytes())]).collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(&sources)
        .zip(&names)
        .map(|((p, s), n)| FileInput { tree: &p.tree, tokens: &p.tokens, source: s.as_bytes(), name: n.clone() })
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
    eprintln!("shape: {}", if i0_shape { "I0 baseline (no traits/impls/projections)" } else { "I2 (traits, impls, projections)" });
    eprintln!("{modules} modules, {lines} lines, {bytes} bytes");
    eprintln!("{} declarations lowered, {} types interned", checked.decls_lowered, checked.types_interned);
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
