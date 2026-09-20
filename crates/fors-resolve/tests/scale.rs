//! Scale measurement (ignored by default): index + resolve a generated
//! ~100k-line multi-module package, reporting time and heap per source
//! byte. `cargo test --release -p fors-resolve --test scale -- --ignored --nocapture`

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
        // MARC: same pre-existing generator bug — a payload binder is
        // also `"let" ident` (`pattern-let-binding-accepted.fors`), not a
        // bare name.
        let _ = writeln!(s, "        Shape{m}_{i}.line(let len) => len,");
        // MARC: pre-existing generator bug, unrelated to I0 — a bare
        // catch-all pattern segment resolves as a name reference (Rule
        // 25), not a binder; only `"let" ident` binds. Fixed here (not
        // touching tests/conformance/**) so the I0 gate's scale
        // measurement can actually run to completion.
        let _ = writeln!(s, "        let other => total,");
        let _ = writeln!(s, "    }};");
        if m > 0 {
            let _ = writeln!(
                s,
                "    let prev: i32 = m{p}.work{p}_{i}(x, item, Shape{p}_0.dot);",
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

#[test]
#[ignore]
fn scale_100k_lines() {
    let (modules, items) = (250, 20);
    let sources: Vec<String> = (0..modules).map(|m| module_source(m, items)).collect();
    let bytes: usize = sources.iter().map(|s| s.len()).sum();
    let lines: usize = sources.iter().map(|s| s.lines().count()).sum();

    let t0 = Instant::now();
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s.as_bytes())).collect();
    let parse_time = t0.elapsed();
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
    let retained = LIVE.load(Ordering::Relaxed) - before;
    let peak = PEAK.load(Ordering::Relaxed) - before;

    let diags: usize = out.files.iter().map(|f| f.diagnostics.len()).sum();
    let uses: usize = out.files.iter().map(|f| f.name_uses.node.len()).sum();
    if let Some(d) = out.files.iter().flat_map(|f| &f.diagnostics).next() {
        panic!("generated package must resolve cleanly, got {d:?} ({diags} total)");
    }
    eprintln!("{modules} modules, {lines} lines, {bytes} bytes, {uses} name uses");
    eprintln!(
        "parse: {parse_time:?}; index+resolve: {resolve_time:?} ({:.2} M lines/s)",
        lines as f64 / resolve_time.as_secs_f64() / 1e6
    );
    eprintln!(
        "index+resolve heap: retained {retained} B ({:.2} B/source byte), peak {peak} B ({:.2} B/source byte)",
        retained as f64 / bytes as f64,
        peak as f64 / bytes as f64
    );
}
