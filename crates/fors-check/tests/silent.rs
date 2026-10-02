//! I10b's gate: **no silent `TY_ERROR`** (design §10, "a node that cannot
//! be typed is reported, never absorbed").
//!
//! The sweep walks every `BodyFacts` of two builds — the whole `std/`
//! package, exactly as `fors-lower`'s `std_checks_clean` builds it, and
//! every conformance target the corpus marks `check-ok` or `run-ok` — and
//! asserts that no node the checker TYPED ended `TY_ERROR` inside a body
//! that produced no diagnostic. A body that spoke is exempt: design §10's
//! per-declaration budget stops the walk at the root cause, and the nodes
//! after it are honestly unvisited rather than absorbed.
//!
//! What remains open lives in [`ALLOWED`], one named row per node with the
//! rule, the reason and the owner — never a count, so a row that goes quiet
//! fails here and is deleted instead of left stale.

use std::fs;
use std::path::{Path, PathBuf};

use fors_fir::ty::TY_ERROR;
use fors_index::{Interner, Segments, module::is_legal_segment};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// One absorbed node: `target/module:line:col-line:col NodeKind`.
type Offender = String;

// ------------------------------------------- the reasons a row may carry
//
// Each is a rule, why the node is still absorbed, and who owns the fix. They
// are the ONLY reasons [`ALLOWED`] may cite: a new kind of absorption needs a
// new named constant here, written down before its rows are added.

/// ch10 R17 / ch01 R15: `main`'s `inout heap: mem.Heap` ("the heap's brand
/// is named by `main`'s parameter", ch10 R17, which makes it behave like a
/// `with allocator heap:` header). Signature lowering fills an omitted
/// trailing brand only inside a `with` HEADER (ch01 R15b, `lower::type_args`)
/// and has no brand named by a VALUE parameter at all (the
/// [`R15_BRAND_PARAM`] gap), so `heap`'s own type, and `Own[i64, heap]` /
/// `Vec[i32, heap]`, lower to `TY_ERROR` and every use absorbs. These rows
/// were filed under ch10 R2 until I10c bound the prelude names to std: with
/// `Vec`, `AllocError` and `mem.Heap`'s `Allocator` impl now real, what is
/// left silent is exactly the brand. Owner: ch10 R17's main-heap brand, on
/// top of ch01 R15's brand-by-parameter form.
const R17_MAIN_HEAP: &str = "ch10 R17/ch01 R15: `main`'s `inout heap: mem.Heap` names the heap's \
                             brand by the PARAMETER; lowering fills an omitted brand only in a \
                             `with` header and has no brand-by-parameter, so `heap` and the types \
                             it brands are TY_ERROR and their uses absorb; owner: ch10 R17's \
                             main-heap brand";

/// R43 tier (2) on a RIGID receiver bounded by the PRELUDE trait
/// `Iterator`. `lookup_on_rigid` marks the table incomplete whenever a
/// candidate trait is a prelude one — its rows need not list every method,
/// since `Iterator`'s adaptors live in `std` — and answers
/// `LookupError::Silent`, so `it.count()` / `it.take(2)` on an `I: Iterator`
/// absorbs. Owner: the increment that gives `Iterator` its full prelude
/// surface (the same one `prelude_head_table_incomplete` waits for).
///
/// Re-justified by I10c, with `std` in the build: a user's `I: Iterator`
/// names the LANGUAGE-KNOWN row, and the provided adaptors are declared on
/// `std.mem.seq`'s row of the same trait (ch10 R32: "one trait, not two").
/// I10c identifies the two rows for BOUND satisfaction (`Wf::holds`, so
/// `zip[J: Iterator]` accepts a user's `I`), but not for member lookup or
/// for projections: offering `seq`'s `map` on a rigid `I` would type its
/// `Self.Item` as `seq`'s projection, which is a different neutral type from
/// the user's `I.Item` (`adaptor-chain-rigid-receiver-accepted` would then
/// be a false T0026). That identity is this owner's, not ch10 R2's.
const R43_RIGID_ITERATOR: &str = "R43 tier (2) on a rigid receiver bounded by the prelude trait \
                                  `Iterator`: the prelude's rows do not list the adaptors, so \
                                  `lookup_on_rigid` stays silent; owner: `Iterator`'s prelude \
                                  surface";

/// R45's `Tr.name(..)` / `Tr[args].name(..)`: "that trait's function, with
/// `Self` determined like any parameter by Rule 38". `call.rs::
/// qualified_callee` accepts only a struct or enum head, so a trait head is
/// `Callee::Undecided` and the call absorbs. Owner: R45's trait-head form.
const R45_TRAIT_HEAD: &str = "R45: the qualified form on a TRAIT head, whose `Self` R38 \
                              determines, is not classified; owner: R45's trait-head form";

/// R7/R41: calling a value whose type is a callable PARAMETER (`F: fn(let T)
/// -> U`). `Wf::callable_of` reads a `fn` row off the type and a `Param` has
/// none, so `f(x)` inside the generic body is `Callee::Undecided`. Owner:
/// R41's callable parameters.
const R7_CALLABLE_PARAM: &str = "R7/R41: a call of a value whose type is a callable PARAMETER has \
                                 no `fn` row to read; owner: R41's callable parameters";

/// R43 on a `dyn Tr` receiver: `lookup_method` dispatches on the receiver's
/// tag and `TyTag::Dyn` falls into "anything else has no method table.
/// Silent", although a `dyn Tr`'s method table is exactly `Tr`'s. Owner:
/// R25/R43's dyn dispatch.
const R43_DYN: &str = "R43: a `dyn Tr` receiver has no method table in `lookup_method`, although \
                       it is exactly `Tr`'s; owner: R25/R43's dyn dispatch";

/// R40 / ch01 R15b's brand inference, the gap `call.rs::unbound_slot`
/// documents: a BRAND slot R38 could not determine is answered `is_brand` and
/// left silent on purpose, because R40 binds a brand "only from a receiver or
/// argument type" and `one.alloc(Node { val: 1 })` takes `A` from an expected
/// type step (c) does not have — a T0039 there would be the wrong diagnostic.
/// Re-checked for this increment and still open. Owner: ch01 R15b's brand
/// inference.
const R40_BRAND: &str = "R40/ch01 R15b: a brand slot R38 could not determine is silent by \
                         `unbound_slot`'s own carve-out (a T0039 would be the wrong \
                         diagnostic); owner: ch01 R15b's brand inference";

/// ch01 R15: a brand argument named by a VALUE parameter (`fn f(let a:
/// Arena, let x: Own[i32, a])`). The parameter's declared type does not lower
/// to a type this build has, so every read of it absorbs. Owner: ch01 R15's
/// brand-by-parameter form.
const R15_BRAND_PARAM: &str = "ch01 R15: a brand argument named by a VALUE parameter does not \
                               lower, so the parameter's type is TY_ERROR and reads of it absorb; \
                               owner: ch01 R15's brand-by-parameter form";

/// `expr::subsume`'s qualifier branch, by design: "Same bare type, different
/// qualifiers (`iso`/`imm`/`secret`): the qualifier discipline is ch01/ch05's
/// (I8b/I10's), not a judgement this increment owns. Silent and absorbing,
/// never a guess in either direction." Owner: ch01/ch05's qualifier
/// discipline.
const R11_QUALS: &str = "`subsume`: same bare type, different `iso`/`imm`/`secret` qualifiers is \
                         silent and absorbing by design; owner: ch01/ch05's qualifier discipline";

/// The nodes that are still typed `TY_ERROR` with nothing said, each with the
/// rule it belongs to, why it is open and who owns it. A row here is a
/// PROMISE that the node is still silent: the sweep asserts every row is
/// live, so a fix DELETES its row rather than leaving it stale. There is no
/// count anywhere — the list is the inventory.
///
/// Rows are `(target, module, "line:col-line:col", NodeKind, reason)` — the node's
/// own SPAN, which is what tells the nested calls of one chain apart.
const ALLOWED: &[(&str, &str, &str, &str, &str)] = &[
    (
        "01-ownership/linear-spawn-move-accepted.fors",
        "m",
        "21:22-21:33",
        "CallExpr",
        R11_QUALS,
    ),
    (
        "08-names/param-in-scope-in-later-param-type-accepted.fors",
        "m",
        "9:12-9:13",
        "NameExpr",
        R15_BRAND_PARAM,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "10:14-10:25",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "10:14-10:33",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "11:20-11:31",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "11:20-11:39",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:26",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:34",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:42",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:23",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:31",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:39",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:22",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:30",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:42",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:50",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:12-11:32",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:12-11:40",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:19-11:31",
        "Bracket",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-name-clash-qualified-accepted.fors",
        "m",
        "9:12-9:37",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/adaptor-name-clash-qualified-accepted.fors",
        "m",
        "9:12-9:45",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/brand-inferred-for-callee-accepted.fors",
        "m",
        "12:38-12:64",
        "CallExpr",
        R40_BRAND,
    ),
    (
        "09-types/brand-inferred-for-callee-accepted.fors",
        "m",
        "12:48-12:63",
        "StructLit",
        R40_BRAND,
    ),
    (
        "09-types/callable-bound-closure-accepted.fors",
        "m",
        "8:69-8:73",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/concrete-to-dyn-accepted.fors",
        "m",
        "11:43-11:51",
        "CallExpr",
        R43_DYN,
    ),
    (
        "09-types/consumer-count-drops-items-accepted.fors",
        "m",
        "11:12-11:22",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/dyn-param-in-generic-body-accepted.fors",
        "m",
        "10:36-10:42",
        "CallExpr",
        R43_DYN,
    ),
    (
        "09-types/generic-raises-type-accepted.fors",
        "m",
        "8:94-8:98",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/generic-raises-type-accepted.fors",
        "m",
        "8:94-8:99",
        "TryExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/map-sum-closure-checked-accepted.fors",
        "m",
        "19:31-19:40",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/qualified-trait-call-accepted.fors",
        "m",
        "10:53-10:64",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/qualified-trait-call-accepted.fors",
        "m",
        "10:67-10:81",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "11:29-11:38",
        "CallExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "12:11-12:26",
        "CallExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "12:21-12:25",
        "NameExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:13-13:17",
        "NameExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:5-13:21",
        "CallExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:5-13:22",
        "TryExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "11:29-11:43",
        "CallExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "11:29-11:44",
        "TryExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:17-12:23",
        "UnaryExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:22-12:23",
        "NameExpr",
        R17_MAIN_HEAP,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:5-12:24",
        "CallExpr",
        R17_MAIN_HEAP,
    ),
];

/// Byte offset to `line:col`, both 1-based, counting bytes in the column
/// (the corpus is ASCII, and a byte column is what every other harness in
/// this repo prints).
fn line_col(src: &[u8], at: u32) -> (usize, usize) {
    let at = (at as usize).min(src.len());
    let mut line = 1usize;
    let mut bol = 0usize;
    for (i, &b) in src[..at].iter().enumerate() {
        if b == b'\n' {
            line += 1;
            bol = i + 1;
        }
    }
    (line, at - bol + 1)
}

/// Resolves, checks, and reports every node that ended [`TY_ERROR`] inside a
/// body whose declaration produced no diagnostic.
fn sweep(
    build: &str,
    names: Vec<Segments>,
    sources: Vec<Vec<u8>>,
    root: Option<usize>,
    package: Option<&[u8]>,
    interner: &mut Interner,
) -> Vec<Offender> {
    let module_names: Vec<String> = names
        .iter()
        .map(|n| {
            n.iter()
                .map(|s| String::from_utf8_lossy(interner.resolve(*s)).into_owned())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect();
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve_in_package(interner, &inputs, root, package);
    let out = fors_check::check_build(&inputs, &resolved, interner);
    let Some(defs) = out.defs.as_ref() else {
        return Vec::new();
    };
    let mut offenders = Vec::new();
    for (def, facts) in &out.facts {
        let Some(row) = defs.get(*def) else { continue };
        let fi = row.file.index();
        if fi >= inputs.len() {
            continue;
        }
        let tree = inputs[fi].tree;
        let tokens = inputs[fi].tokens;
        let src = inputs[fi].source;
        let (start, end) = facts.range();
        if start as usize >= tree.len() {
            continue;
        }
        // The declaration's byte span, for attributing a diagnostic to this
        // body: §10's budget is per DECLARATION, so a signature-level
        // diagnostic exempts its body too.
        let (t0, t1) = tree.token_range(start as usize);
        let last = tokens.starts.len().saturating_sub(1);
        let b0 = tokens.starts.get(t0 as usize).copied().unwrap_or(0);
        let b1 = tokens
            .starts
            .get((t1 as usize).min(last))
            .copied()
            .unwrap_or(u32::MAX);
        let spoke = out
            .diagnostics
            .iter()
            .any(|d| d.file == row.file && d.start >= b0 && d.start <= b1);
        if spoke {
            continue;
        }
        for n in start..end.min(tree.len() as u32) {
            if facts.ty_of(n) != TY_ERROR {
                continue;
            }
            // The node's first and last REAL tokens: a node's token range
            // opens on the trivia before it, which would print the previous
            // line's end — and the SPAN is what tells the nested calls of
            // `v.iter().map(d).count()` apart, since they all start at the
            // same column.
            let (t_a, t_b) = tree.token_range(n as usize);
            let hi = (t_b as usize).min(tokens.kinds.len());
            let real: Vec<usize> = (t_a as usize..hi)
                .filter(|&i| !tokens.kinds[i].is_trivia())
                .collect();
            let first = real.first().copied().unwrap_or(t_a as usize);
            let last = real.last().copied().unwrap_or(first);
            let at = tokens.starts.get(first).copied().unwrap_or(0);
            let to = tokens
                .starts
                .get(last + 1)
                .copied()
                .unwrap_or_else(|| tokens.starts.get(last).copied().unwrap_or(0));
            let (line, col) = line_col(src, at);
            let (eline, ecol) = line_col(src, to);
            offenders.push(format!(
                "{build}/{}:{line}:{col}-{eline}:{ecol} {:?}",
                module_names[fi], tree.kinds[n as usize]
            ));
        }
    }
    offenders.sort();
    offenders
}

// --------------------------------------------------------------- the builds

/// Every `std/*.fors` module under the name ch08 R17's synthetic table gives
/// it — the same 15 files, in the same order, as `fors-lower`'s
/// `std_checks_clean`.
fn std_module_sources() -> Vec<(Vec<Vec<u8>>, Vec<u8>)> {
    let root = repo_root().join("std");
    let files: &[(&str, &[&str])] = &[
        ("io.fors", &["std", "io"]),
        ("mem.fors", &["std", "mem"]),
        ("mem/alloc.fors", &["std", "mem", "alloc"]),
        ("mem/vec.fors", &["std", "mem", "vec"]),
        ("mem/seq.fors", &["std", "mem", "seq"]),
        ("mem/text.fors", &["std", "mem", "text"]),
        ("mem/hashmap.fors", &["std", "mem", "hashmap"]),
        ("fs.fors", &["std", "fs"]),
        ("net.fors", &["std", "net"]),
        ("proc.fors", &["std", "proc"]),
        ("rand.fors", &["std", "rand"]),
        ("time.fors", &["std", "time"]),
        ("env.fors", &["std", "env"]),
        ("ffi.fors", &["std", "ffi"]),
        ("gpu.fors", &["std", "gpu"]),
    ];
    files
        .iter()
        .map(|(rel, segs)| {
            let src = fs::read(root.join(rel)).expect("std module reads");
            let segs: Vec<Vec<u8>> = segs.iter().map(|s| s.as_bytes().to_vec()).collect();
            (segs, src)
        })
        .collect()
}

fn std_offenders() -> Vec<Offender> {
    let mut interner = Interner::new();
    let mut names: Vec<Segments> = Vec::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    for (segs, s) in std_module_sources() {
        names.push(
            segs.iter()
                .map(|b| interner.intern(b))
                .collect::<Segments>(),
        );
        sources.push(s);
    }
    sweep("std", names, sources, None, None, &mut interner)
}

/// The `expect:` directive of a corpus target (`main.fors` for a directory).
fn expect_of(target: &Path) -> String {
    let src = if target.is_dir() {
        fs::read_to_string(target.join("main.fors")).unwrap_or_default()
    } else {
        fs::read_to_string(target).unwrap_or_default()
    };
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        if let Some(v) = rest.trim().strip_prefix("expect:") {
            return v.split("--").next().unwrap_or(v).trim().to_string();
        }
    }
    String::new()
}

fn header_name(source: &[u8], interner: &mut Interner) -> Option<Segments> {
    let p = parse_file(source);
    if p.tree.is_empty() {
        return None;
    }
    let child = p.tree.children(0).next()?;
    if p.tree.kinds[child] != fors_syntax::NodeKind::ModuleHdr {
        return None;
    }
    let path_node = p.tree.children(child).next()?;
    let (first, end) = p.tree.token_range(path_node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if p.tokens.kinds[i] == fors_lex::TokenKind::Ident {
            out.push(interner.intern(p.tokens.text(i, source)));
        }
    }
    (!out.is_empty()).then_some(out)
}

/// Every chapter's targets: a `.fors` file or a multi-file directory.
fn corpus_targets() -> Vec<PathBuf> {
    let root = repo_root().join("tests/conformance");
    let mut chapters: Vec<PathBuf> = fs::read_dir(&root)
        .expect("the conformance corpus is present")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    chapters.sort();
    let mut out = Vec::new();
    for ch in chapters {
        let mut entries: Vec<PathBuf> = fs::read_dir(&ch)
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .collect();
        entries.sort();
        for p in entries {
            if p.is_dir() || p.extension().is_some_and(|e| e == "fors") {
                out.push(p);
            }
        }
    }
    out
}

/// One corpus target as a build: its own files first (module names from the
/// directory layout, or the header / file stem for a single file), then
/// every `std/` module, exactly as `fors-lower`'s `build_and_run_with_std`
/// does it. Without `std` there is no `impl Str`, no `impl Slice` and no
/// `seq`, so the documented carve-outs (`prim_table_incomplete`,
/// `prelude_head_table_incomplete`) make silence the CORRECT answer for a
/// hundred more nodes and the sweep would be measuring the missing sources
/// rather than the judgement. Returns `(names, sources, root, own)`, where
/// `own` is how many of the files are the target's.
fn corpus_build(
    target: &Path,
    interner: &mut Interner,
) -> (Vec<Segments>, Vec<Vec<u8>>, Option<usize>, usize) {
    let mut names: Vec<Segments> = Vec::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    let mut root = None;
    if target.is_dir() {
        let mut paths = Vec::new();
        walk(target, &mut paths);
        for p in &paths {
            let src = fs::read(p).unwrap();
            let rel = p.strip_prefix(target).unwrap_or(p);
            let comps: Vec<_> = rel.components().collect();
            let mut segs = Vec::new();
            for (i, c) in comps.iter().enumerate() {
                let os = c.as_os_str().to_string_lossy();
                let seg = if i + 1 == comps.len() {
                    os.strip_suffix(".fors").unwrap_or(&os).to_string()
                } else {
                    os.to_string()
                };
                segs.push(interner.intern(seg.as_bytes()));
            }
            if comps.len() == 1 && rel.file_stem().is_some_and(|s| s == "main") {
                root = Some(sources.len());
            }
            names.push(segs);
            sources.push(src);
        }
    } else {
        let src = fs::read(target).unwrap();
        let name = header_name(&src, interner).unwrap_or_else(|| {
            let stem = target.file_stem().unwrap().to_string_lossy().into_owned();
            let stem = if is_legal_segment(stem.as_bytes()) {
                stem
            } else {
                "m".to_string()
            };
            vec![interner.intern(stem.as_bytes())]
        });
        names.push(name);
        sources.push(src);
        root = Some(0);
    }
    let own = sources.len();
    for (segs, s) in std_module_sources() {
        names.push(
            segs.iter()
                .map(|b| interner.intern(b))
                .collect::<Segments>(),
        );
        sources.push(s);
    }
    (names, sources, Some(root.unwrap_or(0)), own)
}

fn label_of(target: &Path) -> String {
    target
        .strip_prefix(repo_root().join("tests/conformance"))
        .unwrap_or(target)
        .to_string_lossy()
        .into_owned()
}

fn corpus_offenders() -> (usize, Vec<Offender>) {
    let mut targets = 0usize;
    let mut offenders = Vec::new();
    for target in corpus_targets() {
        let expect = expect_of(&target);
        if expect != "check-ok" && expect != "run-ok" {
            continue;
        }
        targets += 1;
        let mut interner = Interner::new();
        let (names, sources, root, _) = corpus_build(&target, &mut interner);
        offenders.extend(
            sweep(
                &label_of(&target),
                names,
                sources,
                root,
                None,
                &mut interner,
            )
            .into_iter()
            // `std`'s own bodies are swept once, by `std_offenders`.
            .filter(|l| !l.contains("/std."))
            .collect::<Vec<_>>(),
        );
    }
    offenders.sort();
    (targets, offenders)
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().is_some_and(|e| e == "fors") {
            out.push(p);
        }
    }
}

// ---------------------------------------------------------------- the gate

/// Whether an offender line is one [`ALLOWED`] names, by target, module,
/// position AND node kind: a different node at the same place is a new
/// absorption and fails.
fn allowed(line: &str) -> Option<usize> {
    ALLOWED
        .iter()
        .position(|&(target, module, at, kind, _)| line == format!("{target}/{module}:{at} {kind}"))
}

#[test]
fn no_silent_ty_error_anywhere() {
    let mut offenders = std_offenders();
    let (targets, corpus) = corpus_offenders();
    assert!(
        targets >= 200,
        "only {targets} check-ok/run-ok corpus targets: the sweep found nothing to sweep"
    );
    offenders.extend(corpus);
    let mut hit = vec![false; ALLOWED.len()];
    let mut unexplained = Vec::new();
    for line in &offenders {
        match allowed(line) {
            Some(i) => hit[i] = true,
            None => unexplained.push(line.clone()),
        }
    }
    assert!(
        unexplained.is_empty(),
        "{} node(s) were typed TY_ERROR with nothing said (design §10: a node that cannot be \
         typed is REPORTED, never absorbed). Fix the judgement, or add a named row to \
         `ALLOWED` with its rule, reason and owner:\n{}",
        unexplained.len(),
        unexplained.join("\n")
    );
    // Every stale row at once, so one fix that retires a family of rows is
    // one edit, not one rerun per row.
    let stale: Vec<String> = ALLOWED
        .iter()
        .zip(&hit)
        .filter(|&(_, &h)| !h)
        .map(|(&(target, module, at, kind, _), _)| format!("{target}/{module}:{at} {kind}"))
        .collect();
    assert!(
        stale.is_empty(),
        "{} ALLOWED row(s) are no longer silent: DELETE them instead of leaving them stale:\n{}",
        stale.len(),
        stale.join("\n")
    );
}

// ------------------------------------- I10c: std-touching files, for real

/// ch10 R2's eight prelude names: the std types and traits a program names
/// with no `use`.
const R2_NAMES: [&str; 8] = [
    "Allocator",
    "AllocError",
    "PageAllocator",
    "Buffer",
    "Vec",
    "Map",
    "String",
    "Utf8Error",
];

/// Whether `word` occurs in `src` as a whole identifier.
fn mentions_word(src: &str, word: &str) -> bool {
    let is_ident = |c: u8| c.is_ascii_alphanumeric() || c == b'_';
    let b = src.as_bytes();
    src.match_indices(word).any(|(i, _)| {
        let before = i == 0 || !is_ident(b[i - 1]);
        let j = i + word.len();
        let after = j >= b.len() || !is_ident(b[j]);
        before && after
    })
}

/// A target "touches std" when one of its own files names one of ch10 R2's
/// prelude names or calls `.iter()` (std's `Slice`/`Vec`/`Buffer` iterator
/// and the `Iterator` adaptors chained on it), or it is a `09-types`
/// `adaptor-*` file (the ch09 corpus of `Iterator`'s provided methods).
fn touches_std(label: &str, own_sources: &[Vec<u8>]) -> bool {
    label.starts_with("09-types/adaptor-")
        || own_sources.iter().any(|s| {
            let s = String::from_utf8_lossy(s);
            s.contains(".iter()") || R2_NAMES.iter().any(|w| mentions_word(&s, w))
        })
}

/// std-touching `check-ok`/`run-ok` targets on which the checker speaks with
/// `std` in the build, each a conflict that predates I10c (it spoke the same
/// before the prelude binding) between a test written against ch08 R17's
/// signature-only `std` table and the real `std` sources. Listed with the
/// clause rather than silenced; a row that goes quiet fails and is deleted.
const STD_SURFACE_CONFLICTS: &[(&str, &str)] = &[(
    "08-names/use-std-mem-accepted.fors",
    "ch08 R17 resolver-view test: `fn f(inout a: mem.Allocator)` uses std's `Allocator`, a TRAIT, as a \
     parameter type, which ch09 R11 rejects (T0011) once `std.mem.alloc`'s real declaration is in the \
     build; ch08 only asserts that the member access is deferred",
)];

/// std-touching `check-ok`/`run-ok` targets with NO node typed against a std
/// declaration, each for a named reason; the test asserts each row is still
/// true, so a fix deletes it.
const NO_STD_TYPED_NODE: &[(&str, &str)] = &[
    (
        "01-ownership/linear-with-block-defer-accepted.fors",
        "names `PageAllocator` only in a `with allocator a:` header whose binding the body never uses, so \
         no expression has a std type (the header itself lowers to `PageAllocator[<fresh>]` since I10c's \
         R15b fix)",
    ),
    (
        "02-failure/error-exit-through-nested-blocks.fors",
        "same shape as the row above: an unused `with allocator a: PageAllocator` binding",
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-name-clash-qualified-accepted.fors",
        R43_RIGID_ITERATOR,
    ),
    ("10-std/main-heap-parameter-accepted.fors", R17_MAIN_HEAP),
];

/// I10c's "for a REAL reason": every `check-ok`/`run-ok` corpus target that
/// touches std (see [`touches_std`]), built WITH `std`, (1) draws no
/// diagnostic in its own files, and (2) has at least one node in its own
/// bodies the checker typed against a `std` DECLARATION — a nominal type
/// whose head is declared in a `std/` file, or a call resolved to one. (2)
/// is what the prelude binding changed: before it, `Vec[i32, A]` was
/// `TY_ERROR` and such a file passed `check-ok` vacuously, by §7.10's
/// absorption. That nothing in these bodies is still silently `TY_ERROR`
/// is [`no_silent_ty_error_anywhere`]'s aggregate assertion (its
/// [`ALLOWED`] rows are the named exceptions).
#[test]
fn std_touching_corpus_is_typed_against_std() {
    use fors_check::facts::{FactCallee, MemberTarget};
    use fors_fir::ty::TyTag;
    use fors_index::ids::DefId;

    let mut checked = 0usize;
    let mut failures = Vec::new();
    let mut conflict_hit = vec![false; STD_SURFACE_CONFLICTS.len()];
    let mut vacuous_hit = vec![false; NO_STD_TYPED_NODE.len()];
    for target in corpus_targets() {
        let expect = expect_of(&target);
        if expect != "check-ok" && expect != "run-ok" {
            continue;
        }
        let label = label_of(&target);
        let mut interner = Interner::new();
        let (names, sources, root, own) = corpus_build(&target, &mut interner);
        if !touches_std(&label, &sources[..own]) {
            continue;
        }
        checked += 1;
        let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
        let inputs: Vec<FileInput> = parsed
            .iter()
            .zip(sources.iter())
            .zip(names.iter())
            .map(|((p, s), n)| FileInput {
                tree: &p.tree,
                tokens: &p.tokens,
                source: s,
                name: n.clone(),
            })
            .collect();
        let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, root, None);
        let out = fors_check::check_build(&inputs, &resolved, &mut interner);
        let own_diags: Vec<String> = out
            .diagnostics
            .iter()
            .filter(|d| d.file.index() < own)
            .map(|d| format!("{} {}", d.code.as_string(), d.message))
            .collect();
        match STD_SURFACE_CONFLICTS.iter().position(|&(n, _)| n == label) {
            Some(i) => {
                conflict_hit[i] = !own_diags.is_empty();
                continue;
            }
            None if !own_diags.is_empty() => {
                failures.push(format!(
                    "{label}: the checker spoke with std in the build: {own_diags:?}"
                ));
                continue;
            }
            None => {}
        }
        let Some(defs) = out.defs.as_ref() else {
            failures.push(format!("{label}: no definition table"));
            continue;
        };
        let in_std = |d: DefId| defs.get(d).is_some_and(|r| r.file.index() >= own);
        let mut typed = 0usize;
        for (def, facts) in &out.facts {
            if !defs.get(*def).is_some_and(|r| r.file.index() < own) {
                continue;
            }
            let (start, end) = facts.range();
            for n in start..end {
                let t = facts.ty_of(n);
                if t != TY_ERROR && t != fors_fir::ty::NO_TY {
                    let bare = out.fir.tys.unqual(t);
                    if out.fir.tys.tag(bare) == TyTag::Nominal && in_std(DefId(out.fir.tys.a(bare)))
                    {
                        typed += 1;
                        continue;
                    }
                }
                match facts.callee_of(n) {
                    FactCallee::Direct(d) | FactCallee::Method { def: d, .. } if in_std(d) => {
                        typed += 1;
                        continue;
                    }
                    _ => {}
                }
                // `b.len` on a `b: Buffer[u8, 16]` is ONE path node whose
                // type is `usize`: the std declaration it was typed against
                // is the field's head.
                match facts.member_of(n) {
                    MemberTarget::Field { head: d, .. } | MemberTarget::IndexImpl { at: d, .. }
                        if in_std(d) =>
                    {
                        typed += 1
                    }
                    _ => {}
                }
            }
        }
        match NO_STD_TYPED_NODE.iter().position(|&(n, _)| n == label) {
            Some(i) => {
                vacuous_hit[i] = true;
                if typed > 0 {
                    failures.push(format!(
                        "{label}: listed in NO_STD_TYPED_NODE but {typed} node(s) are now typed \
                         against std: delete the row"
                    ));
                }
            }
            None if typed == 0 => failures.push(format!(
                "{label}: no node of its bodies is typed against a std declaration, so it passes \
                 vacuously"
            )),
            None => {}
        }
    }
    for (i, &(n, _)) in NO_STD_TYPED_NODE.iter().enumerate() {
        if !vacuous_hit[i] {
            failures.push(format!(
                "{n}: listed in NO_STD_TYPED_NODE but no longer a std-touching check-ok target"
            ));
        }
    }
    assert!(
        checked >= 45,
        "only {checked} std-touching check-ok/run-ok targets: the filter found nothing to check"
    );
    for (i, &(n, _)) in STD_SURFACE_CONFLICTS.iter().enumerate() {
        if !conflict_hit[i] {
            failures.push(format!(
                "{n}: listed in STD_SURFACE_CONFLICTS but the checker is silent on it now: delete the row"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} std-touching target(s) do not check against std for a real reason:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
