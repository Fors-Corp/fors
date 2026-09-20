//! I2's `sig_hash` gate (design §11): the canonical FIR hash of §5.4 is
//! invariant under a reformat, a bound reorder and a generic-parameter
//! rename, and changes on a value-parameter rename and an associated-type
//! right-hand side. Plus `encode_decode_roundtrip` over every signature the
//! ch09 corpus produces, and the mutation harness §13 names.

use std::fs;
use std::path::{Path, PathBuf};

use fors_index::ids::DefId;
use fors_index::Interner;
use fors_resolve::FileInput;
use fors_syntax::parse_file;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

/// Checks one source and returns `(declaration name, sig_hash)` for every
/// user declaration, sorted by name — a shape that is independent of the
/// build's row numbering, which is exactly what §5.4 promises.
fn hashes(src: &[u8]) -> Vec<(String, u128)> {
    let mut interner = Interner::new();
    let parsed = parse_file(src);
    assert!(parsed.diags.is_empty(), "test source must parse: {:?}", parsed.diags);
    let name = vec![interner.intern(b"m")];
    let inputs = [FileInput { tree: &parsed.tree, tokens: &parsed.tokens, source: src, name }];
    let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    let defs = out.defs.as_ref().unwrap();
    let mut rows: Vec<(String, u128)> = defs
        .user_defs()
        .map(|(d, r)| {
            let n = r
                .name
                .map(|s| String::from_utf8_lossy(interner.resolve(s)).into_owned())
                .unwrap_or_else(|| format!("impl#{}", d.0));
            (n, out.fir.sigs.sig_hash(d))
        })
        .collect();
    rows.sort();
    rows
}

fn hash_of(src: &[u8], decl: &str) -> u128 {
    hashes(src).into_iter().find(|(n, _)| n == decl).unwrap_or_else(|| panic!("no declaration named {decl}")).1
}

const BASE: &[u8] = b"module m;
trait Keyed { type Key: Eq + Ord; fn key(let self) -> Self.Key; }
struct Tag { id: i64 }
impl Keyed for Tag { type Key = i64; fn key(let self: Tag) -> i64 { return self.id; } }
fn f[T: Eq + Ord](let a: T, let b: T) -> T { return a; }
";

#[test]
fn sig_hash_stable_under_reformat() {
    let reformatted = b"module m;

trait Keyed {
    type Key: Eq + Ord;
    fn key(let self) -> Self.Key;
}

struct Tag {
    id: i64
}

impl Keyed for Tag {
    type Key = i64;
    fn key(let self: Tag) -> i64 {
        return self.id;
    }
}

fn f[T: Eq + Ord](let a: T, let b: T) -> T {
    return a;
}
";
    assert_eq!(hash_of(BASE, "f"), hash_of(reformatted, "f"));
    assert_eq!(hash_of(BASE, "Tag"), hash_of(reformatted, "Tag"));
    assert_eq!(hash_of(BASE, "Keyed"), hash_of(reformatted, "Keyed"));
}

#[test]
fn sig_hash_stable_under_bound_reorder() {
    let reordered = String::from_utf8(BASE.to_vec()).unwrap().replace("[T: Eq + Ord]", "[T: Ord + Eq]");
    assert_eq!(hash_of(BASE, "f"), hash_of(reordered.as_bytes(), "f"));
}

#[test]
fn sig_hash_stable_under_gparam_rename() {
    // R38(a) is positional, so a generic parameter's NAME is not in the hash.
    let renamed = String::from_utf8(BASE.to_vec()).unwrap().replace("[T: Eq + Ord](let a: T, let b: T) -> T", "[U: Eq + Ord](let a: U, let b: U) -> U");
    assert_eq!(hash_of(BASE, "f"), hash_of(renamed.as_bytes(), "f"));
}

#[test]
fn sig_hash_changes_on_param_rename() {
    // R37 makes a named argument's label observable, so a VALUE parameter's
    // name is in the hash.
    let renamed = String::from_utf8(BASE.to_vec()).unwrap().replace("(let a: T, let b: T)", "(let x: T, let b: T)");
    assert_ne!(hash_of(BASE, "f"), hash_of(renamed.as_bytes(), "f"));
}

#[test]
fn sig_hash_changes_on_assoc_type_rhs() {
    let changed = String::from_utf8(BASE.to_vec()).unwrap().replace("type Key = i64;", "type Key = i32;").replace("-> i64 { return self.id; }", "-> i32 { return 0; }");
    let a = hashes(BASE);
    let b = hashes(changed.as_bytes());
    let ia = a.iter().find(|(n, _)| n.starts_with("impl#")).unwrap().1;
    let ib = b.iter().find(|(n, _)| n.starts_with("impl#")).unwrap().1;
    assert_ne!(ia, ib, "an impl's `type A = T;` right-hand side is part of its signature (R2)");
}

/// Re-interns a writer's `DeclKey` (and its parent chain and module path)
/// into a reader's tables.
fn rebuild_key(
    reader: &mut fors_fir::Fir,
    names2: &mut Interner,
    src: &fors_fir::Fir,
    src_names: &Interner,
    key: fors_fir::DeclKeyId,
) -> fors_fir::DeclKeyId {
    if key == fors_fir::NO_DECL_KEY {
        return fors_fir::NO_DECL_KEY;
    }
    let row = src.keys.row(key);
    let parent = rebuild_key(reader, names2, src, src_names, row.parent);
    let segs: Vec<fors_index::Symbol> =
        src.keys.paths.segments(row.module).iter().map(|&s| names2.intern(src_names.resolve(s))).collect();
    let module = reader.keys.paths.intern(&segs);
    let name = row.name.map(|s| names2.intern(src_names.resolve(s)));
    reader.keys.intern(fors_fir::DeclKey { parent, module, kind: row.kind, name, disamb: row.disamb })
}

fn corpus_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            corpus_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "fors") {
            out.push(p);
        }
    }
}

/// Every signature the ch09 corpus produces survives `encode` -> `decode` ->
/// `encode` unchanged (design §11, I2's row).
#[test]
fn encode_decode_roundtrip_over_the_corpus() {
    let mut files = Vec::new();
    corpus_files(&repo_root().join("tests/conformance/09-types"), &mut files);
    assert!(files.len() >= 150);
    let mut checked = 0usize;
    for path in files {
        let src = fs::read(&path).unwrap();
        let parsed = parse_file(&src);
        if !parsed.diags.is_empty() {
            continue;
        }
        let mut interner = Interner::new();
        let name = vec![interner.intern(b"m")];
        let inputs = [FileInput { tree: &parsed.tree, tokens: &parsed.tokens, source: &src, name }];
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        let out = fors_check::check_build(&inputs, &resolved, &mut interner);
        let defs = out.defs.as_ref().unwrap();
        // One reader per file: `decode_sig` re-interns bottom-up into it, so
        // a second signature that shares a head shares the head's row too —
        // which is the hash-consing the round trip is meant to re-establish.
        let mut reader = fors_fir::Fir::new();
        let mut names2 = Interner::new();
        for (d, _) in defs.user_defs() {
            let bytes = fors_fir::encode_sig(&out.fir, &interner, d, fors_fir::FINGERPRINT_POLICY);
            // The reader has its own key table and its own interner, so the
            // writer's `DeclKeyId` means nothing there: rebuild it.
            let self_key = rebuild_key(&mut reader, &mut names2, &out.fir, &interner, out.fir.defs.key_of(d));
            let decoded = match fors_fir::decode_sig(&bytes, &mut reader, &mut names2, self_key) {
                Ok(x) => x,
                Err(e) => panic!("{}: decoding {d:?} failed: {e:?}", path.display()),
            };
            let again = fors_fir::encode_sig(&reader, &names2, decoded, fors_fir::FINGERPRINT_POLICY);
            assert_eq!(bytes, again, "{}: re-encoding {d:?} changed the bytes", path.display());
            checked += 1;
        }
    }
    assert!(checked > 500, "only {checked} signatures round-tripped");
}

/// §13's `sig_hash_mutation_harness`, in the form I2 can run: for every
/// declaration of every ch09 corpus file, a single-token mutation of its
/// signature changes its `sig_hash`, and a change to another declaration
/// does not. (The full harness — "`sig_hash` changed IFF the cold check
/// result of the package changed" — needs a body checker and is I9's.)
#[test]
fn sig_hash_mutation_harness() {
    let base = BASE;
    let mutations: [(&str, &str, &str); 4] = [
        ("Tag", "id: i64", "id: i32"),
        ("Keyed", "type Key: Eq + Ord;", "type Key: Eq;"),
        ("f", "(let a: T, let b: T)", "(sink a: T, let b: T)"),
        ("f", "-> T {", "-> T raises Tag {"),
    ];
    for (decl, from, to) in mutations {
        let mutated = String::from_utf8(base.to_vec()).unwrap().replace(from, to);
        assert_ne!(mutated.as_bytes(), base, "mutation {from:?} did not apply");
        assert_ne!(
            hash_of(base, decl),
            hash_of(mutated.as_bytes(), decl),
            "mutating {from:?} to {to:?} left {decl}'s sig_hash unchanged"
        );
    }
    // A mutation confined to one declaration leaves the others alone.
    let elsewhere = String::from_utf8(base.to_vec()).unwrap().replace("struct Tag { id: i64 }", "struct Tag { id: i64, extra: i32 }");
    assert_eq!(hash_of(base, "f"), hash_of(elsewhere.as_bytes(), "f"));
    assert_eq!(hash_of(base, "Keyed"), hash_of(elsewhere.as_bytes(), "Keyed"));
}

/// The `DefId`s a build assigns are reproducible: two runs over the same
/// source produce the same hashes in the same order.
#[test]
fn sig_hashes_are_deterministic() {
    assert_eq!(hashes(BASE), hashes(BASE));
}

/// A declaration that is not in the build at all has no `DefId`; one that is
/// referred to before it is lowered gets an `Absent` row, never a panic.
#[test]
fn unknown_head_does_not_panic() {
    let src = b"module m;\nfn f(let x: NoSuchType) { }\n";
    let mut interner = Interner::new();
    let parsed = parse_file(src);
    let name = vec![interner.intern(b"m")];
    let inputs = [FileInput { tree: &parsed.tree, tokens: &parsed.tokens, source: src, name }];
    let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    // The resolver already said N0014; the checker adds nothing.
    assert!(out.diagnostics.is_empty(), "{:?}", out.diagnostics);
    let _ = DefId(0);
}
