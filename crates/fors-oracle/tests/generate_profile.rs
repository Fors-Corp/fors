//! M2-0's generator gate (`docs/design/m2-dev-backend.md` §10, M2-0 gate
//! table row 1): `generate(seed)` is byte-for-byte what it was before
//! `Profile` / `generate_with` existed. The fingerprints in
//! `tests/golden/generate_fingerprints.txt` were written by THIS test from
//! the unmodified generator (base `deea1ba`) before `generate.rs` was
//! touched; every later change must reproduce them exactly.
//!
//! A fingerprint covers everything a run can observe of a generated program:
//! every function's name, canonical FMIR bytes (`fors_fmir::encode::to_bytes`),
//! string table and intrinsic table, the entry index, and the type store's
//! digest.

use fors_oracle::generate::generate;

const GOLDEN: &str = include_str!("golden/generate_fingerprints.txt");
const SEEDS: u64 = 1_000;

fn put(b: &mut Vec<u8>, bytes: &[u8]) {
    b.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    b.extend_from_slice(bytes);
}

/// The fingerprint of `generate(seed)`.
pub fn fingerprint(seed: u64) -> u128 {
    let g = generate(seed);
    let mut b = Vec::new();
    b.extend_from_slice(&(g.prog.entry as u64).to_le_bytes());
    b.extend_from_slice(&(g.prog.fns.len() as u64).to_le_bytes());
    for f in &g.prog.fns {
        put(&mut b, f.name.as_bytes());
        put(&mut b, &fors_fmir::encode::to_bytes(&f.decl));
        b.extend_from_slice(&(f.strings.len() as u64).to_le_bytes());
        for (id, s) in &f.strings {
            b.extend_from_slice(&id.to_le_bytes());
            put(&mut b, s);
        }
        b.extend_from_slice(&(f.intrinsics.len() as u64).to_le_bytes());
        for (id, n) in &f.intrinsics {
            b.extend_from_slice(&id.to_le_bytes());
            put(&mut b, n.as_bytes());
        }
    }
    b.extend_from_slice(&g.tys.digest().to_le_bytes());
    fors_index::fingerprint::hash_bytes(&b)
}

fn render() -> String {
    let mut out = String::new();
    for seed in 0..SEEDS {
        out.push_str(&format!("{seed} {:032x}\n", fingerprint(seed)));
    }
    out
}

#[test]
fn generate_default_profile_is_unchanged() {
    let now = render();
    if std::env::var_os("FORS_WRITE_GENERATE_FINGERPRINTS").is_some() && GOLDEN.is_empty() {
        // One-shot bootstrap only: an EMPTY golden file may be filled; a
        // non-empty one is never overwritten by the test.
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/golden/generate_fingerprints.txt"
        );
        std::fs::write(path, &now).expect("write fingerprints");
        return;
    }
    assert_eq!(
        GOLDEN.lines().count() as u64,
        SEEDS,
        "golden has one line per seed"
    );
    for (want, got) in GOLDEN.lines().zip(now.lines()) {
        assert_eq!(want, got, "generate(seed) changed");
    }
}

/// `Profile::STRAIGHT_LINE` is M2-0's surface: one function, one block, no
/// calls, no unsigned `sat` `neg` (owner Q6) — and it still exercises every
/// arithmetic mode, division, shifts, `neg`, `not`, the three conversions
/// and both output intrinsics. (`icmp` only feeds branches in the
/// generator, so it never appears here; the native edge table covers it.)
#[test]
fn straight_line_profile_shapes() {
    use fors_fmir::op::{ArithMode, Op};
    use fors_oracle::generate::{Profile, generate_with};
    let mut seen = std::collections::BTreeSet::new();
    for seed in 0..300 {
        let g = generate_with(seed, &Profile::STRAIGHT_LINE);
        assert_eq!(g.prog.fns.len(), 1, "seed {seed}: no helpers");
        let f = &g.prog.fns[0];
        assert_eq!(f.decl.blocks.len(), 1, "seed {seed}: one block");
        for (_, r) in f.decl.insts.all_rows() {
            assert!(
                !matches!(r.op, Op::CallDirect | Op::Icmp(_)),
                "seed {seed}: {:?}",
                r.op
            );
            if r.op == Op::Neg(ArithMode::Sat) {
                let k = g.tys.a(g.tys.unqual(r.ty)) as u8;
                let p = fors_fir::ty::PrimKind::from_u8(k).unwrap();
                assert!(
                    matches!(
                        p,
                        fors_fir::ty::PrimKind::I8
                            | fors_fir::ty::PrimKind::I16
                            | fors_fir::ty::PrimKind::I32
                            | fors_fir::ty::PrimKind::I64
                    ),
                    "seed {seed}: sat neg on {p:?}"
                );
            }
            seen.insert(format!("{:?}", r.op));
        }
    }
    for op in [
        "Add(Trap)",
        "Add(Wrap)",
        "Add(Sat)",
        "Sub(Trap)",
        "Sub(Wrap)",
        "Sub(Sat)",
        "Mul(Trap)",
        "Mul(Wrap)",
        "Mul(Sat)",
        "Div(Trap)",
        "Div(Wrap)",
        "Div(Sat)",
        "Rem(Trap)",
        "Rem(Wrap)",
        "Shl(Wrap)",
        "Shl(Sat)",
        "Shr(Wrap)",
        "Shr(Trap)",
        "Neg(Wrap)",
        "Neg(Sat)",
        "Not",
        "And",
        "Or",
        "Xor",
        "ConvChecked",
        "ConvWrap",
        "ConvSat",
        "CopyFrom",
        "Init",
        "Intrinsic",
        "ConstStr",
    ] {
        assert!(seen.contains(op), "{op} never generated: {seen:?}");
    }
    // FULL still has the shapes STRAIGHT_LINE removes.
    let full_blocks: usize = (0..50)
        .map(|s| {
            fors_oracle::generate::generate(s).prog.fns[0]
                .decl
                .blocks
                .len()
        })
        .sum();
    assert!(full_blocks > 50);
}
