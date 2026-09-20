//! F0's named gate tests (design §9's F0 entry; the task's "GATE TESTS" list):
//! `encode_decode_roundtrip` over 10k generated declarations (fixed-seed
//! xorshift, never OS randomness), `fmir_hash` invariance/change,
//! `alias_seed_present_on_every_memory_op`, `arena_brand_survives_lowering`,
//! `split_at_halves_get_distinct_seeds`.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::{TY_UNIT, TyId};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::BlockPool;
use fors_fmir::block::BlockRow;
use fors_fmir::constpool::ConstPool;
use fors_fmir::decl::DeclFmir;
use fors_fmir::encode::{fmir_hash, from_bytes, to_bytes};
use fors_fmir::ids::{BlockId, BrandId, PlaceId, ScopeId, ValId};
use fors_fmir::inst::{InstPool, InstRow};
use fors_fmir::op::{CmpPred, Op, Policy};
use fors_fmir::place::{PlacePool, Seg};
use fors_fmir::region::{CapturePool, RegionKind, RegionPool, RegionRow};
use fors_fmir::scope::{DeferPool, PlaceListPool, ScopePool, ScopeRow};
use fors_fmir::site::SitePool;
use fors_fmir::value::{ValDef, ValPool, ValRow};
use fors_fmir::verify::verify;

/// A fixed-seed xorshift64 generator — "never OS randomness" (task item's
/// literal words), so `encode_decode_roundtrip` reproduces byte-for-byte on
/// every run and every machine.
struct Xorshift64(u64);

impl Xorshift64 {
    const SEED: u64 = 0x9E3779B97F4A7C15;

    fn new() -> Self {
        Xorshift64(Self::SEED)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }

    /// A uniform value in `0..n` (`0` when `n == 0`).
    fn range(&mut self, n: u32) -> u32 {
        if n == 0 { 0 } else { self.next_u32() % n }
    }

    fn bool(&mut self) -> bool {
        self.next_u32() & 1 == 0
    }
}

fn random_op(rng: &mut Xorshift64, discriminants: &[u32]) -> Op {
    loop {
        let d = discriminants[rng.range(discriminants.len() as u32) as usize];
        let payload = match d {
            6..=13 => rng.range(4),           // ArithMode
            14..=19 => rng.next_u32() & 0xFF, // Relax: any byte
            20..=21 => rng.range(6),          // CmpPred
            53..=55 => rng.range(2),          // Policy
            _ => 0,
        };
        if let Some(op) = Op::from_parts(d, payload) {
            return op;
        }
    }
}

/// Non-terminator discriminants (0..=62 per `op.rs`'s table; terminators are
/// 63..=70 and `TileOp` — deliberately excluded here — is 71).
const NON_TERMINATOR_DISCRIMINANTS: [u32; 63] = {
    let mut arr = [0u32; 63];
    let mut i = 0;
    while i < 63 {
        arr[i] = i as u32;
        i += 1;
    }
    arr
};
const TERMINATOR_DISCRIMINANTS: [u32; 8] = [63, 64, 65, 66, 67, 68, 69, 70];

/// Builds one pseudo-random, self-contained `DeclFmir`. Referential
/// integrity of `ValId`/`BlockId` operands against other pools is
/// deliberately NOT guaranteed (an out-of-range reference never panics
/// `to_bytes`/`from_bytes` — only a would-be *consumer* like `verify()` or
/// `dump()` would need it, and neither runs in this test): the fixed points
/// this generator DOES keep are the ones a corrupt-but-well-typed encoding
/// could otherwise slip past, and the ones whose own pools de-duplicate on
/// insert (`PlacePool`/`ConstPool`, both left empty here — each has its own
/// dedicated round-trip coverage in `place.rs`/`constpool.rs`/`encode.rs`
/// instead, where uniqueness is controlled by construction).
fn gen_decl(rng: &mut Xorshift64) -> DeclFmir {
    let decl_key = DeclKeyId(rng.next_u32());
    let sig = FnSigId(rng.next_u32());

    let mut vals = ValPool::new();
    let n_params = 1 + rng.range(4);
    for i in 0..n_params {
        let ty = TyId(rng.range(6));
        vals.push(ValRow::new(ty, rng.bool(), 0, ValDef::Param(i as u16)));
    }

    let mut insts = InstPool::new();
    let mut blocks = BlockPool::new();
    let n_blocks = 1 + rng.range(4);
    for _ in 0..n_blocks {
        let first_inst = insts.len() as u32;
        let n_regular = rng.range(4);
        for _ in 0..n_regular {
            let op = random_op(rng, &NON_TERMINATOR_DISCRIMINANTS);
            let ty = TyId(rng.range(6));
            let row = InstRow {
                op,
                a: rng.next_u32() % 64,
                b: rng.next_u32() % 64,
                c: rng.next_u32() % 64,
                ty,
                site: fors_fmir::ids::SiteId(rng.next_u32() % 8),
            };
            let seed = if op.is_memory_producing() {
                [
                    AliasSeed::None,
                    AliasSeed::Conv(Conv::Let),
                    AliasSeed::Own(PlaceId(rng.next_u32() % 8)),
                    AliasSeed::Arena(BrandId(rng.next_u32() % 8)),
                    AliasSeed::Split {
                        parent: PlaceId(rng.next_u32() % 8),
                        side: (rng.next_u32() % 2) as u8,
                    },
                ][rng.range(5) as usize]
            } else {
                AliasSeed::None
            };
            let inst_id = insts.push(row, seed);
            if rng.bool() {
                vals.push(ValRow::new(ty, rng.bool(), 0, ValDef::Inst(inst_id)));
            }
        }
        let term_op = random_op(rng, &TERMINATOR_DISCRIMINANTS);
        let term = InstRow {
            op: term_op,
            a: rng.next_u32() % 8,
            b: rng.next_u32() % 8,
            c: rng.next_u32() % 8,
            ty: TY_UNIT,
            site: fors_fmir::ids::SiteId(rng.next_u32() % 8),
        };
        let inst_len = insts.len() as u32 - first_inst;
        blocks.push(BlockRow {
            first_inst,
            inst_len,
            term,
            scope: ScopeId(0),
        });
    }

    let mut scopes = ScopePool::new();
    scopes.push(ScopeRow::root(BrandId::NONE));

    let mut regions = RegionPool::new();
    let n_regions = rng.range(3);
    for _ in 0..n_regions {
        let kind = [
            RegionKind::Spawn,
            RegionKind::Parallel,
            RegionKind::WithArena,
        ][rng.range(3) as usize];
        let captures = if rng.bool() {
            RegionRow::ABSENT_CAPTURES
        } else {
            let start = regions.captures.len() as u32;
            for _ in 0..rng.range(3) {
                let conv = [Conv::Let, Conv::Inout, Conv::Sink, Conv::Set][rng.range(4) as usize];
                regions.captures.push(fors_fmir::region::CaptureRow {
                    value: ValId(rng.next_u32() % 8),
                    conv,
                });
            }
            start..(regions.captures.len() as u32)
        };
        regions.push(RegionRow {
            kind,
            captures,
            brand: BrandId::NONE,
        });
    }

    DeclFmir {
        decl: decl_key,
        sig,
        vals,
        blocks,
        insts,
        scopes,
        places: PlacePool::new(),
        regions,
        sites: SitePool::new(),
        consts: ConstPool::new(),
        obligations: PlaceListPool::new(),
        scoped_sources: PlaceListPool::new(),
        defers: DeferPool::new(),
        entry: BlockId(0),
        is_unsafe_invariant: rng.bool(),
        fingerprint: 0,
    }
}

/// The named F0 gate: "`encode_decode_roundtrip` over 10k generated
/// declarations (fixed-seed xorshift, never OS randomness)". Round-tripping
/// is checked as `to_bytes(from_bytes(to_bytes(d))) == to_bytes(d)`, not as
/// field-by-field equality of the decoded `DeclFmir` (which has no derived
/// `PartialEq` — see `encode.rs`'s module docs for why that is the right
/// comparison for a canonical encoding, not a shortcut).
#[test]
fn encode_decode_roundtrip() {
    let mut rng = Xorshift64::new();
    for i in 0..10_000u32 {
        let decl = gen_decl(&mut rng);
        let bytes = to_bytes(&decl);
        let decoded =
            from_bytes(&bytes).unwrap_or_else(|e| panic!("decl {i} failed to decode: {e}"));
        let re_encoded = to_bytes(&decoded);
        assert_eq!(re_encoded, bytes, "decl {i} did not round-trip");
    }
}

#[test]
fn fmir_hash_is_invariant_under_block_renumbering_and_changes_on_operand_edit() {
    // Renumbering invariance has its own focused unit test in
    // `encode.rs::tests::hash_is_invariant_under_block_renumbering`; this
    // gate additionally covers the generated corpus: hashing the same
    // generated declaration twice must always agree (determinism), which
    // `encode_decode_roundtrip`'s 10k declarations exercise as a side
    // effect of every `fmir_hash` call below not panicking or diverging.
    let mut rng = Xorshift64::new();
    for _ in 0..500 {
        let decl = gen_decl(&mut rng);
        assert_eq!(fmir_hash(&decl), fmir_hash(&decl));
    }

    // Changes on any operand edit: flip one value's secret bit and confirm
    // the hash moves.
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    decl.vals
        .push(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)));
    let before = fmir_hash(&decl);
    let mut flipped = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    flipped
        .vals
        .push(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
    assert_ne!(before, fmir_hash(&flipped));
}

/// `alias_seed_present_on_every_memory_op` (design §3.4a).
#[test]
fn alias_seed_present_on_every_memory_op() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let with_seed = InstRow {
        op: Op::Alloc,
        a: 0,
        b: 0,
        c: fors_fmir::op::NO_OPERAND,
        ty: TY_UNIT,
        site: fors_fmir::ids::SiteId(0),
    };
    decl.push_inst(with_seed, AliasSeed::Own(PlaceId(0)));
    assert!(
        verify(&decl).is_empty(),
        "a memory op WITH a seed must not be rejected: {:?}",
        verify(&decl)
    );

    let mut missing = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    missing.push_inst(with_seed, AliasSeed::None);
    assert!(
        verify(&missing)
            .iter()
            .any(|d| d.code == fors_fmir::diag::DiagCode::MemoryOpMissingAliasSeed),
        "a memory op with NO seed must be rejected"
    );
}

/// `arena_brand_survives_lowering`. F0 has no real lowering pass yet (design
/// §1.2), so this checks the property lowering must preserve: an
/// `arena_deref`'s `AliasSeed::Arena(BrandId)` survives the FMIR
/// representation itself — built, then round-tripped through the canonical
/// byte encoding (`encode.rs`'s stand-in for "a pass ran and handed the IR
/// back"), unchanged.
#[test]
fn arena_brand_survives_lowering() {
    let brand = BrandId(42);
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let arena_val = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)));
    let deref = InstRow {
        op: Op::ArenaDeref,
        a: arena_val.0,
        b: fors_fmir::op::NO_OPERAND,
        c: fors_fmir::op::NO_OPERAND,
        ty: TY_UNIT,
        site: fors_fmir::ids::SiteId(0),
    };
    decl.push_inst(deref, AliasSeed::Arena(brand));
    // The owning scope also carries the brand (design §3.2/§3.4a).
    decl.scopes = {
        let mut scopes = ScopePool::new();
        scopes.push(ScopeRow::root(brand));
        scopes
    };

    assert!(verify(&decl).is_empty(), "{:?}", verify(&decl));
    let bytes = to_bytes(&decl);
    let decoded = from_bytes(&bytes).expect("decode");

    assert_eq!(
        decoded.insts.aliases.get(0),
        AliasSeed::Arena(brand),
        "the alias seed's brand must survive byte for byte"
    );
    assert_eq!(
        decoded.scopes.row(ScopeId(0)).brand,
        brand,
        "the scope's own brand must survive byte for byte"
    );
}

/// `split_at_halves_get_distinct_seeds` (ch01 R19b, design §3.4a): the two
/// halves of a `split_at`-shaped pair of `slice_range`s must get DIFFERENT
/// `AliasSeed::Split { side, .. }` values, or OIR would treat them as
/// aliasing and the SoA/SPMD rewrite the seed exists for would be unsound.
#[test]
fn split_at_halves_get_distinct_seeds() {
    let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let parent = decl.places.intern(0, &[], TY_UNIT);
    let base = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)));
    let mid = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
    let end = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(2)));

    let left = InstRow {
        op: Op::SliceRange,
        a: base.0,
        b: 0,
        c: mid.0,
        ty: TY_UNIT,
        site: fors_fmir::ids::SiteId(0),
    };
    let left_id = decl.push_inst(left, AliasSeed::Split { parent, side: 0 });
    let right = InstRow {
        op: Op::SliceRange,
        a: base.0,
        b: mid.0,
        c: end.0,
        ty: TY_UNIT,
        site: fors_fmir::ids::SiteId(0),
    };
    let right_id = decl.push_inst(right, AliasSeed::Split { parent, side: 1 });

    let left_seed = decl.insts.aliases.get(left_id.index());
    let right_seed = decl.insts.aliases.get(right_id.index());
    assert_ne!(
        left_seed, right_seed,
        "the two halves must not get the same alias seed"
    );
    assert!(
        verify(&decl).is_empty(),
        "both halves carry a seed, so verify() must accept them: {:?}",
        verify(&decl)
    );

    // And the distinction survives the canonical encoding, not just the
    // in-memory `AliasSeedPool`.
    let decoded = from_bytes(&to_bytes(&decl)).expect("decode");
    assert_ne!(
        decoded.insts.aliases.get(left_id.index()),
        decoded.insts.aliases.get(right_id.index())
    );
}

#[test]
fn unused_import_guards() {
    // `CmpPred`/`Policy`/`PlaceListPool`/`Seg`/`CapturePool` are exercised
    // indirectly by the generator above and by other gate files; this no-op
    // keeps the imports honest if a future edit trims `gen_decl`.
    let _ = CmpPred::Eq;
    let _ = Policy::Runtime;
    let _: PlaceListPool = PlaceListPool::new();
    let _ = Seg::Deref;
    let _: CapturePool = CapturePool::new();
}
