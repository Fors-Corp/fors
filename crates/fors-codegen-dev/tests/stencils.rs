//! `stencils_match_fors_asm` (§10 M2-0 gate table; §2.1, risk R10): every
//! stencil, 1,000 random hole fillings each, instantiated from the static
//! table, equals `fors_asm::encode` of the same body built with the same
//! field values. Plus the trap-kind closure of the `brk` stencils and the
//! syscall allowlist over every stencil and runtime atom.

use fors_codegen_dev::stencil::int::Key;
use fors_codegen_dev::stencil::{Fill, Stencil, table};
use fors_codegen_dev::{RUNTIME_SYSCALL_ATOMS, runtime_atoms};
use fors_obj::atom::{brk_imm, is_svc};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % (hi - lo + 1) as u64) as i64
    }
}

/// A random fill every hole kind can encode: slots anywhere in a 32 KiB
/// frame, any 16-bit immediate, trap targets within `tbnz`'s +-32 KiB,
/// calls within `bl`'s +-128 MiB, literals within `adr`'s +-1 MiB.
fn random_fill(r: &mut Rng) -> Fill {
    Fill {
        slot_a: 8 * r.range(0, 4095) as u32,
        slot_b: 8 * r.range(0, 4095) as u32,
        slot_dst: 8 * r.range(0, 4095) as u32,
        imm: std::array::from_fn(|_| r.next() as u16),
        trap: std::array::from_fn(|_| 4 * r.range(-8000, 8000)),
        call: 4 * r.range(-(1 << 24), 1 << 24),
        lit: r.range(-(1 << 19), 1 << 19),
    }
}

#[test]
fn stencils_match_fors_asm() {
    let t = table();
    let mut r = Rng(0x5eed_0f00);
    let mut checked = 0u64;
    for s in &t.stencils {
        for _ in 0..1_000 {
            let fill = random_fill(&mut r);
            let (want, seq) = Stencil::build(s.key, &fill);
            assert_eq!(
                seq.holes, s.holes,
                "{:?}: hole layout depends on the fill",
                s.key
            );
            assert_eq!(
                seq.sites, s.sites,
                "{:?}: trap sites depend on the fill",
                s.key
            );
            let got = s.instantiate(&fill);
            assert!(
                got == want,
                "{:?}: table instantiation != fors_asm::encode for {fill:?}\n got  {got:08x?}\n want {want:08x?}",
                s.key
            );
            checked += 1;
        }
    }
    assert!(t.stencils.len() > 400, "{} stencils", t.stencils.len());
    println!(
        "{} stencils x 1000 fills = {checked} instantiations",
        t.stencils.len()
    );
}

/// The vacuity check of the test above: a stencil body whose hole list
/// omitted a field-dependent word would be caught (a fill that changes only
/// the slot offsets changes the encoded words).
#[test]
fn holes_cover_every_field_dependent_word() {
    let t = table();
    let s = t.get(Key::Copy);
    let a = Fill::placeholder();
    let mut b = a;
    b.slot_a += 8;
    b.slot_dst += 16;
    assert_ne!(Stencil::build(s.key, &a).0, Stencil::build(s.key, &b).0);
    assert_ne!(s.instantiate(&a), s.instantiate(&b));
}

#[test]
fn brk_imm_kinds_are_exactly_eight() {
    let t = table();
    let mut imms = Vec::new();
    for s in &t.stencils {
        for &w in &s.words {
            if let Some(imm) = brk_imm(w) {
                assert!(
                    matches!(s.key, Key::Brk { .. }),
                    "{:?} contains a brk",
                    s.key
                );
                imms.push(imm);
            }
        }
    }
    imms.sort_unstable();
    let want: Vec<u16> = (0..8).map(|k| fors_abi::TRAP_BRK_BASE + k).collect();
    assert_eq!(
        imms, want,
        "one brk stencil per ch02 R15 kind, 0x4600..=0x4607"
    );
    for k in 0..8u32 {
        let kind = fors_oir::TrapKind::from_u32(k).unwrap();
        assert_eq!(kind as u32, k);
        let s = t.get(Key::Brk { kind: k as u8 });
        assert_eq!(brk_imm(s.words[0]), fors_abi::brk_imm(k as u16));
    }
    assert!(
        fors_oir::TrapKind::from_u32(8).is_none(),
        "exactly eight kinds"
    );
}

#[test]
fn svc_only_in_runtime_syscall_atoms() {
    for s in &table().stencils {
        assert!(
            !s.words.iter().any(|&w| is_svc(w)),
            "{:?} contains svc",
            s.key
        );
    }
    let mut svc_atoms = Vec::new();
    for a in runtime_atoms() {
        if a.words().any(is_svc) {
            svc_atoms.push(a.name.clone());
        }
    }
    assert_eq!(
        svc_atoms, RUNTIME_SYSCALL_ATOMS,
        "svc appears exactly in the allowlist"
    );
}
