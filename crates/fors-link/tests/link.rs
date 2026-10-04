//! `link_once` over the real runtime atoms: relocations resolve, the
//! signature recomputes, and the syscall scan holds — `svc` appears only
//! inside the atoms of `RUNTIME_SYSCALL_ATOMS` (E10; M2-3 makes it strict).

use fors_codegen_dev::rt::{ENTRY, FORS_MAIN};
use fors_codegen_dev::{RUNTIME_SYSCALL_ATOMS, runtime_atoms};
use fors_link::{LinkError, link_once};
use fors_obj::Atom;
use fors_obj::atom::is_svc;

/// A Fors `main` that just returns: `ret`.
fn trivial_main() -> Atom {
    let mut a = Atom::new(FORS_MAIN);
    a.push_word(0xd65f_03c0);
    a
}

fn image() -> fors_link::Image {
    link_once(&[trivial_main()], &runtime_atoms(), ENTRY, "prog").expect("links")
}

#[test]
fn every_bl_resolves_to_its_callee() {
    let img = image();
    let text = fors_obj::scan::section_bytes(&img.bytes, "__TEXT", "__text").unwrap();
    let at = |n: &str| img.atoms.iter().find(|p| p.name == n).unwrap().start;
    for a in runtime_atoms() {
        for r in &a.relocs {
            let site = at(&a.name) + r.offset;
            let w = u32::from_le_bytes(text[site as usize..site as usize + 4].try_into().unwrap());
            assert_eq!(w >> 26, 0b100101, "a bl");
            let off = ((w << 6) as i32 >> 6) * 4;
            assert_eq!(
                (i64::from(site) + i64::from(off)) as u32,
                at(&r.target),
                "{} -> {}",
                a.name,
                r.target
            );
        }
    }
    fors_obj::sign::verify_signature(&img.bytes).expect("signed");
    // The directory has one 16-byte row per atom, sorted by address.
    let dir = fors_obj::scan::section_bytes(&img.bytes, "__TEXT", "__fors_dir").unwrap();
    assert_eq!(dir.len(), 16 * img.atoms.len());
    let starts: Vec<u32> = dir
        .chunks(16)
        .map(|r| u32::from_le_bytes(r[..4].try_into().unwrap()))
        .collect();
    assert!(starts.windows(2).all(|w| w[0] < w[1]));
}

/// Design §10 M2-0 "Why `svc` is acceptable": the image contains no `svc`
/// outside `RUNTIME_SYSCALL_ATOMS`. M2-3 empties the allowlist and this
/// test becomes strict.
#[test]
fn image_contains_no_svc() {
    let img = image();
    let text = fors_obj::scan::section_bytes(&img.bytes, "__TEXT", "__text").unwrap();
    let mut seen = 0;
    for (i, c) in text.chunks(4).enumerate() {
        let w = u32::from_le_bytes(c.try_into().unwrap());
        if !is_svc(w) {
            continue;
        }
        seen += 1;
        let off = 4 * i as u32;
        let owner = img
            .atoms
            .iter()
            .find(|p| p.start <= off && off < p.start + p.len)
            .expect("svc inside an atom");
        assert!(
            RUNTIME_SYSCALL_ATOMS.contains(&owner.name.as_str()),
            "svc in {}, not allowlisted",
            owner.name
        );
    }
    assert_eq!(seen, 1, "exactly the one write syscall");
}

#[test]
fn link_errors_are_named() {
    let mut bad = trivial_main();
    bad.push_word(0x9400_0000);
    bad.relocs.push(fors_obj::Reloc {
        offset: 4,
        target: "_nowhere".into(),
    });
    assert!(matches!(
        link_once(&[bad], &runtime_atoms(), ENTRY, "p"),
        Err(LinkError::UndefinedSymbol { .. })
    ));
    assert!(matches!(
        link_once(
            &[trivial_main(), trivial_main()],
            &runtime_atoms(),
            ENTRY,
            "p"
        ),
        Err(LinkError::DuplicateSymbol(_))
    ));
    assert!(matches!(
        link_once(&[trivial_main()], &[], ENTRY, "p"),
        Err(LinkError::NoEntry(_))
    ));
}

#[test]
fn link_is_deterministic() {
    assert_eq!(image().bytes, image().bytes);
}
