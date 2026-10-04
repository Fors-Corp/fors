//! M2-0's `fors-obj` gates (`docs/design/m2-dev-backend.md` §10 M2-0 gate
//! table): the byte golden, the spike's two recorded pitfalls, the
//! content-derived UUID, the unwind/host-path scans, and (macOS only)
//! `codesign --verify` with its negative control. Everything except the
//! last runs on Linux.

use fors_obj::macho::{ExecSpec, build_executable, layout};
use fors_obj::scan;
use fors_obj::sign::{CS_PAGE, verify_signature};

/// `_main: mov w0, #0; ret` — the fixed two-instruction program.
const MINIMAL_TEXT: [u32; 2] = [0x5280_0000, 0xd65f_03c0];

fn text_of(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn minimal_image() -> Vec<u8> {
    let text = text_of(&MINIMAL_TEXT);
    let dir = [0u8; 16];
    build_executable(&ExecSpec {
        text: &text,
        entry: 0,
        function_starts: &[0],
        dir: &dir,
        lines: &[0, 0, 0, 0],
        identifier: "minimal",
    })
}

/// A larger image: several pages of code, so the page-hash and UUID tests
/// see more than page 0.
fn big_image(patch: Option<(usize, u8)>) -> Vec<u8> {
    let mut words = vec![0xd503_201fu32; 9000]; // nop
    words[0] = 0x5280_0000;
    words[1] = 0xd65f_03c0;
    let mut text = text_of(&words);
    if let Some((at, v)) = patch {
        text[at] = v;
    }
    build_executable(&ExecSpec {
        text: &text,
        entry: 0,
        function_starts: &[0, 4096, 64],
        dir: &[1u8; 32],
        lines: &[],
        identifier: "big",
    })
}

const GOLDEN: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/golden/minimal.macho");

#[test]
fn macho_minimal_image_golden() {
    let img = minimal_image();
    let golden = std::fs::read(GOLDEN).ok();
    match golden {
        Some(g) => assert!(
            g == img,
            "the minimal image's bytes changed ({} vs {} bytes); an intended \
             layout change regenerates the golden by deleting it and running \
             with FORS_WRITE_MACHO_GOLDEN=1",
            g.len(),
            img.len()
        ),
        None if std::env::var_os("FORS_WRITE_MACHO_GOLDEN").is_some() => {
            std::fs::create_dir_all(std::path::Path::new(GOLDEN).parent().unwrap()).unwrap();
            std::fs::write(GOLDEN, &img).unwrap();
        }
        None => panic!("golden {GOLDEN} missing"),
    }
    // The golden is a real, self-consistent image.
    let info = verify_signature(&img).expect("signature recomputes");
    assert_eq!(info.identifier, "minimal");
    let text = scan::section_bytes(&img, "__TEXT", "__text").unwrap();
    assert_eq!(text, text_of(&MINIMAL_TEXT).as_slice());
}

#[test]
fn section64_has_three_reserved_fields() {
    let img = minimal_image();
    // Load commands tile `sizeofcmds` exactly: a 76-byte section_64 (two
    // reserved fields) would shift every later command and fail this.
    let lcs = scan::load_commands(&img).expect("load commands parse");
    assert_eq!(lcs.len(), 15);
    let segs = scan::segments(&img).unwrap();
    let text = segs.iter().find(|s| s.name == "__TEXT").unwrap();
    assert_eq!(text.sections.len(), 3);
    for pair in text.sections.windows(2) {
        assert_eq!(
            pair[1].record_off - pair[0].record_off,
            80,
            "section_64 is 80 bytes"
        );
    }
    for s in &text.sections {
        assert_eq!(s.reserved, [0, 0, 0], "{}", s.sectname);
        assert_eq!(s.segname, "__TEXT");
    }
    // The command after __TEXT is __LINKEDIT, exactly 72 + 3 * 80 later.
    let i = lcs
        .iter()
        .position(|l| l.off == segs[1].sections[0].record_off - 72)
        .unwrap();
    assert_eq!(lcs[i].size, 72 + 3 * 80);
    assert_eq!(lcs[i + 1].off, lcs[i].off + 72 + 3 * 80);
}

#[test]
fn page0_fields_final_before_hashing() {
    for img in [minimal_image(), big_image(None)] {
        // Every slot, page 0 included, hashes the FINAL bytes.
        let info = verify_signature(&img).expect("every page hash matches the final bytes");
        let (off, size) = scan::code_signature(&img).unwrap();
        assert_eq!(off + size, img.len(), "LC_CODE_SIGNATURE's size is final");
        assert_eq!(info.code_limit, off);
        assert_eq!(info.slots, off.div_ceil(CS_PAGE));
        let segs = scan::segments(&img).unwrap();
        let le = segs.iter().find(|s| s.name == "__LINKEDIT").unwrap();
        assert_eq!(
            le.fileoff + le.filesize,
            img.len() as u64,
            "__LINKEDIT filesize is final"
        );
        assert_eq!(le.vmsize % 0x4000, 0);
        assert!(le.vmsize >= le.filesize);
        let text = segs.iter().find(|s| s.name == "__TEXT").unwrap();
        assert_eq!(
            info.exec_seg_limit, text.filesize,
            "execSeg limit = __TEXT filesize"
        );
    }
    // A layout's page 0 is already final except for the UUID: signing
    // changes only those 16 bytes before the signature.
    let text = text_of(&MINIMAL_TEXT);
    let spec = ExecSpec {
        text: &text,
        entry: 0,
        function_starts: &[0],
        dir: &[0u8; 16],
        lines: &[0; 4],
        identifier: "minimal",
    };
    let l = layout(&spec);
    let signed = build_executable(&spec);
    let differing: Vec<usize> = (0..l.bytes.len())
        .filter(|&i| l.bytes[i] != signed[i])
        .collect();
    assert!(
        differing
            .iter()
            .all(|&i| (l.uuid_off..l.uuid_off + 16).contains(&i))
    );
}

#[test]
fn uuid_is_content_derived() {
    let a = fors_obj::uuid::image_uuid(&big_image(None)).unwrap();
    let b = fors_obj::uuid::image_uuid(&big_image(None)).unwrap();
    assert_eq!(a, b, "identical inputs, identical UUID");
    assert_eq!(a[6] >> 4, 8, "version nibble 8");
    // One code byte changed, on a page other than page 0.
    let c = fors_obj::uuid::image_uuid(&big_image(Some((20_000, 0x00)))).unwrap();
    assert_ne!(a, c, "one code byte changed, different UUID");
    let m = fors_obj::uuid::image_uuid(&minimal_image()).unwrap();
    assert_ne!(a, m);
}

#[test]
fn image_has_no_unwind_sections() {
    for img in [minimal_image(), big_image(None)] {
        let names = scan::section_names(&img).unwrap();
        for bad in [
            "__eh_frame",
            "__unwind_info",
            "__compact_unwind",
            "__gcc_except_tab",
        ] {
            assert!(
                !names.iter().any(|n| n.ends_with(bad)),
                "{bad} in {names:?}"
            );
        }
        assert_eq!(
            names,
            ["__TEXT,__text", "__TEXT,__fors_dir", "__TEXT,__fors_lines"]
        );
        // And no byte sequence naming one anywhere.
        for bad in [&b"__eh_frame"[..], b"__unwind_info", b"__compact_unwind"] {
            assert!(!img.windows(bad.len()).any(|w| w == bad));
        }
    }
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty() && hay.windows(needle.len()).any(|w| w == needle)
}

#[test]
fn image_has_no_host_paths_or_times() {
    let a = big_image(None);
    std::thread::sleep(std::time::Duration::from_millis(1100));
    let b = big_image(None);
    assert!(
        a == b,
        "two builds a second apart are byte-identical: no time"
    );
    let mut needles: Vec<Vec<u8>> = vec![
        b"/Users/".to_vec(),
        b"/home/".to_vec(),
        b"/tmp".to_vec(),
        b"/private/".to_vec(),
        b"/var/folders".to_vec(),
        env!("CARGO_MANIFEST_DIR").as_bytes().to_vec(),
    ];
    if let Some(h) = std::env::var_os("HOME") {
        needles.push(h.to_string_lossy().as_bytes().to_vec());
    }
    if let Ok(d) = std::env::current_dir() {
        needles.push(d.to_string_lossy().as_bytes().to_vec());
    }
    for img in [&a, &minimal_image()] {
        for n in &needles {
            assert!(
                !contains(img, n),
                "host path {:?} in the image",
                String::from_utf8_lossy(n)
            );
        }
    }
    // The only paths in the image are the two system ones every executable
    // names.
    assert!(contains(&a, b"/usr/lib/dyld\0"));
    assert!(contains(&a, b"/usr/lib/libSystem.B.dylib\0"));
    // LC_LOAD_DYLIB's timestamp is the fixed 2, never a clock.
    let lc = scan::load_commands(&a)
        .unwrap()
        .into_iter()
        .find(|l| l.cmd == fors_obj::macho::LC_LOAD_DYLIB)
        .unwrap();
    assert_eq!(&a[lc.off + 12..lc.off + 16], &2u32.to_le_bytes());
}

#[test]
fn exports_and_entry_point_agree() {
    let img = minimal_image();
    let lcs = scan::load_commands(&img).unwrap();
    let main = lcs
        .iter()
        .find(|l| l.cmd == fors_obj::macho::LC_MAIN)
        .unwrap();
    let entryoff = u64::from_le_bytes(img[main.off + 8..main.off + 16].try_into().unwrap());
    let text = scan::segments(&img).unwrap()[1].sections[0].clone();
    assert_eq!(entryoff, u64::from(text.offset));
    let trie_lc = lcs
        .iter()
        .find(|l| l.cmd == fors_obj::macho::LC_DYLD_EXPORTS_TRIE)
        .unwrap();
    let off =
        u32::from_le_bytes(img[trie_lc.off + 8..trie_lc.off + 12].try_into().unwrap()) as usize;
    let size =
        u32::from_le_bytes(img[trie_lc.off + 12..trie_lc.off + 16].try_into().unwrap()) as usize;
    let trie = &img[off..off + size];
    assert_eq!(fors_obj::trie::lookup(trie, "_main"), Some(entryoff));
    assert_eq!(fors_obj::trie::lookup(trie, "__mh_execute_header"), Some(0));
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod macos {
    use super::*;

    fn scratch(tag: &str) -> std::path::PathBuf {
        let d = std::env::temp_dir().join(format!("fors-obj-{tag}-{}", std::process::id()));
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    fn codesign_ok(path: &std::path::Path) -> bool {
        std::process::Command::new("codesign")
            .arg("--verify")
            .arg(path)
            .output()
            .expect("codesign is a test-time tool on macOS")
            .status
            .success()
    }

    #[test]
    fn codesign_verify_accepts_image() {
        let dir = scratch("codesign");
        for (name, img) in [("minimal", minimal_image()), ("big", big_image(None))] {
            let p = fors_obj::write::write_executable(&dir, name, &img).unwrap();
            assert!(codesign_ok(&p), "codesign --verify rejected {name}");
            // Negative control: one patched code byte is rejected.
            let mut bad = img.clone();
            let text = scan::segments(&img).unwrap()[1].sections[0].clone();
            bad[text.offset as usize + 1] ^= 0x40;
            let q = fors_obj::write::write_executable(&dir, &format!("{name}_bad"), &bad).unwrap();
            assert!(!codesign_ok(&q), "codesign accepted a patched {name}");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The minimal image is not just signed but runs: `_main` returns 0.
    #[test]
    fn minimal_image_runs_and_exits_zero() {
        let dir = scratch("run");
        let p = fors_obj::write::write_executable(&dir, "minimal", &minimal_image()).unwrap();
        let out = std::process::Command::new(&p).env_clear().output().unwrap();
        assert_eq!(out.status.code(), Some(0));
        assert!(out.stdout.is_empty());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
