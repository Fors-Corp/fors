//! Portable regression gate: no assembler needed, so this is what the
//! required Linux x86_64 CI `test` job actually runs. Regenerates the same
//! deterministic case list as `oracle.rs` (this file, `common`, has no
//! `cfg` restriction — it's pure computation, no OS calls) and checks it
//! against the assembler-produced golden file, line for line.
//!
//! If this test fails after a deliberate encoding change, regenerate the
//! golden file on a macOS aarch64 host with:
//! `cargo test -p fors-asm --test oracle -- --ignored regen_golden --exact`
//! then re-run this test to confirm it now agrees.

mod common;

const GOLDEN: &str = include_str!("golden/cases.txt");

#[test]
fn encoder_matches_golden_file() {
    let cases = common::all_cases();
    let golden_lines: Vec<&str> = GOLDEN.lines().filter(|l| !l.is_empty()).collect();
    assert_eq!(
        golden_lines.len(),
        cases.len(),
        "golden file has {} lines but the generator now produces {} cases — regenerate the golden file (see this file's doc comment)",
        golden_lines.len(),
        cases.len()
    );

    let mut mismatches = Vec::new();
    for (i, (case, line)) in cases.iter().zip(golden_lines.iter()).enumerate() {
        let mut parts = line.splitn(2, '\t');
        let golden_asm = parts.next().unwrap_or("");
        let golden_hex = parts.next().unwrap_or("");
        if golden_asm != case.asm {
            mismatches.push(format!("#{i}: generator now produces `{}` but golden file has `{golden_asm}` — the deterministic generator drifted; regenerate", case.asm));
            continue;
        }
        let want = u32::from_str_radix(golden_hex, 16)
            .unwrap_or_else(|_| panic!("bad hex on golden line #{i}: {golden_hex:?}"));
        match fors_asm::encode(&case.inst) {
            Ok(got) if got == want => {}
            Ok(got) => mismatches.push(format!(
                "#{i} `{}`: ours=0x{got:08x} golden=0x{want:08x}",
                case.asm
            )),
            Err(e) => mismatches.push(format!(
                "#{i} `{}`: ours=Err({e}) golden=0x{want:08x}",
                case.asm
            )),
        }
    }
    if !mismatches.is_empty() {
        panic!(
            "{} / {} mismatches against the golden file:\n{}",
            mismatches.len(),
            cases.len(),
            mismatches.join("\n")
        );
    }
    eprintln!(
        "golden: {} cases match the checked-in assembler-derived golden file",
        cases.len()
    );
}
