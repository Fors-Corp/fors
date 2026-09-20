//! The oracle: assembles every generated case with the system toolchain
//! and compares every resulting word against `fors_asm::encode`, byte for
//! byte. macOS/aarch64 only — this is the one machine in CI-shaped setups
//! that actually has a native AArch64 assembler to ask; `golden.rs` is
//! what Linux CI runs instead, against a file this test's `regen_golden`
//! produces.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod common;

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn scratch_dir() -> PathBuf {
    let dir = std::env::temp_dir().join("fors_asm_oracle");
    fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// Assembles `asm_lines` (one instruction per line, no directives) as one
/// `.s` file and returns the `__text` section's words, in order, by
/// invoking `clang -c -x assembler` then `otool -s __TEXT __text` — the
/// same two system tools the spike's `difftest` used, kept as the trusted
/// reference rather than re-deriving a Mach-O reader here.
fn assemble_and_extract(asm_lines: &[String]) -> Result<Vec<u32>, String> {
    let dir = scratch_dir();
    let s_path = dir.join("cases.s");
    let o_path = dir.join("cases.o");
    let mut text = String::from(".text\n_fors_asm_oracle_cases:\n");
    for line in asm_lines {
        text.push_str(line);
        text.push('\n');
    }
    fs::write(&s_path, &text).expect("write .s");

    let asm_out = Command::new("clang")
        .args(["-arch", "arm64", "-c", "-o"])
        .arg(&o_path)
        .arg(&s_path)
        .output()
        .expect("run clang");
    if !asm_out.status.success() {
        return Err(format!(
            "clang failed:\n{}",
            String::from_utf8_lossy(&asm_out.stderr)
        ));
    }

    let otool_out = Command::new("otool")
        .args(["-s", "__TEXT", "__text"])
        .arg(&o_path)
        .output()
        .expect("run otool");
    if !otool_out.status.success() {
        return Err(format!(
            "otool failed:\n{}",
            String::from_utf8_lossy(&otool_out.stderr)
        ));
    }
    let dump = String::from_utf8_lossy(&otool_out.stdout);
    let mut words = Vec::new();
    for line in dump.lines().skip(1) {
        let mut cols = line.split_whitespace();
        cols.next(); // address column
        for hexword in cols {
            if hexword.len() == 8 && hexword.chars().all(|c| c.is_ascii_hexdigit()) {
                words.push(u32::from_str_radix(hexword, 16).unwrap());
            }
        }
    }
    Ok(words)
}

/// A single small assembly attempt, expected to be REJECTED by the system
/// assembler (used for the "one past the boundary" checks, where each
/// case must fail assembly on its own — batching them with the valid
/// cases above would just abort the whole file at the first bad line).
fn assembler_rejects(asm_line: &str) -> bool {
    let dir = scratch_dir();
    let s_path = dir.join("reject_probe.s");
    let o_path = dir.join("reject_probe.o");
    fs::write(
        &s_path,
        format!(".text\n_fors_asm_reject_probe:\n{asm_line}\n"),
    )
    .expect("write .s");
    let status = Command::new("clang")
        .args(["-arch", "arm64", "-c", "-o"])
        .arg(&o_path)
        .arg(&s_path)
        .status()
        .expect("run clang");
    !status.success()
}

#[test]
fn encoder_matches_system_assembler() {
    let cases = common::all_cases();
    assert!(
        cases.len() >= 20_000,
        "case count {} is below the 20000 target — the generator regressed, not just the encoder",
        cases.len()
    );

    let asm_lines: Vec<String> = cases.iter().map(|c| c.asm.clone()).collect();
    let words = assemble_and_extract(&asm_lines).expect("assemble all generated cases");
    assert_eq!(
        words.len(),
        cases.len(),
        "assembler produced a different instruction count than we generated (a generated line likely assembled to something unexpected, e.g. a pseudo-op expanding to 0 or >1 words)"
    );

    let mut mismatches = Vec::new();
    for (i, (case, &want)) in cases.iter().zip(words.iter()).enumerate() {
        match fors_asm::encode(&case.inst) {
            Ok(got) if got == want => {}
            Ok(got) => mismatches.push(format!(
                "#{i} `{}`: ours=0x{got:08x} assembler=0x{want:08x}",
                case.asm
            )),
            Err(e) => mismatches.push(format!(
                "#{i} `{}`: ours=Err({e}) assembler=0x{want:08x}",
                case.asm
            )),
        }
    }
    if !mismatches.is_empty() {
        panic!(
            "{} / {} mismatches:\n{}",
            mismatches.len(),
            cases.len(),
            mismatches.join("\n")
        );
    }
    eprintln!(
        "oracle: {} cases, all byte-for-byte identical to the system assembler",
        cases.len()
    );
}

#[test]
fn boundary_cases_are_rejected_by_both_us_and_the_assembler() {
    // `common::boundary_reject_cases()` already asserts our own
    // constructors return `Err`; this half confirms the assembler agrees
    // that the boundary is real, not an overly strict check on our side.
    let cases = common::boundary_reject_cases();
    assert!(!cases.is_empty());
    let mut unexpected_accepts = Vec::new();
    for c in &cases {
        if !assembler_rejects(&c.attempted_asm) {
            unexpected_accepts.push(format!(
                "{}: assembler ACCEPTED `{}` (we reject it — investigate which side is wrong)",
                c.what, c.attempted_asm
            ));
        }
    }
    if !unexpected_accepts.is_empty() {
        panic!("{}", unexpected_accepts.join("\n"));
    }
    eprintln!(
        "oracle: {} boundary cases confirmed rejected by both this crate and the system assembler",
        cases.len()
    );
}

/// Regenerates `tests/golden/cases.txt` from the same case list, but only
/// ever writes a line whose hex word the assembler ITSELF produced —
/// running this test is, by construction, re-running the full oracle
/// check above. Ignored by default (`cargo test` skips it); run
/// explicitly to regenerate after a deliberate encoding change:
/// `cargo test -p fors-asm --test oracle -- --ignored regen_golden --exact`
#[test]
#[ignore]
fn regen_golden() {
    let cases = common::all_cases();
    let asm_lines: Vec<String> = cases.iter().map(|c| c.asm.clone()).collect();
    let words = assemble_and_extract(&asm_lines).expect("assemble all generated cases");
    assert_eq!(words.len(), cases.len());

    let mut out = String::new();
    for (case, word) in cases.iter().zip(words.iter()) {
        // Fail loudly rather than checking in a golden file that disagrees
        // with our own encoder — a passing regen run IS an oracle-verified
        // update, an update that silently diverged is not a golden file.
        let got = fors_asm::encode(&case.inst).unwrap_or_else(|e| {
            panic!(
                "regen_golden: `{}` no longer encodes ({e}) — fix the encoder before regenerating",
                case.asm
            )
        });
        assert_eq!(
            got, *word,
            "regen_golden: `{}` disagrees with the assembler (ours=0x{got:08x} theirs=0x{word:08x}) — fix the encoder before regenerating",
            case.asm
        );
        out.push_str(&case.asm);
        out.push('\t');
        out.push_str(&format!("{word:08x}"));
        out.push('\n');
    }
    let golden_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/cases.txt");
    fs::write(&golden_path, &out).expect("write golden file");
    eprintln!("wrote {} lines to {}", cases.len(), golden_path.display());
}
