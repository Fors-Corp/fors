//! Runs the hand-written negative FMIR corpus under
//! `tests/negative_corpus/*.fmir` (task item 6 / design risk R5: "a
//! **negative corpus**: ~20 hand-written FMIR declarations, one per §5.2
//! condition, each asserted to its `ub:` class — plus the two *positive*
//! aliasing cases of E14 ... Written in F0's textual FMIR, before F1").
//!
//! Each file's directives are ordinary `//!` lines (harmless to
//! `parse.rs`, which treats `//` as a comment marker) naming what the file
//! is asserting:
//!
//! ```text
//! //! name: <corpus entry name>
//! //! expect: verify-reject | verify-accept
//! //! code: <DiagCode variant, comma-separated if more than one; omitted for verify-accept>
//! ```
//!
//! [decision: a small bespoke directive format rather than reusing
//! `tests/conformance/README.md`'s `name:`/`rule:`/`expect:` grammar
//! verbatim — that format's `expect:` kinds (`parse-ok`, `run-ok`, `trap`,
//! …) describe compiling and running Fors *source*, which none of this
//! corpus is; it hand-writes FMIR text directly, one level below source, as
//! design §4.2 says F0 must ("build the representation and test it against
//! synthetic input before any real input exists")]

use std::path::Path;

use fors_fmir::diag::DiagCode;
use fors_fmir::parse::parse;
use fors_fmir::verify::verify;

fn diag_code_named(name: &str) -> DiagCode {
    match name {
        "MissingSecretField" => DiagCode::MissingSecretField,
        "MissingCtRegion" => DiagCode::MissingCtRegion,
        "DetachWithoutCaptures" => DiagCode::DetachWithoutCaptures,
        "TileOpPresent" => DiagCode::TileOpPresent,
        "TwoTerminators" => DiagCode::TwoTerminators,
        "MemoryOpMissingAliasSeed" => DiagCode::MemoryOpMissingAliasSeed,
        "SecretPropagationViolated" => DiagCode::SecretPropagationViolated,
        "SecretBranchOrIndex" => DiagCode::SecretBranchOrIndex,
        "SecretTrappingOp" => DiagCode::SecretTrappingOp,
        "SecretInContractCheck" => DiagCode::SecretInContractCheck,
        "SecretRaiseCondition" => DiagCode::SecretRaiseCondition,
        "SecretIntrinsicArg" => DiagCode::SecretIntrinsicArg,
        "DeclassifyRequiresUnsafe" => DiagCode::DeclassifyRequiresUnsafe,
        "Malformed" => DiagCode::Malformed,
        other => panic!("unknown DiagCode name in a corpus directive: `{other}`"),
    }
}

struct Directives {
    name: String,
    expect_reject: bool,
    codes: Vec<DiagCode>,
}

fn read_directives(text: &str, file: &Path) -> Directives {
    let mut name = None;
    let mut expect_reject = None;
    let mut codes = Vec::new();
    for line in text.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            continue;
        };
        let rest = rest.trim();
        if let Some(v) = rest.strip_prefix("name:") {
            name = Some(v.trim().to_string());
        } else if let Some(v) = rest.strip_prefix("expect:") {
            expect_reject = Some(match v.trim() {
                "verify-reject" => true,
                "verify-accept" => false,
                other => panic!("{}: unknown `expect:` value `{other}`", file.display()),
            });
        } else if let Some(v) = rest.strip_prefix("code:") {
            codes = v
                .trim()
                .split(',')
                .map(|s| diag_code_named(s.trim()))
                .collect();
        }
    }
    let name = name.unwrap_or_else(|| panic!("{}: missing `//! name:` directive", file.display()));
    let expect_reject = expect_reject
        .unwrap_or_else(|| panic!("{}: missing `//! expect:` directive", file.display()));
    if expect_reject && codes.is_empty() {
        panic!(
            "{}: `expect: verify-reject` needs at least one `//! code:`",
            file.display()
        );
    }
    Directives {
        name,
        expect_reject,
        codes,
    }
}

#[test]
fn negative_corpus_matches_its_directives() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/negative_corpus");
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("fmir"))
        .collect();
    entries.sort();
    assert!(
        entries.len() >= 20,
        "expected at least 20 negative-corpus files, found {}",
        entries.len()
    );

    let mut ran = 0usize;
    for path in &entries {
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
        let directives = read_directives(&text, path);
        let decl = parse(&text).unwrap_or_else(|e| {
            panic!(
                "{} ({}): parse failed: {e}",
                path.display(),
                directives.name
            )
        });
        let diags = verify(&decl);

        if directives.expect_reject {
            for code in &directives.codes {
                assert!(
                    diags.iter().any(|d| d.code == *code),
                    "{} ({}): expected verify() to report {code:?}, got {diags:?}",
                    path.display(),
                    directives.name
                );
            }
        } else {
            assert!(
                diags.is_empty(),
                "{} ({}): expected verify() to accept, got {diags:?}",
                path.display(),
                directives.name
            );
        }
        ran += 1;
    }
    assert_eq!(ran, entries.len());
}
