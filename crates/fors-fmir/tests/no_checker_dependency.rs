//! "a CI-style test asserting this crate does NOT depend on fors-check or
//! fors-syntax (grep its Cargo.toml)" — the task's own words. Design §2's
//! fuller version also greps `crates/fors-fmir/src` itself ("the verifier
//! must not see the checker... the interpreter must not see the CST"); both
//! are cheap, so both run here rather than only the narrower, explicitly
//! required one.

use std::path::Path;

fn forbidden_names() -> [&'static str; 2] {
    ["fors-check", "fors-syntax"]
}

fn forbidden_idents() -> [&'static str; 2] {
    ["fors_check", "fors_syntax"]
}

#[test]
fn cargo_toml_does_not_list_the_checker_or_the_cst_crate() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let text = std::fs::read_to_string(&manifest)
        .unwrap_or_else(|e| panic!("reading {}: {e}", manifest.display()));
    for name in forbidden_names() {
        assert!(
            !text.contains(name),
            "Cargo.toml must not depend on `{name}` (design §2's \"why three\")"
        );
    }
}

/// Belt-and-suspenders over design §2's fuller statement: not one source
/// file under `src/` may even *name* the checker or CST crate, so a
/// dependency could not sneak in through a `path = ".."` workaround either.
#[test]
fn source_never_mentions_the_checker_or_the_cst_crate() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut stack = vec![src];
    let mut checked_any = false;
    while let Some(dir) = stack.pop() {
        for entry in
            std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        {
            let entry = entry.expect("dir entry");
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                continue;
            }
            let text = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("reading {}: {e}", path.display()));
            for ident in forbidden_idents() {
                assert!(
                    !text.contains(ident),
                    "{} must not mention `{ident}`",
                    path.display()
                );
            }
            checked_any = true;
        }
    }
    assert!(
        checked_any,
        "expected to find at least one .rs file under src/"
    );
}
