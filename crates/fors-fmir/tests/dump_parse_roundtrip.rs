//! `dump_parse_roundtrip`: the test `dump.rs`'s module docs promise ("every
//! mnemonic this format DOES accept dumps and re-parses losslessly"). It did
//! not exist when the textual form was first written, which is how `dump`
//! shipped emitting parameter lines *below* the blocks that use them — output
//! 14 of the 20 corpus files could not re-parse at all ("unknown value
//! `%v0`"). Three properties, in order of strength:
//!
//! 1. every corpus file's dump re-parses, and `verify()` says the same thing
//!    about the re-parsed declaration as about the original;
//! 2. the round trip reaches a fixed point: once a declaration has been
//!    through `parse(dump(..))` its dump never changes again;
//! 3. for a declaration whose `ValPool` lists its parameters first (what a
//!    lowering pass and this crate's own builders produce), the round trip is
//!    byte-identical, i.e. it preserves `fmir_hash`.
//!
//! Property 3 is deliberately conditional: `dump` prints every parameter
//! above the first `block`, because a `%name` must be introduced before its
//! first use, so a `ValPool` that interleaves parameters *after*
//! instruction-defined values (which only hand-written FMIR text does) comes
//! back order-isomorphic but renumbered. See `dump.rs`'s module docs.

use std::path::{Path, PathBuf};

use fors_fmir::decl::DeclFmir;
use fors_fmir::dump::dump;
use fors_fmir::encode::to_bytes;
use fors_fmir::parse::parse;
use fors_fmir::value::ValDef;
use fors_fmir::verify::verify;

fn corpus() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/negative_corpus");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("fmir"))
        .collect();
    files.sort();
    assert!(files.len() >= 20, "corpus shrank: {} files", files.len());
    files
}

/// Are this declaration's parameters all listed before its first
/// instruction-defined value? (Property 3's precondition.)
fn params_come_first(d: &DeclFmir) -> bool {
    let mut seen_inst_defined = false;
    for (_, row) in d.vals.all_rows() {
        match row.def() {
            ValDef::Inst(_) => seen_inst_defined = true,
            ValDef::Param(_) => {
                if seen_inst_defined {
                    return false;
                }
            }
        }
    }
    true
}

#[test]
fn every_corpus_file_dumps_and_reparses() {
    for path in corpus() {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).expect("read");
        let original = parse(&text).unwrap_or_else(|e| panic!("{name}: parse failed: {e}"));
        let dumped = dump(&original);
        let reparsed = parse(&dumped)
            .unwrap_or_else(|e| panic!("{name}: dump did not re-parse: {e}\n{dumped}"));

        let before: Vec<_> = verify(&original).iter().map(|d| d.code).collect();
        let after: Vec<_> = verify(&reparsed).iter().map(|d| d.code).collect();
        assert_eq!(
            before, after,
            "{name}: verify() disagrees after a round trip"
        );

        // Property 2: `reparsed` is a fixed point. (`dumped` itself need not
        // be — see property 3's caveat: the first dump may renumber an
        // interleaved `ValPool`. What must not happen is drifting forever.)
        let twice = parse(&dump(&reparsed))
            .unwrap_or_else(|e| panic!("{name}: second dump did not re-parse: {e}"));
        assert_eq!(
            dump(&twice),
            dump(&reparsed),
            "{name}: dump/parse never settles"
        );

        // Property 3, where it applies.
        if params_come_first(&original) {
            assert_eq!(
                to_bytes(&reparsed),
                to_bytes(&original),
                "{name}: params-first declaration did not round-trip byte-identically"
            );
        }
    }
}

#[test]
fn a_parameter_only_declaration_round_trips() {
    // The shape that broke: a terminator whose operand is a parameter.
    let text = "decl 1 sig 1\nblock bb0\nval %x = param 0 ty 1 nosecret ct=0\ndo ret %x\n";
    let d = parse(text).expect("parse");
    let dumped = dump(&d);
    let back = parse(&dumped).unwrap_or_else(|e| panic!("{e}\n{dumped}"));
    assert_eq!(to_bytes(&back), to_bytes(&d), "{dumped}");
}
