//! Independent adversarial checks (verifier pass over increment F0): the
//! properties the F0 task asserts, re-tested from outside the builder's own
//! test set — `fmir_hash` invariance/sensitivity under hand-made edits,
//! `verify()`/`dump()`/`fmir_hash()` totality over malformed pools, and the
//! textual round-trip against adversarial input.

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;
use fors_fir::ty::{TY_UNIT, TyId};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::{BlockPool, BlockRow};
use fors_fmir::decl::DeclFmir;
use fors_fmir::encode::fmir_hash;
use fors_fmir::ids::{BlockId, PlaceId, ScopeId, SiteId};
use fors_fmir::inst::InstRow;
use fors_fmir::op::{ArithMode, NO_OPERAND, Op};
use fors_fmir::value::{ValDef, ValRow};
use fors_fmir::verify::verify;

fn plain(op: Op) -> InstRow {
    InstRow {
        op,
        a: NO_OPERAND,
        b: NO_OPERAND,
        c: NO_OPERAND,
        ty: TY_UNIT,
        site: SiteId(0),
    }
}

/// Three blocks, bb0 -> bb1 -> bb2, plus one value and one instruction.
fn chain(order: [u32; 3]) -> DeclFmir {
    let mut d = DeclFmir::empty(DeclKeyId(7), FnSigId(9));
    d.push_val(ValRow::new(TyId(1), false, 0, ValDef::Param(0)));
    d.push_inst(plain(Op::Add(ArithMode::Trap)), AliasSeed::None);
    // `order[i]` is the storage slot that block `i` of the logical chain
    // occupies, i.e. a renumbering of the same CFG.
    let mut rows = vec![None, None, None];
    let term = |op: Op, a: u32| InstRow { a, ..plain(op) };
    rows[order[0] as usize] = Some(term(Op::Br, order[1]));
    rows[order[1] as usize] = Some(term(Op::Br, order[2]));
    rows[order[2] as usize] = Some(plain(Op::Ret));
    let mut blocks = BlockPool::new();
    for r in rows {
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: r.unwrap(),
            scope: ScopeId(0),
        });
    }
    d.blocks = blocks;
    d.entry = BlockId(order[0]);
    d
}

#[test]
fn hash_is_invariant_under_every_block_permutation() {
    let base = fmir_hash(&chain([0, 1, 2]));
    for order in [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        assert_eq!(
            fmir_hash(&chain(order)),
            base,
            "renumbering {order:?} changed fmir_hash"
        );
    }
}

/// A richer declaration whose every interesting field the mutators below
/// poke one at a time.
fn rich() -> DeclFmir {
    let mut d = DeclFmir::empty(DeclKeyId(3), FnSigId(4));
    d.push_val(ValRow::new(TyId(1), false, 0, ValDef::Param(0)));
    d.push_val(ValRow::new(TyId(1), false, 0, ValDef::Param(1)));
    d.push_val(ValRow::new(
        TyId(1),
        false,
        0,
        ValDef::Inst(fors_fmir::ids::InstId(0)),
    ));
    d.push_inst(
        InstRow {
            a: 0,
            b: 1,
            ..plain(Op::Add(ArithMode::Trap))
        },
        AliasSeed::None,
    );
    d.push_inst(
        InstRow {
            a: 0,
            ..plain(Op::Alloc)
        },
        AliasSeed::Own(PlaceId(0)),
    );
    d.sites.push(fors_fmir::site::SiteRow { line: 4, col: 2 });
    d.consts.intern(fors_fmir::constpool::ConstValue::Int(11));
    d
}

#[test]
fn hash_changes_on_every_single_field_edit() {
    let base = fmir_hash(&rich());
    let mutators: Vec<(&str, fn(&mut DeclFmir))> = vec![
        ("decl key", |d| d.decl = DeclKeyId(99)),
        ("sig", |d| d.sig = FnSigId(99)),
        ("is_unsafe_invariant", |d| d.is_unsafe_invariant = true),
        ("val ty", |d| {
            let mut v = fors_fmir::value::ValPool::new();
            v.push(ValRow::new(TyId(5), false, 0, ValDef::Param(0)));
            d.vals = v;
        }),
        ("val secret bit", |d| {
            let mut v = fors_fmir::value::ValPool::new();
            v.push(ValRow::new(TyId(1), true, 0, ValDef::Param(0)));
            d.vals = v;
        }),
        ("val ct region", |d| {
            let mut v = fors_fmir::value::ValPool::new();
            v.push(ValRow::new(TyId(1), false, 3, ValDef::Param(0)));
            d.vals = v;
        }),
        ("inst operand a", |d| {
            let mut p = fors_fmir::inst::InstPool::new();
            p.push(
                InstRow {
                    a: 1,
                    b: 1,
                    ..plain(Op::Add(ArithMode::Trap))
                },
                AliasSeed::None,
            );
            d.insts = p;
        }),
        ("inst opcode", |d| {
            let mut p = fors_fmir::inst::InstPool::new();
            p.push(
                InstRow {
                    a: 0,
                    b: 1,
                    ..plain(Op::Sub(ArithMode::Trap))
                },
                AliasSeed::None,
            );
            d.insts = p;
        }),
        ("inst site", |d| {
            let mut p = fors_fmir::inst::InstPool::new();
            p.push(
                InstRow {
                    a: 0,
                    b: 1,
                    site: SiteId(1),
                    ..plain(Op::Add(ArithMode::Trap))
                },
                AliasSeed::None,
            );
            d.insts = p;
        }),
        ("alias seed", |d| {
            let mut p = fors_fmir::inst::InstPool::new();
            p.push(
                InstRow {
                    a: 0,
                    ..plain(Op::Alloc)
                },
                AliasSeed::Own(PlaceId(2)),
            );
            d.insts = p;
        }),
        ("site row", |d| {
            let mut s = fors_fmir::site::SitePool::new();
            s.push(fors_fmir::site::SiteRow { line: 0, col: 0 });
            s.push(fors_fmir::site::SiteRow { line: 5, col: 2 });
            d.sites = s;
        }),
        ("const value", |d| {
            let mut c = fors_fmir::constpool::ConstPool::new();
            c.intern(fors_fmir::constpool::ConstValue::Int(12));
            d.consts = c;
        }),
        ("block scope", |d| {
            let mut b = BlockPool::new();
            let mut row = d.blocks.row(d.entry);
            row.scope = ScopeId(1);
            d.entry = b.push(row);
            d.blocks = b;
        }),
    ];
    for (name, m) in mutators {
        let mut d = rich();
        m(&mut d);
        assert_ne!(
            fmir_hash(&d),
            base,
            "editing `{name}` did not change fmir_hash"
        );
    }
}

/// Malformed pools every public entry point must survive without panicking
/// (`encode.rs::safe_remap`'s stated rule: "`fmir_hash` must stay total ...
/// over any `DeclFmir` this crate's own types can express").
fn malformed() -> Vec<(&'static str, DeclFmir)> {
    let mut out = Vec::new();

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_inst(
        InstRow {
            a: 9,
            b: 9,
            ..plain(Op::Add(ArithMode::Trap))
        },
        AliasSeed::None,
    );
    out.push(("operand ValId past the end of ValPool", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_val(ValRow::new(TyId(1), true, 0, ValDef::Param(0)));
    let mut blocks = BlockPool::new();
    d.entry = blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            a: 0,
            b: 7,
            c: 8,
            ..plain(Op::CondBr)
        },
        scope: ScopeId(0),
    });
    d.blocks = blocks;
    out.push(("cond_br targets past the end of BlockPool", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let mut blocks = BlockPool::new();
    d.entry = blocks.push(BlockRow {
        first_inst: 3,
        inst_len: 4,
        term: plain(Op::Ret),
        scope: ScopeId(0),
    });
    d.blocks = blocks;
    out.push(("block inst range past the end of InstPool", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_inst(
        InstRow {
            a: 6,
            b: 2,
            ..plain(Op::AggNew)
        },
        AliasSeed::None,
    );
    out.push(("agg_new operand range with start > end", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_inst(
        InstRow {
            a: 5,
            ..plain(Op::Intrinsic)
        },
        AliasSeed::None,
    );
    out.push(("intrinsic call index past the end of `calls`", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.entry = BlockId(4);
    out.push(("entry block id past the end of BlockPool", d));

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    let mut blocks = BlockPool::new();
    d.entry = blocks.push(BlockRow {
        first_inst: 0,
        inst_len: 0,
        term: InstRow {
            a: 3,
            ..plain(Op::SwitchDiscr)
        },
        scope: ScopeId(0),
    });
    d.blocks = blocks;
    out.push(("switch side-table index past the end of `switches`", d));

    out
}

#[test]
fn verify_is_total_over_malformed_pools() {
    for (name, d) in malformed() {
        let _ = verify(&d);
        let _ = name;
    }
}

#[test]
fn hash_and_encode_are_total_over_malformed_pools() {
    for (name, d) in malformed() {
        let _ = fmir_hash(&d);
        let bytes = fors_fmir::encode::to_bytes(&d);
        let back = fors_fmir::encode::from_bytes(&bytes)
            .unwrap_or_else(|e| panic!("`{name}` failed to decode: {e}"));
        assert_eq!(
            fors_fmir::encode::to_bytes(&back),
            bytes,
            "`{name}` did not round-trip"
        );
    }
}

#[test]
fn dump_is_total_over_malformed_pools() {
    for (_name, d) in malformed() {
        let _ = fors_fmir::dump::dump(&d);
    }
}

/// Adversarial textual input: none of it may panic, each must either parse
/// or return a located `ParseError`.
#[test]
fn parse_survives_adversarial_text() {
    let deep = format!(
        "decl 1 sig 1\nblock bb0\nval %x = param 0 ty 1 nosecret ct=0\n{}do ret %x\n",
        "do check_pre %x\n".repeat(400)
    );
    let cases: Vec<String> = vec![
        String::new(),
        "decl 1 sig 1\n".to_string(),
        // no block at all
        "decl 1 sig 1\nval %x = param 0 ty 1 nosecret ct=0\n".to_string(),
        // a block with no terminator
        "decl 1 sig 1\nblock bb0\nval %x = param 0 ty 1 nosecret ct=0\n".to_string(),
        // duplicate value names and duplicate block names
        "decl 1 sig 1\nblock bb0\nval %x = param 0 ty 1 nosecret ct=0\nval %x = param 1 ty 1 nosecret ct=0\ndo ret %x\n".to_string(),
        "decl 1 sig 1\nblock bb0\ndo br bb0\nblock bb0\ndo ret\n".to_string(),
        // unknown ids
        "decl 1 sig 1\nblock bb0\ndo ret %nope\n".to_string(),
        "decl 1 sig 1\nblock bb0\ndo br bb99\n".to_string(),
        // absurd numbers
        "decl 99999999999999999999 sig 1\nblock bb0\ndo unreachable\n".to_string(),
        "decl 1 sig 1\nblock bb0\nval %x = param 999999 ty 4294967296 nosecret ct=99999\ndo unreachable\n".to_string(),
        // garbage tokens
        "\u{0}\u{1}\u{2}".to_string(),
        "decl\ndecl\nblock\nval\ndo\n".to_string(),
        deep,
    ];
    for case in &cases {
        match fors_fmir::parse::parse(case) {
            Ok(d) => {
                // Anything that parses must survive every consumer, and its
                // text must round-trip to the same bytes.
                let _ = verify(&d);
                let _ = fmir_hash(&d);
                let text = fors_fmir::dump::dump(&d);
                let again = fors_fmir::parse::parse(&text)
                    .unwrap_or_else(|e| panic!("re-parsing our own dump failed: {e}\n{text}"));
                assert_eq!(
                    fors_fmir::encode::to_bytes(&again),
                    fors_fmir::encode::to_bytes(&d),
                    "dump/parse round-trip changed the declaration:\n{text}"
                );
            }
            Err(e) => {
                assert!(
                    e.line <= case.lines().count() + 1,
                    "diagnostic line {} is past the end of the input",
                    e.line
                );
            }
        }
    }
}

/// Attack (c): a value row lacking either mandatory field must be rejected
/// however it was produced — struct literal, `with_flags`, or parser.
#[test]
fn rows_lacking_the_mandatory_fields_are_rejected_however_built() {
    use fors_fmir::diag::DiagCode;
    use fors_fmir::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};

    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_val(ValRow {
        ty: TY_UNIT,
        flags: ValFlags(SECRET_UNSPECIFIED),
        ct: CT_UNSPECIFIED,
        def: 0,
    });
    let codes: Vec<DiagCode> = verify(&d).iter().map(|x| x.code).collect();
    assert!(codes.contains(&DiagCode::MissingSecretField), "{codes:?}");
    assert!(codes.contains(&DiagCode::MissingCtRegion), "{codes:?}");

    // `with_flags` is a safe public API and reaches the same sentinel.
    let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
    d.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)).with_flags(SECRET_UNSPECIFIED));
    assert!(
        verify(&d)
            .iter()
            .any(|x| x.code == DiagCode::MissingSecretField),
        "with_flags(SECRET_UNSPECIFIED) slipped past verify()"
    );
}

/// Attack (e): every rejection must carry an anchor that resolves to a
/// source site, not just a code.
#[test]
fn every_rejection_is_source_located() {
    use fors_fmir::diag::Anchor;
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/negative_corpus");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("corpus dir")
        .map(|e| e.expect("entry").path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("fmir"))
        .collect();
    files.sort();
    for path in files {
        let text = std::fs::read_to_string(&path).expect("read");
        let d = fors_fmir::parse::parse(&text).expect("parse");
        for diag in verify(&d) {
            assert_ne!(
                diag.at,
                Anchor::Decl,
                "{}: {:?} is anchored to the whole declaration, not to a site",
                path.display(),
                diag.code
            );
        }
    }
}

/// Attack (g), cross-run determinism: the hash of a fixed declaration is a
/// constant, so any dependence on OS randomness, address layout or hash-map
/// iteration order would make this test flap between runs.
#[test]
fn fmir_hash_of_a_fixed_declaration_is_a_constant() {
    assert_eq!(fmir_hash(&rich()), FIXED_HASH);
    assert_eq!(fmir_hash(&chain([0, 1, 2])), FIXED_CHAIN_HASH);
}

const FIXED_HASH: u128 = 232435784601953027257337958738078189704;
const FIXED_CHAIN_HASH: u128 = 67825440428221145136381568856017431876;
