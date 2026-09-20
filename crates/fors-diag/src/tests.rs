//! T5: the three primitives a tool trusts blindly — the did-you-mean
//! ranking, edit application, and JSON escaping.

use crate::{Edit, FixKind, apply_edits, explain, json, suggest};

fn s(v: &[&'static str]) -> Vec<&'static [u8]> {
    v.iter().map(|x| x.as_bytes()).collect()
}

#[test]
fn suggest_accepts_within_threshold_and_rejects_beyond() {
    let c = s(&["counter", "count"]);
    // `couner` -> `counter` is one insertion; len 6, threshold max(1, 2) = 2.
    assert_eq!(suggest(b"couner", c.iter().copied()), Some(&b"counter"[..]));
    // Nothing within max(1, 1) = 1 edit of `ab`.
    assert_eq!(suggest(b"ab", s(&["xyzw"]).iter().copied()), None);
    // A one-character name shares nothing with another one-character
    // name: the edit budget must not make `y` a misspelling of `x`...
    assert_eq!(suggest(b"x", s(&["y"]).iter().copied()), None);
    assert_eq!(suggest(b"x", s(&["xs"]).iter().copied()), None);
    // ...but a case-only difference and a two-letter near miss still are.
    assert_eq!(suggest(b"x", s(&["X"]).iter().copied()), Some(&b"X"[..]));
    assert_eq!(suggest(b"ab", s(&["ac"]).iter().copied()), Some(&b"ac"[..]));
    // An exact match is not a suggestion.
    assert_eq!(suggest(b"count", s(&["count"]).iter().copied()), None);
    assert_eq!(suggest(b"anything", std::iter::empty()), None);
}

#[test]
fn suggest_ranks_a_case_only_difference_first() {
    // `Item` is 4 edits away by distance but differs only in case, while
    // `iten` is one edit away: the case-only difference still wins.
    let c = s(&["iten", "ITEM"]);
    assert_eq!(suggest(b"item", c.iter().copied()), Some(&b"ITEM"[..]));
    // ...and it is accepted even though 4 > max(1, 4/3) = 1.
    assert_eq!(
        suggest(b"item", s(&["ITEM"]).iter().copied()),
        Some(&b"ITEM"[..])
    );
}

#[test]
fn suggest_is_independent_of_candidate_order() {
    // Two candidates at distance 1: the lexicographically smaller wins,
    // whichever order they arrive in.
    let a = s(&["cat", "bat"]);
    let b = s(&["bat", "cat"]);
    assert_eq!(suggest(b"mat", a.iter().copied()), Some(&b"bat"[..]));
    assert_eq!(suggest(b"mat", b.iter().copied()), Some(&b"bat"[..]));
}

#[test]
fn suggest_counts_a_transposition_as_one_edit() {
    assert_eq!(
        suggest(b"lenght", s(&["length"]).iter().copied()),
        Some(&b"length"[..])
    );
}

#[test]
fn apply_edits_applies_in_offset_order() {
    let src = b"let x = 1\nlet y = 2\n";
    let out = apply_edits(src, &[Edit::insert(19, ";"), Edit::insert(9, ";")]).unwrap();
    assert_eq!(out, b"let x = 1;\nlet y = 2;\n");
}

#[test]
fn apply_edits_rejects_overlap_and_out_of_range() {
    let src = b"abcdef";
    assert_eq!(
        apply_edits(src, &[Edit::new(0, 3, "X"), Edit::new(2, 4, "Y")]),
        None
    );
    assert_eq!(apply_edits(src, &[Edit::new(0, 99, "X")]), None);
    assert_eq!(apply_edits(src, &[Edit::new(4, 2, "X")]), None);
    // Touching ranges are not overlapping.
    assert_eq!(
        apply_edits(src, &[Edit::new(0, 3, "X"), Edit::new(3, 6, "Y")]),
        Some(b"XY".to_vec())
    );
    // Two insertions at one offset keep the order they were given in.
    assert_eq!(
        apply_edits(src, &[Edit::insert(0, "1"), Edit::insert(0, "2")]),
        Some(b"12abcdef".to_vec())
    );
}

#[test]
fn apply_edits_of_nothing_is_the_source() {
    assert_eq!(apply_edits(b"abc", &[]), Some(b"abc".to_vec()));
}

#[test]
fn json_escapes_quotes_backslashes_and_every_control_character() {
    let mut out = String::new();
    json::escape_into("a\"b\\c", &mut out);
    assert_eq!(out, "a\\\"b\\\\c");

    for b in 0u8..0x20 {
        let mut out = String::new();
        json::escape_into(&(b as char).to_string(), &mut out);
        assert_eq!(out, format!("\\u00{b:02x}"), "control byte {b:#04x}");
    }
}

#[test]
fn json_escapes_the_javascript_line_terminators() {
    let mut out = String::new();
    json::escape_into("a\u{2028}b\u{2029}c", &mut out);
    assert_eq!(out, "a\\u2028b\\u2029c");
}

#[test]
fn json_replaces_invalid_utf8_rather_than_failing() {
    let mut out = String::new();
    json::escape_bytes_into(&[b'a', 0xff, 0xfe, b'b'], &mut out);
    assert_eq!(out, "a\u{fffd}\u{fffd}b");
}

#[test]
fn json_leaves_ordinary_text_alone() {
    let mut out = String::new();
    json::escape_into("module `app.client` — ok", &mut out);
    assert_eq!(out, "module `app.client` — ok");
}

#[test]
fn every_fix_kind_has_a_distinct_stable_name() {
    let mut names: Vec<&str> = FixKind::ALL.iter().map(|k| k.as_str()).collect();
    names.sort_unstable();
    let n = names.len();
    names.dedup();
    assert_eq!(names.len(), n);
}

#[test]
fn rule_of_maps_letters_to_chapters_and_nulls_p_and_l() {
    assert_eq!(explain::rule_of("N0014"), Some(("08-names", 14)));
    assert_eq!(explain::rule_of("T0042"), Some(("09-types", 42)));
    assert_eq!(explain::rule_of("A0008"), Some(("04-authority", 8)));
    assert_eq!(explain::rule_of("P0002"), None);
    assert_eq!(explain::rule_of("L0000"), None);
    assert_eq!(explain::rule_of("nonsense"), None);
}

#[test]
fn explain_quotes_the_chapter_verbatim() {
    let e = explain::explain("N0014").expect("N0014 explains");
    assert!(e.text.starts_with("14. **N0014**"), "{}", e.text);
    assert_eq!(e.spec_path, "docs/spec/08-names.md");
    assert_eq!(e.rule, Some(14));
    assert!(e.chapter_title.starts_with("Chapter 8"));
    assert!(explain::render_text(&e).ends_with("Fors specification, CC-BY-4.0\n"));
}

#[test]
fn explain_knows_the_parser_and_lexer_tables() {
    let e = explain::explain("P0002").expect("P0002 explains");
    assert_eq!(e.rule, None);
    assert!(!e.text.is_empty());
    assert!(explain::explain("L0007").is_some());
    assert!(explain::explain("P0099").is_none());
    assert!(explain::explain("Z0001").is_none());
}

#[test]
fn explain_list_is_non_empty_and_summarised() {
    let rows = explain::list();
    assert!(rows.len() > 100, "only {} rows", rows.len());
    for (code, summary) in &rows {
        assert!(!summary.trim().is_empty(), "{code} has no summary");
        assert!(!summary.contains('\n'), "{code} summary is multi-line");
    }
}

#[test]
fn line_index_agrees_with_the_linear_scan_at_every_offset() {
    // Empty, no trailing newline, CRLF, blank lines, multi-byte text: the
    // index must be the scan, only faster — past the end included.
    let sources: [&[u8]; 5] = [
        b"",
        b"one line",
        b"a\r\nb\r\n",
        b"\n\n\nx\n",
        "let \u{e9} = \"\u{1f600}\";\nnext\n".as_bytes(),
    ];
    for src in sources {
        let ix = crate::LineIndex::new(src);
        for off in 0..=(src.len() as u32 + 3) {
            assert_eq!(ix.pos(off), crate::pos(src, off), "offset {off} of {src:?}");
        }
    }
}
