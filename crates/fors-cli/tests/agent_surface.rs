//! The agent-facing surface, driven the way a tool drives it: the built
//! binary, over the whole conformance corpus and `std`.
//!
//! T2 (JSON validity and agreement with the text format) and T4 (every
//! code this compiler can emit explains itself) live here; the fix arbiter
//! is `fixes.rs`.

use std::path::{Path, PathBuf};
use std::process::Command;

use fors_lsp::json::{Json, parse};

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .canonicalize()
        .expect("the repository root is two levels above this crate")
}

/// Every corpus entry (`tests/conformance/<chapter>/<entry>`, file or
/// directory, never a `.md`) plus `std`, as paths relative to the root.
pub fn corpus_entries() -> Vec<String> {
    let root = repo_root();
    let mut out = Vec::new();
    let mut chapters: Vec<PathBuf> = std::fs::read_dir(root.join("tests/conformance"))
        .expect("the conformance corpus is present")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    chapters.sort();
    for ch in chapters {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(&ch)
            .expect("a chapter directory is readable")
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_none_or(|e| e != "md"))
            .collect();
        entries.sort();
        for e in entries {
            out.push(rel(&root, &e));
        }
    }
    out.push("std".to_string());
    out
}

fn rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root)
        .unwrap_or(p)
        .to_string_lossy()
        .into_owned()
}

pub fn fors(args: &[&str]) -> (String, String, i32) {
    let out = Command::new(env!("CARGO_BIN_EXE_fors"))
        .current_dir(repo_root())
        .args(args)
        .output()
        .expect("the `fors` binary runs");
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
        out.status.code().unwrap_or(-1),
    )
}

/// Every `.fors` file under `entry` (or `entry` itself when it is one) —
/// what the summary record's `files` must count.
fn fors_file_count(entry: &Path) -> usize {
    if entry.is_file() {
        return usize::from(entry.extension().is_some_and(|e| e == "fors"));
    }
    let mut n = 0;
    let Ok(dir) = std::fs::read_dir(entry) else {
        return 0;
    };
    for e in dir.flatten() {
        let p = e.path();
        if p.is_dir() {
            n += fors_file_count(&p);
        } else if p.extension().is_some_and(|x| x == "fors") {
            n += 1;
        }
    }
    n
}

fn field<'a>(v: &'a Json, key: &str) -> &'a Json {
    v.get(key)
        .unwrap_or_else(|| panic!("record has no `{key}` field: {v}"))
}

fn text_of(v: &Json, key: &str) -> String {
    field(v, key)
        .as_str()
        .unwrap_or_else(|| panic!("`{key}` is not a string: {v}"))
        .to_string()
}

fn pos_of(v: &Json, key: &str) -> (u32, u32, u32) {
    let p = field(v, key);
    (
        field(p, "byte").as_u32().expect("byte is a number"),
        field(p, "line").as_u32().expect("line is a number"),
        field(p, "col").as_u32().expect("col is a number"),
    )
}

/// T2: every stdout line of `fors check --format json` over the whole
/// corpus is valid JSON with the required fields, and the diagnostic
/// records are exactly the text-format lines, in the same order.
#[test]
fn json_records_match_the_text_lines_over_the_whole_corpus() {
    let entries = corpus_entries();
    assert!(entries.len() > 800, "corpus shrank to {}", entries.len());
    let root = repo_root();
    let mut checked_records = 0usize;

    for chunk in entries.chunks(150) {
        let refs: Vec<&str> = chunk.iter().map(String::as_str).collect();

        let mut text_args = vec!["check"];
        text_args.extend_from_slice(&refs);
        let (text_out, _, _) = fors(&text_args);
        let text_lines: Vec<&str> = text_out.lines().collect();

        let mut json_args = vec!["check", "--format", "json"];
        json_args.extend_from_slice(&refs);
        let (json_out, _, _) = fors(&json_args);
        let json_lines: Vec<&str> = json_out.lines().collect();

        assert_eq!(
            json_lines.len(),
            text_lines.len() + 1,
            "one JSON record per text line, plus exactly one summary"
        );

        let mut diagnostics = 0usize;
        for (i, line) in json_lines.iter().enumerate() {
            let v = parse(line.as_bytes())
                .unwrap_or_else(|| panic!("line {i} is not valid JSON: {line}"));
            assert_eq!(field(&v, "schema").as_u32(), Some(1));
            let kind = text_of(&v, "kind");
            if i + 1 == json_lines.len() {
                assert_eq!(kind, "summary", "the last record closes the run");
                assert_eq!(
                    field(&v, "errors").as_u32().expect("errors is a number") as usize,
                    diagnostics
                );
                let want: usize = chunk.iter().map(|e| fors_file_count(&root.join(e))).sum();
                assert_eq!(
                    field(&v, "files").as_u32().expect("files is a number") as usize,
                    want
                );
                continue;
            }
            assert_eq!(kind, "diagnostic");
            let path = text_of(&v, "path");
            let code = text_of(&v, "code");
            let message = text_of(&v, "message");
            assert_eq!(text_of(&v, "severity"), "error");
            let rule = field(&v, "rule");
            match code.as_bytes()[0] {
                b'P' | b'L' => assert_eq!(rule, &Json::Null, "{code} numbers no rule"),
                _ => {
                    assert!(!text_of(rule, "chapter").is_empty());
                    assert!(rule.get("number").and_then(Json::as_u32).is_some());
                }
            }
            let range = field(&v, "range");
            let (_, line_no, col) = pos_of(range, "start");
            let (end_byte, _, _) = pos_of(range, "end");
            let (start_byte, _, _) = pos_of(range, "start");
            assert!(end_byte >= start_byte, "an empty or forward range only");
            for f in field(&v, "fixes").as_arr().expect("fixes is an array") {
                assert!(!text_of(f, "title").is_empty());
                assert!(!text_of(f, "kind").is_empty());
                assert!(matches!(
                    text_of(f, "applicability").as_str(),
                    "machine-applicable" | "maybe-incorrect" | "has-placeholders"
                ));
                let edits = field(f, "edits").as_arr().expect("edits is an array");
                assert!(!edits.is_empty(), "a fix with no edit is not a fix");
                for e in edits {
                    let r = field(e, "range");
                    let (a, _, _) = pos_of(r, "start");
                    let (b, _, _) = pos_of(r, "end");
                    assert!(a <= b, "an edit range runs forward");
                    assert!(field(e, "replacement").as_str().is_some());
                }
            }
            assert_eq!(
                format!("{path}:{line_no}:{col}: error[{code}]: {message}"),
                text_lines[i],
                "record {i} must re-render as its text line"
            );
            diagnostics += 1;
            checked_records += 1;
        }
    }
    assert!(
        checked_records > 500,
        "only {checked_records} diagnostics seen"
    );
}

/// `--format` is validated, not guessed at.
#[test]
fn an_unknown_format_is_an_exit_two_error() {
    let (_, err, code) = fors(&["check", "--format", "yaml", "std"]);
    assert_eq!(code, 2);
    assert!(err.contains("unknown --format"), "{err}");
    let (_, err, code) = fors(&["check", "--format"]);
    assert_eq!(code, 2);
    assert!(err.contains("--format needs a value"), "{err}");
}

/// Every code the lexer can raise. The `match` is the guard: a new variant
/// stops this test compiling until it is listed here too.
fn lex_codes() -> Vec<&'static str> {
    use fors_lex::DiagCode as C;
    let all = [
        C::UnterminatedBlockComment,
        C::UnterminatedString,
        C::BadEscape,
        C::BadSuffix,
        C::BadRangeDots,
        C::StrayByte,
        C::FileTooLarge,
        C::InvalidUtf8,
    ];
    for c in all {
        match c {
            C::UnterminatedBlockComment
            | C::UnterminatedString
            | C::BadEscape
            | C::BadSuffix
            | C::BadRangeDots
            | C::StrayByte
            | C::FileTooLarge
            | C::InvalidUtf8 => {}
        }
    }
    all.iter().map(|c| c.as_str()).collect()
}

fn parse_codes() -> Vec<&'static str> {
    use fors_syntax::DiagCode as C;
    let all = [
        C::Expected,
        C::MissingSemicolon,
        C::UnclosedBrace,
        C::AssignTargetNotPlace,
        C::BitwiseNeedsParens,
        C::ComparisonChained,
        C::NestingTooDeep,
        C::LexError,
        C::UnexpectedToken,
        C::RangeChained,
    ];
    for c in all {
        match c {
            C::Expected
            | C::MissingSemicolon
            | C::UnclosedBrace
            | C::AssignTargetNotPlace
            | C::BitwiseNeedsParens
            | C::ComparisonChained
            | C::NestingTooDeep
            | C::LexError
            | C::UnexpectedToken
            | C::RangeChained => {}
        }
    }
    all.iter().map(|c| c.as_str()).collect()
}

fn index_codes() -> Vec<&'static str> {
    use fors_index::DiagCode as C;
    let all = [
        C::HeaderPathMismatch,
        C::ImportCycle,
        C::SelfImport,
        C::IllegalFileName,
    ];
    for c in all {
        match c {
            C::HeaderPathMismatch | C::ImportCycle | C::SelfImport | C::IllegalFileName => {}
        }
    }
    all.iter().map(|c| c.as_str()).collect()
}

/// Every code the corpus actually produces today.
fn corpus_codes() -> Vec<String> {
    let entries = corpus_entries();
    let mut codes: Vec<String> = Vec::new();
    for chunk in entries.chunks(150) {
        let mut args = vec!["check", "--format", "json"];
        args.extend(chunk.iter().map(String::as_str));
        let (out, _, _) = fors(&args);
        for line in out.lines() {
            let Some(v) = parse(line.as_bytes()) else {
                continue;
            };
            if v.get("kind").and_then(Json::as_str) != Some("diagnostic") {
                continue;
            }
            if let Some(c) = v.get("code").and_then(Json::as_str)
                && !codes.iter().any(|x| x == c)
            {
                codes.push(c.to_string());
            }
        }
    }
    codes.sort();
    codes
}

/// T4: every code that can reach a user explains itself, non-emptily, in
/// both formats, and appears in `--list`.
#[test]
fn every_reachable_code_explains_itself() {
    let mut wanted: Vec<String> = corpus_codes();
    assert!(
        wanted.len() > 40,
        "only {} codes in the corpus",
        wanted.len()
    );
    for c in lex_codes()
        .into_iter()
        .chain(parse_codes())
        .chain(index_codes())
    {
        wanted.push(c.to_string());
    }
    // Every ch09 rule in the checker's traceability table, whether or not
    // the corpus reaches it yet.
    for r in fors_check::rules::CH09_RULES {
        wanted.push(format!("T{:04}", r.rule));
    }
    wanted.sort();
    wanted.dedup();

    let (list_out, _, list_code) = fors(&["explain", "--list"]);
    assert_eq!(list_code, 0);
    let listed: Vec<&str> = list_out
        .lines()
        .filter_map(|l| l.split_whitespace().next())
        .collect();

    for code in &wanted {
        let (out, err, status) = fors(&["explain", code]);
        assert_eq!(status, 0, "`fors explain {code}` failed: {err}");
        assert!(
            out.lines().count() >= 4,
            "`fors explain {code}` is near-empty:\n{out}"
        );
        assert!(
            out.trim_end().ends_with("Fors specification, CC-BY-4.0"),
            "`fors explain {code}` has no licence footer"
        );
        assert!(
            listed.contains(&code.as_str()),
            "`{code}` is missing from `fors explain --list`"
        );

        let (jout, _, jstatus) = fors(&["explain", "--format", "json", code]);
        assert_eq!(jstatus, 0);
        let v = parse(jout.trim_end().as_bytes())
            .unwrap_or_else(|| panic!("`fors explain --format json {code}` is not JSON: {jout}"));
        assert_eq!(v.get("code").and_then(Json::as_str), Some(code.as_str()));
        assert!(
            !v.get("text")
                .and_then(Json::as_str)
                .unwrap_or("")
                .is_empty(),
            "{code} explains to nothing"
        );
    }
}

#[test]
fn an_unknown_code_is_an_exit_two_error() {
    let (out, err, status) = fors(&["explain", "N9999"]);
    assert_eq!(status, 2);
    assert!(out.is_empty());
    assert_eq!(err.lines().count(), 1, "one line, not a wall of text");
    assert!(err.contains("N9999"), "{err}");
    let (_, _, status) = fors(&["explain"]);
    assert_eq!(status, 2);
}

/// `--list` is machine-readable too.
#[test]
fn explain_list_json_is_one_record_per_line() {
    let (out, _, status) = fors(&["explain", "--list", "--format", "json"]);
    assert_eq!(status, 0);
    let mut n = 0;
    for line in out.lines() {
        let v = parse(line.as_bytes()).unwrap_or_else(|| panic!("not JSON: {line}"));
        assert_eq!(v.get("kind").and_then(Json::as_str), Some("code"));
        assert!(v.get("code").and_then(Json::as_str).is_some());
        assert!(
            !v.get("summary")
                .and_then(Json::as_str)
                .unwrap_or("")
                .is_empty()
        );
        n += 1;
    }
    assert!(n > 100, "only {n} codes listed");
}

/// T7: the two INDEPENDENT rule extractors must agree.
///
/// `docs/spec/PACK.md`'s rule index is produced by `tools/specpack/gen.py`
/// (Python) and `fors explain` by `fors_diag::explain` (Rust), from the same
/// chapters. Every citation the pack prints — including a lettered sub-rule
/// like `O0019c`, which the pack indexes as its own line — must therefore be
/// a code `fors explain` answers, or an agent reading the pack follows a
/// citation into `unknown diagnostic code` and has nowhere left to go.
#[test]
fn every_code_the_pack_cites_explains() {
    let pack = std::fs::read_to_string(repo_root().join("docs/spec/PACK.md"))
        .expect("the spec-in-context pack is generated and committed");
    let index = pack
        .split("## 3. Rule index")
        .nth(1)
        .expect("the pack has a rule index")
        .split("\n## ")
        .next()
        .expect("the rule index ends at the next section");

    let mut codes: Vec<&str> = Vec::new();
    for line in index.lines() {
        let Some(code) = line.split_whitespace().next() else {
            continue;
        };
        let b = code.as_bytes();
        let shaped = (b.len() == 5 || (b.len() == 6 && b[5].is_ascii_lowercase()))
            && b[0].is_ascii_uppercase()
            && b[1..5].iter().all(u8::is_ascii_digit);
        if shaped {
            codes.push(code);
        }
    }
    assert!(
        codes.len() > 200,
        "only {} citations in the pack's rule index — the parse above is wrong",
        codes.len()
    );
    assert!(
        codes.iter().any(|c| c.len() == 6),
        "no lettered sub-rule citation in the pack: this test would not be testing anything"
    );

    for code in codes {
        let (out, err, status) = fors(&["explain", code]);
        assert_eq!(
            status, 0,
            "the pack cites `{code}` but `fors explain {code}` fails: {err}"
        );
        assert!(
            out.trim_end().ends_with("Fors specification, CC-BY-4.0"),
            "`fors explain {code}` has no licence footer"
        );
    }
}
