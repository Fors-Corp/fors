//! The five non-negotiable properties, over the whole conformance corpus
//! (tests/conformance, ~1010 files) and the whole std stub tree.
//!
//! These fixtures are READ-ONLY here: the formatter runs in memory and the
//! files on disk are never touched.

use std::path::{Path, PathBuf};

use fors_fmt::{Status, check_source, format_source, same_tokens};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<PathBuf> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    entries.sort(); // deterministic order, so a failure is reproducible
    for p in entries {
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().is_some_and(|e| e == "fors") {
            out.push(p);
        }
    }
}

fn fixtures() -> Vec<PathBuf> {
    let root = repo_root();
    let mut v = Vec::new();
    walk(&root.join("tests").join("conformance"), &mut v);
    walk(&root.join("std"), &mut v);
    assert!(
        v.len() > 1000,
        "expected the corpus and std, found {} files",
        v.len()
    );
    v
}

/// The `//! expect:` directive of a corpus file, when it has one.
fn expect_directive(src: &[u8]) -> Option<String> {
    for line in src.split(|&b| b == b'\n') {
        let line = String::from_utf8_lossy(line);
        if !line.starts_with("//!") {
            break;
        }
        if let Some(rest) = line
            .trim_start_matches('/')
            .trim_start_matches('!')
            .trim()
            .strip_prefix("expect:")
        {
            return Some(rest.trim().to_string());
        }
    }
    None
}

/// Every comment's text, in order, CR-before-LF removed.
fn comments(src: &[u8]) -> Vec<Vec<u8>> {
    let (t, _) = fors_lex::lex(src);
    (0..t.len())
        .filter(|&i| {
            matches!(
                t.kinds[i],
                fors_lex::TokenKind::LineComment | fors_lex::TokenKind::BlockComment
            )
        })
        .map(|i| {
            t.text(i, src)
                .iter()
                .copied()
                .filter(|&b| b != b'\r')
                .collect()
        })
        .collect()
}

/// Properties 1, 2, 4 and 5 in one sweep.
#[test]
fn lossless_idempotent_tolerant_deterministic() {
    let mut formatted = 0usize;
    let mut unchanged = 0usize;
    let mut parse_failed = 0usize;
    let mut widest = 0usize;
    for path in fixtures() {
        let src = std::fs::read(&path).unwrap();
        let p = path.display();
        let once = format_source(&src);

        // 4. a file that does not parse comes back untouched, with a flag —
        //    and the files that do not parse are EXACTLY the corpus's
        //    `expect: parse-error` files (a formatter that declined a valid
        //    file, or rewrote an invalid one, would hide here otherwise)
        let expects_parse_error = expect_directive(&src).is_some_and(|e| e == "parse-error");
        if once.status == Status::ParseFailed {
            assert_eq!(once.text, src, "{p}: a parse-error file was rewritten");
            assert!(!once.changed);
            assert!(once.parse_diagnostics > 0);
            assert!(
                expects_parse_error,
                "{p}: declined as a parse error but the corpus expects it to parse"
            );
            parse_failed += 1;
            continue;
        }
        assert!(
            !expects_parse_error,
            "{p}: the corpus expects a parse error but the formatter accepted the file"
        );
        assert_eq!(
            once.status,
            Status::Formatted,
            "{p}: formatter declined its own output"
        );

        // 1. lossless: the same tokens, and every comment exactly once,
        //    in the same position relative to the code around it
        assert!(same_tokens(&src, &once.text), "{p}: token stream changed");

        // 2. idempotent, byte for byte
        let twice = format_source(&once.text);
        assert_eq!(twice.status, Status::Formatted, "{p}: second pass declined");
        assert_eq!(
            String::from_utf8_lossy(&twice.text),
            String::from_utf8_lossy(&once.text),
            "{p}: not idempotent"
        );

        // 5. deterministic: same input, same bytes
        assert_eq!(format_source(&src).text, once.text, "{p}: nondeterministic");

        // the check mode agrees with the formatter
        let c = check_source(&src);
        assert_eq!(
            c.formatted, !once.changed,
            "{p}: check disagrees with format"
        );
        assert_eq!(
            c.edits.is_empty(),
            !once.changed,
            "{p}: check produced no edits for a change"
        );
        // and its edits really do produce the formatted text
        let mut patched = src.clone();
        for e in c.edits.iter().rev() {
            patched.splice(e.start as usize..e.end as usize, e.new_text.iter().copied());
        }
        assert_eq!(
            patched, once.text,
            "{p}: applying the check edits did not format the file"
        );

        for line in once.text.split(|&b| b == b'\n') {
            let w = line.iter().filter(|b| (**b & 0xC0) != 0x80).count();
            widest = widest.max(w);
            assert!(
                !line.ends_with(b" ") && !line.ends_with(b"\t"),
                "{p}: trailing whitespace"
            );
            assert!(!line.contains(&b'\r'), "{p}: a CR survived formatting");
        }
        assert!(
            once.text.is_empty() || once.text.ends_with(b"\n"),
            "{p}: no trailing newline"
        );
        assert!(
            !once.text.ends_with(b"\n\n"),
            "{p}: more than one trailing newline"
        );
        // every comment exactly once, in order (same_tokens compares comments
        // too, but a comment-only check names the failure precisely)
        assert_eq!(
            comments(&src),
            comments(&once.text),
            "{p}: comment sequence changed"
        );
        if once.changed {
            formatted += 1
        } else {
            unchanged += 1
        }
    }
    eprintln!(
        "corpus+std: {} reformatted, {} already canonical, {} parse-error files left alone; widest line {widest}",
        formatted, unchanged, parse_failed
    );
}

/// Property 3: resolving the formatted text yields exactly the
/// diagnostics (codes and count) that resolving the original yields —
/// including in files that are deliberately ill-formed.
#[test]
fn diagnostics_are_unchanged() {
    let mut checked = 0usize;
    let mut with_diags = 0usize;
    for path in fixtures() {
        let src = std::fs::read(&path).unwrap();
        let out = format_source(&src);
        if out.status != Status::Formatted || !out.changed {
            continue;
        }
        let is_std = path.components().any(|c| c.as_os_str() == "std");
        let before = resolve_codes(&src, is_std);
        let after = resolve_codes(&out.text, is_std);
        assert_eq!(
            before,
            after,
            "{}: formatting changed the diagnostics",
            path.display()
        );
        checked += 1;
        if !before.is_empty() {
            with_diags += 1;
        }
    }
    eprintln!(
        "diagnostic neutrality: {checked} reformatted files resolved twice, {with_diags} of them with diagnostics"
    );
}

/// Every diagnostic code resolution reports for one file, in order.
fn resolve_codes(src: &[u8], is_std: bool) -> Vec<String> {
    let mut interner = fors_index::Interner::new();
    // One fixed module name for both runs: the comparison is original vs
    // formatted, so any name-dependent diagnostic appears in both.
    let name: fors_index::Segments = vec![interner.intern(b"m")];
    let parse = fors_syntax::parse_file(src);
    let inputs = vec![fors_resolve::FileInput {
        tree: &parse.tree,
        tokens: &parse.tokens,
        source: src,
        name,
    }];
    let pkg: Option<&[u8]> = if is_std { Some(b"std") } else { None };
    let out = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), pkg);
    let mut codes: Vec<String> = parse
        .diags
        .iter()
        .map(|d| d.code.as_str().to_string())
        .collect();
    codes.extend(out.files[0].diagnostics.iter().map(|d| d.code.as_string()));
    codes
}

/// The corpus, perturbed: every whitespace token of every file that parses
/// is rewritten four ways — squashed to one space, exploded to blank lines
/// and tabs, replaced by a block comment, prefixed by a line comment —
/// and every variant that still parses must satisfy the same properties.
/// The corpus is written by careful people; editors are not.
#[test]
fn perturbed_corpus_keeps_the_properties() {
    use fors_lex::TokenKind as T;
    let mut variants = 0usize;
    let mut formatted = 0usize;
    for path in fixtures() {
        let src = std::fs::read(&path).unwrap();
        if format_source(&src).status == Status::ParseFailed {
            continue;
        }
        let (toks, _) = fors_lex::lex(&src);
        for mode in 0..4u8 {
            let mut v: Vec<u8> = Vec::with_capacity(src.len() * 2);
            for i in 0..toks.len() {
                let text = toks.text(i, &src);
                if toks.kinds[i] != T::Whitespace {
                    v.extend_from_slice(text);
                    continue;
                }
                let had_newline = text.contains(&b'\n');
                let had_blank = text.iter().filter(|&&b| b == b'\n').count() >= 2;
                match mode {
                    0 => v.extend_from_slice(if had_blank {
                        b"\n\n"
                    } else if had_newline {
                        b"\n"
                    } else {
                        b" "
                    }),
                    1 => v.extend_from_slice(if had_newline { b"\n\n\t \n\t" } else { b" \t " }),
                    2 => {
                        if had_newline {
                            // after a line comment the block comment needs its
                            // own line, or the line comment swallows it
                            if i > 0 && toks.kinds[i - 1] == T::LineComment {
                                v.extend_from_slice(b"\n/* w\n w */\n");
                            } else {
                                v.extend_from_slice(b" /* w\n w */\n");
                            }
                        } else {
                            v.extend_from_slice(b" /*w*/ ");
                        }
                    }
                    _ => {
                        if had_newline {
                            v.extend_from_slice(b" // c\n");
                        } else {
                            v.extend_from_slice(text);
                        }
                    }
                }
            }
            variants += 1;
            let p = format!("{} (variant {mode})", path.display());
            let once = format_source(&v);
            assert_ne!(
                once.status,
                Status::Bailed,
                "{p}: formatter declined its own output"
            );
            if once.status == Status::ParseFailed {
                assert_eq!(once.text, v, "{p}: a parse-error variant was rewritten");
                continue;
            }
            formatted += 1;
            assert!(same_tokens(&v, &once.text), "{p}: token stream changed");
            assert_eq!(
                comments(&v),
                comments(&once.text),
                "{p}: comment sequence changed"
            );
            let twice = format_source(&once.text);
            assert_eq!(twice.status, Status::Formatted, "{p}: second pass declined");
            assert_eq!(
                String::from_utf8_lossy(&twice.text),
                String::from_utf8_lossy(&once.text),
                "{p}: not idempotent\n--- input ---\n{}",
                String::from_utf8_lossy(&v)
            );
            for line in once.text.split(|&b| b == b'\n') {
                assert!(
                    !line.ends_with(b" ") && !line.ends_with(b"\t"),
                    "{p}: trailing whitespace"
                );
            }
            // the squashed variant carries the same tokens AND the same blank
            // lines as the original (a run of blanks collapses to one either
            // way), so it must format to the very same bytes
            if mode == 0 {
                let canon = format_source(&src).text;
                assert_eq!(
                    String::from_utf8_lossy(&once.text),
                    String::from_utf8_lossy(&canon),
                    "{p}: canonical form depends on the input's whitespace"
                );
            }
        }
    }
    eprintln!("perturbed corpus: {variants} variants, {formatted} formatted");
}
