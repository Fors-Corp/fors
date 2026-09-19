//! The lexer hazards from ch07's "Conformance tests" section and the
//! disambiguation rules that are decided in the lexer rather than the
//! parser.

use fors_lex::{lex, DiagCode, TokenKind};

/// Lexes `src` and returns only the non-trivia token kinds (comments and
/// whitespace dropped), which is what most of these hazards care about.
fn kinds(src: &str) -> Vec<TokenKind> {
    let (tokens, _) = lex(src.as_bytes());
    (0..tokens.len())
        .map(|i| tokens.kinds[i])
        .filter(|k| !k.is_trivia() && *k != TokenKind::Eof)
        .collect()
}

fn texts(src: &str) -> Vec<String> {
    let bytes = src.as_bytes();
    let (tokens, _) = lex(bytes);
    (0..tokens.len())
        .filter(|&i| !tokens.kinds[i].is_trivia() && tokens.kinds[i] != TokenKind::Eof)
        .map(|i| String::from_utf8_lossy(tokens.text(i, bytes)).into_owned())
        .collect()
}

#[test]
fn lex_numbers_range_vs_float() {
    use TokenKind::*;
    assert_eq!(kinds("1..<2"), vec![Int, DotDotLt, Int]);
    assert_eq!(texts("1..<2"), vec!["1", "..<", "2"]);
    assert_eq!(kinds("1."), vec![Int, Dot]);
    assert_eq!(kinds("1.e3"), vec![Int, Dot, Ident]);
    assert_eq!(texts("1.e3"), vec!["1", ".", "e3"]);
    assert_eq!(kinds(".5"), vec![Dot, Int]);
    assert_eq!(kinds("1.5..<2.5"), vec![Float, DotDotLt, Float]);
}

#[test]
fn lex_numbers_one_token_each() {
    for src in ["1e3", "1.5e-3", "300u32", "0xFFu8", "1_000"] {
        let ks = kinds(src);
        assert_eq!(ks.len(), 1, "{src:?} should be one token, got {ks:?}");
        assert!(matches!(ks[0], TokenKind::Int | TokenKind::Float));
    }
}

#[test]
fn lex_numbers_rejected() {
    // `1__0`: the second `_` is not followed by a digit, so the dec run
    // stops after `1`; `__0` glues on as an illegal suffix.
    let (tokens, diags) = lex(b"1__0");
    assert!(tokens.kinds.contains(&TokenKind::Error));
    assert!(diags.iter().any(|d| d.code == DiagCode::BadSuffix));

    // `1.5q`: `q` is not a legal float suffix.
    let (tokens, diags) = lex(b"1.5q");
    assert!(tokens.kinds.contains(&TokenKind::Error));
    assert!(diags.iter().any(|d| d.code == DiagCode::BadSuffix));
}

#[test]
fn lex_munch() {
    use TokenKind::*;
    assert_eq!(kinds("&out"), vec![Amp, Ident]);
    assert_eq!(kinds("||"), vec![Pipe, Pipe]);
    assert_eq!(kinds("a<=-b"), vec![Ident, LtEq, Minus, Ident]);
    assert_eq!(texts("a<=-b"), vec!["a", "<=", "-", "b"]);
    assert_eq!(kinds("x=>y"), vec![Ident, FatArrow, Ident]);
    assert_eq!(kinds("f()?.x"), vec![Ident, LParen, RParen, Question, Dot, Ident]);

    let (tokens, diags) = lex(b"..");
    assert!(tokens.kinds.contains(&TokenKind::Error));
    assert!(diags.iter().any(|d| d.code == DiagCode::BadRangeDots));
}

#[test]
fn lex_nested_comment() {
    let src = r#"/* a /* b */ " */ c"#;
    let (tokens, diags) = lex(src.as_bytes());
    assert!(diags.is_empty());
    // the comment should end right after the SECOND `*/`
    let comment_end = src.find("*/ c").unwrap() + 2;
    assert_eq!(tokens.kinds[0], TokenKind::BlockComment);
    assert_eq!(tokens.range(0).1 as usize, comment_end);

    let (tokens, diags) = lex(b"/* unterminated");
    assert_eq!(tokens.kinds[0], TokenKind::Error);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].code, DiagCode::UnterminatedBlockComment);
}

#[test]
fn lex_multiline_string() {
    let src = "\\\\ one\n\\\\ two\n";
    let (tokens, diags) = lex(src.as_bytes());
    assert!(diags.is_empty());
    let ms: Vec<usize> = (0..tokens.len())
        .filter(|&i| tokens.kinds[i] == TokenKind::MultilineStr)
        .collect();
    assert_eq!(ms.len(), 1, "two adjacent \\\\ lines must merge into one token");

    let src2 = "\"a\\\\b\"";
    let (tokens2, diags2) = lex(src2.as_bytes());
    assert!(diags2.is_empty());
    assert_eq!(tokens2.kinds[0], TokenKind::Str);

    // a comment between two `\\` lines ends the literal: two separate tokens
    let src3 = "\\\\ one\n// c\n\\\\ two\n";
    let (tokens3, _) = lex(src3.as_bytes());
    let ms3: Vec<usize> = (0..tokens3.len())
        .filter(|&i| tokens3.kinds[i] == TokenKind::MultilineStr)
        .collect();
    assert_eq!(ms3.len(), 2);
}

#[test]
fn contextual_kw_as_identifier() {
    let src = "let arena = 1; let brand = 2; let out = 3; let set = 4; \
               let scoped = 5; let needs = 6; let pre = 7; let grain = 8;";
    let (_tokens, diags) = lex(src.as_bytes());
    assert!(diags.is_empty());
    for word in ["arena", "brand", "out", "set", "scoped", "needs", "pre", "grain"] {
        assert!(texts(src).contains(&word.to_string()));
    }
}

#[test]
fn reserved_words_are_not_identifiers() {
    for word in ["secret", "in", "true", "false", "iso", "dyn", "not"] {
        let ks = kinds(word);
        assert_eq!(ks.len(), 1);
        assert_ne!(ks[0], TokenKind::Ident, "{word:?} must be a reserved keyword token");
    }
    assert_eq!(kinds("_"), vec![TokenKind::Underscore]);
}

#[test]
fn bang_and_tilde_are_not_tokens() {
    let (tokens, diags) = lex(b"!");
    assert_eq!(tokens.kinds[0], TokenKind::Error);
    assert_eq!(diags[0].code, DiagCode::StrayByte);

    let (tokens, _) = lex(b"!=");
    assert_eq!(tokens.kinds[0], TokenKind::NotEq);

    let (tokens, diags) = lex(b"~");
    assert_eq!(tokens.kinds[0], TokenKind::Error);
    assert_eq!(diags[0].code, DiagCode::StrayByte);
}

#[test]
fn string_escapes() {
    let (tokens, diags) = lex(br#""a\n\t\\\"\x41\u{1F600}""#);
    assert!(diags.is_empty());
    assert_eq!(tokens.kinds[0], TokenKind::Str);

    let (tokens, diags) = lex(br#""bad \q escape""#);
    assert_eq!(tokens.kinds[0], TokenKind::Error);
    assert_eq!(diags[0].code, DiagCode::BadEscape);

    let (tokens, diags) = lex(b"\"unterminated\n rest");
    assert_eq!(tokens.kinds[0], TokenKind::Error);
    assert_eq!(diags[0].code, DiagCode::UnterminatedString);
}

#[test]
fn oversized_source_is_one_diagnostic_and_still_ends_in_eof() {
    // zero pages are mapped lazily: this does not touch 1 GiB of memory
    let src = vec![0u8; fors_lex::MAX_SOURCE_LEN + 1];
    let (tokens, diags) = fors_lex::lex(&src);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].code, fors_lex::DiagCode::FileTooLarge);
    assert_eq!(tokens.kinds, [fors_lex::TokenKind::Error, fors_lex::TokenKind::Eof]);
    assert_eq!(tokens.starts.len(), tokens.kinds.len() + 1);
}

#[test]
fn utf8_boundary() {
    use fors_lex::DiagCode::*;
    let codes = |src: &[u8]| fors_lex::lex(src).1.iter().map(|d| (d.code, d.start, d.end)).collect::<Vec<_>>();
    // legal inside comments and strings
    assert!(codes("// é\n/* ü */ \"ß\" \\\\ ø".as_bytes()).is_empty());
    // one error per run outside them, not one per byte
    assert_eq!(codes("a éü b".as_bytes()), [(StrayByte, 2, 6)]);
    // invalid sequences are caught wherever they hide, first occurrence, exact range
    assert_eq!(codes(b"// \xFF\n"), [(InvalidUtf8, 3, 4)]);
    assert_eq!(codes(b"\"\xE2\x82\" x"), [(InvalidUtf8, 1, 3)]);
    assert_eq!(codes(b"x \xFF y"), [(StrayByte, 2, 3)]);
    assert_eq!(codes(b"/* \xC3"), [(UnterminatedBlockComment, 0, 4)]);
}
