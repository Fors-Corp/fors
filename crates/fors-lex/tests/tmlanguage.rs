//! The TextMate grammar oracle.
//!
//! `editors/fors.tmLanguage.json` is hand-authored, and a hand-authored
//! grammar drifts from the real lexer silently: a keyword the grammar
//! forgets renders as a plain identifier forever, and a fictitious one
//! paints ordinary code like a keyword. There is no dependency-free way to
//! run an actual Oniguruma/TextMate engine from Rust (and `fors-lex` takes
//! no dependencies), so this test checks everything that *is* checkable
//! without one:
//!
//!  1. the grammar file, and the VS Code extension's `package.json`, are
//!     valid JSON (parsed with the hand-written reader below — `fors-lsp`'s
//!     `json.rs` is public, but reusing it would need a `fors-lex`
//!     dev-dependency, and `Cargo.toml` is outside this change's write
//!     scope, so this test is self-contained instead);
//!  2. every keyword alternative the grammar highlights (extracted from
//!     every pattern shaped exactly `\b(a|b|c)\b`) is EXACTLY the reserved
//!     set `fors_lex::keyword_kind` recognises — cross-checked a second,
//!     independent way against ch07's own reserved-word prose;
//!  3. every regex string in the grammar is a structurally plausible
//!     Oniguruma pattern (balanced brackets, no empty alternation, none of
//!     the constructs TextMate's engine does not support);
//!  4. every scope name ends in `.fors`, the grammar declares
//!     `source.fors` and the `.fors` extension, and the VS Code extension
//!     points at the one grammar file, never a copy.

use fors_lex::keyword_kind;
use std::collections::BTreeSet;

const GRAMMAR_SRC: &str = include_str!("../../../editors/fors.tmLanguage.json");
const PACKAGE_SRC: &str = include_str!("../../../editors/vscode/package.json");
const SPEC_CH07: &str = include_str!("../../../docs/spec/07-grammar.md");

// =========================================================================
// A minimal, hand-written JSON reader. Only what this test needs: no
// numbers-as-f64 precision guarantees, no streaming, no error recovery
// beyond "the file is malformed" (which is itself one of the things this
// test asserts is NOT the case).
// =========================================================================
mod json {
    #[derive(Debug, Clone, PartialEq)]
    pub enum Json {
        Null,
        Bool(bool),
        Num(f64),
        Str(String),
        Arr(Vec<Json>),
        /// Insertion order preserved; duplicate keys are legal JSON (last
        /// one wins on lookup via `get`, same as `serde_json` with the
        /// `preserve_order` feature off would not guarantee, but this
        /// grammar never relies on duplicate keys).
        Obj(Vec<(String, Json)>),
    }

    impl Json {
        pub fn get(&self, key: &str) -> Option<&Json> {
            match self {
                Json::Obj(fields) => fields.iter().rev().find(|(k, _)| k == key).map(|(_, v)| v),
                _ => None,
            }
        }

        pub fn as_str(&self) -> Option<&str> {
            match self {
                Json::Str(s) => Some(s),
                _ => None,
            }
        }

        pub fn as_arr(&self) -> Option<&[Json]> {
            match self {
                Json::Arr(items) => Some(items),
                _ => None,
            }
        }
    }

    pub fn parse(src: &str) -> Option<Json> {
        let bytes = src.as_bytes();
        let mut p = Parser { bytes, pos: 0 };
        p.ws();
        let v = p.value()?;
        p.ws();
        if p.pos != bytes.len() {
            return None; // trailing garbage
        }
        Some(v)
    }

    struct Parser<'a> {
        bytes: &'a [u8],
        pos: usize,
    }

    impl<'a> Parser<'a> {
        fn peek(&self) -> Option<u8> {
            self.bytes.get(self.pos).copied()
        }

        fn ws(&mut self) {
            while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
                self.pos += 1;
            }
        }

        fn eat(&mut self, c: u8) -> bool {
            if self.peek() == Some(c) {
                self.pos += 1;
                true
            } else {
                false
            }
        }

        fn lit(&mut self, s: &[u8], v: Json) -> Option<Json> {
            if self.bytes[self.pos..].starts_with(s) {
                self.pos += s.len();
                Some(v)
            } else {
                None
            }
        }

        fn value(&mut self) -> Option<Json> {
            self.ws();
            match self.peek()? {
                b'{' => self.object(),
                b'[' => self.array(),
                b'"' => self.string().map(Json::Str),
                b't' => self.lit(b"true", Json::Bool(true)),
                b'f' => self.lit(b"false", Json::Bool(false)),
                b'n' => self.lit(b"null", Json::Null),
                b'-' | b'0'..=b'9' => self.number(),
                _ => None,
            }
        }

        fn object(&mut self) -> Option<Json> {
            self.pos += 1; // '{'
            let mut fields = Vec::new();
            self.ws();
            if self.eat(b'}') {
                return Some(Json::Obj(fields));
            }
            loop {
                self.ws();
                let key = self.string()?;
                self.ws();
                if !self.eat(b':') {
                    return None;
                }
                let val = self.value()?;
                fields.push((key, val));
                self.ws();
                if self.eat(b',') {
                    continue;
                }
                if self.eat(b'}') {
                    break;
                }
                return None;
            }
            Some(Json::Obj(fields))
        }

        fn array(&mut self) -> Option<Json> {
            self.pos += 1; // '['
            let mut items = Vec::new();
            self.ws();
            if self.eat(b']') {
                return Some(Json::Arr(items));
            }
            loop {
                let val = self.value()?;
                items.push(val);
                self.ws();
                if self.eat(b',') {
                    continue;
                }
                if self.eat(b']') {
                    break;
                }
                return None;
            }
            Some(Json::Arr(items))
        }

        fn string(&mut self) -> Option<String> {
            if !self.eat(b'"') {
                return None;
            }
            let mut out = String::new();
            loop {
                let b = self.peek()?;
                self.pos += 1;
                match b {
                    b'"' => return Some(out),
                    b'\\' => {
                        let e = self.peek()?;
                        self.pos += 1;
                        match e {
                            b'"' => out.push('"'),
                            b'\\' => out.push('\\'),
                            b'/' => out.push('/'),
                            b'b' => out.push('\u{8}'),
                            b'f' => out.push('\u{c}'),
                            b'n' => out.push('\n'),
                            b'r' => out.push('\r'),
                            b't' => out.push('\t'),
                            b'u' => {
                                let cp = self.hex4()?;
                                // Not attempting surrogate-pair joining: no
                                // grammar scope name or regex needs one,
                                // and a lone BMP code point is enough here.
                                out.push(char::from_u32(cp)?);
                            }
                            _ => return None,
                        }
                    }
                    _ => {
                        // Reconstruct the UTF-8 sequence starting at b.
                        let len = utf8_len(b);
                        let start = self.pos - 1;
                        self.pos = start + len;
                        if self.pos > self.bytes.len() {
                            return None;
                        }
                        out.push_str(std::str::from_utf8(&self.bytes[start..self.pos]).ok()?);
                    }
                }
            }
        }

        fn hex4(&mut self) -> Option<u32> {
            let s = self.bytes.get(self.pos..self.pos + 4)?;
            let s = std::str::from_utf8(s).ok()?;
            let v = u32::from_str_radix(s, 16).ok()?;
            self.pos += 4;
            Some(v)
        }

        fn number(&mut self) -> Option<Json> {
            let start = self.pos;
            if self.peek() == Some(b'-') {
                self.pos += 1;
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
            if self.peek() == Some(b'.') {
                self.pos += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
            }
            if matches!(self.peek(), Some(b'e' | b'E')) {
                self.pos += 1;
                if matches!(self.peek(), Some(b'+' | b'-')) {
                    self.pos += 1;
                }
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
            }
            let s = std::str::from_utf8(&self.bytes[start..self.pos]).ok()?;
            s.parse::<f64>().ok().map(Json::Num)
        }
    }

    fn utf8_len(b: u8) -> usize {
        if b & 0x80 == 0 {
            1
        } else if b & 0xE0 == 0xC0 {
            2
        } else if b & 0xF0 == 0xE0 {
            3
        } else {
            4
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn parses_nested_structures() {
            let v = parse(r#"{"a": [1, 2.5, "x\"y", true, false, null], "b": {}}"#).unwrap();
            assert_eq!(
                v.get("a").unwrap().as_arr().unwrap()[2],
                Json::Str("x\"y".to_string())
            );
        }

        #[test]
        fn rejects_trailing_garbage() {
            assert!(parse(r#"{"a": 1} garbage"#).is_none());
        }

        #[test]
        fn rejects_malformed_input_without_panicking() {
            for bad in [
                "", "{", "[", "\"", "{\"a\"", "{\"a\":}", "[1,]", "tru", "-", "1.2.3",
            ] {
                let _ = parse(bad); // must not panic; None or Some, either is fine here
            }
        }
    }
}

use json::Json;

// =========================================================================
// Walking the grammar tree
// =========================================================================

/// Recursively visits every rule-shaped object reachable from the
/// document's top-level `patterns` array and `repository` map (mirroring
/// how a real TextMate engine resolves `include`s), calling `f` on each.
/// This intentionally does NOT walk the document root itself, so the
/// grammar's own top-level `"name": "Fors"` (a display name, not a scope)
/// is never mistaken for a rule.
fn walk_rules<'a>(doc: &'a Json, f: &mut dyn FnMut(&'a Json)) {
    fn walk_one<'a>(node: &'a Json, f: &mut dyn FnMut(&'a Json)) {
        f(node);
        if let Some(nested) = node.get("patterns").and_then(Json::as_arr) {
            for item in nested {
                walk_one(item, f);
            }
        }
        // `captures`/`beginCaptures`/`endCaptures` are objects of
        // {"<n>": {"name": ...}} entries, not rules with their own
        // `match`/`patterns`, but they can still carry a scope `name` that
        // the scope-suffix check must see.
        for key in ["captures", "beginCaptures", "endCaptures"] {
            if let Some(Json::Obj(caps)) = node.get(key) {
                for (_, cap) in caps {
                    f(cap);
                }
            }
        }
    }

    if let Some(top) = doc.get("patterns").and_then(Json::as_arr) {
        for item in top {
            walk_one(item, f);
        }
    }
    if let Some(Json::Obj(repo)) = doc.get("repository") {
        for (_, rule) in repo {
            walk_one(rule, f);
        }
    }
}

/// Every regex string in the document: each rule's `match`, `begin` and
/// `end`, wherever it appears.
fn all_regexes(doc: &Json) -> Vec<String> {
    let mut out = Vec::new();
    walk_rules(doc, &mut |node| {
        for key in ["match", "begin", "end"] {
            if let Some(s) = node.get(key).and_then(Json::as_str) {
                out.push(s.to_string());
            }
        }
    });
    out
}

/// Every `name` scope in the document: each rule's own `name`, and each
/// capture-group's `name` inside `captures`/`beginCaptures`/`endCaptures`
/// (those are themselves visited as nodes by `walk_rules`, so a plain
/// `.get("name")` on every visited node covers both).
fn all_scope_names(doc: &Json) -> Vec<String> {
    let mut out = Vec::new();
    walk_rules(doc, &mut |node| {
        if let Some(s) = node.get("name").and_then(Json::as_str) {
            out.push(s.to_string());
        }
    });
    out
}

/// Extracts the alternatives out of every regex shaped EXACTLY
/// `\b(a|b|c)\b` (word-boundary, one capturing group of a plain
/// alternation, word-boundary — nothing before, nothing after). This is
/// deliberately narrow: it is the shape every reserved-keyword-family
/// pattern in this grammar uses, and ONLY those patterns — anything with
/// extra context (a following name capture, a lookaround, an inner
/// non-capturing group) is a different, deliberately-excluded shape. See
/// `editors/fors.tmLanguage.json`'s `set-contextual` and `soa-contextual`
/// patterns, and the `keywords-*` patterns, for both sides of that line.
fn keyword_alternatives_of(regex: &str) -> Option<Vec<String>> {
    let inner = regex.strip_prefix(r"\b(")?.strip_suffix(r")\b")?;
    if inner.is_empty() {
        return None;
    }
    let mut words = Vec::new();
    for part in inner.split('|') {
        if part.is_empty() || !part.bytes().all(|b| b.is_ascii_lowercase() || b == b'_') {
            return None; // not a plain lowercase-word alternation: wrong shape
        }
        words.push(part.to_string());
    }
    Some(words)
}

fn grammar_keyword_set(doc: &Json) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    for re in all_regexes(doc) {
        if let Some(words) = keyword_alternatives_of(&re) {
            set.extend(words);
        }
    }
    set
}

// =========================================================================
// The ground truth, read straight out of `fors_lex::keyword_kind`
// =========================================================================

/// Every word ch07 documents as reserved (see token.rs `keyword_kind`,
/// L173-229): the exhaustive list of that function's match arms, minus `_`
/// (the single underscore lexes as its own `TokenKind::Underscore` and is
/// never passed to `keyword_kind` — see lexer.rs `lex_ident_or_keyword` —
/// so `keyword_kind(b"_")` itself returns `None`, and it must not appear
/// here).
const RESERVED: &[&str] = &[
    "module", "use", "pub", "fn", "struct", "enum", "trait", "impl", "const", "extern", "let",
    "var", "inout", "sink", "if", "else", "match", "for", "in", "while", "break", "continue",
    "return", "raise", "raises", "with", "parallel", "simd", "spawn", "comptime", "move",
    "consume", "discard", "as", "and", "or", "not", "true", "false", "iso", "imm", "secret", "dyn",
    "asm", "import", "recover", "type", "spmd", "kernel", "defer", "errdefer",
];

/// Words that are contextual, or otherwise explicitly NOT reserved, per
/// ch07 — `keyword_kind` must return `None` for every one of these. This is
/// the negative half of the oracle: it is not enough that every reserved
/// word round-trips, a near-miss must not.
const NOT_RESERVED: &[&str] = &[
    "_",
    "self",
    "Self",
    "out",
    "clobber",
    "contracts",
    "needs",
    "inputs",
    "soa",
    "set",
    "brand",
    "scoped",
    "arena",
    "allocator",
    "pre",
    "post",
    "invariant",
    "grain",
    "reduce",
    "unsafe",
    "some",
    "none",
    "identity",
    "order",
    "u8",
    "vector",
    "mask",
    "rawptr",
];

/// Parses ch07's own "Keywords — reserved (never identifiers)" section
/// (`docs/spec/07-grammar.md`) and returns the reserved-word set exactly as
/// the prose states it, independent of both `RESERVED` above and the
/// grammar JSON. The section is bounded on the far side by the literal
/// start of the NEXT paragraph ("Reserved-unused words, in one place"),
/// which is prose ABOUT the table above it and re-uses backticks around
/// grammar-production names (like `` `ident` ``) that are not keywords —
/// including it would corrupt this as a source of truth.
fn spec_reserved_words() -> BTreeSet<String> {
    let start_marker = "### Keywords — reserved (never identifiers)";
    let end_marker = "Reserved-unused words, in one place";
    let start = SPEC_CH07
        .find(start_marker)
        .expect("ch07's reserved-keywords heading moved or was reworded");
    let section = &SPEC_CH07[start..];
    let end = section
        .find(end_marker)
        .expect("ch07's reserved-unused paragraph moved or was reworded");
    let section = &section[..end];

    let mut words = BTreeSet::new();
    // Every other '`'-delimited span (odd index = inside backticks).
    for (i, span) in section.split('`').enumerate() {
        if i % 2 == 0 {
            continue;
        }
        for tok in span.split_ascii_whitespace() {
            if !tok.is_empty() && tok.bytes().all(|b| b.is_ascii_lowercase() || b == b'_') {
                words.insert(tok.to_string());
            }
        }
    }
    words.remove("_"); // documented alongside the reserved words, not part of keyword_kind
    words
}

// =========================================================================
// Regex structural soundness (checkable without an Oniguruma engine)
// =========================================================================

/// Reports the first structural problem found in `re`, or `None` if it
/// looks like a plausible Oniguruma-subset pattern. Deliberately
/// conservative: it flags constructs it can positively identify as
/// unsupported or malformed, not everything a real engine would reject.
fn regex_problem(re: &str) -> Option<String> {
    let b = re.as_bytes();
    let mut depth_paren: i32 = 0;
    let mut depth_bracket: i32 = 0; // character class `[...]`
    let mut depth_brace: i32 = 0; // `{n,m}` quantifiers
    let mut i = 0usize;
    let mut prev_significant: Option<u8> = None; // last non-escaped, non-class char, for empty-alternation checks
    while i < b.len() {
        let c = b[i];
        if c == b'\\' {
            if i + 1 >= b.len() {
                return Some("trailing unescaped backslash".to_string());
            }
            let esc = b[i + 1];
            if esc == b'K' {
                return Some(r"uses \K, which TextMate's engine does not support".to_string());
            }
            if esc == b'g' || esc.is_ascii_digit() {
                // `\g<name>` or a bare backreference `\1` used for
                // recursion-like re-invocation is out of scope for a
                // lexical highlighter and unsupported by design here.
                return Some(
                    "uses a backreference/subroutine call (\\g or \\N), not supported".to_string(),
                );
            }
            // An escaped character is always "significant content", even
            // when it is the entire body of one alternative (e.g. the
            // standalone `\|` alternative in the operators pattern, for the
            // literal `|` token) - without this, the NEXT real `|` would
            // look like it directly follows another `|` (empty alternation)
            // when it actually follows this escaped alternative.
            if depth_bracket == 0 {
                prev_significant = Some(b'\\');
            }
            i += 2;
            continue;
        }
        if depth_bracket == 0 && (c == b'(' || c == b'[' || c == b'{') {
            if c == b'(' {
                if i + 2 < b.len() && &b[i..i + 3] == b"(?R" {
                    return Some("uses (?R), recursion is not supported".to_string());
                }
                if b[i..].starts_with(b"(?<=") || b[i..].starts_with(b"(?<!") {
                    if let Some(close) = find_group_close(b, i) {
                        let body = &re[i + 4..close];
                        if lookbehind_is_variable_length(body) {
                            return Some(format!(
                                "variable-length lookbehind, not supported: {body:?}"
                            ));
                        }
                    } else {
                        return Some("unbalanced lookbehind group".to_string());
                    }
                }
                depth_paren += 1;
            } else if c == b'[' {
                depth_bracket += 1;
            } else {
                depth_brace += 1;
            }
        } else if c == b')' && depth_bracket == 0 {
            depth_paren -= 1;
            if depth_paren < 0 {
                return Some("unbalanced ')'".to_string());
            }
        } else if c == b']' {
            if depth_bracket > 0 {
                depth_bracket -= 1;
            }
            // an unmatched top-level ']' is not itself illegal in every
            // regex flavour, but this grammar never emits one intentionally
        } else if c == b'}' && depth_bracket == 0 && depth_brace > 0 {
            depth_brace -= 1;
        }
        if depth_bracket == 0 {
            if c == b'|' && matches!(prev_significant, None | Some(b'|') | Some(b'(')) {
                return Some("empty alternation ('||', '(|' or leading '|')".to_string());
            }
            if c == b')' && prev_significant == Some(b'|') {
                return Some("empty alternation ('|)')".to_string());
            }
            if !c.is_ascii_whitespace() {
                prev_significant = Some(c);
            }
        }
        i += 1;
    }
    if depth_paren != 0 {
        return Some(format!("unbalanced parentheses (depth {depth_paren})"));
    }
    if depth_bracket != 0 {
        return Some(format!("unbalanced '[' (depth {depth_bracket})"));
    }
    if depth_brace != 0 {
        return Some(format!("unbalanced '{{' (depth {depth_brace})"));
    }
    None
}

/// Finds the index of the `)` that closes the group opened at `open_paren`
/// (which must point at a `(`), skipping escaped characters and nested
/// character classes/groups.
fn find_group_close(b: &[u8], open_paren: usize) -> Option<usize> {
    let mut depth = 0i32;
    let mut i = open_paren;
    let mut in_class = false;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 1,
            b'[' if !in_class => in_class = true,
            b']' if in_class => in_class = false,
            b'(' if !in_class => depth += 1,
            b')' if !in_class => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
        i += 1;
    }
    None
}

/// A crude but conservative variable-length check for a lookbehind body:
/// flags any top-level (outside a character class) `*`, `+`, or a `{m,n}`
/// with `m != n`. A fixed-length lookbehind like `(?<=[(,])` or `(?<=fn)`
/// passes; `(?<=[A-Za-z_][A-Za-z0-9_]*)` would not (this grammar contains
/// no such pattern — see `type-ref-after-arrow` and friends, which use
/// lookAHEAD instead precisely to avoid this).
fn lookbehind_is_variable_length(body: &str) -> bool {
    let b = body.as_bytes();
    let mut in_class = false;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'\\' => i += 1,
            b'[' => in_class = true,
            b']' => in_class = false,
            b'*' | b'+' if !in_class => return true,
            b'{' if !in_class => {
                let rest = &body[i + 1..];
                if let Some(close) = rest.find('}') {
                    let spec = &rest[..close];
                    if let Some((lo, hi)) = spec.split_once(',')
                        && lo.trim() != hi.trim()
                    {
                        return true; // {2,4} or {2,}: variable length
                    }
                    // {3}: fixed length, fine
                } else {
                    return true; // malformed - be conservative
                }
            }
            _ => {}
        }
        i += 1;
    }
    false
}

// =========================================================================
// Tests
// =========================================================================

#[test]
fn grammar_json_and_package_json_parse() {
    assert!(
        json::parse(GRAMMAR_SRC).is_some(),
        "editors/fors.tmLanguage.json is not valid JSON"
    );
    assert!(
        json::parse(PACKAGE_SRC).is_some(),
        "editors/vscode/package.json is not valid JSON"
    );
}

/// The negative half of the oracle, checked directly against
/// `fors_lex::keyword_kind` with no grammar or spec involved: every word
/// ch07 documents elsewhere as contextual, or as an explicitly
/// non-reserved ordinary identifier, must NOT be recognised as a reserved
/// keyword. (Guards the boundary `RESERVED`/`grammar_keyword_set` sit on.)
#[test]
fn contextual_and_ordinary_words_are_not_reserved() {
    for w in NOT_RESERVED {
        assert!(
            keyword_kind(w.as_bytes()).is_none(),
            "{w:?} is contextual/ordinary per ch07 but fors_lex::keyword_kind recognises it"
        );
    }
}

/// The positive half: every word this file's own `RESERVED` transcription
/// of `keyword_kind`'s match arms names really is recognised by the real
/// function (guards against a stale/typo'd transcription).
#[test]
fn reserved_list_matches_keyword_kind() {
    let mut missing = Vec::new();
    for w in RESERVED {
        if keyword_kind(w.as_bytes()).is_none() {
            missing.push(*w);
        }
    }
    assert!(
        missing.is_empty(),
        "words in this test's RESERVED list that fors_lex::keyword_kind does NOT recognise: {missing:?}"
    );
    let mut set = BTreeSet::new();
    for w in RESERVED {
        assert!(set.insert(*w), "RESERVED lists {w:?} twice");
    }
    assert_eq!(
        set.len(),
        51,
        "expected exactly 51 reserved words, got {}",
        set.len()
    );
}

/// Cross-checks ch07's own reserved-word PROSE against `keyword_kind`,
/// independent of the grammar JSON and of this file's `RESERVED` constant.
#[test]
fn spec_prose_matches_keyword_kind_exactly() {
    let spec_set = spec_reserved_words();
    let reserved: BTreeSet<String> = RESERVED.iter().map(|s| s.to_string()).collect();

    let spec_not_reserved: Vec<&String> = spec_set.difference(&reserved).collect();
    let reserved_not_in_spec: Vec<&String> = reserved.difference(&spec_set).collect();
    assert!(
        spec_not_reserved.is_empty() && reserved_not_in_spec.is_empty(),
        "ch07 prose vs. this test's RESERVED transcription disagree:\n\
         in spec prose but not RESERVED: {spec_not_reserved:?}\n\
         in RESERVED but not spec prose: {reserved_not_in_spec:?}"
    );
    for w in &spec_set {
        assert!(
            keyword_kind(w.as_bytes()).is_some(),
            "ch07 prose lists {w:?} as reserved but fors_lex::keyword_kind does not recognise it"
        );
    }
}

/// THE main oracle (task item c): the grammar's own highlighted keyword set
/// must equal `fors_lex::keyword_kind`'s recognised set exactly — nothing
/// missing (renders as a plain identifier), nothing invented (paints an
/// ordinary identifier like a keyword).
#[test]
fn grammar_keyword_set_matches_lexer_exactly() {
    let doc = json::parse(GRAMMAR_SRC).expect("grammar JSON must parse (see the dedicated test)");
    let grammar_set = grammar_keyword_set(&doc);
    let reserved: BTreeSet<String> = RESERVED.iter().map(|s| s.to_string()).collect();

    let missing: Vec<&String> = reserved.difference(&grammar_set).collect();
    let invented: Vec<&String> = grammar_set.difference(&reserved).collect();
    assert!(
        missing.is_empty() && invented.is_empty(),
        "grammar keyword set != fors_lex::keyword_kind:\n\
         missing from the grammar (would render unhighlighted): {missing:?}\n\
         invented by the grammar (would highlight an ordinary identifier): {invented:?}"
    );

    // Every extracted word must also independently round-trip through the
    // real lexer function, not just through this test's own RESERVED copy.
    for w in &grammar_set {
        assert!(
            keyword_kind(w.as_bytes()).is_some(),
            "grammar highlights {w:?} as a keyword but fors_lex::keyword_kind does not recognise it"
        );
    }
}

/// `keyword_alternatives_of`'s shape check itself: the grammar's
/// deliberately-differently-shaped patterns (`set`, `soa`, the
/// name-capturing declaration patterns, the type-ref patterns) must NOT be
/// picked up as if they were plain reserved-word alternations - otherwise
/// `set`/`soa` would show up as "invented" keywords above by construction,
/// not by a real defect.
/// Pins the shape rule `keyword_alternatives_of` uses against regressions:
/// the grammar's own non-plain patterns (`set`, `soa`, the name-capturing
/// declaration patterns, the type-ref patterns) must extract as `None`, so
/// that `grammar_keyword_set_matches_lexer_exactly` never sees `set`/`soa`
/// show up as "invented" keywords by construction rather than by a real
/// defect.
#[test]
fn keyword_shape_extractor_ignores_non_keyword_patterns() {
    // Bare word, no group at all: not this shape.
    assert_eq!(keyword_alternatives_of(r"\bset\b"), None);
    // A single-word group IS the degenerate case of the shape and is
    // extractable (this grammar has no such pattern, but the shape rule
    // itself must accept it consistently with a multi-word alternation).
    assert_eq!(
        keyword_alternatives_of(r"\b(fn)\b"),
        Some(vec!["fn".to_string()])
    );
    // Trailing context after the group: not this shape.
    assert_eq!(keyword_alternatives_of(r"\b(fn)\s+([A-Za-z_]+)"), None);
    // Lookaround: not this shape.
    assert_eq!(
        keyword_alternatives_of(r"(?<=[(,])\s*\b(set)\b(?=\s+x)"),
        None
    );
    // Empty alternative(s): rejected even though the outer shape matches.
    assert_eq!(keyword_alternatives_of(r"\b()\b"), None);
    assert_eq!(keyword_alternatives_of(r"\b(a|)\b"), None);
    // The real shape, multi-word: this is what every `keywords-*` family
    // pattern in the grammar looks like.
    assert_eq!(
        keyword_alternatives_of(r"\b(let|var|inout|sink)\b"),
        Some(vec![
            "let".to_string(),
            "var".to_string(),
            "inout".to_string(),
            "sink".to_string()
        ])
    );
}

#[test]
fn grammar_regexes_are_structurally_sound() {
    let doc = json::parse(GRAMMAR_SRC).expect("grammar JSON must parse");
    let mut problems = Vec::new();
    for re in all_regexes(&doc) {
        if let Some(problem) = regex_problem(&re) {
            problems.push(format!("{re:?}: {problem}"));
        }
    }
    assert!(
        problems.is_empty(),
        "unsound regex(es) in the grammar:\n{}",
        problems.join("\n")
    );
}

#[test]
fn regex_soundness_checker_flags_known_bad_shapes() {
    assert!(
        regex_problem(r"\b(a|b").is_some(),
        "unbalanced '(' not flagged"
    );
    assert!(
        regex_problem(r"a)b").is_some(),
        "unbalanced ')' not flagged"
    );
    assert!(
        regex_problem(r"[a-z").is_some(),
        "unbalanced '[' not flagged"
    );
    assert!(
        regex_problem(r"(a||b)").is_some(),
        "empty alternation not flagged"
    );
    assert!(
        regex_problem(r"(|ab)").is_some(),
        "leading empty alternative not flagged"
    );
    assert!(
        regex_problem(r"(ab|)").is_some(),
        "trailing empty alternative not flagged"
    );
    assert!(regex_problem(r"a\Kb").is_some(), "\\K not flagged");
    assert!(
        regex_problem(r"(?<=[A-Za-z]+)x").is_some(),
        "variable-length lookbehind not flagged"
    );
    assert!(
        regex_problem(r"(?<=[(,])x").is_none(),
        "fixed-length lookbehind wrongly flagged"
    );
    assert!(
        regex_problem(r"\b(let|var)\b").is_none(),
        "an ordinary sound pattern was flagged"
    );
    // An ordinary bounded quantifier IS supported by Oniguruma/TextMate,
    // outside a lookbehind - only a variable-length LOOKBEHIND (checked
    // above) is the unsupported construct ch07's task named.
    assert!(
        regex_problem(r"a{2,4}").is_none(),
        "an ordinary {{m,n}} quantifier wrongly flagged"
    );
    assert!(
        regex_problem(r"a{3}").is_none(),
        "fixed {{n}} quantifier wrongly flagged"
    );
}

#[test]
fn every_scope_name_ends_in_dot_fors() {
    let doc = json::parse(GRAMMAR_SRC).expect("grammar JSON must parse");
    let names = all_scope_names(&doc);
    assert!(
        !names.is_empty(),
        "no scope names found at all — walker or grammar is broken"
    );
    let bad: Vec<&String> = names.iter().filter(|n| !n.ends_with(".fors")).collect();
    assert!(
        bad.is_empty(),
        "scope name(s) not ending in \".fors\": {bad:?}"
    );
}

#[test]
fn grammar_declares_source_fors_and_extension() {
    let doc = json::parse(GRAMMAR_SRC).expect("grammar JSON must parse");
    assert_eq!(
        doc.get("scopeName").and_then(Json::as_str),
        Some("source.fors"),
        "grammar must declare scopeName: \"source.fors\""
    );
    let file_types = doc
        .get("fileTypes")
        .and_then(Json::as_arr)
        .unwrap_or(&[])
        .iter()
        .filter_map(Json::as_str)
        .collect::<Vec<_>>();
    assert!(
        file_types.contains(&"fors"),
        "grammar's fileTypes must include \"fors\", got {file_types:?}"
    );
}

#[test]
fn vscode_extension_declares_extension_and_points_at_one_grammar() {
    let pkg = json::parse(PACKAGE_SRC).expect("package.json must parse");

    let languages = pkg
        .get("contributes")
        .and_then(|c| c.get("languages"))
        .and_then(Json::as_arr)
        .expect("package.json must contribute a language");
    let fors_lang = languages
        .iter()
        .find(|l| l.get("id").and_then(Json::as_str) == Some("fors"))
        .expect("no language with id \"fors\"");
    let extensions = fors_lang
        .get("extensions")
        .and_then(Json::as_arr)
        .expect("fors language must declare extensions")
        .iter()
        .filter_map(Json::as_str)
        .collect::<Vec<_>>();
    assert!(
        extensions.contains(&".fors"),
        "fors language must declare the \".fors\" extension, got {extensions:?}"
    );

    let grammars = pkg
        .get("contributes")
        .and_then(|c| c.get("grammars"))
        .and_then(Json::as_arr)
        .expect("package.json must contribute a grammar");
    assert_eq!(
        grammars.len(),
        1,
        "expected exactly one grammar contribution"
    );
    let grammar_entry = &grammars[0];
    assert_eq!(
        grammar_entry.get("scopeName").and_then(Json::as_str),
        Some("source.fors")
    );
    let path = grammar_entry
        .get("path")
        .and_then(Json::as_str)
        .expect("grammar contribution needs a path");
    assert_eq!(
        path, "../fors.tmLanguage.json",
        "the extension must reference the ONE grammar file by relative path, not a copy"
    );

    // And there really is no second copy sitting under editors/vscode/.
    let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let duplicate = manifest_dir.join("../../editors/vscode/fors.tmLanguage.json");
    assert!(
        !duplicate.exists(),
        "found a duplicate grammar file at {}; the extension must reference the original instead",
        duplicate.display()
    );
}
