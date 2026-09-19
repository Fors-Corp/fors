//! The Fors lexer: byte-oriented, context-free, maximal-munch, never panics.
//!
//! Each file is lexed independently with no global state, so callers may
//! lex files in parallel. Source is treated as raw bytes end to end;
//! non-ASCII bytes are legal only inside comments and string literals (ch07
//! "Lexical grammar" preamble). `lex` is the UTF-8 boundary: bytes are never
//! decoded while scanning, and one validation pass at the end reports the
//! first invalid sequence hiding inside a comment or string (anywhere else
//! it is already a `StrayByte`).

use crate::diag::{DiagCode, Diagnostic};
use crate::token::{is_legal_suffix, keyword_kind, TokenKind};

// MARC: token packing trade-off - (kind: u8, start: u32) recomputes length
// from the next start; adding a len column costs 4 bytes per token but
// removes the dependent load in diagnostics. Measure on the 100k-line
// corpus before changing.

/// The lossless token stream for one file: struct-of-arrays, no per-token
/// allocation. `kinds[i]` is the i-th token; `starts[i]` is its first byte.
/// `starts` has one more entry than `kinds` — a sentinel equal to the source
/// length — so `starts[i]..starts[i+1]` always bounds token `i`'s text with
/// no branch for the last token.
pub struct Tokens {
    pub kinds: Vec<TokenKind>,
    pub starts: Vec<u32>,
}

impl Tokens {
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }

    /// The source length this stream was built over.
    pub fn source_len(&self) -> u32 {
        *self.starts.last().unwrap_or(&0)
    }

    /// Token `i`'s byte range `[start, end)` into the source it was lexed
    /// from.
    pub fn range(&self, i: usize) -> (u32, u32) {
        (self.starts[i], self.starts[i + 1])
    }

    /// Token `i`'s source text. `source` must be the exact bytes this
    /// stream was lexed from.
    pub fn text<'s>(&self, i: usize, source: &'s [u8]) -> &'s [u8] {
        let (start, end) = self.range(i);
        &source[start as usize..end as usize]
    }
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_continue(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn is_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n')
}

fn is_hex(b: u8) -> bool {
    b.is_ascii_hexdigit()
}

fn is_oct(b: u8) -> bool {
    (b'0'..=b'7').contains(&b)
}

fn is_bin(b: u8) -> bool {
    b == b'0' || b == b'1'
}

fn is_dec(b: u8) -> bool {
    b.is_ascii_digit()
}

/// Scans one run of `dec = digit { ["_"] digit }` (ch07 §4): `pos` must
/// already point at a digit that satisfies `ok`. A single `_` is consumed
/// only when a digit satisfying `ok` immediately follows it, so `1__0`
/// stops after the first `1` (the second `_` is not followed by a digit).
fn scan_digit_run(bytes: &[u8], mut pos: usize, ok: fn(u8) -> bool) -> usize {
    let len = bytes.len();
    while pos < len {
        if ok(bytes[pos]) {
            pos += 1;
        } else if bytes[pos] == b'_' && pos + 1 < len && ok(bytes[pos + 1]) {
            pos += 2;
        } else {
            break;
        }
    }
    pos
}

/// Scans a `\\`-line-oriented multiline string starting at `start` (where
/// `bytes[start..start+2] == "\\\\"`). Consecutive `\\` lines separated only
/// by whitespace merge into one token; anything else (a comment, EOF, real
/// content) ends it (ch07 §6).
fn scan_multiline_string(bytes: &[u8], start: usize) -> usize {
    let len = bytes.len();
    let mut pos = start;
    loop {
        pos += 2; // the two backslashes
        while pos < len && bytes[pos] != b'\n' {
            pos += 1;
        }
        let line_end = pos;
        let mut lookahead = pos;
        while lookahead < len && is_ws(bytes[lookahead]) {
            lookahead += 1;
        }
        if lookahead + 1 < len && bytes[lookahead] == b'\\' && bytes[lookahead + 1] == b'\\' {
            pos = lookahead; // absorb the whitespace and continue into the next line
        } else {
            return line_end;
        }
    }
}

/// Longest-match on the fixed punctuation/operator table (ch07 §7), except
/// `..`, which needs its lexical-error case and is handled by the caller.
fn scan_punct(bytes: &[u8], pos: usize) -> Option<(TokenKind, usize)> {
    use TokenKind::*;
    let b0 = bytes[pos];
    let b1 = bytes.get(pos + 1).copied();

    macro_rules! two {
        ($b:expr, $k:expr) => {
            if b1 == Some($b) {
                return Some(($k, pos + 2));
            }
        };
    }

    match b0 {
        b'(' => return Some((LParen, pos + 1)),
        b')' => return Some((RParen, pos + 1)),
        b'[' => return Some((LBracket, pos + 1)),
        b']' => return Some((RBracket, pos + 1)),
        b'{' => return Some((LBrace, pos + 1)),
        b'}' => return Some((RBrace, pos + 1)),
        b',' => return Some((Comma, pos + 1)),
        b';' => return Some((Semi, pos + 1)),
        b':' => return Some((Colon, pos + 1)),
        b'@' => return Some((At, pos + 1)),
        b'?' => return Some((Question, pos + 1)),
        b'-' => {
            two!(b'>', Arrow);
            two!(b'=', MinusEq);
            return Some((Minus, pos + 1));
        }
        b'=' => {
            two!(b'>', FatArrow);
            two!(b'=', EqEq);
            return Some((Eq, pos + 1));
        }
        b'!' => {
            two!(b'=', NotEq);
            return None; // bare `!` is deliberately not a token
        }
        b'<' => {
            if b1 == Some(b'<') {
                if bytes.get(pos + 2) == Some(&b'=') {
                    return Some((ShlEq, pos + 3));
                }
                return Some((Shl, pos + 2));
            }
            two!(b'=', LtEq);
            return Some((Lt, pos + 1));
        }
        b'>' => {
            if b1 == Some(b'>') {
                if bytes.get(pos + 2) == Some(&b'=') {
                    return Some((ShrEq, pos + 3));
                }
                return Some((Shr, pos + 2));
            }
            two!(b'=', GtEq);
            return Some((Gt, pos + 1));
        }
        b'+' => {
            two!(b'=', PlusEq);
            return Some((Plus, pos + 1));
        }
        b'*' => {
            two!(b'=', StarEq);
            return Some((Star, pos + 1));
        }
        b'/' => {
            two!(b'=', SlashEq);
            return Some((Slash, pos + 1));
        }
        b'%' => {
            two!(b'=', PercentEq);
            return Some((Percent, pos + 1));
        }
        b'&' => {
            two!(b'=', AmpEq);
            return Some((Amp, pos + 1));
        }
        b'|' => {
            two!(b'=', PipeEq);
            return Some((Pipe, pos + 1));
        }
        b'^' => {
            two!(b'=', CaretEq);
            return Some((Caret, pos + 1));
        }
        b'.' => return Some((Dot, pos + 1)),
        _ => None,
    }
}

struct Lexer<'a> {
    bytes: &'a [u8],
    kinds: Vec<TokenKind>,
    starts: Vec<u32>,
    diags: Vec<Diagnostic>,
}

impl<'a> Lexer<'a> {
    fn push(&mut self, kind: TokenKind, start: usize) {
        self.kinds.push(kind);
        self.starts.push(start as u32);
    }

    fn diag(&mut self, start: usize, end: usize, code: DiagCode) {
        self.diags.push(Diagnostic::new(start as u32, end as u32, code));
    }

    fn lex_whitespace(&mut self, start: usize) -> usize {
        let mut pos = start + 1;
        while pos < self.bytes.len() && is_ws(self.bytes[pos]) {
            pos += 1;
        }
        self.push(TokenKind::Whitespace, start);
        pos
    }

    fn lex_line_comment(&mut self, start: usize) -> usize {
        let mut pos = start + 2;
        while pos < self.bytes.len() && self.bytes[pos] != b'\n' {
            pos += 1;
        }
        self.push(TokenKind::LineComment, start);
        pos
    }

    fn lex_block_comment(&mut self, start: usize) -> usize {
        let len = self.bytes.len();
        let mut pos = start + 2;
        let mut depth: u32 = 1;
        let mut terminated = false;
        while pos < len {
            if self.bytes[pos] == b'/' && self.bytes.get(pos + 1) == Some(&b'*') {
                depth += 1;
                pos += 2;
            } else if self.bytes[pos] == b'*' && self.bytes.get(pos + 1) == Some(&b'/') {
                depth -= 1;
                pos += 2;
                if depth == 0 {
                    terminated = true;
                    break;
                }
            } else {
                pos += 1;
            }
        }
        if terminated {
            self.push(TokenKind::BlockComment, start);
        } else {
            self.diag(start, pos, DiagCode::UnterminatedBlockComment);
            self.push(TokenKind::Error, start);
        }
        pos
    }

    fn lex_ident_or_keyword(&mut self, start: usize) -> usize {
        let len = self.bytes.len();
        let mut pos = start + 1;
        while pos < len && is_ident_continue(self.bytes[pos]) {
            pos += 1;
        }
        let word = &self.bytes[start..pos];
        let kind = if word == b"_" {
            TokenKind::Underscore
        } else {
            keyword_kind(word).unwrap_or(TokenKind::Ident)
        };
        self.push(kind, start);
        pos
    }

    fn lex_number(&mut self, start: usize) -> usize {
        let bytes = self.bytes;
        let len = bytes.len();
        let mut is_float = false;
        let mut is_radix = false;
        let mut pos;

        if bytes[start] == b'0' {
            let radix_kind = bytes.get(start + 1).copied();
            let check: Option<fn(u8) -> bool> = match radix_kind {
                Some(b'x') => Some(is_hex),
                Some(b'o') => Some(is_oct),
                Some(b'b') => Some(is_bin),
                _ => None,
            };
            if let Some(ok) = check {
                let digits_start = start + 2;
                if digits_start < len && ok(bytes[digits_start]) {
                    is_radix = true;
                    pos = scan_digit_run(bytes, digits_start, ok);
                } else {
                    pos = scan_digit_run(bytes, start, is_dec);
                }
            } else {
                pos = scan_digit_run(bytes, start, is_dec);
            }
        } else {
            pos = scan_digit_run(bytes, start, is_dec);
        }

        if !is_radix {
            // fractional part: `.` continues the number only if a digit follows
            if pos + 1 < len && bytes[pos] == b'.' && is_dec(bytes[pos + 1]) {
                is_float = true;
                pos = scan_digit_run(bytes, pos + 1, is_dec);
            }
            // exponent: `[eE]` starts one only if followed by a digit, or by
            // `+`/`-` and a digit
            if pos < len && matches!(bytes[pos], b'e' | b'E') {
                let mut q = pos + 1;
                if q < len && matches!(bytes[q], b'+' | b'-') {
                    q += 1;
                }
                if q < len && is_dec(bytes[q]) {
                    is_float = true;
                    pos = scan_digit_run(bytes, q, is_dec);
                }
            }
        }

        // suffix: an identifier run glued directly onto the literal
        let mut suffix_end = pos;
        while suffix_end < len && is_ident_continue(bytes[suffix_end]) {
            suffix_end += 1;
        }
        let suffix = &bytes[pos..suffix_end];
        let kind = if is_float { TokenKind::Float } else { TokenKind::Int };

        if suffix.is_empty() {
            self.push(kind, start);
            pos
        } else if is_legal_suffix(suffix, is_radix, is_float) {
            self.push(kind, start);
            suffix_end
        } else {
            // the literal is valid up to `pos`; the glued run is its own
            // lexical error, not part of the number
            self.push(kind, start);
            self.diag(pos, suffix_end, DiagCode::BadSuffix);
            self.push(TokenKind::Error, pos);
            suffix_end
        }
    }

    fn lex_string(&mut self, start: usize) -> usize {
        let bytes = self.bytes;
        let len = bytes.len();
        let mut pos = start + 1;
        let mut bad_escape = false;
        let mut terminated = false;

        while pos < len {
            match bytes[pos] {
                b'\n' => break,
                b'"' => {
                    pos += 1;
                    terminated = true;
                    break;
                }
                b'\\' => match bytes.get(pos + 1) {
                    Some(b'n') | Some(b'r') | Some(b't') | Some(b'0') | Some(b'\\')
                    | Some(b'"') => pos += 2,
                    Some(b'x') => {
                        let h0 = bytes.get(pos + 2).copied();
                        let h1 = bytes.get(pos + 3).copied();
                        if h0.map(is_hex_byte).unwrap_or(false) && h1.map(is_hex_byte).unwrap_or(false)
                        {
                            pos += 4;
                        } else {
                            bad_escape = true;
                            pos += 2;
                        }
                    }
                    Some(b'u') => {
                        if bytes.get(pos + 2) == Some(&b'{') {
                            let mut q = pos + 3;
                            let digits_start = q;
                            while q < len && bytes[q].is_ascii_hexdigit() {
                                q += 1;
                            }
                            if q > digits_start && bytes.get(q) == Some(&b'}') {
                                pos = q + 1;
                            } else {
                                bad_escape = true;
                                pos = q;
                            }
                        } else {
                            bad_escape = true;
                            pos += 2;
                        }
                    }
                    _ => {
                        bad_escape = true;
                        pos += if bytes.get(pos + 1).is_some() { 2 } else { 1 };
                    }
                },
                _ => pos += 1,
            }
        }

        if terminated {
            if bad_escape {
                self.diag(start, pos, DiagCode::BadEscape);
                self.push(TokenKind::Error, start);
            } else {
                self.push(TokenKind::Str, start);
            }
        } else {
            self.diag(start, pos, DiagCode::UnterminatedString);
            self.push(TokenKind::Error, start);
        }
        pos
    }
}

fn is_hex_byte(b: u8) -> bool {
    b.is_ascii_hexdigit()
}

/// Largest source `lex` accepts. Keeps every byte offset, token index and
/// (at well under four nodes per byte) syntax-tree node index inside `u32`.
pub const MAX_SOURCE_LEN: usize = 1 << 30;

/// Lexes one file's raw bytes into a lossless token stream plus the
/// diagnostics found along the way. Never panics: any input, including
/// invalid UTF-8, unterminated constructs and arbitrary stray bytes,
/// produces a stream and (possibly empty) diagnostic list.
pub fn lex(source: &[u8]) -> (Tokens, Vec<Diagnostic>) {
    let len = source.len();

    if len > MAX_SOURCE_LEN {
        // Report it and stop rather than truncating or wrapping an offset:
        // one error token over the addressable part, then `Eof` as always.
        let end = MAX_SOURCE_LEN as u32;
        return (
            Tokens {
                kinds: vec![TokenKind::Error, TokenKind::Eof],
                starts: vec![0, end, end],
            },
            vec![Diagnostic::new(0, end, DiagCode::FileTooLarge)],
        );
    }

    let mut lx = Lexer {
        bytes: source,
        kinds: Vec::new(),
        starts: Vec::new(),
        diags: Vec::new(),
    };

    let mut pos = 0usize;
    while pos < len {
        let start = pos;
        let b = lx.bytes[pos];
        pos = match b {
            _ if is_ws(b) => lx.lex_whitespace(start),
            b'/' if lx.bytes.get(start + 1) == Some(&b'/') => lx.lex_line_comment(start),
            b'/' if lx.bytes.get(start + 1) == Some(&b'*') => lx.lex_block_comment(start),
            b'\\' if lx.bytes.get(start + 1) == Some(&b'\\') => {
                let end = scan_multiline_string(lx.bytes, start);
                lx.push(TokenKind::MultilineStr, start);
                end
            }
            _ if is_ident_start(b) => lx.lex_ident_or_keyword(start),
            _ if is_dec(b) => lx.lex_number(start),
            b'"' => lx.lex_string(start),
            b'.' if lx.bytes.get(start + 1) == Some(&b'.') => {
                match lx.bytes.get(start + 2) {
                    Some(b'<') => {
                        lx.push(TokenKind::DotDotLt, start);
                        start + 3
                    }
                    Some(b'=') => {
                        lx.push(TokenKind::DotDotEq, start);
                        start + 3
                    }
                    _ => {
                        lx.diag(start, start + 2, DiagCode::BadRangeDots);
                        lx.push(TokenKind::Error, start);
                        start + 2
                    }
                }
            }
            _ => match scan_punct(lx.bytes, start) {
                Some((kind, end)) => {
                    lx.push(kind, start);
                    end
                }
                None => {
                    // one error per run of non-ASCII bytes, not per byte
                    let mut end = start + 1;
                    if b >= 0x80 {
                        while end < len && lx.bytes[end] >= 0x80 {
                            end += 1;
                        }
                    }
                    lx.diag(start, end, DiagCode::StrayByte);
                    lx.push(TokenKind::Error, start);
                    end
                }
            },
        };
    }

    if let Err(e) = std::str::from_utf8(source) {
        let at = e.valid_up_to();
        if !lx.diags.iter().any(|d| d.start as usize <= at && at < d.end as usize) {
            let bad = e.error_len().unwrap_or(len - at);
            lx.diag(at, at + bad, DiagCode::InvalidUtf8);
            lx.diags.sort_by_key(|d| d.start);
        }
    }

    lx.kinds.push(TokenKind::Eof);
    lx.starts.push(len as u32);
    lx.starts.push(len as u32); // sentinel closing the Eof token's (empty) span

    (
        Tokens {
            kinds: lx.kinds,
            starts: lx.starts,
        },
        lx.diags,
    )
}
