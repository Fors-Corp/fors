//! The machine format: JSON Lines, hand-written (the repo takes no
//! third-party dependency; `crates/fors-lsp/src/json.rs` does the same for
//! LSP). One record per line, no pretty-printing, no trailing commas, and
//! never a panic: a byte sequence that is not valid UTF-8 becomes U+FFFD
//! rather than an error.

use crate::{LineIndex, Rendered, explain, push_u32};

/// The version of the record shape. Bump it when a field's MEANING
/// changes; adding a field does not need a bump, since a reader that keys
/// on names ignores what it does not know.
pub const SCHEMA: u32 = 1;

/// Escapes `s` into `out` as a JSON string, WITHOUT the surrounding quotes.
///
/// `"` and `\` are escaped; every control character below U+0020 is written
/// as `\u00XX` (no `\n`/`\t` shorthands — one rule is easier for a reader
/// to verify than seven). U+2028 and U+2029 are escaped too: they are legal
/// in JSON but terminate a line in JavaScript, and the JSON Lines reader on
/// the other end is often a JS one.
pub fn escape_into(s: &str, out: &mut String) {
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{2028}' => out.push_str("\\u2028"),
            '\u{2029}' => out.push_str("\\u2029"),
            c if (c as u32) < 0x20 => {
                out.push_str("\\u00");
                const HEX: &[u8; 16] = b"0123456789abcdef";
                let b = c as u32;
                out.push(HEX[(b >> 4) as usize] as char);
                out.push(HEX[(b & 0xf) as usize] as char);
            }
            c => out.push(c),
        }
    }
}

/// [`escape_into`] for bytes that are only probably UTF-8 (a path on a
/// platform whose file names are not, a message built from such a path).
/// Invalid sequences become U+FFFD.
pub fn escape_bytes_into(b: &[u8], out: &mut String) {
    escape_into(&String::from_utf8_lossy(b), out);
}

fn field_str(name: &str, value: &str, out: &mut String) {
    out.push('"');
    out.push_str(name);
    out.push_str("\":\"");
    escape_into(value, out);
    out.push('"');
}

fn write_pos(byte: u32, lines: &LineIndex, out: &mut String) {
    let p = lines.pos(byte);
    out.push_str("{\"byte\":");
    push_u32(p.byte, out);
    out.push_str(",\"line\":");
    push_u32(p.line, out);
    out.push_str(",\"col\":");
    push_u32(p.col, out);
    out.push('}');
}

fn write_range(start: u32, end: u32, lines: &LineIndex, out: &mut String) {
    out.push_str("{\"start\":");
    write_pos(start, lines, out);
    out.push_str(",\"end\":");
    write_pos(end, lines, out);
    out.push('}');
}

/// One `"kind":"diagnostic"` record, with no trailing newline. `lines` is
/// the line index of `r.path`, needed because an edit carries byte offsets
/// only and the record reports every position in all three units.
pub fn diagnostic_line(r: &Rendered, lines: &LineIndex, out: &mut String) {
    out.push_str("{\"schema\":");
    push_u32(SCHEMA, out);
    out.push_str(",\"kind\":\"diagnostic\",");
    field_str("path", &r.path, out);
    // Every diagnostic this compiler raises is an error; `severity` exists
    // so that the day a warning does exist, no reader has to change.
    out.push_str(",\"severity\":\"error\",");
    field_str("code", &r.code, out);
    out.push_str(",\"rule\":");
    match explain::rule_of(&r.code) {
        Some((chapter, number)) => {
            out.push_str("{\"chapter\":\"");
            escape_into(chapter, out);
            out.push_str("\",\"number\":");
            push_u32(u32::from(number), out);
            out.push('}');
        }
        // P (parser) and L (lexer) codes number nothing in the spec's rule
        // lists; `fors explain` still knows them.
        None => out.push_str("null"),
    }
    out.push(',');
    field_str("message", &r.message, out);
    out.push_str(",\"range\":");
    // The rendered start/end already carry their line/col; they were
    // computed from this same source, so re-deriving them would be waste.
    out.push_str("{\"start\":");
    write_pos_of(r.start, out);
    out.push_str(",\"end\":");
    write_pos_of(r.end, out);
    out.push('}');
    out.push_str(",\"fixes\":[");
    for (i, f) in r.fixes.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('{');
        field_str("title", &f.title, out);
        out.push(',');
        field_str("kind", f.kind.as_str(), out);
        out.push(',');
        field_str("applicability", f.applicability().as_str(), out);
        out.push_str(",\"edits\":[");
        for (j, e) in f.edits.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            out.push_str("{\"range\":");
            write_range(e.start, e.end, lines, out);
            out.push(',');
            field_str("replacement", &e.replacement, out);
            out.push('}');
        }
        out.push_str("]}");
    }
    out.push_str("]}");
}

fn write_pos_of(p: crate::Pos, out: &mut String) {
    out.push_str("{\"byte\":");
    push_u32(p.byte, out);
    out.push_str(",\"line\":");
    push_u32(p.line, out);
    out.push_str(",\"col\":");
    push_u32(p.col, out);
    out.push('}');
}

/// The one `"kind":"summary"` record that closes a run, with no trailing
/// newline. `counters` is `Some` exactly when `--count` was given; its
/// order is the caller's and is preserved.
pub fn summary_line(
    errors: usize,
    files: usize,
    counters: Option<&[(&str, u64)]>,
    out: &mut String,
) {
    out.push_str("{\"schema\":");
    push_u32(SCHEMA, out);
    out.push_str(",\"kind\":\"summary\",\"errors\":");
    push_u64(errors as u64, out);
    out.push_str(",\"files\":");
    push_u64(files as u64, out);
    if let Some(c) = counters {
        out.push_str(",\"counters\":{");
        for (i, (k, v)) in c.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            out.push('"');
            escape_into(k, out);
            out.push_str("\":");
            push_u64(*v, out);
        }
        out.push('}');
    }
    out.push('}');
}

fn push_u64(n: u64, out: &mut String) {
    let mut buf = [0u8; 20];
    let mut i = buf.len();
    let mut v = n;
    loop {
        i -= 1;
        buf[i] = b'0' + (v % 10) as u8;
        v /= 10;
        if v == 0 {
            break;
        }
    }
    out.push_str(std::str::from_utf8(&buf[i..]).unwrap_or("0"));
}

/// A JSON string literal, quotes included — for the `explain` records,
/// which are assembled the same way.
pub fn quoted(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    escape_into(s, &mut out);
    out.push('"');
    out
}
