//! JSON, by hand. The project takes no external crates, so this is the
//! whole of the reader and the writer the protocol needs — enough of
//! RFC 8259 for LSP traffic and nothing more.
//!
//! Objects keep their members in insertion order in a `Vec`: there is no
//! map anywhere, so serialisation is byte-for-byte deterministic and a
//! response never depends on hash iteration order.

/// Nesting deeper than this is rejected by the reader. A recursive-descent
/// parser with no limit is a stack overflow one crafted message away; no
/// LSP message nests past a dozen levels.
const MAX_DEPTH: u32 = 256;

// MARC: numbers are `f64`, like JavaScript's, so a request id above 2^53
// would be echoed back rounded. Ids are small integers or strings in every
// client, and the alternative (a second numeric variant) buys nothing else.
#[derive(Clone, Debug, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    pub fn obj(fields: Vec<(&str, Json)>) -> Json {
        Json::Obj(fields.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    pub fn str(s: impl Into<String>) -> Json {
        Json::Str(s.into())
    }

    pub fn int(n: i64) -> Json {
        Json::Num(n as f64)
    }

    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(v) => v.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_u32(&self) -> Option<u32> {
        match self {
            Json::Num(n) if *n >= 0.0 => Some(*n as u32),
            _ => None,
        }
    }

    pub fn as_arr(&self) -> Option<&[Json]> {
        match self {
            Json::Arr(v) => Some(v),
            _ => None,
        }
    }

    pub fn write(&self, out: &mut String) {
        match self {
            Json::Null => out.push_str("null"),
            Json::Bool(true) => out.push_str("true"),
            Json::Bool(false) => out.push_str("false"),
            Json::Num(n) => {
                if !n.is_finite() {
                    out.push_str("null"); // JSON has no inf/nan
                } else if n.fract() == 0.0 && n.abs() < 9e15 {
                    out.push_str(&format!("{}", *n as i64));
                } else {
                    out.push_str(&format!("{n}"));
                }
            }
            Json::Str(s) => write_string(s, out),
            Json::Arr(v) => {
                out.push('[');
                for (i, e) in v.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    e.write(out);
                }
                out.push(']');
            }
            Json::Obj(v) => {
                out.push('{');
                for (i, (k, e)) in v.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_string(k, out);
                    out.push(':');
                    e.write(out);
                }
                out.push('}');
            }
        }
    }

    pub fn to_string(&self) -> String {
        let mut s = String::new();
        self.write(&mut s);
        s
    }
}

fn write_string(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Reads one JSON value. `None` for anything that is not well-formed
/// JSON, for a number that is not finite, for nesting past `MAX_DEPTH`,
/// and for trailing garbage after the value; never a panic.
pub fn parse(bytes: &[u8]) -> Option<Json> {
    let mut p = Parser { b: bytes, i: 0, depth: 0 };
    p.ws();
    let v = p.value()?;
    p.ws();
    if p.i != p.b.len() {
        return None;
    }
    Some(v)
}

struct Parser<'a> {
    b: &'a [u8],
    i: usize,
    depth: u32,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u8> {
        self.b.get(self.i).copied()
    }

    fn ws(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.i += 1;
        }
    }

    fn eat(&mut self, c: u8) -> bool {
        if self.peek() == Some(c) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn lit(&mut self, s: &[u8], v: Json) -> Option<Json> {
        if self.b[self.i..].starts_with(s) {
            self.i += s.len();
            Some(v)
        } else {
            None
        }
    }

    fn value(&mut self) -> Option<Json> {
        self.ws();
        match self.peek()? {
            b'n' => self.lit(b"null", Json::Null),
            b't' => self.lit(b"true", Json::Bool(true)),
            b'f' => self.lit(b"false", Json::Bool(false)),
            b'"' => self.string().map(Json::Str),
            b'[' => {
                self.i += 1;
                self.depth += 1;
                if self.depth > MAX_DEPTH {
                    return None;
                }
                let mut v = Vec::new();
                self.ws();
                if self.eat(b']') {
                    self.depth -= 1;
                    return Some(Json::Arr(v));
                }
                loop {
                    v.push(self.value()?);
                    self.ws();
                    if self.eat(b',') {
                        continue;
                    }
                    self.depth -= 1;
                    return if self.eat(b']') { Some(Json::Arr(v)) } else { None };
                }
            }
            b'{' => {
                self.i += 1;
                self.depth += 1;
                if self.depth > MAX_DEPTH {
                    return None;
                }
                let mut v = Vec::new();
                self.ws();
                if self.eat(b'}') {
                    self.depth -= 1;
                    return Some(Json::Obj(v));
                }
                loop {
                    self.ws();
                    let k = self.string()?;
                    self.ws();
                    if !self.eat(b':') {
                        return None;
                    }
                    let val = self.value()?;
                    v.push((k, val));
                    self.ws();
                    if self.eat(b',') {
                        continue;
                    }
                    self.depth -= 1;
                    return if self.eat(b'}') { Some(Json::Obj(v)) } else { None };
                }
            }
            _ => self.number(),
        }
    }

    fn number(&mut self) -> Option<Json> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        while matches!(self.peek(), Some(b'0'..=b'9' | b'.' | b'e' | b'E' | b'+' | b'-')) {
            self.i += 1;
        }
        let n: f64 = std::str::from_utf8(&self.b[start..self.i]).ok()?.parse().ok()?;
        // `1e999` parses as infinity; it is not a JSON number and would be
        // written back as one
        if n.is_finite() { Some(Json::Num(n)) } else { None }
    }

    fn string(&mut self) -> Option<String> {
        if !self.eat(b'"') {
            return None;
        }
        let mut s = String::new();
        loop {
            let c = self.peek()?;
            self.i += 1;
            match c {
                b'"' => return Some(s),
                b'\\' => {
                    let e = self.peek()?;
                    self.i += 1;
                    match e {
                        b'"' => s.push('"'),
                        b'\\' => s.push('\\'),
                        b'/' => s.push('/'),
                        b'b' => s.push('\u{8}'),
                        b'f' => s.push('\u{c}'),
                        b'n' => s.push('\n'),
                        b'r' => s.push('\r'),
                        b't' => s.push('\t'),
                        b'u' => {
                            let hi = self.hex4()?;
                            let cp = if (0xD800..0xDC00).contains(&hi) {
                                // a surrogate pair, as JSON spells astral planes
                                if !(self.eat(b'\\') && self.eat(b'u')) {
                                    return None;
                                }
                                let lo = self.hex4()?;
                                // a high surrogate not followed by a low one
                                // is malformed (and `lo - 0xDC00` would
                                // underflow)
                                if !(0xDC00..0xE000).contains(&lo) {
                                    return None;
                                }
                                0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00)
                            } else {
                                hi // a lone low surrogate fails in from_u32
                            };
                            s.push(char::from_u32(cp)?);
                        }
                        _ => return None,
                    }
                }
                _ => {
                    // raw UTF-8 passes through untouched
                    let start = self.i - 1;
                    let len = utf8_len(c);
                    self.i = start + len;
                    s.push_str(std::str::from_utf8(self.b.get(start..self.i)?).ok()?);
                }
            }
        }
    }

    fn hex4(&mut self) -> Option<u32> {
        let s = std::str::from_utf8(self.b.get(self.i..self.i + 4)?).ok()?;
        self.i += 4;
        u32::from_str_radix(s, 16).ok()
    }
}

fn utf8_len(b: u8) -> usize {
    match b {
        0x00..=0x7F => 1,
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        _ => 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let src = r#"{"a":[1,-2.5,true,null,"x\ny"],"b":{"c":"é😀"}}"#;
        let v = parse(src.as_bytes()).unwrap();
        assert_eq!(v.get("a").unwrap().as_arr().unwrap().len(), 5);
        assert_eq!(v.get("b").unwrap().get("c").unwrap().as_str().unwrap(), "é😀");
        let out = v.to_string();
        assert_eq!(parse(out.as_bytes()).unwrap(), v);
    }

    #[test]
    fn escapes_control_characters() {
        assert_eq!(Json::str("a\u{1}b").to_string(), "\"a\\u0001b\"");
    }

    #[test]
    fn malformed_input_is_rejected_not_panicked_on() {
        // a high surrogate followed by a non-surrogate used to underflow
        assert_eq!(parse(br#""\ud800\u0041""#), None);
        assert_eq!(parse(br#""\udc00""#), None); // lone low surrogate
        assert_eq!(parse(br#""\ud83d\ude00""#), Some(Json::str("\u{1F600}")));
        assert_eq!(parse(b"1e999"), None); // not finite
        assert_eq!(parse(b"-"), None);
        assert_eq!(parse(b"{} x"), None); // trailing garbage
        assert_eq!(parse(b"\"\xff\""), None); // invalid UTF-8
        let deep: Vec<u8> = std::iter::repeat_n(b'[', 100_000).collect();
        assert_eq!(parse(&deep), None); // must not overflow the stack
        assert_eq!(parse(b"[[[[[[[[[[1]]]]]]]]]]").is_some(), true);
        assert_eq!(Json::Num(f64::INFINITY).to_string(), "null");
    }
}
