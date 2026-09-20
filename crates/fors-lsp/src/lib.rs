//! `fors-lsp`: the language-server skeleton for Fors.
//!
//! Std only, no external crates: the JSON reader/writer ([`json`]) and the
//! `Content-Length` framing below are written out here rather than taken
//! from `serde`/`tower-lsp`, which is a project constraint.
//!
//! What it serves today, all of it off the same frontend the compiler
//! uses (lex -> parse -> resolve) and the canonical formatter:
//!
//! * `initialize` / `initialized` / `shutdown` / `exit`
//! * `textDocument/didOpen` / `didChange` (full sync) / `didClose`, each
//!   answered with a fresh `textDocument/publishDiagnostics`
//! * `textDocument/formatting` and `textDocument/rangeFormatting`, as the
//!   minimal line edits `fors-fmt` computes — never one edit replacing the
//!   whole file, so the editor keeps the cursor and the undo stack
//! * `textDocument/documentSymbol`, from the per-file declaration table
//! * `textDocument/foldingRange`, from the lossless CST
//!
//! [`Server::handle`] is a pure function from one message to the messages
//! that answer it, so every behaviour here is testable without a pipe;
//! `end_to_end_over_a_scripted_stream` drives [`serve`] the way an editor
//! drives the binary.
//!
//! Robustness rules, each with a test: no input can panic the loop (a
//! malformed body is answered with `-32700` and the loop goes on; the JSON
//! reader bounds nesting and rejects bad surrogates and infinities; the
//! framing rejects a `Content-Length` above [`MAX_MESSAGE`] instead of
//! allocating it); a message with no `method` is a client response and is
//! ignored, never answered; after `shutdown` every request is `-32600`
//! until `exit`. Positions cross the wire in UTF-16 code units through a
//! per-request [`LineIndex`].

pub mod json;

use fors_index::{DeclKind, Interner, Segments};
use json::Json;

// ---- position mapping -------------------------------------------------
// LSP counts lines from 0 and characters in UTF-16 code units; the
// compiler counts bytes. Everything crossing the wire goes through here.

/// Byte offset of the start of every line, built once per request.
///
/// MARC: one table per request, not a scan per position. Every response
/// converts two offsets per item (folds, symbols, diagnostics, edits), so a
/// per-call scan from the start of the buffer is O(items * bytes): a
/// 1 MB file with 20k folds would read 40 GB. With the table a conversion
/// is a binary search plus a walk over one line, and no allocation.
pub struct LineIndex {
    starts: Vec<u32>,
}

impl LineIndex {
    pub fn new(src: &[u8]) -> Self {
        let mut starts = Vec::with_capacity(src.len() / 32 + 1);
        starts.push(0);
        for (i, &b) in src.iter().enumerate() {
            if b == b'\n' {
                starts.push(i as u32 + 1);
            }
        }
        LineIndex { starts }
    }

    /// Byte offset -> `(line, utf16 character)`, clamped to the buffer.
    pub fn pos(&self, src: &[u8], off: u32) -> (u32, u32) {
        let off = off.min(src.len() as u32);
        let line = self.starts.partition_point(|&s| s <= off) - 1;
        let col = utf16_units(&src[self.starts[line] as usize..off as usize]);
        (line as u32, col)
    }

    /// `(line, utf16 character)` -> byte offset, clamped to the line (a
    /// character past the end of the line maps to the line's end, and a
    /// line past the end of the buffer to the buffer's end). A character
    /// inside a surrogate pair maps past that pair.
    pub fn offset(&self, src: &[u8], line: u32, character: u32) -> u32 {
        let Some(&at) = self.starts.get(line as usize) else {
            return src.len() as u32;
        };
        let end = self
            .starts
            .get(line as usize + 1)
            .map_or(src.len(), |&n| n as usize - 1);
        let line_bytes = &src[at as usize..end];
        let mut used = 0u32;
        let mut i = 0usize;
        while i < line_bytes.len() {
            if used >= character {
                break;
            }
            let (len, units) = utf8_char(line_bytes[i]);
            used += units;
            i = (i + len).min(line_bytes.len());
        }
        at + i as u32
    }
}

/// Byte length and UTF-16 width of the character whose lead byte is `b`.
/// A stray continuation byte counts as one byte, one unit.
fn utf8_char(b: u8) -> (usize, u32) {
    match b {
        0x00..=0x7F => (1, 1),
        0xC0..=0xDF => (2, 1),
        0xE0..=0xEF => (3, 1),
        0xF0..=0xF7 => (4, 2), // outside the BMP: a surrogate pair
        _ => (1, 1),
    }
}

/// UTF-16 length of a UTF-8 slice, without decoding it: every byte that is
/// not a continuation byte starts a character, and a 4-byte character is
/// two units.
fn utf16_units(bytes: &[u8]) -> u32 {
    let mut n = 0u32;
    for &b in bytes {
        if (b & 0xC0) != 0x80 {
            n += 1;
            if b >= 0xF0 {
                n += 1;
            }
        }
    }
    n
}

/// Byte offset -> `(line, utf16 character)`. Builds a [`LineIndex`]; a
/// caller with more than one position to convert should build its own.
pub fn offset_to_pos(src: &[u8], off: u32) -> (u32, u32) {
    LineIndex::new(src).pos(src, off)
}

/// `(line, utf16 character)` -> byte offset, clamped to the buffer.
pub fn pos_to_offset(src: &[u8], line: u32, character: u32) -> u32 {
    LineIndex::new(src).offset(src, line, character)
}

fn range_json(ix: &LineIndex, src: &[u8], start: u32, end: u32) -> Json {
    let (sl, sc) = ix.pos(src, start);
    let (el, ec) = ix.pos(src, end);
    Json::obj(vec![
        (
            "start",
            Json::obj(vec![
                ("line", Json::int(sl as i64)),
                ("character", Json::int(sc as i64)),
            ]),
        ),
        (
            "end",
            Json::obj(vec![
                ("line", Json::int(el as i64)),
                ("character", Json::int(ec as i64)),
            ]),
        ),
    ])
}

// ---- the server -------------------------------------------------------

struct Doc {
    uri: String,
    text: Vec<u8>,
    version: i64,
}

#[derive(Default)]
pub struct Server {
    /// Open documents, in the order they were opened. A `Vec`, not a map:
    /// nothing here is big enough to need hashing, and every response stays
    /// order-deterministic.
    docs: Vec<Doc>,
    pub shutdown_requested: bool,
    pub exited: bool,
}

impl Server {
    pub fn new() -> Self {
        Server::default()
    }

    fn doc(&self, uri: &str) -> Option<&Doc> {
        self.docs.iter().find(|d| d.uri == uri)
    }

    /// Answers one incoming message with the messages to send back: a
    /// response (when the message carried an `id`) and any notifications.
    pub fn handle(&mut self, msg: &Json) -> Vec<Json> {
        let id = msg.get("id").cloned();
        let params = msg.get("params").cloned().unwrap_or(Json::Null);
        let mut out = Vec::new();
        let method = match msg.get("method").and_then(|m| m.as_str()) {
            Some(m) => m,
            None => {
                // A message with no method is a RESPONSE to a request this
                // server sent (it sends none, so nothing is waiting for it)
                // or a malformed request. Answering a response with an error
                // would make the client answer that, and so on forever.
                if id.is_some() && msg.get("result").is_none() && msg.get("error").is_none() {
                    out.push(error(id, -32600, "request without a method"));
                }
                return out;
            }
        };
        // MARC: per the LSP spec, every request after `shutdown` must be
        // rejected (InvalidRequest) until `exit`; `exit` itself and bare
        // notifications are unaffected.
        if self.shutdown_requested && method != "exit" {
            if id.is_some() {
                out.push(error(id, -32600, "server is shutting down"));
            }
            return out;
        }
        match method {
            "initialize" => out.push(response(id, self.initialize())),
            "initialized" => {}
            "shutdown" => {
                self.shutdown_requested = true;
                out.push(response(id, Json::Null));
            }
            "exit" => self.exited = true,
            "textDocument/didOpen" => {
                if let Some(td) = params.get("textDocument") {
                    let uri = td
                        .get("uri")
                        .and_then(|u| u.as_str())
                        .unwrap_or("")
                        .to_string();
                    let text = td
                        .get("text")
                        .and_then(|t| t.as_str())
                        .unwrap_or("")
                        .as_bytes()
                        .to_vec();
                    let version = td.get("version").and_then(|v| v.as_u32()).unwrap_or(0) as i64;
                    self.docs.retain(|d| d.uri != uri);
                    self.docs.push(Doc {
                        uri: uri.clone(),
                        text,
                        version,
                    });
                    out.push(self.diagnostics(&uri));
                }
            }
            "textDocument/didChange" => {
                let uri = uri_of(&params);
                let version = params
                    .get("textDocument")
                    .and_then(|t| t.get("version"))
                    .and_then(|v| v.as_u32())
                    .unwrap_or(0) as i64;
                // full sync only: the last change with no range is the document
                if let Some(changes) = params.get("contentChanges").and_then(|c| c.as_arr())
                    && let Some(full) = changes.iter().rev().find(|c| c.get("range").is_none())
                {
                    let text = full
                        .get("text")
                        .and_then(|t| t.as_str())
                        .unwrap_or("")
                        .as_bytes()
                        .to_vec();
                    if let Some(d) = self.docs.iter_mut().find(|d| d.uri == uri) {
                        d.text = text;
                        d.version = version;
                    }
                }
                out.push(self.diagnostics(&uri));
            }
            "textDocument/didClose" => {
                let uri = uri_of(&params);
                self.docs.retain(|d| d.uri != uri);
                out.push(notification(
                    "textDocument/publishDiagnostics",
                    Json::obj(vec![
                        ("uri", Json::str(uri)),
                        ("diagnostics", Json::Arr(Vec::new())),
                    ]),
                ));
            }
            "textDocument/formatting" => {
                let uri = uri_of(&params);
                out.push(response(id, self.format(&uri, None)));
            }
            "textDocument/rangeFormatting" => {
                let uri = uri_of(&params);
                let r = params.get("range").cloned();
                out.push(response(id, self.format(&uri, r)));
            }
            "textDocument/documentSymbol" => {
                let uri = uri_of(&params);
                out.push(response(id, self.symbols(&uri)));
            }
            "textDocument/foldingRange" => {
                let uri = uri_of(&params);
                out.push(response(id, self.folding(&uri)));
            }
            _ => {
                if id.is_some() {
                    out.push(error(id, -32601, &format!("unhandled method `{method}`")));
                }
            }
        }
        out
    }

    fn initialize(&self) -> Json {
        Json::obj(vec![
            (
                "capabilities",
                Json::obj(vec![
                    ("textDocumentSync", Json::int(1)), // full
                    ("documentFormattingProvider", Json::Bool(true)),
                    ("documentRangeFormattingProvider", Json::Bool(true)),
                    ("documentSymbolProvider", Json::Bool(true)),
                    ("foldingRangeProvider", Json::Bool(true)),
                ]),
            ),
            (
                "serverInfo",
                Json::obj(vec![
                    ("name", Json::str("fors-lsp")),
                    ("version", Json::str(env!("CARGO_PKG_VERSION"))),
                ]),
            ),
        ])
    }

    /// `textDocument/formatting` and `rangeFormatting`: the canonical
    /// formatter's minimal edits. A file that does not parse produces no
    /// edits at all rather than a mangled buffer.
    fn format(&self, uri: &str, range: Option<Json>) -> Json {
        let Some(doc) = self.doc(uri) else {
            return Json::Arr(Vec::new());
        };
        let src = &doc.text;
        let ix = LineIndex::new(src);
        let check = match &range {
            None => fors_fmt::check_source(src),
            Some(r) => {
                let (s, e) = json_range(&ix, src, r);
                fors_fmt::format_range(src, s, e)
            }
        };
        Json::Arr(
            check
                .edits
                .iter()
                .map(|e| {
                    Json::obj(vec![
                        ("range", range_json(&ix, src, e.start, e.end)),
                        (
                            "newText",
                            Json::str(String::from_utf8_lossy(&e.new_text).into_owned()),
                        ),
                    ])
                })
                .collect(),
        )
    }

    fn diagnostics(&self, uri: &str) -> Json {
        let Some(doc) = self.doc(uri) else {
            return notification(
                "textDocument/publishDiagnostics",
                Json::obj(vec![
                    ("uri", Json::str(uri)),
                    ("diagnostics", Json::Arr(Vec::new())),
                ]),
            );
        };
        let src = &doc.text;
        let ix = LineIndex::new(src);
        let parse = fors_syntax::parse_file(src);
        let mut items: Vec<Json> = parse
            .diags
            .iter()
            .map(|d| diag_json(&ix, src, d.start, d.end, d.code.as_str(), d.message))
            .collect();
        // Resolution runs only on a clean parse: on a broken tree its
        // diagnostics are noise about recovery, not about the program.
        if parse.diags.is_empty() {
            let mut interner = Interner::new();
            let name: Segments = vec![interner.intern(module_stem(uri).as_bytes())];
            let inputs = vec![fors_resolve::FileInput {
                tree: &parse.tree,
                tokens: &parse.tokens,
                source: src,
                name,
            }];
            let out = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
            for d in &out.files[0].diagnostics {
                items.push(diag_json(
                    &ix,
                    src,
                    d.start,
                    d.end,
                    &d.code.as_string(),
                    &d.message,
                ));
            }
        }
        notification(
            "textDocument/publishDiagnostics",
            Json::obj(vec![
                ("uri", Json::str(uri)),
                ("version", Json::int(doc.version)),
                ("diagnostics", Json::Arr(items)),
            ]),
        )
    }

    fn symbols(&self, uri: &str) -> Json {
        let Some(doc) = self.doc(uri) else {
            return Json::Arr(Vec::new());
        };
        let src = &doc.text;
        let ix = LineIndex::new(src);
        let parse = fors_syntax::parse_file(src);
        let mut interner = Interner::new();
        let table = fors_index::build_decl_table(&parse.tree, &parse.tokens, src, &mut interner);
        let mut out = Vec::new();
        for i in 0..table.len() {
            let Some(sym) = table.name[i] else { continue };
            let kind = match table.kind[i] {
                // SymbolKind values from the LSP specification
                DeclKind::Fn | DeclKind::ExternFn => 12, // Function
                DeclKind::Struct => 23,                  // Struct
                // MARC: an impl block is shown as an Object (19), not a
                // Struct: it is a group of methods, and a client that
                // filters "types" should not list every impl twice.
                DeclKind::Impl => 19,
                DeclKind::Enum => 10,  // Enum
                DeclKind::Trait => 11, // Interface
                DeclKind::Const => 14, // Constant
                _ => continue,         // header clauses are not symbols
            };
            let ntok = parse.tokens.len();
            if ntok == 0 {
                continue;
            }
            let first = (table.range_start[i] as usize).min(ntok - 1);
            let last = (table.range_end[i] as usize).min(ntok);
            let start = parse.tokens.range(first).0;
            let end = if last > first {
                parse.tokens.range(last - 1).1
            } else {
                start
            };
            let name = String::from_utf8_lossy(interner.resolve(sym)).into_owned();
            out.push(Json::obj(vec![
                ("name", Json::str(name)),
                ("kind", Json::int(kind)),
                ("range", range_json(&ix, src, start, end)),
                ("selectionRange", range_json(&ix, src, start, end)),
            ]));
        }
        Json::Arr(out)
    }

    /// Folding ranges straight off the lossless CST: every construct whose
    /// tokens span more than one line folds, which is exactly what a tree
    /// with every token in it can answer for free.
    fn folding(&self, uri: &str) -> Json {
        let Some(doc) = self.doc(uri) else {
            return Json::Arr(Vec::new());
        };
        let src = &doc.text;
        let ix = LineIndex::new(src);
        let parse = fors_syntax::parse_file(src);
        let tree = &parse.tree;
        let mut out = Vec::new();
        for i in 0..tree.len() {
            use fors_syntax::NodeKind as K;
            if !matches!(
                tree.kinds[i],
                K::Block
                    | K::StructDecl
                    | K::EnumDecl
                    | K::TraitDecl
                    | K::ImplDecl
                    | K::MatchExpr
                    | K::Params
                    | K::ArrayLit
                    | K::StructLit
                    | K::AsmExpr
            ) {
                continue;
            }
            let (a, b) = tree.token_range(i);
            if b == 0 || b <= a || b as usize > parse.tokens.len() {
                continue;
            }
            // skip the node's leading trivia: a fold starts at real code
            let mut t = a as usize;
            while t < b as usize && parse.tokens.kinds[t].is_trivia() {
                t += 1;
            }
            if t >= b as usize {
                continue;
            }
            let start = parse.tokens.range(t).0;
            let end = parse.tokens.range(b as usize - 1).1;
            let (sl, _) = ix.pos(src, start);
            let (el, _) = ix.pos(src, end);
            if el > sl {
                out.push(Json::obj(vec![
                    ("startLine", Json::int(sl as i64)),
                    ("endLine", Json::int((el - 1) as i64)),
                ]));
            }
        }
        Json::Arr(out)
    }
}

fn module_stem(uri: &str) -> String {
    let file = uri.rsplit('/').next().unwrap_or(uri);
    let stem = file.strip_suffix(".fors").unwrap_or(file);
    if stem.is_empty() {
        "m".to_string()
    } else {
        stem.replace('-', "_")
    }
}

fn uri_of(params: &Json) -> String {
    params
        .get("textDocument")
        .and_then(|t| t.get("uri"))
        .and_then(|u| u.as_str())
        .unwrap_or("")
        .to_string()
}

fn json_range(ix: &LineIndex, src: &[u8], r: &Json) -> (u32, u32) {
    let at = |key: &str| -> u32 {
        let p = r.get(key);
        let line = p
            .and_then(|p| p.get("line"))
            .and_then(|v| v.as_u32())
            .unwrap_or(0);
        let ch = p
            .and_then(|p| p.get("character"))
            .and_then(|v| v.as_u32())
            .unwrap_or(0);
        ix.offset(src, line, ch)
    };
    let (s, e) = (at("start"), at("end"));
    (s.min(e), e.max(s))
}

fn diag_json(ix: &LineIndex, src: &[u8], start: u32, end: u32, code: &str, message: &str) -> Json {
    Json::obj(vec![
        ("range", range_json(ix, src, start, end.max(start))),
        ("severity", Json::int(1)),
        ("code", Json::str(code)),
        ("source", Json::str("fors")),
        ("message", Json::str(message)),
    ])
}

fn response(id: Option<Json>, result: Json) -> Json {
    Json::obj(vec![
        ("jsonrpc", Json::str("2.0")),
        ("id", id.unwrap_or(Json::Null)),
        ("result", result),
    ])
}

fn error(id: Option<Json>, code: i64, message: &str) -> Json {
    Json::obj(vec![
        ("jsonrpc", Json::str("2.0")),
        ("id", id.unwrap_or(Json::Null)),
        (
            "error",
            Json::obj(vec![
                ("code", Json::int(code)),
                ("message", Json::str(message)),
            ]),
        ),
    ])
}

fn notification(method: &str, params: Json) -> Json {
    Json::obj(vec![
        ("jsonrpc", Json::str("2.0")),
        ("method", Json::str(method)),
        ("params", params),
    ])
}

// ---- framing ----------------------------------------------------------

/// The largest body `read_message` accepts.
pub const MAX_MESSAGE: usize = 64 << 20;

/// Reads one `Content-Length`-framed message. `Ok(None)` at end of input.
pub fn read_message(r: &mut impl std::io::BufRead) -> std::io::Result<Option<Vec<u8>>> {
    let mut len: Option<usize> = None;
    loop {
        let mut line = String::new();
        if r.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some(v) = trimmed.strip_prefix("Content-Length:") {
            len = v.trim().parse().ok();
        }
        // Content-Type is accepted and ignored; any other header too.
    }
    let Some(len) = len else {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "message without Content-Length",
        ));
    };
    // MARC: a header claiming a multi-gigabyte body would otherwise be an
    // allocation of that size before a single byte is read — an abort, from
    // one line of input. 64 MiB is far beyond any document an editor sends.
    if len > MAX_MESSAGE {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Content-Length too large",
        ));
    }
    let mut buf = vec![0u8; len];
    r.read_exact(&mut buf)?;
    Ok(Some(buf))
}

pub fn write_message(w: &mut impl std::io::Write, msg: &Json) -> std::io::Result<()> {
    let body = msg.to_string();
    write!(w, "Content-Length: {}\r\n\r\n", body.len())?;
    w.write_all(body.as_bytes())?;
    w.flush()
}

/// Runs the server over one pair of streams until `exit` (or end of input).
pub fn serve(mut r: impl std::io::BufRead, mut w: impl std::io::Write) -> std::io::Result<()> {
    let mut server = Server::new();
    while let Some(bytes) = read_message(&mut r)? {
        let Some(msg) = json::parse(&bytes) else {
            write_message(&mut w, &error(None, -32700, "parse error"))?;
            continue;
        };
        for out in server.handle(&msg) {
            write_message(&mut w, &out)?;
        }
        if server.exited {
            break;
        }
    }
    Ok(())
}

/// `fors lsp`: serve on stdin/stdout. The CLI wires this up.
pub fn run_stdio() -> std::io::Result<()> {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    serve(stdin.lock(), stdout.lock())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn utf16_len(c: char) -> u32 {
        c.len_utf16() as u32
    }

    fn frame(body: &str) -> Vec<u8> {
        format!("Content-Length: {}\r\n\r\n{}", body.len(), body).into_bytes()
    }

    /// Splits a byte stream of framed messages back into parsed values.
    fn unframe(mut bytes: &[u8]) -> Vec<Json> {
        let mut out = Vec::new();
        let mut cur = std::io::Cursor::new(&mut bytes);
        while let Some(m) = read_message(&mut cur).unwrap() {
            out.push(json::parse(&m).unwrap());
        }
        out
    }

    /// The whole protocol over one scripted byte stream through `serve`,
    /// the way an editor drives the binary: initialize, open, change,
    /// format, a malformed body, shutdown, a rejected request, exit.
    #[test]
    fn end_to_end_over_a_scripted_stream() {
        let src = "fn f( ) {let  x=1 ;}\n";
        let src2 = "fn f() {\n    let x = 1;\n}\nfn g( {\n";
        let mut input: Vec<u8> = Vec::new();
        input.extend(frame(
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#,
        ));
        input.extend(frame(
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        ));
        input.extend(frame(&format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file:///w/m.fors","languageId":"fors","version":1,"text":{}}}}}}}"#,
            Json::str(src)
        )));
        input.extend(frame(r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/formatting","params":{"textDocument":{"uri":"file:///w/m.fors"},"options":{"tabSize":4,"insertSpaces":true}}}"#));
        input.extend(frame(&format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didChange","params":{{"textDocument":{{"uri":"file:///w/m.fors","version":2}},"contentChanges":[{{"text":{}}}]}}}}"#,
            Json::str(src2)
        )));
        // a response from the client (no method) must be ignored, not answered
        input.extend(frame(r#"{"jsonrpc":"2.0","id":77,"result":null}"#));
        // a malformed body must produce a parse error and NOT stop the loop
        input.extend(frame(
            r#"{"jsonrpc":"2.0","id":3,"method":"textDocument/formatting","params":{"#,
        ));
        input.extend(frame(r#"{"jsonrpc":"2.0","id":4,"method":"textDocument/foldingRange","params":{"textDocument":{"uri":"file:///w/m.fors"}}}"#));
        input.extend(frame(r#"{"jsonrpc":"2.0","id":5,"method":"shutdown"}"#));
        input.extend(frame(r#"{"jsonrpc":"2.0","id":6,"method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///w/m.fors"}}}"#));
        input.extend(frame(r#"{"jsonrpc":"2.0","method":"exit"}"#));
        // anything after exit must never be read
        input.extend(frame(r#"{"jsonrpc":"2.0","id":7,"method":"initialize"}"#));

        let mut output: Vec<u8> = Vec::new();
        serve(std::io::Cursor::new(input), &mut output).unwrap();
        let msgs = unframe(&output);
        let method = |m: &Json| {
            m.get("method")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_string()
        };
        let id = |m: &Json| m.get("id").cloned();

        // 1. initialize: the capability object, field by field, against the
        //    LSP specification's names (a typo silently disables a feature)
        assert_eq!(id(&msgs[0]), Some(Json::int(1)));
        let caps = msgs[0].get("result").unwrap().get("capabilities").unwrap();
        let Json::Obj(fields) = caps else {
            panic!("capabilities is not an object")
        };
        let names: Vec<&str> = fields.iter().map(|(k, _)| k.as_str()).collect();
        assert_eq!(
            names,
            vec![
                "textDocumentSync",
                "documentFormattingProvider",
                "documentRangeFormattingProvider",
                "documentSymbolProvider",
                "foldingRangeProvider"
            ]
        );
        assert_eq!(caps.get("textDocumentSync"), Some(&Json::int(1))); // TextDocumentSyncKind.Full
        for k in &names[1..] {
            assert_eq!(caps.get(k), Some(&Json::Bool(true)), "{k}");
        }
        assert_eq!(
            msgs[0]
                .get("result")
                .unwrap()
                .get("serverInfo")
                .unwrap()
                .get("name"),
            Some(&Json::str("fors-lsp"))
        );

        // 2. didOpen -> publishDiagnostics for that uri and version
        assert_eq!(method(&msgs[1]), "textDocument/publishDiagnostics");
        let p = msgs[1].get("params").unwrap();
        assert_eq!(p.get("uri"), Some(&Json::str("file:///w/m.fors")));
        assert_eq!(p.get("version"), Some(&Json::int(1)));
        assert_eq!(p.get("diagnostics").unwrap().as_arr().unwrap().len(), 0);

        // 3. formatting: applying the edits yields exactly fors-fmt's output
        assert_eq!(id(&msgs[2]), Some(Json::int(2)));
        let edits = msgs[2].get("result").unwrap().as_arr().unwrap();
        assert!(!edits.is_empty());
        let ix = LineIndex::new(src.as_bytes());
        let mut spans: Vec<(u32, u32, String)> = edits
            .iter()
            .map(|e| {
                let (a, b) = json_range(&ix, src.as_bytes(), e.get("range").unwrap());
                (
                    a,
                    b,
                    e.get("newText").unwrap().as_str().unwrap().to_string(),
                )
            })
            .collect();
        spans.sort_by_key(|(a, _, _)| *a);
        let mut buf = src.as_bytes().to_vec();
        for (a, b, t) in spans.into_iter().rev() {
            buf.splice(a as usize..b as usize, t.bytes());
        }
        assert_eq!(buf, fors_fmt::format_source(src.as_bytes()).text);

        // 4. didChange -> publishDiagnostics with the NEW version, and the
        //    parse error in the new text, before anything later is answered
        assert_eq!(method(&msgs[3]), "textDocument/publishDiagnostics");
        let p = msgs[3].get("params").unwrap();
        assert_eq!(p.get("version"), Some(&Json::int(2)));
        let diags = p.get("diagnostics").unwrap().as_arr().unwrap();
        assert!(!diags.is_empty());
        let d = &diags[0];
        for k in ["range", "severity", "code", "source", "message"] {
            assert!(d.get(k).is_some(), "diagnostic lacks `{k}`");
        }
        assert_eq!(
            d.get("range").unwrap().get("start").unwrap().get("line"),
            Some(&Json::int(3))
        );

        // 5. the client's response was ignored; the malformed body got a
        //    parse error with a null id and the loop went on
        let e = &msgs[4];
        assert_eq!(id(e), Some(Json::Null));
        assert_eq!(
            e.get("error").unwrap().get("code"),
            Some(&Json::int(-32700))
        );

        // 6. folding still answered after the bad frame
        assert_eq!(id(&msgs[5]), Some(Json::int(4)));
        let folds = msgs[5].get("result").unwrap().as_arr().unwrap();
        assert_eq!(folds[0].get("startLine"), Some(&Json::int(0)));
        assert_eq!(folds[0].get("endLine"), Some(&Json::int(1)));

        // 7. shutdown -> null result; a request after it -> InvalidRequest
        assert_eq!(id(&msgs[6]), Some(Json::int(5)));
        assert_eq!(msgs[6].get("result"), Some(&Json::Null));
        assert_eq!(id(&msgs[7]), Some(Json::int(6)));
        assert_eq!(
            msgs[7].get("error").unwrap().get("code"),
            Some(&Json::int(-32600))
        );

        // 8. exit ended the loop: nothing for id 7
        assert_eq!(msgs.len(), 8, "{msgs:?}");
        // every message on the wire is JSON-RPC 2.0
        for m in &msgs {
            assert_eq!(m.get("jsonrpc"), Some(&Json::str("2.0")));
        }
    }

    /// Hand-computed UTF-16 columns: `let s = "日本😀";` is 9 ASCII bytes,
    /// then 3 + 3 + 4 bytes of text that an editor counts as 1 + 1 + 2
    /// UTF-16 units.
    #[test]
    fn utf16_columns_by_hand() {
        let src = "let s = \"日本😀\";\nlet t = \"é\";\n".as_bytes();
        let ix = LineIndex::new(src);
        assert_eq!(&src[9..12], "日".as_bytes());
        assert_eq!(&src[15..19], "😀".as_bytes());
        // byte 9 (start of 日) is column 9; byte 12 (本) is 10; byte 15
        // (😀) is 11; byte 19 (the closing quote) is 13; byte 20 (`;`) is 14
        assert_eq!(ix.pos(src, 9), (0, 9));
        assert_eq!(ix.pos(src, 12), (0, 10));
        assert_eq!(ix.pos(src, 15), (0, 11));
        assert_eq!(ix.pos(src, 19), (0, 13));
        assert_eq!(ix.pos(src, 20), (0, 14));
        assert_eq!(ix.offset(src, 0, 9), 9);
        assert_eq!(ix.offset(src, 0, 10), 12);
        assert_eq!(ix.offset(src, 0, 11), 15);
        assert_eq!(ix.offset(src, 0, 12), 19); // inside the pair: past it
        assert_eq!(ix.offset(src, 0, 13), 19);
        assert_eq!(ix.offset(src, 0, 14), 20);
        // second line: `let t = "é";` — é is 2 bytes, 1 unit
        let l1 = 22u32;
        assert_eq!(&src[l1 as usize..l1 as usize + 3], b"let");
        assert_eq!(ix.pos(src, l1 + 9 + 2), (1, 10)); // after é
        assert_eq!(ix.offset(src, 1, 10), l1 + 11);
        // clamping: past the end of a line, and past the last line
        assert_eq!(ix.offset(src, 0, 999), 21); // before the `\n`
        assert_eq!(ix.offset(src, 5, 0), src.len() as u32);
        assert_eq!(ix.pos(src, 9999), (2, 0));
        // round trip every character boundary
        let text = std::str::from_utf8(src).unwrap();
        for (i, _) in text.char_indices() {
            let (l, c) = ix.pos(src, i as u32);
            assert_eq!(ix.offset(src, l, c), i as u32, "byte {i}");
        }
    }

    #[test]
    fn framing_rejects_an_absurd_content_length_instead_of_allocating_it() {
        let mut cur = std::io::Cursor::new(b"Content-Length: 99999999999999999\r\n\r\n{}".to_vec());
        assert!(read_message(&mut cur).is_err());
        let mut cur = std::io::Cursor::new(b"Content-Length: -5\r\n\r\n{}".to_vec());
        assert!(read_message(&mut cur).is_err());
        let mut cur = std::io::Cursor::new(b"Content-Length: 2\r\n\r\n{".to_vec());
        assert!(read_message(&mut cur).is_err()); // truncated body
    }

    #[test]
    fn a_range_format_returns_only_edits_touching_the_range() {
        let mut s = Server::new();
        let src = "fn f( ) {let  x=1 ;}\n\n\n\nfn g( ) {let  y=2 ;}\n";
        open(&mut s, src);
        let params = Json::obj(vec![
            (
                "textDocument",
                Json::obj(vec![("uri", Json::str("file:///w/m.fors"))]),
            ),
            (
                "range",
                Json::obj(vec![
                    (
                        "start",
                        Json::obj(vec![("line", Json::int(4)), ("character", Json::int(0))]),
                    ),
                    (
                        "end",
                        Json::obj(vec![("line", Json::int(4)), ("character", Json::int(5))]),
                    ),
                ]),
            ),
        ]);
        let out = s.handle(&req("textDocument/rangeFormatting", 2, params));
        let edits = out[0].get("result").unwrap().as_arr().unwrap();
        assert!(!edits.is_empty());
        for e in edits {
            let line = e
                .get("range")
                .unwrap()
                .get("start")
                .unwrap()
                .get("line")
                .unwrap();
            assert_ne!(
                line,
                &Json::int(0),
                "an edit outside the range was returned: {e:?}"
            );
        }
    }

    fn req(method: &str, id: i64, params: Json) -> Json {
        Json::obj(vec![
            ("jsonrpc", Json::str("2.0")),
            ("id", Json::int(id)),
            ("method", Json::str(method)),
            ("params", params),
        ])
    }

    fn open(s: &mut Server, text: &str) {
        s.handle(&Json::obj(vec![
            ("jsonrpc", Json::str("2.0")),
            ("method", Json::str("textDocument/didOpen")),
            (
                "params",
                Json::obj(vec![(
                    "textDocument",
                    Json::obj(vec![
                        ("uri", Json::str("file:///w/m.fors")),
                        ("version", Json::int(1)),
                        ("text", Json::str(text)),
                    ]),
                )]),
            ),
        ]));
    }

    fn doc_param() -> Json {
        Json::obj(vec![(
            "textDocument",
            Json::obj(vec![("uri", Json::str("file:///w/m.fors"))]),
        )])
    }

    #[test]
    fn initialize_advertises_formatting() {
        let mut s = Server::new();
        let out = s.handle(&req("initialize", 1, Json::Null));
        let caps = out[0].get("result").unwrap().get("capabilities").unwrap();
        assert_eq!(
            caps.get("documentFormattingProvider"),
            Some(&Json::Bool(true))
        );
        assert_eq!(
            caps.get("documentRangeFormattingProvider"),
            Some(&Json::Bool(true))
        );
    }

    #[test]
    fn formatting_returns_edits_that_format_the_file() {
        let mut s = Server::new();
        let src = "fn f( ) {let  x=1 ;}\n";
        open(&mut s, src);
        let out = s.handle(&req("textDocument/formatting", 2, doc_param()));
        let edits = out[0].get("result").unwrap().as_arr().unwrap();
        assert!(!edits.is_empty());
        let want = fors_fmt::format_source(src.as_bytes());
        // apply the edits back to front, as an editor does
        let mut buf = src.as_bytes().to_vec();
        let mut spans: Vec<(u32, u32, String)> = edits
            .iter()
            .map(|e| {
                let r = e.get("range").unwrap();
                let (a, b) = json_range(&LineIndex::new(src.as_bytes()), src.as_bytes(), r);
                (
                    a,
                    b,
                    e.get("newText").unwrap().as_str().unwrap().to_string(),
                )
            })
            .collect();
        spans.sort_by_key(|(a, _, _)| *a);
        for (a, b, t) in spans.into_iter().rev() {
            buf.splice(a as usize..b as usize, t.bytes());
        }
        assert_eq!(
            String::from_utf8(buf).unwrap(),
            String::from_utf8(want.text).unwrap()
        );
    }

    #[test]
    fn a_broken_file_is_never_rewritten() {
        let mut s = Server::new();
        open(&mut s, "fn f( {\n");
        let out = s.handle(&req("textDocument/formatting", 3, doc_param()));
        assert_eq!(out[0].get("result").unwrap().as_arr().unwrap().len(), 0);
    }

    #[test]
    fn diagnostics_are_published_on_open() {
        let mut s = Server::new();
        open(&mut s, "fn f( {\n");
        let note = s.handle(&Json::obj(vec![
            ("jsonrpc", Json::str("2.0")),
            ("method", Json::str("textDocument/didChange")),
            (
                "params",
                Json::obj(vec![
                    (
                        "textDocument",
                        Json::obj(vec![
                            ("uri", Json::str("file:///w/m.fors")),
                            ("version", Json::int(2)),
                        ]),
                    ),
                    (
                        "contentChanges",
                        Json::Arr(vec![Json::obj(vec![("text", Json::str("fn f( {\n"))])]),
                    ),
                ]),
            ),
        ]));
        let params = note[0].get("params").unwrap();
        assert_eq!(
            note[0].get("method").unwrap().as_str(),
            Some("textDocument/publishDiagnostics")
        );
        assert!(
            !params
                .get("diagnostics")
                .unwrap()
                .as_arr()
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn symbols_and_folding() {
        let mut s = Server::new();
        open(
            &mut s,
            "fn f() {\n    let x = 1;\n}\n\nstruct P { x: i32 }\n",
        );
        let syms = s.handle(&req("textDocument/documentSymbol", 4, doc_param()));
        let arr = syms[0].get("result").unwrap().as_arr().unwrap();
        let names: Vec<&str> = arr.iter().filter_map(|s| s.get("name")?.as_str()).collect();
        assert_eq!(names, vec!["f", "P"]);
        let folds = s.handle(&req("textDocument/foldingRange", 5, doc_param()));
        assert!(!folds[0].get("result").unwrap().as_arr().unwrap().is_empty());
    }

    #[test]
    fn utf16_positions() {
        let src = "let s = \"é😀\";\nlet t = 1;\n".as_bytes();
        let off = src.iter().position(|&b| b == b'\n').unwrap() as u32;
        let (line, ch) = offset_to_pos(src, off);
        assert_eq!(line, 0);
        // 8 ascii + " + é(1) + 😀(2) + " + ; = 14 utf-16 units
        assert_eq!(ch, 14);
        assert_eq!(pos_to_offset(src, 1, 0), off + 1);
    }

    #[test]
    fn framing_round_trip() {
        let mut buf: Vec<u8> = Vec::new();
        write_message(&mut buf, &Json::obj(vec![("a", Json::int(1))])).unwrap();
        let mut cur = std::io::Cursor::new(buf);
        let msg = read_message(&mut cur).unwrap().unwrap();
        assert_eq!(
            json::parse(&msg).unwrap().get("a").unwrap().as_u32(),
            Some(1)
        );
    }

    /// A reader that hands back one byte at a time, so `read_message` must
    /// reassemble a message split arbitrarily across `read`s.
    struct Trickle<'a> {
        data: &'a [u8],
        at: usize,
    }
    impl<'a> std::io::Read for Trickle<'a> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.at >= self.data.len() {
                return Ok(0);
            }
            buf[0] = self.data[self.at];
            self.at += 1;
            Ok(1)
        }
    }

    #[test]
    fn framing_survives_a_message_split_across_reads() {
        let mut buf: Vec<u8> = Vec::new();
        // a UTF-8 multi-byte body: Content-Length must be the byte length,
        // not the char count (é😀 is 2 chars but 5 bytes).
        write_message(&mut buf, &Json::obj(vec![("s", Json::str("é😀"))])).unwrap();
        let header_end = buf.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
        let declared: usize = String::from_utf8_lossy(&buf[16..header_end - 4])
            .trim()
            .parse()
            .unwrap();
        assert_eq!(
            declared,
            buf.len() - header_end,
            "Content-Length must count bytes, not chars"
        );

        let mut r = std::io::BufReader::new(Trickle { data: &buf, at: 0 });
        let msg = read_message(&mut r).unwrap().unwrap();
        assert_eq!(
            json::parse(&msg).unwrap().get("s").unwrap().as_str(),
            Some("é😀")
        );
    }

    #[test]
    fn unknown_method_gets_a_jsonrpc_error_not_a_crash() {
        let mut s = Server::new();
        let out = s.handle(&req("totally/madeUp", 9, Json::Null));
        assert_eq!(out.len(), 1);
        let code = out[0].get("error").unwrap().get("code").unwrap();
        assert_eq!(*code, Json::Num(-32601.0)); // MethodNotFound
    }

    #[test]
    fn request_after_shutdown_errors() {
        let mut s = Server::new();
        s.handle(&req("shutdown", 1, Json::Null));
        assert!(s.shutdown_requested);
        let out = s.handle(&req("initialize", 2, Json::Null));
        assert!(
            out[0].get("error").is_some(),
            "a request after shutdown must be rejected"
        );
        // `exit` itself still goes through
        s.handle(&Json::obj(vec![
            ("jsonrpc", Json::str("2.0")),
            ("method", Json::str("exit")),
        ]));
        assert!(s.exited);
    }

    #[test]
    fn unparseable_didchange_still_publishes_diagnostics() {
        let mut s = Server::new();
        open(&mut s, "fn f() {}\n");
        let note = s.handle(&Json::obj(vec![
            ("jsonrpc", Json::str("2.0")),
            ("method", Json::str("textDocument/didChange")),
            (
                "params",
                Json::obj(vec![
                    (
                        "textDocument",
                        Json::obj(vec![
                            ("uri", Json::str("file:///w/m.fors")),
                            ("version", Json::int(2)),
                        ]),
                    ),
                    (
                        "contentChanges",
                        Json::Arr(vec![Json::obj(vec![("text", Json::str("fn f( {\n"))])]),
                    ),
                ]),
            ),
        ]));
        assert_eq!(
            note[0].get("method").unwrap().as_str(),
            Some("textDocument/publishDiagnostics")
        );
        assert!(
            !note[0]
                .get("params")
                .unwrap()
                .get("diagnostics")
                .unwrap()
                .as_arr()
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn utf16_positions_mixed_scripts_and_emoji() {
        // ascii + accented Latin + CJK + emoji, on the second line, so both
        // the line-scan and the column-scan are exercised together.
        let src = "let a = 1;\nlet café = \"日本語😀\";\n".as_bytes();
        let line1_start = src.iter().position(|&b| b == b'\n').unwrap() as u32 + 1;
        // "let café = \"" = 12 ascii chars but "é" is 1 code point -> +1 utf16
        let after_open_quote =
            line1_start + "let caf".len() as u32 + "é".len() as u32 + " = \"".len() as u32;
        let (line, ch) = offset_to_pos(src, after_open_quote);
        assert_eq!(line, 1);
        assert_eq!(ch, "let café = \"".chars().map(utf16_len).sum::<u32>());
        // round trip: offset -> pos -> offset
        assert_eq!(pos_to_offset(src, line, ch), after_open_quote);
        // the emoji costs 2 utf-16 units; the whole line's utf16 length
        // must be less than its byte length (multi-byte chars present).
        let line_bytes = &src[line1_start as usize..src.len() - 1];
        let line_str = std::str::from_utf8(line_bytes).unwrap();
        let utf16_total: u32 = line_str.chars().map(utf16_len).sum();
        assert!((utf16_total as usize) < line_bytes.len());
    }

    /// A tiny deterministic linear-congruential generator: no external
    /// crate, reproducible across runs.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        fn byte(&mut self) -> u8 {
            (self.next() >> 33) as u8
        }
    }

    #[test]
    fn fuzz_reader_never_panics_on_malformed_input() {
        let seed_msgs: Vec<Vec<u8>> = vec![
            b"Content-Length: 13\r\n\r\n{\"a\":1,\"b\":2}".to_vec(),
            b"Content-Length: 5\r\n\r\n{\"x\":".to_vec(),
            b"Content-Type: application/json\r\nContent-Length: 2\r\n\r\n{}".to_vec(),
        ];
        let mut lcg = Lcg(0xC0FFEE);
        for trial in 0..500u32 {
            let base = &seed_msgs[(trial as usize) % seed_msgs.len()];
            let mut mutated = base.clone();
            // truncate at a random point, or flip/insert a few random bytes
            if trial % 2 == 0 && !mutated.is_empty() {
                let cut = (lcg.next() as usize) % (mutated.len() + 1);
                mutated.truncate(cut);
            } else {
                for _ in 0..(lcg.next() % 4 + 1) {
                    if mutated.is_empty() {
                        break;
                    }
                    let idx = (lcg.next() as usize) % mutated.len();
                    mutated[idx] = lcg.byte();
                }
            }
            let mut cur = std::io::Cursor::new(mutated.clone());
            // read_message must return Ok/Err, never panic
            if let Ok(Some(bytes)) = read_message(&mut cur) {
                // a malformed body must not panic the JSON parser either
                let parsed = json::parse(&bytes);
                if let Some(msg) = parsed {
                    let mut s = Server::new();
                    let _ = s.handle(&msg);
                }
            }
        }
    }
}
