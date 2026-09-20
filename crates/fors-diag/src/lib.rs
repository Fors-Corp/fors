//! The agent-facing diagnostic surface: one rendered diagnostic shape, the
//! two writers over it (the human text line and the JSON Lines record), the
//! machine-applicable edits a tool may apply, and the offline explanation of
//! every stable code.
//!
//! Fors is written largely by coding agents that have never seen Fors, so
//! the compiler has to be drivable by a program: stable codes, edits with
//! byte offsets, and a rule citation that does not need the network. Owner
//! policy R14: a suggested fix is a GUESS and the compiler is the arbiter —
//! nothing here ever applies an edit on the compiler's behalf, and
//! [`policy::applicability`] is where the owner decides how far a tool may
//! trust one.
//!
//! **Position units.** [`Pos::byte`] is a 0-based byte offset into the file
//! the diagnostic belongs to. [`Pos::line`] is 1-based, counting `\n`.
//! [`Pos::col`] is 1-based and counts BYTES since the last `\n`, not
//! characters, not UTF-16 code units — exactly the `line:col` the text
//! format has always printed. A tool that wants character columns must
//! re-derive them from the file's bytes.
//!
//! This crate is a leaf: zero dependencies, and nothing here knows what a
//! token, a tree or a type is.

pub mod explain;
pub mod json;
pub mod policy;

pub use explain::{Explanation, explain, list, rule_of};
pub use policy::applicability;

/// How far a tool may trust a [`Fix`] (the vocabulary `rustc` established,
/// kept because agents already know it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Applicability {
    /// Applying it is safe without review: the compiler's own arbiter test
    /// has shown, over the whole conformance corpus, that it removes the
    /// diagnostic and adds no new error.
    MachineApplicable,
    /// A guess. It parses, but it may not be what the author meant.
    MaybeIncorrect,
    /// The replacement text contains something a human or an agent must
    /// fill in before the result compiles.
    HasPlaceholders,
}

impl Applicability {
    pub fn as_str(self) -> &'static str {
        match self {
            Applicability::MachineApplicable => "machine-applicable",
            Applicability::MaybeIncorrect => "maybe-incorrect",
            Applicability::HasPlaceholders => "has-placeholders",
        }
    }
}

/// Every kind of fix the compiler knows how to suggest. The string form is
/// the stable name a tool keys on (a tool may, say, auto-apply
/// `insert-semicolon` and queue `replace-identifier` for review); append,
/// never rename.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FixKind {
    /// P0002: the parser reached a statement boundary with no `;` and
    /// inserted a virtual one. The insertion point is the end of the
    /// previous token, and the parse that follows is already the parse of
    /// the fixed text.
    InsertSemicolon,
    /// N0014 on a head segment that spells a std module: insert the
    /// `use std.<m>;` the header is missing.
    InsertStdImport,
    /// N0014: the identifier is one edit away from a name that IS in
    /// scope here. A guess — see [`suggest`].
    ReplaceIdentifier,
    /// N0001: rewrite the `module` header's path to the one the file's
    /// location derives (ch08 Rule 1).
    FixModuleHeaderPath,
    /// T0042: a method was read as a field; append the call parentheses.
    CallMethod,
}

impl FixKind {
    pub fn as_str(self) -> &'static str {
        match self {
            FixKind::InsertSemicolon => "insert-semicolon",
            FixKind::InsertStdImport => "insert-std-import",
            FixKind::ReplaceIdentifier => "replace-identifier",
            FixKind::FixModuleHeaderPath => "fix-module-header-path",
            FixKind::CallMethod => "call-method",
        }
    }

    /// Every kind, for tools (and tests) that want to enumerate the surface.
    pub const ALL: [FixKind; 5] = [
        FixKind::InsertSemicolon,
        FixKind::InsertStdImport,
        FixKind::ReplaceIdentifier,
        FixKind::FixModuleHeaderPath,
        FixKind::CallMethod,
    ];
}

/// One replacement of `start..end` (a half-open BYTE range into the same
/// file the diagnostic is in) by `replacement`. `start == end` is an
/// insertion.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Edit {
    pub start: u32,
    pub end: u32,
    pub replacement: String,
}

impl Edit {
    pub fn new(start: u32, end: u32, replacement: impl Into<String>) -> Edit {
        Edit {
            start,
            end,
            replacement: replacement.into(),
        }
    }

    pub fn insert(at: u32, text: impl Into<String>) -> Edit {
        Edit::new(at, at, text)
    }
}

/// One suggested repair: a title an agent can show or log, the kind that
/// decides its [`Applicability`], and the edits that carry it out. All the
/// edits of one fix are applied together or not at all.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Fix {
    pub title: String,
    pub kind: FixKind,
    pub edits: Vec<Edit>,
}

impl Fix {
    pub fn new(kind: FixKind, title: impl Into<String>, edits: Vec<Edit>) -> Fix {
        Fix {
            title: title.into(),
            kind,
            edits,
        }
    }

    pub fn insert(
        kind: FixKind,
        title: impl Into<String>,
        at: u32,
        text: impl Into<String>,
    ) -> Fix {
        Fix::new(kind, title, vec![Edit::insert(at, text)])
    }

    pub fn replace(
        kind: FixKind,
        title: impl Into<String>,
        start: u32,
        end: u32,
        text: impl Into<String>,
    ) -> Fix {
        Fix::new(kind, title, vec![Edit::new(start, end, text)])
    }

    pub fn applicability(&self) -> Applicability {
        policy::applicability(self.kind)
    }
}

/// A position in a file: see the crate docs for the unit of each field.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Pos {
    pub byte: u32,
    pub line: u32,
    pub col: u32,
}

/// One diagnostic, resolved against its file: everything both writers need
/// and nothing that only one phase understands.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rendered {
    pub path: String,
    pub start: Pos,
    pub end: Pos,
    pub code: String,
    pub message: String,
    pub fixes: Vec<Fix>,
}

/// The 1-based `(line, col)` of `byte_offset`, col counting bytes. An
/// offset past the end clamps to the end (never a panic, never an index
/// out of range).
pub fn line_col(source: &[u8], byte_offset: u32) -> (u32, u32) {
    let offset = (byte_offset as usize).min(source.len());
    let mut line = 1u32;
    let mut col = 1u32;
    for &b in &source[..offset] {
        if b == b'\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

pub fn pos(source: &[u8], byte: u32) -> Pos {
    let (line, col) = line_col(source, byte);
    Pos { byte, line, col }
}

/// The start offset of every line of one file, so that a position costs a
/// binary search rather than a scan from byte 0. [`line_col`] is linear in
/// the offset, which made rendering quadratic: a 1 MB file with 22,000
/// diagnostics spent 17 of its 21 seconds counting newlines. Build one per
/// file, and only for a file that has a diagnostic (error path only).
///
/// `LineIndex::pos` agrees with [`pos`] for every offset, including one
/// past the end (both clamp the line and column, and report `byte` as
/// given).
pub struct LineIndex {
    starts: Vec<u32>,
    len: u32,
}

impl LineIndex {
    pub fn new(source: &[u8]) -> Self {
        let mut starts = vec![0u32];
        for (i, &b) in source.iter().enumerate() {
            if b == b'\n' {
                starts.push(i as u32 + 1);
            }
        }
        LineIndex {
            starts,
            len: source.len() as u32,
        }
    }

    pub fn line_col(&self, byte: u32) -> (u32, u32) {
        let offset = byte.min(self.len);
        // `starts[0] == 0 <= offset`, so the partition point is at least 1.
        let line = self.starts.partition_point(|&s| s <= offset);
        let start = self.starts[line - 1];
        (line as u32, offset - start + 1)
    }

    pub fn pos(&self, byte: u32) -> Pos {
        let (line, col) = self.line_col(byte);
        Pos { byte, line, col }
    }
}

/// The human line, byte for byte what `fors check` has always printed:
/// `path:line:col: error[CODE]: message`, with no trailing newline.
/// Fixes are deliberately NOT shown here — the text format is a baseline
/// other tooling diffs against, and the machine format is where a fix
/// belongs.
pub fn write_text(r: &Rendered, out: &mut String) {
    out.push_str(&r.path);
    out.push(':');
    push_u32(r.start.line, out);
    out.push(':');
    push_u32(r.start.col, out);
    out.push_str(": error[");
    out.push_str(&r.code);
    out.push_str("]: ");
    out.push_str(&r.message);
}

pub(crate) fn push_u32(n: u32, out: &mut String) {
    let mut buf = [0u8; 10];
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
    // `buf[i..]` is ASCII digits by construction.
    out.push_str(std::str::from_utf8(&buf[i..]).unwrap_or("0"));
}

/// Applies `edits` to `source`, returning the new bytes. `None` — never a
/// panic and never a partial write — when two edits overlap or one is out
/// of range, because a caller that cannot apply the whole fix must apply
/// none of it.
///
/// Two insertions at the same offset do not overlap; they are applied in
/// the order the slice gives, which keeps the result deterministic.
pub fn apply_edits(source: &[u8], edits: &[Edit]) -> Option<Vec<u8>> {
    let len = source.len() as u64;
    let mut order: Vec<usize> = (0..edits.len()).collect();
    // Stable, so equal-start insertions keep their given order.
    order.sort_by_key(|&i| (edits[i].start, edits[i].end));
    let mut cursor: u32 = 0;
    let mut out = Vec::with_capacity(source.len());
    for &i in &order {
        let e = &edits[i];
        if e.start > e.end || u64::from(e.end) > len || e.start < cursor {
            return None;
        }
        out.extend_from_slice(&source[cursor as usize..e.start as usize]);
        out.extend_from_slice(e.replacement.as_bytes());
        cursor = e.end;
    }
    out.extend_from_slice(&source[cursor as usize..]);
    Some(out)
}

/// Optimal string alignment (Damerau-Levenshtein restricted to adjacent
/// transpositions) over BYTES, in integers. Bytes rather than chars because
/// a Fors identifier is ASCII (ch08 Rule 24) and a byte table cannot
/// disagree with the byte offsets the rest of this crate speaks in.
///
/// `rows` are the caller's, so that one `suggest` over a large scope
/// allocates them once rather than once per candidate.
fn osa_distance_in(a: &[u8], b: &[u8], rows: &mut [Vec<usize>; 3]) -> usize {
    let (n, m) = (a.len(), b.len());
    if n == 0 {
        return m;
    }
    if m == 0 {
        return n;
    }
    // Three rows: previous-previous, previous, current.
    let [pp, p, cur] = rows;
    pp.clear();
    pp.resize(m + 1, 0);
    p.clear();
    p.extend(0..=m);
    cur.clear();
    cur.resize(m + 1, 0);
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut d = (cur[j - 1] + 1).min(p[j] + 1).min(p[j - 1] + cost);
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                d = d.min(pp[j - 2] + 1);
            }
            cur[j] = d;
        }
        std::mem::swap(pp, p);
        std::mem::swap(p, cur);
    }
    p[m]
}

fn eq_ignore_ascii_case(a: &[u8], b: &[u8]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|(x, y)| x.eq_ignore_ascii_case(y))
}

/// Deterministic "did you mean". Returns the single best candidate, or
/// `None` when nothing is close enough.
///
/// A candidate is ACCEPTED when its optimal-string-alignment distance from
/// `name` is at most `max(1, name.len() / 3)`, or when it differs from
/// `name` only in ASCII case (`Foo` for `foo` is one mistake however many
/// letters it spans, so the ratio threshold must not hide it). A
/// non-case-only candidate whose distance is as long as the shorter of the
/// two names is REJECTED whatever the threshold says: every byte differs,
/// so for a one-letter name the threshold alone would accept every other
/// one-letter name in scope (measured: 8 of the corpus's 24 suggestions
/// were `x` -> `f`, none of them right).
///
/// Candidates are RANKED by `(not a case-only difference, distance,
/// candidate bytes)`: a case-only difference first, then the nearest, then
/// lexicographic order. The last key is what makes the answer independent
/// of hash order or iteration order — two runs over the same set of names
/// in any order give the same suggestion.
///
/// This must only ever run on the error path: it is O(candidates x
/// name x candidate).
pub fn suggest<'a>(name: &[u8], candidates: impl Iterator<Item = &'a [u8]>) -> Option<&'a [u8]> {
    let threshold = (name.len() / 3).max(1);
    let mut best: Option<(bool, usize, &'a [u8])> = None;
    let mut rows = [Vec::new(), Vec::new(), Vec::new()];
    for c in candidates {
        if c == name {
            continue;
        }
        let case_only = eq_ignore_ascii_case(name, c);
        // The distance is at least the difference in length, so most of a
        // large scope is rejected here without running the alignment.
        // ...and at least 1 (`c != name`), which already fails the "shares
        // something" rule below when either name is a single byte.
        if !case_only && (name.len().abs_diff(c.len()) > threshold || name.len().min(c.len()) <= 1)
        {
            continue;
        }
        let d = osa_distance_in(name, c, &mut rows);
        // A distance as long as the shorter name means the two share
        // nothing: `f` is not a misspelling of `x`, it is a different name.
        if !case_only && (d > threshold || d >= name.len().min(c.len())) {
            continue;
        }
        let key = (!case_only, d, c);
        if best.is_none_or(|b| key < b) {
            best = Some(key);
        }
    }
    best.map(|(_, _, c)| c)
}

#[cfg(test)]
mod tests;
