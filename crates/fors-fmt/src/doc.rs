//! The layout IR and its renderer.
//!
//! A format run lowers the CST to one flat `Vec<Op>` — no per-node
//! allocation, no boxed document tree — and renders it in two linear
//! passes: one that measures every group's *flat* width, one that emits
//! bytes. This is Wadler/Oppen pretty-printing in struct-of-arrays form:
//! a group prints on one line when it fits inside the margin from the
//! current column, otherwise every `Line`/`Soft` directly inside it
//! becomes a newline and its nested groups are measured again.
//!
//! The only text the renderer ever emits is a slice of the ORIGINAL
//! source ([`Op::Src`]) — the formatter never synthesises, rewrites or
//! drops a token's bytes, which is what makes the losslessness property
//! checkable by token equality.

/// The canonical line budget (owner decision 2026-09-19).
pub const MARGIN: usize = 100;
/// The canonical indent (owner decision 2026-09-19).
pub const INDENT: usize = 4;

/// A width that no group can fit into: added by `Hard`/`Blank` and by any
/// text containing a newline, so a group holding one always breaks.
const INF: u64 = 1 << 40;
/// Width added by [`Op::Ghost`] to force a break (magic trailing comma)
/// without pretending the line is infinitely long.
pub const FORCE: u32 = 1 << 20;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    /// `source[start..end]` — the only bytes the renderer emits.
    Src(u32, u32),
    /// Counts toward a group's flat width, prints nothing. Used to charge
    /// a group for text that follows it (the `{` after a signature) and to
    /// force a break (`FORCE`).
    Ghost(u32),
    /// One space, always.
    Space,
    /// A space when the enclosing group is flat, a newline when it broke.
    Line,
    /// Nothing when flat, a newline when broken.
    Soft,
    /// Always a newline.
    Hard,
    /// Always a newline and one blank line.
    Blank,
    Indent,
    Dedent,
    Open,
    Close,
}

/// Display width of one source slice: `None` when it spans lines (a block
/// comment or a `\\` multiline string), which is treated as unfittable.
fn text_width(t: &[u8]) -> Option<usize> {
    if t.contains(&b'\n') {
        return None;
    }
    // UTF-8 continuation bytes are not columns of their own. Wide glyphs
    // are counted as one; the margin is a budget, not a guarantee.
    Some(t.iter().filter(|b| (*b & 0xC0) != 0x80).count())
}

fn op_width(op: Op, src: &[u8]) -> u64 {
    match op {
        Op::Src(a, b) => match text_width(&src[a as usize..b as usize]) {
            Some(w) => w as u64,
            None => INF,
        },
        Op::Ghost(n) => n as u64,
        Op::Space | Op::Line => 1,
        Op::Hard | Op::Blank => INF,
        _ => 0,
    }
}

/// Flat width of each group (at the index of its `Open`) and the index of
/// its `Close`.
fn group_widths(ops: &[Op], src: &[u8]) -> (Vec<u64>, Vec<usize>) {
    let mut gw = vec![0u64; ops.len()];
    let mut end = vec![0usize; ops.len()];
    let mut cum = 0u64;
    let mut stack: Vec<(usize, u64)> = Vec::new();
    for (i, &op) in ops.iter().enumerate() {
        match op {
            Op::Open => stack.push((i, cum)),
            Op::Close => {
                if let Some((o, at)) = stack.pop() {
                    gw[o] = cum - at;
                    end[o] = i;
                }
            }
            _ => cum += op_width(op, src),
        }
    }
    // an unbalanced Open would make a group unfittable rather than wrong
    for (o, _) in stack {
        gw[o] = INF;
        end[o] = ops.len().saturating_sub(1);
    }
    (gw, end)
}

/// Width of what follows index `i` up to the NEXT BREAK OPPORTUNITY of
/// any kind. A group fits only if its own flat width plus this tail fits,
/// which is what stops a parameter list from staying flat because the
/// `-> Ret` after it was never counted.
///
/// MARC: the tail stops at the first `Line`/`Soft` even when it is inside
/// a group that has not been decided yet (an optimistic tail). Measuring
/// that inner group flat instead would make the OUTER construct break
/// first — a long signature would break its generics rather than its
/// parameters — and breaking the innermost thing that can absorb the
/// overflow is the rule that keeps diffs local.
fn tail_widths(ops: &[Op], src: &[u8]) -> Vec<u64> {
    let n = ops.len();
    let mut tail = vec![0u64; n + 1];
    for i in (0..n).rev() {
        tail[i] = match ops[i] {
            Op::Hard | Op::Blank | Op::Line | Op::Soft | Op::Close => 0,
            Op::Open | Op::Indent | Op::Dedent => tail[i + 1],
            op => op_width(op, src).saturating_add(tail[i + 1]),
        };
    }
    tail
}

const SPACES: &str = "                                                                ";

/// Renders the op stream. Deterministic: the output is a pure function of
/// `ops` and `src`, with no map iteration and no floating point anywhere.
pub fn render(ops: &[Op], src: &[u8]) -> Vec<u8> {
    let (gw, gend) = group_widths(ops, src);
    let tail = tail_widths(ops, src);
    let mut out: Vec<u8> = Vec::with_capacity(src.len() + src.len() / 8);
    let mut flat: Vec<bool> = Vec::new();
    let mut indent = 0usize;
    let mut col = 0usize;
    // 0 = nothing pending, 1 = newline, 2 = newline + blank line.
    let mut pending = 0u8;
    let mut space = false;
    // Last byte emitted on this line, for the token-gluing guard.
    let mut last: Option<u8> = None;

    for (i, &op) in ops.iter().enumerate() {
        match op {
            Op::Open => {
                let inherited = *flat.last().unwrap_or(&false);
                let at = if pending > 0 { indent * INDENT } else { col + space as usize };
                let need = gw[i].saturating_add(tail[gend[i] + 1]);
                flat.push(inherited || (need < INF && at as u64 + need <= MARGIN as u64));
            }
            Op::Close => {
                flat.pop();
            }
            Op::Indent => indent += 1,
            Op::Dedent => indent = indent.saturating_sub(1),
            Op::Space => space = true,
            Op::Line => {
                if *flat.last().unwrap_or(&false) {
                    space = true;
                } else {
                    pending = pending.max(1);
                    space = false;
                }
            }
            Op::Soft => {
                if !*flat.last().unwrap_or(&false) {
                    pending = pending.max(1);
                    space = false;
                }
            }
            Op::Hard => {
                pending = pending.max(1);
                space = false;
            }
            Op::Blank => {
                pending = 2;
                space = false;
            }
            Op::Ghost(_) => {}
            Op::Src(a, b) => {
                let text = &src[a as usize..b as usize];
                if text.is_empty() {
                    continue; // the zero-length Eof token
                }
                let at_line_start = pending > 0;
                if pending > 0 {
                    if !out.is_empty() {
                        out.push(b'\n');
                        if pending == 2 {
                            out.push(b'\n');
                        }
                    }
                    pending = 0;
                    space = false;
                    last = None;
                    let mut n = indent * INDENT;
                    while n > 0 {
                        let take = n.min(SPACES.len());
                        out.extend_from_slice(&SPACES.as_bytes()[..take]);
                        n -= take;
                    }
                    col = indent * INDENT;
                }
                if space {
                    out.push(b' ');
                    col += 1;
                    space = false;
                    last = Some(b' ');
                }
                // MARC: the gluing guard. Layout must never change the token
                // stream, and the lexer is maximal-munch, so two tokens that
                // would re-lex as one (or as a comment) get a space no rule
                // asked for. It costs two byte compares per token and it is
                // the last line of defence behind the corpus-wide losslessness
                // test.
                if let Some(p) = last {
                    if glues(p, text[0], text.get(1).copied()) {
                        out.push(b' ');
                        col += 1;
                    }
                }
                out.extend_from_slice(text);
                match text_width(text) {
                    Some(w) => col += w,
                    None => {
                        let after_nl = text.iter().rposition(|&b| b == b'\n').map_or(0, |p| p + 1);
                        col = text_width(&text[after_nl..]).unwrap_or(0);
                    }
                }
                last = text.last().copied();
                // MARC: a comment that starts a line owns that line. The
                // emitter splices a same-line comment in front of the
                // layout ops queued after its token; when one of those was
                // a `Line` that then broke, the comment lands at the start
                // of the next line, and the second pass would read it as a
                // standalone comment and give it a line of its own. Doing
                // that here on the first pass is what makes the two passes
                // agree. (Only a comment can start with `//` or `/*`: a
                // `/` operator is a one-byte token.)
                if at_line_start && text.len() >= 2 && text[0] == b'/' && matches!(text[1], b'/' | b'*') {
                    pending = pending.max(1);
                    space = false;
                }
            }
        }
    }
    if !out.is_empty() && out.last() != Some(&b'\n') {
        out.push(b'\n');
    }
    out
}

fn identish(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// Whether emitting `b` (whose second byte is `b2`) directly after `a`
/// would change the token stream under the lexer's maximal munch.
fn glues(a: u8, b: u8, b2: Option<u8>) -> bool {
    if identish(a) && identish(b) {
        return true; // `x y`, and a literal's width suffix
    }
    match (a, b) {
        (b'-', b'>') | (b'-', b'=') => true,
        (b'=', b'>') | (b'=', b'=') => true,
        (b'!', b'=') => true,
        (b'<', b'<') | (b'<', b'=') => true,
        (b'>', b'>') | (b'>', b'=') => true,
        (b'+', b'=') | (b'*', b'=') | (b'/', b'=') | (b'%', b'=') => true,
        (b'&', b'=') | (b'|', b'=') | (b'^', b'=') => true,
        (b'/', b'/') | (b'/', b'*') => true, // a comment, not an operator
        (b'.', b'.') => true,                // `..` is a lexical error, never a token
        // a digit then `.` is a fraction only when a digit follows, so
        // `0..<n` stays tight while `1 . 0` does not glue into `1.0`
        (b'0'..=b'9', b'.') => b2.is_some_and(|c| c.is_ascii_digit()),
        _ => false,
    }
}
