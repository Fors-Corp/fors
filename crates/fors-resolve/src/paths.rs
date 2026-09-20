//! Extracting the dotted-identifier segments a name-use tree node owns
//! directly (ch08's `Path`, `NameExpr`, `TypeApp`, `PatPath`, `PatDot`):
//! per-file work, depends only on that file's tree/tokens.

use fors_index::{Interner, Symbol};
use fors_lex::{TokenKind, Tokens};
use fors_syntax::Tree;

/// The raw-token span a node owns directly, before its first child (a
/// `TypeApp`'s `[targs]`, a `PatPath`'s `Payload`): exactly its own
/// dotted-path tokens, since every name-use node's only other content is
/// such a trailing child.
pub fn own_span(tree: &Tree, node: usize) -> (u32, u32) {
    let (first, end) = tree.token_range(node);
    let child_end = tree
        .children(node)
        .next()
        .map_or(end, |c| tree.token_range(c).0);
    (first, child_end)
}

/// Interns and returns each `Ident` segment owned directly by `node`
/// (skipping `.` and trivia), each paired with its byte range.
pub fn segments_with_ranges(
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    node: usize,
) -> Vec<(Symbol, (u32, u32))> {
    let (first, end) = own_span(tree, node);
    let mut out = Vec::new();
    let mut i = first as usize;
    let end = end as usize;
    while i < end {
        if tokens.kinds[i] == TokenKind::Ident {
            out.push((interner.intern(tokens.text(i, source)), tokens.range(i)));
        }
        i += 1;
    }
    out
}

/// The byte range of a node's whole subtree, from its first significant
/// token to its last (a node's token range starts with its leading
/// trivia, which a diagnostic should not underline).
pub fn byte_range(tree: &Tree, tokens: &Tokens, node: usize) -> (u32, u32) {
    let (a, b) = tree.token_range(node);
    let (a, b) = (a as usize, (b as usize).min(tokens.kinds.len()));
    let sig = |i: &usize| !tokens.kinds[*i].is_trivia();
    match ((a..b).find(sig), (a..b).rev().find(sig)) {
        (Some(first), Some(last)) => (tokens.range(first).0, tokens.range(last).1),
        _ if a < tokens.kinds.len() => (tokens.range(a).0, tokens.range(a).0),
        _ => (0, 0),
    }
}
