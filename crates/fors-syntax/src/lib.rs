//! `fors-syntax`: the Fors parser (spec ch07). Std only, no per-node heap
//! allocation: the tree is struct-of-arrays columns in pre-order (see
//! [`Tree`]), a hand-written recursive-descent / precedence-climbing
//! parser with at most 2 tokens of lookahead and no backtracking, no
//! symbol table. Each file is parsed independently with no global state.
//! Never panics: every failure, including recursion past the nesting
//! limit, becomes a [`Diagnostic`] and an `Error` node.

mod diag;
mod node_kind;
mod parser;
mod tree;

pub use diag::{DiagCode, Diagnostic};
pub use node_kind::NodeKind;
pub use parser::{Parse, parse, parse_file};
pub use tree::Tree;

/// Pretty-prints the tree, one node per line, indented by nesting depth,
/// each line naming the node kind and the source text it spans (truncated
/// for readability). Used by `fors parse --tree`.
pub fn dump_tree(tree: &Tree, tokens: &fors_lex::Tokens, source: &[u8], out: &mut String) {
    fn rec(
        tree: &Tree,
        tokens: &fors_lex::Tokens,
        source: &[u8],
        i: usize,
        depth: usize,
        out: &mut String,
    ) {
        let (a, b) = tree.token_range(i);
        let byte_start = tokens.range(a as usize).0;
        let byte_end = if b > a {
            tokens.range(b as usize - 1).1
        } else {
            byte_start
        };
        for _ in 0..depth {
            out.push_str("  ");
        }
        out.push_str(&format!("{:?}", tree.kinds[i]));
        out.push_str(&format!(" @{}..{}", byte_start, byte_end));
        if tree.is_leaf(i) {
            let text = &source[byte_start as usize..byte_end as usize];
            let text = String::from_utf8_lossy(text);
            let text: String = text.chars().take(40).collect();
            out.push_str(" \"");
            out.push_str(&text.replace('\n', "\\n"));
            out.push('"');
        }
        out.push('\n');
        let end = tree.subtree_end(i);
        let mut c = i + 1;
        while c < end {
            rec(tree, tokens, source, c, depth + 1, out);
            c = tree.subtree_end(c);
        }
    }
    if !tree.is_empty() {
        rec(tree, tokens, source, 0, 0, out);
    }
}

/// Reconstructs the source bytes from the tree: walks the nodes in
/// pre-order and emits every token the first time a node's range reaches
/// it. Equals `source` iff the root covers the whole token stream and
/// ranges never run backwards — the losslessness half of [`validate`].
pub fn reconstruct(tree: &Tree, tokens: &fors_lex::Tokens, source: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(source.len());
    let mut emit = |from: u32, to: u32| {
        for t in from..to.min(tokens.len() as u32) {
            out.extend_from_slice(tokens.text(t as usize, source));
        }
    };
    let mut pos = 0u32;
    for i in 0..tree.len() {
        let first = tree.first_token[i];
        // a node starting before `pos` would re-emit tokens: visible as a mismatch
        emit(pos.min(first), first);
        pos = first;
    }
    if !tree.is_empty() {
        emit(pos, tree.token_range(0).1);
    }
    out
}

/// Checks every structural invariant later phases rely on. Meant for
/// tests and debug builds; returns the first violation.
///
/// - node 0 is `File`, spans every token and every node;
/// - each node's children lie inside its token range, in order, without
///   overlap (so every token is owned by exactly one innermost node), and
///   inside its `subtree_len`;
/// - the direct children of `File` are header clauses, `UseDecl`s,
///   declarations or `Error`s, and every declaration starts on its own
///   first token (attributes and `pub` are inside it);
/// - an `Error` node never swallows the start of a declaration: no token
///   after its first significant one begins a declaration-sync sequence.
pub fn validate(tree: &Tree, tokens: &fors_lex::Tokens, source: &[u8]) -> Result<(), String> {
    use fors_lex::TokenKind as T;
    let n = tree.len();
    if n == 0 {
        return Err("empty tree".into());
    }
    if tree.kinds[0] != NodeKind::File {
        return Err(format!("root is {:?}", tree.kinds[0]));
    }
    if tree.token_range(0) != (0, tokens.len() as u32) {
        return Err(format!(
            "root spans {:?}, stream has {} tokens",
            tree.token_range(0),
            tokens.len()
        ));
    }
    if tree.subtree_len[0] as usize != n {
        return Err(format!(
            "root subtree_len {} != {n} nodes",
            tree.subtree_len[0]
        ));
    }
    // (end node index, end token, next free token) per open ancestor
    let mut stack: Vec<(usize, u32, u32)> = Vec::new();
    for i in 0..n {
        while stack.last().is_some_and(|&(end, _, _)| end <= i) {
            stack.pop();
        }
        let (first, end_tok) = tree.token_range(i);
        let sub = tree.subtree_len[i] as usize;
        if sub == 0 {
            return Err(format!("node {i}: subtree_len 0"));
        }
        if let Some(&mut (pend, pend_tok, ref mut next_tok)) = stack.last_mut() {
            if i + sub > pend {
                return Err(format!(
                    "node {i} ({:?}): subtree overruns its parent",
                    tree.kinds[i]
                ));
            }
            if first < *next_tok || end_tok > pend_tok {
                return Err(format!(
                    "node {i} ({:?}): tokens {first}..{end_tok} overlap a sibling or leave the parent (free from {}, parent ends {pend_tok})",
                    tree.kinds[i], *next_tok
                ));
            }
            *next_tok = end_tok;
        }
        if stack.len() == 1 {
            let k = tree.kinds[i];
            let header = matches!(
                k,
                NodeKind::ModuleHdr
                    | NodeKind::ContractsClause
                    | NodeKind::NeedsClause
                    | NodeKind::InputsClause
                    | NodeKind::UseDecl
            );
            if !(header || k.is_decl() || k == NodeKind::Error) {
                return Err(format!("node {i}: {k:?} is a direct child of File"));
            }
        }
        if tree.kinds[i] == NodeKind::Error {
            let sig: Vec<usize> = (first as usize..end_tok as usize)
                .filter(|&t| !tokens.kinds[t].is_trivia() && tokens.kinds[t] != T::Error)
                .collect();
            for w in 1..sig.len() {
                let k = tokens.kinds[sig[w]];
                let next = sig.get(w + 1).map(|&t| tokens.kinds[t]);
                let starts_decl = match k {
                    T::KwModule
                    | T::KwUse
                    | T::KwStruct
                    | T::KwEnum
                    | T::KwTrait
                    | T::KwImpl
                    | T::KwConst
                    | T::KwExtern => true,
                    T::KwFn => next == Some(T::Ident),
                    T::Ident => next == Some(T::KwStruct) && tokens.text(sig[w], source) == b"soa",
                    _ => false,
                };
                // the keyword right after a swallowed `pub` is part of the same sync sequence
                if starts_decl && !(w == 1 && tokens.kinds[sig[0]] == T::KwPub) {
                    return Err(format!(
                        "Error node {i} swallows a declaration start at token {}",
                        sig[w]
                    ));
                }
            }
        }
        stack.push((i + sub, end_tok, first));
    }
    if reconstruct(tree, tokens, source) != source {
        return Err("reconstruct() does not reproduce the source".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(src: &str) -> Vec<Diagnostic> {
        let (_, diags) = parse(src.as_bytes());
        diags
    }

    #[test]
    fn empty_file_ok() {
        assert!(check("").is_empty());
    }

    #[test]
    fn smoke_fn() {
        assert!(check("fn f() { let x = 1 + 2; }").is_empty());
    }

    #[test]
    fn round_trip_smoke() {
        let src = b"fn f(let x: i32) -> i32 { x + 1 }\n";
        let (tokens, _) = fors_lex::lex(src);
        let (tree, _) = parse(src);
        assert_eq!(reconstruct(&tree, &tokens, src), src);
    }
}
