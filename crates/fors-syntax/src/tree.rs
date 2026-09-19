//! The flat, lossless syntax tree: struct-of-arrays columns in pre-order, no
//! per-node heap allocation. A node's `[first_token, first_token+token_len)`
//! is a raw-token-index range (the lexer's *full* stream, trivia included)
//! that is the union of the node itself and every descendant; `subtree_len`
//! is the number of nodes (self + all descendants), so a subtree is always
//! the contiguous slice `[i, i + subtree_len[i])` of these columns — a
//! sibling can be skipped without walking its interior.
//!
//! Every raw token is owned by exactly one node: the innermost node whose
//! range contains it (for an interior node these are its keywords,
//! operators and delimiters, i.e. the gaps between its children). Trivia
//! and lexical-error tokens are *leading*: they belong to the same node as
//! the significant token that follows them, so a top-level declaration's
//! range starts at the comments above it and the file's trailing trivia
//! belongs to `File` (with the `Eof` token).
//!
//! The direct children of node 0 (`File`) are the header clauses, the
//! `use` declarations and one node per top-level declaration (attributes
//! and `pub` included), each a contiguous token range: see
//! [`Tree::children`].

use crate::node_kind::NodeKind;

pub struct Tree {
    pub kinds: Vec<NodeKind>,
    pub first_token: Vec<u32>,
    pub token_len: Vec<u32>,
    pub subtree_len: Vec<u32>,
}

impl Tree {
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }

    /// Raw token range `[first, first+len)` node `i` spans.
    pub fn token_range(&self, i: usize) -> (u32, u32) {
        (self.first_token[i], self.first_token[i] + self.token_len[i])
    }

    /// Whether node `i` has no children.
    pub fn is_leaf(&self, i: usize) -> bool {
        self.subtree_len[i] == 1
    }

    /// Index one past the end of node `i`'s subtree.
    pub fn subtree_end(&self, i: usize) -> usize {
        i + self.subtree_len[i] as usize
    }

    /// Direct children of node `i`, as their starting indices.
    pub fn children(&self, i: usize) -> ChildIter<'_> {
        ChildIter { tree: self, next: i + 1, end: self.subtree_end(i) }
    }
}

pub struct ChildIter<'a> {
    tree: &'a Tree,
    next: usize,
    end: usize,
}

impl<'a> Iterator for ChildIter<'a> {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        if self.next >= self.end {
            return None;
        }
        let cur = self.next;
        self.next = self.tree.subtree_end(cur);
        Some(cur)
    }
}

const NONE: u32 = u32::MAX;

/// Builds a [`Tree`]. Nodes are recorded in creation order, which is
/// pre-order except for *wrappers* (`wrap_last_sibling`: `a` becomes
/// `Call(a)` only once `(` is seen). A wrapper is appended like any other
/// node and linked from the subtree it encloses; [`Self::finish`] emits the
/// final pre-order columns in one linear pass. Nothing is ever inserted in
/// the middle of a column, so building is O(nodes) on any input.
pub struct TreeBuilder {
    kinds: Vec<NodeKind>,
    first_token: Vec<u32>,
    end_token: Vec<u32>,
    /// Creation index one past the node's last descendant.
    end_idx: Vec<u32>,
    /// Creation index where the node's subtree starts: itself for a plain
    /// node, the enclosed sibling's start for a wrapper.
    start_of: Vec<u32>,
    /// The wrapper that must be emitted directly before this node.
    wrapper: Vec<u32>,
    stack: Vec<u32>,
    cur_token: u32,
    /// The most recently finished child of the innermost open node; reset
    /// by `start_node`, so a stale sibling can never be wrapped.
    last_closed: u32,
}

impl Default for TreeBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl TreeBuilder {
    pub fn new() -> Self {
        TreeBuilder {
            kinds: Vec::new(),
            first_token: Vec::new(),
            end_token: Vec::new(),
            end_idx: Vec::new(),
            start_of: Vec::new(),
            wrapper: Vec::new(),
            stack: Vec::new(),
            cur_token: 0,
            last_closed: NONE,
        }
    }

    pub fn with_capacity(nodes: usize) -> Self {
        let mut b = Self::new();
        b.kinds.reserve(nodes);
        b.first_token.reserve(nodes);
        b.end_token.reserve(nodes);
        b.end_idx.reserve(nodes);
        b.start_of.reserve(nodes);
        b.wrapper.reserve(nodes);
        b
    }

    pub fn cur_token(&self) -> u32 {
        self.cur_token
    }

    fn push(&mut self, kind: NodeKind, first_token: u32, start_of: u32) -> u32 {
        let idx = self.kinds.len() as u32;
        self.kinds.push(kind);
        self.first_token.push(first_token);
        self.end_token.push(first_token);
        self.end_idx.push(idx + 1);
        self.start_of.push(if start_of == NONE { idx } else { start_of });
        self.wrapper.push(NONE);
        self.stack.push(idx);
        idx
    }

    pub fn start_node(&mut self, kind: NodeKind) {
        self.push(kind, self.cur_token, NONE);
        self.last_closed = NONE;
    }

    pub fn finish_node(&mut self) {
        let Some(idx) = self.stack.pop() else { return };
        let i = idx as usize;
        self.end_token[i] = self.cur_token;
        self.end_idx[i] = self.kinds.len() as u32;
        self.last_closed = idx;
    }

    /// Retroactively wraps the most recently finished sibling subtree in a
    /// new node of `kind`. The new node is left open — call `finish_node`
    /// once its own extra tokens/children have been parsed. With no
    /// finished sibling it degrades to `start_node`.
    pub fn wrap_last_sibling(&mut self, kind: NodeKind) {
        let inner = self.last_closed;
        if inner == NONE {
            self.start_node(kind);
            return;
        }
        let i = inner as usize;
        let idx = self.push(kind, self.first_token[i], self.start_of[i]);
        self.wrapper[i] = idx;
        self.last_closed = NONE;
    }

    /// Relabels the currently open node (a production recognised only
    /// after some of its children were parsed under a tentative kind).
    pub fn set_current_kind(&mut self, kind: NodeKind) {
        if let Some(&idx) = self.stack.last() {
            self.kinds[idx as usize] = kind;
        }
    }

    /// Relabels the most recently finished sibling (ch07 rule 11: a bare
    /// path generic argument turns out to seed a constant expression).
    pub fn set_last_kind(&mut self, kind: NodeKind) {
        if self.last_closed != NONE {
            self.kinds[self.last_closed as usize] = kind;
        }
    }

    /// Advances the raw-token cursor by `n` (a significant token plus its
    /// leading trivia). The tree only ever stores indices into `Tokens`.
    pub fn bump_raw(&mut self, n: u32) {
        self.cur_token += n;
    }

    pub fn empty_node(&mut self, kind: NodeKind) {
        self.start_node(kind);
        self.finish_node();
    }

    pub fn finish(mut self) -> Tree {
        while !self.stack.is_empty() {
            self.finish_node();
        }
        let n = self.kinds.len();
        let mut tree = Tree {
            kinds: vec![NodeKind::Error; n],
            first_token: vec![0; n],
            token_len: vec![0; n],
            subtree_len: vec![0; n],
        };
        let mut out = 0usize;
        for i in 0..n {
            if self.start_of[i] as usize != i {
                continue; // a wrapper: emitted with the subtree it encloses
            }
            let mut chain = 1usize;
            let mut j = i;
            while self.wrapper[j] != NONE {
                j = self.wrapper[j] as usize;
                chain += 1;
            }
            // outermost wrapper first, the plain node last
            let mut pos = out + chain;
            let mut j = i;
            loop {
                pos -= 1;
                tree.kinds[pos] = self.kinds[j];
                tree.first_token[pos] = self.first_token[j];
                tree.token_len[pos] = self.end_token[j] - self.first_token[j];
                tree.subtree_len[pos] = self.end_idx[j] - self.start_of[j];
                if self.wrapper[j] == NONE {
                    break;
                }
                j = self.wrapper[j] as usize;
            }
            out += chain;
        }
        tree
    }
}
