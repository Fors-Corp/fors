//! The normative `reduce` tree — the ONE place its shape is written down
//! (design §3.9: "a normative expansion given once in `fors-fmir::reduce.rs`
//! that the interpreter executes and every backend must implement
//! identically"; §5.7 "`reduce` as the normative tree").
//!
//! Normative inputs, verbatim obligations:
//! - ch03 **R11**: `k = ceil(n/B)` leaf blocks of CONSECUTIVE elements; per
//!   block a lane fold (`l_j = x_j; l_j = op(l_j, x_{j+L}); …`, ascending,
//!   accumulator on the LEFT) followed by the fixed pairwise lane combine
//!   `((l0∘l1)∘(l2∘l3))∘((l4∘l5)∘(l6∘l7))` with the lower-numbered lane on
//!   the left; then the `k` block partials combine level by level, adjacent
//!   pairs `(0,1),(2,3),…`, the unpaired last partial carried up unchanged.
//! - ch03 **R11a**: `n = 0` traps `empty-reduce` unless an `identity:` was
//!   supplied; for `n >= 1` the identity MUST NOT participate.
//! - ch03 **R12** (as reworded by owner decision Q3, 2026-10-02): `reduce`
//!   MUST be given its final shape in FMIR, as a function of `(n, B, L)`,
//!   before parallel lowering; where `n` is comptime-known the tree MUST be
//!   explicit. [`reduce_tree`] is that shape function; [`unrolled`] is the
//!   explicit form, and [`shape_table_hash`] pins both.
//! - ch03 **R13(a)**: NO identity padding, ever. A combine node with one
//!   empty operand yields the other operand UNCHANGED, with no `op`
//!   application; a node with two empty operands is empty. The consequence
//!   this module makes checkable: a reduce over `n` elements applies `op`
//!   exactly `n - 1` times ([`op_applications`]).
//! - ch03 **R13(b)/(c)**: `-0.0` and NaN flow through `op` in tree order and
//!   nothing is reordered, normalised or dropped. For floats the TREE is
//!   normative, not the fold: `[1.0, 1e16, -1e16, 1.0]` folds to `1.0` and
//!   the tree computes `0.0`, and the tree is the right answer.
//!
//! Lifted from the verified spike `spikes/reduce-tree/reduce_tree.rs`, which
//! stays where it is (standalone, outside the workspace) as the derivation
//! record. This module is the production copy: `fors-lower` builds the
//! explicit tree from it, `fors-interp` executes it, and both read the same
//! [`REDUCE_BLOCK`]/[`REDUCE_LANES`].

/// ch03 R11's `REDUCE_BLOCK`: a target-independent literal. MUST NOT depend
/// on hardware lane width, grain, threads, locales, target or build flags,
/// and is not overridable (ch03 open question 2, drafted "no").
pub const REDUCE_BLOCK: u32 = 256;

/// ch03 R11's `REDUCE_LANES` (owner decision D3, 2026-09-19): eight LOGICAL
/// lanes. A target with fewer than eight (or no) vector lanes computes the
/// same eight by scalar emulation; a wider target MUST NOT use more.
pub const REDUCE_LANES: u32 = 8;

/// One lane of one leaf block: the global element indices it folds, in
/// ascending order. An empty `elems` is an EMPTY lane — skipped in the
/// combine, never padded (R13a).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LaneAssign {
    pub lane: u32,
    pub elems: Vec<u32>,
}

/// One leaf block: the consecutive elements `[start, start + len)`, split
/// across exactly `L` lanes (some possibly empty).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BlockAssign {
    pub block: u32,
    pub start: u32,
    pub len: u32,
    pub lanes: Vec<LaneAssign>,
}

/// The shape of `reduce(op, xs)` for `len(xs) == n`: the partition and the
/// leaf lanes. A pure function of `(n, B, L)` and of nothing else.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReduceTree {
    pub n: u32,
    pub b: u32,
    pub l: u32,
    pub blocks: Vec<BlockAssign>,
}

/// `reduce_tree(n, B, L)` — ch03 R11's partition and lane assignment.
/// `ceil(n / B)` consecutive blocks; lane `j` of a block holds the
/// block-relative indices `j, j + L, j + 2L, …`. `n == 0` yields zero blocks
/// (R11a's trap-or-identity decision belongs to the executor, not here).
///
/// # Panics
/// If `b` or `l` is zero — a `reduce_tree` instruction carrying either is a
/// lowering bug the verifier rejects before anything reaches here.
pub fn reduce_tree(n: u32, b: u32, l: u32) -> ReduceTree {
    assert!(b >= 1, "block size B must be >= 1");
    assert!(l >= 1, "lane count L must be >= 1");
    let mut blocks: Vec<BlockAssign> = Vec::new();
    let mut start = 0u32;
    while start < n {
        let len = (n - start).min(b);
        let mut lanes = Vec::with_capacity(l as usize);
        for lane in 0..l {
            let elems: Vec<u32> = (lane..len).step_by(l as usize).map(|t| start + t).collect();
            lanes.push(LaneAssign { lane, elems });
        }
        blocks.push(BlockAssign {
            block: blocks.len() as u32,
            start,
            len,
            lanes,
        });
        start += len;
    }
    ReduceTree { n, b, l, blocks }
}

/// Pairwise levels `(0,1),(2,3),…`; an unpaired last item is carried up
/// UNCHANGED (R11's block combine, and — over exactly `L` items — R11's
/// fixed lane combine `((l0∘l1)∘(l2∘l3))∘((l4∘l5)∘(l6∘l7))`).
///
/// `None` is "empty": a node with one empty side passes the other side
/// through with NO `op` application, and a node with two empty sides stays
/// empty (R13a — this is the one function that must never insert a neutral
/// element).
fn combine_levels<T, E, F>(mut items: Vec<Option<T>>, pair: &mut F) -> Result<Option<T>, E>
where
    F: FnMut(T, T) -> Result<T, E>,
{
    while items.len() > 1 {
        let mut next = Vec::with_capacity(items.len().div_ceil(2));
        let mut it = items.into_iter();
        loop {
            match (it.next(), it.next()) {
                (Some(a), Some(b)) => next.push(match (a, b) {
                    (None, None) => None,
                    (Some(v), None) | (None, Some(v)) => Some(v),
                    (Some(x), Some(y)) => Some(pair(x, y)?),
                }),
                (Some(a), None) => next.push(a),
                (None, _) => break,
            }
        }
        items = next;
    }
    Ok(items.into_iter().next().flatten())
}

/// Evaluates the tree over `xs` with `op`, in exactly R11's order. `op` is
/// fallible so a trapping integer `op` reports its trap instead of panicking.
/// Returns `None` only for `n == 0` (R11a's caller-side decision).
///
/// # Panics
/// If `xs.len()` disagrees with `tree.n`.
pub fn reduce_eval<T, E, F>(tree: &ReduceTree, xs: &[T], op: &mut F) -> Result<Option<T>, E>
where
    T: Clone,
    F: FnMut(T, T) -> Result<T, E>,
{
    assert_eq!(xs.len(), tree.n as usize, "values must match the tree's n");
    let mut partials: Vec<Option<T>> = Vec::with_capacity(tree.blocks.len());
    for block in &tree.blocks {
        let mut lanes: Vec<Option<T>> = Vec::with_capacity(block.lanes.len());
        for lane in &block.lanes {
            // Lane fold: accumulator is the LEFT operand, ascending index.
            let mut acc: Option<T> = None;
            for &e in &lane.elems {
                let rhs = xs[e as usize].clone();
                acc = Some(match acc {
                    None => rhs,
                    Some(a) => op(a, rhs)?,
                });
            }
            lanes.push(acc);
        }
        partials.push(combine_levels(lanes, op)?);
    }
    combine_levels(partials, op)
}

/// The comptime-`n` explicit tree (ch03 R12 as reworded by Q3: "where `n` is
/// comptime-known the tree MUST be explicit"). `Op`'s left child is the left
/// operand.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Elem(u32),
    Op(Box<Expr>, Box<Expr>),
}

/// Builds the explicit tree by an INDEPENDENT walk — its own partition loop,
/// its own lane fold and its own level pairing, sharing no code with
/// [`reduce_tree`]/[`reduce_eval`]. That independence is the whole point:
/// `comptime_and_runtime_forms_agree` (and `fors-lower`'s emission check)
/// compare two separately written derivations of R11, so a mistake in either
/// one is visible instead of cancelling out.
///
/// `None` for `n == 0` (R11a).
///
/// # Panics
/// If `b` or `l` is zero.
pub fn unrolled(n: u32, b: u32, l: u32) -> Option<Expr> {
    assert!(b >= 1, "block size B must be >= 1");
    assert!(l >= 1, "lane count L must be >= 1");
    if n == 0 {
        return None;
    }
    // Own level pairing: adjacent pairs, unpaired last carried up, empty
    // sides passed through with no node created (R13a).
    fn levels(mut items: Vec<Option<Expr>>) -> Option<Expr> {
        while items.len() > 1 {
            let mut next: Vec<Option<Expr>> = Vec::new();
            let mut i = 0;
            while i < items.len() {
                if i + 1 < items.len() {
                    let a = items[i].clone();
                    let bb = items[i + 1].clone();
                    next.push(match (a, bb) {
                        (None, None) => None,
                        (Some(v), None) | (None, Some(v)) => Some(v),
                        (Some(x), Some(y)) => Some(Expr::Op(Box::new(x), Box::new(y))),
                    });
                } else {
                    next.push(items[i].clone());
                }
                i += 2;
            }
            items = next;
        }
        items.into_iter().next().flatten()
    }
    let mut partials: Vec<Option<Expr>> = Vec::new();
    let mut start = 0u32;
    while start < n {
        let len = if n - start < b { n - start } else { b };
        let mut lanes: Vec<Option<Expr>> = Vec::new();
        for lane in 0..l {
            let mut acc: Option<Expr> = None;
            let mut t = lane;
            while t < len {
                let e = Expr::Elem(start + t);
                acc = Some(match acc {
                    None => e,
                    Some(a) => Expr::Op(Box::new(a), Box::new(e)),
                });
                t += l;
            }
            lanes.push(acc);
        }
        partials.push(levels(lanes));
        start += len;
    }
    levels(partials)
}

/// Evaluates an explicit tree (left child = left operand).
pub fn eval_expr<T, E, F>(e: &Expr, xs: &[T], op: &mut F) -> Result<T, E>
where
    T: Clone,
    F: FnMut(T, T) -> Result<T, E>,
{
    match e {
        Expr::Elem(i) => Ok(xs[*i as usize].clone()),
        Expr::Op(a, b) => {
            let l = eval_expr(a, xs, op)?;
            let r = eval_expr(b, xs, op)?;
            op(l, r)
        }
    }
}

/// Renders an explicit tree as an s-expression with atoms `x{i}` — the form
/// ch03's own `reduce_shape_reference` worked examples use, and the form
/// `fors-lower`'s emission test compares against.
pub fn render(e: &Expr) -> String {
    match e {
        Expr::Elem(i) => format!("x{i}"),
        Expr::Op(a, b) => format!("({} {})", render(a), render(b)),
    }
}

/// How many times `op` is applied for `n` elements. With NO identity padding
/// every application consumes two values and produces one, from `n` leaves
/// down to one result, so the count is exactly `n - 1` (and `0` for `n == 0`
/// and `n == 1`). R13(a) in one number.
pub fn op_applications(n: u32) -> u32 {
    n.saturating_sub(1)
}

/// The serial left fold `((x0∘x1)∘x2)…`. Present only so tests can state
/// what `reduce` is NOT: ch03 R11 says the tree equals this fold only for
/// `n <= 3`.
pub fn left_fold(n: u32) -> Option<Expr> {
    if n == 0 {
        return None;
    }
    let mut acc = Expr::Elem(0);
    for i in 1..n {
        acc = Expr::Op(Box::new(acc), Box::new(Expr::Elem(i)));
    }
    Some(acc)
}

fn fnv1a(h: &mut u64, bytes: &[u8]) {
    for &byte in bytes {
        *h ^= byte as u64;
        *h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
}

/// A stable hash of the whole shape table for `n` in `0..upto`: the
/// partition, every lane's element list, and the explicit tree's rendering.
/// Committed as [`REDUCE_SHAPE_TABLE_HASH_1024`] so that ANY change to the
/// tree — a reordered operand, a different tail rule, a changed `B` or `L` —
/// is a one-line visible diff in a test instead of a silent bit-pattern
/// change in every float program (ch05 R17's differential corpus).
pub fn shape_table_hash(upto: u32, b: u32, l: u32) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for n in 0..upto {
        fnv1a(&mut h, &n.to_le_bytes());
        let t = reduce_tree(n, b, l);
        fnv1a(&mut h, &(t.blocks.len() as u32).to_le_bytes());
        for blk in &t.blocks {
            fnv1a(&mut h, &blk.block.to_le_bytes());
            fnv1a(&mut h, &blk.start.to_le_bytes());
            fnv1a(&mut h, &blk.len.to_le_bytes());
            for lane in &blk.lanes {
                fnv1a(&mut h, &lane.lane.to_le_bytes());
                fnv1a(&mut h, &(lane.elems.len() as u32).to_le_bytes());
                for e in &lane.elems {
                    fnv1a(&mut h, &e.to_le_bytes());
                }
            }
        }
        match unrolled(n, b, l) {
            None => fnv1a(&mut h, b"<empty>"),
            Some(e) => fnv1a(&mut h, render(&e).as_bytes()),
        }
    }
    h
}

/// `shape_table_hash(1024, REDUCE_BLOCK, REDUCE_LANES)`, committed.
pub const REDUCE_SHAPE_TABLE_HASH_1024: u64 = 0x7682_a325_6bac_f59e;

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    const B: u32 = REDUCE_BLOCK;
    const L: u32 = REDUCE_LANES;

    fn add(a: i64, b: i64) -> Result<i64, Infallible> {
        Ok(a.wrapping_add(b))
    }

    /// Deterministic pseudo-values spanning negative and positive, no RNG.
    fn vals(n: u32) -> Vec<i64> {
        (0..n)
            .map(|i| ((i as u64).wrapping_mul(2_654_435_761) % 1000) as i64 - 500)
            .collect()
    }

    #[test]
    fn constants_are_the_spec_literals() {
        assert_eq!(REDUCE_BLOCK, 256, "ch03 R11");
        assert_eq!(REDUCE_LANES, 8, "ch03 R11, owner decision D3");
    }

    /// F5 gate unit test: the shape table over `n in 0..1024` hashes to a
    /// committed constant, so a later change to the tree is a visible diff.
    #[test]
    fn reduce_shape_table_hash() {
        assert_eq!(
            shape_table_hash(1024, B, L),
            REDUCE_SHAPE_TABLE_HASH_1024,
            "the reduce shape changed; if that was intended, ch03 R11/R13 \
             and every pinned float value change with it"
        );
        // The hash is a function of (n, B, L) and nothing else: recomputing
        // it twice agrees, and a different B or L gives a different table.
        assert_eq!(shape_table_hash(1024, B, L), shape_table_hash(1024, B, L));
        assert_ne!(shape_table_hash(1024, 4, L), REDUCE_SHAPE_TABLE_HASH_1024);
        assert_ne!(shape_table_hash(1024, B, 4), REDUCE_SHAPE_TABLE_HASH_1024);
    }

    /// F5 gate unit test: ch03 R11's own claim — "it equals the serial left
    /// fold only for `n <= 3`" — as a structural statement over the whole
    /// table, plus the float witness that makes the difference observable.
    #[test]
    fn reduce_equals_left_fold_only_below_4() {
        for n in 0..1024u32 {
            let tree = unrolled(n, B, L);
            let fold = left_fold(n);
            if n < 4 {
                assert_eq!(tree, fold, "n={n} must equal the left fold");
            } else {
                assert_ne!(tree, fold, "n={n} must NOT equal the left fold");
            }
        }
        // And it is not merely a different shape: with a non-associative
        // float `op` the two give different answers, and the TREE is
        // normative (R13b/c, design §3.9's FLOAT NOTE).
        let xs = [1.0f64, 1e16, -1e16, 1.0];
        let mut plus = |a: f64, b: f64| -> Result<f64, Infallible> { Ok(a + b) };
        let tree = reduce_eval(&reduce_tree(4, B, L), &xs, &mut plus)
            .unwrap()
            .unwrap();
        let fold = eval_expr(&left_fold(4).unwrap(), &xs, &mut plus).unwrap();
        assert_eq!(tree, 0.0, "the tree is (1.0+1e16)+(-1e16+1.0)");
        assert_eq!(fold, 1.0, "the left fold is ((1.0+1e16)-1e16)+1.0");
        assert_ne!(tree, fold);
    }

    /// F5 gate unit test: R13(a). `op` is called exactly as many times as
    /// the tree has internal nodes — `n - 1` — and never with an inserted
    /// identity. A single padded lane or block would raise the count.
    #[test]
    fn reduce_no_identity_padding() {
        for n in 0..1024u32 {
            let xs = vals(n);
            let mut calls = 0u32;
            let mut counting = |a: i64, b: i64| -> Result<i64, Infallible> {
                calls += 1;
                add(a, b)
            };
            let got = reduce_eval(&reduce_tree(n, B, L), &xs, &mut counting).unwrap();
            assert_eq!(calls, op_applications(n), "op application count at n={n}");
            assert_eq!(got.is_some(), n > 0, "n={n}");
            // The same bound for the explicit form.
            if let Some(e) = unrolled(n, B, L) {
                let mut calls2 = 0u32;
                let mut counting2 = |a: i64, b: i64| -> Result<i64, Infallible> {
                    calls2 += 1;
                    add(a, b)
                };
                eval_expr(&e, &xs, &mut counting2).unwrap();
                assert_eq!(calls2, op_applications(n), "unrolled op count at n={n}");
            }
        }
    }

    /// F5's agreement assertion: the comptime-`n` explicit form and the
    /// runtime-length shape function agree on every `n` in `0..1024`, both
    /// structurally (same `op` sequence over the same operands) and on
    /// values.
    #[test]
    fn comptime_and_runtime_forms_agree() {
        for n in 0..1024u32 {
            let xs = vals(n);
            // Structural: record the operand pairs each form applies, in
            // order, as rendered s-expressions over symbolic atoms.
            let names: Vec<String> = (0..n).map(|i| format!("x{i}")).collect();
            let mut cat =
                |a: String, b: String| -> Result<String, Infallible> { Ok(format!("({a} {b})")) };
            let from_tree = reduce_eval(&reduce_tree(n, B, L), &names, &mut cat).unwrap();
            let from_unrolled = unrolled(n, B, L).map(|e| render(&e));
            assert_eq!(from_tree, from_unrolled, "shape disagreement at n={n}");
            // Numeric, with a trapping-shaped fallible op.
            let mut plus = |a: i64, b: i64| -> Result<i64, Infallible> { add(a, b) };
            let v_tree = reduce_eval(&reduce_tree(n, B, L), &xs, &mut plus).unwrap();
            let v_unrolled = unrolled(n, B, L).map(|e| eval_expr(&e, &xs, &mut plus).unwrap());
            assert_eq!(v_tree, v_unrolled, "value disagreement at n={n}");
        }
    }

    #[test]
    fn partition_matches_the_spec_examples() {
        let t = reduce_tree(257, B, L);
        assert_eq!(t.blocks.len(), 2);
        assert_eq!((t.blocks[0].start, t.blocks[0].len), (0, 256));
        assert_eq!((t.blocks[1].start, t.blocks[1].len), (256, 1));
        assert_eq!(t.blocks[1].lanes[0].elems, vec![256]);
        assert!(t.blocks[1].lanes[1..].iter().all(|l| l.elems.is_empty()));
        let full = reduce_tree(256, B, L);
        for lane in &full.blocks[0].lanes {
            assert_eq!(lane.elems.len(), 32);
        }
        assert_eq!(
            full.blocks[0].lanes[0].elems,
            (0..32).map(|k| k * 8).collect::<Vec<u32>>()
        );
        assert!(reduce_tree(0, B, L).blocks.is_empty());
    }

    /// Design §3.9's hand-checked shapes, which are also the corpus's own
    /// `detail:` lines for `reduce-n7/n9`.
    #[test]
    fn worked_shapes_match_the_design_and_the_corpus() {
        assert_eq!(
            render(&unrolled(7, B, L).unwrap()),
            "(((x0 x1) (x2 x3)) ((x4 x5) x6))"
        );
        assert_eq!(
            render(&unrolled(8, B, L).unwrap()),
            "(((x0 x1) (x2 x3)) ((x4 x5) (x6 x7)))"
        );
        assert_eq!(
            render(&unrolled(9, B, L).unwrap()),
            "((((x0 x8) x1) (x2 x3)) ((x4 x5) (x6 x7)))"
        );
        assert_eq!(render(&unrolled(1, B, L).unwrap()), "x0");
        // k = 3 blocks with B = 4: the odd tail block is carried up.
        assert_eq!(
            render(&unrolled(9, 4, L).unwrap()),
            "((((x0 x1) (x2 x3)) ((x4 x5) (x6 x7))) x8)"
        );
    }

    /// The pinned corpus values, computed here before any interpreter is in
    /// the picture: `xi = 2^i` with `op = -` for n = 1/7/8/9, and all-ones
    /// with `op = -` for n = 257.
    #[test]
    fn pinned_corpus_values() {
        let mut sub = |a: f64, b: f64| -> Result<f64, Infallible> { Ok(a - b) };
        let pow2 = |n: u32| -> Vec<f64> { (0..n).map(|i| (1u64 << i) as f64).collect() };
        for (n, want) in [(1u32, 1.0f64), (7, 83.0), (8, -45.0), (9, -301.0)] {
            let xs = pow2(n);
            let got = reduce_eval(&reduce_tree(n, B, L), &xs, &mut sub)
                .unwrap()
                .unwrap();
            assert_eq!(got, want, "n={n}");
        }
        let ones = vec![1.0f64; 257];
        let got = reduce_eval(&reduce_tree(257, B, L), &ones, &mut sub)
            .unwrap()
            .unwrap();
        assert_eq!(got, -1.0);
    }

    /// The lower-numbered lane / accumulator / left partial is the LEFT
    /// operand of every `op` application (R11, D3's verifier addition).
    #[test]
    fn lower_operand_is_always_on_the_left() {
        let mut sub = |a: f64, b: f64| -> Result<f64, Infallible> { Ok(a - b) };
        let got = reduce_eval(&reduce_tree(2, B, L), &[5.0, 3.0], &mut sub).unwrap();
        assert_eq!(got, Some(2.0), "flipped operands would give -2.0");
        // Lane fold first, and it is `x0` on the left of `x8` at n = 9.
        let mut first: Option<(String, String)> = None;
        let names: Vec<String> = (0..9).map(|i| format!("x{i}")).collect();
        let mut rec = |a: String, b: String| -> Result<String, Infallible> {
            if first.is_none() {
                first = Some((a.clone(), b.clone()));
            }
            Ok(format!("({a} {b})"))
        };
        reduce_eval(&reduce_tree(9, B, L), &names, &mut rec).unwrap();
        assert_eq!(first, Some(("x0".into(), "x8".into())));
    }

    /// A fallible `op` reports its error from inside the tree instead of
    /// panicking — the shape the interpreter needs for a trapping integer
    /// `op` (ch03 R2).
    #[test]
    fn a_failing_op_propagates() {
        let mut boom = |_a: i64, _b: i64| -> Result<i64, &'static str> { Err("overflow") };
        assert_eq!(
            reduce_eval(&reduce_tree(5, B, L), &vals(5), &mut boom),
            Err("overflow")
        );
        // n = 1 applies `op` zero times, so it cannot fail.
        assert_eq!(
            reduce_eval(&reduce_tree(1, B, L), &vals(1), &mut boom),
            Ok(Some(vals(1)[0]))
        );
    }
}
