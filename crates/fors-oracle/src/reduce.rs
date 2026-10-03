//! The three-stage minimiser (design §7.3, `compiler-architecture.md` §8's
//! "SoA-level delta-debugging reduction").
//!
//! Given a program and a PREDICATE — "the bug still shows": a miscompile
//! (two engines, or a correct and a seeded-miscompiled lowering, disagree),
//! an interpreter panic, or a `ub:` report — the minimiser shrinks the
//! program while the predicate stays true, re-checking it after EVERY
//! candidate step and keeping only candidates that satisfy it:
//!
//! 1. **source level** ([`reduce_source`]): delta debugging over the
//!    program's declarations, then over its statements (CST nodes, removed
//!    by byte range), then expression hoisting (an expression replaced by
//!    one of its sub-expressions), repeated until none shrinks. A candidate
//!    that no longer builds simply fails the predicate.
//! 2. **FMIR level** ([`reduce_fmir`]): unreachable functions dropped;
//!    terminators simplified (`cond_br` to one arm, `try_br` to its `ok`
//!    edge, `switch_discr` to its default, the entry's tail cut to `ret`),
//!    with every block that becomes unreachable emptied to `unreachable`;
//!    then delta debugging over the instructions of every reachable block.
//!    Every candidate is re-VERIFIED (`fors_fmir::verify`) before it is
//!    run: one that does not verify is discarded, never executed.
//! 3. **value level** ([`reduce_values`]): every `const_int` narrowed toward
//!    zero (zero, then the smallest magnitude, by binary search, that keeps
//!    the predicate).
//!
//! The ORDER in which candidates are tried is the only freedom, and it is
//! drawn from one seeded [`Rng`]: the same program, predicate and seed give
//! the same result, byte for byte (`a_reduction_is_reproducible_from_its_seed`).
//!
//! An instruction removed from the pools leaves its value row behind with a
//! retired definition ([`RETIRED`]); a candidate that still READS such a
//! value reads an undefined slot, which the interpreter reports, which no
//! predicate built on [`crate::clean_record`] accepts.

use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{BlockId, InstId};
use fors_fmir::inst::Callee;
use fors_fmir::op::{NO_OPERAND, Op};
use fors_fmir::value::{PARAM_TAG, ValDef};
use fors_syntax::NodeKind;

use crate::Candidate;
use crate::rng::Rng;

/// The definition an instruction's value row gets when the instruction is
/// removed: an `InstId` no row has, so nothing ever defines the value.
pub const RETIRED: InstId = InstId(PARAM_TAG - 1);

/// What one stage did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageReport {
    pub stage: &'static str,
    /// FMIR instructions ([`fmir_size`]) before and after the stage.
    pub before: usize,
    pub after: usize,
    /// Candidates the predicate was asked about, and how many it accepted.
    pub attempts: u64,
    pub accepted: u64,
}

impl StageReport {
    fn new(stage: &'static str, before: usize) -> StageReport {
        StageReport {
            stage,
            before,
            after: before,
            attempts: 0,
            accepted: 0,
        }
    }

    pub fn line(&self) -> String {
        format!(
            "{}: {} -> {} FMIR instructions ({} candidates tried, {} kept)",
            self.stage, self.before, self.after, self.attempts, self.accepted
        )
    }
}

// -- size ---------------------------------------------------------------------

/// The functions reachable from the entry through direct calls, entry first.
pub fn reachable_fns(c: &Candidate) -> Vec<usize> {
    let prog = &c.prog;
    if prog.entry >= prog.fns.len() {
        return Vec::new();
    }
    let mut order = vec![prog.entry];
    let mut i = 0;
    while i < order.len() {
        let decl = &prog.fns[order[i]].decl;
        let live = reachable_blocks(decl);
        for (bid, b) in decl.blocks.all_rows() {
            if !live[bid.index()] {
                continue;
            }
            for row in decl.insts.slice(b.inst_range()) {
                if row.op != Op::CallDirect {
                    continue;
                }
                if let Some(call) = decl.insts.calls.get(row.a as usize)
                    && let Callee::Direct(key) = call.callee
                    && let Some(t) = prog.fns.iter().position(|f| f.decl.decl == key)
                    && !order.contains(&t)
                {
                    order.push(t);
                }
            }
        }
        i += 1;
    }
    order
}

fn successors(decl: &DeclFmir, b: BlockId) -> Vec<BlockId> {
    let t = decl.blocks.row(b).term;
    match t.op {
        Op::Br => vec![BlockId(t.a)],
        Op::CondBr | Op::TryBr => vec![BlockId(t.b), BlockId(t.c)],
        Op::SwitchDiscr => match decl.insts.switches.get(t.a as usize) {
            Some(sw) => {
                let mut v = vec![sw.default];
                let arms = &decl.insts.switch_arms;
                let r = sw.arms.start as usize..(sw.arms.end as usize).min(arms.len());
                v.extend(arms[r].iter().map(|a| a.target));
                v
            }
            None => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// Blocks reachable from the entry and from every deferred body.
pub fn reachable_blocks(decl: &DeclFmir) -> Vec<bool> {
    let n = decl.blocks.len();
    let mut live = vec![false; n];
    let mut stack = vec![decl.entry];
    stack.extend(
        decl.defers
            .get(0..decl.defers.len() as u32)
            .iter()
            .map(|d| d.body),
    );
    while let Some(b) = stack.pop() {
        if b.index() >= n || live[b.index()] {
            continue;
        }
        live[b.index()] = true;
        stack.extend(successors(decl, b));
    }
    live
}

/// FMIR instructions that can execute: over every reachable function's
/// reachable blocks, the instruction rows plus the terminator.
pub fn fmir_size(c: &Candidate) -> usize {
    reachable_fns(c)
        .into_iter()
        .map(|fi| {
            let decl = &c.prog.fns[fi].decl;
            let live = reachable_blocks(decl);
            decl.blocks
                .all_rows()
                .filter(|(b, _)| live[b.index()])
                .map(|(_, r)| r.inst_len as usize + 1)
                .sum::<usize>()
        })
        .sum()
}

// -- stage 1: source ------------------------------------------------------------

fn is_decl(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::FnDecl
            | NodeKind::ExternFnDecl
            | NodeKind::StructDecl
            | NodeKind::EnumDecl
            | NodeKind::TraitDecl
            | NodeKind::ImplDecl
            | NodeKind::ConstDecl
    )
}

fn is_stmt(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::LetStmt
            | NodeKind::AssignStmt
            | NodeKind::ExprStmt
            | NodeKind::ForStmt
            | NodeKind::WhileStmt
            | NodeKind::BreakStmt
            | NodeKind::ContinueStmt
            | NodeKind::ReturnStmt
            | NodeKind::RaiseStmt
            | NodeKind::WithStmt
            | NodeKind::DiscardStmt
    )
}

/// The byte ranges of every declaration (`stmts == false`) or statement
/// node, in source order.
fn units(src: &str, stmts: bool) -> Vec<(usize, usize)> {
    let p = fors_syntax::parse_file(src.as_bytes());
    let mut out = Vec::new();
    // A statement is a statement node, or any direct child of a block (an
    // `if` or `match` in statement position is an expression node there).
    let mut in_block = vec![false; p.tree.len()];
    for i in 0..p.tree.len() {
        if p.tree.kinds[i] == NodeKind::Block {
            for ch in p.tree.children(i) {
                in_block[ch] = true;
            }
        }
    }
    for (i, &k) in p.tree.kinds.iter().enumerate() {
        if (stmts && (is_stmt(k) || in_block[i])) || (!stmts && is_decl(k)) {
            let (first, end) = p.tree.token_range(i);
            let (a, b) = (
                p.tokens.starts[first as usize] as usize,
                p.tokens.starts[end as usize] as usize,
            );
            if b > a {
                out.push((a, b));
            }
        }
    }
    out
}

fn remove_ranges(src: &str, ranges: &[(usize, usize)]) -> String {
    let mut rs = ranges.to_vec();
    rs.sort();
    let mut out = String::with_capacity(src.len());
    let mut at = 0;
    for (a, b) in rs {
        if a > at {
            out.push_str(&src[at..a]);
        }
        at = at.max(b);
    }
    out.push_str(&src[at.min(src.len())..]);
    out
}

/// Complement-only delta debugging over `units(cur, stmts)`: tries removing
/// chunks (in a seeded order), restarts on every success, halves the chunk
/// on a full pass with none. Returns whether anything was removed.
fn ddmin_text(
    cur: &mut String,
    stmts: bool,
    pred: &mut dyn FnMut(&str) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) -> bool {
    let mut any = false;
    let mut chunk = (units(cur, stmts).len() / 2).max(1);
    loop {
        let us = units(cur, stmts);
        if us.is_empty() {
            return any;
        }
        let chunk_now = chunk.min(us.len());
        let mut starts: Vec<usize> = (0..us.len()).step_by(chunk_now).collect();
        rng.shuffle(&mut starts);
        let mut progressed = false;
        for s in starts {
            let set = &us[s..(s + chunk_now).min(us.len())];
            let cand = remove_ranges(cur, set);
            if cand == *cur {
                continue;
            }
            rep.attempts += 1;
            if pred(&cand) {
                rep.accepted += 1;
                *cur = cand;
                any = true;
                progressed = true;
                break;
            }
        }
        if progressed {
            continue;
        }
        if chunk_now <= 1 {
            return any;
        }
        chunk = chunk_now / 2;
    }
}

fn is_compound_expr(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::OrExpr
            | NodeKind::AndExpr
            | NodeKind::NotExpr
            | NodeKind::CmpExpr
            | NodeKind::BitExpr
            | NodeKind::AddExpr
            | NodeKind::MulExpr
            | NodeKind::CastExpr
            | NodeKind::UnaryExpr
            | NodeKind::CallExpr
            | NodeKind::TupleOrParen
    )
}

/// Every `(expression span, sub-expression span)` pair: replacing the
/// former's text by the latter's is one hoisting candidate.
fn hoists(src: &str) -> Vec<((usize, usize), (usize, usize))> {
    let p = fors_syntax::parse_file(src.as_bytes());
    let span = |i: usize| {
        let (first, end) = p.tree.token_range(i);
        (
            p.tokens.starts[first as usize] as usize,
            p.tokens.starts[end as usize] as usize,
        )
    };
    let mut out = Vec::new();
    for i in 0..p.tree.len() {
        if !is_compound_expr(p.tree.kinds[i]) {
            continue;
        }
        let outer = span(i);
        for ch in p.tree.children(i) {
            let inner = span(ch);
            if inner.1 > inner.0 && inner != outer {
                out.push((outer, inner));
            }
        }
    }
    out
}

/// Hoisting: an expression replaced by one of its own sub-expressions
/// (`mix(h, d)` by `d`, `a - b` by `a`), so the source stage can shrink
/// past statements whose VALUE matters but whose wrapping does not.
fn hoist_exprs(
    cur: &mut String,
    pred: &mut dyn FnMut(&str) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) -> bool {
    let mut any = false;
    loop {
        let mut hs = hoists(cur);
        rng.shuffle(&mut hs);
        let mut progressed = false;
        for ((oa, ob), (ia, ib)) in hs {
            let cand = format!("{}{}{}", &cur[..oa], cur[ia..ib].trim(), &cur[ob..]);
            if cand == *cur {
                continue;
            }
            rep.attempts += 1;
            if pred(&cand) {
                rep.accepted += 1;
                *cur = cand;
                any = true;
                progressed = true;
                break;
            }
        }
        if !progressed {
            return any;
        }
    }
}

/// Stage 1. `pred` must hold of `src`; the result is the smallest source
/// this search finds that still satisfies it: declarations, then
/// statements, then expression hoisting, repeated until none shrinks.
pub fn reduce_source(
    src: &str,
    pred: &mut dyn FnMut(&str) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) -> String {
    let mut cur = src.to_string();
    loop {
        let a = ddmin_text(&mut cur, false, pred, rng, rep);
        let b = ddmin_text(&mut cur, true, pred, rng, rep);
        let c = hoist_exprs(&mut cur, pred, rng, rep);
        if !a && !b && !c {
            return cur;
        }
    }
}

// -- stage 2: FMIR ---------------------------------------------------------------

/// `decl` with the rows in `del` removed: block windows, `try_br` operands
/// and value definitions remapped (a removed row's value gets [`RETIRED`]).
/// `None` when a `try_br` names a removed call.
pub fn delete_insts(decl: &DeclFmir, del: &[bool]) -> Option<DeclFmir> {
    for (_, b) in decl.blocks.all_rows() {
        if b.term.op == Op::TryBr && del.get(b.term.a as usize).copied().unwrap_or(false) {
            return None;
        }
    }
    let mut d = decl.clone();
    let keep: Vec<bool> = (0..decl.insts.len())
        .map(|i| !del.get(i).copied().unwrap_or(false))
        .collect();
    let map = d.insts.retain_rows(&keep);
    let blocks: Vec<_> = d.blocks.all_rows().collect();
    for (bid, mut row) in blocks {
        let kept: Vec<u32> = row
            .inst_range()
            .filter_map(|i| map.get(i as usize).copied().flatten())
            .map(|id| id.0)
            .collect();
        row.first_inst = kept.first().copied().unwrap_or(0);
        row.inst_len = kept.len() as u32;
        if row.term.op == Op::TryBr {
            row.term.a = map.get(row.term.a as usize).copied().flatten()?.0;
        }
        d.blocks.set_row(bid, row);
    }
    let vals: Vec<_> = d.vals.all_rows().collect();
    for (vid, mut row) in vals {
        if let ValDef::Inst(i) = row.def() {
            let to = map.get(i.index()).copied().flatten().unwrap_or(RETIRED);
            row.def = ValDef::Inst(to).encode();
            d.vals.set_row(vid, row);
        }
    }
    Some(d)
}

/// Empties every unreachable block to `unreachable` and removes its rows.
fn prune(decl: &DeclFmir) -> Option<DeclFmir> {
    let live = reachable_blocks(decl);
    let mut del = vec![false; decl.insts.len()];
    let mut d = decl.clone();
    let blocks: Vec<_> = decl.blocks.all_rows().collect();
    for (bid, mut row) in blocks {
        if live[bid.index()] {
            continue;
        }
        for i in row.inst_range() {
            if let Some(x) = del.get_mut(i as usize) {
                *x = true;
            }
        }
        row.term.op = Op::Unreachable;
        row.term.a = NO_OPERAND;
        row.term.b = NO_OPERAND;
        row.term.c = NO_OPERAND;
        d.blocks.set_row(bid, row);
    }
    delete_insts(&d, &del)
}

fn verifies(d: &DeclFmir) -> bool {
    fors_fmir::verify::verify(d).is_empty()
}

/// Asks `pred` about `c` with function `fi` replaced by `decl` (if it
/// verifies); keeps it on success.
fn try_decl(
    c: &mut Candidate,
    fi: usize,
    decl: DeclFmir,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rep: &mut StageReport,
) -> bool {
    if !verifies(&decl) {
        return false;
    }
    let mut cand = c.clone();
    cand.prog.fns[fi].decl = decl;
    rep.attempts += 1;
    if pred(&cand) {
        rep.accepted += 1;
        *c = cand;
        true
    } else {
        false
    }
}

fn drop_unreachable_fns(
    c: &mut Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rep: &mut StageReport,
) -> bool {
    let keep = reachable_fns(c);
    if keep.len() == c.prog.fns.len() {
        return false;
    }
    let mut cand = c.clone();
    let mut sorted = keep.clone();
    sorted.sort();
    cand.prog.fns = sorted.iter().map(|&i| c.prog.fns[i].clone()).collect();
    cand.prog.entry = sorted.iter().position(|&i| i == c.prog.entry).unwrap_or(0);
    rep.attempts += 1;
    if pred(&cand) {
        rep.accepted += 1;
        *c = cand;
        true
    } else {
        false
    }
}

fn simplify_terminators(
    c: &mut Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) -> bool {
    let mut any = false;
    let mut fns = reachable_fns(c);
    rng.shuffle(&mut fns);
    for fi in fns {
        let entry_fn = fi == c.prog.entry;
        let mut progressed = true;
        while progressed {
            progressed = false;
            let decl = c.prog.fns[fi].decl.clone();
            let live = reachable_blocks(&decl);
            let mut bids: Vec<BlockId> = decl
                .blocks
                .all_rows()
                .map(|(b, _)| b)
                .filter(|b| live[b.index()])
                .collect();
            rng.shuffle(&mut bids);
            'blocks: for b in bids {
                let row = decl.blocks.row(b);
                let t = row.term;
                let mut terms = Vec::new();
                let br = |to: BlockId| {
                    let mut n = t;
                    n.op = Op::Br;
                    n.a = to.0;
                    n.b = NO_OPERAND;
                    n.c = NO_OPERAND;
                    n
                };
                match t.op {
                    Op::CondBr => {
                        terms.push(br(BlockId(t.b)));
                        terms.push(br(BlockId(t.c)));
                    }
                    Op::TryBr => terms.push(br(BlockId(t.b))),
                    Op::SwitchDiscr => {
                        if let Some(sw) = decl.insts.switches.get(t.a as usize) {
                            terms.push(br(sw.default));
                        }
                    }
                    _ => {}
                }
                // The entry's tail cut: `ret` (no value) ends `main` here.
                if entry_fn && !(t.op == Op::Ret && t.a == NO_OPERAND) {
                    let mut n = t;
                    n.op = Op::Ret;
                    n.a = NO_OPERAND;
                    n.b = NO_OPERAND;
                    n.c = NO_OPERAND;
                    terms.push(n);
                }
                for nt in terms {
                    let mut d = decl.clone();
                    let mut r = row;
                    r.term = nt;
                    d.blocks.set_row(b, r);
                    let Some(d) = prune(&d) else { continue };
                    if try_decl(c, fi, d, pred, rep) {
                        any = true;
                        progressed = true;
                        break 'blocks;
                    }
                }
            }
        }
    }
    any
}

fn delete_instructions(
    c: &mut Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) -> bool {
    let mut any = false;
    let mut fns = reachable_fns(c);
    rng.shuffle(&mut fns);
    for fi in fns {
        let rows = |d: &DeclFmir| -> Vec<u32> {
            let live = reachable_blocks(d);
            d.blocks
                .all_rows()
                .filter(|(b, _)| live[b.index()])
                .flat_map(|(_, r)| r.inst_range())
                .collect()
        };
        let mut chunk = (rows(&c.prog.fns[fi].decl).len() / 2).max(1);
        loop {
            let decl = c.prog.fns[fi].decl.clone();
            let rs = rows(&decl);
            if rs.is_empty() {
                break;
            }
            let chunk_now = chunk.min(rs.len());
            let mut starts: Vec<usize> = (0..rs.len()).step_by(chunk_now).collect();
            rng.shuffle(&mut starts);
            let mut progressed = false;
            for s in starts {
                let mut del = vec![false; decl.insts.len()];
                for &i in &rs[s..(s + chunk_now).min(rs.len())] {
                    del[i as usize] = true;
                }
                let Some(d) = delete_insts(&decl, &del) else {
                    continue;
                };
                if try_decl(c, fi, d, pred, rep) {
                    any = true;
                    progressed = true;
                    break;
                }
            }
            if progressed {
                continue;
            }
            if chunk_now <= 1 {
                break;
            }
            chunk = chunk_now / 2;
        }
    }
    any
}

/// Stage 2: functions, terminators and blocks, instructions — to a fixed
/// point.
pub fn reduce_fmir(
    c: &mut Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) {
    loop {
        let a = drop_unreachable_fns(c, pred, rep);
        let b = simplify_terminators(c, pred, rng, rep);
        let d = delete_instructions(c, pred, rng, rep);
        if !a && !b && !d {
            break;
        }
    }
    rep.after = fmir_size(c);
}

// -- stage 3: values ----------------------------------------------------------------

fn with_const(c: &Candidate, fi: usize, inst: InstId, v: i64) -> Candidate {
    let mut cand = c.clone();
    let decl = &mut cand.prog.fns[fi].decl;
    let mut row = decl.insts.row(inst);
    let bits = v as u64;
    row.a = bits as u32;
    row.b = (bits >> 32) as u32;
    decl.insts.set_row(inst, row);
    cand
}

/// Stage 3: every reachable `const_int` narrowed toward zero.
pub fn reduce_values(
    c: &mut Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    rng: &mut Rng,
    rep: &mut StageReport,
) {
    let mut sites: Vec<(usize, InstId)> = Vec::new();
    for fi in reachable_fns(c) {
        let decl = &c.prog.fns[fi].decl;
        let live = reachable_blocks(decl);
        for (b, r) in decl.blocks.all_rows() {
            if !live[b.index()] {
                continue;
            }
            for i in r.inst_range() {
                if decl.insts.row(InstId(i)).op == Op::ConstInt {
                    sites.push((fi, InstId(i)));
                }
            }
        }
    }
    rng.shuffle(&mut sites);
    for (fi, inst) in sites {
        let row = c.prog.fns[fi].decl.insts.row(inst);
        let v = (((row.b as u64) << 32) | row.a as u64) as i64;
        if v == 0 {
            continue;
        }
        let mut ask = |c: &Candidate, x: i64, rep: &mut StageReport| {
            rep.attempts += 1;
            let cand = with_const(c, fi, inst, x);
            if pred(&cand) {
                rep.accepted += 1;
                Some(cand)
            } else {
                None
            }
        };
        if let Some(n) = ask(c, 0, rep) {
            *c = n;
            continue;
        }
        // Binary search the smallest magnitude, sign kept, in (0, |v|].
        let neg = v < 0;
        let mag = v.unsigned_abs();
        let (mut lo, mut hi) = (0u64, mag);
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            let x = if neg {
                (mid as i64).wrapping_neg()
            } else {
                mid as i64
            };
            match ask(c, x, rep) {
                Some(n) => {
                    *c = n;
                    hi = mid;
                }
                None => lo = mid,
            }
        }
    }
    rep.after = fmir_size(c);
}

// -- the pipeline ---------------------------------------------------------------------

/// A finished reduction: the reduced source, the reduced FMIR program, and
/// one report per stage (source, FMIR, values).
pub struct Minimised {
    pub source: String,
    pub candidate: Candidate,
    pub reports: Vec<StageReport>,
}

/// Runs the three stages over `src`. `build` turns source into FMIR (the
/// correct lowering); `src_pred` judges a source candidate, `fmir_pred` an
/// FMIR candidate. Both must hold of the input, and `fmir_pred` must hold
/// of the source stage's result built by `build`, or the reduction is
/// refused by name.
pub fn minimise(
    src: &str,
    build: &dyn Fn(&str) -> Result<Candidate, String>,
    src_pred: &mut dyn FnMut(&str) -> bool,
    fmir_pred: &mut dyn FnMut(&Candidate) -> bool,
    seed: u64,
) -> Result<Minimised, String> {
    let mut rng = Rng::new(seed);
    let first = build(src)?;
    if !src_pred(src) {
        return Err("the predicate does not hold of the input program".into());
    }
    let mut r1 = StageReport::new("source", fmir_size(&first));
    let source = reduce_source(src, src_pred, &mut rng, &mut r1);
    let mut c = build(&source)?;
    r1.after = fmir_size(&c);
    if !fmir_pred(&c) {
        return Err("the FMIR predicate does not hold of the source stage's result".into());
    }
    let mut r2 = StageReport::new("fmir", r1.after);
    reduce_fmir(&mut c, fmir_pred, &mut rng, &mut r2);
    let mut r3 = StageReport::new("values", r2.after);
    reduce_values(&mut c, fmir_pred, &mut rng, &mut r3);
    Ok(Minimised {
        source,
        candidate: c,
        reports: vec![r1, r2, r3],
    })
}

/// Stages 2 and 3 only, for a program that has no source (a generated one).
pub fn minimise_fmir(
    c: &Candidate,
    pred: &mut dyn FnMut(&Candidate) -> bool,
    seed: u64,
) -> Result<(Candidate, Vec<StageReport>), String> {
    if !pred(c) {
        return Err("the predicate does not hold of the input program".into());
    }
    let mut rng = Rng::new(seed);
    let mut c = c.clone();
    let mut r2 = StageReport::new("fmir", fmir_size(&c));
    reduce_fmir(&mut c, pred, &mut rng, &mut r2);
    let mut r3 = StageReport::new("values", r2.after);
    reduce_values(&mut c, pred, &mut rng, &mut r3);
    Ok((c, vec![r2, r3]))
}

// -- predicates ------------------------------------------------------------------------

/// A record of a run that completed WITHOUT a `ub:` report and without an
/// interpreter refusal or panic — the precondition every miscompile
/// predicate puts on the REFERENCE run, so a reduction can never "succeed"
/// by producing a program whose behaviour is undefined.
pub fn clean_record(c: &Candidate) -> Option<fors_interp::OracleRecord> {
    match crate::run_capped(c, None, crate::REDUCE_STEP_CAP) {
        crate::RunResult::Record(r) if !matches!(r.exit, fors_interp::RecordExit::Ub { .. }) => {
            Some(r)
        }
        _ => None,
    }
}

/// The miscompile predicate: `c` runs cleanly, and `transform(c)` (the
/// "other engine") produces a different record. Only the observable fields
/// are compared — exit, stdout, stderr — never the program digest (which
/// differs by construction) or the step count (an engine may differ there).
pub fn differs_under(c: &Candidate, transform: &dyn Fn(&mut DeclFmir)) -> bool {
    let Some(good) = clean_record(c) else {
        return false;
    };
    let mut other = c.clone();
    for f in &mut other.prog.fns {
        transform(&mut f.decl);
    }
    match crate::run_capped(&other, None, crate::REDUCE_STEP_CAP) {
        crate::RunResult::Record(bad) => {
            bad.exit != good.exit || bad.stdout != good.stdout || bad.stderr != good.stderr
        }
        // The other engine refusing or panicking on a program the reference
        // runs is a disagreement too.
        _ => true,
    }
}

/// The `ub:` predicate: the run ends in a `ub:` report of class `class`.
pub fn ub_of_class(c: &Candidate, class: fors_interp::UbClass) -> bool {
    matches!(
        crate::run_capped(c, None, crate::REDUCE_STEP_CAP),
        crate::RunResult::Record(r) if r.exit_class_is_ub(class)
    )
}

/// The panic predicate: the interpreter panics on `c`.
pub fn panics(c: &Candidate) -> bool {
    matches!(
        crate::run_capped(c, None, crate::REDUCE_STEP_CAP),
        crate::RunResult::Panicked(_)
    )
}

trait UbExit {
    fn exit_class_is_ub(&self, class: fors_interp::UbClass) -> bool;
}

impl UbExit for fors_interp::OracleRecord {
    fn exit_class_is_ub(&self, class: fors_interp::UbClass) -> bool {
        matches!(self.exit, fors_interp::RecordExit::Ub { class: c, .. } if c == class)
    }
}
