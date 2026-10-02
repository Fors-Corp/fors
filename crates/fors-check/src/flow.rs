//! The flow pass (design §7.9, increment I8): ONE forward walk over a
//! body's use tape, deciding the ownership obligations ch09 inherits from
//! ch01 — Rule 3 (a `let` parameter is never moved from), Rule 4a(a)-(e)
//! (use after move, a move inside a loop, a partial move, a move out of a
//! `let`/`inout` parameter, a move of a captured place) and Rule 8's
//! two-valued merge (every path reaching a join, a loop head or a loop
//! exit must agree on each place's liveness) — and rendering ch09 Rule
//! 46's mandatory message whenever the move that caused the fault was an
//! implicit receiver move.
//!
//! The pass computes nothing typing did not already write down. The tape
//! says WHICH place each event touched and WHY ([`Cause`]); the CST says
//! which `if`/`match` alternative, loop, closure or `defer` body the
//! event sits in; the recorded type of a block says whether control falls
//! out of its end. The state is one set of dead places, two-valued per
//! place. On entering a region the state is saved; an alternative hands
//! the state it ends with to the join, where the paths that fall through
//! are compared: a place dead on every one of them stays dead, a place
//! dead on some and live on others is Rule 8's disagreement, reported
//! once. There is no fixpoint, no second analysis, no "maybe live" state
//! and no drop flag (ch01 Rule 8's round-6 note forbids all three).
//!
//! Rule 4 and Rule 5 (definite initialisation of a `sink`/`set` parameter
//! on every path) are NOT decided here: they need the dataflow this pass
//! deliberately does not run (design §8's ch01 R4, R5 row puts them in
//! M3). ch01 Rules 22-23f (linearity, `defer`) read this same tape and
//! are increment I8b's: a `defer` body's moves are confined to it here.

use fors_fir::sig::Conv;
use fors_fir::ty::{NO_TY, TY_ERROR, TY_NEVER};
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::paths::own_span;
use fors_syntax::NodeKind;

use crate::body::BodyCx;
use crate::lower::FileCtx;
use crate::tape::{Cause, PlaceId, Seg, UseKind, UseTape};
use crate::wf::Wf;

/// What a syntactic region does to the liveness state.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RegionKind {
    /// An `if` chain or a `match` as a whole: the point where its
    /// alternatives merge (ch01 Rule 8). `implicit_alt` is an `if` with no
    /// trailing `else`, whose missing alternative is an empty path.
    Join { what: Joined, implicit_alt: bool },
    /// One alternative of the join at index `join`: a block of the `if`
    /// chain, or an arm.
    Alt { join: usize },
    /// A loop body (Rule 4a(b), Rule 8 at the loop head and the loop
    /// exit).
    Loop,
    /// A closure body: it does not run here, and must not move a place
    /// it captured (Rule 4a(e)).
    Closure,
    /// A `defer`/`errdefer` body: it runs at an exit, not here (ch01
    /// Rule 23d is I8b's).
    Defer,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Joined {
    If,
    Match,
}

impl Joined {
    fn word(self) -> &'static str {
        match self {
            Joined::If => "`if`",
            Joined::Match => "`match`",
        }
    }
}

#[derive(Clone, Copy)]
struct Region {
    kind: RegionKind,
    /// The subtree whose events belong to the region.
    start: u32,
    end: u32,
    /// The span that decides whether a place is declared INSIDE this
    /// region. For a `for` loop it is the whole statement, because the
    /// loop's own binding is declared by the header, outside the body
    /// block but not "outside the loop"; for an alternative it is the
    /// whole `if`/`match`, so that nothing declared in a condition or a
    /// pattern survives the join.
    scope_start: u32,
    scope_end: u32,
    /// The node whose recorded type says whether control falls out of
    /// the region's end: an alternative's block or arm body, a loop's
    /// body block.
    body: u32,
}

impl Region {
    fn holds(&self, n: u32) -> bool {
        n >= self.start && n < self.end
    }

    /// Whether the place introduced at `n` belongs to this region.
    fn declares(&self, n: u32) -> bool {
        n >= self.scope_start && n < self.scope_end
    }
}

/// Where control goes when it leaves a region's end.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Target {
    /// Into the code that follows.
    Falls,
    /// Out of the body (`return`, `raise`, a call that never returns).
    Exit,
    /// To the enclosing loop's exit.
    Break,
    /// To the enclosing loop's head.
    Continue,
}

/// A move that left a place dead.
#[derive(Clone, Copy)]
struct Kill {
    place: PlaceId,
    at: u32,
    cause: Cause,
}

/// The liveness state of one path: the places that are dead on it.
type State = Vec<Kill>;

/// One region the walk is inside of.
struct Frame {
    region: usize,
    /// The state when the region was entered.
    saved: State,
    /// A join's alternatives that have run: the state each one ended
    /// with, and where its end went.
    alts: Vec<(usize, State, Target)>,
    /// A loop's states forwarded from a `continue` (to the head) or a
    /// `break` (to the exit) inside an alternative.
    heads: Vec<State>,
    exits: Vec<State>,
}

/// Which clause a move diagnostic cites, and why.
struct Fault {
    rule: u16,
    clause: Option<char>,
    why: String,
}

/// Where paths merge, for Rule 8's message.
#[derive(Clone, Copy)]
enum Merge {
    Join(Joined, u32),
    Loop(u32),
}

/// One body's flow state: the regions of its CST, the assignment
/// left-hand sides (whose read event is the store's own, not a use), the
/// dead places on the current path and the regions the walk is inside.
struct Flow<'t> {
    tape: &'t UseTape,
    regions: Vec<Region>,
    assign_lhs: Vec<u32>,
    dead: State,
    stack: Vec<Frame>,
}

impl<'t> Flow<'t> {
    /// Collects the regions and assignment places of one declaration's
    /// subtree. A join's alternatives are pushed right after it, so the
    /// list is NOT sorted by start; [`Flow::holding`] sorts.
    fn new(cx: &BodyCx, tape: &'t UseTape) -> Flow<'t> {
        let (start, end) = cx.facts.range();
        let tree = cx.f.tree;
        let mut regions: Vec<Region> = Vec::new();
        let mut assign_lhs: Vec<u32> = Vec::new();
        let add = |regions: &mut Vec<Region>,
                   kind: RegionKind,
                   node: usize,
                   scope: usize,
                   body: usize| {
            regions.push(Region {
                kind,
                start: node as u32,
                end: tree.subtree_end(node) as u32,
                scope_start: scope as u32,
                scope_end: tree.subtree_end(scope) as u32,
                body: body as u32,
            });
        };
        let last_block = |n: usize| {
            tree.children(n)
                .filter(|&c| tree.kinds[c] == NodeKind::Block)
                .last()
        };
        for n in start as usize..(end as usize).min(tree.kinds.len()) {
            match tree.kinds[n] {
                // The alternatives of an `if` chain are its blocks; the
                // conditions run in sequence and are not alternatives. The
                // children alternate condition, block, ..., so an odd
                // count means a trailing `else` (`expr::if_expr`).
                NodeKind::IfExpr => {
                    let kids: Vec<usize> = tree.children(n).collect();
                    let join = regions.len();
                    add(
                        &mut regions,
                        RegionKind::Join {
                            what: Joined::If,
                            implicit_alt: kids.len().is_multiple_of(2),
                        },
                        n,
                        n,
                        n,
                    );
                    for c in kids {
                        if tree.kinds[c] == NodeKind::Block {
                            add(&mut regions, RegionKind::Alt { join }, c, n, c);
                        }
                    }
                }
                // A `match` is exhaustive (R53), so it has no implicit
                // alternative; an arm's body is its last child.
                NodeKind::MatchExpr => {
                    let join = regions.len();
                    add(
                        &mut regions,
                        RegionKind::Join {
                            what: Joined::Match,
                            implicit_alt: false,
                        },
                        n,
                        n,
                        n,
                    );
                    for c in tree.children(n) {
                        if tree.kinds[c] == NodeKind::Arm {
                            let body = tree.children(c).last().unwrap_or(c);
                            add(&mut regions, RegionKind::Alt { join }, c, n, body);
                        }
                    }
                }
                NodeKind::DeferStmt | NodeKind::ErrdeferStmt => {
                    add(&mut regions, RegionKind::Defer, n, n, n)
                }
                // `for`-shaped loops evaluate their iterable ONCE, so the
                // repeated region is the body block — but the loop's own
                // binding, declared in the header, is still the loop's, so
                // the scope that "declares" is the whole statement.
                NodeKind::ForStmt | NodeKind::ParallelForStmt | NodeKind::SimdForStmt => {
                    let body = last_block(n).unwrap_or(n);
                    add(&mut regions, RegionKind::Loop, body, n, body);
                }
                // A `while`'s condition is re-evaluated every iteration,
                // so the whole statement is the repeated region.
                NodeKind::WhileStmt => {
                    let body = last_block(n).unwrap_or(n);
                    add(&mut regions, RegionKind::Loop, n, n, body);
                }
                NodeKind::Closure => add(&mut regions, RegionKind::Closure, n, n, n),
                NodeKind::AssignStmt => {
                    if let Some(p) = tree.children(n).next() {
                        assign_lhs.push(p as u32);
                    }
                }
                _ => {}
            }
        }
        assign_lhs.sort_unstable();
        Flow {
            tape,
            regions,
            assign_lhs,
            dead: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// The regions holding `n`, outermost first.
    fn holding(&self, n: u32) -> Vec<usize> {
        let mut out: Vec<usize> = (0..self.regions.len())
            .filter(|&r| self.regions[r].holds(n))
            .collect();
        out.sort_by_key(|&r| self.regions[r].start);
        out
    }

    /// The innermost region of `kind` holding `n`.
    fn region_of(&self, kind: RegionKind, n: u32) -> Option<Region> {
        self.holding(n)
            .into_iter()
            .rev()
            .map(|r| self.regions[r])
            .find(|r| r.kind == kind)
    }

    /// The kill that makes a use of `place` at `node` a use after move, if
    /// there is one. One SYNTACTIC use writes several events on the tape
    /// — the operand's read, the `move` wrapper's own event, the
    /// argument's convention event — and they nest in the CST, so an
    /// event inside (or around) the killing move's subtree is that same
    /// use, not a later one.
    fn killer(&self, cx: &BodyCx, place: PlaceId, node: u32) -> Option<&Kill> {
        let tree = cx.f.tree;
        let nested = |a: u32, b: u32| {
            (a as usize) < tree.kinds.len() && b >= a && b < tree.subtree_end(a as usize) as u32
        };
        self.dead
            .iter()
            .rev()
            .find(|k| self.overlaps(k.place, place) && !nested(k.at, node) && !nested(node, k.at))
    }

    /// An assignment, a declaration or an `&out` initialisation revives
    /// the place and every path below it.
    fn reinit(&mut self, place: PlaceId) {
        let (root, path) = self.tape.place(place);
        let path = path.to_vec();
        let tape = self.tape;
        self.dead.retain(|k| {
            let (r, p) = tape.place(k.place);
            !(r == root && p.starts_with(&path))
        });
    }

    /// Two places overlap when one is a prefix of the other: moving `a`
    /// kills `a.b`, and moving `a.b` makes `a` partly dead (ch01 Rule
    /// 4a(a), "or of a path that has it as a prefix").
    fn overlaps(&self, a: PlaceId, b: PlaceId) -> bool {
        let (ra, pa) = self.tape.place(a);
        let (rb, pb) = self.tape.place(b);
        ra == rb && (pa.starts_with(pb) || pb.starts_with(pa))
    }

    /// Whether `a` is a strict prefix of `b` (`a` dead makes a store to
    /// `a.b` a use of a dead path, not the store that revives it).
    fn strict_prefix(&self, a: PlaceId, b: PlaceId) -> bool {
        let (ra, pa) = self.tape.place(a);
        let (rb, pb) = self.tape.place(b);
        ra == rb && pa.len() < pb.len() && pb.starts_with(pa)
    }

    /// The state without the places `region` declares: they do not exist
    /// once the region is left.
    fn scoped(&self, state: &State, region: Region) -> State {
        state
            .iter()
            .copied()
            .filter(|k| !region.declares(self.tape.place(k.place).0))
            .collect()
    }

    /// Hands a state that leaves an alternative by `break`/`continue` to
    /// the loop it targets: the innermost one the walk is inside, unless
    /// a closure or `defer` body intervenes (a `break` there targets no
    /// loop of this body, and typing has already said so).
    fn forward(&mut self, state: State, target: Target) {
        for frame in self.stack.iter_mut().rev() {
            match self.regions[frame.region].kind {
                RegionKind::Loop => {
                    if target == Target::Break {
                        frame.exits.push(state);
                    } else {
                        frame.heads.push(state);
                    }
                    return;
                }
                RegionKind::Closure | RegionKind::Defer => return,
                _ => {}
            }
        }
    }
}

/// Where control goes when it leaves the end of `node`, read from the
/// types typing recorded: a block that is not `never` falls through; one
/// that is has a diverging statement, whose kind names the target. An
/// `if`/`match` that diverges forwarded its own alternatives at its join,
/// so what remains of it exits.
fn target(cx: &BodyCx, node: u32) -> Target {
    let n = node as usize;
    if n >= cx.f.tree.kinds.len() || cx.facts.ty_of(node) != TY_NEVER {
        return Target::Falls;
    }
    diverges_to(cx, n)
}

fn diverges_to(cx: &BodyCx, n: usize) -> Target {
    if cx.kind(n) != NodeKind::Block {
        return Target::Exit;
    }
    for s in cx.f.tree.children(n) {
        match cx.kind(s) {
            NodeKind::BreakStmt => return Target::Break,
            NodeKind::ContinueStmt => return Target::Continue,
            NodeKind::ReturnStmt | NodeKind::RaiseStmt => return Target::Exit,
            NodeKind::ExprStmt => {
                if let Some(e) = cx.f.tree.children(s).next()
                    && cx.facts.ty_of(e as u32) == TY_NEVER
                {
                    return diverges_to(cx, e);
                }
            }
            NodeKind::Block if cx.facts.ty_of(s as u32) == TY_NEVER => {
                return diverges_to(cx, s);
            }
            _ => {}
        }
    }
    Target::Exit
}

/// The convention a `Param` node declares, read from its own tokens (the
/// same reading `lower::conv_of` performs on a signature).
fn param_conv(cx: &BodyCx, node: usize) -> Conv {
    let (a, b) = own_span(cx.f.tree, node);
    for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
        match cx.f.tokens.kinds[i] {
            TokenKind::KwLet | TokenKind::KwVar => return Conv::Let,
            TokenKind::KwInout => return Conv::Inout,
            TokenKind::KwSink => return Conv::Sink,
            TokenKind::Ident if cx.f.tokens.text(i, cx.f.source) == b"set" => return Conv::Set,
            _ => {}
        }
    }
    Conv::Let
}

/// The name a `Param` or `Binding` node introduces (`set out: T` owns two
/// identifiers; the convention keyword is not the name).
fn intro_name(cx: &BodyCx, node: usize) -> String {
    let (a, b) = own_span(cx.f.tree, node);
    for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
        if cx.f.tokens.kinds[i] == TokenKind::Ident {
            let text = cx.f.tokens.text(i, cx.f.source);
            if text == b"set" {
                continue;
            }
            return String::from_utf8_lossy(text).into_owned();
        }
    }
    "this place".to_string()
}

/// Whether the place's root has a settled type (design §7.10: `TY_ERROR`
/// absorbs, and a body that already failed must not be told again).
fn settled(cx: &BodyCx, root: u32) -> bool {
    match cx.local(root) {
        Some((t, _)) => t != TY_ERROR && t != NO_TY,
        None => false,
    }
}

impl Wf<'_> {
    /// Design §7.9: the forward pass. Runs once per body, after typing, so
    /// every event the body produced is on the tape and the declaration's
    /// own diagnostic budget (design §10) is still this declaration's.
    pub fn flow(&mut self, cx: &mut BodyCx, tape: &UseTape, files: &[FileCtx]) {
        if tape.is_empty() || self.sink.poisoned() {
            return;
        }
        let mut f = Flow::new(cx, tape);
        for ev in &tape.events {
            if self.sink.poisoned() {
                return;
            }
            let (root, path) = tape.place(ev.place);
            let path = path.to_vec();
            // Design §7.10: an event whose place has no settled type is
            // skipped — a diagnostic from it would be a guess about a
            // program that already failed for another reason.
            if !settled(cx, root) {
                continue;
            }
            self.sync(cx, files, &mut f, ev.node);
            match ev.kind {
                UseKind::Declare | UseKind::Assign | UseKind::OutBorrow => f.reinit(ev.place),
                UseKind::Read | UseKind::Copy | UseKind::MutBorrow | UseKind::Move => {
                    // The read `assign_stmt` records for its own left-hand
                    // side is the store, not a use: `p = e;` is exactly
                    // what re-initialises a dead `p` (ch01 Rule 4a) — but
                    // `p.a = e;` with `p` dead is a use of a dead path.
                    let lhs_store =
                        ev.kind != UseKind::Move && f.assign_lhs.binary_search(&ev.node).is_ok();
                    let killed = f
                        .killer(cx, ev.place, ev.node)
                        .filter(|k| !lhs_store || f.strict_prefix(k.place, ev.place))
                        .copied();
                    if let Some(k) = killed {
                        let who = self.place_text(cx, root, &path);
                        let fault = Fault {
                            rule: 4,
                            clause: Some('a'),
                            why: format!(
                                "`{who}` is used here after it was moved at {}",
                                self.at(cx, k.at)
                            ),
                        };
                        self.move_fault(cx, files, &f, ev.node, fault, k);
                        continue;
                    }
                    if ev.kind != UseKind::Move {
                        continue;
                    }
                    let kill = Kill {
                        place: ev.place,
                        at: ev.node,
                        cause: ev.cause,
                    };
                    match self.move_clause(cx, &f, kill, root, &path) {
                        Some(fault) => self.move_fault(cx, files, &f, ev.node, fault, kill),
                        None => f.dead.push(kill),
                    }
                }
            }
        }
        // Leave every region still open: the last alternatives merge, the
        // last loop checks its head.
        self.sync(cx, files, &mut f, u32::MAX);
    }

    /// Brings the region stack to the regions holding `node`, leaving the
    /// ones that no longer hold it (innermost first, which is where the
    /// merges happen) and entering the ones that newly do.
    fn sync(&mut self, cx: &mut BodyCx, files: &[FileCtx], f: &mut Flow, node: u32) {
        let want = f.holding(node);
        let common = f
            .stack
            .iter()
            .zip(want.iter())
            .take_while(|(frame, r)| frame.region == **r)
            .count();
        while f.stack.len() > common {
            self.leave(cx, files, f);
        }
        for &r in &want[common..] {
            f.stack.push(Frame {
                region: r,
                saved: f.dead.clone(),
                alts: Vec::new(),
                heads: Vec::new(),
                exits: Vec::new(),
            });
        }
    }

    /// Leaves the innermost open region.
    fn leave(&mut self, cx: &mut BodyCx, files: &[FileCtx], f: &mut Flow) {
        let Some(frame) = f.stack.pop() else {
            return;
        };
        let region = f.regions[frame.region];
        match region.kind {
            // The alternative hands its end state to the join and the
            // walk continues on the state the alternative started from
            // (the next alternative, or the join itself, sees that one).
            RegionKind::Alt { .. } => {
                let state = f.scoped(&f.dead, region);
                let went = target(cx, region.body);
                f.dead = frame.saved;
                if let Some(parent) = f.stack.last_mut() {
                    parent.alts.push((frame.region, state, went));
                }
            }
            RegionKind::Join { what, implicit_alt } => {
                // The state after the conditions or the scrutinee, which
                // an alternative that recorded no event left untouched.
                let base = f.dead.clone();
                let mut falls: Vec<State> = Vec::new();
                for a in 0..f.regions.len() {
                    if !matches!(f.regions[a].kind, RegionKind::Alt { join } if join == frame.region)
                    {
                        continue;
                    }
                    let (state, went) = match frame.alts.iter().find(|(r, _, _)| *r == a) {
                        Some((_, s, t)) => (s.clone(), *t),
                        None => (base.clone(), Target::Falls),
                    };
                    match went {
                        Target::Falls => falls.push(state),
                        Target::Exit => {}
                        Target::Break | Target::Continue => f.forward(state, went),
                    }
                }
                if implicit_alt {
                    falls.push(base.clone());
                }
                f.dead = if falls.is_empty() {
                    base
                } else {
                    self.merge(cx, files, f, falls, &base, Merge::Join(what, region.start))
                };
            }
            RegionKind::Loop => {
                let entry = frame.saved;
                let end = f.scoped(&f.dead, region);
                let mut heads: Vec<State> =
                    frame.heads.iter().map(|s| f.scoped(s, region)).collect();
                let mut exits: Vec<State> =
                    frame.exits.iter().map(|s| f.scoped(s, region)).collect();
                match target(cx, region.body) {
                    Target::Falls | Target::Continue => heads.push(end),
                    Target::Break => exits.push(end),
                    Target::Exit => {}
                }
                self.loop_head(cx, files, f, &entry, &heads, region.scope_start);
                // After the loop: the entry state (it ran zero times, or
                // ended normally — which the head check made agree with
                // entry) and every `break`.
                let mut paths = vec![entry.clone()];
                paths.extend(exits);
                f.dead = self.merge(cx, files, f, paths, &entry, Merge::Loop(region.scope_start));
            }
            RegionKind::Closure | RegionKind::Defer => f.dead = frame.saved,
        }
    }

    /// ch01 Rule 4a(b) / Rule 8 at the loop head: every path that reaches
    /// the next iteration must agree with the state the loop was entered
    /// in. A place dead there and live at entry was moved inside the loop
    /// and not re-initialised on that path; the reverse was dead at entry
    /// and revived on only some paths.
    fn loop_head(
        &mut self,
        cx: &mut BodyCx,
        files: &[FileCtx],
        f: &Flow,
        entry: &State,
        heads: &[State],
        node: u32,
    ) {
        let mut done: Vec<PlaceId> = Vec::new();
        for h in heads {
            for k in h {
                if entry.iter().any(|e| e.place == k.place) || done.contains(&k.place) {
                    continue;
                }
                done.push(k.place);
                let who = self.text_of(cx, f, k.place);
                let fault = Fault {
                    rule: 4,
                    clause: Some('b'),
                    why: format!(
                        "`{who}` is declared outside this loop and moved inside it; every path that \
                         reaches the next iteration must re-initialise it first"
                    ),
                };
                self.move_fault(cx, files, f, k.at, fault, *k);
            }
            for e in entry {
                if h.iter().any(|k| k.place == e.place) || done.contains(&e.place) {
                    continue;
                }
                done.push(e.place);
                let who = self.text_of(cx, f, e.place);
                let fault = Fault {
                    rule: 8,
                    clause: None,
                    why: format!(
                        "`{who}` is dead when this loop is entered and live when it reaches the next \
                         iteration; every path must agree at the loop head"
                    ),
                };
                self.move_fault(cx, files, f, node, fault, *e);
            }
        }
    }

    /// ch01 Rule 8's two-valued merge of the paths that fall into one
    /// point: a place is dead afterwards iff it is dead on every path;
    /// dead on some and live on others is the disagreement, reported once
    /// per place and then resolved to the live side so nothing cascades.
    fn merge(
        &mut self,
        cx: &mut BodyCx,
        files: &[FileCtx],
        f: &Flow,
        paths: Vec<State>,
        before: &State,
        at: Merge,
    ) -> State {
        let mut out = State::new();
        let mut seen: Vec<PlaceId> = Vec::new();
        for p in &paths {
            for k in p {
                if seen.contains(&k.place) {
                    continue;
                }
                seen.push(k.place);
                let n = paths
                    .iter()
                    .filter(|q| q.iter().any(|x| x.place == k.place))
                    .count();
                if n == paths.len() {
                    out.push(*k);
                    continue;
                }
                let who = self.text_of(cx, f, k.place);
                let (node, why) = if before.iter().any(|b| b.place == k.place) {
                    let (what, node) = match at {
                        Merge::Join(j, n) => (j.word(), n),
                        Merge::Loop(n) => ("loop", n),
                    };
                    (
                        node,
                        format!(
                            "`{who}` is dead when this {what} is entered and re-initialised on only \
                             some of the paths through it; every path must agree where they merge"
                        ),
                    )
                } else {
                    let why = match at {
                        Merge::Join(j, _) => format!(
                            "`{who}` is moved here on one path through this {} and still live on \
                             another; every path must agree where they merge: consume or discard it \
                             on the other path too",
                            j.word()
                        ),
                        Merge::Loop(_) => format!(
                            "`{who}` is moved here on a path that leaves this loop by `break` and is \
                             still live when the loop ends another way; every path must agree where \
                             they merge"
                        ),
                    };
                    (k.at, why)
                };
                let fault = Fault {
                    rule: 8,
                    clause: None,
                    why,
                };
                self.move_fault(cx, files, f, node, fault, *k);
            }
        }
        out
    }

    /// Which clause of ch01 Rules 3/4a this move violates, if any.
    fn move_clause(
        &mut self,
        cx: &BodyCx,
        f: &Flow,
        kill: Kill,
        root: u32,
        path: &[Seg],
    ) -> Option<Fault> {
        let who = self.place_text(cx, root, path);
        // (c) a partial move: a field or index projection, rejected in
        // v0.1. ch01 R4a(c) names two forms, `move a.b` and `a.b.m()`,
        // and its remedy ("take the value apart with a pattern, or move
        // the whole") fits both. It does NOT name the `for` iterable,
        // which is ch09 R31's round-4 "the iterable is a value use", and
        // the ch09 corpus accepts `for x in self.it` on a field place
        // (`constraint-entry-on-impl-param-in-method-accepted`, a
        // check-ok test this increment must not break), so an
        // [`Cause::Iterable`] move of a projection is left undecided
        // here rather than settled against the corpus.
        if !path.is_empty() && !matches!(kill.cause, Cause::Iterable(_)) {
            return Some(Fault {
                rule: 4,
                clause: Some('c'),
                why: format!(
                    "`{who}` is a projection out of an aggregate, and a partial move is rejected \
                     in v0.1; take the value apart with a pattern, or move the whole"
                ),
            });
        }
        // (d) and Rule 3: the two parameter conventions that may not be
        // moved from. A `set` parameter is Rule 5's, which is M3.
        if (root as usize) < cx.f.tree.kinds.len()
            && cx.f.tree.kinds[root as usize] == NodeKind::Param
        {
            match param_conv(cx, root as usize) {
                Conv::Let => {
                    return Some(Fault {
                        rule: 3,
                        clause: None,
                        why: format!("`{who}` is a `let` parameter and must not be moved from"),
                    });
                }
                Conv::Inout => {
                    return Some(Fault {
                        rule: 4,
                        clause: Some('d'),
                        why: format!("`{who}` is an `inout` parameter and must not be moved from"),
                    });
                }
                Conv::Set => return None,
                Conv::Sink => {}
            }
        }
        // (e) a closure may run more than once, so its body must not move
        // a place it captured.
        if let Some(r) = f.region_of(RegionKind::Closure, kill.at)
            && !r.declares(root)
        {
            return Some(Fault {
                rule: 4,
                clause: Some('e'),
                why: format!("this closure captures `{who}` and must not move it"),
            });
        }
        // (b) is decided when the loop is left, against every path that
        // reaches its head (`loop_head`).
        None
    }

    /// Emits one ch01 move diagnostic, with ch09 Rule 46's mandatory
    /// sentence appended when the move was an implicit receiver move.
    fn move_fault(
        &mut self,
        cx: &mut BodyCx,
        files: &[FileCtx],
        f: &Flow,
        node: u32,
        fault: Fault,
        kill: Kill,
    ) {
        let cite = match fault.clause {
            Some(c) => format!("ch01 R{}a({c})", fault.rule),
            None => format!("ch01 R{}", fault.rule),
        };
        let moved = self.text_of(cx, f, kill.place);
        let tail = self.render_move_error(cx, files, &moved, kill.cause);
        // Design §10: the emission site's rule. An implicit receiver move
        // is ch09 R46's site; any other move of a place is the tape's,
        // which §8 lists in row 57.
        let site = if matches!(kill.cause, Cause::ImplicitReceiver { .. }) {
            46
        } else {
            57
        };
        self.bemit_code(
            cx,
            node as usize,
            Code::O(fault.rule),
            site,
            format!("{} ({cite}){tail}", fault.why),
        );
    }

    /// ch09 Rule 46's normative diagnostic requirement: a move error whose
    /// move was an IMPLICIT receiver move must name the consuming call and
    /// the `sink self` declaration it resolved to. The three fields are
    /// non-optional on [`Cause::ImplicitReceiver`] exactly so that this
    /// sentence can always be built (design §7.9). `moved` is the place
    /// the call consumed, as its source spelling.
    pub fn render_move_error(
        &self,
        cx: &BodyCx,
        files: &[FileCtx],
        moved: &str,
        cause: Cause,
    ) -> String {
        let Cause::ImplicitReceiver {
            call,
            method,
            owner,
        } = cause
        else {
            return String::new();
        };
        let text = self.call_text(cx, call);
        let m = self.method_label(owner, method);
        format!(
            ": `{moved}` was moved by the call `{text}` at {}, because `{m}` takes `sink self` \
             (declared at {})",
            self.at(cx, call),
            self.decl_at(files, method)
        )
    }

    /// `Owner.method`, the name ch09 Rule 46's example writes
    /// ("`Builder.finish` takes `sink self`"). The owner is the inherent
    /// `impl` or the trait: a trait has its own name, an `impl` block has
    /// none, so its head is its self type.
    fn method_label(&self, owner: DefId, method: DefId) -> String {
        let m = self.name_of_def(method);
        let declared = self.defs.get(owner).and_then(|r| r.name);
        let o = match declared {
            Some(_) => self.head_name(owner),
            None => {
                let t = self.fir.sigs.self_ty(owner);
                if t == NO_TY || t == TY_ERROR {
                    return m;
                }
                self.show(t)
            }
        };
        format!("{o}.{m}")
    }

    fn name_of_def(&self, def: DefId) -> String {
        self.defs
            .get(def)
            .and_then(|r| r.name)
            .map(|s| self.sym(s))
            .unwrap_or_else(|| "this method".to_string())
    }

    /// `L:C` of a node of the body being checked.
    fn at(&self, cx: &BodyCx, node: u32) -> String {
        let (l, c) = fors_diag::line_col(cx.f.source, cx.range(node as usize).0);
        format!("{l}:{c}")
    }

    /// `L:C` of a declaration's own header, in ITS file.
    fn decl_at(&self, files: &[FileCtx], def: DefId) -> String {
        let Some(row) = self.defs.get(def) else {
            return "an unknown position".to_string();
        };
        let Some(f) = files.get(row.file.index()) else {
            return "an unknown position".to_string();
        };
        let (l, c) = fors_diag::line_col(f.source, f.header_range(row.node as usize).0);
        format!("{l}:{c}")
    }

    /// The source text of a node, whitespace-collapsed, for a message that
    /// quotes the program back (ch09 Rule 46 quotes the call).
    fn call_text(&self, cx: &BodyCx, node: u32) -> String {
        let (a, b) = cx.range(node as usize);
        let end = (b as usize).min(cx.f.source.len());
        let start = (a as usize).min(end);
        let raw = String::from_utf8_lossy(&cx.f.source[start..end]);
        raw.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    /// A tape place as its source spelling.
    fn text_of(&self, cx: &BodyCx, f: &Flow, place: PlaceId) -> String {
        let (root, path) = f.tape.place(place);
        self.place_text(cx, root, path)
    }

    /// `x`, `s.b`, `xs[_]` — a place as its source spelling.
    fn place_text(&self, cx: &BodyCx, root: u32, path: &[Seg]) -> String {
        let mut out = if (root as usize) < cx.f.tree.kinds.len() {
            intro_name(cx, root as usize)
        } else {
            "this place".to_string()
        };
        for s in path {
            match *s {
                Seg::Field(sym) => {
                    out.push('.');
                    out.push_str(&self.sym(sym));
                }
                Seg::Index => out.push_str("[_]"),
            }
        }
        out
    }
}
