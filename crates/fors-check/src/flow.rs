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
use fors_fir::ty::{NO_TY, TY_ERROR, TY_NEVER, TY_UNIT, TyId, TyTag};
use fors_index::diag::Code;
use fors_index::ids::DefId;
use fors_lex::TokenKind;
use fors_resolve::paths::own_span;
use fors_syntax::NodeKind;

use crate::body::{BodyCx, own_first};
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
    /// A LEXICAL SCOPE (I8b, ch01 Rule 22h): a `block` — a function body, a
    /// `with`, a `parallel`, a loop body, an arm block, a closure body — or
    /// an arm whose body is not a block. Leaving it is the scope exit the
    /// linear obligations are checked at. It changes no liveness: the state
    /// passes straight through, minus the places the scope declared.
    Scope,
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
    /// Two regions may start at the SAME node — a `Scope` always shares its
    /// node with the `Alt` or `Loop` whose body it is. The scope is the
    /// inner one: its `}` is reached before the alternative hands its state
    /// to the join, and before the loop checks its head.
    fn tier(&self) -> u8 {
        match self.kind {
            RegionKind::Scope => 1,
            _ => 0,
        }
    }

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

/// ch01 Rule 22d: one cleanup obligation — a live binding of linear type.
#[derive(Clone, Copy)]
struct Oblig {
    /// The `Binding`, `PatLet`, `FPat` or `Param` node that introduced it.
    root: u32,
    /// The scope that owes it: a `Block`, or an `Arm` whose body is not a
    /// block. Rule 22h checks it at every exit of this scope.
    scope: u32,
    ty: TyId,
    /// The `let`/`var` statement that introduces it, as `(start, end)`.
    /// An exit INSIDE it — `var b: Own[..] = a.create(1)?;` — happens
    /// before the binding exists and owes nothing.
    decl: (u32, u32),
}

/// ch01 Rule 23: one `defer`/`errdefer` statement, with the two summaries
/// Rule 23d asks for — the places the body MOVES (deferred consumption,
/// 23d(b)) and every place it mentions at all (23d(a)) — as place ROOTS,
/// which is what the tape already interned.
struct DeferRow {
    node: u32,
    /// The `block` that DIRECTLY contains the statement (Rule 23).
    scope: u32,
    errdefer: bool,
    /// Position among the statements of `scope`: the bodies of one scope
    /// run in ONE reverse `stmt_order` sequence (Rule 23a, 23b).
    order: u32,
    moves: Vec<u32>,
    mentions: Vec<u32>,
}

/// ch01 Rule 22h's "every point where control leaves a scope".
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ExitKind {
    /// The `}` of the block, reached by fall-through or a tail value.
    BlockEnd,
    Return,
    Raise,
    /// The error edge of a `?` (ch02 Rule 16).
    Question,
    Break,
    Continue,
}

impl ExitKind {
    /// Rule 23b: an `errdefer` body runs on the ERROR exits only.
    fn is_error(self) -> bool {
        matches!(self, ExitKind::Raise | ExitKind::Question)
    }

    fn word(self) -> &'static str {
        match self {
            ExitKind::BlockEnd => "the `}` of the block opened at",
            ExitKind::Return => "the `return` at",
            ExitKind::Raise => "the `raise` at",
            ExitKind::Question => "the `?` at",
            ExitKind::Break => "the `break` at",
            ExitKind::Continue => "the `continue` at",
        }
    }
}

#[derive(Clone, Copy)]
struct ExitRow {
    kind: ExitKind,
    /// The `return`/`raise`/`?`/`break`/`continue` node, or the block.
    node: u32,
    /// Where the exit sits in the event stream: after everything inside the
    /// statement, because Rule 23a evaluates and moves the operand FIRST.
    key: u32,
}

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
    // ------------------------------------------------- I8b (ch01 R22-R23f)
    /// Every lexical scope, `(node, subtree end)`, sorted by node.
    scopes: Vec<(u32, u32)>,
    /// The declaration's own body block: where a `sink` parameter's
    /// obligation lives and where a `return`'s scope chain stops.
    body_block: u32,
    /// Scopes that are a closure's body (a `return` stops there too) and
    /// scopes that are a loop's body (where `break`/`continue` stop).
    closure_bodies: Vec<u32>,
    loop_bodies: Vec<u32>,
    obligs: Vec<Oblig>,
    defers: Vec<DeferRow>,
    exits: Vec<ExitRow>,
    /// R22d(ii): a `match` on a linear place destructures it, which
    /// discharges the scrutinee's obligation. `(match node, scrutinee
    /// root)`.
    match_dis: Vec<(u32, u32)>,
    /// Matches whose scrutinee is borrowed, not owned.
    borrowed_matches: Vec<u32>,
    /// D9: `(closure node, captured place roots)` — ch01 R19d's sources.
    sources: Vec<(u32, Vec<u32>)>,
    /// R22d(i)'s tail value: `(scope, root)` — the place a scope's tail
    /// expression moves into the enclosing result.
    tail_dis: Vec<(u32, u32)>,
    /// Obligations already reported, so one leaked value is one
    /// diagnostic even when several exits leave the same scope.
    said: Vec<u32>,
    /// `}` exits already taken, so the sweep at the end of the walk does
    /// not repeat one the region walk already reached.
    done_blocks: Vec<u32>,
    /// Obligations whose binding has been INITIALISED on the path so far.
    /// A `var b: Own[..] = a.create(1)?;` owes nothing at its own `?`:
    /// the binding does not exist until its `Declare` event.
    born: Vec<u32>,
    /// D8: `(exit, obligation root, what consumed it)`, decided AT the exit
    /// from the state of the path that reaches it — so a move on another
    /// branch is never credited to this edge.
    discharges: Vec<(ExitRow, u32, crate::facts::Discharge)>,
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
        let mut flow = Flow {
            tape,
            regions,
            assign_lhs,
            dead: Vec::new(),
            stack: Vec::new(),
            scopes: Vec::new(),
            body_block: u32::MAX,
            closure_bodies: Vec::new(),
            loop_bodies: Vec::new(),
            obligs: Vec::new(),
            defers: Vec::new(),
            exits: Vec::new(),
            match_dis: Vec::new(),
            borrowed_matches: Vec::new(),
            sources: Vec::new(),
            tail_dis: Vec::new(),
            said: Vec::new(),
            done_blocks: Vec::new(),
            born: Vec::new(),
            discharges: Vec::new(),
        };
        flow.collect_scopes(cx);
        flow
    }

    /// I8b: the lexical scopes, the exits, the `defer` rows and the
    /// `match` destructurings of one declaration's subtree, in ONE walk of
    /// the CST. Nothing here is dataflow: it is the static shape ch01
    /// Rules 22h and 23a read (design §13's "the set of bodies at each
    /// exit is static").
    fn collect_scopes(&mut self, cx: &BodyCx) {
        let (start, end) = cx.facts.range();
        let tree = cx.f.tree;
        let last = (end as usize).min(tree.kinds.len());
        let mut scope_regions: Vec<Region> = Vec::new();
        for n in start as usize..last {
            let k = tree.kinds[n];
            let is_scope = k == NodeKind::Block
                || (k == NodeKind::Arm
                    && tree
                        .children(n)
                        .last()
                        .is_some_and(|c| tree.kinds[c] != NodeKind::Block));
            if !is_scope {
                continue;
            }
            let e = tree.subtree_end(n) as u32;
            self.scopes.push((n as u32, e));
            scope_regions.push(Region {
                kind: RegionKind::Scope,
                start: n as u32,
                end: e,
                scope_start: n as u32,
                scope_end: e,
                body: n as u32,
            });
        }
        self.scopes.sort_unstable();
        self.regions.extend(scope_regions);
        // The declaration's own body block is its first `Block` child.
        self.body_block = tree
            .children(start as usize)
            .find(|&c| tree.kinds[c] == NodeKind::Block)
            .map(|c| c as u32)
            .unwrap_or(u32::MAX);
        for n in start as usize..last {
            match tree.kinds[n] {
                NodeKind::Closure => {
                    if let Some(b) = tree.children(n).find(|&c| tree.kinds[c] == NodeKind::Block) {
                        self.closure_bodies.push(b as u32);
                    }
                }
                NodeKind::ForStmt
                | NodeKind::ParallelForStmt
                | NodeKind::SimdForStmt
                | NodeKind::WhileStmt => {
                    if let Some(b) = tree
                        .children(n)
                        .filter(|&c| tree.kinds[c] == NodeKind::Block)
                        .last()
                    {
                        self.loop_bodies.push(b as u32);
                    }
                }
                _ => {}
            }
        }
        self.closure_bodies.sort_unstable();
        self.loop_bodies.sort_unstable();
        // Exits.
        for &(b, e) in &self.scopes.clone() {
            // Rule 22h's `}`: only when control can reach it. A block that
            // ends in a `return` has no fall-through exit, and reporting
            // there would double every diverging path.
            if target(cx, b) == Target::Falls {
                self.exits.push(ExitRow {
                    kind: ExitKind::BlockEnd,
                    node: b,
                    key: e.saturating_sub(1),
                });
            }
        }
        for n in start as usize..last {
            let kind = match tree.kinds[n] {
                NodeKind::ReturnStmt => ExitKind::Return,
                NodeKind::RaiseStmt => ExitKind::Raise,
                NodeKind::TryExpr => ExitKind::Question,
                NodeKind::BreakStmt => ExitKind::Break,
                NodeKind::ContinueStmt => ExitKind::Continue,
                _ => continue,
            };
            self.exits.push(ExitRow {
                kind,
                node: n as u32,
                key: (tree.subtree_end(n) as u32).saturating_sub(1),
            });
        }
        self.exits.sort_by_key(|x| (x.key, x.node));
        // `defer`/`errdefer` rows.
        for n in start as usize..last {
            let errdefer = match tree.kinds[n] {
                NodeKind::DeferStmt => false,
                NodeKind::ErrdeferStmt => true,
                _ => continue,
            };
            let scope = self.innermost_scope(n as u32).unwrap_or(self.body_block);
            // D7's `stmt_order`: the statement's POSITION among the
            // statements of its block, which `fors-lower` stores as a
            // `u16` by construction. (A `defer` is always a direct child of
            // the block that contains it, Rule 23; the node index is the
            // fallback for a shape the parser never produces.)
            let order = tree
                .children(scope as usize)
                .position(|c| c == n)
                .map(|p| p as u32)
                .unwrap_or(n as u32);
            let e = tree.subtree_end(n) as u32;
            let mut moves = Vec::new();
            let mut mentions = Vec::new();
            for ev in &self.tape.events {
                if ev.node < n as u32 || ev.node >= e {
                    continue;
                }
                let (root, path) = self.tape.place(ev.place);
                if !path.is_empty() {
                    continue;
                }
                // A place the body DECLARES is the body's own, not the
                // enclosing scope's.
                if root >= n as u32 && root < e {
                    continue;
                }
                if !mentions.contains(&root) {
                    mentions.push(root);
                }
                if ev.kind == UseKind::Move && !moves.contains(&root) {
                    moves.push(root);
                }
            }
            self.defers.push(DeferRow {
                node: n as u32,
                scope,
                errdefer,
                order,
                moves,
                mentions,
            });
        }
        // R22d(i)'s "the function body's tail value", generalised to every
        // scope: a block's or an arm's tail expression MOVES the place it
        // names into the enclosing expression's result.
        for &(b, _) in &self.scopes.clone() {
            let Some(tail) = tree.children(b as usize).last() else {
                continue;
            };
            if let Some(root) = local_root(cx, tail as u32) {
                self.tail_dis.push((b, root));
            }
        }
        // R22d(ii): a `match` destructures its scrutinee — but only when
        // the scrutinee is a place the body OWNS. Matching through a
        // `let`/`inout` parameter is a borrow (Rules 3 and 4a(d) forbid
        // moving out of one), so its arm bindings are views that owe
        // nothing and the scrutinee itself is not consumed.
        for n in start as usize..last {
            if tree.kinds[n] != NodeKind::MatchExpr {
                continue;
            }
            let Some(scrut) = tree.children(n).next() else {
                continue;
            };
            if !owning_place(cx, scrut as u32) {
                self.borrowed_matches.push(n as u32);
                continue;
            }
            if let Some(ev) = self
                .tape
                .events
                .iter()
                .find(|e| e.node == scrut as u32)
                .copied()
            {
                let (root, path) = self.tape.place(ev.place);
                if path.is_empty() {
                    self.match_dis.push((n as u32, root));
                }
            }
        }
    }

    /// Whether `n` sits inside a `match` whose scrutinee the body does not
    /// own: its pattern bindings are views (see `collect_scopes`).
    fn in_borrowed_match(&self, cx: &BodyCx, n: u32) -> bool {
        self.borrowed_matches.iter().any(|&m| {
            (m as usize) < cx.f.tree.kinds.len()
                && n >= m
                && n < cx.f.tree.subtree_end(m as usize) as u32
        })
    }

    /// The innermost scope holding `n`, or `None` when `n` is outside every
    /// block of this declaration (a parameter, a `for` header binding).
    fn innermost_scope(&self, n: u32) -> Option<u32> {
        self.scopes
            .iter()
            .filter(|&&(a, b)| n >= a && n < b)
            .max_by_key(|&&(a, _)| a)
            .map(|&(a, _)| a)
    }

    /// The scopes `n` sits in, innermost first.
    fn scope_chain(&self, n: u32) -> Vec<u32> {
        let mut out: Vec<u32> = self
            .scopes
            .iter()
            .filter(|&&(a, b)| n >= a && n < b)
            .map(|&(a, _)| a)
            .collect();
        out.sort_unstable();
        out.reverse();
        out
    }

    /// The scopes an exit leaves, innermost first (ch01 Rule 22h).
    fn scopes_left(&self, x: ExitRow) -> Vec<u32> {
        match x.kind {
            ExitKind::BlockEnd => vec![x.node],
            ExitKind::Break | ExitKind::Continue => {
                let mut out = Vec::new();
                for s in self.scope_chain(x.node) {
                    out.push(s);
                    if self.loop_bodies.binary_search(&s).is_ok() {
                        break;
                    }
                }
                out
            }
            _ => {
                let mut out = Vec::new();
                for s in self.scope_chain(x.node) {
                    out.push(s);
                    if s == self.body_block || self.closure_bodies.binary_search(&s).is_ok() {
                        break;
                    }
                }
                out
            }
        }
    }

    /// The deferred bodies that run on `x`, in the order Rule 23a fixes:
    /// innermost scope first, and within one scope ONE reverse
    /// `stmt_order` sequence interleaving `defer` and `errdefer`.
    fn running_defers(&self, x: ExitRow) -> Vec<usize> {
        let mut out = Vec::new();
        for s in self.scopes_left(x) {
            let mut rows: Vec<usize> = (0..self.defers.len())
                .filter(|&i| {
                    let d = &self.defers[i];
                    d.scope == s
                        && (!d.errdefer || x.kind.is_error())
                        && (x.kind == ExitKind::BlockEnd || d.node < x.node)
                })
                .collect();
            rows.sort_by_key(|&i| std::cmp::Reverse(self.defers[i].order));
            out.extend(rows);
        }
        out
    }

    /// The interned `PlaceId` of `root`'s WHOLE place, when the body ever
    /// used it (D8's `place`).
    fn whole_place(&self, root: u32) -> Option<PlaceId> {
        (0..self.tape.places() as u32).map(PlaceId).find(|&p| {
            let (r, path) = self.tape.place(p);
            r == root && path.is_empty()
        })
    }

    /// Whether `root`'s whole place is dead in `state`.
    fn root_dead(&self, state: &State, root: u32) -> bool {
        state.iter().any(|k| {
            let (r, p) = self.tape.place(k.place);
            r == root && p.is_empty()
        })
    }

    /// The regions holding `n`, outermost first.
    fn holding(&self, n: u32) -> Vec<usize> {
        let mut out: Vec<usize> = (0..self.regions.len())
            .filter(|&r| self.regions[r].holds(n))
            .collect();
        out.sort_by_key(|&r| (self.regions[r].start, self.regions[r].tier()));
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

/// Whether the body OWNS the place `n` denotes: a local, a `sink`
/// parameter, a pattern binding of an owning match — or a temporary,
/// which is owned by definition. A `let`/`inout`/`set` parameter, and any
/// projection of one, is borrowed.
fn owning_place(cx: &BodyCx, n: u32) -> bool {
    let tree = cx.f.tree;
    let mut m = n as usize;
    loop {
        if m >= tree.kinds.len() {
            return true;
        }
        match tree.kinds[m] {
            NodeKind::FieldExpr | NodeKind::Bracket | NodeKind::TupleOrParen => {
                match tree.children(m).next() {
                    Some(c) => m = c,
                    None => return true,
                }
            }
            NodeKind::UnaryExpr if own_first(cx, m) == Some(TokenKind::KwMove) => {
                match tree.children(m).next() {
                    Some(c) => m = c,
                    None => return true,
                }
            }
            NodeKind::NameExpr => {
                let Some(fors_resolve::target::ResolvedTarget::Local { node }) =
                    cx.f.uses.target_of(m as u32)
                else {
                    return true;
                };
                let r = node as usize;
                if r < tree.kinds.len() && tree.kinds[r] == NodeKind::Param {
                    return param_conv(cx, r) == Conv::Sink;
                }
                return true;
            }
            _ => return true,
        }
    }
}

/// Whether a `Binding` node is a loop header's binding.
fn for_binding(cx: &BodyCx, n: u32) -> bool {
    let tree = cx.f.tree;
    let (start, _) = cx.facts.range();
    for p in start as usize..(n as usize).min(tree.kinds.len()) {
        if !matches!(
            tree.kinds[p],
            NodeKind::ForStmt | NodeKind::ParallelForStmt | NodeKind::SimdForStmt
        ) {
            continue;
        }
        if tree.children(p).next() == Some(n as usize) {
            return true;
        }
    }
    false
}

/// The local a bare place expression names, unwrapping `move e` and
/// `(e)` exactly as `body::place_of` does — without interning, so the
/// flow pass can ask about a node typing wrote no tape event for.
fn local_root(cx: &BodyCx, node: u32) -> Option<u32> {
    let tree = cx.f.tree;
    let mut n = node as usize;
    loop {
        if n >= tree.kinds.len() {
            return None;
        }
        match tree.kinds[n] {
            NodeKind::TupleOrParen => {
                let mut kids = tree.children(n);
                let first = kids.next()?;
                if kids.next().is_some() {
                    return None;
                }
                n = first;
            }
            NodeKind::UnaryExpr if own_first(cx, n) == Some(TokenKind::KwMove) => {
                n = tree.children(n).next()?;
            }
            NodeKind::NameExpr => {
                return match cx.f.uses.target_of(n as u32)? {
                    fors_resolve::target::ResolvedTarget::Local { node } => Some(node),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// The `let`/`var` statement a `Binding` is introduced by, as `(start,
/// end)`; `(n, n)` when there is none, which excludes nothing.
///
/// Only the statement that DIRECTLY introduces the binding counts: a
/// binding written inside a closure, a block or an arm that sits in some
/// outer `let`'s initialiser (`let v = match o { some(let r) => .. }`,
/// `let c = || { var r = ..; }`) is not "not yet bound" at the exits of
/// that closure or arm — those exits are its own.
fn decl_stmt(cx: &BodyCx, n: u32) -> (u32, u32) {
    let tree = cx.f.tree;
    let (start, _) = cx.facts.range();
    let mut best = (n, n);
    for p in start as usize..(n as usize + 1).min(tree.kinds.len()) {
        if tree.kinds[p] != NodeKind::LetStmt {
            continue;
        }
        let e = tree.subtree_end(p) as u32;
        if (p as u32) <= n && e > n {
            best = (p as u32, e);
        }
    }
    if best == (n, n) {
        return best;
    }
    // A scope boundary between the innermost `let` and the binding means
    // the `let` is some enclosing statement, not this binding's.
    for q in (best.0 as usize + 1)..(n as usize) {
        if matches!(
            tree.kinds[q],
            NodeKind::Block | NodeKind::Closure | NodeKind::Arm | NodeKind::DeferStmt
        ) && tree.subtree_end(q) as u32 > n
        {
            return (n, n);
        }
    }
    best
}

/// Where in the TAPE an exit is taken: just after the last event inside
/// its own statement (ch01 Rule 23a evaluates and moves the operand
/// first), or, when the statement produced no event, just before the
/// first event of whatever follows it.
fn fire_at(cx: &BodyCx, tape: &UseTape, x: ExitRow) -> usize {
    let end = if (x.node as usize) < cx.f.tree.kinds.len() {
        cx.f.tree.subtree_end(x.node as usize) as u32
    } else {
        x.node + 1
    };
    let inside = |n: u32| n >= x.node && n < end;
    if let Some(i) = tape.events.iter().rposition(|e| inside(e.node)) {
        return i + 1;
    }
    tape.events
        .iter()
        .position(|e| e.node >= end)
        .unwrap_or(tape.events.len())
}

/// Whether a `Param` node is the receiver `self`. A `sink self` receiver
/// is ch01 Rule 22i's CONSUMER of its own head: it carries no obligation
/// of its own, which is the reading that makes Rule 22h agree with the
/// corpus (`fn close(sink self) { }` is accepted everywhere, while
/// `fn f(sink r: Res) { }` is `linear-sink-parameter-unconsumed-rejected`).
fn is_self_param(cx: &BodyCx, node: usize) -> bool {
    let (a, b) = own_span(cx.f.tree, node);
    for i in a as usize..(b as usize).min(cx.f.tokens.kinds.len()) {
        if cx.f.tokens.text(i, cx.f.source) == b"self" {
            return true;
        }
    }
    false
}

/// Whether a `Binding` node names anything (`let _ = e;` and a `_`
/// component of a tuple binding do not: ch01 Rule 22h's temporaries).
fn names_something(cx: &BodyCx, node: usize) -> bool {
    let (a, b) = own_span(cx.f.tree, node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .any(|i| cx.f.tokens.kinds[i] == TokenKind::Ident)
}

/// The scope that owes a binding introduced at `n`.
///
/// A `let`/`var` binding belongs to the block it is written in. A PATTERN
/// binding is written in the arm's pattern, which is OUTSIDE the arm's
/// body block, so it belongs to that body block (or, for an arm whose
/// body is an expression, to the arm). A `for` loop's binding is written
/// in the header and belongs to the loop body, which is the scope it is
/// re-bound in on every iteration (Rule 23e).
fn pattern_scope(cx: &BodyCx, f: &Flow, n: u32) -> u32 {
    let tree = cx.f.tree;
    let (start, _) = cx.facts.range();
    // The innermost `Arm` or loop header holding `n`.
    let mut best: Option<(u32, u32)> = None; // (arm/loop node, its scope)
    for p in start as usize
        ..(tree.kinds.len()).min(
            f.scopes
                .last()
                .map(|x| x.1 as usize)
                .unwrap_or(0)
                .max(n as usize + 1),
        )
    {
        let e = tree.subtree_end(p) as u32;
        if (p as u32) > n || e <= n {
            continue;
        }
        let scope = match tree.kinds[p] {
            NodeKind::Arm => tree
                .children(p)
                .last()
                .map(|c| {
                    if tree.kinds[c] == NodeKind::Block {
                        c as u32
                    } else {
                        p as u32
                    }
                })
                .unwrap_or(p as u32),
            NodeKind::ForStmt | NodeKind::ParallelForStmt | NodeKind::SimdForStmt => tree
                .children(p)
                .filter(|&c| tree.kinds[c] == NodeKind::Block)
                .last()
                .map(|c| c as u32)
                .unwrap_or(p as u32),
            _ => continue,
        };
        // The binding must be OUTSIDE the scope it is attributed to —
        // otherwise the ordinary innermost-block answer is already right.
        if n >= scope && n < tree.subtree_end(scope as usize) as u32 {
            continue;
        }
        match best {
            Some((b, _)) if b >= p as u32 => {}
            _ => best = Some((p as u32, scope)),
        }
    }
    if let Some((_, scope)) = best {
        return scope;
    }
    f.innermost_scope(n).unwrap_or(f.body_block)
}

/// Whether `scope` shows any error exit at all (ch02 Rule 16's syntactic
/// set): a `?` or a `raise` outside every nested deferred body or closure.
fn has_error_exit(cx: &BodyCx, f: &Flow, scope: u32) -> bool {
    error_exit_follows(cx, f, scope, scope.saturating_sub(1))
}

/// ch01 Rule 23b: does an ERROR exit of `scope` follow the statement at
/// `after`? The set of error exits is syntactic (ch02 Rule 16): a `?` or a
/// `raise` written inside the scope, outside any nested deferred body or
/// closure, which runs on a path that leaves the scope.
fn error_exit_follows(cx: &BodyCx, f: &Flow, scope: u32, after: u32) -> bool {
    let tree = cx.f.tree;
    let end = if (scope as usize) < tree.kinds.len() {
        tree.subtree_end(scope as usize) as u32
    } else {
        return false;
    };
    for n in (after as usize + 1)..(end as usize).min(tree.kinds.len()) {
        if !matches!(tree.kinds[n], NodeKind::TryExpr | NodeKind::RaiseStmt) {
            continue;
        }
        if f.region_of(RegionKind::Defer, n as u32).is_some()
            || f.region_of(RegionKind::Closure, n as u32).is_some()
        {
            continue;
        }
        return true;
    }
    false
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
        if self.sink.poisoned() {
            return;
        }
        let mut f = Flow::new(cx, tape);
        self.collect_obligations(cx, &mut f);
        self.static_linear_checks(cx, &mut f);
        // I8b: each non-`}` exit is taken at the tape position where its
        // statement has finished evaluating. Rule 23a fixes that order:
        // the returned or raised operand is moved into the result FIRST,
        // then the pending bodies run, then Rule 22h checks what is left.
        // The tape is in TYPING order, not node order (a `let`'s `Declare`
        // follows its initialiser), so the position is computed from the
        // events, never from the node numbering.
        let mut fire: Vec<(usize, ExitRow)> = f
            .exits
            .iter()
            .filter(|x| x.kind != ExitKind::BlockEnd)
            .map(|&x| (fire_at(cx, tape, x), x))
            .collect();
        fire.sort_by_key(|&(i, x)| (i, x.node));
        let mut next_exit = 0usize;
        for (i, ev) in tape.events.iter().enumerate() {
            if self.sink.poisoned() {
                return;
            }
            while next_exit < fire.len() && fire[next_exit].0 <= i {
                let x = fire[next_exit].1;
                next_exit += 1;
                self.sync(cx, files, &mut f, x.node);
                self.scope_exit(cx, files, &mut f, x);
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
                UseKind::Declare | UseKind::Assign | UseKind::OutBorrow => {
                    if ev.kind == UseKind::Declare && !f.born.contains(&root) {
                        f.born.push(root);
                    }
                    // ch01 R22h: "a `var` of linear type ASSIGNED while
                    // live" overwrites an unconsumed value.
                    if ev.kind == UseKind::Assign
                        && path.is_empty()
                        && !f.root_dead(&f.dead, root)
                        && f.born.contains(&root)
                        && let Some(o) = f.obligs.iter().find(|o| o.root == root).copied()
                        && !f.said.contains(&root)
                    {
                        f.said.push(root);
                        let who = format!("`{}`", self.place_text(cx, root, &[]));
                        let at = format!("the assignment at {}", self.at(cx, ev.node));
                        self.linear_leak_at(cx, ev.node, &who, o.ty, &at);
                        continue;
                    }
                    f.reinit(ev.place)
                }
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
        while next_exit < fire.len() {
            let x = fire[next_exit].1;
            next_exit += 1;
            self.sync(cx, files, &mut f, x.node);
            self.scope_exit(cx, files, &mut f, x);
        }
        // Leave every region still open: the last alternatives merge, the
        // last loop checks its head, and every scope's `}` is Rule 22h's
        // last exit.
        self.sync(cx, files, &mut f, u32::MAX);
        // A scope the walk never entered — a body that wrote no event at
        // all, such as `fn f(sink r: Res) { }` — still has a `}`.
        let mut rest: Vec<ExitRow> = f
            .exits
            .iter()
            .copied()
            .filter(|x| x.kind == ExitKind::BlockEnd && !f.done_blocks.contains(&x.node))
            .collect();
        rest.sort_by_key(|x| std::cmp::Reverse(x.node));
        for x in rest {
            self.scope_exit(cx, files, &mut f, x);
        }
        self.closure_sources(cx, &mut f);
        self.publish_facts(cx, &f);
    }

    /// ch01 R19d: a closure that captures at least one place is a SCOPED
    /// value whose sources are its captured places together with the
    /// sources of every captured place that is itself scoped. The captures
    /// are read off the tape — a closure body's events are the accesses
    /// typing already recorded — and never from a second walk.
    ///
    /// Its first consequence is the one this increment can decide without
    /// `std`: "a closure over a local can be RETURNED by no function"
    /// (Rule 19 names parameters only, and Rule 19a forbids storing it).
    fn closure_sources(&mut self, cx: &mut BodyCx, f: &mut Flow) {
        let tree = cx.f.tree;
        let (start, end) = cx.facts.range();
        let last = (end as usize).min(tree.kinds.len());
        for n in start as usize..last {
            if tree.kinds[n] != NodeKind::Closure {
                continue;
            }
            let e = tree.subtree_end(n) as u32;
            let mut sources: Vec<u32> = Vec::new();
            for ev in &f.tape.events {
                if ev.node < n as u32 || ev.node >= e {
                    continue;
                }
                let (root, _) = f.tape.place(ev.place);
                // A place the closure DECLARES is not a capture.
                if root >= n as u32 && root < e {
                    continue;
                }
                if !sources.contains(&root) {
                    sources.push(root);
                }
            }
            if sources.is_empty() {
                continue;
            }
            sources.sort_unstable();
            f.sources.push((n as u32, sources));
        }
        // The decidable half of R19/R19d: returning a closure whose
        // sources include a LOCAL of this body.
        if self.sink.poisoned() {
            return;
        }
        let rows = f.sources.clone();
        for (node, srcs) in rows {
            let returned = f.exits.iter().any(|x| {
                matches!(x.kind, ExitKind::Return | ExitKind::Raise)
                    && (x.node as usize) < tree.kinds.len()
                    && node > x.node
                    && node < tree.subtree_end(x.node as usize) as u32
            });
            if !returned {
                continue;
            }
            let Some(&local) = srcs.iter().find(|&&r| {
                (r as usize) < tree.kinds.len() && tree.kinds[r as usize] != NodeKind::Param
            }) else {
                continue;
            };
            let who = self.place_text(cx, local, &[]);
            self.bemit_code(
                cx,
                node as usize,
                Code::O(19),
                57,
                format!(
                    "this closure captures the local `{who}`, so it is a scoped value and no \
                     function may return it: ch01 R19 names parameters only, and a closure \
                     over a `let` parameter `p` may be returned only under `scoped(p)` \
                     (ch01 R19d)"
                ),
            );
            return;
        }
    }

    /// The three side tables FMIR lowering reads (design §13, "Interface
    /// to FMIR lowering"): D7 `defer_regions`, D8 `linear_obligations`,
    /// D9 `scoped_sources`. Written ONCE, after the pass has decided
    /// everything; the checker never reads them back, so a bug here can
    /// only starve lowering, never mis-check a program.
    fn publish_facts(&mut self, cx: &mut BodyCx, f: &Flow) {
        use crate::facts as fx;
        let mut d7 = fx::DeferRegions::default();
        for d in &f.defers {
            d7.rows.push(fx::DeferRegionRow {
                scope: d.scope,
                kind: if d.errdefer {
                    fx::DeferKind::ErrDefer
                } else {
                    fx::DeferKind::Defer
                },
                body: d.node,
                stmt_order: d.order,
            });
            for &m in &d.mentions {
                d7.accesses.push(fx::DeferAccessRow {
                    body: d.node,
                    root: m,
                    access: if d.moves.contains(&m) {
                        fx::Access::Move
                    } else {
                        fx::Access::Inout
                    },
                });
            }
        }
        let mut d8 = fx::LinearObligations::default();
        for o in &f.obligs {
            let place = f.whole_place(o.root);
            d8.obligations.push(fx::ObligationRow {
                scope: o.scope,
                root: o.root,
                place,
                ty: o.ty,
                decl: o.decl,
            });
            if !d8.lin.iter().any(|&(t, _)| t == o.ty) {
                d8.lin.push((o.ty, true));
            }
        }
        for x in &f.exits {
            let running = f.running_defers(*x);
            let idx = d7.exits.len() as u32;
            d7.exits.push(fx::ExitEdge {
                kind: match x.kind {
                    ExitKind::BlockEnd => fx::ExitEdgeKind::BlockEnd,
                    ExitKind::Return => fx::ExitEdgeKind::Return,
                    ExitKind::Raise => fx::ExitEdgeKind::Raise,
                    ExitKind::Question => fx::ExitEdgeKind::Question,
                    ExitKind::Break => fx::ExitEdgeKind::Break,
                    ExitKind::Continue => fx::ExitEdgeKind::Continue,
                },
                node: x.node,
                scopes: f.scopes_left(*x),
                defers: running.iter().map(|&i| i as u32).collect(),
            });
            // The discharges `scope_exit` decided on this edge, from the
            // state of the path that reached it.
            for &(ex, root, how) in &f.discharges {
                if ex.kind == x.kind && ex.node == x.node {
                    d8.discharges.push(fx::DischargeRow {
                        exit: idx,
                        root,
                        how,
                    });
                }
            }
        }
        let d9 = fx::ScopedSources {
            rows: f.sources.clone(),
        };
        cx.facts.defer_regions = d7;
        cx.facts.linear_obligations = d8;
        cx.facts.scoped_sources = d9;
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
            // I8b: the `}` of a scope. Liveness passes straight through —
            // this region adds no dataflow state (ch01 Rule 8's note) —
            // and what it does is Rule 22h's check on the obligations the
            // scope declared.
            RegionKind::Scope => {
                if let Some(x) = f
                    .exits
                    .iter()
                    .copied()
                    .find(|x| x.kind == ExitKind::BlockEnd && x.node == region.start)
                {
                    f.done_blocks.push(x.node);
                    self.scope_exit(cx, files, f, x);
                }
                f.dead = f.scoped(&f.dead, region);
            }
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

    // ------------------------------------------- I8b: ch01 R22-R23f

    /// ch01 Rule 22d: the cleanup obligations of one body.
    ///
    /// A LIVE BINDING of linear type — a local, a `sink` parameter, a
    /// pattern binding — carries one; the binding of a `with` block never
    /// does (Rule 15a governs it), and neither does a `sink self`
    /// receiver, which IS the consumer Rule 22i points callers at: what it
    /// does with the representation is ch10's, not this rule's.
    fn collect_obligations(&mut self, cx: &mut BodyCx, f: &mut Flow) {
        let (start, end) = cx.facts.range();
        let tree = cx.f.tree;
        let last = (end as usize).min(tree.kinds.len());
        for n in start as usize..last {
            let k = tree.kinds[n];
            let introduces = matches!(
                k,
                NodeKind::Binding | NodeKind::PatLet | NodeKind::FPat | NodeKind::Param
            );
            if !introduces {
                continue;
            }
            let Some((ty, _)) = cx.local(n as u32) else {
                continue;
            };
            if ty == TY_ERROR || ty == NO_TY || !self.is_linear(ty) {
                continue;
            }
            if k == NodeKind::Param {
                // Rule 22h names the `sink` parameter and nothing else: a
                // `let`/`inout`/`set` parameter is the caller's to consume.
                if param_conv(cx, n) != Conv::Sink {
                    continue;
                }
                // A `sink self` receiver is Rule 22i's consumer of its own
                // HEAD and does not owe that; but a linear COMPONENT of
                // `self` (Rule 22a(b)) is consumed only by a move or by a
                // destructuring that binds it, so the receiver still owes
                // whenever `self` has one.
                if is_self_param(cx, n) && !self.has_linear_component(ty) {
                    continue;
                }
                f.obligs.push(Oblig {
                    root: n as u32,
                    scope: f.body_block,
                    ty,
                    decl: (n as u32, n as u32),
                });
                f.born.push(n as u32);
                continue;
            }
            // Rule 22h's temporaries: a binding that names nothing (`let _
            // = e;`, a `_` component of a tuple binding) can never be
            // consumed, so it is reported where it is written.
            if k == NodeKind::Binding && !names_something(cx, n) {
                let who = format!("the value bound by `_` at {}", self.at(cx, n as u32));
                self.linear_leak(cx, n as u32, &who, ty, None);
                continue;
            }
            // A `for` binding is a view of the iterable's element, not a
            // binding the loop body owns: ch10 Rules 23-26 decide what a
            // container does with linear elements (increment F7), and
            // `container-of-linear-not-iterated-by-value-rejected` is
            // theirs, not this pass's.
            if k != NodeKind::Binding && f.in_borrowed_match(cx, n as u32) {
                continue;
            }
            if k == NodeKind::Binding && for_binding(cx, n as u32) {
                continue;
            }
            let scope = pattern_scope(cx, f, n as u32);
            // A pattern binding exists as soon as its arm is entered; only a
            // `let`/`var` `Binding` waits for its own initialiser.
            let decl = if k == NodeKind::Binding {
                decl_stmt(cx, n as u32)
            } else {
                (n as u32, n as u32)
            };
            f.obligs.push(Oblig {
                root: n as u32,
                scope,
                ty,
                decl,
            });
            if k != NodeKind::Binding {
                // A pattern binding exists as soon as the arm is entered;
                // only a `let`/`var` waits for its initialiser.
                f.born.push(n as u32);
            }
        }
    }

    /// The I8b checks that read the STATIC shape only: Rule 22h's
    /// temporaries, Rule 22d's non-consumptions (`discard`/`consume`),
    /// Rule 23b's "no error exit follows this `errdefer`" and Rule 23d(d)'s
    /// deferred move of a place declared outside the loop.
    fn static_linear_checks(&mut self, cx: &mut BodyCx, f: &mut Flow) {
        let (start, end) = cx.facts.range();
        let tree = cx.f.tree;
        let last = (end as usize).min(tree.kinds.len());
        // Rule 23b, and Rule 23d(d).
        for i in 0..f.defers.len() {
            if self.sink.poisoned() {
                return;
            }
            let (node, scope, errdefer) =
                (f.defers[i].node, f.defers[i].scope, f.defers[i].errdefer);
            // ch01 R23b, read DEFINITE-ONLY (design §7.10). The rule names
            // two cases: "the function does not `raises`" and "every `?`
            // and `raise` of `B` precedes the statement". In a body that
            // DOES declare `raises` and shows no `?`/`raise` at all, the
            // checker cannot see whether a call raises (the callee may be
            // in a package this build does not have), and
            // `errdefer-skipped-on-return-run-ok` is exactly that program
            // and is well-formed — so silence there, and the rule fires on
            // the two cases the corpus rejects.
            // and the body must have something to LOSE: an `errdefer`
            // whose body consumes nothing loses nothing the checker can
            // see, which is the shape of the two programs the corpus
            // calls well-formed (ch09's
            // `defer-body-checks-against-unit-accepted`, ch02's
            // `handler-makes-normal-exit`). Rule 23b's own rationale is
            // the consumption that silently does not happen.
            let visible = cx.raises == NO_TY || has_error_exit(cx, f, scope);
            let consumes = !f.defers[i].moves.is_empty();
            if errdefer && visible && consumes && !error_exit_follows(cx, f, scope, node) {
                self.bemit_code(
                    cx,
                    node as usize,
                    Code::O(23),
                    57,
                    format!(
                        "this `errdefer` at {} can never run: no error exit follows it (ch01 R23b)",
                        self.at(cx, node)
                    ),
                );
                continue;
            }
            let Some(loop_region) = f.region_of(RegionKind::Loop, node) else {
                continue;
            };
            let moves = f.defers[i].moves.clone();
            for m in moves {
                if loop_region.declares(m) {
                    continue;
                }
                let who = self.place_text(cx, m, &[]);
                self.bemit_code(
                    cx,
                    node as usize,
                    Code::O(4),
                    57,
                    format!(
                        "this deferred body moves `{who}`, which is declared outside the loop it \
                         sits in, and nothing re-initialises it before the next iteration (ch01 \
                         R23d(d), R4a(b))"
                    ),
                );
                break;
            }
        }
        // Rule 22h's other temporaries: an expression statement whose value
        // is linear, and a call result that is never bound.
        for n in start as usize..last {
            if self.sink.poisoned() {
                return;
            }
            if tree.kinds[n] != NodeKind::ExprStmt {
                continue;
            }
            let Some(e) = tree.children(n).next() else {
                continue;
            };
            let ty = cx.facts.ty_of(e as u32);
            if ty == TY_ERROR || ty == NO_TY || ty == TY_NEVER || ty == TY_UNIT {
                continue;
            }
            if !self.is_linear(ty) {
                continue;
            }
            let text = self.call_text(cx, e as u32);
            let who = format!("the result of `{text}` at {}", self.at(cx, e as u32));
            self.linear_leak(cx, e as u32, &who, ty, None);
        }
        // Rule 22h's "a call result that is not bound": a linear TEMPORARY
        // handed to a call in a position that does not consume it — the
        // receiver of a `let`/`inout self` method (`make().peek()`), or an
        // argument to a `let`/`inout` parameter (`use_it(make())`) — dies
        // when the call returns. A `sink` position moves it (Rule 22d(i));
        // a struct literal's field init is a consumption too, which is why
        // only `CallExpr` is read here.
        for n in start as usize..last {
            if self.sink.poisoned() {
                return;
            }
            if tree.kinds[n] != NodeKind::CallExpr {
                continue;
            }
            let kids: Vec<usize> = tree.children(n).collect();
            let Some(&callee) = kids.first() else {
                continue;
            };
            let mut dropped: Vec<u32> = Vec::new();
            if tree.kinds[callee] == NodeKind::FieldExpr
                && let Some(recv) = tree.children(callee).next()
                && let Some(conv) = cx.facts.recv_conv_of(n as u32)
                && conv != Conv::Sink
            {
                dropped.push(recv as u32);
            }
            let convs = cx
                .facts
                .arg_convs
                .iter()
                .find(|&&(c, _)| c == n as u32)
                .map(|(_, v)| v.clone())
                .unwrap_or_default();
            let args = kids
                .iter()
                .copied()
                .skip(1)
                .filter(|&c| tree.kinds[c] != NodeKind::Handler);
            for (a, conv) in args.zip(convs) {
                if conv == Conv::Sink {
                    continue;
                }
                let v = if tree.kinds[a] == NodeKind::NamedArg {
                    tree.children(a).last().unwrap_or(a)
                } else {
                    a
                };
                dropped.push(v as u32);
            }
            for v in dropped {
                let temporary = (v as usize) < tree.kinds.len()
                    && matches!(
                        tree.kinds[v as usize],
                        NodeKind::CallExpr | NodeKind::StructLit | NodeKind::TupleOrParen
                    )
                    && local_root(cx, v).is_none();
                if !temporary {
                    continue;
                }
                let ty = cx.facts.ty_of(v);
                if ty == TY_ERROR || ty == NO_TY || ty == TY_NEVER || !self.is_linear(ty) {
                    continue;
                }
                // Rule 22c's own list — going out of scope, `discard`, a
                // `_`, an expression statement — does not include a
                // call-position temporary, so a RIGID one is left to the
                // clauses that name it (`self.b().conv()` on a `Self.B` is
                // ch09's `assoc-type-bound-mentions-other-assoc-type-
                // accepted`); this is Rule 22h's "call result that is not
                // bound", which is about LINEAR types.
                if matches!(
                    self.fir.tys.tag(self.fir.tys.unqual(ty)),
                    TyTag::Param | TyTag::Proj
                ) {
                    continue;
                }
                let text = self.call_text(cx, v);
                let who = format!("the result of `{text}` at {}", self.at(cx, v));
                let at = format!(
                    "the call at {}, which receives it by `let`/`inout` and does not consume it",
                    self.at(cx, n as u32)
                );
                self.linear_leak_at(cx, v, &who, ty, &at);
                return;
            }
        }
        // Rule 22d: `discard p;` and `consume p;` are NOT consumption.
        for n in start as usize..last {
            if self.sink.poisoned() {
                return;
            }
            let word = match tree.kinds[n] {
                NodeKind::DiscardStmt => "discard",
                NodeKind::ConsumeStmt => "consume",
                _ => continue,
            };
            for c in tree.children(n) {
                let ty = cx.facts.ty_of(c as u32);
                if ty == TY_ERROR || ty == NO_TY || !self.is_linear(ty) {
                    continue;
                }
                let who = self.expr_text(cx, c as u32);
                self.linear_leak(cx, c as u32, &who, ty, Some(word));
            }
        }
    }

    /// ch01 Rule 22h at one exit, AFTER the pending `defer`/`errdefer`
    /// bodies of the scopes being left have been accounted for (Rule
    /// 23d(b)), plus Rule 23d(a)'s "every place a body mentions must be
    /// live at every exit at which that body runs".
    fn scope_exit(&mut self, cx: &mut BodyCx, files: &[FileCtx], f: &mut Flow, x: ExitRow) {
        if self.sink.poisoned() {
            return;
        }
        let _ = files;
        let running = f.running_defers(x);
        // (1) Rule 23d(a): the bodies that run here still need their places.
        for &i in &running {
            for m in f.defers[i].mentions.clone() {
                if !f.root_dead(&f.dead, m) {
                    continue;
                }
                let at = f
                    .dead
                    .iter()
                    .rev()
                    .find(|k| f.tape.place(k.place).0 == m)
                    .map(|k| k.at);
                let who = self.place_text(cx, m, &[]);
                let moved_at = at.map(|a| self.at(cx, a)).unwrap_or_default();
                self.bemit_code(
                    cx,
                    f.defers[i].node as usize,
                    Code::O(23),
                    57,
                    format!(
                        "`{who}` is moved at {moved_at} but the deferred body at {} still needs \
                         it (ch01 R23d(a))",
                        self.at(cx, f.defers[i].node)
                    ),
                );
                return;
            }
        }
        // (2) Rule 22h on what is left, and D8's record of what consumed
        // the rest: one `Discharge` per obligation owed on this edge.
        use crate::facts::Discharge;
        let mut discharged: Vec<(u32, Discharge)> = Vec::new();
        for &i in &running {
            for &m in &f.defers[i].moves {
                discharged.push((
                    m,
                    Discharge::DeferredBody {
                        scope: f.defers[i].scope,
                        body: f.defers[i].node,
                    },
                ));
            }
        }
        for &(m, root) in &f.match_dis {
            if m < x.key {
                discharged.push((root, Discharge::Destructured(m)));
            }
        }
        if x.kind == ExitKind::BlockEnd {
            // A tail value anywhere INSIDE the scope being left moves its
            // place into the result of the expression it closes, and that
            // result is what leaves the scope (R22d(i), R23a).
            let end = f
                .scopes
                .iter()
                .find(|&&(a, _)| a == x.node)
                .map(|&(_, e)| e)
                .unwrap_or(x.node + 1);
            for &(b, root) in &f.tail_dis {
                if b >= x.node && b < end {
                    discharged.push((root, Discharge::TailValue(b)));
                }
            }
        }
        let scopes = f.scopes_left(x);
        let obligs: Vec<Oblig> = f
            .obligs
            .iter()
            .filter(|o| scopes.contains(&o.scope))
            .copied()
            .collect();
        for o in obligs {
            if f.said.contains(&o.root)
                || (x.node >= o.decl.0 && x.node < o.decl.1)
                || !f.born.contains(&o.root)
            {
                continue;
            }
            // A whole-place move on THIS path (the kill's own node), or one
            // of the static discharges above.
            let moved = f
                .dead
                .iter()
                .rev()
                .find(|k| {
                    let (r, p) = f.tape.place(k.place);
                    r == o.root && p.is_empty()
                })
                .map(|k| Discharge::MovedAt(k.at));
            let how = moved.or_else(|| {
                discharged
                    .iter()
                    .find(|&&(r, _)| r == o.root)
                    .map(|&(_, how)| how)
            });
            if let Some(how) = how {
                f.discharges.push((x, o.root, how));
                continue;
            }
            f.said.push(o.root);
            let who = format!("`{}`", self.place_text(cx, o.root, &[]));
            let site = match x.kind {
                ExitKind::BlockEnd => x.node,
                _ => x.node,
            };
            let at = format!("{} {}", x.kind.word(), self.at(cx, site));
            self.linear_leak_at(cx, site, &who, o.ty, &at);
            return;
        }
    }

    /// ch01 Rule 22i's diagnostic, for a value that is dropped where it is
    /// written (a temporary, a `discard`): the exit is the statement
    /// itself.
    fn linear_leak(&mut self, cx: &mut BodyCx, node: u32, who: &str, ty: TyId, verb: Option<&str>) {
        let at = match verb {
            Some(w) => format!("the `{w}` at {}", self.at(cx, node)),
            None => format!("the statement at {}", self.at(cx, node)),
        };
        self.linear_leak_at(cx, node, who, ty, &at);
    }

    /// ch01 Rule 22i (normative CONTENT, not wording): the value's name or
    /// "the result of `f()` at L:C", its type as ch09 Rule 20 displays it,
    /// the scope being left, the exit's kind and location, and the
    /// consumers — read from the head's defining module.
    pub fn render_linear_leak(
        &mut self,
        cx: &mut BodyCx,
        who: &str,
        ty: TyId,
        exit: &str,
    ) -> (Code, u16, String) {
        let shown = self.show(ty);
        let rigid = matches!(
            self.fir.tys.tag(self.fir.tys.unqual(ty)),
            TyTag::Param | TyTag::Proj
        );
        if rigid {
            // ch09 R57 (ch01 R22c): a value of rigid type may be linear.
            return (
                Code::T(57),
                57,
                format!(
                    "{who} of rigid type `{shown}` is dropped at {exit}: `{shown}` may be linear, \
                     so bound it `Droppable`, or consume it (ch01 R22c)"
                ),
            );
        }
        let consumers = self.linear_consumers(ty);
        let tail = if consumers.is_empty() {
            "destructure it with a pattern that binds its linear components, or move the whole"
                .to_string()
        } else {
            format!("consume it with {}", consumers.join(" or "))
        };
        let _ = cx;
        (
            Code::O(22),
            57,
            format!(
                "{who} of linear type `{shown}` is not consumed on the path leaving its scope at \
                 {exit}; {tail}, or attach the cleanup with `defer` or `errdefer` (ch01 R22h)"
            ),
        )
    }

    fn linear_leak_at(&mut self, cx: &mut BodyCx, node: u32, who: &str, ty: TyId, exit: &str) {
        let (code, site, msg) = self.render_linear_leak(cx, who, ty, exit);
        self.bemit_code(cx, node as usize, code, site, msg);
    }

    /// ch01 Rule 22i's CONSUMERS: every `sink self` receiver method of the
    /// type's head, plus every function or method declared in the head's
    /// defining module with a `sink` parameter of a type with that head,
    /// `@unsafe` declarations excluded.
    fn linear_consumers(&mut self, ty: TyId) -> Vec<String> {
        let bare = self.fir.tys.unqual(ty);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return Vec::new();
        }
        let head = DefId(self.fir.tys.a(bare));
        let Some(home) = self.defs.get(head).map(|r| r.module) else {
            return Vec::new();
        };
        let mut out: Vec<String> = Vec::new();
        let candidates: Vec<DefId> = self.defs.user_defs().map(|(d, _)| d).collect();
        for def in candidates {
            let Some(row) = self.defs.get(def).copied() else {
                continue;
            };
            if row.kind != fors_index::decl::DeclKind::Fn || row.module != home {
                continue;
            }
            let sig = self.fir.sigs.fn_sig(def);
            if sig == fors_fir::sig::NO_FN_SIG {
                continue;
            }
            let n = self.fir.sigs.fn_sigs.count(sig);
            let mut takes = false;
            for i in 0..n {
                let p = self.fir.sigs.fn_sigs.param(sig, i);
                if p.conv != Conv::Sink {
                    continue;
                }
                let t = self.fir.tys.unqual(p.ty);
                if self.fir.tys.tag(t) == TyTag::Nominal && DefId(self.fir.tys.a(t)) == head {
                    takes = true;
                }
            }
            if !takes {
                continue;
            }
            let name = self
                .defs
                .get(def)
                .and_then(|r| r.name)
                .map(|s| self.sym(s))
                .unwrap_or_default();
            if name.is_empty() {
                continue;
            }
            // R22i writes a receiver method as `Head.method`
            // ("`Vec[i32, heap]` ... is `Vec.deinit(&<allocator>)`"); a
            // free function of the defining module is named as itself.
            let in_impl = row.parent != fors_fir::NO_DEF
                && self.fir.sigs.self_ty(row.parent) != NO_TY
                && self
                    .fir
                    .tys
                    .tag(self.fir.tys.unqual(self.fir.sigs.self_ty(row.parent)))
                    == TyTag::Nominal
                && DefId(
                    self.fir
                        .tys
                        .a(self.fir.tys.unqual(self.fir.sigs.self_ty(row.parent))),
                ) == head;
            let label = if in_impl {
                let owner = self.head_name(head);
                format!("`{owner}.{name}`")
            } else {
                format!("`{name}`")
            };
            if !out.contains(&label) {
                out.push(label);
            }
        }
        out.sort();
        out
    }

    /// The source text of an expression, for a message that quotes the
    /// program back.
    fn expr_text(&self, cx: &BodyCx, node: u32) -> String {
        format!("`{}`", self.call_text(cx, node))
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
