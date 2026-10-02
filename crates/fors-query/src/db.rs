//! The engine (design §9): input and derived nodes with a value hash,
//! dependency recording, red-green verification with early cutoff, cycle
//! recovery and cancellation that writes nothing.
//!
//! The engine is deliberately ignorant of what a query *computes*. It owns
//! four columns per node — the last revision the node was verified at, the
//! last revision its value hash changed at, its value hash, and its
//! dependency edges — and nothing else. The query set keeps the values in
//! its own struct-of-arrays and hands back a hash, so there is no
//! `Arc<dyn Any>` anywhere and no allocation per answer.
//!
//! Invalidation is the two revision columns and nothing more:
//!
//! - `set_input` bumps the global revision and stamps the input's
//!   `changed_at`.
//! - a derived node is up to date iff `verified_at == revision`.
//! - otherwise its recorded dependencies are asked, in order, whether they
//!   changed since this node was last verified. If none did, the node is
//!   re-stamped and NOT re-executed (green).
//! - if one did, the node is re-executed. If the new value hash equals the
//!   old one, `changed_at` is left where it was: the node's own dependents
//!   then verify green. That is the early cutoff, and it is what makes a
//!   whitespace edit free and a re-spelled bound free for every dependent.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::cycle::{Cancelled, Cycle, Frame};
use crate::key::{QueryKey, Revision, ValueHash};
use crate::stats::Stats;

/// What a query's computation returns.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Outcome {
    /// The value's hash. The value itself is already in the query set's own
    /// memo.
    Value(ValueHash),
    /// The computation noticed the cancellation flag and stopped. The
    /// engine writes nothing for this node.
    Cancelled,
}

/// The query set: one implementation per language, holding the memos.
///
/// `compute` reads its dependencies back through the same `Db` (`db.read`),
/// which is how the edges are recorded — a query never declares its edges
/// up front, so an edge cannot be forgotten by a later edit to the body.
pub trait Queries {
    /// Computes `key`, reading dependencies with [`Db::read`].
    fn compute(&mut self, db: &mut Db, key: QueryKey) -> Outcome;

    /// The recovery value for a cycle through `key` — design §9's
    /// "caller-declared `on_cycle` recovery value". Called instead of
    /// re-entering `compute`, and never memoised.
    fn on_cycle(&mut self, key: QueryKey, cycle: &Cycle) -> ValueHash;
}

/// One node's answer: its value hash and the revision that value last
/// changed at.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Answer {
    pub value: ValueHash,
    pub changed_at: Revision,
}

/// A flag a cancelling thread sets and the engine polls. Shared, so an LSP
/// can cancel a check from the request thread; a cancelled demand leaves
/// every node exactly as it was.
#[derive(Clone, Default, Debug)]
pub struct CancelFlag(Arc<AtomicBool>);

impl CancelFlag {
    pub fn new() -> CancelFlag {
        CancelFlag::default()
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    pub fn reset(&self) {
        self.0.store(false, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum State {
    /// Interned but never computed.
    Empty,
    /// Has a value and a dependency range.
    Valid,
}

/// Node columns, struct-of-arrays like every other table in this compiler.
#[derive(Default)]
struct Nodes {
    key: Vec<QueryKey>,
    value: Vec<ValueHash>,
    verified_at: Vec<u64>,
    changed_at: Vec<u64>,
    dep_start: Vec<u32>,
    dep_len: Vec<u32>,
    state: Vec<State>,
    is_input: Vec<bool>,
}

impl Nodes {
    fn push(&mut self, key: QueryKey) -> u32 {
        let id = self.key.len() as u32;
        self.key.push(key);
        self.value.push(0);
        self.verified_at.push(0);
        self.changed_at.push(0);
        self.dep_start.push(0);
        self.dep_len.push(0);
        self.state.push(State::Empty);
        self.is_input.push(false);
        id
    }

    fn len(&self) -> usize {
        self.key.len()
    }
}

/// The incremental database.
pub struct Db {
    rev: u64,
    nodes: Nodes,
    index: HashMap<QueryKey, u32>,
    /// Append-only dependency arena. A re-execution appends a fresh range
    /// rather than patching the old one in place, so a verification walk
    /// already reading a range is never invalidated under it;
    /// [`Db::compact`] reclaims the superseded ranges.
    deps: Vec<u32>,
    stack: Vec<Frame>,
    stats: Stats,
    cancel: CancelFlag,
    /// Keys executed since the last [`Db::open_window`], in execution
    /// order. The M1 gate (c) test reads exactly this.
    executed: Vec<QueryKey>,
    window: bool,
}

impl Default for Db {
    fn default() -> Db {
        Db::new()
    }
}

impl Db {
    pub fn new() -> Db {
        Db {
            rev: 0,
            nodes: Nodes::default(),
            index: HashMap::new(),
            deps: Vec::new(),
            stack: Vec::new(),
            stats: Stats::default(),
            cancel: CancelFlag::new(),
            executed: Vec::new(),
            window: false,
        }
    }

    pub fn revision(&self) -> Revision {
        Revision(self.rev)
    }

    pub fn cancel_flag(&self) -> CancelFlag {
        self.cancel.clone()
    }

    pub fn is_cancelled(&self) -> bool {
        self.cancel.is_cancelled()
    }

    /// Declares `key` an input and gives it a value hash. Returns whether
    /// the value changed; a change bumps the revision, which is the only
    /// thing that can make a derived node red.
    pub fn set_input(&mut self, key: QueryKey, value: ValueHash) -> bool {
        let id = self.intern(key);
        let i = id as usize;
        assert!(
            self.nodes.state[i] != State::Valid || self.nodes.is_input[i],
            "{key:?} was computed as a derived query and cannot become an input"
        );
        self.nodes.is_input[i] = true;
        if self.nodes.state[i] == State::Valid && self.nodes.value[i] == value {
            return false;
        }
        self.rev += 1;
        self.nodes.value[i] = value;
        self.nodes.changed_at[i] = self.rev;
        self.nodes.verified_at[i] = self.rev;
        self.nodes.state[i] = State::Valid;
        self.stats.input_writes += 1;
        true
    }

    /// An input's current value hash, if it has one.
    pub fn input(&self, key: QueryKey) -> Option<ValueHash> {
        let id = *self.index.get(&key)? as usize;
        (self.nodes.is_input[id] && self.nodes.state[id] == State::Valid)
            .then(|| self.nodes.value[id])
    }

    /// A node's memoised value hash, without demanding it. `None` when the
    /// node was never computed.
    pub fn value_of(&self, key: QueryKey) -> Option<ValueHash> {
        let id = *self.index.get(&key)? as usize;
        (self.nodes.state[id] == State::Valid).then(|| self.nodes.value[id])
    }

    /// The revision a node's value last changed at.
    pub fn changed_at(&self, key: QueryKey) -> Option<Revision> {
        let id = *self.index.get(&key)? as usize;
        (self.nodes.state[id] == State::Valid).then(|| Revision(self.nodes.changed_at[id]))
    }

    /// The dependency edges a node recorded at its last execution.
    pub fn deps_of(&self, key: QueryKey) -> Vec<QueryKey> {
        let Some(&id) = self.index.get(&key) else {
            return Vec::new();
        };
        let i = id as usize;
        let (s, l) = (
            self.nodes.dep_start[i] as usize,
            self.nodes.dep_len[i] as usize,
        );
        self.deps[s..s + l]
            .iter()
            .map(|&d| self.nodes.key[d as usize])
            .collect()
    }

    /// Demands `key`, recording it as a dependency of the query currently
    /// executing (if any).
    pub fn read(&mut self, q: &mut dyn Queries, key: QueryKey) -> Result<ValueHash, Cancelled> {
        self.pull(q, key, true).map(|a| a.value)
    }

    /// Demands `key` at the top level: the same work as [`Db::read`], but
    /// never an edge (nothing is executing).
    pub fn demand(&mut self, q: &mut dyn Queries, key: QueryKey) -> Result<ValueHash, Cancelled> {
        self.pull(q, key, true).map(|a| a.value)
    }

    /// Whether demanding `key` right now would re-execute it: the planning
    /// primitive. It runs the red-green verification — so a node that comes
    /// out green IS re-stamped and will not be re-executed later in this
    /// revision — but it never calls `compute`.
    ///
    /// The Fors query set needs this because one pass of `fors-check` types
    /// many bodies in one traversal: it asks which `check_body` nodes are
    /// red, runs the body phase for exactly those, and only then demands
    /// them. See `fors_check::queries`.
    pub fn is_red(&mut self, q: &mut dyn Queries, key: QueryKey) -> Result<bool, Cancelled> {
        if self.cancel.is_cancelled() {
            self.stats.cancellations += 1;
            return Err(Cancelled);
        }
        let id = self.intern(key);
        let i = id as usize;
        self.stats.probes += 1;
        if self.nodes.is_input[i] {
            return Ok(false);
        }
        if self.nodes.state[i] == State::Valid && self.nodes.verified_at[i] == self.rev {
            self.stats.memo_hits += 1;
            return Ok(false);
        }
        if self.stack.iter().any(|f| f.node == id) {
            return Ok(false);
        }
        Ok(!self.verify(q, id)?)
    }

    /// Opens a counting window: [`Db::executed_keys`] then reports exactly
    /// the keys executed from here on. Clears the per-window counters too.
    pub fn open_window(&mut self) {
        self.executed.clear();
        self.window = true;
        let by_kind_len = self.stats.by_kind.len();
        self.stats = Stats {
            by_kind: vec![0; by_kind_len],
            ..Stats::default()
        };
    }

    /// The keys executed since [`Db::open_window`], in execution order.
    pub fn executed_keys(&self) -> &[QueryKey] {
        &self.executed
    }

    /// The keys of one kind executed since [`Db::open_window`], sorted and
    /// deduplicated — the set the M1 gate (c) test compares.
    pub fn executed_of_kind(&self, kind: u16) -> Vec<QueryKey> {
        let mut v: Vec<QueryKey> = self
            .executed
            .iter()
            .copied()
            .filter(|k| k.kind == kind)
            .collect();
        v.sort_unstable();
        v.dedup();
        v
    }

    /// The counters, with the node totals refreshed.
    pub fn stats(&self) -> Stats {
        let mut s = self.stats.clone();
        s.revision = self.rev;
        s.nodes = self.nodes.len() as u64;
        s.inputs = self.nodes.is_input.iter().filter(|&&b| b).count() as u64;
        s.dep_edges = self.nodes.dep_len.iter().map(|&l| l as u64).sum();
        s.dep_arena = self.deps.len() as u64;
        s
    }

    /// Rebuilds the dependency arena from the live ranges, dropping the
    /// edges of superseded executions. Safe only outside a demand.
    pub fn compact(&mut self) {
        assert!(self.stack.is_empty(), "compact() during a demand");
        let mut fresh: Vec<u32> =
            Vec::with_capacity(self.nodes.dep_len.iter().sum::<u32>() as usize);
        for i in 0..self.nodes.len() {
            let (s, l) = (
                self.nodes.dep_start[i] as usize,
                self.nodes.dep_len[i] as usize,
            );
            let start = fresh.len() as u32;
            fresh.extend_from_slice(&self.deps[s..s + l]);
            self.nodes.dep_start[i] = start;
        }
        self.deps = fresh;
    }

    // ------------------------------------------------------------ internals

    fn intern(&mut self, key: QueryKey) -> u32 {
        if let Some(&id) = self.index.get(&key) {
            return id;
        }
        let id = self.nodes.push(key);
        self.index.insert(key, id);
        id
    }

    fn answer(&self, i: usize) -> Answer {
        Answer {
            value: self.nodes.value[i],
            changed_at: Revision(self.nodes.changed_at[i]),
        }
    }

    fn pull(
        &mut self,
        q: &mut dyn Queries,
        key: QueryKey,
        attribute: bool,
    ) -> Result<Answer, Cancelled> {
        if self.cancel.is_cancelled() {
            self.stats.cancellations += 1;
            return Err(Cancelled);
        }
        let id = self.intern(key);
        let i = id as usize;
        self.stats.probes += 1;
        if attribute
            && let Some(f) = self.stack.last_mut()
            && f.attribute
            && f.node != id
        {
            f.deps.push(id);
        }
        if self.nodes.is_input[i] {
            self.stats.input_reads += 1;
            assert!(
                self.nodes.state[i] == State::Valid,
                "input {key:?} was read before it was set"
            );
            return Ok(self.answer(i));
        }
        if self.nodes.state[i] == State::Valid && self.nodes.verified_at[i] == self.rev {
            self.stats.memo_hits += 1;
            return Ok(self.answer(i));
        }
        if self.stack.iter().any(|f| f.node == id) {
            self.stats.cycles += 1;
            let cycle = self.cycle_report(id, key);
            let value = q.on_cycle(key, &cycle);
            // Never memoised: see `cycle.rs`.
            return Ok(Answer {
                value,
                changed_at: Revision(self.rev),
            });
        }
        if self.verify(q, id)? {
            return Ok(self.answer(i));
        }
        self.execute(q, key, id)
    }

    /// The red-green walk. `true` means "already up to date, not
    /// re-executed"; the node is re-stamped at the current revision.
    fn verify(&mut self, q: &mut dyn Queries, id: u32) -> Result<bool, Cancelled> {
        let i = id as usize;
        if self.nodes.state[i] != State::Valid {
            return Ok(false);
        }
        let (s, l) = (
            self.nodes.dep_start[i] as usize,
            self.nodes.dep_len[i] as usize,
        );
        let verified = self.nodes.verified_at[i];
        // Pushed so a dependency that leads back here is caught as a cycle
        // rather than recursing for ever; `attribute: false` keeps the
        // "did you change?" reads out of the edge set.
        self.stack.push(Frame {
            node: id,
            deps: Vec::new(),
            attribute: false,
        });
        let mut dirty = false;
        for j in 0..l {
            let dep = self.deps[s + j];
            let dep_key = self.nodes.key[dep as usize];
            match self.pull(q, dep_key, false) {
                Ok(a) => {
                    if a.changed_at.0 > verified {
                        dirty = true;
                        break;
                    }
                }
                Err(c) => {
                    self.stack.pop();
                    return Err(c);
                }
            }
        }
        self.stack.pop();
        if dirty {
            self.stats.red += 1;
            return Ok(false);
        }
        self.nodes.verified_at[i] = self.rev;
        self.stats.green += 1;
        Ok(true)
    }

    fn execute(
        &mut self,
        q: &mut dyn Queries,
        key: QueryKey,
        id: u32,
    ) -> Result<Answer, Cancelled> {
        self.stack.push(Frame {
            node: id,
            deps: Vec::new(),
            attribute: true,
        });
        let out = q.compute(self, key);
        let frame = self.stack.pop().expect("the frame just pushed");
        let i = id as usize;
        let value = match out {
            Outcome::Cancelled => {
                // Writes nothing: `frame` (and with it every edge this
                // attempt recorded) is dropped, and neither revision column
                // moved.
                self.stats.cancellations += 1;
                return Err(Cancelled);
            }
            Outcome::Value(v) => v,
        };
        let mut deps = frame.deps;
        deps.sort_unstable();
        deps.dedup();
        let start = self.deps.len() as u32;
        self.deps.extend_from_slice(&deps);
        self.nodes.dep_start[i] = start;
        self.nodes.dep_len[i] = deps.len() as u32;
        self.stats.executed += 1;
        self.stats.charge_kind(key.kind);
        if self.window {
            self.executed.push(key);
        }
        let fresh = self.nodes.state[i] != State::Valid;
        self.nodes.verified_at[i] = self.rev;
        if fresh || self.nodes.value[i] != value {
            self.nodes.value[i] = value;
            self.nodes.changed_at[i] = self.rev;
        } else {
            self.stats.cutoffs += 1;
        }
        self.nodes.state[i] = State::Valid;
        Ok(self.answer(i))
    }

    fn cycle_report(&self, id: u32, key: QueryKey) -> Cycle {
        let from = self
            .stack
            .iter()
            .position(|f| f.node == id)
            .unwrap_or_default();
        Cycle {
            at: key,
            path: self.stack[from..]
                .iter()
                .map(|f| self.nodes.key[f.node as usize])
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const IN: u16 = 0;
    const MID: u16 = 1;
    const TOP: u16 = 2;
    const CYC: u16 = 3;

    /// A synthetic query set: `mid(i)` is `in(i)` rounded down to a
    /// multiple of ten (so an input edit that does not cross a ten is an
    /// early cutoff), and `top()` sums every `mid`.
    #[derive(Default)]
    struct Synth {
        n: u32,
        /// The SoA memo: one column per query type, no `dyn Any`.
        mid: Vec<u64>,
        top: u64,
        runs: Vec<QueryKey>,
        cancel_at: Option<QueryKey>,
        cycles_seen: Vec<Cycle>,
    }

    impl Queries for Synth {
        fn compute(&mut self, db: &mut Db, key: QueryKey) -> Outcome {
            self.runs.push(key);
            if self.cancel_at == Some(key) {
                return Outcome::Cancelled;
            }
            match key.kind {
                MID => {
                    let v = match db.read(self, QueryKey::one(IN, key.a)) {
                        Ok(v) => v as u64,
                        Err(_) => return Outcome::Cancelled,
                    };
                    let out = v - v % 10;
                    if self.mid.len() <= key.a as usize {
                        self.mid.resize(key.a as usize + 1, 0);
                    }
                    self.mid[key.a as usize] = out;
                    Outcome::Value(out as u128)
                }
                TOP => {
                    let mut sum = 0u64;
                    for i in 0..self.n {
                        match db.read(self, QueryKey::one(MID, i)) {
                            Ok(v) => sum += v as u64,
                            Err(_) => return Outcome::Cancelled,
                        }
                    }
                    self.top = sum;
                    Outcome::Value(sum as u128)
                }
                CYC => {
                    let next = QueryKey::one(CYC, (key.a + 1) % 3);
                    match db.read(self, next) {
                        Ok(v) => Outcome::Value(v + 1),
                        Err(_) => Outcome::Cancelled,
                    }
                }
                _ => unreachable!("kind {}", key.kind),
            }
        }

        fn on_cycle(&mut self, _key: QueryKey, cycle: &Cycle) -> ValueHash {
            self.cycles_seen.push(cycle.clone());
            0
        }
    }

    fn build(n: u32, values: &[u128]) -> (Db, Synth) {
        let mut db = Db::new();
        let mut q = Synth {
            n,
            ..Synth::default()
        };
        for (i, &v) in values.iter().enumerate() {
            db.set_input(QueryKey::one(IN, i as u32), v);
        }
        db.demand(&mut q, QueryKey::unit(TOP)).expect("cold build");
        (db, q)
    }

    #[test]
    fn a_cold_build_executes_every_derived_node_once() {
        let (db, q) = build(3, &[11, 22, 33]);
        assert_eq!(q.runs.len(), 4, "3 mid + 1 top: {:?}", q.runs);
        assert_eq!(db.value_of(QueryKey::unit(TOP)), Some(60));
    }

    #[test]
    fn an_unchanged_input_write_is_not_a_revision() {
        let (mut db, mut q) = build(2, &[11, 22]);
        let rev = db.revision();
        assert!(!db.set_input(QueryKey::one(IN, 0), 11));
        assert_eq!(db.revision(), rev);
        db.open_window();
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(db.executed_keys(), &[], "nothing may re-execute");
    }

    #[test]
    fn an_edit_re_executes_only_the_path_to_the_root() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        db.set_input(QueryKey::one(IN, 1), 25);
        db.open_window();
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        // `mid(1)` re-executes; its value is still 20, so `top` is cut off.
        assert_eq!(db.executed_keys(), &[QueryKey::one(MID, 1)]);
        assert_eq!(db.stats().cutoffs, 1);
        // `top` walks all three `mid`s and finds none changed, and the two
        // untouched `mid`s verify green against their own input: 3 green.
        assert_eq!(db.stats().green, 3, "top verified green after the cutoff");
    }

    #[test]
    fn an_edit_that_changes_the_value_wakes_the_dependent() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        db.set_input(QueryKey::one(IN, 1), 35);
        db.open_window();
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(
            db.executed_keys(),
            &[QueryKey::one(MID, 1), QueryKey::unit(TOP)]
        );
        assert_eq!(db.value_of(QueryKey::unit(TOP)), Some(70));
        assert_eq!(db.stats().cutoffs, 0);
    }

    #[test]
    fn an_edit_and_revert_restores_the_cold_value_and_executes_nothing_new() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        let cold = db.value_of(QueryKey::unit(TOP));
        db.set_input(QueryKey::one(IN, 1), 99);
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        db.set_input(QueryKey::one(IN, 1), 22);
        db.open_window();
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(db.value_of(QueryKey::unit(TOP)), cold);
        assert_eq!(
            db.executed_keys(),
            &[QueryKey::one(MID, 1), QueryKey::unit(TOP)]
        );
    }

    #[test]
    fn dependency_edges_are_the_reads_the_computation_took() {
        let (db, _) = build(2, &[1, 2]);
        assert_eq!(
            db.deps_of(QueryKey::unit(TOP)),
            vec![QueryKey::one(MID, 0), QueryKey::one(MID, 1)]
        );
        assert_eq!(
            db.deps_of(QueryKey::one(MID, 0)),
            vec![QueryKey::one(IN, 0)]
        );
    }

    #[test]
    fn a_cycle_is_broken_by_the_callers_recovery_value_and_not_memoised() {
        let mut db = Db::new();
        let mut q = Synth::default();
        let v = db.demand(&mut q, QueryKey::one(CYC, 0)).unwrap();
        assert_eq!(v, 3, "three +1 hops over the recovery value 0");
        assert_eq!(db.stats().cycles, 1);
        let cycle = &q.cycles_seen[0];
        assert_eq!(cycle.at, QueryKey::one(CYC, 0));
        assert_eq!(cycle.path.len(), 3, "the whole in-flight path: {cycle:?}");
    }

    #[test]
    fn a_cancelled_computation_writes_nothing() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        let before = db.value_of(QueryKey::one(MID, 1));
        let deps_before = db.deps_of(QueryKey::unit(TOP));
        db.set_input(QueryKey::one(IN, 1), 95);
        q.cancel_at = Some(QueryKey::one(MID, 1));
        assert_eq!(
            db.demand(&mut q, QueryKey::unit(TOP)),
            Err(Cancelled),
            "the demand must report the cancellation"
        );
        assert_eq!(db.value_of(QueryKey::one(MID, 1)), before);
        assert_eq!(db.deps_of(QueryKey::unit(TOP)), deps_before);
        // And the build recovers: the same demand, with the cancellation
        // lifted, produces the value the edit asked for.
        q.cancel_at = None;
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(db.value_of(QueryKey::one(MID, 1)), Some(90));
    }

    #[test]
    fn the_cancellation_flag_stops_a_demand_before_it_starts() {
        let (mut db, mut q) = build(2, &[11, 22]);
        db.set_input(QueryKey::one(IN, 0), 95);
        db.cancel_flag().cancel();
        assert_eq!(db.demand(&mut q, QueryKey::unit(TOP)), Err(Cancelled));
        db.cancel_flag().reset();
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(db.value_of(QueryKey::unit(TOP)), Some(110));
    }

    #[test]
    fn is_red_plans_without_computing() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        db.set_input(QueryKey::one(IN, 1), 95);
        db.open_window();
        assert!(db.is_red(&mut q, QueryKey::one(MID, 1)).unwrap());
        assert!(!db.is_red(&mut q, QueryKey::one(MID, 0)).unwrap());
        assert_eq!(db.executed_keys(), &[], "planning executes nothing");
        // The green node stays green afterwards; the red one runs.
        db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        assert_eq!(
            db.executed_keys(),
            &[QueryKey::one(MID, 1), QueryKey::unit(TOP)]
        );
    }

    #[test]
    fn compact_keeps_every_live_edge() {
        let (mut db, mut q) = build(3, &[11, 22, 33]);
        for v in [95u128, 15, 25] {
            db.set_input(QueryKey::one(IN, 1), v);
            db.demand(&mut q, QueryKey::unit(TOP)).unwrap();
        }
        let before: Vec<Vec<QueryKey>> = (0..3)
            .map(|i| db.deps_of(QueryKey::one(MID, i)))
            .chain(std::iter::once(db.deps_of(QueryKey::unit(TOP))))
            .collect();
        assert!(db.stats().dep_arena > db.stats().dep_edges);
        db.compact();
        let after: Vec<Vec<QueryKey>> = (0..3)
            .map(|i| db.deps_of(QueryKey::one(MID, i)))
            .chain(std::iter::once(db.deps_of(QueryKey::unit(TOP))))
            .collect();
        assert_eq!(before, after);
        assert_eq!(db.stats().dep_arena, db.stats().dep_edges);
    }

    #[test]
    fn stats_count_executions_per_kind() {
        let (db, _) = build(3, &[11, 22, 33]);
        let s = db.stats();
        assert_eq!(s.executed_of(MID), 3);
        assert_eq!(s.executed_of(TOP), 1);
        assert!(s.render(&["in", "mid", "top"]).contains("mid"));
    }
}
