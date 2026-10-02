//! `--stats` (design §9): what the engine did, as counts of work rather
//! than durations, so CI can gate on them (design §12: "near-linearity is
//! gated on deterministic counters, wall time is secondary").

use crate::key::Revision;

/// Engine counters. Everything here is deterministic for a given sequence
/// of input writes and demands — two runs of the same edit script produce
/// the same numbers on any machine.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// The engine's revision at the time the stats were read.
    pub revision: u64,
    /// Interned nodes, and how many of them are inputs.
    pub nodes: u64,
    pub inputs: u64,
    /// Dependency edges the current node set records, and the total the
    /// append-only edge arena holds (edges of superseded executions are
    /// not reclaimed until [`crate::Db::compact`]).
    pub dep_edges: u64,
    pub dep_arena: u64,
    /// `set_input` calls that actually changed a value.
    pub input_writes: u64,
    /// Every `read`/`demand`, including the ones a memo answered.
    pub probes: u64,
    pub input_reads: u64,
    /// Answered because the node was already verified at this revision.
    pub memo_hits: u64,
    /// Verified by walking the recorded dependencies and finding none
    /// changed — the node was NOT re-executed (red-green's green path).
    pub green: u64,
    /// A dependency had changed, so the node was re-executed.
    pub red: u64,
    /// Nodes executed (the number the M1 gate (b) counter test reads).
    pub executed: u64,
    /// Executions whose value came out byte-identical, so no dependent was
    /// woken: the early cutoff.
    pub cutoffs: u64,
    /// Cycles broken by the caller's `on_cycle` recovery value.
    pub cycles: u64,
    /// Demands abandoned because the cancellation flag was set. A cancelled
    /// computation writes nothing.
    pub cancellations: u64,
    /// Executions per query kind, indexed by `QueryKey::kind`.
    pub by_kind: Vec<u64>,
}

impl Stats {
    pub(crate) fn charge_kind(&mut self, kind: u16) {
        let i = kind as usize;
        if self.by_kind.len() <= i {
            self.by_kind.resize(i + 1, 0);
        }
        self.by_kind[i] += 1;
    }

    pub fn revision(&self) -> Revision {
        Revision(self.revision)
    }

    /// Executions of one query kind.
    pub fn executed_of(&self, kind: u16) -> u64 {
        self.by_kind.get(kind as usize).copied().unwrap_or(0)
    }

    /// The `--stats` block. `names[k]` names kind `k`; a kind past the end
    /// of `names` prints as its number.
    pub fn render(&self, names: &[&str]) -> String {
        use std::fmt::Write as _;
        let mut s = String::new();
        let _ = writeln!(s, "revision             r{}", self.revision);
        let _ = writeln!(s, "nodes                {}", self.nodes);
        let _ = writeln!(s, "  inputs             {}", self.inputs);
        let _ = writeln!(s, "dependency edges     {}", self.dep_edges);
        let _ = writeln!(s, "  edge arena         {}", self.dep_arena);
        let _ = writeln!(s, "input writes         {}", self.input_writes);
        let _ = writeln!(s, "probes               {}", self.probes);
        let _ = writeln!(s, "  input reads        {}", self.input_reads);
        let _ = writeln!(s, "  memo hits          {}", self.memo_hits);
        let _ = writeln!(s, "  verified green     {}", self.green);
        let _ = writeln!(s, "  verified red       {}", self.red);
        let _ = writeln!(s, "executed             {}", self.executed);
        let _ = writeln!(s, "  early cutoffs      {}", self.cutoffs);
        let _ = writeln!(s, "cycles recovered     {}", self.cycles);
        let _ = writeln!(s, "cancellations        {}", self.cancellations);
        for (k, n) in self.by_kind.iter().enumerate() {
            if *n == 0 {
                continue;
            }
            match names.get(k) {
                Some(name) => {
                    let _ = writeln!(s, "  {name:<17} {n}");
                }
                None => {
                    let _ = writeln!(s, "  kind {k:<12} {n}");
                }
            }
        }
        s
    }
}
