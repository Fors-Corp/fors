//! Comptime budgets (ch04 R14; design §6's budget table, §10.1).
//!
//! **Deterministic counters, never wall time**: a wall-clock budget would
//! make the build non-reproducible (ch04 R12, ch06). Steps are charged
//! PER INSTRUCTION (every instruction and every terminator the dispatch loop
//! executes is one step — the granularity design §6 names, and the only one
//! that bounds a pathological straight-line body); bytes are charged per
//! allocated byte (an `alloc`'s size, a `Str`'s length, eight bytes per
//! aggregate cell — the size of the slot it holds).
//!
//! Three limits:
//! - [`COMPTIME_STEP_BUDGET`] and [`COMPTIME_ALLOC_BUDGET`] bound ONE
//!   evaluation (ch04 R14 charges per evaluation); exceeding either is a
//!   build error naming the declaration, with the counts.
//! - [`COMPTIME_BUILD_STEP_BUDGET`] (owner Q6, recorded in design §11.1)
//!   bounds the whole build: the sum of every evaluation's steps. Exceeding
//!   it is a build error naming the MOST EXPENSIVE declaration evaluated so
//!   far, with the counts — a per-declaration cap is not a build cap.

/// ch04 R14's per-evaluation step budget: `2^20` (design §6: ≈35 ms at the
/// §10.1 speed target).
pub const COMPTIME_STEP_BUDGET: u64 = 1 << 20;

/// ch04 R14's per-evaluation allocation budget: 64 MiB (design §6).
pub const COMPTIME_ALLOC_BUDGET: u64 = 64 << 20;

/// The build-wide step cap, owner decision Q6: `2^28`.
pub const COMPTIME_BUILD_STEP_BUDGET: u64 = 1 << 28;

/// The limits one build evaluates under. The memo key covers the
/// per-evaluation pair (a result is a function of the budget it was
/// computed under: a smaller budget can turn it into an error).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Limits {
    pub step: u64,
    pub alloc: u64,
    pub build_step: u64,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            step: COMPTIME_STEP_BUDGET,
            alloc: COMPTIME_ALLOC_BUDGET,
            build_step: COMPTIME_BUILD_STEP_BUDGET,
        }
    }
}

/// Which limit an evaluation hit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Exceeded {
    /// [`COMPTIME_STEP_BUDGET`] (or the build's own limit) for this
    /// evaluation: `steps` charged when the limit tripped.
    Steps { steps: u64, limit: u64 },
    /// [`COMPTIME_ALLOC_BUDGET`]: `bytes` charged when it tripped.
    Bytes { bytes: u64, limit: u64 },
    /// [`COMPTIME_BUILD_STEP_BUDGET`]: the build had `remaining` steps left
    /// when this evaluation started and used them all.
    Build {
        build_steps: u64,
        limit: u64,
        most_expensive: Option<(String, u64)>,
    },
}

/// One evaluation's meter.
#[derive(Clone, Debug)]
pub struct Meter {
    pub steps: u64,
    pub bytes: u64,
    step_limit: u64,
    alloc_limit: u64,
    /// The build's remaining steps when this evaluation started; tripping
    /// it before `step_limit` is [`Exceeded::Build`].
    build_remaining: u64,
}

impl Meter {
    pub fn new(limits: &Limits, build_remaining: u64) -> Meter {
        Meter {
            steps: 0,
            bytes: 0,
            step_limit: limits.step,
            alloc_limit: limits.alloc,
            build_remaining,
        }
    }

    /// One step. `Err` names which limit tripped; the dispatch loop stops
    /// right there (the step is counted, so the reported count is one past
    /// the limit — the first step that did not fit).
    pub fn step(&mut self) -> Result<(), Exceeded> {
        self.steps += 1;
        if self.steps > self.build_remaining && self.build_remaining < self.step_limit {
            return Err(Exceeded::Build {
                build_steps: 0,
                limit: 0,
                most_expensive: None,
            });
        }
        if self.steps > self.step_limit {
            return Err(Exceeded::Steps {
                steps: self.steps,
                limit: self.step_limit,
            });
        }
        Ok(())
    }

    /// `n` allocated bytes.
    pub fn bytes(&mut self, n: u64) -> Result<(), Exceeded> {
        self.bytes = self.bytes.saturating_add(n);
        if self.bytes > self.alloc_limit {
            return Err(Exceeded::Bytes {
                bytes: self.bytes,
                limit: self.alloc_limit,
            });
        }
        Ok(())
    }
}

/// The build-wide account (owner Q6): every evaluation's steps, and which
/// declaration cost the most.
#[derive(Clone, Debug)]
pub struct BuildMeter {
    pub steps: u64,
    pub limit: u64,
    /// `(declaration, steps)` of every evaluation charged, in order.
    pub per_decl: Vec<(String, u64)>,
}

impl BuildMeter {
    pub fn new(limits: &Limits) -> BuildMeter {
        BuildMeter {
            steps: 0,
            limit: limits.build_step,
            per_decl: Vec::new(),
        }
    }

    /// Steps the build may still spend.
    pub fn remaining(&self) -> u64 {
        self.limit.saturating_sub(self.steps)
    }

    /// Charges one finished (or stopped) evaluation.
    pub fn charge(&mut self, decl: &str, steps: u64) {
        self.steps = self.steps.saturating_add(steps);
        self.per_decl.push((decl.to_string(), steps));
    }

    /// The most expensive declaration so far: the largest step count, the
    /// earliest on a tie (deterministic).
    pub fn most_expensive(&self) -> Option<(String, u64)> {
        let mut best: Option<&(String, u64)> = None;
        for row in &self.per_decl {
            if best.is_none_or(|b| row.1 > b.1) {
                best = Some(row);
            }
        }
        best.cloned()
    }

    /// The [`Exceeded::Build`] this account reports.
    pub fn exceeded(&self) -> Exceeded {
        Exceeded::Build {
            build_steps: self.steps,
            limit: self.limit,
            most_expensive: self.most_expensive(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_constants_are_the_recorded_figures() {
        assert_eq!(COMPTIME_STEP_BUDGET, 1_048_576);
        assert_eq!(COMPTIME_ALLOC_BUDGET, 67_108_864);
        assert_eq!(COMPTIME_BUILD_STEP_BUDGET, 268_435_456);
    }

    #[test]
    fn a_meter_trips_one_past_its_limit() {
        let limits = Limits {
            step: 3,
            alloc: 10,
            build_step: 100,
        };
        let mut m = Meter::new(&limits, 100);
        for _ in 0..3 {
            m.step().expect("within budget");
        }
        assert_eq!(m.step(), Err(Exceeded::Steps { steps: 4, limit: 3 }));
        m.bytes(10).expect("exactly the budget fits");
        assert_eq!(
            m.bytes(1),
            Err(Exceeded::Bytes {
                bytes: 11,
                limit: 10
            })
        );
    }

    #[test]
    fn the_build_remainder_trips_before_the_evaluation_limit() {
        let limits = Limits {
            step: 10,
            alloc: 10,
            build_step: 12,
        };
        let mut b = BuildMeter::new(&limits);
        b.charge("first", 9);
        let mut m = Meter::new(&limits, b.remaining());
        for _ in 0..3 {
            m.step().expect("three steps remain in the build");
        }
        assert!(matches!(m.step(), Err(Exceeded::Build { .. })));
        b.charge("second", m.steps);
        assert_eq!(b.most_expensive(), Some(("first".to_string(), 9)));
    }
}
