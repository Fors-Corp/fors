//! `ub:` reports — design §5.2's detection list — and the borrow stack that
//! produces the aliasing row.
//!
//! The contract of §5.2 is "anything a compiled program would get silently
//! wrong, the interpreter NAMES". A `ub:` report is **not** a trap: ch02 R15
//! closes the trap-kind list at eight, and a compiler bug must not look like
//! a program trap (engineering call E4). It exits with status **70** and
//! carries a machine-readable record, so a differential runner can tell "the
//! program is wrong" from "the compiler is wrong".
//!
//! Every report names its detection CLASS and the INSTRUCTION that produced
//! it, plus the source site. Nothing here is ever downgraded to a trap and
//! nothing is swallowed: [`UbReport`] is a value the dispatch loop returns
//! all the way out, never a log line.

use fors_fmir::op::TrapKind;

/// design §5.2's "Reported as" column, in the order the table lists it, plus
/// §5.5's `unchecked_*` row. The strings are the report's own vocabulary and
/// are asserted against this list by test, so a tenth class cannot appear
/// without being named here.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UbClass {
    /// Use after move: the place's `live` bit, cleared by `move_from` (and by
    /// an exit edge's drops). A compiler bug if it reaches here — the
    /// checker's ch01 R4a(a) should have caught it.
    UseAfterMove,
    /// A linear obligation discharged twice on one exit edge.
    DoubleConsume,
    /// ch01 R22h: a scope exit with an undischarged obligation. design §3.5:
    /// "A leak reaching the interpreter is a **compiler bug**, and a compiler
    /// bug must not look like a program trap."
    LinearLeak,
    /// Uninitialised read, including through `&out`.
    UninitRead,
    /// `inout`/`sink`/`set` exclusivity violation (ch01 R7's two overlapping
    /// `let` accesses stay LEGAL — see [`BorrowStack`]).
    Aliasing,
    /// A `flags.SCOPED` value reaching an outer-scope place, a field, or
    /// `erase_to_dyn`.
    ///
    /// **The only row of design §5.2 with no detection wired in F6.** The
    /// detection reads `flags.SCOPED` and a value's `sources`, which
    /// `fors-lower` populates from checker increment I8b's **D9**
    /// (`scoped_sources`, `type-checker.md` §13 I8b) — and I8b does not
    /// exist ([HOLE-11]). Every hand-written fixture would therefore have to
    /// assert its own answer, which tests the fixture rather than the
    /// interpreter. The CLASS is defined here so the vocabulary is complete
    /// and closed; wiring it belongs with D9.
    ScopeEscape,
    /// Use of a freed heap allocation. (The arena case is a program trap,
    /// `arena-generation`, because ch01 R17 makes it one.)
    UseAfterFree,
    /// ch01 R18's erased case: `AllocKind::Heap(id)` versus the freeing
    /// allocator's identity.
    AllocatorMismatch,
    /// ch03 R4's `unchecked_*` behind `@unsafe(invariant:)`: violating the
    /// invariant is a UB report, not a trap (design §5.5).
    UncheckedOverflow,
}

impl UbClass {
    /// The closed class list, in variant order. `ub_class_names_are_closed`
    /// asserts the two stay in step.
    pub const CLASSES: [&'static str; 9] = [
        "use-after-move",
        "double-consume",
        "linear-leak",
        "uninit-read",
        "aliasing",
        "scope-escape",
        "use-after-free",
        "allocator-mismatch",
        "unchecked-overflow",
    ];

    pub const ALL: [UbClass; 9] = [
        UbClass::UseAfterMove,
        UbClass::DoubleConsume,
        UbClass::LinearLeak,
        UbClass::UninitRead,
        UbClass::Aliasing,
        UbClass::ScopeEscape,
        UbClass::UseAfterFree,
        UbClass::AllocatorMismatch,
        UbClass::UncheckedOverflow,
    ];

    pub const fn as_str(self) -> &'static str {
        Self::CLASSES[self.index()]
    }

    pub const fn index(self) -> usize {
        match self {
            UbClass::UseAfterMove => 0,
            UbClass::DoubleConsume => 1,
            UbClass::LinearLeak => 2,
            UbClass::UninitRead => 3,
            UbClass::Aliasing => 4,
            UbClass::ScopeEscape => 5,
            UbClass::UseAfterFree => 6,
            UbClass::AllocatorMismatch => 7,
            UbClass::UncheckedOverflow => 8,
        }
    }

    /// A `ub:` class is never one of ch02 R15's eight trap kinds — stated as
    /// code so the two vocabularies cannot drift into each other (E4).
    pub fn is_a_trap_kind(self) -> bool {
        TrapKind::KINDS.contains(&self.as_str())
    }
}

/// The interpreter's exit status for a `ub:` report (design §5.2).
pub const UB_EXIT_STATUS: i32 = 70;

/// One `ub:` report. `inst` is the instruction that produced it (`u32::MAX`
/// when the detection belongs to a terminator rather than to an `InstPool`
/// row), and `site` is its `(line, col)`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UbReport {
    pub class: UbClass,
    pub inst: u32,
    pub site: (u32, u32),
    pub detail: String,
}

impl UbReport {
    pub fn new(class: UbClass, inst: u32, site: (u32, u32), detail: impl Into<String>) -> UbReport {
        UbReport {
            class,
            inst,
            site,
            detail: detail.into(),
        }
    }

    /// The machine-readable one-line form, shaped like design §7.2a's trap
    /// line so a harness can split both the same way: the class, the site,
    /// the instruction, then the detail.
    pub fn line(&self, file: &str) -> String {
        let at = if self.inst == u32::MAX {
            "terminator".to_string()
        } else {
            format!("inst {}", self.inst)
        };
        format!(
            "ub: {} at {}:{}:{} ({}): {}\n",
            self.class.as_str(),
            file,
            self.site.0,
            self.site.1,
            at,
            self.detail
        )
    }
}

/// A borrow-stack rejection: the access is `ub: aliasing`. A unit struct
/// rather than a bare `()` so the signature says what the failure MEANS.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Violation;

/// What an access through a tag does to the stack.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Access {
    Read,
    Write,
}

/// One item of a borrow stack. Engineering call **E14**: two item kinds, not
/// one. `borrow_mut`/`borrow_out` push a [`BorrowItem::Unique`] tag;
/// `borrow` pushes into the topmost [`BorrowItem::SharedRo`] group.
///
/// ch01 R7 makes **two overlapping `let` accesses LEGAL** ("two read-only
/// accesses cannot race, and forbidding them would outlaw `f(&x, &x)`-shaped
/// calls that are plainly sound"), so a single-tag Stacked Borrows would
/// report UB on ACCEPTED code — and because a `ub:` report exits 70, that
/// would fail the corpus rather than merely annoy (design §5.2).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BorrowItem {
    Unique(u32),
    SharedRo(Vec<u32>),
}

impl BorrowItem {
    fn holds(&self, tag: u32) -> bool {
        match self {
            BorrowItem::Unique(t) => *t == tag,
            BorrowItem::SharedRo(group) => group.contains(&tag),
        }
    }
}

/// One memory range's borrow stack.
///
/// [decision: the granularity is one stack per allocation OBJECT (and one per
/// frame-local root slot), not per sub-range. design §5.2 says "a borrow
/// stack per allocation range"; sub-range splitting is what `split_at` and
/// SoA field identity need (ch05 R5's other alias sources), and those are
/// F7's and M2's. Whole-object granularity is strictly MORE conservative for
/// the negative rows and exactly as permissive for ch01 R7's two positive
/// rows, which are the ones a false report would break.]
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct BorrowStack {
    items: Vec<BorrowItem>,
}

impl BorrowStack {
    /// A fresh stack owning `tag`: the object's or root slot's own
    /// unrestricted access.
    pub fn rooted(tag: u32) -> BorrowStack {
        BorrowStack {
            items: vec![BorrowItem::Unique(tag)],
        }
    }

    pub fn depth(&self) -> u32 {
        self.items.len() as u32
    }

    /// `borrow_mut` / `borrow_out`: a new UNIQUE tag. "only a write or a new
    /// unique tag pops" (design §5.2) — the shared-read-only groups a new
    /// exclusive access sits above are invalidated by it, exactly as a write
    /// through the item below them would be.
    pub fn push_unique(&mut self, tag: u32) {
        while matches!(self.items.last(), Some(BorrowItem::SharedRo(_))) {
            self.items.pop();
        }
        self.items.push(BorrowItem::Unique(tag));
    }

    /// `borrow`: joins the topmost shared-read-only group, opening one if the
    /// top is not already a group. This is the clause that keeps `f(&x, &x)`
    /// legal.
    pub fn push_shared(&mut self, tag: u32) {
        match self.items.last_mut() {
            Some(BorrowItem::SharedRo(group)) => group.push(tag),
            _ => self.items.push(BorrowItem::SharedRo(vec![tag])),
        }
    }

    /// An access through `tag`. `Ok(())` is legal; `Err(Violation)` is
    /// `ub: aliasing` — the caller turns it into the report, since only it
    /// knows the instruction and the site.
    ///
    /// - a READ through any item of a live group is legal and pops nothing;
    /// - a WRITE through a unique item pops everything above it;
    /// - a WRITE through a shared-read-only item is a violation (the access
    ///   is `let`, the use is not);
    /// - a tag no longer on the stack is a violation.
    pub fn access(&mut self, tag: u32, how: Access) -> Result<(), Violation> {
        let Some(i) = self.items.iter().rposition(|it| it.holds(tag)) else {
            return Err(Violation);
        };
        match how {
            Access::Read => Ok(()),
            Access::Write => match self.items[i] {
                BorrowItem::Unique(_) => {
                    self.items.truncate(i + 1);
                    Ok(())
                }
                BorrowItem::SharedRo(_) => Err(Violation),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ub_class_names_are_closed_and_disjoint_from_trap_kinds() {
        assert_eq!(UbClass::ALL.len(), UbClass::CLASSES.len());
        for (i, c) in UbClass::ALL.iter().enumerate() {
            assert_eq!(c.index(), i);
            assert_eq!(c.as_str(), UbClass::CLASSES[i]);
            // E4: ch02 R15's kind list is closed at eight; a `ub:` class is
            // never one of them.
            assert!(
                !c.is_a_trap_kind(),
                "{} collides with a trap kind",
                c.as_str()
            );
        }
    }

    #[test]
    fn a_report_line_names_the_class_and_the_instruction() {
        let r = UbReport::new(UbClass::UseAfterFree, 7, (12, 5), "through a freed block");
        let line = r.line("main.fors");
        assert_eq!(
            line,
            "ub: use-after-free at main.fors:12:5 (inst 7): through a freed block\n"
        );
    }

    #[test]
    fn two_shared_borrows_both_stay_usable() {
        // ch01 R7 / E14's positive case, at the stack level.
        let mut s = BorrowStack::rooted(0);
        s.push_shared(1);
        s.push_shared(2);
        assert_eq!(s.depth(), 2, "both `let` borrows share one group");
        assert!(s.access(1, Access::Read).is_ok());
        assert!(s.access(2, Access::Read).is_ok());
        assert!(s.access(1, Access::Read).is_ok(), "a read pops nothing");
    }

    #[test]
    fn a_unique_borrow_invalidates_the_shared_group_below_it() {
        let mut s = BorrowStack::rooted(0);
        s.push_shared(1);
        s.push_unique(2);
        assert!(s.access(2, Access::Write).is_ok());
        assert!(
            s.access(1, Access::Read).is_err(),
            "a new unique tag pops the shared group"
        );
    }

    #[test]
    fn a_write_through_a_shared_borrow_is_a_violation() {
        let mut s = BorrowStack::rooted(0);
        s.push_shared(1);
        assert!(s.access(1, Access::Write).is_err());
    }

    #[test]
    fn a_write_through_the_root_pops_everything_above() {
        let mut s = BorrowStack::rooted(0);
        s.push_shared(1);
        s.push_unique(2);
        assert!(s.access(0, Access::Write).is_ok());
        assert!(s.access(2, Access::Read).is_err());
        assert!(s.access(0, Access::Read).is_ok());
    }
}
