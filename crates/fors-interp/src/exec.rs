//! The dispatch loop (design §5.1-§5.4).
//!
//! Executes the F1 FMIR subset over [`Slot`](crate::value::Slot)s. Frames
//! live in one reusable stack arena; calls push a window, returns pop it.
//! No per-value heap allocation exists in the loop.
//!
//! Aggregates (design §5.1) live in cell tables: field-granular `Vec<Slot>`
//! cells, NOT bytes. Byte-exact layout needs D12 ([HOLE-6]: no chapter
//! defines the layout algorithm), so F1 models a struct value as its fields
//! in order — field reads return exactly the stored values, which is all
//! the F1 gate needs. `Str` values are handles into a byte table fed by
//! [`Program`](crate::program::Program)'s side table.
//!
//! Traps (design §5.3) abort the whole run deterministically: evaluation
//! stops at the first `trap` terminator or trapping op, and [`Outcome`]
//! records the kind. Anything the F1 subset cannot execute (an opcode
//! outside it, a dangling operand, an unknown intrinsic) is
//! [`InterpError`] — an interpreter diagnostic, never a program trap and
//! never a panic.

use fors_fir::ty::TyStore;
use fors_fir::ty::{PrimKind, TyTag};
use fors_fmir::ids::{BlockId, ValId};
use fors_fmir::inst::{Callee, InstRow};
use fors_fmir::op::{Op, TrapKind};
use fors_fmir::value::ValDef;

use crate::arith::{FloatKind, IntKind, NumKind};
use crate::program::Program;
use crate::value::Slot;

/// How the process ended.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Exit {
    /// Returned from the entry function.
    Return,
    /// An error left the entry function by a `raise` terminator — ch02 R17's
    /// error exit, status 1. F4 needs this to have an ERROR EXIT at all
    /// (ch01 R23b: `errdefer` runs on error exits and never on normal ones);
    /// `render`'s `error: ` line and `?`/`try_br` stay **F3's**, so the slot
    /// the error was moved into is carried here and nothing formats it.
    Raise,
    /// A program trap: one of ch02 R15's closed eight.
    Trap(TrapKind),
    /// A `ub:` report (design §5.2): the interpreter found something a
    /// compiled program would get silently wrong. **Not** a trap (ch02 R15's
    /// kind list is closed at eight, E4) — status
    /// [`crate::ub::UB_EXIT_STATUS`], and the full record is
    /// [`Outcome::ub`].
    Ub(crate::ub::UbClass),
}

/// One run's observable behaviour (design §7.1's `OracleRecord` restricted
/// to F1+F2: exit, exact stdout bytes, and whether `Stdout` ended the run
/// latched (ch10 R39/R40) — the exit-status table's F2 input (§5.3, §5.4,
/// ch10 R40(d)), computed over this by [`crate::shim::entry_exit`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Outcome {
    pub exit: Exit,
    pub stdout: Vec<u8>,
    /// Whether `Stdout` carried a latched error at the point `main`
    /// returned (ch10 R39): set when a `write_line` through
    /// [`crate::shim::HostEnv::stdout_fd`] failed (a closed pipe) instead
    /// of appending bytes. Meaningless when `exit` is a trap (§5.3: the
    /// trap path never reaches the entry shim's flush at all).
    pub stdout_latched: bool,
    /// The `(line, col)` the trap or `ub:` report points at — what design
    /// §7.2a's `trap: <kind> at <file>:<L>:<C>` line needs. `None` on a clean
    /// return.
    pub site: Option<(u32, u32)>,
    /// The machine-readable `ub:` record (design §5.2), `Some` exactly when
    /// `exit` is [`Exit::Ub`].
    pub ub: Option<crate::ub::UbReport>,
    /// The opt-in backtrace (owner **Q7**): populated ONLY when
    /// `FORS_BACKTRACE=1` was set for this process, and **never** part of the
    /// oracle record — see [`Outcome::oracle_record`] and design §7.2a's
    /// "a backtrace on the trap path is illegal for any program in the
    /// differential corpus".
    pub backtrace: Vec<crate::trap::BacktraceFrame>,
}

impl Outcome {
    /// What design §7.1 compares: the exit, the exact `Stdout` bytes and the
    /// latch. The site, the `ub:` record and the Q7 backtrace are diagnostic
    /// payload and are deliberately OUTSIDE this projection, which is how
    /// §7.2a's "a backtrace ... is never part of the oracle record" is kept
    /// true by construction rather than by a comment.
    pub fn oracle_record(&self) -> (Exit, &[u8], bool) {
        (self.exit, &self.stdout, self.stdout_latched)
    }
}

/// A clean interpreter diagnostic: a malformed program, an unimplemented
/// F1-external opcode, or resource exhaustion. Never a trap, never a panic.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum InterpError {
    /// No function with the entry name exists.
    NoEntry(String),
    /// A call names a declaration key the program does not contain.
    UnknownCallee(u32),
    /// An opcode outside the F1 subset (discriminant for grepability).
    UnsupportedOp(u32),
    /// An operand names a value the pool does not contain.
    DanglingOperand { inst: u32, slot: u32 },
    /// A block terminator jumps to a block the pool does not contain.
    DanglingBlock(u32),
    /// An `intrinsic` callee outside the closed table.
    UnknownIntrinsic(String),
    /// A `const_str` with no bytes in the side table, or a `Str` handle
    /// (an intrinsic's receiver) outside the machine's byte table.
    MissingString(u32),
    /// A value of unexpected type reached an op (lowering bug, not a trap).
    TypeMismatch(String),
    /// An exit edge is internally inconsistent in a way `verify()` rejects
    /// and the interpreter must not paper over: an `errdefer` body on a
    /// NORMAL edge (ch01 R23b), a pending `DeferId` outside the pool, or a
    /// deferred body that ran off the end of its own sub-CFG. A compiler
    /// bug, never a trap and never silently skipped.
    MalformedExitEdge(String),
    /// A `raise` left a NON-entry frame and no `try_br` in the caller took
    /// it. Propagating an error into a caller is `?`/`try_br`'s job, which
    /// is F3's (design §3.6); until then the condition is REPORTED rather
    /// than settled as if `main` had raised — which would skip the caller's
    /// own pending bodies (ch01 R23a) and misreport ch02 R17's exit.
    UnhandledRaise(String),
    /// A quantity the interpreter's own representation cannot carry: an
    /// arena offset past the `u32` design §3.7's `RefVal` packs. Not a trap
    /// (ch02 R15's eight contain no such kind) and not silent truncation.
    Unrepresentable(String),
    /// Exceeded the runaway guard. Run mode has no step budget (budgets are
    /// F9's comptime rule); this is a fixed cap far above any gate test,
    /// existing only so a bad loop reports instead of hanging the harness.
    StepBudget,
    /// Call-depth guard (same rationale as `StepBudget`).
    StackOverflow,
}

impl std::fmt::Display for InterpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpError::NoEntry(n) => write!(f, "no entry function `{n}`"),
            InterpError::UnknownCallee(k) => write!(f, "call to unknown declaration key {k}"),
            InterpError::UnsupportedOp(d) => write!(f, "opcode {d} is outside the F1 subset"),
            InterpError::DanglingOperand { inst, slot } => {
                write!(f, "instruction {inst} names missing value {slot}")
            }
            InterpError::DanglingBlock(b) => write!(f, "jump to missing block {b}"),
            InterpError::UnknownIntrinsic(n) => write!(f, "intrinsic `{n}` is not in the F1 table"),
            InterpError::MissingString(c) => write!(f, "const_str {c} has no bytes in the program"),
            InterpError::TypeMismatch(m) => write!(f, "type mismatch: {m}"),
            InterpError::MalformedExitEdge(m) => write!(f, "malformed exit edge: {m}"),
            InterpError::UnhandledRaise(func) => write!(
                f,
                "`{func}` raised into a caller with no `try_br`; error propagation into a \
                 caller is F3's (design §3.6)"
            ),
            InterpError::Unrepresentable(m) => write!(f, "unrepresentable: {m}"),
            InterpError::StepBudget => write!(f, "step budget exceeded"),
            InterpError::StackOverflow => write!(f, "call stack overflow"),
        }
    }
}

impl std::error::Error for InterpError {}

/// A fault inside one instruction: a program trap, a `ub:` report, or a
/// malformed-program diagnostic. `?` on `InterpError` lifts into the
/// diagnostic side; trapping arithmetic raises the trap side; design §5.2's
/// detection list raises the `ub:` side, which is NEVER downgraded to either
/// of the other two (E4).
enum Fault {
    Trap(TrapKind),
    Ub(crate::ub::UbReport),
    Error(InterpError),
}

impl From<InterpError> for Fault {
    fn from(e: InterpError) -> Fault {
        Fault::Error(e)
    }
}

/// Steps before [`InterpError::StepBudget`]. Far above any gate test (the
/// largest corpus test, `reduce-n257`-shaped, is ~10⁴ steps); only a
/// runaway loop trips it.
const STEP_BUDGET: u64 = 100_000_000;
/// Frames before [`InterpError::StackOverflow`].
const MAX_FRAMES: usize = 1024;

/// The F1 closed intrinsic table (design §5.8, mechanism 2). Until std
/// exists with Fors-written `write_*` bodies over `@fd_write`, lowering
/// maps the `write_line` method to `stdout_write_line`, which appends one
/// line to the in-memory stdout. No other host effect exists in F1.
const INTRINSIC_STDOUT_WRITE_LINE: &str = "stdout_write_line";
/// F7's twin stand-in (same §5.8 mechanism-2 note above): `write_uint` has
/// no trailing newline (ch10 R39's "base 10, no locale"), so it cannot
/// reuse `stdout_write_line`'s intrinsic.
const INTRINSIC_STDOUT_WRITE_UINT: &str = "stdout_write_uint";
/// F7's §5.8 "byte length"/"byte at" primitives for `Str` (ch10 R26:
/// indexing is by byte). `Str.len`/`Str.at`'s real Fors bodies
/// (`std/mem/text.fors`) bottom out in these.
const INTRINSIC_STR_BYTE_LEN: &str = "str_byte_len";
const INTRINSIC_STR_BYTE_AT: &str = "str_byte_at";
/// F7's byte-slice primitive: `Str.slice`'s materialisation of
/// `self[start ..< end]` AFTER its own boundary check (the `not_a_boundary`
/// raise is Fors code in `std/mem/text.fors`; this only copies bytes).
const INTRINSIC_STR_BYTE_SLICE: &str = "str_byte_slice";

/// `seq_len(seq)`: the element count of an `Array`/`Slice`-shaped value.
/// ch10 Rule 42's `len` builtin and the bound of every `for` over a
/// sequence (`fors-lower::emit_seq_len`). FMIR has no `len` opcode — design
/// §3.10's 71 do not include one, because a real `Slice` is a `{ptr, len}`
/// pair whose length is a `field` read — so until F7's real `Slice`
/// representation lands the descriptor's own window answers it.
const INTRINSIC_SEQ_LEN: &str = "seq_len";

/// The bytes a `Str` handle names in the machine's byte table. A handle
/// outside the table is a lowering bug (an intrinsic reached with a
/// non-`Str` receiver), reported as [`InterpError::MissingString`] — never
/// an empty string or a zero length.
fn str_bytes<'m>(m: &'m Machine<'_>, handle: Slot) -> Result<&'m [u8], Fault> {
    m.strs
        .get(handle.bits as usize)
        .map(|b| b.as_slice())
        .ok_or_else(|| InterpError::MissingString(handle.bits as u32).into())
}

/// Aggregate cells: one field-granular allocation (see the module docs for
/// why cells, not bytes, in F1).
///
/// `kind` tells an AGGREGATE's own cells from a `Slice` DESCRIPTOR's three
/// bookkeeping cells (`slice_range`'s `{base, start, len}`). Without it the
/// two are indistinguishable — a three-element `Array[T, 3]` and a slice
/// descriptor are both "a cell with three slots" — and `index` would read a
/// descriptor's `start` as if it were element 1.
#[derive(Clone, Debug, Default)]
struct Cells {
    slots: Vec<Slot>,
    kind: CellKind,
}

/// What a [`Cells`] row holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
enum CellKind {
    /// A struct, tuple, enum payload or array: one slot per component.
    #[default]
    Agg,
    /// `slice_range`'s descriptor: `{base cell handle, start, len}`.
    Slice,
}

impl Cells {
    fn agg(slots: Vec<Slot>) -> Cells {
        Cells {
            slots,
            kind: CellKind::Agg,
        }
    }
}

/// Where a sequence VALUE's elements live: `(cell handle, start, len)`. An
/// aggregate is its own elements; a `Slice` descriptor names another cell
/// plus a window into it. The one resolver `index`, a `Seg::Index` place and
/// `seq_len` all share, so the four never disagree about what element `i` is.
fn seq_window(m: &Machine<'_>, v: Slot) -> Result<(usize, u64, u64), InterpError> {
    let cell = m
        .cells
        .get(v.bits as usize)
        .ok_or_else(|| InterpError::TypeMismatch("value is not a sequence".into()))?;
    match cell.kind {
        CellKind::Agg => Ok((v.bits as usize, 0, cell.slots.len() as u64)),
        CellKind::Slice => {
            let [base, start, len] = cell.slots.as_slice() else {
                return Err(InterpError::TypeMismatch(
                    "a slice descriptor must have exactly three cells".into(),
                ));
            };
            let base_len = m
                .cells
                .get(base.bits as usize)
                .map(|c| c.slots.len() as u64)
                .ok_or_else(|| {
                    InterpError::TypeMismatch("a slice descriptor's base is not a cell".into())
                })?;
            if start.bits.saturating_add(len.bits) > base_len {
                return Err(InterpError::TypeMismatch(
                    "a slice descriptor reaches past its base".into(),
                ));
            }
            Ok((base.bits as usize, start.bits, len.bits))
        }
    }
}

/// Which memory range a borrow stack belongs to (design §5.2).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum BorrowKey {
    /// A frame-local root slot: `&x` on a `let` binding allocates nothing
    /// but still has provenance and exclusivity.
    Root {
        frame: u32,
        root: u32,
    },
    Alloc(u32),
}

/// A running machine: frames, cell tables, string bytes, captured stdout,
/// and (F6) the allocation, arena, provenance and borrow tables.
struct Machine<'a> {
    prog: &'a Program,
    tys: &'a TyStore,
    frames: Vec<Frame>,
    /// `pending[i]`: where frame `i`'s `ret` value goes (`None` for the
    /// entry frame). Parallel to `frames`.
    pending: Vec<Option<ValId>>,
    cells: Vec<Cells>,
    strs: Vec<Vec<u8>>,
    stdout: Vec<u8>,
    stdout_latched: bool,
    host: crate::shim::HostEnv,
    steps: u64,
    /// design §5.1's allocation objects. Index 0 is a placeholder so that
    /// [`crate::mem::PROV_NONE`] names no real row.
    allocs: Vec<crate::mem::Alloc>,
    /// design §3.7's live arena values, indexed by `ArenaId`.
    arenas: Vec<crate::mem::ArenaVal>,
    /// The `with arena` region each arena was entered by, parallel to
    /// `arenas`: `region_exit` retires the newest live arena of ITS region,
    /// not whichever arena was created last — with nested regions those
    /// differ, and retiring the wrong one leaves the outer arena's `Ref`s
    /// dereferenceable after their block has ended (ch01 R15, R17).
    arena_region: Vec<fors_fmir::ids::RegionId>,
    /// `Slot.prov -> ProvRow`. Row 0 is the `PROV_NONE` placeholder.
    provs: Vec<crate::mem::ProvRow>,
    /// One borrow stack per allocation object and per frame-local root
    /// (design §5.2, E14).
    borrows: std::collections::HashMap<BorrowKey, crate::ub::BorrowStack>,
    next_tag: u32,
    /// The next frame activation number (see [`Frame::serial`]).
    next_serial: u32,
}

/// One scope exit in progress: `type-checker.md` §13 I8b's four steps,
/// driven from the edge's own data (design §3.5, §3.8).
///
/// ch01 R23a licenses exactly this shape — "an implementation MAY emit one
/// copy and jump to it; the behaviour is the same" — so each pending body is
/// entered as a sub-CFG and ends at [`fors_fmir::scope::BODY_END`]. Bodies
/// may nest (R23c), hence a STACK of these per frame rather than one slot.
#[derive(Clone, Debug)]
struct ExitRun {
    /// The edge being executed.
    edge: fors_fmir::ids::ExitEdgeId,
    /// How many of the edge's pending bodies have been entered.
    done: u32,
    /// Where control goes once steps 2-4 are complete, or `BlockId::NONE`
    /// for a function exit.
    resume: BlockId,
    /// Step 1's already-moved result operand (ch01 R23a: evaluated and moved
    /// into the result BEFORE any body runs, so a body "can neither read nor
    /// change the result").
    result: Option<Slot>,
    /// Does the function exit by `raise` when this sequence finishes?
    raising: bool,
}

#[derive(Clone, Debug)]
struct Frame {
    /// Function index in `prog.fns`.
    func: usize,
    /// This activation's number, unique over the run. A frame INDEX is
    /// reused by the next call after a return, so a pointer into a local
    /// (`MemTarget::Root`) carries the serial too and is refused once the
    /// frame it names has returned (design §5.2, `ub: use-after-free`).
    serial: u32,
    /// `ValId.0 -> Slot`, sized to the value pool at call time.
    vals: Vec<Slot>,
    /// Local slots (`PlaceRow.root`): parameters in order, then `let`
    /// bindings. Grown on demand; a slot that was never `init`-ed reads
    /// as uninitialised.
    roots: Vec<Slot>,
    /// Current block and program counter (instruction index within the
    /// block's regular range).
    block: BlockId,
    pc: u32,
    /// The scope exits this frame is in the middle of (innermost last).
    exits: Vec<ExitRun>,
}

impl<'a> Machine<'a> {
    fn func(&self, fi: usize) -> &'a crate::program::ProgFn {
        &self.prog.fns[fi]
    }

    fn slot(&self, fr: usize, inst: u32, v: ValId) -> Result<Slot, InterpError> {
        self.frames[fr]
            .vals
            .get(v.0 as usize)
            .copied()
            .ok_or(InterpError::DanglingOperand { inst, slot: v.0 })
    }

    fn define(&mut self, fr: usize, v: ValId, s: Slot) {
        let vals = &mut self.frames[fr].vals;
        let i = v.0 as usize;
        if i >= vals.len() {
            vals.resize(i + 1, Slot::uninit());
        }
        vals[i] = s;
    }

    fn charge(&mut self) -> Result<(), InterpError> {
        self.steps += 1;
        if self.steps > STEP_BUDGET {
            return Err(InterpError::StepBudget);
        }
        Ok(())
    }

    /// The numeric kind of a value's type. Non-numeric types (`bool`,
    /// `Str`, `()`, aggregates) have none — an op asking for one is a
    /// lowering bug.
    fn num_kind(&self, ty: fors_fir::ty::TyId) -> Result<Option<NumKind>, InterpError> {
        let bare = self.tys.unqual(ty);
        match self.tys.tag(bare) {
            TyTag::Prim => {
                let p = PrimKind::from_u8(self.tys.a(bare) as u8)
                    .ok_or_else(|| InterpError::TypeMismatch("bad PrimKind".into()))?;
                if p == PrimKind::Bool || p == PrimKind::Str || p == PrimKind::RawPtr {
                    Ok(None)
                } else {
                    NumKind::from_prim(p)
                        .map(Some)
                        .ok_or_else(|| InterpError::TypeMismatch("non-numeric primitive".into()))
                }
            }
            _ => Ok(None),
        }
    }

    fn int_kind(&self, ty: fors_fir::ty::TyId) -> Result<IntKind, InterpError> {
        match self.num_kind(ty)? {
            Some(NumKind::Int(k)) => Ok(k),
            _ => Err(InterpError::TypeMismatch("expected integer type".into())),
        }
    }

    fn float_kind(&self, ty: fors_fir::ty::TyId) -> Result<FloatKind, InterpError> {
        match self.num_kind(ty)? {
            Some(NumKind::Float(k)) => Ok(k),
            _ => Err(InterpError::TypeMismatch("expected float type".into())),
        }
    }

    // -- F6: provenance, allocations, borrows -----------------------------

    fn fresh_tag(&mut self) -> u32 {
        self.next_tag += 1;
        self.next_tag
    }

    fn push_prov(&mut self, target: crate::mem::MemTarget, tag: u32) -> u32 {
        let id = self.provs.len() as u32;
        self.provs.push(crate::mem::ProvRow { target, tag });
        id
    }

    fn prov_of(&self, slot: Slot) -> Result<crate::mem::ProvRow, InterpError> {
        if slot.prov == crate::mem::PROV_NONE {
            return Err(InterpError::TypeMismatch(
                "expected a pointer, got a value with no provenance".into(),
            ));
        }
        self.provs
            .get(slot.prov as usize)
            .copied()
            .ok_or_else(|| InterpError::TypeMismatch("dangling provenance".into()))
    }

    /// The allocator identity in force at `block` — ch01 R18's brand. A block
    /// in no `with allocator` scope allocates from
    /// [`crate::mem::AllocatorId::AMBIENT`].
    fn allocator_at(&self, fr: usize, block: BlockId) -> crate::mem::AllocatorId {
        let decl = &self.func(self.frames[fr].func).decl;
        let Some(row) = decl.blocks.try_row(block) else {
            return crate::mem::AllocatorId::AMBIENT;
        };
        if row.scope.index() >= decl.scopes.len() {
            return crate::mem::AllocatorId::AMBIENT;
        }
        crate::mem::AllocatorId(decl.scopes.row(row.scope).brand.0)
    }

    /// The `(line, col)` of an instruction's site, for a trap or `ub:` line
    /// (design §7.2a). Site 0 is the fallback for FMIR with no real spans.
    fn site_of(&self, fr: usize, site: fors_fmir::ids::SiteId) -> (u32, u32) {
        let decl = &self.func(self.frames[fr].func).decl;
        decl.sites
            .try_row(site)
            .map(|r| (r.line, r.col))
            .unwrap_or((0, 0))
    }

    /// The opt-in Q7 backtrace, innermost frame first. Built ONLY when
    /// `FORS_BACKTRACE=1`: §7.2a keeps it out of the differential corpus, so
    /// an unset variable must not even pay for the `Vec`.
    fn backtrace(&self) -> Vec<crate::trap::BacktraceFrame> {
        if !crate::trap::backtrace_enabled() {
            return Vec::new();
        }
        self.frames
            .iter()
            .rev()
            .map(|f| {
                let decl = &self.prog.fns[f.func].decl;
                let (line, col) = decl
                    .blocks
                    .try_row(f.block)
                    .and_then(|b| decl.sites.try_row(b.term.site))
                    .map(|s| (s.line, s.col))
                    .unwrap_or((0, 0));
                crate::trap::BacktraceFrame {
                    func: self.prog.fns[f.func].name.clone(),
                    line,
                    col,
                }
            })
            .collect()
    }

    /// Applies `how` through `tag` to `key`'s borrow stack. A range with no
    /// stack yet is one nothing has borrowed, so the access is unrestricted.
    fn borrow_access(
        &mut self,
        key: BorrowKey,
        tag: u32,
        how: crate::ub::Access,
    ) -> Result<(), crate::ub::Violation> {
        match self.borrows.get_mut(&key) {
            Some(stack) => stack.access(tag, how),
            None => Ok(()),
        }
    }

    fn borrow_stack(&mut self, key: BorrowKey) -> &mut crate::ub::BorrowStack {
        self.borrows
            .entry(key)
            .or_insert_with(|| crate::ub::BorrowStack::rooted(ROOT_TAG))
    }
}

/// The tag a frame-local root slot's own stack is rooted at: the binding's
/// unrestricted access. `fresh_tag` starts above it, so no borrow shares it.
const ROOT_TAG: u32 = 0;

/// Builds a `ub:` fault (design §5.2). Every report names its CLASS and the
/// instruction that produced it; `inst == u32::MAX` is a terminator.
fn ub(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    class: crate::ub::UbClass,
    detail: impl Into<String>,
) -> Fault {
    Fault::Ub(crate::ub::UbReport::new(
        class,
        inst,
        m.site_of(fr, site),
        detail,
    ))
}

/// The interpreter environment: what a run needs beyond the program.
pub struct Env<'a> {
    pub tys: &'a TyStore,
}

/// Runs `prog.entry` to completion with the default host environment
/// (`Stdout` open): `Ok(Outcome)` for a returned or trapped run,
/// `Err(InterpError)` for a malformed program.
pub fn run(prog: &Program, tys: &TyStore) -> Result<Outcome, InterpError> {
    run_with_host(prog, tys, &crate::shim::HostEnv::default())
}

/// As [`run`], with an explicit [`crate::shim::HostEnv`] — the conformance
/// runner's hook for §7.2a's "stdout descriptor closed before `main`"
/// (`main-returns-latched-stdout-exit-2`,
/// `10-std/sigpipe-ignored-write-latches-run-error`): it hands over the
/// write end of a real pipe whose read end it closed.
pub fn run_with_host(
    prog: &Program,
    tys: &TyStore,
    host: &crate::shim::HostEnv,
) -> Result<Outcome, InterpError> {
    if prog.entry >= prog.fns.len() {
        return Err(InterpError::NoEntry(format!("entry {}", prog.entry)));
    }
    let mut m = Machine {
        prog,
        tys,
        frames: Vec::new(),
        pending: Vec::new(),
        cells: Vec::new(),
        strs: Vec::new(),
        stdout: Vec::new(),
        stdout_latched: false,
        host: *host,
        steps: 0,
        // Row 0 of each table is the `PROV_NONE` / "no allocation"
        // placeholder, so a zeroed `Slot.prov` can never name a real object.
        allocs: vec![crate::mem::Alloc::new(
            0,
            1,
            crate::mem::AllocKind::Static,
            0,
        )],
        arenas: Vec::new(),
        arena_region: Vec::new(),
        provs: vec![crate::mem::ProvRow {
            target: crate::mem::MemTarget::Alloc(crate::mem::AllocId(0)),
            tag: 0,
        }],
        borrows: std::collections::HashMap::new(),
        next_tag: 0,
        next_serial: 0,
    };
    call(prog.entry, None, Vec::new(), &mut m)?;
    loop {
        let fr = m.frames.len() - 1;
        match step_frame(fr, &mut m)? {
            FrameStep::Continue => {}
            FrameStep::Return(v) => {
                pop_frame(&mut m);
                let dest = m.pending.pop().unwrap_or(None);
                match m.frames.last() {
                    None => {
                        debug_assert!(dest.is_none());
                        return Ok(settle(&mut m, Exit::Return, None, None));
                    }
                    Some(_) => {
                        let caller = m.frames.len() - 1;
                        if let Some(d) = dest {
                            m.define(caller, d, v);
                        }
                    }
                }
            }
            FrameStep::Raise(err) => {
                // ch01 R23a: the operand was evaluated and moved into the
                // result BEFORE the first body ran, so by here it is a live,
                // initialised value — `render`ing it is F3's.
                debug_assert!(err.init && err.live);
                // ch02 R17's error exit. Only `main` raising is modelled
                // here: propagating an error INTO a caller is `try_br`'s
                // job, which is F3's (design §3.6) — so a raise out of any
                // OTHER frame is reported, not settled as if `main` had
                // raised (that would skip the caller's own pending bodies).
                if m.frames.len() > 1 {
                    let func = m.prog.fns[m.frames[fr].func].name.clone();
                    return Err(InterpError::UnhandledRaise(func));
                }
                let site = m
                    .frames
                    .last()
                    .and_then(|f| {
                        let decl = &m.prog.fns[f.func].decl;
                        decl.blocks.try_row(f.block).map(|b| b.term.site)
                    })
                    .map(|s| m.site_of(m.frames.len() - 1, s));
                return Ok(settle(&mut m, Exit::Raise, site, None));
            }
            FrameStep::Trap(kind, site) => {
                let site = Some(m.site_of(fr, site));
                return Ok(settle(&mut m, Exit::Trap(kind), site, None));
            }
            FrameStep::Ub(report) => {
                let exit = Exit::Ub(report.class);
                let site = Some(report.site);
                return Ok(settle(&mut m, exit, site, Some(report)));
            }
        }
    }
}

/// Packages the final [`Outcome`], capturing the Q7 backtrace while the
/// frames are still alive (and only when `FORS_BACKTRACE=1`).
fn settle(
    m: &mut Machine<'_>,
    exit: Exit,
    site: Option<(u32, u32)>,
    ub: Option<crate::ub::UbReport>,
) -> Outcome {
    let backtrace = match exit {
        Exit::Return => Vec::new(),
        _ => m.backtrace(),
    };
    Outcome {
        exit,
        stdout: std::mem::take(&mut m.stdout),
        stdout_latched: m.stdout_latched,
        site,
        ub,
        backtrace,
    }
}

enum FrameStep {
    Continue,
    Return(Slot),
    /// ch02 R17: the entry function left by `raise`. The slot is the error
    /// operand, already moved into the result by step 1 of the exit
    /// sequence; `render`ing it is F3's.
    Raise(Slot),
    Trap(TrapKind, fors_fmir::ids::SiteId),
    Ub(crate::ub::UbReport),
}

fn call(
    func: usize,
    dest: Option<ValId>,
    args: Vec<Slot>,
    m: &mut Machine<'_>,
) -> Result<(), InterpError> {
    if m.frames.len() >= MAX_FRAMES {
        return Err(InterpError::StackOverflow);
    }
    let decl = &m.func(func).decl;
    let nvals = decl.vals.len();
    let mut vals = vec![Slot::uninit(); nvals];
    // Bind arguments to parameters in order: params are the `ValDef::Param`
    // rows sorted by ordinal.
    let mut params: Vec<(u16, ValId)> = Vec::new();
    for (id, row) in decl.vals.all_rows() {
        if let ValDef::Param(o) = row.def() {
            params.push((o, id));
        }
    }
    params.sort();
    let mut roots: Vec<Slot> = Vec::new();
    for (i, (_, id)) in params.iter().enumerate() {
        let s = args.get(i).copied().unwrap_or_else(Slot::unit);
        vals[id.0 as usize] = s;
        // Parameters are roots `0..n` in order: the place side of a
        // parameter reads the same value its `ValDef::Param` row names.
        debug_assert_eq!(roots.len(), i);
        roots.push(s);
    }
    let entry = decl.entry;
    m.pending.push(dest);
    let serial = m.next_serial;
    m.next_serial += 1;
    m.frames.push(Frame {
        func,
        serial,
        vals,
        roots,
        block: entry,
        pc: 0,
        exits: Vec::new(),
    });
    Ok(())
}

/// Pops the innermost frame and the borrow stacks of its root slots: the
/// next call reuses the frame index, and a stack left behind would make a
/// fresh local start life with another activation's borrow history.
fn pop_frame(m: &mut Machine<'_>) {
    let fr = m.frames.len() - 1;
    m.frames.pop();
    m.borrows
        .retain(|k, _| !matches!(k, BorrowKey::Root { frame, .. } if *frame as usize == fr));
}

fn goto(m: &mut Machine<'_>, fr: usize, b: BlockId) -> Result<(), InterpError> {
    let decl = &m.func(m.frames[fr].func).decl;
    if decl.blocks.try_row(b).is_none() {
        return Err(InterpError::DanglingBlock(b.0));
    }
    m.frames[fr].block = b;
    m.frames[fr].pc = 0;
    Ok(())
}

fn step_frame(fr: usize, m: &mut Machine<'_>) -> Result<FrameStep, InterpError> {
    m.charge()?;
    let func = m.frames[fr].func;
    let block = m.frames[fr].block;
    let pc = m.frames[fr].pc;
    let decl = &m.func(func).decl;
    let row = decl
        .blocks
        .try_row(block)
        .ok_or(InterpError::DanglingBlock(block.0))?;
    if pc < row.inst_len {
        let inst_id = fors_fmir::ids::InstId(row.first_inst + pc);
        let inst = decl
            .insts
            .try_row(inst_id)
            .ok_or(InterpError::DanglingBlock(block.0))?;
        m.frames[fr].pc += 1;
        match exec_inst(fr, inst_id.0, inst, m) {
            Ok(()) => Ok(FrameStep::Continue),
            Err(Fault::Trap(kind)) => Ok(FrameStep::Trap(kind, inst.site)),
            Err(Fault::Ub(report)) => Ok(FrameStep::Ub(report)),
            Err(Fault::Error(e)) => Err(e),
        }
    } else {
        match exec_term(fr, block, row.term, m) {
            Ok(step) => Ok(step),
            Err(Fault::Trap(kind)) => Ok(FrameStep::Trap(kind, row.term.site)),
            Err(Fault::Ub(report)) => Ok(FrameStep::Ub(report)),
            Err(Fault::Error(e)) => Err(e),
        }
    }
}

fn val_operand(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    raw: u32,
) -> Result<Slot, Fault> {
    if raw == fors_fmir::op::NO_OPERAND {
        return Err(InterpError::TypeMismatch("missing operand".into()).into());
    }
    let v = ValId(raw);
    let s = m.slot(fr, inst, v)?;
    if !s.live {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UseAfterMove,
            format!("value %{raw} was moved out of before this use"),
        ));
    }
    if !s.init {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UninitRead,
            format!("value %{raw} is read before it is initialised"),
        ));
    }
    Ok(s)
}

/// The `ValId` a non-terminator instruction defines: the value whose `def`
/// names this instruction.
fn result_of(m: &Machine<'_>, fr: usize, inst: u32) -> Option<ValId> {
    let decl = &m.func(m.frames[fr].func).decl;
    decl.vals
        .all_rows()
        .find(|(_, r)| r.def() == ValDef::Inst(fors_fmir::ids::InstId(inst)))
        .map(|(id, _)| id)
}

#[allow(clippy::too_many_lines)]
fn exec_inst(fr: usize, inst: u32, inst_row: InstRow, m: &mut Machine<'_>) -> Result<(), Fault> {
    let op = inst_row.op;
    let dest = result_of(m, fr, inst);
    match op {
        Op::ConstInt | Op::ConstFloat => {
            // Lowering convention (`fors-lower::consts`): the 64-bit bit
            // pattern split across `a` (low) and `b` (high).
            let v = ((inst_row.b as u64) << 32) | (inst_row.a as u64);
            define(dest, m, fr, Slot::val(v));
        }
        Op::ConstBool => {
            define(dest, m, fr, Slot::val((inst_row.a != 0) as u64));
        }
        Op::ConstUnit => {
            define(dest, m, fr, Slot::unit());
        }
        Op::ConstStr => {
            let bytes = find_string(m, fr, inst_row.a)?.to_vec();
            let id = m.strs.len() as u64;
            m.strs.push(bytes);
            define(dest, m, fr, Slot::val(id));
        }
        Op::Add(mode)
        | Op::Sub(mode)
        | Op::Mul(mode)
        | Op::Div(mode)
        | Op::Rem(mode)
        | Op::Shl(mode)
        | Op::Shr(mode) => {
            let name = match op {
                Op::Add(_) => "add",
                Op::Sub(_) => "sub",
                Op::Mul(_) => "mul",
                Op::Div(_) => "div",
                Op::Rem(_) => "rem",
                Op::Shl(_) => "shl",
                _ => "shr",
            };
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.int_kind(ty)?;
            let r = crate::arith::int_binop(name, mode, a.bits, b.bits, k).map_err(Fault::Trap)?;
            unchecked_overflow_check(
                m,
                fr,
                inst,
                inst_row.site,
                mode,
                crate::arith::int_binop(name, fors_fmir::op::ArithMode::Trap, a.bits, b.bits, k),
                name,
            )?;
            define(dest, m, fr, Slot::val(r));
        }
        Op::Neg(mode) => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.int_kind(ty)?;
            let r = crate::arith::int_neg(mode, a.bits, k).map_err(Fault::Trap)?;
            unchecked_overflow_check(
                m,
                fr,
                inst,
                inst_row.site,
                mode,
                crate::arith::int_neg(fors_fmir::op::ArithMode::Trap, a.bits, k),
                "neg",
            )?;
            define(dest, m, fr, Slot::val(r));
        }
        Op::Fadd(_) | Op::Fsub(_) | Op::Fmul(_) | Op::Fdiv(_) | Op::Frem(_) => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.float_kind(ty)?;
            let af = k.from_bits(a.bits);
            let bf = k.from_bits(b.bits);
            let r = match op {
                Op::Fadd(_) => crate::arith::fadd(af, bf, k),
                Op::Fsub(_) => crate::arith::fsub(af, bf, k),
                Op::Fmul(_) => crate::arith::fmul(af, bf, k),
                Op::Fdiv(_) => crate::arith::fdiv(af, bf, k),
                _ => match k {
                    FloatKind::F32 => crate::arith::frem_f32(af as f32, bf as f32),
                    FloatKind::F64 => crate::arith::frem_f64(af, bf),
                },
            };
            define(dest, m, fr, Slot::val(r));
        }
        Op::Fneg(_) => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.float_kind(ty)?;
            let r = crate::arith::fneg(k.from_bits(a.bits), k);
            define(dest, m, fr, Slot::val(r));
        }
        Op::Icmp(pred) => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let r = match m.num_kind(ty)? {
                Some(NumKind::Int(k)) => crate::arith::icmp(a.bits, b.bits, k, pred),
                // A `bool` comparison is an 8-bit unsigned one.
                None if is_bool(m, ty) => crate::arith::icmp(a.bits, b.bits, IntKind::U8, pred),
                _ => {
                    return Err(InterpError::TypeMismatch("icmp on non-integer".into()).into());
                }
            };
            define(dest, m, fr, Slot::val(r as u64));
        }
        Op::Fcmp(pred) => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.float_kind(ty)?;
            let r = crate::arith::fcmp(k.from_bits(a.bits), k.from_bits(b.bits), pred);
            define(dest, m, fr, Slot::val(r as u64));
        }
        Op::And | Op::Or | Op::Xor => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let r = match op {
                Op::And => a.bits & b.bits,
                Op::Or => a.bits | b.bits,
                _ => a.bits ^ b.bits,
            };
            define(dest, m, fr, Slot::val(r));
        }
        Op::Not => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            // `!b` on a `bool` is logical; on an integer it is bitwise.
            let r = if is_bool(m, ty) {
                (a.bits == 0) as u64
            } else {
                !a.bits
            };
            define(dest, m, fr, Slot::val(r));
        }
        Op::ConvChecked | Op::ConvWrap | Op::ConvSat | Op::ConvTrunc => {
            let a = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let from_ty = val_ty(m, fr, inst, inst_row.a)?;
            let to_ty = result_ty(m, fr, inst, dest)?;
            let from = num_kind_of(m, from_ty)?;
            let to = num_kind_of(m, to_ty)?;
            let r = match op {
                Op::ConvChecked => {
                    crate::arith::conv_checked(a.bits, from, to).map_err(Fault::Trap)?
                }
                Op::ConvWrap => crate::arith::conv_wrap(a.bits, from, to),
                Op::ConvSat => crate::arith::conv_sat(a.bits, from, to),
                _ => crate::arith::conv_trunc(a.bits, from, to),
            };
            define(dest, m, fr, Slot::val(r));
        }
        Op::AggNew | Op::TupleNew => {
            let args = {
                let decl = &m.func(m.frames[fr].func).decl;
                decl.insts.args(inst_row.a..inst_row.b).to_vec()
            };
            let mut slots = Vec::new();
            for v in args {
                slots.push(m.slot(fr, inst, v)?);
            }
            let id = m.cells.len() as u64;
            m.cells.push(Cells::agg(slots));
            define(dest, m, fr, Slot::val(id));
        }
        Op::Field => {
            let base = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let field = m
                .cells
                .get(base.bits as usize)
                .ok_or_else(|| InterpError::TypeMismatch("field base is not an aggregate".into()))
                .and_then(|cell| {
                    cell.slots
                        .get(inst_row.b as usize)
                        .copied()
                        .ok_or_else(|| InterpError::TypeMismatch("field index out of range".into()))
                })?;
            define(dest, m, fr, field);
        }
        Op::SliceRange => {
            // F5's `Slice[T]` stand-in (see `slice_parts`). `base` is the
            // aggregate the elements live in; the result is a descriptor,
            // not a copy, so the slice keeps aliasing its source exactly
            // as a real slice does.
            let base = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let lo = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let hi = val_operand(m, fr, inst, inst_row.site, inst_row.c)?;
            // Re-slicing a slice is ch03 R24's own composition: the new
            // window is relative to the base's elements, not to the
            // descriptor's three cells, so the bounds are checked against
            // the window `base` already names.
            let (cell, start, base_len) = seq_window(m, base)?;
            if lo.bits > hi.bits || hi.bits > base_len {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            let id = m.cells.len() as u64;
            m.cells.push(Cells {
                slots: vec![
                    Slot::val(cell as u64),
                    Slot::val(start + lo.bits),
                    Slot::val(hi.bits - lo.bits),
                ],
                kind: CellKind::Slice,
            });
            define(dest, m, fr, Slot::val(id));
        }
        Op::Index => {
            // ch03 R24 / ch10 R23: `a[i]` is bounds-checked, and the check
            // is ch02 R15's `bounds` TRAP — never a wrap, never a clamp,
            // and never elided (there is no mode field on this opcode).
            let base = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let idx = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            let (cell, start, len) = seq_window(m, base)?;
            if idx.bits >= len {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            let s = m.cells[cell].slots[(start + idx.bits) as usize];
            define(dest, m, fr, s);
        }
        Op::ReduceTree => {
            // design §5.7: the interpreter executes §3.9's expansion
            // literally, with `B` and `L` READ FROM THE INSTRUCTION, never
            // from the host's vector width. The expansion itself is
            // `fors_fmir::reduce`'s — this arm only resolves the operands
            // and the `op`.
            let (op_sym, xs, identity, b, l) = {
                let decl = &m.func(m.frames[fr].func).decl;
                let red = decl.insts.reduces.get(inst_row.a as usize).ok_or_else(|| {
                    InterpError::TypeMismatch("reduce_tree names no reduce row".into())
                })?;
                let Callee::Intrinsic(sym) = red.op else {
                    return Err(InterpError::TypeMismatch(
                        "reduce_tree's op must be a named binary primitive".into(),
                    )
                    .into());
                };
                (sym.0, red.xs, red.identity, red.b, red.l)
            };
            let (base, start, n) = seq_window(m, m.slot(fr, inst, xs)?)?;
            if n == 0 {
                // ch03 R11a: trap unless an `identity:` was supplied.
                if identity.0 == fors_fmir::ids::ABSENT {
                    return Err(Fault::Trap(TrapKind::EmptyReduce));
                }
                let e = m.slot(fr, inst, identity)?;
                define(dest, m, fr, e);
                return Ok(());
            }
            let elems: Vec<Slot> = {
                let cell = m.cells.get(base).ok_or_else(|| {
                    InterpError::TypeMismatch("reduce_tree operand is not a slice".into())
                })?;
                cell.slots
                    .get(start as usize..(start + n) as usize)
                    .ok_or_else(|| {
                        InterpError::TypeMismatch("reduce_tree slice is out of range".into())
                    })?
                    .to_vec()
            };
            let kind = num_kind_of(m, inst_row.ty)?;
            let name = decl_intrinsic_name(m, fr, op_sym)?;
            let op = crate::reduce::ReduceOp::resolve(&name, kind)
                .ok_or_else(|| InterpError::UnknownIntrinsic(name.clone()))?;
            // One step per `op` application, so a huge `reduce` is charged
            // like the loop it is (design §6, E5).
            for _ in 0..fors_fmir::reduce::op_applications(n as u32) {
                m.charge()?;
            }
            let r = crate::reduce::run(&elems, b, l, op)
                .map_err(Fault::Trap)?
                .ok_or_else(|| {
                    InterpError::TypeMismatch("non-empty reduce yielded no value".into())
                })?;
            define(dest, m, fr, r);
        }
        Op::CallDirect => {
            let (key, args) = {
                let decl = &m.func(m.frames[fr].func).decl;
                let crow =
                    decl.insts.calls.get(inst_row.a as usize).ok_or_else(|| {
                        InterpError::TypeMismatch("call names no call row".into())
                    })?;
                let Callee::Direct(key) = crow.callee else {
                    return Err(InterpError::TypeMismatch("call_direct without key".into()).into());
                };
                let argv: Vec<Slot> = decl
                    .insts
                    .args(crow.args.clone())
                    .iter()
                    .map(|v| m.slot(fr, inst, *v))
                    .collect::<Result<Vec<Slot>, InterpError>>()?;
                (key, argv)
            };
            let target = m
                .prog
                .fns
                .iter()
                .position(|f| f.decl.decl == key)
                .ok_or(InterpError::UnknownCallee(key.0))?;
            call(target, dest, args, m)?;
        }
        Op::Intrinsic => {
            let (name, args) = {
                let decl = &m.func(m.frames[fr].func).decl;
                let crow = decl.insts.calls.get(inst_row.a as usize).ok_or_else(|| {
                    InterpError::TypeMismatch("intrinsic names no call row".into())
                })?;
                let Callee::Intrinsic(sym) = crow.callee else {
                    return Err(InterpError::TypeMismatch("intrinsic without symbol".into()).into());
                };
                let iname = decl_intrinsic_name(m, fr, sym.0)?;
                let argv: Vec<Slot> = decl
                    .insts
                    .args(crow.args.clone())
                    .iter()
                    .map(|v| m.slot(fr, inst, *v))
                    .collect::<Result<Vec<Slot>, InterpError>>()?;
                (iname, argv)
            };
            exec_intrinsic(fr, dest, &name, args, m)?;
        }
        Op::CopyFrom => {
            // F1 place read: conventions need I8's flow data (D6), so a copy
            // shares the current value (aggregates are reference-shared; see
            // `fors-lower`'s module docs).
            let s = read_place(m, fr, inst, inst_row.site, inst_row.a)?;
            define(dest, m, fr, s);
        }
        Op::MoveFrom => {
            // design §5.2's first row: `move_from` clears the source place's
            // `live` bit, so a later read is `ub: use-after-move` — "a
            // compiler bug if it reaches here: the checker's ch01 R4a(a)
            // should have caught it".
            let s = read_place(m, fr, inst, inst_row.site, inst_row.a)?;
            let (root, segs, _) = place_shape(m, fr, inst_row.a)?;
            if segs.is_empty()
                && let Some(slot) = m.frames[fr].roots.get_mut(root as usize)
            {
                *slot = slot.moved_out();
            }
            define(dest, m, fr, s);
        }
        Op::Borrow | Op::BorrowMut | Op::BorrowOut => {
            // design §3.3: these PRODUCE a pointer, they do not read. The
            // borrow stack is pushed here (E14's two item kinds) and the
            // result carries the new tag as its provenance.
            let (root, segs, _) = place_shape(m, fr, inst_row.a)?;
            if !segs.is_empty() {
                return Err(InterpError::TypeMismatch(
                    "a borrow of a projected place needs sub-range borrow stacks (F7/M2)".into(),
                )
                .into());
            }
            let key = BorrowKey::Root {
                frame: fr as u32,
                root,
            };
            let tag = m.fresh_tag();
            if op == Op::Borrow {
                m.borrow_stack(key).push_shared(tag);
            } else {
                m.borrow_stack(key).push_unique(tag);
            }
            if op == Op::BorrowOut {
                // `&out x` targets an UNINITIALISED slot (design §3.3): the
                // callee must write it, and a read before that write is
                // §5.2's "Uninitialised read (incl. through `&out`)".
                let roots = &mut m.frames[fr].roots;
                if (root as usize) >= roots.len() {
                    roots.resize(root as usize + 1, Slot::uninit());
                }
                roots[root as usize] = Slot::uninit();
            }
            let serial = m.frames[fr].serial;
            let prov = m.push_prov(
                crate::mem::MemTarget::Root {
                    frame: fr as u32,
                    serial,
                    root,
                },
                tag,
            );
            define(dest, m, fr, Slot::ptr(0, prov));
        }
        Op::Init => {
            let v = val_operand(m, fr, inst, inst_row.site, inst_row.b)?;
            write_place(m, fr, inst, inst_row.site, inst_row.a, v)?;
        }
        Op::Alloc => {
            // `@alloc` (ch01 R18). The allocator's IDENTITY is the brand of
            // the block's scope — `with allocator x: Alloc { ... }` is what
            // introduces one (R15) — so the allocation records who made it
            // and `free` can compare.
            let size = val_operand(m, fr, inst, inst_row.site, inst_row.a)?.bits as u32;
            let align = val_operand(m, fr, inst, inst_row.site, inst_row.b)?.bits as u32;
            let block = m.frames[fr].block;
            let owner = m.allocator_at(fr, block);
            let id = m.allocs.len() as u32;
            m.allocs.push(crate::mem::Alloc::new(
                size,
                align.max(1),
                crate::mem::AllocKind::Heap(owner),
                0,
            ));
            let tag = m.fresh_tag();
            m.borrows
                .insert(BorrowKey::Alloc(id), crate::ub::BorrowStack::rooted(tag));
            let prov = m.push_prov(crate::mem::MemTarget::Alloc(crate::mem::AllocId(id)), tag);
            define(dest, m, fr, Slot::ptr(0, prov));
        }
        Op::Free => {
            // design §5.2's two heap rows at once: freeing something already
            // freed is `ub: use-after-free`, and freeing with the WRONG
            // allocator is `ub: allocator-mismatch` (ch01 R18 makes the
            // *typed* case a compile error; this catches the erased case).
            let ptr = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let prov = m.prov_of(ptr)?;
            let crate::mem::MemTarget::Alloc(id) = prov.target else {
                return Err(ub(
                    m,
                    fr,
                    inst,
                    inst_row.site,
                    crate::ub::UbClass::AllocatorMismatch,
                    "`free` of a pointer that no allocator produced".to_string(),
                ));
            };
            check_alloc_live(m, fr, inst, inst_row.site, id.0)?;
            let block = m.frames[fr].block;
            let freeing = m.allocator_at(fr, block);
            let owner = m.allocs[id.0 as usize].kind;
            match owner {
                crate::mem::AllocKind::Heap(o) if o == freeing => {}
                _ => {
                    return Err(ub(
                        m,
                        fr,
                        inst,
                        inst_row.site,
                        crate::ub::UbClass::AllocatorMismatch,
                        format!(
                            "allocation {} was produced by {owner:?} but is freed by allocator \
                             brand {}",
                            id.0, freeing.0
                        ),
                    ));
                }
            }
            m.allocs[id.0 as usize].state = crate::mem::AllocState::Freed(inst_row.site);
            define(dest, m, fr, Slot::unit());
        }
        Op::RegionEnter => {
            // `with arena x: Arena[T] { ... }` (ch01 R15): the block's own
            // fresh brand becomes one live `ArenaVal` (R15a: no constructor,
            // at most one live value per brand per block instance).
            let region = fors_fmir::ids::RegionId(inst_row.a);
            let kind = {
                let decl = &m.func(m.frames[fr].func).decl;
                if region.index() >= decl.regions.len() {
                    None
                } else {
                    Some(decl.regions.row(region).kind)
                }
            };
            match kind {
                Some(fors_fmir::region::RegionKind::WithArena) => {
                    let arena = crate::mem::ArenaId(m.arenas.len() as u32);
                    let data = m.allocs.len() as u32;
                    m.allocs.push(crate::mem::Alloc::new(
                        0,
                        16,
                        crate::mem::AllocKind::Arena(arena),
                        0,
                    ));
                    let tag = m.fresh_tag();
                    m.borrows
                        .insert(BorrowKey::Alloc(data), crate::ub::BorrowStack::rooted(tag));
                    m.arenas.push(crate::mem::ArenaVal::new(
                        arena,
                        crate::mem::AllocId(data),
                        u64::MAX,
                    ));
                    m.arena_region.push(region);
                    let prov = m.push_prov(
                        crate::mem::MemTarget::Arena {
                            arena,
                            data: crate::mem::AllocId(data),
                        },
                        tag,
                    );
                    // The arena HANDLE carries no generation: ch01 R15a
                    // keeps it alive across its own `reset`s, and §3.7 puts
                    // the generation on the `Ref`, not on the arena value.
                    define(dest, m, fr, Slot::ptr(0, prov));
                }
                // M1 runs a `spawn`/`parallel` region inline, which IS the
                // serial elision (design §1.2).
                Some(_) => define(dest, m, fr, Slot::unit()),
                None => {
                    return Err(InterpError::TypeMismatch(
                        "region_enter names no region row".into(),
                    )
                    .into());
                }
            }
        }
        Op::RegionExit => {
            // Leaving a `with arena` block retires the arena: every `Ref`
            // minted inside it is now stale, which ch01 R17 makes a program
            // `trap arena-generation` on the next dereference.
            let region = fors_fmir::ids::RegionId(inst_row.a);
            let is_arena = {
                let decl = &m.func(m.frames[fr].func).decl;
                region.index() < decl.regions.len()
                    && decl.regions.row(region).kind == fors_fmir::region::RegionKind::WithArena
            };
            if is_arena {
                // The newest LIVE arena of THIS region (regions nest, so
                // `arenas.last()` may be an inner region's). None live is a
                // `region_exit` with no matching `region_enter`: malformed.
                let live = m.arenas.iter().zip(&m.arena_region).rposition(|(a, r)| {
                    *r == region
                        && m.allocs[a.data.0 as usize].state == crate::mem::AllocState::Live
                });
                let Some(i) = live else {
                    return Err(InterpError::TypeMismatch(format!(
                        "region_exit of arena region {} with no live arena entered by it",
                        region.0
                    ))
                    .into());
                };
                let data = m.arenas[i].data;
                m.allocs[data.0 as usize].state = crate::mem::AllocState::Reset(inst_row.site);
            }
            define(dest, m, fr, Slot::unit());
        }
        Op::ArenaAlloc => {
            let arena_slot = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let size = val_operand(m, fr, inst, inst_row.site, inst_row.b)?.bits as u32;
            let prov = m.prov_of(arena_slot)?;
            let crate::mem::MemTarget::Arena { arena, data } = prov.target else {
                return Err(
                    InterpError::TypeMismatch("arena_alloc on a non-arena value".into()).into(),
                );
            };
            check_arena_live(m, data.0)?;
            let a = m.arenas[arena.0 as usize];
            // design §3.7 packs the offset into a `u32`; an arena past that
            // is a representation limit, reported rather than truncated
            // (a wrapped `off` would alias an earlier allocation).
            let end = a.bump + u64::from(size);
            let Ok(end32) = u32::try_from(end) else {
                return Err(InterpError::Unrepresentable(format!(
                    "arena {} would reach offset {end}, past the u32 a `RefVal` offset holds",
                    arena.0
                ))
                .into());
            };
            let off = end32 - size;
            m.arenas[arena.0 as usize].bump = end;
            m.allocs[data.0 as usize].grow_to(end32);
            // Every `Ref` into one arena shares the arena's own borrow tag:
            // at this crate's whole-object granularity (see `ub.rs`'s
            // `BorrowStack` decision) two bump allocations are disjoint
            // SUB-RANGES of one object, and minting a unique tag per `Ref`
            // would make the second one pop the first.
            let tag = prov.tag;
            let prov = m.push_prov(crate::mem::MemTarget::Arena { arena, data }, tag);
            // design §3.7's `RefVal { arena, generation, off }`: the generation is
            // captured HERE, which is what a later `reset` invalidates.
            define(
                dest,
                m,
                fr,
                Slot::ptr(crate::mem::RefVal::pack(a.generation, off), prov),
            );
        }
        Op::ArenaDeref => {
            // ch01 R17: generation-checked in EVERY build mode. There is no
            // `may_elide` bit on this instruction and no representation in
            // which the check could be dropped (design §3.7).
            let r = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let d = resolve_deref(m, fr, inst, inst_row.site, r)?;
            let alloc = d
                .alloc
                .ok_or_else(|| InterpError::TypeMismatch("arena_deref on a local".into()))?;
            let prov = m.push_prov(
                crate::mem::MemTarget::Alloc(crate::mem::AllocId(alloc)),
                d.tag,
            );
            define(dest, m, fr, Slot::ptr(u64::from(d.off), prov));
        }
        Op::ArenaReset => {
            let arena_slot = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
            let prov = m.prov_of(arena_slot)?;
            let crate::mem::MemTarget::Arena { arena, data } = prov.target else {
                return Err(
                    InterpError::TypeMismatch("arena_reset on a non-arena value".into()).into(),
                );
            };
            check_arena_live(m, data.0)?;
            // [HOLE-2] / E9: the bump goes through `next_generation`, which
            // TRAPS at `u32::MAX` rather than wrapping onto a generation a
            // stale `Ref` still carries.
            m.arenas[arena.0 as usize].reset().map_err(Fault::Trap)?;
            m.allocs[data.0 as usize].forget();
            define(dest, m, fr, Slot::unit());
        }
        Op::CheckPre(policy) | Op::CheckPost(policy) | Op::CheckInv(policy) => {
            // Lowering never emits these in F1 (contracts are F2), but the
            // dispatch implements them: `Runtime` evaluates the condition,
            // `Off` skips it. A false condition is a program trap.
            let active = match policy {
                fors_fmir::op::Policy::Runtime => true,
                fors_fmir::op::Policy::Off => false,
            };
            if active {
                let c = val_operand(m, fr, inst, inst_row.site, inst_row.a)?;
                if c.bits == 0 {
                    return Err(Fault::Trap(TrapKind::Contract));
                }
            }
            define(dest, m, fr, Slot::unit());
        }
        _ => return Err(InterpError::UnsupportedOp(op.discriminant()).into()),
    }
    Ok(())
}

/// design §5.5: "`unchecked_*` is wrapping **plus** a Miri-mode
/// `ub: unchecked-overflow` diagnostic when the true result is out of range
/// (ch03 R4 puts it behind `@unsafe(invariant:)`, so violating the invariant
/// is exactly a UB report, not a trap)."
///
/// `trapping` is what the SAME operation would have answered in `Trap` mode;
/// only `TrapKind::Overflow` means "out of range" (a zero divisor and a
/// too-wide shift are different conditions, and ch03 R4's invariant is about
/// representability).
fn unchecked_overflow_check(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    mode: fors_fmir::op::ArithMode,
    trapping: Result<u64, TrapKind>,
    name: &str,
) -> Result<(), Fault> {
    if mode != fors_fmir::op::ArithMode::Unchecked {
        return Ok(());
    }
    if trapping == Err(TrapKind::Overflow) {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UncheckedOverflow,
            format!("`unchecked_{name}`'s true result is out of the type's range"),
        ));
    }
    Ok(())
}

fn define(dest: Option<ValId>, m: &mut Machine<'_>, fr: usize, s: Slot) {
    if let Some(v) = dest {
        m.define(fr, v, s);
    }
}

fn val_ty(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    raw: u32,
) -> Result<fors_fir::ty::TyId, InterpError> {
    let decl = &m.func(m.frames[fr].func).decl;
    decl.vals
        .try_row(ValId(raw))
        .map(|r| r.ty)
        .ok_or(InterpError::DanglingOperand { inst, slot: raw })
}

fn result_ty(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    dest: Option<ValId>,
) -> Result<fors_fir::ty::TyId, InterpError> {
    match dest {
        Some(v) => val_ty(m, fr, inst, v.0),
        None => Err(InterpError::TypeMismatch("typeless conversion".into())),
    }
}

fn is_bool(m: &Machine<'_>, ty: fors_fir::ty::TyId) -> bool {
    let bare = m.tys.unqual(ty);
    if m.tys.tag(bare) != TyTag::Prim {
        return false;
    }
    PrimKind::from_u8(m.tys.a(bare) as u8) == Some(PrimKind::Bool)
}

fn num_kind_of(m: &Machine<'_>, ty: fors_fir::ty::TyId) -> Result<NumKind, InterpError> {
    match m.num_kind(ty)? {
        Some(k) => Ok(k),
        None => Err(InterpError::TypeMismatch("expected numeric type".into())),
    }
}

fn find_string<'m>(m: &'m Machine<'_>, fr: usize, const_idx: u32) -> Result<&'m [u8], Fault> {
    let func = m.frames[fr].func;
    m.prog.fns[func]
        .strings
        .iter()
        .find(|(id, _)| *id == const_idx)
        .map(|(_, b)| b.as_slice())
        .ok_or_else(|| InterpError::MissingString(const_idx).into())
}

fn decl_intrinsic_name(m: &Machine<'_>, fr: usize, sym: u32) -> Result<String, InterpError> {
    let func = m.frames[fr].func;
    m.prog.fns[func]
        .intrinsics
        .iter()
        .find(|(id, _)| *id == sym)
        .map(|(_, n)| n.clone())
        .ok_or_else(|| InterpError::UnknownIntrinsic(format!("symbol {sym}")))
}

/// Resolves a `PlaceId` operand to its `(root, segs, ty)`. Bounds-checked: a
/// dangling place is a diagnostic, never a panic. The type is what a
/// `[Deref]` read or write needs to know how many bytes it touches.
fn place_shape(
    m: &Machine<'_>,
    fr: usize,
    raw: u32,
) -> Result<(u32, Vec<fors_fmir::place::Seg>, fors_fir::ty::TyId), InterpError> {
    let decl = &m.func(m.frames[fr].func).decl;
    if (raw as usize) >= decl.places.len() {
        return Err(InterpError::TypeMismatch("dangling place".into()));
    }
    let pid = fors_fmir::ids::PlaceId(raw);
    let row = decl.places.row(pid);
    Ok((row.root, decl.places.segs(pid).to_vec(), row.ty))
}

/// Reads a frame-local root slot, with design §5.2's two Miri bits checked
/// in order: a DEAD slot (moved out of, or dropped at a scope exit) is
/// `ub: use-after-move`; a live but UNINITIALISED one is `ub: uninit-read`.
fn root_slot(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    root: u32,
) -> Result<Slot, Fault> {
    // A root that was never declared reads exactly like one that was
    // declared and never written: uninitialised, and a clean report.
    let s = m.frames[fr]
        .roots
        .get(root as usize)
        .copied()
        .unwrap_or_else(Slot::uninit);
    if !s.live {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UseAfterMove,
            format!("local slot {root} was moved out of (or dropped) before this read"),
        ));
    }
    if !s.init {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UninitRead,
            format!("local slot {root} is read before it is initialised"),
        ));
    }
    Ok(s)
}

/// Resolves a `Seg::Index` segment's runtime index, bounds-checked against
/// `len` (ch02 R15's `bounds` trap — F2's `trap-bounds` gate, §5.8's
/// "minimal intrinsic-backed stub" for `Buffer`/`Slice`, real bodies F7's).
fn index_in_bounds(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    idx: ValId,
    len: usize,
) -> Result<usize, Fault> {
    let idx_slot = val_operand(m, fr, inst, site, idx.0)?;
    let i = idx_slot.bits as usize;
    if i >= len {
        return Err(Fault::Trap(TrapKind::Bounds));
    }
    Ok(i)
}

/// The byte width of a scalar type, for a read or write THROUGH a pointer
/// into an [`crate::mem::Alloc`] (design §5.1's byte-granular `init` map).
///
/// [decision: pointer traffic is scalar-only in F6. An aggregate read
/// through a pointer needs a byte LAYOUT, which is D12 / **[HOLE-6]** — no
/// chapter defines the algorithm yet (owner Q1). Every §5.2 detection the F6
/// gate names (`use-after-free`, `uninit-read` through `&out`,
/// `allocator-mismatch`, the arena generation trap) is reachable with scalar
/// traffic, so F6 detects them all without pre-empting Q1.]
fn scalar_width(m: &Machine<'_>, ty: fors_fir::ty::TyId) -> Result<u32, InterpError> {
    let bare = m.tys.unqual(ty);
    if m.tys.tag(bare) != TyTag::Prim {
        return Err(InterpError::TypeMismatch(
            "a non-scalar read through a pointer needs D12's layout ([HOLE-6])".into(),
        ));
    }
    let p = PrimKind::from_u8(m.tys.a(bare) as u8)
        .ok_or_else(|| InterpError::TypeMismatch("bad PrimKind".into()))?;
    Ok(match p {
        PrimKind::Bool | PrimKind::I8 | PrimKind::U8 => 1,
        PrimKind::I16 | PrimKind::U16 => 2,
        PrimKind::I32 | PrimKind::U32 | PrimKind::F32 => 4,
        // `isize`/`usize`/`rawptr` are "the target pointer" width (ch09 R3),
        // which comes from the explicit `Config`, never from the host.
        PrimKind::Isize | PrimKind::Usize | PrimKind::RawPtr => {
            u32::from(m.prog.config.ptr_bits) / 8
        }
        _ => 8,
    })
}

/// Everything a dereference needs: which object, at which offset, through
/// which borrow tag. Resolving it is where the arena generation check
/// (ch01 R17 — a program TRAP) and the freed-allocation check (design §5.2 —
/// a `ub:` report) both live.
struct Deref {
    key: BorrowKey,
    alloc: Option<u32>,
    off: u32,
    tag: u32,
}

fn resolve_deref(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    ptr: Slot,
) -> Result<Deref, Fault> {
    let prov = m.prov_of(ptr)?;
    match prov.target {
        crate::mem::MemTarget::Root {
            frame,
            serial,
            root,
        } => {
            // design §5.2's "use of a freed allocation", on a stack slot: the
            // frame this pointer names has returned (its index may already
            // hold another activation, hence the serial, not the index).
            let alive = m
                .frames
                .get(frame as usize)
                .is_some_and(|f| f.serial == serial);
            if !alive {
                return Err(ub(
                    m,
                    fr,
                    inst,
                    site,
                    crate::ub::UbClass::UseAfterFree,
                    format!(
                        "a pointer to local slot {root} of a frame that has returned \
                         (activation {serial})"
                    ),
                ));
            }
            Ok(Deref {
                key: BorrowKey::Root { frame, root },
                alloc: None,
                off: 0,
                tag: prov.tag,
            })
        }
        crate::mem::MemTarget::Alloc(id) => {
            check_alloc_live(m, fr, inst, site, id.0)?;
            Ok(Deref {
                key: BorrowKey::Alloc(id.0),
                alloc: Some(id.0),
                off: ptr.bits as u32,
                tag: prov.tag,
            })
        }
        crate::mem::MemTarget::Arena { arena, data } => {
            // ch01 R17: "every `Ref` dereference MUST be generation-checked
            // in every build mode, never elided by optimization level" — and
            // design §5.2 makes the mismatch a program `trap`, not a `ub:`.
            let (generation, off) = crate::mem::RefVal::unpack(ptr.bits);
            let live = m
                .arenas
                .get(arena.0 as usize)
                .ok_or_else(|| InterpError::TypeMismatch("dangling arena".into()))?;
            if live.generation != generation {
                return Err(Fault::Trap(TrapKind::ArenaGeneration));
            }
            if !matches!(
                m.allocs.get(data.0 as usize).map(|a| a.state),
                Some(crate::mem::AllocState::Live)
            ) {
                return Err(Fault::Trap(TrapKind::ArenaGeneration));
            }
            Ok(Deref {
                key: BorrowKey::Alloc(data.0),
                alloc: Some(data.0),
                off,
                tag: prov.tag,
            })
        }
    }
}

/// design §5.2: "Use of a freed or reset allocation -> `ub: use-after-free`
/// (heap)". The arena half is handled in [`resolve_deref`], where ch01 R17
/// makes it a trap instead.
fn check_alloc_live(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    id: u32,
) -> Result<(), Fault> {
    match m.allocs.get(id as usize).map(|a| a.state) {
        Some(crate::mem::AllocState::Live) => Ok(()),
        Some(crate::mem::AllocState::Freed(_)) => Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::UseAfterFree,
            format!("allocation {id} was freed before this access"),
        )),
        // `Reset` is set only by `region_exit` on an ARENA's backing object,
        // and §5.2's row sends the arena case to ch01 R17's program trap.
        Some(crate::mem::AllocState::Reset(_)) => Err(Fault::Trap(TrapKind::ArenaGeneration)),
        None => Err(InterpError::TypeMismatch("dangling allocation".into()).into()),
    }
}

/// The arena half of the same row: "Use of a freed or reset allocation ->
/// ... **`trap arena-generation`** (arena, because ch01 R17 makes it a
/// program trap)". An `arena_alloc`/`arena_reset` through a handle whose
/// `with arena` block has ended is such a use; [`resolve_deref`] gives a
/// stale `Ref` the same answer.
fn check_arena_live(m: &Machine<'_>, data: u32) -> Result<(), Fault> {
    match m.allocs.get(data as usize).map(|a| a.state) {
        Some(crate::mem::AllocState::Live) => Ok(()),
        Some(_) => Err(Fault::Trap(TrapKind::ArenaGeneration)),
        None => Err(InterpError::TypeMismatch("dangling arena allocation".into()).into()),
    }
}

/// Reads a place: `[]` is the local slot itself, `[Field(i)]` is one cell
/// of the aggregate the slot names, `[Index(v)]` is the same cell array
/// read at a RUNTIME index (bounds-checked), and `[Deref]` follows an
/// `Own`/`Ref` into an allocation object (design §3.3, §5.1). Deeper paths
/// are a lowering bug.
fn read_place(
    m: &mut Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    raw: u32,
) -> Result<Slot, Fault> {
    let (root, segs, ty) = place_shape(m, fr, raw)?;
    if let [fors_fmir::place::Seg::Deref] = segs.as_slice() {
        return read_through(m, fr, inst, site, root, ty);
    }
    let base = root_slot(m, fr, inst, site, root)?;
    match segs.as_slice() {
        [] => Ok(base),
        [fors_fmir::place::Seg::Field(i)] => {
            let cell = m.cells.get(base.bits as usize).ok_or_else(|| {
                InterpError::TypeMismatch("place base is not an aggregate".into())
            })?;
            cell.slots
                .get(*i as usize)
                .copied()
                .ok_or_else(|| InterpError::TypeMismatch("place field out of range".into()).into())
        }
        [fors_fmir::place::Seg::Index(idx)] => {
            let idx = *idx;
            let (cell, start, len) = seq_window(m, base)?;
            let i = index_in_bounds(m, fr, inst, site, idx, len as usize)?;
            Ok(m.cells[cell].slots[start as usize + i])
        }
        // `self.data[i]`: one field, then one element of it. The only
        // two-segment path F1 lowering builds (`fors-lower::
        // lower_index_assign`), and the shape `Buffer`/`Vec` bodies use.
        [
            fors_fmir::place::Seg::Field(f),
            fors_fmir::place::Seg::Index(idx),
        ] => {
            let (f, idx) = (*f, *idx);
            let seq = m
                .cells
                .get(base.bits as usize)
                .and_then(|c| c.slots.get(f as usize))
                .copied()
                .ok_or_else(|| InterpError::TypeMismatch("place field out of range".into()))?;
            let (cell, start, len) = seq_window(m, seq)?;
            let i = index_in_bounds(m, fr, inst, site, idx, len as usize)?;
            Ok(m.cells[cell].slots[start as usize + i])
        }
        _ => Err(InterpError::TypeMismatch("place path outside the F1/F2 shapes".into()).into()),
    }
}

/// `*p` where `p` is the root's pointer value: the borrow-stack access, the
/// liveness check and the byte-granular init check (design §5.1, §5.2).
fn read_through(
    m: &mut Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    root: u32,
    ty: fors_fir::ty::TyId,
) -> Result<Slot, Fault> {
    let ptr = root_slot(m, fr, inst, site, root)?;
    let d = resolve_deref(m, fr, inst, site, ptr)?;
    if m.borrow_access(d.key, d.tag, crate::ub::Access::Read)
        .is_err()
    {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::Aliasing,
            format!("a read through a borrow of local slot {root} that is no longer live"),
        ));
    }
    match d.alloc {
        // A pointer straight at a frame-local root: the value IS the slot.
        // `resolve_deref` has checked the frame is the live activation.
        None => {
            let crate::mem::MemTarget::Root { frame, root: r, .. } = m.prov_of(ptr)?.target else {
                unreachable!("`alloc == None` is exactly the Root target")
            };
            let s = m
                .frames
                .get(frame as usize)
                .and_then(|f| f.roots.get(r as usize))
                .copied()
                .unwrap_or_else(Slot::uninit);
            if !s.live {
                return Err(ub(
                    m,
                    fr,
                    inst,
                    site,
                    crate::ub::UbClass::UseAfterMove,
                    format!("a read through a pointer to local slot {r}, which was moved out of"),
                ));
            }
            if !s.init {
                // design §5.2's "Uninitialised read (incl. through `&out`)".
                return Err(ub(
                    m,
                    fr,
                    inst,
                    site,
                    crate::ub::UbClass::UninitRead,
                    format!("a read through a pointer to local slot {r}, which is uninitialised"),
                ));
            }
            Ok(s)
        }
        Some(id) => {
            let width = scalar_width(m, ty)?;
            let alloc = &m.allocs[id as usize];
            if d.off.saturating_add(width) > alloc.size() {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            if !alloc.init.all_set(d.off, width) {
                return Err(ub(
                    m,
                    fr,
                    inst,
                    site,
                    crate::ub::UbClass::UninitRead,
                    format!(
                        "a read of {width} bytes at offset {} of allocation {id}, which are \
                         uninitialised",
                        d.off
                    ),
                ));
            }
            let mut bits = 0u64;
            for i in 0..width {
                bits |= (alloc.bytes[(d.off + i) as usize] as u64) << (8 * i);
            }
            let prov = alloc
                .prov
                .get(&d.off)
                .copied()
                .unwrap_or(crate::mem::PROV_NONE);
            Ok(Slot::ptr(bits, prov))
        }
    }
}

/// Writes a place (same shapes as [`read_place`], plus `[Deref]`).
fn write_place(
    m: &mut Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    raw: u32,
    v: Slot,
) -> Result<(), Fault> {
    let (root, segs, ty) = place_shape(m, fr, raw)?;
    if !matches!(segs.as_slice(), [fors_fmir::place::Seg::Deref]) {
        // A write to the binding ITSELF (or, at this crate's whole-object
        // granularity, to one of its fields or elements) goes through the
        // root's own tag and pops every borrow above it (design §5.2: "only
        // a write or a new unique tag pops") — so an outstanding `let`
        // borrow of `x` is invalid once `x` is assigned. The root tag is
        // unrestricted, so this cannot fail; it only pops.
        let key = BorrowKey::Root {
            frame: fr as u32,
            root,
        };
        let _ = m.borrow_access(key, ROOT_TAG, crate::ub::Access::Write);
    }
    match segs.as_slice() {
        [] => {
            let roots = &mut m.frames[fr].roots;
            let i = root as usize;
            if i >= roots.len() {
                roots.resize(i + 1, Slot::uninit());
            }
            roots[i] = v;
            Ok(())
        }
        [fors_fmir::place::Seg::Deref] => write_through(m, fr, inst, site, root, ty, v),
        [fors_fmir::place::Seg::Field(i)] => {
            let base = root_slot(m, fr, inst, site, root)?;
            let cell = m.cells.get_mut(base.bits as usize).ok_or_else(|| {
                InterpError::TypeMismatch("place base is not an aggregate".into())
            })?;
            let slot = cell
                .slots
                .get_mut(*i as usize)
                .ok_or_else(|| InterpError::TypeMismatch("place field out of range".into()))?;
            *slot = v;
            Ok(())
        }
        [fors_fmir::place::Seg::Index(idx)] => {
            let idx = *idx;
            let base = root_slot(m, fr, inst, site, root)?;
            let (cell, start, len) = seq_window(m, base)?;
            let i = index_in_bounds(m, fr, inst, site, idx, len as usize)?;
            m.cells[cell].slots[start as usize + i] = v;
            Ok(())
        }
        // `self.data[i] = v`: see `read_place`'s matching arm.
        [
            fors_fmir::place::Seg::Field(f),
            fors_fmir::place::Seg::Index(idx),
        ] => {
            let (f, idx) = (*f, *idx);
            let base = root_slot(m, fr, inst, site, root)?;
            let seq = m
                .cells
                .get(base.bits as usize)
                .and_then(|c| c.slots.get(f as usize))
                .copied()
                .ok_or_else(|| InterpError::TypeMismatch("place field out of range".into()))?;
            let (cell, start, len) = seq_window(m, seq)?;
            let i = index_in_bounds(m, fr, inst, site, idx, len as usize)?;
            m.cells[cell].slots[start as usize + i] = v;
            Ok(())
        }
        _ => Err(InterpError::TypeMismatch("place path outside the F1/F2 shapes".into()).into()),
    }
}

/// `*p = v`: the write half of [`read_through`]. A write is what pops a
/// borrow stack (design §5.2), and it is what turns an `&out` target from
/// uninitialised into initialised.
fn write_through(
    m: &mut Machine<'_>,
    fr: usize,
    inst: u32,
    site: fors_fmir::ids::SiteId,
    root: u32,
    ty: fors_fir::ty::TyId,
    v: Slot,
) -> Result<(), Fault> {
    let ptr = root_slot(m, fr, inst, site, root)?;
    let d = resolve_deref(m, fr, inst, site, ptr)?;
    if m.borrow_access(d.key, d.tag, crate::ub::Access::Write)
        .is_err()
    {
        return Err(ub(
            m,
            fr,
            inst,
            site,
            crate::ub::UbClass::Aliasing,
            format!("a write through a borrow of local slot {root} that does not permit it"),
        ));
    }
    match d.alloc {
        None => {
            let crate::mem::MemTarget::Root { frame, root: r, .. } = m.prov_of(ptr)?.target else {
                unreachable!("`alloc == None` is exactly the Root target")
            };
            // `resolve_deref` has checked the frame is the live activation.
            let Some(f) = m.frames.get_mut(frame as usize) else {
                return Err(InterpError::TypeMismatch("dangling frame".into()).into());
            };
            let roots = &mut f.roots;
            let i = r as usize;
            if i >= roots.len() {
                roots.resize(i + 1, Slot::uninit());
            }
            roots[i] = v;
            Ok(())
        }
        Some(id) => {
            let width = scalar_width(m, ty)?;
            let alloc = &mut m.allocs[id as usize];
            if d.off.saturating_add(width) > alloc.size() {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            for i in 0..width {
                alloc.bytes[(d.off + i) as usize] = (v.bits >> (8 * i)) as u8;
            }
            alloc.init.set_range(d.off, width, true);
            if v.prov == crate::mem::PROV_NONE {
                alloc.prov.remove(&d.off);
            } else {
                alloc.prov.insert(d.off, v.prov);
            }
            Ok(())
        }
    }
}

fn exec_intrinsic(
    fr: usize,
    dest: Option<ValId>,
    name: &str,
    args: Vec<Slot>,
    m: &mut Machine<'_>,
) -> Result<(), Fault> {
    match name {
        INTRINSIC_STDOUT_WRITE_LINE => {
            // `stdout_write_line(receiver, text)`: the receiver is ignored
            // (the entry shim fabricates it); the text operand is a `Str`
            // handle into the machine's byte table. ch10 R39: TOTAL and
            // LATCHING — when the host gave `Stdout` a real descriptor
            // (`HostEnv::stdout_fd`, §7.2a's closed-pipe tests) the bytes
            // go through it first, and a failed write never traps and
            // never reaches the captured image: it sets the sticky flag
            // `entry_exit` reads (R40(d): status 2 on return).
            let text = args.get(1).copied().unwrap_or_else(Slot::unit);
            let mut bytes = str_bytes(m, text)?.to_vec();
            bytes.push(b'\n');
            let arrived = match m.host.stdout_fd {
                Some(fd) => crate::shim::host_write(fd, &bytes).is_ok(),
                None => true,
            };
            if arrived {
                m.stdout.extend_from_slice(&bytes);
            } else {
                m.stdout_latched = true;
            }
            define(dest, m, fr, Slot::unit());
            Ok(())
        }
        INTRINSIC_STDOUT_WRITE_UINT => {
            // `stdout_write_uint(receiver, v)`: base 10, no locale, no
            // trailing newline (ch10 R39) — same total/latching write
            // path as `stdout_write_line`, minus the `\n`.
            let v = args.get(1).copied().unwrap_or_else(Slot::unit).bits;
            let bytes = v.to_string().into_bytes();
            let arrived = match m.host.stdout_fd {
                Some(fd) => crate::shim::host_write(fd, &bytes).is_ok(),
                None => true,
            };
            if arrived {
                m.stdout.extend_from_slice(&bytes);
            } else {
                m.stdout_latched = true;
            }
            define(dest, m, fr, Slot::unit());
            Ok(())
        }
        INTRINSIC_STR_BYTE_LEN => {
            // `str_byte_len(self)`: the receiver's own byte count. `Str`
            // values are handles into the machine's byte table (§5.1
            // treats `Str` as an allocation object; F1's materialisation
            // keeps it in the separate pool `write_line` already reads).
            let recv = args.first().copied().unwrap_or_else(Slot::unit);
            let n = str_bytes(m, recv)?.len();
            define(dest, m, fr, Slot::val(n as u64));
            Ok(())
        }
        INTRINSIC_STR_BYTE_AT => {
            // `str_byte_at(self, i)`: ch10 R23/R26 — out of range is a
            // bug, trap `bounds`, same as `index` on a `Slice`/`Array`.
            let recv = args.first().copied().unwrap_or_else(Slot::unit);
            let i = args.get(1).copied().unwrap_or_else(Slot::unit).bits as usize;
            let Some(&b) = str_bytes(m, recv)?.get(i) else {
                return Err(Fault::Trap(TrapKind::Bounds));
            };
            define(dest, m, fr, Slot::val(b as u64));
            Ok(())
        }
        INTRINSIC_STR_BYTE_SLICE => {
            // `str_byte_slice(self, start, end)`: a fresh handle over the
            // byte range. `Str.slice`'s `pre start <= end and end <=
            // self.len()` (kind `contract`) runs before this is reached;
            // a range that still escapes it is a bug, trap `bounds`.
            let recv = args.first().copied().unwrap_or_else(Slot::unit);
            let start = args.get(1).copied().unwrap_or_else(Slot::unit).bits as usize;
            let end = args.get(2).copied().unwrap_or_else(Slot::unit).bits as usize;
            let bytes = str_bytes(m, recv)?;
            if start > end || end > bytes.len() {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            let out = bytes[start..end].to_vec();
            let id = m.strs.len() as u64;
            m.strs.push(out);
            define(dest, m, fr, Slot::val(id));
            Ok(())
        }
        INTRINSIC_SEQ_LEN => {
            // `seq_len(seq)`: see `INTRINSIC_SEQ_LEN`. Total — it reads a
            // window, touches no element, and cannot trap.
            let seq = args.first().copied().unwrap_or_else(Slot::unit);
            let (_, _, len) = seq_window(m, seq)?;
            define(dest, m, fr, Slot::val(len));
            Ok(())
        }
        other => Err(InterpError::UnknownIntrinsic(other.to_string()).into()),
    }
}

/// A terminator. Every control transfer out of a block first asks whether
/// this `(from, to)` pair is a SCOPE EXIT (`DeclFmir::exits`); if it is, the
/// four steps of `type-checker.md` §13 I8b run before the transfer.
///
/// `trap` is the one terminator that asks nothing: ch01 R23f, R22d and ch02
/// R7 make a trap *not an exit* — it has no successor, runs no deferred
/// body and discharges nothing. `verify()` rejects an exit edge on a
/// `trap`-terminated block, and this arm never looks for one.
fn exec_term(
    fr: usize,
    block: BlockId,
    term: InstRow,
    m: &mut Machine<'_>,
) -> Result<FrameStep, Fault> {
    match term.op {
        Op::Br => {
            let to = BlockId(term.a);
            // The jump BACK out of a deferred body (ch01 R23a's "emit one
            // copy and jump to it"): resume the exit sequence.
            if to == fors_fmir::scope::BODY_END {
                return advance_exit(fr, m);
            }
            begin_exit_or_goto(fr, block, to, None, false, m)
        }
        Op::CondBr => {
            let c = read_terminator_operand(m, fr, term.site, term.a)?;
            let to = BlockId(if c.bits != 0 { term.b } else { term.c });
            begin_exit_or_goto(fr, block, to, None, false, m)
        }
        Op::SwitchDiscr => {
            // design §3.10: `a` indexes `DeclFmir::switches`; the row
            // carries the scrutinee, the default edge and the arm table.
            // Arms are compared on the scrutinee's own BITS — `fors-lower`
            // narrows each pattern literal to the scrutinee's width, so a
            // negative `i32` pattern and the zero-extended slot agree.
            //
            // ch09 R55's arm-selection step budget is the CHECKER's
            // (type-checker.md §13 I7); at run time the arms are a linear
            // scan in source order, and the FIRST match wins, which is what
            // makes an earlier arm shadow a later duplicate exactly as the
            // surface reads.
            let (discr, default, arms) = {
                let decl = &m.func(m.frames[fr].func).decl;
                let sw = decl.insts.switches.get(term.a as usize).ok_or_else(|| {
                    InterpError::TypeMismatch("switch_discr names no switch row".into())
                })?;
                let arms: Vec<fors_fmir::inst::SwitchArm> = decl
                    .insts
                    .switch_arms
                    .get(sw.arms.start as usize..sw.arms.end as usize)
                    .ok_or_else(|| {
                        InterpError::TypeMismatch("switch_discr's arm range is out of range".into())
                    })?
                    .to_vec();
                (sw.discr, sw.default, arms)
            };
            let v = read_terminator_operand(m, fr, term.site, discr.0)?;
            let to = arms
                .iter()
                .find(|a| a.value as u64 == v.bits)
                .map(|a| a.target)
                .unwrap_or(default);
            begin_exit_or_goto(fr, block, to, None, false, m)
        }
        Op::Ret | Op::Raise => {
            // Step 1 (ch01 R23a): the operand is evaluated and moved into
            // the result BEFORE any body runs. Made structural here by
            // reading it at the terminator, ahead of `begin_exit_or_goto`.
            let v = if term.a == fors_fmir::op::NO_OPERAND {
                Slot::unit()
            } else {
                read_terminator_operand(m, fr, term.site, term.a)?
            };
            begin_exit_or_goto(fr, block, BlockId::NONE, Some(v), term.op == Op::Raise, m)
        }
        Op::Trap => {
            let kind = fors_fmir::op::TrapKind::from_u32(term.a)
                .ok_or_else(|| InterpError::TypeMismatch("bad trap kind".into()))?;
            Ok(FrameStep::Trap(kind, term.site))
        }
        Op::Unreachable => Err(InterpError::TypeMismatch("reached unreachable".into()).into()),
        _ => Err(InterpError::UnsupportedOp(term.op.discriminant()).into()),
    }
}

/// A terminator's `ValId` operand, with design §5.2's two Miri bits checked
/// (`inst == u32::MAX`: a terminator has no `InstPool` row).
fn read_terminator_operand(
    m: &Machine<'_>,
    fr: usize,
    site: fors_fmir::ids::SiteId,
    raw: u32,
) -> Result<Slot, Fault> {
    val_operand(m, fr, u32::MAX, site, raw)
}

/// Either begin this terminator's exit sequence, or transfer control
/// directly when the edge leaves no scope.
fn begin_exit_or_goto(
    fr: usize,
    from: BlockId,
    to: BlockId,
    result: Option<Slot>,
    raising: bool,
    m: &mut Machine<'_>,
) -> Result<FrameStep, Fault> {
    let edge = {
        let decl = &m.func(m.frames[fr].func).decl;
        decl.exits.find(from, to).map(|(id, _)| id)
    };
    match edge {
        Some(edge) => {
            m.frames[fr].exits.push(ExitRun {
                edge,
                done: 0,
                resume: to,
                result,
                raising,
            });
            advance_exit(fr, m)
        }
        None => finish_transfer(fr, to, result, raising, m),
    }
}

/// Runs the NEXT pending body of the innermost exit in progress, or — once
/// they are all done — steps 3 and 4 and the control transfer.
///
/// Step 2 (ch01 R23a, R23b): the bodies are taken from the edge's own
/// `pending` list, IN THE ORDER IT CARRIES. The interpreter never re-derives
/// that order (design §3.8: the verifier is what asserts the multiset); it
/// does refuse to run an `ErrDefer` body on a NORMAL edge, because that is a
/// compiler bug and §5.2's rule is that nothing is silently swallowed.
fn advance_exit(fr: usize, m: &mut Machine<'_>) -> Result<FrameStep, Fault> {
    let Some(run) = m.frames[fr].exits.last().cloned() else {
        return Err(InterpError::DanglingBlock(fors_fmir::ids::ABSENT).into());
    };
    let next_body = {
        let decl = &m.func(m.frames[fr].func).decl;
        let row = decl.exits.row(run.edge);
        let pending = decl.exits.pending(row.pending.clone());
        let next = pending.get(run.done as usize).copied();
        match next {
            None => None,
            Some(id) => {
                let rows = decl.defers.get(id.0..id.0 + 1);
                match rows.first() {
                    None => {
                        return Err(InterpError::MalformedExitEdge(format!(
                            "exit edge {} names defer row {}, which does not exist",
                            run.edge.0, id.0
                        ))
                        .into());
                    }
                    Some(d) => {
                        if d.kind == fors_fmir::scope::DeferKind::ErrDefer
                            && row.kind == fors_fmir::exit::ExitKind::Normal
                        {
                            return Err(InterpError::MalformedExitEdge(format!(
                                "exit edge {} is a normal exit but carries `errdefer` body {}; \
                                 ch01 R23b runs an `errdefer` only on an error exit",
                                run.edge.0, id.0
                            ))
                            .into());
                        }
                        Some(d.body)
                    }
                }
            }
        }
    };

    if let Some(body) = next_body {
        m.frames[fr].exits.last_mut().expect("just read").done += 1;
        goto(m, fr, body)?;
        return Ok(FrameStep::Continue);
    }

    // Step 3: the drops of the remaining non-linear bindings, AFTER the
    // bodies (R23d(a), R23d(f)). A drop in v0.1 runs no user code — ch01
    // R22c's `Droppable` has no impls — so its whole observable effect is
    // that the binding is no longer live (design §5.2's `live` bit).
    let (drops, discharges, leaving) = {
        let decl = &m.func(m.frames[fr].func).decl;
        let row = decl.exits.row(run.edge);
        (
            decl.exits.drops(row.drops.clone()).to_vec(),
            decl.exits.discharges(row.discharges.clone()).to_vec(),
            decl.exits.scopes(row.scopes.clone()).to_vec(),
        )
    };
    for place in &drops {
        let (root, _, _) = place_shape(m, fr, place.0)?;
        if let Some(slot) = m.frames[fr].roots.get_mut(root as usize) {
            *slot = slot.moved_out();
        }
    }

    // Step 4: ch01 R22h's check on what is left, AFTER the pending bodies
    // have been accounted for. design §3.5: the interpreter does not
    // re-derive this — it ASSERTS the discharge records the edge carries.
    if let Some(fault) = check_obligations(fr, m, &run, &leaving, &discharges) {
        return Err(fault);
    }

    m.frames[fr].exits.pop();
    finish_transfer(fr, run.resume, run.result, run.raising, m)
}

/// ch01 R22h as the interpreter sees it (design §3.5, §5.2): an obligation
/// of a scope being left with NO discharge record is `ub: linear-leak`, and
/// two records for one obligation is `ub: double-consume`. Neither is a
/// trap: ch02 R15's kind list is closed at eight and a compiler bug must not
/// look like a program trap (E4).
fn check_obligations(
    fr: usize,
    m: &Machine<'_>,
    run: &ExitRun,
    leaving: &[fors_fmir::ids::ScopeId],
    discharges: &[fors_fmir::exit::DischargeRow],
) -> Option<Fault> {
    // The report points at the EXIT's terminator (the edge's `from`), not at
    // the current block: once a deferred body has run, the current block is
    // the body's last one, and its `br BODY_END` is not where the leak is.
    let site = {
        let decl = &m.func(m.frames[fr].func).decl;
        let from = decl.exits.row(run.edge).from;
        decl.blocks
            .try_row(from)
            .map(|b| b.term.site)
            .unwrap_or(fors_fmir::ids::SiteId(0))
    };
    let mut obligations: Vec<fors_fmir::ids::PlaceId> = Vec::new();
    {
        let decl = &m.func(m.frames[fr].func).decl;
        for scope in leaving {
            if scope.index() >= decl.scopes.len() {
                continue;
            }
            obligations
                .extend_from_slice(decl.obligations.get(decl.scopes.row(*scope).obligations));
        }
    }
    for (i, d) in discharges.iter().enumerate() {
        if discharges[..i].iter().any(|e| e.place == d.place) {
            return Some(ub(
                m,
                fr,
                u32::MAX,
                site,
                crate::ub::UbClass::DoubleConsume,
                format!(
                    "exit edge {} discharges place {} twice",
                    run.edge.0, d.place.0
                ),
            ));
        }
    }
    for place in &obligations {
        if !discharges.iter().any(|d| d.place == *place) {
            return Some(ub(
                m,
                fr,
                u32::MAX,
                site,
                crate::ub::UbClass::LinearLeak,
                format!(
                    "place {} carries a linear obligation that is undischarged on exit edge {} \
                     (ch01 R22h); this is a compiler bug, not a program trap",
                    place.0, run.edge.0
                ),
            ));
        }
    }
    None
}

/// The control transfer itself, once steps 1-4 are done.
fn finish_transfer(
    fr: usize,
    to: BlockId,
    result: Option<Slot>,
    raising: bool,
    m: &mut Machine<'_>,
) -> Result<FrameStep, Fault> {
    if to == BlockId::NONE {
        let v = result.unwrap_or_else(Slot::unit);
        return Ok(if raising {
            FrameStep::Raise(v)
        } else {
            FrameStep::Return(v)
        });
    }
    goto(m, fr, to)?;
    Ok(FrameStep::Continue)
}
