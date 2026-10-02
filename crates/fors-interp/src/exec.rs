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
    /// Returned from the entry function (unit value; F1 has no `raises`
    /// edge yet — that is F3).
    Return,
    /// A program trap: one of ch02 R15's closed eight (only the arithmetic
    /// and conversion kinds are reachable in F1).
    Trap(TrapKind),
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
    /// A `const_str` with no bytes in the side table.
    MissingString(u32),
    /// A value of unexpected type reached an op (lowering bug, not a trap).
    TypeMismatch(String),
    /// Uninitialised slot read (would be `ub: uninit-read` in F6's Miri
    /// mode; F1 reports it as a diagnostic).
    UninitRead(u32),
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
            InterpError::UninitRead(v) => write!(f, "read of uninitialised value {v}"),
            InterpError::StepBudget => write!(f, "step budget exceeded"),
            InterpError::StackOverflow => write!(f, "call stack overflow"),
        }
    }
}

impl std::error::Error for InterpError {}

/// A fault inside one instruction: either a program trap (an outcome) or a
/// malformed-program diagnostic (an error). `?` on `InterpError` lifts into
/// the diagnostic side; trapping arithmetic raises the trap side.
enum Fault {
    Trap(TrapKind),
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

/// Aggregate cells: one field-granular allocation (see the module docs for
/// why cells, not bytes, in F1).
#[derive(Clone, Debug, Default)]
struct Cells {
    slots: Vec<Slot>,
}

/// A running machine: frames, cell tables, string bytes, captured stdout.
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
}

#[derive(Clone, Debug)]
struct Frame {
    /// Function index in `prog.fns`.
    func: usize,
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
    };
    call(prog.entry, None, Vec::new(), &mut m)?;
    loop {
        let fr = m.frames.len() - 1;
        match step_frame(fr, &mut m)? {
            FrameStep::Continue => {}
            FrameStep::Return(v) => {
                m.frames.pop();
                let dest = m.pending.pop().unwrap_or(None);
                match m.frames.last() {
                    None => {
                        debug_assert!(dest.is_none());
                        return Ok(Outcome {
                            exit: Exit::Return,
                            stdout: std::mem::take(&mut m.stdout),
                            stdout_latched: m.stdout_latched,
                        });
                    }
                    Some(_) => {
                        let caller = m.frames.len() - 1;
                        if let Some(d) = dest {
                            m.define(caller, d, v);
                        }
                    }
                }
            }
            FrameStep::Trap(kind) => {
                return Ok(Outcome {
                    exit: Exit::Trap(kind),
                    stdout: std::mem::take(&mut m.stdout),
                    stdout_latched: m.stdout_latched,
                });
            }
        }
    }
}

enum FrameStep {
    Continue,
    Return(Slot),
    Trap(TrapKind),
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
    m.frames.push(Frame {
        func,
        vals,
        roots,
        block: entry,
        pc: 0,
    });
    Ok(())
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
            Err(Fault::Trap(kind)) => Ok(FrameStep::Trap(kind)),
            Err(Fault::Error(e)) => Err(e),
        }
    } else {
        exec_term(fr, row.term, m)
    }
}

fn val_operand(m: &Machine<'_>, fr: usize, inst: u32, raw: u32) -> Result<Slot, Fault> {
    if raw == fors_fmir::op::NO_OPERAND {
        return Err(InterpError::TypeMismatch("missing operand".into()).into());
    }
    let v = ValId(raw);
    let s = m.slot(fr, inst, v)?;
    if !s.init {
        return Err(InterpError::UninitRead(raw).into());
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
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.int_kind(ty)?;
            let r = crate::arith::int_binop(name, mode, a.bits, b.bits, k).map_err(Fault::Trap)?;
            define(dest, m, fr, Slot::val(r));
        }
        Op::Neg(mode) => {
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.int_kind(ty)?;
            let r = crate::arith::int_neg(mode, a.bits, k).map_err(Fault::Trap)?;
            define(dest, m, fr, Slot::val(r));
        }
        Op::Fadd(_) | Op::Fsub(_) | Op::Fmul(_) | Op::Fdiv(_) | Op::Frem(_) => {
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.b)?;
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
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.float_kind(ty)?;
            let r = crate::arith::fneg(k.from_bits(a.bits), k);
            define(dest, m, fr, Slot::val(r));
        }
        Op::Icmp(pred) => {
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.b)?;
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
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.b)?;
            let ty = val_ty(m, fr, inst, inst_row.a)?;
            let k = m.float_kind(ty)?;
            let r = crate::arith::fcmp(k.from_bits(a.bits), k.from_bits(b.bits), pred);
            define(dest, m, fr, Slot::val(r as u64));
        }
        Op::And | Op::Or | Op::Xor => {
            let a = val_operand(m, fr, inst, inst_row.a)?;
            let b = val_operand(m, fr, inst, inst_row.b)?;
            let r = match op {
                Op::And => a.bits & b.bits,
                Op::Or => a.bits | b.bits,
                _ => a.bits ^ b.bits,
            };
            define(dest, m, fr, Slot::val(r));
        }
        Op::Not => {
            let a = val_operand(m, fr, inst, inst_row.a)?;
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
            let a = val_operand(m, fr, inst, inst_row.a)?;
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
            m.cells.push(Cells { slots });
            define(dest, m, fr, Slot::val(id));
        }
        Op::Field => {
            let base = val_operand(m, fr, inst, inst_row.a)?;
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
            let base = val_operand(m, fr, inst, inst_row.a)?;
            let lo = val_operand(m, fr, inst, inst_row.b)?;
            let hi = val_operand(m, fr, inst, inst_row.c)?;
            let base_len = m
                .cells
                .get(base.bits as usize)
                .map(|c| c.slots.len() as u64)
                .ok_or_else(|| {
                    InterpError::TypeMismatch("slice_range base is not an aggregate".into())
                })?;
            if lo.bits > hi.bits || hi.bits > base_len {
                return Err(Fault::Trap(TrapKind::Bounds));
            }
            let id = m.cells.len() as u64;
            m.cells.push(Cells {
                slots: vec![
                    Slot::val(base.bits),
                    Slot::val(lo.bits),
                    Slot::val(hi.bits - lo.bits),
                ],
            });
            define(dest, m, fr, Slot::val(id));
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
            let (base, start, n) = slice_parts(m, m.slot(fr, inst, xs)?)?;
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
                let cell = m.cells.get(base as usize).ok_or_else(|| {
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
        Op::CopyFrom | Op::MoveFrom | Op::Borrow | Op::BorrowMut | Op::BorrowOut => {
            // F1 place read: conventions need I8's flow data (D6), so every
            // read shares the current value (aggregates are
            // reference-shared; see `fors-lower`'s module docs).
            let s = read_place(m, fr, inst, inst_row.a)?;
            define(dest, m, fr, s);
        }
        Op::Init => {
            let v = val_operand(m, fr, inst, inst_row.b)?;
            write_place(m, fr, inst, inst_row.a, v)?;
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
                let c = val_operand(m, fr, inst, inst_row.a)?;
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

/// F5's `Slice[T]` stand-in, the read half: `slice_range` builds a
/// three-cell DESCRIPTOR `{ base aggregate handle, start, len }` rather
/// than copying elements, and this reads it back. It is the same kind of
/// "minimal intrinsic-backed stub" F2 used for `Buffer.fixed` (design
/// §5.8): real `Slice` bodies, with `len`, indexing and the iterator
/// surface, are F7's, and when they land this descriptor is what they
/// replace. Nothing but `reduce_tree` consumes it today.
fn slice_parts(m: &Machine<'_>, desc: Slot) -> Result<(u64, u64, u64), InterpError> {
    let cell = m
        .cells
        .get(desc.bits as usize)
        .ok_or_else(|| InterpError::TypeMismatch("slice operand is not a slice".into()))?;
    match cell.slots.as_slice() {
        [base, start, len] => Ok((base.bits, start.bits, len.bits)),
        _ => Err(InterpError::TypeMismatch(
            "slice operand is not a three-cell slice descriptor".into(),
        )),
    }
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

/// Resolves a `PlaceId` operand to its `(root, segs)`. Bounds-checked: a
/// dangling place is a diagnostic, never a panic.
fn place_shape(
    m: &Machine<'_>,
    fr: usize,
    raw: u32,
) -> Result<(u32, Vec<fors_fmir::place::Seg>), InterpError> {
    let decl = &m.func(m.frames[fr].func).decl;
    if (raw as usize) >= decl.places.len() {
        return Err(InterpError::TypeMismatch("dangling place".into()));
    }
    let pid = fors_fmir::ids::PlaceId(raw);
    let row = decl.places.row(pid);
    Ok((row.root, decl.places.segs(pid).to_vec()))
}

fn root_slot(m: &Machine<'_>, fr: usize, _inst: u32, root: u32) -> Result<Slot, InterpError> {
    // A slot that was never `init`-ed reads as uninitialised — whether it
    // was declared and skipped, or never declared at all. Both are clean
    // `UninitRead` diagnostics, never panics.
    m.frames[fr]
        .roots
        .get(root as usize)
        .copied()
        .filter(|s| s.init)
        .ok_or(InterpError::UninitRead(root))
}

/// Resolves a `Seg::Index` segment's runtime index, bounds-checked against
/// `len` (ch02 R15's `bounds` trap — F2's `trap-bounds` gate, §5.8's
/// "minimal intrinsic-backed stub" for `Buffer`/`Slice`, real bodies F7's).
fn index_in_bounds(
    m: &Machine<'_>,
    fr: usize,
    inst: u32,
    idx: ValId,
    len: usize,
) -> Result<usize, Fault> {
    let idx_slot = val_operand(m, fr, inst, idx.0)?;
    let i = idx_slot.bits as usize;
    if i >= len {
        return Err(Fault::Trap(TrapKind::Bounds));
    }
    Ok(i)
}

/// Reads a place: `[]` is the local slot itself, `[Field(i)]` is one cell
/// of the aggregate the slot names, `[Index(v)]` is the same cell array
/// read at a RUNTIME index (bounds-checked). Deeper paths are a lowering
/// bug (lowering only ever emits these shapes through F2).
fn read_place(m: &mut Machine<'_>, fr: usize, inst: u32, raw: u32) -> Result<Slot, Fault> {
    let (root, segs) = place_shape(m, fr, raw)?;
    let base = root_slot(m, fr, inst, root)?;
    if !base.init {
        return Err(InterpError::UninitRead(root).into());
    }
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
            let cell = m.cells.get(base.bits as usize).ok_or_else(|| {
                InterpError::TypeMismatch("place base is not an aggregate".into())
            })?;
            let len = cell.slots.len();
            let i = index_in_bounds(m, fr, inst, idx, len)?;
            Ok(m.cells[base.bits as usize].slots[i])
        }
        _ => Err(InterpError::TypeMismatch("place path outside the F1/F2 shapes".into()).into()),
    }
}

/// Writes a place (same shapes as [`read_place`]).
fn write_place(m: &mut Machine<'_>, fr: usize, inst: u32, raw: u32, v: Slot) -> Result<(), Fault> {
    let (root, segs) = place_shape(m, fr, raw)?;
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
        [fors_fmir::place::Seg::Field(i)] => {
            let base = root_slot(m, fr, inst, root)?;
            if !base.init {
                return Err(InterpError::UninitRead(root).into());
            }
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
            let base = root_slot(m, fr, inst, root)?;
            if !base.init {
                return Err(InterpError::UninitRead(root).into());
            }
            let len = m
                .cells
                .get(base.bits as usize)
                .ok_or_else(|| InterpError::TypeMismatch("place base is not an aggregate".into()))?
                .slots
                .len();
            let i = index_in_bounds(m, fr, inst, idx, len)?;
            m.cells[base.bits as usize].slots[i] = v;
            Ok(())
        }
        _ => Err(InterpError::TypeMismatch("place path outside the F1/F2 shapes".into()).into()),
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
            let mut bytes = m.strs.get(text.bits as usize).cloned().unwrap_or_default();
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
        other => Err(InterpError::UnknownIntrinsic(other.to_string()).into()),
    }
}

fn exec_term(fr: usize, term: InstRow, m: &mut Machine<'_>) -> Result<FrameStep, InterpError> {
    match term.op {
        Op::Br => {
            goto(m, fr, BlockId(term.a))?;
            Ok(FrameStep::Continue)
        }
        Op::CondBr => {
            let c = m.slot(fr, u32::MAX, ValId(term.a))?;
            if !c.init {
                return Err(InterpError::UninitRead(term.a));
            }
            goto(m, fr, BlockId(if c.bits != 0 { term.b } else { term.c }))?;
            Ok(FrameStep::Continue)
        }
        Op::Ret => {
            let v = if term.a == fors_fmir::op::NO_OPERAND {
                Slot::unit()
            } else {
                let s = m.slot(fr, u32::MAX, ValId(term.a))?;
                if !s.init {
                    return Err(InterpError::UninitRead(term.a));
                }
                s
            };
            Ok(FrameStep::Return(v))
        }
        Op::Trap => {
            let kind = fors_fmir::op::TrapKind::from_u32(term.a)
                .ok_or_else(|| InterpError::TypeMismatch("bad trap kind".into()))?;
            Ok(FrameStep::Trap(kind))
        }
        Op::Unreachable => Err(InterpError::TypeMismatch("reached unreachable".into())),
        _ => Err(InterpError::UnsupportedOp(term.op.discriminant())),
    }
}
