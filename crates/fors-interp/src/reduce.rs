//! Executing the normative `reduce` tree (design §5.7: "the interpreter
//! executes §3.9's expansion literally, with `B = 256`, `L = 8` read from
//! the instruction's operands, never from the host's vector width").
//!
//! The SHAPE is not written here. It lives once, in
//! [`fors_fmir::reduce`], and this module only supplies the `op` the tree
//! applies and the slot plumbing around it. Anything about blocks, lanes,
//! operand order or the tail rules belongs there, so the interpreter and
//! every future backend cannot drift apart.
//!
//! **[HOLE-7] hard-coding, executor half.** No checker increment types
//! ch03 R11's `reduce`, so `fors-lower` hard-codes the primitive's typing
//! and names the combining function by the FMIR opcode spelling it would
//! have emitted for the same binary operator in ordinary code
//! (`fadd`/`fsub`/`fmul`/`fdiv`/`frem`, `add`/`sub`/`mul`/`div`/`rem`).
//! [`ReduceOp::resolve`] is the other end of that convention; the single
//! site that produces the names is `fors-lower::lower::reduce_op_name`.
//! When the adopting checker increment lands, both ends move together.

use fors_fmir::op::TrapKind;

use crate::arith::{FloatKind, IntKind, NumKind};
use crate::value::Slot;

/// The resolved combining function of one `reduce_tree` instruction: a
/// binary primitive plus the numeric kind it is applied at. `op` MUST be
/// pure (ch03 R11), which a primitive trivially is.
#[derive(Clone, Copy, Debug)]
pub enum ReduceOp {
    /// A trapping integer op (ch03 R2's default mode — the surface
    /// `+ - * / %` the corpus writes inside `reduce`).
    Int(IntOp, IntKind),
    Float(FloatOp, FloatKind),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FloatOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl ReduceOp {
    /// Resolves the lowering-side name against the element kind. `None` is
    /// a lowering bug (an unknown name, or a float op at an integer kind),
    /// which the caller reports as an interpreter error, never as a trap.
    pub fn resolve(name: &str, kind: NumKind) -> Option<ReduceOp> {
        match kind {
            NumKind::Int(k) => {
                let op = match name {
                    "add" => IntOp::Add,
                    "sub" => IntOp::Sub,
                    "mul" => IntOp::Mul,
                    "div" => IntOp::Div,
                    "rem" => IntOp::Rem,
                    _ => return None,
                };
                Some(ReduceOp::Int(op, k))
            }
            NumKind::Float(k) => {
                let op = match name {
                    "fadd" => FloatOp::Add,
                    "fsub" => FloatOp::Sub,
                    "fmul" => FloatOp::Mul,
                    "fdiv" => FloatOp::Div,
                    "frem" => FloatOp::Rem,
                    _ => return None,
                };
                Some(ReduceOp::Float(op, k))
            }
        }
    }

    /// One `op` application, left operand first. Strict IEEE-754 for floats
    /// (ch03 R7, design §5.6: the interpreter always computes strict, and
    /// `frem` is in-crate, never the host's). An integer op traps exactly
    /// as it would outside a `reduce`.
    pub fn apply(self, a: Slot, b: Slot) -> Result<Slot, TrapKind> {
        let bits = match self {
            ReduceOp::Int(op, k) => {
                let name = match op {
                    IntOp::Add => "add",
                    IntOp::Sub => "sub",
                    IntOp::Mul => "mul",
                    IntOp::Div => "div",
                    IntOp::Rem => "rem",
                };
                crate::arith::int_binop(name, fors_fmir::op::ArithMode::Trap, a.bits, b.bits, k)?
            }
            ReduceOp::Float(op, k) => {
                let (x, y) = (k.from_bits(a.bits), k.from_bits(b.bits));
                match op {
                    FloatOp::Add => crate::arith::fadd(x, y, k),
                    FloatOp::Sub => crate::arith::fsub(x, y, k),
                    FloatOp::Mul => crate::arith::fmul(x, y, k),
                    FloatOp::Div => crate::arith::fdiv(x, y, k),
                    FloatOp::Rem => match k {
                        FloatKind::F32 => crate::arith::frem_f32(x as f32, y as f32),
                        FloatKind::F64 => crate::arith::frem_f64(x, y),
                    },
                }
            }
        };
        Ok(Slot::val(bits))
    }
}

/// Runs `reduce(op, xs)` over `elems` with the normative shape for
/// `(n, b, l)`.
///
/// `Ok(None)` means `n == 0`: ch03 R11a's decision (trap `empty-reduce`, or
/// return the `identity:`) belongs to the caller, which is the only place
/// that knows whether an identity operand was supplied. For `n >= 1` the
/// identity never enters here at all, which is R11a's "both forms are
/// bit-identical on non-empty input" made structural rather than tested.
pub fn run(elems: &[Slot], b: u32, l: u32, op: ReduceOp) -> Result<Option<Slot>, TrapKind> {
    let tree = fors_fmir::reduce::reduce_tree(elems.len() as u32, b, l);
    let mut apply = |x: Slot, y: Slot| op.apply(x, y);
    fors_fmir::reduce::reduce_eval(&tree, elems, &mut apply)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_fmir::reduce::{REDUCE_BLOCK, REDUCE_LANES};

    fn f64s(xs: &[f64]) -> Vec<Slot> {
        xs.iter().map(|v| Slot::val(v.to_bits())).collect()
    }

    fn sub_f64() -> ReduceOp {
        ReduceOp::resolve("fsub", NumKind::Float(FloatKind::F64)).unwrap()
    }

    fn run_f64(xs: &[f64], op: ReduceOp) -> Option<f64> {
        run(&f64s(xs), REDUCE_BLOCK, REDUCE_LANES, op)
            .unwrap()
            .map(|s| f64::from_bits(s.bits))
    }

    /// The five pinned corpus shapes, executed through the interpreter's
    /// own float arithmetic rather than Rust's directly.
    #[test]
    fn pinned_corpus_values_run_through_the_interpreter_ops() {
        let pow2 = |n: u32| -> Vec<f64> { (0..n).map(|i| (1u64 << i) as f64).collect() };
        assert_eq!(run_f64(&pow2(1), sub_f64()), Some(1.0));
        assert_eq!(run_f64(&pow2(7), sub_f64()), Some(83.0));
        assert_eq!(run_f64(&pow2(8), sub_f64()), Some(-45.0));
        assert_eq!(run_f64(&pow2(9), sub_f64()), Some(-301.0));
        assert_eq!(run_f64(&vec![1.0; 257], sub_f64()), Some(-1.0));
    }

    #[test]
    fn empty_input_yields_none_and_never_an_identity() {
        assert_eq!(run_f64(&[], sub_f64()), None);
    }

    /// ch03 R13(b): `-0.0` is not normalised away on the way through.
    #[test]
    fn negative_zero_survives_the_tree() {
        let add = ReduceOp::resolve("fadd", NumKind::Float(FloatKind::F64)).unwrap();
        let got = run_f64(&[-0.0, -0.0], add).unwrap();
        assert!(got.is_sign_negative(), "-0.0 + -0.0 is -0.0");
    }

    /// A trapping integer `op` reports its trap from inside the tree.
    #[test]
    fn an_integer_overflow_inside_the_tree_traps() {
        let add = ReduceOp::resolve("add", NumKind::Int(IntKind::I8)).unwrap();
        let xs: Vec<Slot> = [100i64, 100].iter().map(|v| Slot::val(*v as u64)).collect();
        assert!(matches!(
            run(&xs, REDUCE_BLOCK, REDUCE_LANES, add),
            Err(TrapKind::Overflow)
        ));
    }

    #[test]
    fn an_unknown_or_mistyped_op_name_is_not_resolvable() {
        assert!(ReduceOp::resolve("fadd", NumKind::Int(IntKind::I64)).is_none());
        assert!(ReduceOp::resolve("add", NumKind::Float(FloatKind::F64)).is_none());
        assert!(ReduceOp::resolve("nonesuch", NumKind::Float(FloatKind::F64)).is_none());
    }
}
