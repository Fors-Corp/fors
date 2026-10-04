//! `select` (§2.1): OIR → LIR-dev, one OIR row → one stencil instance, no
//! allocation decisions (stage A: every value in its slot). Also the last
//! line of refusal: a frame over 32 KiB, and any row whose shape has no
//! stencil, is a [`Refusal`] — never a miscompile.

use fors_oir::from_fmir::reason;
use fors_oir::{LowTy, Mode, NONE, OirFunc, OirOp, Refusal, Term};

use crate::frame::Frame;
use crate::lir::{Lir, NO_LIT};
use crate::stencil::int::{ArMode, BinOp, ConvOp, IntTy, Key, LogicOp, Pred, RawExt, ShiftOp};
use crate::stencil::{Fill, table};

fn refuse(f: &OirFunc, row: Option<usize>, op: &str, why: &str) -> Refusal {
    Refusal {
        decl: f.decl,
        inst: row.map(|r| r as u32),
        op: op.to_string(),
        reason: why.to_string(),
    }
}

fn ar(m: Mode) -> Option<ArMode> {
    match m {
        Mode::Trap => Some(ArMode::Trap),
        Mode::Wrap => Some(ArMode::Wrap),
        Mode::Sat => Some(ArMode::Sat),
        Mode::None => None,
    }
}

/// The value bits as the canonical 64-bit slot pattern (E5): sign-extended
/// for a signed type, zero-extended for an unsigned one.
pub fn canonical(bits: u64, ty: IntTy) -> u64 {
    let w = ty.width();
    if w == 64 {
        return bits;
    }
    let low = bits & ((1u64 << w) - 1);
    if ty.signed() {
        (((low << (64 - w)) as i64) >> (64 - w)) as u64
    } else {
        low
    }
}

/// The stencil key of OIR row `i`.
fn key_of(f: &OirFunc, i: usize) -> Option<Key> {
    let r = &f.rows;
    let ty = r.ty[i];
    let vty = |v: u32| f.values.ty[v as usize];
    let int = IntTy::of(ty);
    Some(match r.op[i] {
        OirOp::ConstInt | OirOp::ConstBool => Key::Const,
        OirOp::ConstUnit | OirOp::ConstStr => return None,
        OirOp::SlotLoad | OirOp::SlotStore => Key::Copy,
        OirOp::Add | OirOp::Sub | OirOp::Mul | OirOp::Div | OirOp::Rem => {
            let op = match r.op[i] {
                OirOp::Add => BinOp::Add,
                OirOp::Sub => BinOp::Sub,
                OirOp::Mul => BinOp::Mul,
                OirOp::Div => BinOp::Div,
                _ => BinOp::Rem,
            };
            Key::Bin {
                op,
                mode: ar(r.mode[i])?,
                ty: int?,
            }
        }
        OirOp::Shl | OirOp::Shr => Key::Shift {
            op: if r.op[i] == OirOp::Shl {
                ShiftOp::Shl
            } else {
                ShiftOp::Shr
            },
            mode: ar(r.mode[i])?,
            ty: int?,
            count: IntTy::of(vty(r.b[i]))?.raw_ext(),
        },
        OirOp::Neg => {
            let mode = ar(r.mode[i])?;
            let ty = int?;
            if !ty.signed() && mode != ArMode::Wrap {
                return None;
            }
            Key::Neg { mode, ty }
        }
        OirOp::And | OirOp::Or | OirOp::Xor => Key::Logic {
            op: match r.op[i] {
                OirOp::And => LogicOp::And,
                OirOp::Or => LogicOp::Or,
                _ => LogicOp::Xor,
            },
        },
        OirOp::Not if ty == LowTy::Bool => Key::NotBool,
        OirOp::Not => Key::Not { ty: int? },
        OirOp::Icmp(p) => {
            let at = vty(r.a[i]);
            Key::Icmp {
                pred: Pred::of(p),
                signed: at.signed(),
            }
        }
        OirOp::ConvChecked | OirOp::ConvWrap | OirOp::ConvSat => Key::Conv {
            op: match r.op[i] {
                OirOp::ConvChecked => ConvOp::Checked,
                OirOp::ConvWrap => ConvOp::Wrap,
                _ => ConvOp::Sat,
            },
            from: IntTy::of(vty(r.a[i]))?,
            to: int?,
        },
        OirOp::WriteUint => {
            let at = vty(r.a[i]);
            Key::WriteUint {
                ext: IntTy::of(at).map(IntTy::raw_ext).unwrap_or(RawExt::None),
            }
        }
        OirOp::WriteLine => Key::WriteLine,
        OirOp::Tile => return None,
    })
}

/// OIR → LIR-dev for one function.
pub fn select(f: &OirFunc) -> Result<Lir, Refusal> {
    let Some(frame) = Frame::of(f) else {
        return Err(refuse(f, None, "frame", reason::FRAME));
    };
    let t = table();
    let mut lir = Lir::default();
    let mut prologue = Fill::default();
    prologue.imm[0] = frame.size as u16;
    lir.push(
        t.id(Key::Prologue).expect("prologue stencil"),
        prologue,
        NO_LIT,
        0,
        0,
        u32::MAX,
        0,
    );
    let r = &f.rows;
    // The string index of every `ConstStr` value (write_line's literal).
    let mut str_of = vec![NONE; f.values.len()];
    for k in 0..r.len() {
        if r.op[k] == OirOp::ConstStr && r.dst[k] != NONE {
            str_of[r.dst[k] as usize] = r.a[k];
        }
    }
    for i in 0..r.len() {
        let op = r.op[i];
        if r.dst[i] != NONE && f.values.secret[r.dst[i] as usize] {
            return Err(refuse(f, Some(i), op.name(), reason::SECRET));
        }
        let Some(key) = key_of(f, i) else {
            if matches!(op, OirOp::ConstUnit | OirOp::ConstStr) {
                continue; // no storage: unit, or a literal the writer reads
            }
            return Err(refuse(f, Some(i), op.name(), reason::OP));
        };
        #[cfg(feature = "inject-miscompile")]
        let key = crate::inject::mutate(key);
        let mut fill = Fill::default();
        let mut lit = NO_LIT;
        let val = |v: u32| frame.value(v);
        match op {
            OirOp::ConstInt => {
                let bits = (u64::from(r.b[i]) << 32) | u64::from(r.a[i]);
                let c = canonical(bits, IntTy::of(r.ty[i]).expect("int const"));
                fill.imm = std::array::from_fn(|k| (c >> (16 * k)) as u16);
                fill.slot_dst = val(r.dst[i]);
            }
            OirOp::ConstBool => {
                fill.imm = [r.a[i] as u16, 0, 0, 0];
                fill.slot_dst = val(r.dst[i]);
            }
            OirOp::SlotLoad => {
                fill.slot_a = frame.place(r.a[i]);
                fill.slot_dst = val(r.dst[i]);
            }
            OirOp::SlotStore => {
                fill.slot_a = val(r.b[i]);
                fill.slot_dst = frame.place(r.a[i]);
            }
            OirOp::WriteUint => fill.slot_a = val(r.a[i]),
            OirOp::WriteLine => {
                // The text operand is a `ConstStr` value; its row's `a` is
                // the string index.
                lit = str_of[r.a[i] as usize];
                if lit == NONE {
                    return Err(refuse(f, Some(i), op.name(), reason::STR_USE));
                }
                let len = f.strings[lit as usize].len();
                if len > u32::MAX as usize {
                    return Err(refuse(f, Some(i), op.name(), reason::TYPE));
                }
                fill.imm = [len as u16, (len >> 16) as u16, 0, 0];
            }
            _ => {
                fill.slot_a = val(r.a[i]);
                if r.b[i] != NONE {
                    fill.slot_b = val(r.b[i]);
                }
                if r.dst[i] != NONE {
                    fill.slot_dst = val(r.dst[i]);
                }
            }
        }
        let ct = if r.dst[i] != NONE {
            f.values.ct[r.dst[i] as usize]
        } else {
            0
        };
        lir.push(
            t.id(key).expect("every key has a stencil"),
            fill,
            lit,
            0,
            ct,
            i as u32,
            r.site[i],
        );
    }
    match f.term {
        Term::Ret => lir.push(
            t.id(Key::Epilogue).expect("epilogue stencil"),
            Fill::default(),
            NO_LIT,
            0,
            0,
            u32::MAX,
            f.term_site,
        ),
        Term::Trap(k) => lir.push(
            t.id(Key::TrapJump { kind: k as u8 }).expect("trap stencil"),
            Fill::default(),
            NO_LIT,
            0,
            0,
            u32::MAX,
            f.term_site,
        ),
    }
    Ok(lir)
}
