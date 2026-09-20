//! The FMIR opcode set (design §3.10): **71 opcodes**, "counting the groups
//! ... exactly as listed and taking `wrap_`/`sat_`/`unchecked_` as a 2-bit
//! mode field on the eight trapping arithmetic opcodes rather than as 24
//! further opcodes". Every trapping-arithmetic and float variant therefore
//! carries its mode/relax mask as an embedded field rather than being a
//! separate `Op` variant, which is what keeps the count at 71 while Rust's
//! enum stays exhaustive and type-safe (no separate `mode: u8` column needed
//! on `InstRow`). [decision: embed `ArithMode`/`Relax`/`Policy`/`CmpPred`
//! inside the `Op` variant rather than packing them into `InstRow.a/b/c` or
//! adding an `InstRow` column beyond the design's literal `op, a, b, c, ty,
//! site` list]
//!
//! Operand convention (design §3.10: "Operand shape is `(a, b, c)` `ValId`s
//! plus `ty` and `site`; anything variadic spills to `operands`"), documented
//! per group since the design fixes the *set* of opcodes but not each one's
//! exact `a`/`b`/`c` assignment:
//!
//! | Group | `a` | `b` | `c` |
//! |---|---|---|---|
//! | binary value op (`add`..`xor`, `fadd`..`fcmp`, `conv_*`) | lhs `ValId` | rhs `ValId` (`ABSENT` if unary: `neg`/`fneg`/`not`/`conv_*`) | unused, except `icmp`/`fcmp` pack `CmpPred` here |
//! | `agg_new` / `tuple_new` | start into `operands` | len | unused |
//! | `variant_new` | start into `operands` (payload) | len | variant index |
//! | `field` | base `ValId` | field index | unused |
//! | `discr` / `payload` | base `ValId` | (`payload`: variant index) | unused |
//! | `move_from`/`copy_from`/`borrow`/`borrow_mut`/`borrow_out` | `PlaceId` | unused | unused |
//! | `init` | `PlaceId` | value `ValId` | unused |
//! | `index` | base `ValId` | index `ValId` | unused |
//! | `slice_range` | base `ValId` | start `ValId` | end `ValId` |
//! | `alloc` | size `ValId` | align `ValId` | unused |
//! | `free` | ptr `ValId` | unused | unused |
//! | `arena_alloc` | arena `ValId` | size `ValId` | unused |
//! | `arena_deref` / `arena_reset` | arena/ref `ValId` | unused | unused |
//! | `call_direct`/`call_witness`/`call_closure`/`intrinsic` | index into `DeclFmir::calls` | unused | unused |
//! | `check_pre`/`check_post`/`check_inv` | condition `ValId` | unused | unused (policy lives on the `Op` variant) |
//! | `reduce_tree` | index into `DeclFmir::reduces` | unused | unused |
//! | `erase_to_dyn` / `declassify` | src `ValId` | unused | unused |
//! | `region_enter`/`region_exit`/`spawn`/`sync` | `RegionId` | unused | unused |
//!
//! Terminators reuse this exact same `InstRow` shape (design's own operand
//! line covers "the instruction set" as a whole, terminators included) but
//! live in `BlockRow.term`, never in `InstPool` — see `block.rs`.
//!
//! | Terminator | `a` | `b` | `c` |
//! |---|---|---|---|
//! | `br` | target `BlockId` | unused | unused |
//! | `cond_br` | cond `ValId` | then `BlockId` | else `BlockId` |
//! | `switch_discr` | index into `DeclFmir::switches` | unused | unused |
//! | `try_br` | call `InstId` | ok `BlockId` | err `BlockId` |
//! | `ret` / `raise` | value `ValId` (`ABSENT` = none) | unused | unused |
//! | `trap` | `TrapKind` discriminant | unused | unused |
//! | `unreachable` | unused | unused | unused |

use crate::ids::ABSENT;

/// The explicit mode of a trapping-arithmetic opcode (design §3.10, ch03
/// Rule 4). `Trap` is the default surface spelling (`+ - * / %` etc.);
/// `Wrap`/`Sat`/`Unchecked` are the `wrap_`/`sat_`/`unchecked_` forms.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArithMode {
    Trap,
    Wrap,
    Sat,
    Unchecked,
}

impl ArithMode {
    pub const fn as_u32(self) -> u32 {
        match self {
            ArithMode::Trap => 0,
            ArithMode::Wrap => 1,
            ArithMode::Sat => 2,
            ArithMode::Unchecked => 3,
        }
    }

    pub const fn from_u32(v: u32) -> Option<ArithMode> {
        Some(match v {
            0 => ArithMode::Trap,
            1 => ArithMode::Wrap,
            2 => ArithMode::Sat,
            3 => ArithMode::Unchecked,
            _ => return None,
        })
    }
}

/// `@fastmath`'s per-instruction mask (design §5.6(6)): `{reassoc, contract,
/// nsz, finite, recip}`. F0 only carries it (F1's interpreter is the one
/// that "ignores it, always computing the strict result").
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Relax(pub u8);

impl Relax {
    pub const NONE: Relax = Relax(0);
    pub const REASSOC: u8 = 1 << 0;
    pub const CONTRACT: u8 = 1 << 1;
    pub const NSZ: u8 = 1 << 2;
    pub const FINITE: u8 = 1 << 3;
    pub const RECIP: u8 = 1 << 4;
}

/// `check_pre`/`check_post`/`check_inv`'s policy (design §3.6): "resolved
/// from the module's `contracts:` line at lower time". `fors-lower` (E11)
/// reads the module header itself until I10 lands D10; F0 just carries
/// whichever policy a builder/parser was given.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Policy {
    Runtime,
    Off,
}

impl Policy {
    pub const fn as_u32(self) -> u32 {
        match self {
            Policy::Runtime => 0,
            Policy::Off => 1,
        }
    }

    pub const fn from_u32(v: u32) -> Option<Policy> {
        Some(match v {
            0 => Policy::Runtime,
            1 => Policy::Off,
            _ => return None,
        })
    }
}

/// `icmp`/`fcmp`'s predicate. Not named by the design's opcode table (which
/// fixes only the *opcode* set); embedding it in the `Op` variant keeps
/// `icmp`/`fcmp` single opcodes rather than one-per-predicate.
/// [decision: predicate is part of `Op`, invented — not specified by design §3.10]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CmpPred {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpPred {
    pub const fn as_u32(self) -> u32 {
        match self {
            CmpPred::Eq => 0,
            CmpPred::Ne => 1,
            CmpPred::Lt => 2,
            CmpPred::Le => 3,
            CmpPred::Gt => 4,
            CmpPred::Ge => 5,
        }
    }

    pub const fn from_u32(v: u32) -> Option<CmpPred> {
        Some(match v {
            0 => CmpPred::Eq,
            1 => CmpPred::Ne,
            2 => CmpPred::Lt,
            3 => CmpPred::Le,
            4 => CmpPred::Gt,
            5 => CmpPred::Ge,
            _ => return None,
        })
    }
}

/// ch02 Rule 15's closed eight — "a Rust enum with exactly eight variants
/// and a `const KINDS: [&str; 8]` asserted against the corpus's `detail:`
/// strings by a test, so a ninth kind cannot be added without a spec edit."
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u32)]
pub enum TrapKind {
    Bounds = 0,
    Overflow = 1,
    DivZero = 2,
    Shift = 3,
    CheckedConversion = 4,
    ArenaGeneration = 5,
    Contract = 6,
    EmptyReduce = 7,
}

impl TrapKind {
    pub const KINDS: [&'static str; 8] = [
        "bounds",
        "overflow",
        "div-zero",
        "shift",
        "checked-conversion",
        "arena-generation",
        "contract",
        "empty-reduce",
    ];

    pub const fn as_str(self) -> &'static str {
        Self::KINDS[self as usize]
    }

    pub fn from_u32(v: u32) -> Option<TrapKind> {
        Some(match v {
            0 => TrapKind::Bounds,
            1 => TrapKind::Overflow,
            2 => TrapKind::DivZero,
            3 => TrapKind::Shift,
            4 => TrapKind::CheckedConversion,
            5 => TrapKind::ArenaGeneration,
            6 => TrapKind::Contract,
            7 => TrapKind::EmptyReduce,
            _ => return None,
        })
    }

    pub fn parse_name(s: &str) -> Option<TrapKind> {
        Self::KINDS
            .iter()
            .position(|k| *k == s)
            .map(|i| TrapKind::from_u32(i as u32).unwrap())
    }
}

/// The 71-opcode set. Grouped and ordered exactly as design §3.10 lists them
/// (a comment marks each group boundary) plus one sentinel appended at the
/// end that is **not** one of the 71: [`Op::TileOp`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    // -- Constants (6) --------------------------------------------------
    ConstInt,
    ConstFloat,
    ConstBool,
    ConstUnit,
    ConstStr,
    ConstFn,
    // -- Arithmetic, trapping by default (8) -----------------------------
    Add(ArithMode),
    Sub(ArithMode),
    Mul(ArithMode),
    Div(ArithMode),
    Rem(ArithMode),
    Shl(ArithMode),
    Shr(ArithMode),
    Neg(ArithMode),
    // -- Float (6) --------------------------------------------------------
    Fadd(Relax),
    Fsub(Relax),
    Fmul(Relax),
    Fdiv(Relax),
    Frem(Relax),
    Fneg(Relax),
    // -- Compare / logic (6) ----------------------------------------------
    Icmp(CmpPred),
    Fcmp(CmpPred),
    And,
    Or,
    Xor,
    Not,
    // -- Conversion (4) -----------------------------------------------------
    ConvChecked,
    ConvWrap,
    ConvSat,
    ConvTrunc,
    // -- Aggregate (6) ------------------------------------------------------
    AggNew,
    Field,
    VariantNew,
    Discr,
    Payload,
    TupleNew,
    // -- Place / memory (8) --------------------------------------------------
    MoveFrom,
    CopyFrom,
    Init,
    Borrow,
    BorrowMut,
    BorrowOut,
    Index,
    SliceRange,
    // -- Heap / arena (5) -----------------------------------------------------
    Alloc,
    Free,
    ArenaAlloc,
    ArenaDeref,
    ArenaReset,
    // -- Calls (4) --------------------------------------------------------------
    CallDirect,
    CallWitness,
    CallClosure,
    Intrinsic,
    // -- Contracts (3) ------------------------------------------------------------
    CheckPre(Policy),
    CheckPost(Policy),
    CheckInv(Policy),
    // -- Reduce (1) -----------------------------------------------------------------
    ReduceTree,
    // -- Erasure / secret (2) ---------------------------------------------------------
    EraseToDyn,
    Declassify,
    // -- Regions, M3 shells (4) -------------------------------------------------------
    RegionEnter,
    RegionExit,
    Spawn,
    Sync,
    // -- Terminators (8) --------------------------------------------------------------
    Br,
    CondBr,
    SwitchDiscr,
    TryBr,
    Ret,
    Raise,
    Trap,
    Unreachable,

    // -- NOT one of the 71 -------------------------------------------------------------
    /// A `tile.*` mnemonic. `tile.*` "MUST appear only in FMIR" per ch05 Rule
    /// 12, but no `tile.*` op is *defined* yet ("ch05 R12 fixes the home; no
    /// op is defined yet", design §1.2) — M6 owns the real opcodes. The
    /// parser (`parse.rs`) turns any `tile.<name>` mnemonic into this one
    /// sentinel variant rather than hard-failing, so rejecting it is
    /// `verify()`'s job like every other "not licensed at this level" case
    /// ("The verifier rejects `tile.*` outside FMIR from F0, which costs
    /// nothing" — design §1.2) instead of bespoke parser error recovery.
    /// [decision: `TileOp` sentinel, count stays 71 excluding it]
    TileOp,
}

impl Op {
    /// The 8 terminator-class opcodes of design §3.10's "Terminators" group.
    /// A `BlockRow.term` must hold one of these; an `InstPool` row in a
    /// block's regular instruction range must never hold one — that second
    /// half is exactly `verify_rejects_two_terminators` (see `verify.rs`).
    pub const fn is_terminator(self) -> bool {
        matches!(
            self,
            Op::Br
                | Op::CondBr
                | Op::SwitchDiscr
                | Op::TryBr
                | Op::Ret
                | Op::Raise
                | Op::Trap
                | Op::Unreachable
        )
    }

    /// The instructions design §3.4a's `AliasSeed` pool exists for: every one
    /// produces a fresh pointer/place-like, potentially-aliasing value.
    /// `move_from`/`copy_from`/`init`/`field`/`arena_reset`/`free` are
    /// deliberately excluded — their identity is already carried by
    /// `PlaceRow` ("SoA field identity ... derivable from the place, no
    /// extra field", §3.4a) or they consume rather than produce.
    /// [decision: this exact 8-op set is not enumerated verbatim by the
    /// design, which gives the five alias *sources* rather than the op list;
    /// derived from §3.4a's table plus §5.2's detection list]
    pub const fn is_memory_producing(self) -> bool {
        matches!(
            self,
            Op::Alloc
                | Op::ArenaAlloc
                | Op::ArenaDeref
                | Op::Borrow
                | Op::BorrowMut
                | Op::BorrowOut
                | Op::Index
                | Op::SliceRange
        )
    }

    /// The eight ch03 Rule 2 trapping-by-default arithmetic ops (the ones an
    /// `ArithMode` rides on).
    pub const fn is_trapping_arith(self) -> bool {
        matches!(
            self,
            Op::Add(_)
                | Op::Sub(_)
                | Op::Mul(_)
                | Op::Div(_)
                | Op::Rem(_)
                | Op::Shl(_)
                | Op::Shr(_)
                | Op::Neg(_)
        )
    }

    pub const fn arith_mode(self) -> Option<ArithMode> {
        match self {
            Op::Add(m)
            | Op::Sub(m)
            | Op::Mul(m)
            | Op::Div(m)
            | Op::Rem(m)
            | Op::Shl(m)
            | Op::Shr(m)
            | Op::Neg(m) => Some(m),
            _ => None,
        }
    }

    /// ch05 Rule 6b's "any trapping operation on a secret operand ... use
    /// `wrap_`/`sat_`/`unchecked_` forms" escape hatch: only the `Trap` mode
    /// is rejected on a secret operand; `Wrap`/`Sat`/`Unchecked` are the
    /// accepted explicit forms. `conv_checked` gets the same treatment
    /// (`conv_wrap`/`conv_sat`/`conv_trunc` are its escapes).
    pub const fn is_secret_rejected_trapping_op(self) -> bool {
        matches!(self.arith_mode(), Some(ArithMode::Trap)) || matches!(self, Op::ConvChecked)
    }

    /// Does this instruction bounds/lossy-check and therefore "hide a
    /// branch" on its index/bound operand (ch05 Rule 6b)?
    pub const fn is_bounds_or_index(self) -> bool {
        matches!(self, Op::Index | Op::SliceRange)
    }

    /// A host-effecting door (design §3.10: "`intrinsic` is the single door
    /// to the host"). F0 has no closed intrinsic table yet (that is F1's
    /// `fors-interp::intrinsic.rs`), so every `intrinsic` call is treated
    /// conservatively as host-effecting for ch05 Rule 6b's "secret argument
    /// to a host-effecting `intrinsic`" check. [decision: conservative
    /// over-approximation, no purity table at F0]
    pub const fn is_host_intrinsic(self) -> bool {
        matches!(self, Op::Intrinsic)
    }

    pub const fn is_call(self) -> bool {
        matches!(
            self,
            Op::CallDirect | Op::CallWitness | Op::CallClosure | Op::Intrinsic
        )
    }

    pub const fn is_contract_check(self) -> bool {
        matches!(self, Op::CheckPre(_) | Op::CheckPost(_) | Op::CheckInv(_))
    }

    /// A stable `(discriminant, payload)` pair for `encode.rs`'s canonical
    /// byte encoding — deliberately not Rust's own enum discriminant (which
    /// is not guaranteed addressable for a data-carrying variant without
    /// `unsafe`), and deliberately not derived (no dependency can provide
    /// one). `payload` is `0` for every opcode with no embedded mode.
    pub const fn discriminant(self) -> u32 {
        match self {
            Op::ConstInt => 0,
            Op::ConstFloat => 1,
            Op::ConstBool => 2,
            Op::ConstUnit => 3,
            Op::ConstStr => 4,
            Op::ConstFn => 5,
            Op::Add(_) => 6,
            Op::Sub(_) => 7,
            Op::Mul(_) => 8,
            Op::Div(_) => 9,
            Op::Rem(_) => 10,
            Op::Shl(_) => 11,
            Op::Shr(_) => 12,
            Op::Neg(_) => 13,
            Op::Fadd(_) => 14,
            Op::Fsub(_) => 15,
            Op::Fmul(_) => 16,
            Op::Fdiv(_) => 17,
            Op::Frem(_) => 18,
            Op::Fneg(_) => 19,
            Op::Icmp(_) => 20,
            Op::Fcmp(_) => 21,
            Op::And => 22,
            Op::Or => 23,
            Op::Xor => 24,
            Op::Not => 25,
            Op::ConvChecked => 26,
            Op::ConvWrap => 27,
            Op::ConvSat => 28,
            Op::ConvTrunc => 29,
            Op::AggNew => 30,
            Op::Field => 31,
            Op::VariantNew => 32,
            Op::Discr => 33,
            Op::Payload => 34,
            Op::TupleNew => 35,
            Op::MoveFrom => 36,
            Op::CopyFrom => 37,
            Op::Init => 38,
            Op::Borrow => 39,
            Op::BorrowMut => 40,
            Op::BorrowOut => 41,
            Op::Index => 42,
            Op::SliceRange => 43,
            Op::Alloc => 44,
            Op::Free => 45,
            Op::ArenaAlloc => 46,
            Op::ArenaDeref => 47,
            Op::ArenaReset => 48,
            Op::CallDirect => 49,
            Op::CallWitness => 50,
            Op::CallClosure => 51,
            Op::Intrinsic => 52,
            Op::CheckPre(_) => 53,
            Op::CheckPost(_) => 54,
            Op::CheckInv(_) => 55,
            Op::ReduceTree => 56,
            Op::EraseToDyn => 57,
            Op::Declassify => 58,
            Op::RegionEnter => 59,
            Op::RegionExit => 60,
            Op::Spawn => 61,
            Op::Sync => 62,
            Op::Br => 63,
            Op::CondBr => 64,
            Op::SwitchDiscr => 65,
            Op::TryBr => 66,
            Op::Ret => 67,
            Op::Raise => 68,
            Op::Trap => 69,
            Op::Unreachable => 70,
            Op::TileOp => 71,
        }
    }

    pub const fn payload(self) -> u32 {
        match self {
            Op::Add(m)
            | Op::Sub(m)
            | Op::Mul(m)
            | Op::Div(m)
            | Op::Rem(m)
            | Op::Shl(m)
            | Op::Shr(m)
            | Op::Neg(m) => m.as_u32(),
            Op::Fadd(r) | Op::Fsub(r) | Op::Fmul(r) | Op::Fdiv(r) | Op::Frem(r) | Op::Fneg(r) => {
                r.0 as u32
            }
            Op::Icmp(p) | Op::Fcmp(p) => p.as_u32(),
            Op::CheckPre(p) | Op::CheckPost(p) | Op::CheckInv(p) => p.as_u32(),
            _ => 0,
        }
    }

    pub fn from_parts(discriminant: u32, payload: u32) -> Option<Op> {
        let arith = |ctor: fn(ArithMode) -> Op| Some(ctor(ArithMode::from_u32(payload)?));
        let relax = |ctor: fn(Relax) -> Op| Some(ctor(Relax(payload as u8)));
        let cmp = |ctor: fn(CmpPred) -> Op| Some(ctor(CmpPred::from_u32(payload)?));
        let policy = |ctor: fn(Policy) -> Op| Some(ctor(Policy::from_u32(payload)?));
        match discriminant {
            0 => Some(Op::ConstInt),
            1 => Some(Op::ConstFloat),
            2 => Some(Op::ConstBool),
            3 => Some(Op::ConstUnit),
            4 => Some(Op::ConstStr),
            5 => Some(Op::ConstFn),
            6 => arith(Op::Add),
            7 => arith(Op::Sub),
            8 => arith(Op::Mul),
            9 => arith(Op::Div),
            10 => arith(Op::Rem),
            11 => arith(Op::Shl),
            12 => arith(Op::Shr),
            13 => arith(Op::Neg),
            14 => relax(Op::Fadd),
            15 => relax(Op::Fsub),
            16 => relax(Op::Fmul),
            17 => relax(Op::Fdiv),
            18 => relax(Op::Frem),
            19 => relax(Op::Fneg),
            20 => cmp(Op::Icmp),
            21 => cmp(Op::Fcmp),
            22 => Some(Op::And),
            23 => Some(Op::Or),
            24 => Some(Op::Xor),
            25 => Some(Op::Not),
            26 => Some(Op::ConvChecked),
            27 => Some(Op::ConvWrap),
            28 => Some(Op::ConvSat),
            29 => Some(Op::ConvTrunc),
            30 => Some(Op::AggNew),
            31 => Some(Op::Field),
            32 => Some(Op::VariantNew),
            33 => Some(Op::Discr),
            34 => Some(Op::Payload),
            35 => Some(Op::TupleNew),
            36 => Some(Op::MoveFrom),
            37 => Some(Op::CopyFrom),
            38 => Some(Op::Init),
            39 => Some(Op::Borrow),
            40 => Some(Op::BorrowMut),
            41 => Some(Op::BorrowOut),
            42 => Some(Op::Index),
            43 => Some(Op::SliceRange),
            44 => Some(Op::Alloc),
            45 => Some(Op::Free),
            46 => Some(Op::ArenaAlloc),
            47 => Some(Op::ArenaDeref),
            48 => Some(Op::ArenaReset),
            49 => Some(Op::CallDirect),
            50 => Some(Op::CallWitness),
            51 => Some(Op::CallClosure),
            52 => Some(Op::Intrinsic),
            53 => policy(Op::CheckPre),
            54 => policy(Op::CheckPost),
            55 => policy(Op::CheckInv),
            56 => Some(Op::ReduceTree),
            57 => Some(Op::EraseToDyn),
            58 => Some(Op::Declassify),
            59 => Some(Op::RegionEnter),
            60 => Some(Op::RegionExit),
            61 => Some(Op::Spawn),
            62 => Some(Op::Sync),
            63 => Some(Op::Br),
            64 => Some(Op::CondBr),
            65 => Some(Op::SwitchDiscr),
            66 => Some(Op::TryBr),
            67 => Some(Op::Ret),
            68 => Some(Op::Raise),
            69 => Some(Op::Trap),
            70 => Some(Op::Unreachable),
            71 => Some(Op::TileOp),
            _ => None,
        }
    }
}

/// A generic "no operand here" marker for an `InstRow`/terminator `a`/`b`/`c`
/// slot, reusing [`crate::ids::ABSENT`] (`u32::MAX`) — no FMIR pool is ever
/// `u32::MAX` rows long (§10.3's 12 B/source-byte budget alone rules that
/// out), so the sentinel cannot collide with a real index.
pub const NO_OPERAND: u32 = ABSENT;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trap_kind_strings_are_stable_and_total() {
        for i in 0..8u32 {
            let k = TrapKind::from_u32(i).unwrap();
            assert_eq!(TrapKind::parse_name(k.as_str()), Some(k));
        }
        assert_eq!(TrapKind::from_u32(8), None);
    }

    #[test]
    fn exactly_71_opcodes_excluding_the_tile_sentinel() {
        // One representative value per `Op` variant, TileOp last and
        // excluded from the count the design pins at 71 (§3.10, §13 finding
        // 12: "opcode count corrected to 71").
        let all = [
            Op::ConstInt,
            Op::ConstFloat,
            Op::ConstBool,
            Op::ConstUnit,
            Op::ConstStr,
            Op::ConstFn,
            Op::Add(ArithMode::Trap),
            Op::Sub(ArithMode::Trap),
            Op::Mul(ArithMode::Trap),
            Op::Div(ArithMode::Trap),
            Op::Rem(ArithMode::Trap),
            Op::Shl(ArithMode::Trap),
            Op::Shr(ArithMode::Trap),
            Op::Neg(ArithMode::Trap),
            Op::Fadd(Relax::NONE),
            Op::Fsub(Relax::NONE),
            Op::Fmul(Relax::NONE),
            Op::Fdiv(Relax::NONE),
            Op::Frem(Relax::NONE),
            Op::Fneg(Relax::NONE),
            Op::Icmp(CmpPred::Eq),
            Op::Fcmp(CmpPred::Eq),
            Op::And,
            Op::Or,
            Op::Xor,
            Op::Not,
            Op::ConvChecked,
            Op::ConvWrap,
            Op::ConvSat,
            Op::ConvTrunc,
            Op::AggNew,
            Op::Field,
            Op::VariantNew,
            Op::Discr,
            Op::Payload,
            Op::TupleNew,
            Op::MoveFrom,
            Op::CopyFrom,
            Op::Init,
            Op::Borrow,
            Op::BorrowMut,
            Op::BorrowOut,
            Op::Index,
            Op::SliceRange,
            Op::Alloc,
            Op::Free,
            Op::ArenaAlloc,
            Op::ArenaDeref,
            Op::ArenaReset,
            Op::CallDirect,
            Op::CallWitness,
            Op::CallClosure,
            Op::Intrinsic,
            Op::CheckPre(Policy::Runtime),
            Op::CheckPost(Policy::Runtime),
            Op::CheckInv(Policy::Runtime),
            Op::ReduceTree,
            Op::EraseToDyn,
            Op::Declassify,
            Op::RegionEnter,
            Op::RegionExit,
            Op::Spawn,
            Op::Sync,
            Op::Br,
            Op::CondBr,
            Op::SwitchDiscr,
            Op::TryBr,
            Op::Ret,
            Op::Raise,
            Op::Trap,
            Op::Unreachable,
        ];
        assert_eq!(
            all.len(),
            71,
            "design §3.10 fixes the M1 opcode count at 71"
        );
        assert_eq!(all.iter().filter(|op| op.is_terminator()).count(), 8);
    }

    #[test]
    fn every_discriminant_0_to_71_round_trips_through_from_parts() {
        for d in 0..=71u32 {
            let op = Op::from_parts(d, 0).expect("every discriminant 0..=71 is assigned");
            assert_eq!(op.discriminant(), d);
        }
        assert!(Op::from_parts(72, 0).is_none());
    }

    #[test]
    fn arith_mode_payload_round_trips() {
        for mode in [
            ArithMode::Trap,
            ArithMode::Wrap,
            ArithMode::Sat,
            ArithMode::Unchecked,
        ] {
            let op = Op::Add(mode);
            let back = Op::from_parts(op.discriminant(), op.payload()).unwrap();
            assert_eq!(back, op);
        }
    }

    #[test]
    fn tile_op_is_not_among_the_71_and_is_always_rejected_shape() {
        // TileOp classifies as none of the recognised families: it exists
        // solely so `verify()` has something to reject.
        assert!(!Op::TileOp.is_terminator());
        assert!(!Op::TileOp.is_memory_producing());
        assert!(!Op::TileOp.is_call());
    }
}
