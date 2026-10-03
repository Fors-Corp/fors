//! F10's seeded-miscompile hook (design §7.3's exit criterion, borrowed from
//! `compiler-architecture.md` C3: "the reducer shrinks a seeded miscompile to
//! under 30 FMIR instructions").
//!
//! **Test-only.** This module exists only under the `seeded-miscompile`
//! feature, which no build of `fors-cli` enables: `fors-lower`'s default
//! feature set is empty, and the one crate that turns it on does so from its
//! `[dev-dependencies]` (`fors-oracle`'s tests), which
//! `fors-oracle/tests/seeded.rs`'s `the_miscompile_hook_is_unreachable_from_a_real_build`
//! asserts over every manifest in the workspace. A real `fors build`/`fors
//! run` therefore has no way to reach [`lower_build_miscompiled`].
//!
//! Each canned miscompile is a deliberate LOWERING bug, applied as the last
//! step of lowering to every lowered body ([`lower_build_miscompiled`]),
//! and exposed on its own ([`apply`]) so the reducer's FMIR stage can ask
//! "does the bug still show?" of a candidate it has already lowered — the
//! two are the same rewrite, so a reduction at either level is judged by
//! the same miscompile.

use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::InstId;
use fors_fmir::op::{ArithMode, CmpPred, Op};

/// The seven canned miscompiles.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Miscompile {
    /// `sub a, b` emitted as `sub b, a` (an operand-order bug).
    SubOperandSwap,
    /// `icmp lt` emitted as `icmp le` (an off-by-one in a comparison).
    LtAsLe,
    /// An integer constant `>= 100` emitted one too large (a bug in the
    /// large-immediate encoding path).
    BigConstOffByOne,
    /// `xor` emitted as `or` (a wrong opcode-table row).
    XorAsOr,
    /// A wrapping add emitted as a SATURATING add (a mode-bit bug: identical
    /// until the add overflows).
    WrapAddAsSat,
    /// `icmp lt a, b` emitted as `icmp lt b, a` (an operand-order bug in a
    /// comparison; F10 verification).
    LtOperandSwap,
    /// A `field` read of index 1 emitted as index 0 (a dropped field
    /// offset: `p.b` reads `p.a`; F10 verification).
    FieldOneAsZero,
}

impl Miscompile {
    pub const ALL: [Miscompile; 7] = [
        Miscompile::SubOperandSwap,
        Miscompile::LtAsLe,
        Miscompile::BigConstOffByOne,
        Miscompile::XorAsOr,
        Miscompile::WrapAddAsSat,
        Miscompile::LtOperandSwap,
        Miscompile::FieldOneAsZero,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Miscompile::SubOperandSwap => "sub-operand-swap",
            Miscompile::LtAsLe => "lt-as-le",
            Miscompile::BigConstOffByOne => "big-const-off-by-one",
            Miscompile::XorAsOr => "xor-as-or",
            Miscompile::WrapAddAsSat => "wrap-add-as-sat",
            Miscompile::LtOperandSwap => "lt-operand-swap",
            Miscompile::FieldOneAsZero => "field-one-as-zero",
        }
    }
}

/// Applies `m` to every instruction of `decl` it matches; returns how many
/// rows it rewrote.
pub fn apply(m: Miscompile, decl: &mut DeclFmir) -> usize {
    let rows: Vec<(InstId, fors_fmir::inst::InstRow)> = decl.insts.all_rows().collect();
    let mut n = 0;
    for (id, row) in rows {
        let mut new = row;
        match (m, row.op) {
            (Miscompile::SubOperandSwap, Op::Sub(_)) => {
                new.a = row.b;
                new.b = row.a;
            }
            (Miscompile::LtAsLe, Op::Icmp(CmpPred::Lt)) => new.op = Op::Icmp(CmpPred::Le),
            (Miscompile::BigConstOffByOne, Op::ConstInt) => {
                let v = ((row.b as u64) << 32) | row.a as u64;
                if (v as i64) >= 100 {
                    let w = v.wrapping_add(1);
                    new.a = w as u32;
                    new.b = (w >> 32) as u32;
                }
            }
            (Miscompile::XorAsOr, Op::Xor) => new.op = Op::Or,
            (Miscompile::WrapAddAsSat, Op::Add(ArithMode::Wrap)) => {
                new.op = Op::Add(ArithMode::Sat)
            }
            (Miscompile::LtOperandSwap, Op::Icmp(CmpPred::Lt)) => {
                new.a = row.b;
                new.b = row.a;
            }
            (Miscompile::FieldOneAsZero, Op::Field) if row.b == 1 => new.b = 0,
            _ => {}
        }
        if new != row {
            decl.insts.set_row(id, new);
            n += 1;
        }
    }
    n
}

/// [`crate::lower_build`], then `m` applied to every lowered body: the
/// seeded-miscompile build.
pub fn lower_build_miscompiled(
    inputs: &[fors_resolve::FileInput<'_>],
    out: &fors_check::CheckOutput,
    interner: &mut fors_index::Interner,
    m: Miscompile,
) -> crate::LoweredBuild {
    let mut build = crate::lower_build(inputs, out, interner);
    for f in &mut build.fns {
        apply(m, &mut f.decl);
    }
    build
}
