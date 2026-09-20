//! The textual dump (task item 4): "A textual dump AND a parser for it
//! (round-trip). The parser is what lets the negative corpus and later
//! increments be written by hand."
//!
//! [decision: scope. The byte encoding (`encode.rs`) already gives
//! full-fidelity round-tripping over all 71 opcodes and every pool — that is
//! what `encode_decode_roundtrip`'s 10k generated declarations exercise. The
//! textual format's only *required* job (task item 4, item 6, design's risk
//! R5) is being hand-writable for a ~20-declaration negative corpus, each
//! exercising one verifier condition, plus a positive smoke test. Rather than
//! give every one of the 71 opcodes bespoke hand-written textual syntax for
//! no consumer, this format covers exactly the opcodes the negative corpus
//! and a representative positive declaration need: `param` values, the
//! trapping arithmetic family, `index`/`slice_range`, `alloc`/`arena_alloc`/
//! `arena_deref`/`free`, `check_pre`/`post`/`inv`, `intrinsic`, `declassify`,
//! `erase_to_dyn`, every terminator, `spawn`/`region_enter`/`region_exit`/
//! `sync`, and the `tile.*` sentinel — deliberately NOT the constant pool
//! (`const_*`), which no F0 verifier check reads. A hand-built
//! `DeclFmir` for anything outside that list still exists and is
//! `verify()`-checkable — it is just built with `crates/fors-fmir`'s own pool
//! API (as `verify.rs`'s and `encode.rs`'s own unit tests already do)
//! instead of parsed from text. Every mnemonic this format DOES accept dumps
//! and re-parses losslessly; `tests/dump_parse_roundtrip.rs` checks that
//! directly, on top of `verify()` agreeing before and after.]
//!
//! One documented limitation of the textual form, which
//! `tests/dump_parse_roundtrip.rs` states as a precondition rather than
//! hides: a `%name` must be introduced above its first use (`parse` resolves
//! names in one pass, in file order), so `dump` prints every `param` value
//! above the first `block`. A `ValPool` that interleaves parameters *after*
//! instruction-defined values — which only hand-written text produces, never
//! this crate's builders or a lowering pass — therefore comes back
//! order-isomorphic but renumbered, and so with a different `fmir_hash`. The
//! byte encoding (`encode.rs`) has no such caveat and is the fidelity-
//! critical path; the textual form is the hand-writable one.
//!
//! Grammar (line-oriented, `//` to end of line is a comment, blank lines
//! ignored):
//!
//! ```text
//! decl <u32> sig <u32> [unsafe]
//! region <name> <spawn|parallel|with-arena> [captures (%name:conv)*]
//! block <name>
//! val %<name> = param <u16> ty <u32> <secret> <ct>
//! val %<name> = <mnemonic> <operand>* ty <u32> <secret> <ct> [seed <seedspec>]
//! do <mnemonic> <operand>*
//! ```
//! `<secret>` is `secret` | `nosecret` | `?` (omitted, ch05 Rule 6's missing
//! field). `<ct>` is `ct=<u16>` | `ct=?`. An operand is `%name` (a value),
//! `bb<name>` (a block), or `place<u32>` (a place with an empty projection
//! path — see the module docs' scope note); `switch_discr`'s arms are
//! `<i64>:bb<name>` tokens after its discriminant and default.
//! Every `val`/`do` line belongs to the most recently opened `block`; the
//! LAST such line in a block becomes its `term` regardless of whether its
//! own opcode is terminator-class — see `block.rs`'s module docs for why
//! that is exactly what makes `verify_rejects_two_terminators` constructible.

use std::fmt::Write as _;

use crate::decl::DeclFmir;
use crate::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED};
use crate::ids::{PlaceId, ValId};
use crate::inst::InstRow;
use crate::op::{ArithMode, Op};
use crate::value::ValDef;

/// Renders `decl` in the grammar the module docs describe. Every value gets
/// a stable `%vN` name (`N` = its `ValId`) and every block a stable `bbN`
/// name (`N` = its `BlockId`), so `dump` never needs a name-allocation pass.
pub fn dump(d: &DeclFmir) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "decl {} sig {}{}",
        d.decl.0,
        d.sig.0,
        if d.is_unsafe_invariant { " unsafe" } else { "" }
    );
    for (id, row) in d.regions.all_rows() {
        let kind = match row.kind {
            crate::region::RegionKind::Spawn => "spawn",
            crate::region::RegionKind::Parallel => "parallel",
            crate::region::RegionKind::WithArena => "with-arena",
        };
        let mut line = format!("region r{} {}", id.0, kind);
        if !row.captures_absent() {
            line.push_str(" captures");
            for cap in d.regions.captures.get(row.captures.clone()) {
                let conv = conv_str(cap.conv);
                let _ = write!(line, " %v{}:{}", cap.value.0, conv);
            }
        }
        let _ = writeln!(out, "{line}");
    }
    // `InstId -> ValId`, positional and built once: the O(n) alternative to
    // searching `d.vals` for "whose `def` names this instruction" per
    // instruction (which would also be wrong for `block.term`, since a
    // terminator has no `InstId` at all — it never lives in `InstPool`).
    let mut inst_to_val: Vec<Option<ValId>> = vec![None; d.insts.len()];
    for (val_id, row) in d.vals.all_rows() {
        // A `def` naming an instruction outside `InstPool` is malformed FMIR
        // (`verify()`'s business); `dump` stays total and just has no name to
        // print for it.
        if let ValDef::Inst(inst_id) = row.def()
            && inst_id.index() < inst_to_val.len()
        {
            inst_to_val[inst_id.index()] = Some(val_id);
        }
    }

    // Parameters are printed BEFORE the blocks, because `parse.rs` resolves a
    // `%name` in one pass, in file order: a `do ret %v0` above the `val %v0`
    // line that introduces it does not re-parse ("unknown value"), so dumping
    // them after the blocks would break the dump/parse round-trip for every
    // declaration that mentions a parameter. Values defined by an instruction
    // need no line of their own — `dump_inst_as_do` announces them inline as
    // `%vN = ...` — so this loop covers exactly the parameters.
    for (id, row) in d.vals.all_rows() {
        match row.def() {
            ValDef::Param(ordinal) => {
                let _ = writeln!(
                    out,
                    "val %v{} = param {} ty {} {} {}",
                    id.0,
                    ordinal,
                    row.ty.0,
                    secret_tok(row.flags.0),
                    ct_tok(row.ct)
                );
            }
            ValDef::Inst(_) => {}
        }
    }

    for (block_id, block) in d.blocks.all_rows() {
        let _ = writeln!(out, "block bb{}", block_id.0);
        for i in block.inst_range() {
            let id = crate::ids::InstId(i);
            // A block whose `first_inst`/`inst_len` runs past `InstPool` is
            // malformed FMIR (`verify()` reports it); `dump` prints what is
            // there instead of panicking.
            let Some(row) = d.insts.try_row(id) else {
                continue;
            };
            let name = inst_to_val.get(id.index()).copied().flatten();
            dump_inst_as_do(&mut out, d, id.index(), row, name);
        }
        // A terminator can never itself define a value in this crate's model
        // (see `op.rs`'s module docs), so there is no `ValId` to look up.
        dump_inst_as_do(&mut out, d, usize::MAX, block.term, None);
    }
    out
}

fn secret_tok(flags: u16) -> &'static str {
    if flags & SECRET_UNSPECIFIED != 0 {
        "?"
    } else if flags & crate::flags::SECRET != 0 {
        "secret"
    } else {
        "nosecret"
    }
}

fn ct_tok(ct: u16) -> String {
    if ct == CT_UNSPECIFIED {
        "ct=?".to_string()
    } else {
        format!("ct={ct}")
    }
}

fn conv_str(c: fors_fir::sig::Conv) -> &'static str {
    match c {
        fors_fir::sig::Conv::Let => "let",
        fors_fir::sig::Conv::Inout => "inout",
        fors_fir::sig::Conv::Sink => "sink",
        fors_fir::sig::Conv::Set => "set",
    }
}

fn mnemonic(op: Op) -> String {
    match op {
        Op::ConstInt => "const_int".into(),
        Op::ConstFloat => "const_float".into(),
        Op::ConstBool => "const_bool".into(),
        Op::ConstUnit => "const_unit".into(),
        Op::ConstStr => "const_str".into(),
        Op::ConstFn => "const_fn".into(),
        Op::Add(m) => format!("add{}", mode_suffix(m)),
        Op::Sub(m) => format!("sub{}", mode_suffix(m)),
        Op::Mul(m) => format!("mul{}", mode_suffix(m)),
        Op::Div(m) => format!("div{}", mode_suffix(m)),
        Op::Rem(m) => format!("rem{}", mode_suffix(m)),
        Op::Shl(m) => format!("shl{}", mode_suffix(m)),
        Op::Shr(m) => format!("shr{}", mode_suffix(m)),
        Op::Neg(m) => format!("neg{}", mode_suffix(m)),
        Op::Index => "index".into(),
        Op::SliceRange => "slice_range".into(),
        Op::Alloc => "alloc".into(),
        Op::ArenaAlloc => "arena_alloc".into(),
        Op::ArenaDeref => "arena_deref".into(),
        Op::ArenaReset => "arena_reset".into(),
        Op::Free => "free".into(),
        Op::CheckPre(_) => "check_pre".into(),
        Op::CheckPost(_) => "check_post".into(),
        Op::CheckInv(_) => "check_inv".into(),
        Op::Intrinsic => "intrinsic".into(),
        Op::Declassify => "declassify".into(),
        Op::EraseToDyn => "erase_to_dyn".into(),
        Op::RegionEnter => "region_enter".into(),
        Op::RegionExit => "region_exit".into(),
        Op::Spawn => "spawn".into(),
        Op::Sync => "sync".into(),
        Op::Br => "br".into(),
        Op::CondBr => "cond_br".into(),
        Op::SwitchDiscr => "switch_discr".into(),
        Op::TryBr => "try_br".into(),
        Op::Ret => "ret".into(),
        Op::Raise => "raise".into(),
        Op::Trap => "trap".into(),
        Op::Unreachable => "unreachable".into(),
        Op::TileOp => "tile.op".into(),
        other => format!("unsupported({})", other.discriminant()),
    }
}

/// A `:`-joined suffix on the mnemonic ITSELF (`add:wrap`), matching
/// `parse.rs::parse_mnemonic`'s `head.split_once(':')` — arithmetic mode is
/// the one modifier that must be readable from the mnemonic token alone,
/// since operand parsing already needs to know the op before it can even
/// look for `%`/`bb` tokens.
fn mode_suffix(m: ArithMode) -> &'static str {
    match m {
        ArithMode::Trap => "",
        ArithMode::Wrap => ":wrap",
        ArithMode::Sat => ":sat",
        ArithMode::Unchecked => ":unchecked",
    }
}

/// A separate trailing token AFTER the operands (`do check_pre %v0
/// policy=off`), matching `parse.rs::apply_trailing_policy`, which only
/// looks for it once the condition operand has already been consumed.
fn policy_suffix(p: crate::op::Policy) -> &'static str {
    match p {
        crate::op::Policy::Runtime => "",
        crate::op::Policy::Off => " policy=off",
    }
}

/// Dumps one instruction as a `do`/`val =` line. Operand rendering follows
/// `op.rs`'s documented `a`/`b`/`c` convention per group. `alias_idx` is
/// `usize::MAX` for a block's `term` (which has no `InstId`, so no
/// `AliasSeedPool` row either — terminators are never memory-producing).
fn dump_inst_as_do(
    out: &mut String,
    d: &DeclFmir,
    alias_idx: usize,
    inst: InstRow,
    dest: Option<ValId>,
) {
    let head = mnemonic(inst.op);
    let operands = dump_operands(d, inst);
    let trailing = trailing_modifier(inst.op);
    match dest {
        Some(val_id) if !inst.op.is_terminator() => {
            let row = d.vals.row(val_id);
            let _ = writeln!(
                out,
                "val %v{} = {head}{operands}{trailing} ty {} {} {}{}",
                val_id.0,
                row.ty.0,
                secret_tok(row.flags.0),
                ct_tok(row.ct),
                dump_seed(d, alias_idx, inst)
            );
        }
        _ => {
            let _ = writeln!(out, "do {head}{operands}{trailing}");
        }
    }
}

/// A modifier that rides after the operand list rather than on the mnemonic
/// (only `check_pre`/`post`/`inv`'s policy at F0) — see `policy_suffix`'s
/// docs for why it cannot be folded into `mnemonic()` the way arithmetic
/// mode is.
fn trailing_modifier(op: Op) -> &'static str {
    match op {
        Op::CheckPre(p) | Op::CheckPost(p) | Op::CheckInv(p) => policy_suffix(p),
        _ => "",
    }
}

fn dump_operands(d: &DeclFmir, inst: InstRow) -> String {
    let mut s = String::new();
    let val = |v: u32| format!(" %v{v}");
    let bb = |v: u32| format!(" bb{v}");
    match inst.op {
        Op::Add(_)
        | Op::Sub(_)
        | Op::Mul(_)
        | Op::Div(_)
        | Op::Rem(_)
        | Op::Shl(_)
        | Op::Shr(_) => {
            s.push_str(&val(inst.a));
            s.push_str(&val(inst.b));
        }
        Op::Neg(_) | Op::ArenaDeref | Op::ArenaReset | Op::Declassify | Op::EraseToDyn => {
            s.push_str(&val(inst.a));
        }
        Op::Index => {
            s.push_str(&val(inst.a));
            s.push_str(&val(inst.b));
        }
        Op::SliceRange => {
            s.push_str(&val(inst.a));
            s.push_str(&val(inst.b));
            s.push_str(&val(inst.c));
        }
        Op::Alloc | Op::ArenaAlloc => {
            s.push_str(&val(inst.a));
            s.push_str(&val(inst.b));
        }
        Op::Free => s.push_str(&val(inst.a)),
        Op::CheckPre(_) | Op::CheckPost(_) | Op::CheckInv(_) => s.push_str(&val(inst.a)),
        // Both side-table lookups below guard against an out-of-range
        // index the same way `encode.rs::safe_remap` does: an arbitrary
        // `DeclFmir` is not guaranteed referentially consistent, and a
        // dump is diagnostic output, not something that should itself
        // panic over malformed input.
        Op::Intrinsic if (inst.a as usize) >= d.insts.calls.len() => {}
        Op::Intrinsic => {
            let call = &d.insts.calls[inst.a as usize];
            if let crate::inst::Callee::Intrinsic(sym) = call.callee {
                let _ = write!(s, " @{}", sym.0);
            }
            for arg in d.insts.args(call.args.clone()) {
                s.push_str(&val(arg.0));
            }
        }
        Op::Br => s.push_str(&bb(inst.a)),
        Op::CondBr => {
            s.push_str(&val(inst.a));
            s.push_str(&bb(inst.b));
            s.push_str(&bb(inst.c));
        }
        Op::SwitchDiscr if (inst.a as usize) >= d.insts.switches.len() => {}
        Op::SwitchDiscr => {
            let sw = &d.insts.switches[inst.a as usize];
            s.push_str(&val(sw.discr.0));
            s.push_str(&bb(sw.default.0));
            for arm in &d.insts.switch_arms[sw.arms.start as usize..sw.arms.end as usize] {
                let _ = write!(s, " {}:bb{}", arm.value, arm.target.0);
            }
        }
        Op::TryBr => {
            let _ = write!(s, " %inst{}", inst.a);
            s.push_str(&bb(inst.b));
            s.push_str(&bb(inst.c));
        }
        Op::Ret | Op::Raise => {
            if inst.a != crate::op::NO_OPERAND {
                s.push_str(&val(inst.a));
            }
        }
        Op::Trap => {
            let kind = crate::op::TrapKind::from_u32(inst.a)
                .map(|k| k.as_str())
                .unwrap_or("?");
            let _ = write!(s, " kind={kind}");
        }
        Op::Spawn | Op::Sync | Op::RegionEnter | Op::RegionExit => {
            let _ = write!(s, " r{}", inst.a);
        }
        _ => {}
    }
    s
}

fn dump_seed(d: &DeclFmir, alias_idx: usize, inst: InstRow) -> String {
    if !inst.op.is_memory_producing() || alias_idx == usize::MAX {
        return String::new();
    }
    match d.insts.aliases.get(alias_idx) {
        crate::alias::AliasSeed::None => String::new(),
        crate::alias::AliasSeed::Conv(c) => format!(" seed conv-{}", conv_str(c)),
        crate::alias::AliasSeed::Own(p) => format!(" seed own{}", place_root(d, p)),
        crate::alias::AliasSeed::Arena(b) => format!(" seed arena{}", b.0),
        crate::alias::AliasSeed::Split { parent, side } => {
            format!(" seed split{},{}", place_root(d, parent), side)
        }
    }
}

fn place_root(d: &DeclFmir, p: PlaceId) -> u32 {
    d.places.row(p).root
}
