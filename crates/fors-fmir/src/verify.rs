//! The structural verifier (design item 5 of the F0 task list): "the
//! structural verifier, returning source-located diagnostics." Every check
//! here is over ONE declaration's own pools — no cross-declaration analysis,
//! matching design §1.2's "FMIR must still represent them" scope for F0 and
//! ch05 Rule 3 ("FMIR MUST be the sole input" — the verifier does not read
//! anything this crate does not already hold).

use crate::alias::AliasSeed;
use crate::decl::DeclFmir;
use crate::diag::{Anchor, DiagCode, Diagnostic};
use crate::ids::ValId;
use crate::inst::InstRow;
use crate::op::Op;
use crate::region::RegionKind;

/// Runs every check and returns every diagnostic found (never stops at the
/// first one — a hand-written negative-corpus file may trip more than one
/// rule, and a caller deduping by [`DiagCode`] should still see every site).
pub fn verify(decl: &DeclFmir) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    check_secret_fields(decl, &mut out);
    check_terminators(decl, &mut out);
    check_tile_ops(decl, &mut out);
    check_alias_seeds(decl, &mut out);
    check_region_captures(decl, &mut out);
    check_reduce_shape(decl, &mut out);
    check_secret_propagation(decl, &mut out);
    check_secret_rejection(decl, &mut out);
    check_defer_bodies(decl, &mut out);
    check_exit_edges(decl, &mut out);
    out
}

/// Every `DeferRow.body` must be a real block whose own sub-CFG ends at
/// [`crate::scope::BODY_END`] and contains no `ret`/`raise`/`try_br`
/// (ch01 R23c: a body "MUST NOT contain `return`, `raise`, `?`"). A `trap`
/// inside a body IS legal — R23c's own escape is "an `else |e| { }` handler
/// that neither `raise`s nor `return`s: it yields the success value or
/// traps".
fn check_defer_bodies(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    let n_defers = decl.defers.len() as u32;
    for (i, row) in decl.defers.get(0..n_defers).iter().enumerate() {
        let body = row.body;
        if decl.blocks.try_row(body).is_none() {
            out.push(Diagnostic::new(
                DiagCode::DeferBodyMalformed,
                Anchor::Decl,
                format!("defer row {i} names block {} which does not exist", body.0),
            ));
            continue;
        }
        // Walk the body's own blocks. `BODY_END` is the stop; anything else
        // out of range, or a forbidden terminator, is a finding.
        let mut seen = vec![false; decl.blocks.len()];
        let mut stack = vec![body];
        let mut reaches_end = false;
        while let Some(b) = stack.pop() {
            if b == crate::scope::BODY_END {
                reaches_end = true;
                continue;
            }
            let Some(blk) = decl.blocks.try_row(b) else {
                out.push(Diagnostic::new(
                    DiagCode::DeferBodyMalformed,
                    Anchor::Block(body),
                    format!("defer row {i}'s body branches to missing block {}", b.0),
                ));
                continue;
            };
            if seen[b.index()] {
                continue;
            }
            seen[b.index()] = true;
            match blk.term.op {
                Op::Br => stack.push(crate::ids::BlockId(blk.term.a)),
                Op::CondBr => {
                    stack.push(crate::ids::BlockId(blk.term.b));
                    stack.push(crate::ids::BlockId(blk.term.c));
                }
                Op::SwitchDiscr => {
                    if let Some(sw) = decl.insts.switches.get(blk.term.a as usize) {
                        stack.push(sw.default);
                        let arms = &decl.insts.switch_arms[crate::inst::clamp_range(
                            sw.arms.clone(),
                            decl.insts.switch_arms.len(),
                        )];
                        for arm in arms {
                            stack.push(arm.target);
                        }
                    }
                }
                // ch01 R23c: none of these may appear inside a body.
                Op::Ret | Op::Raise | Op::TryBr => out.push(Diagnostic::new(
                    DiagCode::DeferBodyMalformed,
                    Anchor::Block(b),
                    format!(
                        "defer row {i}'s body reaches a `{:?}` terminator; ch01 R23c forbids \
                         `return`, `raise` and `?` inside a deferred body",
                        blk.term.op
                    ),
                )),
                // `trap` ends the process (ch02 R7) and `unreachable` ends
                // nothing: neither continues the body, and neither is a way
                // out of it.
                _ => {}
            }
        }
        if !reaches_end {
            out.push(Diagnostic::new(
                DiagCode::DeferBodyMalformed,
                Anchor::Block(body),
                format!(
                    "defer row {i}'s body never reaches `br BODY_END`, so the exit sequence \
                     could not resume after it"
                ),
            ));
        }
    }
}

/// design §3.8's verifier job — "asserting every exit edge of a scope
/// carries exactly the right multiset" — plus ch01 R22h's discharge records
/// (design §3.5: the interpreter "does **not** re-derive this ... but it
/// **asserts** it", and so does this).
fn check_exit_edges(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.exits.all_rows() {
        let Some(from) = decl.blocks.try_row(row.from) else {
            out.push(Diagnostic::new(
                DiagCode::Malformed,
                Anchor::Decl,
                format!("exit edge {} leaves missing block {}", id.0, row.from.0),
            ));
            continue;
        };

        // ch01 R23f / ch02 R7: a `trap` is not an exit.
        if from.term.op == Op::Trap {
            out.push(Diagnostic::new(
                DiagCode::TrapHasExitEdge,
                Anchor::Block(row.from),
                format!(
                    "exit edge {} leaves block {}, whose terminator is `trap`: a trap has no \
                     successor, runs no deferred body and discharges nothing",
                    id.0, row.from.0
                ),
            ));
        }

        // Exactly one row per `(from, to)`.
        if decl
            .exits
            .all_rows()
            .any(|(other, o)| other.0 < id.0 && o.from == row.from && o.to == row.to)
        {
            out.push(Diagnostic::new(
                DiagCode::ExitEdgeDuplicate,
                Anchor::Block(row.from),
                format!(
                    "two exit edges for ({} -> {})",
                    row.from.0,
                    if row.is_function_exit() {
                        "<return>".to_string()
                    } else {
                        row.to.0.to_string()
                    }
                ),
            ));
        }

        check_edge_shape(decl, id, &row, &from.term, out);
        check_edge_scopes(decl, id, &row, from.scope, out);
        check_edge_pending(decl, id, &row, out);
        check_edge_discharges(decl, id, &row, out);
    }
}

/// Is the edge's `scopes` list the chain `type-checker.md` §13 I8b step 2
/// runs — innermost FIRST? [`crate::exit::expected_pending`] takes the list
/// in the order carried, so without this an edge listing the scopes
/// outer-first, with a pending list to match, would pass the per-scope
/// multiset/order check and the interpreter would run the OUTER scope's
/// bodies before the inner's. The chain must start at the `from` block's
/// own scope, step to the parent each time, and (for a non-function exit)
/// stop at an ancestor of the `to` block's scope, i.e. leave exactly the
/// scopes between the two blocks.
fn check_edge_scopes(
    decl: &DeclFmir,
    id: crate::ids::ExitEdgeId,
    row: &crate::exit::ExitEdgeRow,
    from_scope: crate::ids::ScopeId,
    out: &mut Vec<Diagnostic>,
) {
    let leaving = decl.exits.scopes(row.scopes.clone());
    let mut reject = |why: String| {
        out.push(Diagnostic::new(
            DiagCode::ExitEdgeScopesNotAChain,
            Anchor::Block(row.from),
            format!("exit edge {}: {why}", id.0),
        ));
    };
    let Some(first) = leaving.first() else {
        return;
    };
    if *first != from_scope {
        reject(format!(
            "the scopes list starts at scope {} but block {} is in scope {} (innermost first)",
            first.0, row.from.0, from_scope.0
        ));
        return;
    }
    for pair in leaving.windows(2) {
        let (inner, next) = (pair[0], pair[1]);
        let parent = if inner.index() < decl.scopes.len() {
            decl.scopes.row(inner).parent
        } else {
            reject(format!("scope {} does not exist", inner.0));
            return;
        };
        if next != parent {
            reject(format!(
                "scope {} follows scope {} in the list but is not its parent ({}); the list must \
                 be the parent chain, innermost first",
                next.0, inner.0, parent.0
            ));
            return;
        }
    }
    let last = *leaving.last().expect("non-empty");
    if last.index() >= decl.scopes.len() {
        reject(format!("scope {} does not exist", last.0));
        return;
    }
    if row.is_function_exit() {
        return;
    }
    // The first scope NOT left must contain `to`.
    let stop = decl.scopes.row(last).parent;
    let Some(to) = decl.blocks.try_row(row.to) else {
        return; // `check_edge_shape` reports the missing successor.
    };
    let mut s = to.scope;
    loop {
        if s == stop {
            return;
        }
        if s.index() >= decl.scopes.len() {
            break;
        }
        s = decl.scopes.row(s).parent;
    }
    reject(format!(
        "the list leaves scopes up to {} but block {} is in scope {}, which is not inside scope {}",
        last.0,
        row.to.0,
        to.scope.0,
        if stop.0 == crate::ids::ABSENT {
            "<root>".to_string()
        } else {
            stop.0.to_string()
        }
    ));
}

/// Is `to` a successor of `from`'s terminator, and is the edge's `kind` the
/// one ch02 R16 gives that successor?
fn check_edge_shape(
    decl: &DeclFmir,
    id: crate::ids::ExitEdgeId,
    row: &crate::exit::ExitEdgeRow,
    term: &InstRow,
    out: &mut Vec<Diagnostic>,
) {
    use crate::exit::ExitKind;
    let function_exit = row.is_function_exit();
    let (ok_successor, want_kind) = match term.op {
        Op::Ret => (function_exit, Some(ExitKind::Normal)),
        Op::Raise => (function_exit, Some(ExitKind::Error)),
        Op::Br => (row.to.0 == term.a, Some(ExitKind::Normal)),
        Op::CondBr => (row.to.0 == term.b || row.to.0 == term.c, None),
        Op::TryBr if row.to.0 == term.b => (true, Some(ExitKind::Normal)),
        Op::TryBr if row.to.0 == term.c => (true, Some(ExitKind::Error)),
        Op::TryBr => (false, None),
        Op::SwitchDiscr => {
            let targets: Vec<u32> = match decl.insts.switches.get(term.a as usize) {
                Some(sw) => {
                    let arms = &decl.insts.switch_arms
                        [crate::inst::clamp_range(sw.arms.clone(), decl.insts.switch_arms.len())];
                    std::iter::once(sw.default.0)
                        .chain(arms.iter().map(|a| a.target.0))
                        .collect()
                }
                None => Vec::new(),
            };
            (targets.contains(&row.to.0), Some(ExitKind::Normal))
        }
        // `trap`/`unreachable` have no successors at all; the `trap` case is
        // already reported with its own code.
        _ => (false, None),
    };
    if !ok_successor && term.op != Op::Trap {
        out.push(Diagnostic::new(
            DiagCode::ExitEdgeNotASuccessor,
            Anchor::Block(row.from),
            format!(
                "exit edge {} names a `to` that block {}'s `{:?}` terminator does not branch to",
                id.0, row.from.0, term.op
            ),
        ));
    }
    if let Some(want) = want_kind
        && row.kind != want
        && ok_successor
    {
        out.push(Diagnostic::new(
            DiagCode::ExitEdgeWrongKind,
            Anchor::Block(row.from),
            format!(
                "exit edge {} is marked `{}` but a `{:?}` edge is a `{}` exit (ch02 R16)",
                id.0,
                row.kind.as_str(),
                term.op,
                want.as_str()
            ),
        ));
    }
}

fn check_edge_pending(
    decl: &DeclFmir,
    id: crate::ids::ExitEdgeId,
    row: &crate::exit::ExitEdgeRow,
    out: &mut Vec<Diagnostic>,
) {
    let leaving = decl.exits.scopes(row.scopes.clone());
    let want = crate::exit::expected_pending(&decl.scopes, &decl.defers, leaving, row.kind);
    let got = decl.exits.pending(row.pending.clone()).to_vec();
    if got == want {
        return;
    }
    let mut want_sorted = want.clone();
    let mut got_sorted = got.clone();
    want_sorted.sort();
    got_sorted.sort();
    let code = if want_sorted == got_sorted {
        DiagCode::ExitEdgeWrongPendingOrder
    } else {
        DiagCode::ExitEdgeWrongPendingMultiset
    };
    out.push(Diagnostic::new(
        code,
        Anchor::Block(row.from),
        format!(
            "exit edge {} carries pending bodies {:?} but the {} exit of scopes {:?} runs {:?} \
             (ch01 R23a reverse textual order, R23b `errdefer` only on an error exit)",
            id.0,
            got.iter().map(|d| d.0).collect::<Vec<_>>(),
            row.kind.as_str(),
            leaving.iter().map(|s| s.0).collect::<Vec<_>>(),
            want.iter().map(|d| d.0).collect::<Vec<_>>(),
        ),
    ));
}

fn check_edge_discharges(
    decl: &DeclFmir,
    id: crate::ids::ExitEdgeId,
    row: &crate::exit::ExitEdgeRow,
    out: &mut Vec<Diagnostic>,
) {
    let leaving = decl.exits.scopes(row.scopes.clone());
    let mut obligations: Vec<crate::ids::PlaceId> = Vec::new();
    for scope in leaving {
        if scope.index() >= decl.scopes.len() {
            continue;
        }
        obligations.extend_from_slice(decl.obligations.get(decl.scopes.row(*scope).obligations));
    }
    let discharges = decl.exits.discharges(row.discharges.clone());
    for (i, d) in discharges.iter().enumerate() {
        if !obligations.contains(&d.place) {
            out.push(Diagnostic::new(
                DiagCode::ExitEdgeUnknownDischarge,
                Anchor::Block(row.from),
                format!(
                    "exit edge {}'s discharge {i} names place {}, which is not an obligation of \
                     any scope this edge leaves",
                    id.0, d.place.0
                ),
            ));
        }
        if discharges[..i].iter().any(|e| e.place == d.place) {
            out.push(Diagnostic::new(
                DiagCode::ExitEdgeDuplicateDischarge,
                Anchor::Block(row.from),
                format!(
                    "exit edge {} discharges place {} twice (design §5.2's `ub: double-consume`)",
                    id.0, d.place.0
                ),
            ));
        }
    }
    for place in &obligations {
        if !discharges.iter().any(|d| d.place == *place) {
            out.push(Diagnostic::new(
                DiagCode::ExitEdgeMissingDischarge,
                Anchor::Block(row.from),
                format!(
                    "exit edge {} leaves place {} with an undischarged linear obligation (ch01 \
                     R22h); the interpreter reports this as `ub: linear-leak`, never a trap",
                    id.0, place.0
                ),
            ));
        }
    }
}

pub fn is_ok(decl: &DeclFmir) -> bool {
    verify(decl).is_empty()
}

/// Is `v` secret? `v` comes from an instruction's raw `a`/`b`/`c` slot, which
/// arbitrary FMIR may leave dangling; a value that does not exist is not
/// secret, so the ch05 Rule 6b checks below simply find nothing to reject
/// rather than panicking (F0 has no "operand out of range" diagnostic — see
/// `check_one_secret_rejection`'s `Op::Intrinsic` arm for the same rule).
fn is_secret(decl: &DeclFmir, v: ValId) -> bool {
    decl.vals.try_row(v).is_some_and(|row| row.is_secret())
}

fn val_or_none(raw: u32) -> Option<ValId> {
    if raw == crate::op::NO_OPERAND {
        None
    } else {
        Some(ValId(raw))
    }
}

/// ch05 Rule 6: "Every FMIR/OIR/LIR value MUST carry a secret bit and
/// `ct_region` id as non-optional fields; `--verify-each` MUST reject any
/// lacking them." The safe builder can never produce a row lacking either
/// (`ValRow::new` takes both as required arguments); this check exists for
/// the textual/parsed path, which can (design §1, `flags.rs`,
/// `SECRET_UNSPECIFIED`/`CT_UNSPECIFIED`).
fn check_secret_fields(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.vals.all_rows() {
        if row.flags.is_secret_unspecified() {
            out.push(Diagnostic::new(
                DiagCode::MissingSecretField,
                Anchor::Val(id),
                "value has no secret field",
            ));
        }
        if row.ct == crate::flags::CT_UNSPECIFIED {
            out.push(Diagnostic::new(
                DiagCode::MissingCtRegion,
                Anchor::Val(id),
                "value has no ct_region field",
            ));
        }
    }
}

/// `verify_rejects_two_terminators`: a terminator-class [`Op`] found among a
/// block's *regular* instructions (i.e. anywhere other than `term`) — see
/// `block.rs`'s module docs for why this is how "two terminators" is
/// constructible at all.
fn check_terminators(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, _row) in decl.blocks.all_rows() {
        for stray in decl.blocks.stray_terminator_indices(id, &decl.insts) {
            out.push(Diagnostic::new(
                DiagCode::TwoTerminators,
                Anchor::Inst(crate::ids::InstId(stray)),
                "block has a terminator-class op outside its `term` slot (two terminators)",
            ));
        }
        let term_op = decl.blocks.row(id).term.op;
        if !term_op.is_terminator() {
            out.push(Diagnostic::new(
                DiagCode::TwoTerminators,
                Anchor::Block(id),
                "block's `term` slot does not hold a terminator opcode",
            ));
        }
    }
}

/// `verify_rejects_tile_op`: `tile.*` "MUST appear only in FMIR" (ch05 Rule
/// 12) but M1 defines no `tile.*` opcode at all (design §1.2) — any
/// [`Op::TileOp`] found anywhere is rejected uniformly, terminator slot or
/// not.
fn check_tile_ops(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        if row.op == Op::TileOp {
            out.push(Diagnostic::new(
                DiagCode::TileOpPresent,
                Anchor::Inst(id),
                "tile.* is not defined before M6",
            ));
        }
    }
    for (id, row) in decl.blocks.all_rows() {
        if row.term.op == Op::TileOp {
            out.push(Diagnostic::new(
                DiagCode::TileOpPresent,
                Anchor::Block(id),
                "tile.* is not defined before M6",
            ));
        }
    }
}

/// `alias_seed_present_on_every_memory_op` (design §3.4a, ch05 Rule 5): every
/// [`Op::is_memory_producing`] row must carry a seed other than
/// [`AliasSeed::None`].
fn check_alias_seeds(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        if row.op.is_memory_producing() && decl.insts.aliases.get(id.index()) == AliasSeed::None {
            out.push(Diagnostic::new(
                DiagCode::MemoryOpMissingAliasSeed,
                Anchor::Inst(id),
                "memory-producing instruction has no alias seed",
            ));
        }
    }
}

/// ch03 R11/R12 (as reworded by owner decision Q3, 2026-10-02): a
/// `reduce_tree` instruction carries its shape parameters as LITERAL
/// operands, so the shape is fixed in FMIR before parallel lowering. The
/// verifier is where "the shape is a pure function of `(n, B, L)`" stops
/// being a comment: `b`/`l` must be exactly ch03's named constants (neither
/// is overridable), and the row index must exist.
fn check_reduce_shape(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        if row.op != Op::ReduceTree {
            continue;
        }
        let Some(red) = decl.insts.reduces.get(row.a as usize) else {
            out.push(Diagnostic::new(
                DiagCode::Malformed,
                Anchor::Inst(id),
                "reduce_tree names no reduce row",
            ));
            continue;
        };
        if red.b != crate::reduce::REDUCE_BLOCK || red.l != crate::reduce::REDUCE_LANES {
            out.push(Diagnostic::new(
                DiagCode::Malformed,
                Anchor::Inst(id),
                "reduce_tree must carry REDUCE_BLOCK = 256 and REDUCE_LANES = 8 \
                 (ch03 Rule 11: neither is overridable)",
            ));
        }
        if decl.vals.try_row(red.xs).is_none() {
            out.push(Diagnostic::new(
                DiagCode::Malformed,
                Anchor::Inst(id),
                "reduce_tree's operand sequence is not a value of this body",
            ));
        }
        if red.identity.0 != crate::ids::ABSENT && decl.vals.try_row(red.identity).is_none() {
            out.push(Diagnostic::new(
                DiagCode::Malformed,
                Anchor::Inst(id),
                "reduce_tree's identity is not a value of this body",
            ));
        }
    }
}

/// `verify_rejects_detach_without_captures` (ch05 Rule 9). See `region.rs`'s
/// module docs for why "detach" means an FMIR `spawn` region here.
fn check_region_captures(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.regions.all_rows() {
        if row.kind == RegionKind::Spawn && row.captures_absent() {
            out.push(Diagnostic::new(
                DiagCode::DetachWithoutCaptures,
                region_anchor(decl, id),
                format!("spawn region {} has no capture list", id.0),
            ));
        }
    }
}

/// Where to point a reader at a [`crate::ids::RegionId`]. A `RegionRow` has no
/// `SiteId` of its own (design §3.7 gives it none), but the `spawn`/
/// `region_enter` instruction that opens it does — that instruction carries
/// the region id in slot `a` (`op.rs`'s operand table), so the diagnostic
/// anchors to it and resolves to a real source site. `Anchor::Decl` remains
/// the fallback for a region no instruction opens, which is itself only
/// reachable in a hand-written fixture.
fn region_anchor(decl: &DeclFmir, region: crate::ids::RegionId) -> Anchor {
    decl.insts
        .all_rows()
        .find(|(_, row)| matches!(row.op, Op::Spawn | Op::RegionEnter) && row.a == region.0)
        .map(|(id, _)| Anchor::Inst(id))
        .unwrap_or(Anchor::Decl)
}

/// The value-to-value operands of `op` that ch05 Rule 6a's propagation
/// invariant applies to: "the result of any operation with a secret operand
/// is secret". Scoped to instructions whose operands are genuinely `ValId`s
/// (arithmetic, logic, conversion, aggregate construction, projection) —
/// `move_from`/`copy_from`/`init`/`borrow*`/calls read a *place* or invoke a
/// *callee*, which R6a's "local FMIR type rule" wording does not extend to
/// without a flow analysis this crate does not perform. [decision: see
/// `verify.rs`'s module docs and the `decisions` list for the full
/// rationale]
fn propagation_operands(op: Op, row: &InstRow, decl: &DeclFmir) -> Vec<ValId> {
    match op {
        Op::Add(_)
        | Op::Sub(_)
        | Op::Mul(_)
        | Op::Div(_)
        | Op::Rem(_)
        | Op::Shl(_)
        | Op::Shr(_)
        | Op::Neg(_) => [val_or_none(row.a), val_or_none(row.b)]
            .into_iter()
            .flatten()
            .collect(),
        Op::Fadd(_) | Op::Fsub(_) | Op::Fmul(_) | Op::Fdiv(_) | Op::Frem(_) | Op::Fneg(_) => {
            [val_or_none(row.a), val_or_none(row.b)]
                .into_iter()
                .flatten()
                .collect()
        }
        Op::Icmp(_) | Op::Fcmp(_) | Op::And | Op::Or | Op::Xor | Op::Not => {
            [val_or_none(row.a), val_or_none(row.b)]
                .into_iter()
                .flatten()
                .collect()
        }
        Op::ConvChecked | Op::ConvWrap | Op::ConvSat | Op::ConvTrunc => {
            [val_or_none(row.a)].into_iter().flatten().collect()
        }
        Op::Field | Op::Discr | Op::Payload => [val_or_none(row.a)].into_iter().flatten().collect(),
        Op::AggNew | Op::TupleNew => decl.insts.args(row.a..row.b).to_vec(),
        Op::VariantNew => decl.insts.args(row.a..row.b).to_vec(),
        _ => Vec::new(),
    }
}

/// `secret_propagates`: checks the ch05 Rule 6a invariant already holds,
/// rather than computing it (`fors-lower` computes it — design §3.11).
fn check_secret_propagation(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    for (id, row) in decl.insts.all_rows() {
        let operands = propagation_operands(row.op, &row, decl);
        if operands.is_empty() {
            continue;
        }
        let any_secret = operands.iter().any(|v| is_secret(decl, *v));
        if !any_secret {
            continue;
        }
        // The instruction's *result* is the value whose `def` names this
        // instruction (design §3.1: "def: u32, // defining instruction").
        let result_secret = decl
            .vals
            .all_rows()
            .find(|(_, v)| matches!(v.def(), crate::value::ValDef::Inst(inst) if inst == id))
            .map(|(_, v)| v.is_secret());
        if let Some(false) = result_secret {
            out.push(Diagnostic::new(
                DiagCode::SecretPropagationViolated,
                Anchor::Inst(id),
                "result is not secret despite a secret operand (ch05 Rule 6a)",
            ));
        }
    }
}

/// ch05 Rule 6b's rejection list, as far as design §3.11 assigns it to this
/// crate: branch/index/trapping-op/contract/raise/intrinsic on secret, and
/// `declassify` outside `@unsafe(invariant:)`.
fn check_secret_rejection(decl: &DeclFmir, out: &mut Vec<Diagnostic>) {
    // Regular instructions.
    for (id, row) in decl.insts.all_rows() {
        check_one_secret_rejection(decl, Anchor::Inst(id), row.op, row, out);
    }
    // Terminators (which live in `BlockRow.term`, not `InstPool` — see
    // `block.rs`).
    for (block_id, block) in decl.blocks.all_rows() {
        let row = block.term;
        check_one_secret_rejection(decl, Anchor::Block(block_id), row.op, row, out);
        if row.op == Op::CondBr
            && let Some(cond) = val_or_none(row.a)
            && is_secret(decl, cond)
        {
            let leads_to_raise = [row.b, row.c].into_iter().any(|bb| {
                bb != crate::op::NO_OPERAND
                    && decl
                        .blocks
                        .try_row(crate::ids::BlockId(bb))
                        .is_some_and(|target| target.term.op == Op::Raise)
            });
            if leads_to_raise {
                out.push(Diagnostic::new(
                    DiagCode::SecretRaiseCondition,
                    Anchor::Block(block_id),
                    "raise is reached only through a secret-derived branch",
                ));
            }
        }
    }
}

fn check_one_secret_rejection(
    decl: &DeclFmir,
    at: Anchor,
    op: Op,
    row: InstRow,
    out: &mut Vec<Diagnostic>,
) {
    match op {
        Op::CondBr | Op::SwitchDiscr => {
            if let Some(cond) = val_or_none(row.a)
                && is_secret(decl, cond)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretBranchOrIndex,
                    at,
                    "branch on a secret operand",
                ));
            }
        }
        Op::Index => {
            if let Some(idx) = val_or_none(row.b)
                && is_secret(decl, idx)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretBranchOrIndex,
                    at,
                    "index derived from secret",
                ));
            }
        }
        Op::SliceRange => {
            for bound in [row.b, row.c] {
                if let Some(v) = val_or_none(bound)
                    && is_secret(decl, v)
                {
                    out.push(Diagnostic::new(
                        DiagCode::SecretBranchOrIndex,
                        at,
                        "slice bound derived from secret",
                    ));
                }
            }
        }
        _ if op.is_secret_rejected_trapping_op() => {
            for slot in [row.a, row.b] {
                if let Some(v) = val_or_none(slot)
                    && is_secret(decl, v)
                {
                    out.push(Diagnostic::new(
                        DiagCode::SecretTrappingOp,
                        at,
                        "trapping arithmetic (or conv_checked) on a secret operand: use wrap_/sat_/unchecked_",
                    ));
                    break;
                }
            }
        }
        _ if op.is_contract_check() => {
            if let Some(cond) = val_or_none(row.a)
                && is_secret(decl, cond)
            {
                out.push(Diagnostic::new(
                    DiagCode::SecretInContractCheck,
                    at,
                    "contract check on a secret operand",
                ));
            }
        }
        Op::Raise => {
            // The payload itself MAY be secret (design §3.11: "A secret
            // error payload is accepted and stays secret"); only a
            // secret-conditioned *reachability* of this terminator is
            // rejected, checked from the upstream `cond_br` in
            // `check_secret_rejection` above.
        }
        // A `row.a` past the end of `calls` is a different malformation
        // than anything ch05 Rule 6b names; nothing else in this crate's
        // `verify()` is positioned to report it either (there is no generic
        // "side-table index out of range" diagnostic at F0), so this arm
        // simply has no secret argument to find rather than panicking —
        // consistent with `encode.rs::safe_remap`'s "stay total, don't
        // crash on a malformed `DeclFmir`" rule.
        Op::Intrinsic if (row.a as usize) >= decl.insts.calls.len() => {}
        Op::Intrinsic => {
            let call = &decl.insts.calls[row.a as usize];
            if op.is_host_intrinsic() {
                for arg in decl.insts.args(call.args.clone()) {
                    if is_secret(decl, *arg) {
                        out.push(Diagnostic::new(
                            DiagCode::SecretIntrinsicArg,
                            at,
                            "secret argument to a host-effecting intrinsic",
                        ));
                        break;
                    }
                }
            }
        }
        Op::Declassify if !decl.is_unsafe_invariant => {
            out.push(Diagnostic::new(
                DiagCode::DeclassifyRequiresUnsafe,
                at,
                "declassify outside @unsafe(invariant: ...)",
            ));
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block::BlockRow;
    use crate::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};
    use crate::inst::InstRow;
    use crate::op::ArithMode;
    use crate::value::{ValDef, ValRow};
    use fors_fir::defpath::DeclKeyId;
    use fors_fir::sig::FnSigId;
    use fors_fir::ty::TY_UNIT;

    fn plain(op: Op) -> InstRow {
        InstRow {
            op,
            a: crate::op::NO_OPERAND,
            b: crate::op::NO_OPERAND,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        }
    }

    #[test]
    fn empty_well_formed_decl_is_ok() {
        let decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn missing_secret_field_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut row = ValRow::new(TY_UNIT, false, 0, ValDef::Param(0));
        row.flags = ValFlags(SECRET_UNSPECIFIED);
        decl.push_val(row);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::MissingSecretField),
            "{diags:?}"
        );
    }

    #[test]
    fn missing_ct_region_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let row = ValRow {
            ty: TY_UNIT,
            flags: ValFlags::new(false),
            ct: CT_UNSPECIFIED,
            def: 0,
        };
        decl.push_val(row);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::MissingCtRegion),
            "{diags:?}"
        );
    }

    #[test]
    fn secret_add_rejected_unless_result_marked_secret() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
        let add = InstRow {
            op: Op::Add(ArithMode::Trap),
            a: secret.0,
            b: one.0,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        };
        let add_id = decl.push_inst(add, AliasSeed::None);
        // Result NOT marked secret: violates ch05 Rule 6a.
        decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Inst(add_id)));
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::SecretPropagationViolated),
            "{diags:?}"
        );
    }

    #[test]
    fn secret_add_accepted_when_result_is_marked_secret() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
        // `Wrap`, not the default `Trap` mode: ch05 Rule 6b rejects a
        // *trapping* op on a secret operand outright (`secret_trapping_add_
        // is_rejected_but_wrap_add_is_accepted` below covers that). This
        // test isolates Rule 6a's propagation-acceptance question alone.
        let add = InstRow {
            op: Op::Add(ArithMode::Wrap),
            a: secret.0,
            b: one.0,
            c: crate::op::NO_OPERAND,
            ty: TY_UNIT,
            site: crate::ids::SiteId(0),
        };
        let add_id = decl.push_inst(add, AliasSeed::None);
        decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Inst(add_id)));
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn secret_trapping_add_is_rejected_but_wrap_add_is_accepted() {
        for (mode, expect_ok) in [(ArithMode::Trap, false), (ArithMode::Wrap, true)] {
            let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
            let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
            let one = decl.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(1)));
            let add = InstRow {
                op: Op::Add(mode),
                a: secret.0,
                b: one.0,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            };
            let add_id = decl.push_inst(add, AliasSeed::None);
            decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Inst(add_id)));
            let diags = verify(&decl);
            let has_trapping_diag = diags.iter().any(|d| d.code == DiagCode::SecretTrappingOp);
            assert_eq!(!has_trapping_diag, expect_ok, "mode {mode:?}: {diags:?}");
        }
    }

    #[test]
    fn branch_on_secret_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let secret_cond = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        let target = decl.blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Unreachable),
            scope: crate::ids::ScopeId(0),
        });
        decl.entry = decl.blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: InstRow {
                op: Op::CondBr,
                a: secret_cond.0,
                b: target.0,
                c: target.0,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            },
            scope: crate::ids::ScopeId(0),
        });
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::SecretBranchOrIndex),
            "{diags:?}"
        );
    }

    #[test]
    fn declassify_outside_unsafe_is_rejected_but_accepted_inside_it() {
        for (is_unsafe, expect_ok) in [(false, false), (true, true)] {
            let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
            decl.is_unsafe_invariant = is_unsafe;
            let secret = decl.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
            let inst = InstRow {
                op: Op::Declassify,
                a: secret.0,
                b: crate::op::NO_OPERAND,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            };
            decl.push_inst(inst, AliasSeed::None);
            let diags = verify(&decl);
            let rejected = diags
                .iter()
                .any(|d| d.code == DiagCode::DeclassifyRequiresUnsafe);
            assert_eq!(!rejected, expect_ok, "is_unsafe={is_unsafe}: {diags:?}");
        }
    }

    #[test]
    fn tile_op_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.push_inst(plain(Op::TileOp), AliasSeed::None);
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::TileOpPresent),
            "{diags:?}"
        );
    }

    #[test]
    fn two_terminators_in_one_block_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        // Smuggle a terminator-class op into the entry block's regular range
        // in addition to its real `term`.
        let stray = decl.insts.push(plain(Op::Ret), AliasSeed::None);
        assert_eq!(stray.0, 0);
        let mut entry = decl.blocks.row(decl.entry);
        entry.first_inst = 0;
        entry.inst_len = 1;
        // Rebuild the block pool with the corrected row (there is no
        // in-place mutator by design — pools are append-only elsewhere).
        let mut blocks = crate::block::BlockPool::new();
        let new_entry = blocks.push(entry);
        decl.blocks = blocks;
        decl.entry = new_entry;
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::TwoTerminators),
            "{diags:?}"
        );
    }

    #[test]
    fn memory_op_without_alias_seed_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.push_inst(plain(Op::Alloc), AliasSeed::None);
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::MemoryOpMissingAliasSeed),
            "{diags:?}"
        );
    }

    #[test]
    fn spawn_region_without_captures_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.regions.push(crate::region::RegionRow {
            kind: RegionKind::Spawn,
            captures: crate::region::RegionRow::ABSENT_CAPTURES,
            brand: crate::ids::BrandId::NONE,
        });
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::DetachWithoutCaptures),
            "{diags:?}"
        );
    }

    #[test]
    fn spawn_region_with_an_explicit_empty_capture_list_is_accepted() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.regions.push(crate::region::RegionRow {
            kind: RegionKind::Spawn,
            captures: 0..0,
            brand: crate::ids::BrandId::NONE,
        });
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }
    // -- F4/F6: exit edges, deferred bodies, obligations -------------------

    /// A `DeclFmir` with: one scope holding `defer`(0), `errdefer`(1),
    /// `defer`(2) whose bodies are blocks 1..=3, an entry block (0)
    /// terminated `ret`, and one obligation on place 0.
    fn with_defers_and_obligation() -> (DeclFmir, crate::ids::ScopeId, Vec<crate::ids::DeferId>) {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let place = decl.places.intern(0, &[], TY_UNIT);
        // Blocks: 0 = entry (`ret`), 1..=3 = bodies (`br BODY_END`).
        let mut blocks = crate::block::BlockPool::new();
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Ret),
            scope: crate::ids::ScopeId(1),
        });
        for _ in 0..3 {
            let mut term = plain(Op::Br);
            term.a = crate::scope::BODY_END.0;
            blocks.push(BlockRow {
                first_inst: 0,
                inst_len: 0,
                term,
                scope: crate::ids::ScopeId(1),
            });
        }
        decl.blocks = blocks;
        decl.entry = crate::ids::BlockId(0);

        let mut ids = Vec::new();
        for (i, kind) in [
            crate::scope::DeferKind::Defer,
            crate::scope::DeferKind::ErrDefer,
            crate::scope::DeferKind::Defer,
        ]
        .into_iter()
        .enumerate()
        {
            ids.push(decl.defers.push(crate::scope::DeferRow {
                kind,
                body: crate::ids::BlockId(1 + i as u32),
                stmt_order: i as u16,
            }));
        }
        let obligations = decl.obligations.push_list(&[place]);
        let scope = decl.scopes.push(crate::scope::ScopeRow {
            parent: crate::ids::ScopeId(0),
            brand: crate::ids::BrandId::NONE,
            defers: 0..3,
            obligations,
            region: crate::ids::RegionId::NONE,
        });
        assert_eq!(scope.0, 1);
        (decl, scope, ids)
    }

    fn push_edge(
        decl: &mut DeclFmir,
        kind: crate::exit::ExitKind,
        scope: crate::ids::ScopeId,
        pending: &[crate::ids::DeferId],
        discharges: &[crate::exit::DischargeRow],
    ) {
        let scopes = decl.exits.push_scopes(&[scope]);
        let pending = decl.exits.push_pending(pending);
        let discharges = decl.exits.push_discharges(discharges);
        let mut row = crate::exit::ExitEdgeRow::plain(
            crate::ids::BlockId(0),
            crate::ids::BlockId::NONE,
            kind,
        );
        row.scopes = scopes;
        row.pending = pending;
        row.discharges = discharges;
        decl.exits.push(row);
    }

    fn returned(place: crate::ids::PlaceId) -> crate::exit::DischargeRow {
        crate::exit::DischargeRow {
            place,
            how: crate::scope::Discharge::Returned,
        }
    }

    #[test]
    fn a_correct_exit_edge_is_accepted() {
        // The multiset ch01 R23a/R23b require on a NORMAL exit: reverse
        // statement order, the `errdefer` skipped.
        let (mut decl, scope, ids) = with_defers_and_obligation();
        let place = crate::ids::PlaceId(0);
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[2], ids[0]],
            &[returned(place)],
        );
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn an_exit_edge_with_the_wrong_multiset_is_rejected() {
        // The `errdefer` carried on a normal exit (ch01 R23b forbids it).
        let (mut decl, scope, ids) = with_defers_and_obligation();
        let place = crate::ids::PlaceId(0);
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[2], ids[1], ids[0]],
            &[returned(place)],
        );
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeWrongPendingMultiset),
            "{diags:?}"
        );
    }

    #[test]
    fn an_exit_edge_with_the_right_multiset_in_the_wrong_order_is_rejected() {
        // ch01 R23a's reverse textual order is not a suggestion.
        let (mut decl, scope, ids) = with_defers_and_obligation();
        let place = crate::ids::PlaceId(0);
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[0], ids[2]],
            &[returned(place)],
        );
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeWrongPendingOrder),
            "{diags:?}"
        );
    }

    #[test]
    fn an_error_exit_interleaves_the_errdefer_in_one_reverse_sequence() {
        let (mut decl, scope, ids) = with_defers_and_obligation();
        let place = crate::ids::PlaceId(0);
        // `raise`, so the edge really is an error exit (ch02 R16).
        let mut blocks = crate::block::BlockPool::new();
        for (i, row) in decl.blocks.all_rows() {
            let mut row = row;
            if i.0 == 0 {
                row.term = plain(Op::Raise);
            }
            blocks.push(row);
        }
        decl.blocks = blocks;
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Error,
            scope,
            &[ids[2], ids[1], ids[0]],
            &[returned(place)],
        );
        assert!(is_ok(&decl), "{:?}", verify(&decl));
    }

    #[test]
    fn an_undischarged_obligation_on_an_exit_edge_is_rejected() {
        // ch01 R22h, statically. The interpreter reports the same condition
        // as `ub: linear-leak` (design §3.5, §5.2) — never a trap.
        let (mut decl, scope, ids) = with_defers_and_obligation();
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[2], ids[0]],
            &[],
        );
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeMissingDischarge),
            "{diags:?}"
        );
    }

    #[test]
    fn discharging_one_obligation_twice_is_rejected() {
        let (mut decl, scope, ids) = with_defers_and_obligation();
        let place = crate::ids::PlaceId(0);
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[2], ids[0]],
            &[returned(place), returned(place)],
        );
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeDuplicateDischarge),
            "{diags:?}"
        );
    }

    #[test]
    fn a_discharge_for_a_place_no_scope_owes_is_rejected() {
        let (mut decl, scope, ids) = with_defers_and_obligation();
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[ids[2], ids[0]],
            &[
                returned(crate::ids::PlaceId(0)),
                returned(crate::ids::PlaceId(7)),
            ],
        );
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeUnknownDischarge),
            "{diags:?}"
        );
    }

    #[test]
    fn a_trap_terminated_block_may_carry_no_exit_edge() {
        // ch01 R23f, R22d, ch02 R7: a trap is NOT an exit — no successor, no
        // body, no discharge.
        let (mut decl, scope, _) = with_defers_and_obligation();
        let mut blocks = crate::block::BlockPool::new();
        for (i, row) in decl.blocks.all_rows() {
            let mut row = row;
            if i.0 == 0 {
                row.term = plain(Op::Trap);
            }
            blocks.push(row);
        }
        decl.blocks = blocks;
        push_edge(
            &mut decl,
            crate::exit::ExitKind::Normal,
            scope,
            &[],
            &[returned(crate::ids::PlaceId(0))],
        );
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::TrapHasExitEdge),
            "{diags:?}"
        );
    }

    #[test]
    fn a_raise_edge_marked_normal_is_rejected() {
        let (mut decl, scope, _) = with_defers_and_obligation();
        let mut blocks = crate::block::BlockPool::new();
        for (i, row) in decl.blocks.all_rows() {
            let mut row = row;
            if i.0 == 0 {
                row.term = plain(Op::Raise);
            }
            blocks.push(row);
        }
        decl.blocks = blocks;
        // An empty scope list keeps the pending check quiet, isolating the
        // kind check.
        let scopes = decl.exits.push_scopes(&[]);
        let mut row = crate::exit::ExitEdgeRow::plain(
            crate::ids::BlockId(0),
            crate::ids::BlockId::NONE,
            crate::exit::ExitKind::Normal,
        );
        row.scopes = scopes;
        decl.exits.push(row);
        let _ = scope;
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::ExitEdgeWrongKind),
            "{diags:?}"
        );
    }

    /// `type-checker.md` §13 I8b step 2's "innermost scope first" is a
    /// property of the edge's `scopes` LIST, which `expected_pending` takes
    /// as given — so it is asserted here: the list must start at the `from`
    /// block's own scope and step to the parent each time.
    #[test]
    fn an_exit_edge_whose_scopes_are_not_the_innermost_first_chain_is_rejected() {
        // Block 0 is in scope 1, whose parent is scope 0. Listing the parent
        // first, or starting at the parent, is not the chain.
        for scopes in [
            vec![crate::ids::ScopeId(0), crate::ids::ScopeId(1)],
            vec![crate::ids::ScopeId(0)],
        ] {
            let (mut decl, _, _) = with_defers_and_obligation();
            let range = decl.exits.push_scopes(&scopes);
            let mut row = crate::exit::ExitEdgeRow::plain(
                crate::ids::BlockId(0),
                crate::ids::BlockId::NONE,
                crate::exit::ExitKind::Normal,
            );
            row.scopes = range;
            decl.exits.push(row);
            let diags = verify(&decl);
            assert!(
                diags
                    .iter()
                    .any(|d| d.code == DiagCode::ExitEdgeScopesNotAChain),
                "{scopes:?}: {diags:?}"
            );
        }
        // The chain itself is accepted by this check (the edge then fails
        // only on its missing pending list and discharge).
        let (mut decl, _, _) = with_defers_and_obligation();
        let range = decl
            .exits
            .push_scopes(&[crate::ids::ScopeId(1), crate::ids::ScopeId(0)]);
        let mut row = crate::exit::ExitEdgeRow::plain(
            crate::ids::BlockId(0),
            crate::ids::BlockId::NONE,
            crate::exit::ExitKind::Normal,
        );
        row.scopes = range;
        decl.exits.push(row);
        let diags = verify(&decl);
        assert!(
            !diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeScopesNotAChain),
            "{diags:?}"
        );
    }

    #[test]
    fn an_exit_edge_to_a_block_the_terminator_does_not_branch_to_is_rejected() {
        let (mut decl, _, _) = with_defers_and_obligation();
        let scopes = decl.exits.push_scopes(&[]);
        let mut row = crate::exit::ExitEdgeRow::plain(
            crate::ids::BlockId(0),
            crate::ids::BlockId(2),
            crate::exit::ExitKind::Normal,
        );
        row.scopes = scopes;
        decl.exits.push(row);
        let diags = verify(&decl);
        assert!(
            diags
                .iter()
                .any(|d| d.code == DiagCode::ExitEdgeNotASuccessor),
            "{diags:?}"
        );
    }

    #[test]
    fn two_edges_for_one_from_to_pair_are_rejected() {
        let (mut decl, _, _) = with_defers_and_obligation();
        for _ in 0..2 {
            let scopes = decl.exits.push_scopes(&[]);
            let mut row = crate::exit::ExitEdgeRow::plain(
                crate::ids::BlockId(0),
                crate::ids::BlockId::NONE,
                crate::exit::ExitKind::Normal,
            );
            row.scopes = scopes;
            decl.exits.push(row);
        }
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::ExitEdgeDuplicate),
            "{diags:?}"
        );
    }

    #[test]
    fn a_deferred_body_that_never_reaches_body_end_is_rejected() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut blocks = crate::block::BlockPool::new();
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Ret),
            scope: crate::ids::ScopeId(0),
        });
        // Block 1 is a "body" that falls into `unreachable` instead of
        // jumping back: the exit sequence could never resume.
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Unreachable),
            scope: crate::ids::ScopeId(0),
        });
        decl.blocks = blocks;
        decl.defers.push(crate::scope::DeferRow {
            kind: crate::scope::DeferKind::Defer,
            body: crate::ids::BlockId(1),
            stmt_order: 0,
        });
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::DeferBodyMalformed),
            "{diags:?}"
        );
    }

    #[test]
    fn a_deferred_body_containing_a_return_is_rejected() {
        // ch01 R23c: "A body MUST NOT contain `return`, `raise`, `?` ..."
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut blocks = crate::block::BlockPool::new();
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Ret),
            scope: crate::ids::ScopeId(0),
        });
        let mut back = plain(Op::Br);
        back.a = crate::scope::BODY_END.0;
        let mut cond = plain(Op::CondBr);
        cond.b = 2;
        cond.c = 3;
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: cond,
            scope: crate::ids::ScopeId(0),
        });
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: back,
            scope: crate::ids::ScopeId(0),
        });
        blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: plain(Op::Ret),
            scope: crate::ids::ScopeId(0),
        });
        decl.blocks = blocks;
        decl.defers.push(crate::scope::DeferRow {
            kind: crate::scope::DeferKind::Defer,
            body: crate::ids::BlockId(1),
            stmt_order: 0,
        });
        let diags = verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == DiagCode::DeferBodyMalformed),
            "{diags:?}"
        );
    }
}
