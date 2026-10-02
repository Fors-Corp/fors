//! **F4's interpreter half**: `defer`/`errdefer` exit-edge execution
//! (design §3.8, §5.3, §5.4; ch01 R23-R23f; `type-checker.md` §13 I8b).
//!
//! F4's LOWERING half needs checker increment I8b's `D7`, which does not
//! exist ([HOLE-11]); design §4.2 says the interpreter half "runs on
//! hand-written FMIR fixtures and is not blocked", which is what these are.
//!
//! The order under test, on ONE exit edge, is I8b's and `fors-lower` must
//! reproduce it: (1) the result operand is moved, (2) the pending bodies,
//! innermost scope first, in one reverse `stmt_order` sequence interleaving
//! `Defer` and `ErrDefer` with `ErrDefer` only on an error exit, (3) the
//! drops of the remaining non-linear bindings, (4) ch01 R22h's check. A trap
//! is not an exit and runs none of it.
//!
//! Observability: these fixtures write through F1's one host intrinsic
//! (`Stdout`), not `Stderr`, because the interpreter has no `Stderr`
//! intrinsic yet (F2 built the unbuffered WRITER, not a std body that calls
//! it). What is under test is ORDER, which is the same on either stream;
//! the corpus tests that name `err.write_line` are F4's lowering half's.

mod fixture;

use fixture::{Fx, run_fx, run_fx_unverified};
use fors_fmir::exit::ExitKind;
use fors_fmir::ids::{BlockId, BrandId, ScopeId};
use fors_fmir::op::{NO_OPERAND, Op, TrapKind};
use fors_fmir::scope::{BODY_END, DeferKind};
use fors_interp::Exit;

/// A single-block deferred body that prints `text` and jumps back to the
/// exit sequence (ch01 R23a's "emit one copy and jump to it").
fn body(fx: &mut Fx, b: BlockId, scope: ScopeId, text: &str) {
    fx.begin(b, scope);
    fx.print(text);
    fx.end(fx.term(Op::Br, BODY_END.0, NO_OPERAND, NO_OPERAND));
}

// -- `defer-reverse-order-run-ok` --------------------------------------------

#[test]
fn defer_bodies_run_in_reverse_textual_order() {
    // ch01 R23a: "All bodies pending in `B` run in REVERSE textual order."
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let b0 = fx.reserve();
    let b1 = fx.reserve();
    let b2 = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[
            (DeferKind::Defer, b0, 0),
            (DeferKind::Defer, b1, 1),
            (DeferKind::Defer, b2, 2),
        ],
        &[],
    );
    body(&mut fx, b0, scope, "first");
    body(&mut fx, b1, scope, "second");
    body(&mut fx, b2, scope, "third");
    fx.begin(entry, scope);
    fx.print("body");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    fx.exit(entry, BlockId::NONE, ExitKind::Normal, &[scope]);

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["body", "third", "second", "first"]);
}

// -- `defer-runs-on-return-run-ok` -------------------------------------------

#[test]
fn defer_runs_on_an_early_return() {
    // ch01 R23a: the body runs when control leaves `B` by ANY exit,
    // `return` included — here the early one, taken before the fall-through
    // exit is reached at all.
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let early = fx.reserve();
    let late = fx.reserve();
    let b0 = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, b0, 0)],
        &[],
    );
    body(&mut fx, b0, scope, "cleanup");

    let bool_ty = fx.ty(fors_fir::ty::PrimKind::Bool);
    fx.begin(entry, scope);
    let cond = fx.emit(Op::ConstBool, 1, NO_OPERAND, NO_OPERAND, bool_ty);
    fx.end(fx.term(Op::CondBr, cond.0, early.0, late.0));

    fx.begin(early, scope);
    fx.print("early");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    fx.begin(late, scope);
    fx.print("late");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    fx.exit(early, BlockId::NONE, ExitKind::Normal, &[scope]);
    fx.exit(late, BlockId::NONE, ExitKind::Normal, &[scope]);

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["early", "cleanup"]);
}

// -- `defer-per-iteration-run-ok` --------------------------------------------

#[test]
fn a_defer_inside_a_loop_body_runs_once_per_iteration() {
    // ch01 R23e: "The body block of `for`, `while` ... is exited at the end
    // of every iteration ... so a `defer` written inside it runs once per
    // iteration."
    let mut fx = Fx::new();
    let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);
    let bool_ty = fx.ty(fors_fir::ty::PrimKind::Bool);

    let entry = fx.reserve();
    let head = fx.reserve();
    let loop_body = fx.reserve();
    let done = fx.reserve();
    let cleanup = fx.reserve();

    let outer = ScopeId(0); // `DeclFmir::empty`'s root scope: no defers.
    let (inner, _) = fx.scope(outer, BrandId::NONE, &[(DeferKind::Defer, cleanup, 0)], &[]);
    body(&mut fx, cleanup, inner, "tick");

    let counter = fors_fmir::ids::PlaceId(0);
    let counter = {
        let pid = fx.decl.places.intern(0, &[], i64_ty);
        assert_eq!(pid, counter);
        pid
    };

    fx.begin(entry, outer);
    let zero = fx.const_int(0, i64_ty);
    fx.emit_void(
        Op::Init,
        counter.0,
        zero.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    fx.end(fx.term(Op::Br, head.0, NO_OPERAND, NO_OPERAND));

    fx.begin(head, outer);
    let n = fx.emit(Op::CopyFrom, counter.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let three = fx.const_int(3, i64_ty);
    let go = fx.emit(
        Op::Icmp(fors_fmir::op::CmpPred::Lt),
        n.0,
        three.0,
        NO_OPERAND,
        bool_ty,
    );
    fx.end(fx.term(Op::CondBr, go.0, loop_body.0, done.0));

    fx.begin(loop_body, inner);
    fx.print("work");
    let cur = fx.emit(Op::CopyFrom, counter.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let one = fx.const_int(1, i64_ty);
    let next = fx.emit(
        Op::Add(fors_fmir::op::ArithMode::Trap),
        cur.0,
        one.0,
        NO_OPERAND,
        i64_ty,
    );
    fx.emit_void(
        Op::Init,
        counter.0,
        next.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    fx.end(fx.term(Op::Br, head.0, NO_OPERAND, NO_OPERAND));

    fx.begin(done, outer);
    fx.print("after");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    // The back edge out of the loop body leaves the body's scope, so the
    // pending body runs on EVERY iteration.
    fx.exit(loop_body, head, ExitKind::Normal, &[inner]);

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(
        lines,
        ["work", "tick", "work", "tick", "work", "tick", "after"]
    );
}

// -- `defer-nested-scope-order-run-ok` ---------------------------------------

#[test]
fn nested_scopes_run_innermost_first() {
    // ch01 R23a: "then the exit continues into the enclosing block, whose
    // pending bodies run next, and so on outward"; I8b step 2 spells it
    // "innermost scope first".
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let inner_block = fx.reserve();
    let outer_body = fx.reserve();
    let inner_body_a = fx.reserve();
    let inner_body_b = fx.reserve();

    let (outer, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, outer_body, 0)],
        &[],
    );
    let (inner, _) = fx.scope(
        outer,
        BrandId::NONE,
        &[
            (DeferKind::Defer, inner_body_a, 0),
            (DeferKind::Defer, inner_body_b, 1),
        ],
        &[],
    );
    body(&mut fx, outer_body, outer, "outer");
    body(&mut fx, inner_body_a, inner, "inner-a");
    body(&mut fx, inner_body_b, inner, "inner-b");

    fx.begin(entry, outer);
    fx.print("start");
    fx.end(fx.term(Op::Br, inner_block.0, NO_OPERAND, NO_OPERAND));

    fx.begin(inner_block, inner);
    fx.print("in-inner");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    // One `ret` leaves BOTH scopes: innermost first, each in reverse
    // statement order.
    fx.exit(
        inner_block,
        BlockId::NONE,
        ExitKind::Normal,
        &[inner, outer],
    );

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["start", "in-inner", "inner-b", "inner-a", "outer"]);
}

// -- `defer-result-evaluated-first-run-ok` -----------------------------------

#[test]
fn the_result_is_moved_before_the_first_body_runs() {
    // ch01 R23a: "On `return e;` ... `e` is evaluated, and moved into the
    // result, BEFORE any body runs; a body can neither read nor change the
    // result." The body here overwrites the very slot `e` was read from and
    // prints the new value, and the returned value is still the old one.
    let mut fx = Fx::new();
    let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);
    let bool_ty = fx.ty(fors_fir::ty::PrimKind::Bool);

    let entry = fx.reserve();
    let check = fx.reserve();
    let ok = fx.reserve();
    let bad = fx.reserve();
    let overwrite = fx.reserve();

    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, overwrite, 0)],
        &[],
    );
    let slot = fx.decl.places.intern(0, &[], i64_ty);

    // The body writes 99 into the slot the result came from, and announces
    // that it ran, so "the body did run" and "the result is unchanged" are
    // two independent observations.
    fx.begin(overwrite, scope);
    fx.print("body-ran");
    let ninety_nine = fx.const_int(99, i64_ty);
    fx.emit_void(
        Op::Init,
        slot.0,
        ninety_nine.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    fx.end(fx.term(Op::Br, BODY_END.0, NO_OPERAND, NO_OPERAND));

    fx.begin(entry, scope);
    let seven = fx.const_int(7, i64_ty);
    fx.emit_void(
        Op::Init,
        slot.0,
        seven.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    let result = fx.emit(Op::CopyFrom, slot.0, NO_OPERAND, NO_OPERAND, i64_ty);
    // `br` out of the scope is the exit edge; `check` then observes both the
    // moved result and the slot the body overwrote.
    fx.end(fx.term(Op::Br, check.0, NO_OPERAND, NO_OPERAND));
    fx.exit(entry, check, ExitKind::Normal, &[scope]);

    fx.begin(check, ScopeId(0));
    let now = fx.emit(Op::CopyFrom, slot.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let unchanged = fx.emit(
        Op::Icmp(fors_fmir::op::CmpPred::Eq),
        result.0,
        now.0,
        NO_OPERAND,
        bool_ty,
    );
    fx.end(fx.term(Op::CondBr, unchanged.0, bad.0, ok.0));

    fx.begin(ok, ScopeId(0));
    fx.print("result-is-pre-body");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    fx.begin(bad, ScopeId(0));
    fx.print("result-was-changed");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["body-ran", "result-is-pre-body"]);
}

// -- `errdefer-skipped-on-return-run-ok` / the error-exit twin ---------------

/// One fixture, two edges: a normal `ret` and an error `raise`, each leaving
/// the same scope, which holds `defer`(0), `errdefer`(1), `defer`(2).
fn errdefer_fixture(take_error_exit: bool) -> (fors_interp::Outcome, Vec<String>) {
    let mut fx = Fx::new();
    let bool_ty = fx.ty(fors_fir::ty::PrimKind::Bool);
    let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);

    let entry = fx.reserve();
    let normal = fx.reserve();
    let error = fx.reserve();
    let d0 = fx.reserve();
    let e1 = fx.reserve();
    let d2 = fx.reserve();

    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[
            (DeferKind::Defer, d0, 0),
            (DeferKind::ErrDefer, e1, 1),
            (DeferKind::Defer, d2, 2),
        ],
        &[],
    );
    body(&mut fx, d0, scope, "defer-0");
    body(&mut fx, e1, scope, "errdefer-1");
    body(&mut fx, d2, scope, "defer-2");

    fx.begin(entry, scope);
    let cond = fx.emit(
        Op::ConstBool,
        u32::from(take_error_exit),
        NO_OPERAND,
        NO_OPERAND,
        bool_ty,
    );
    fx.end(fx.term(Op::CondBr, cond.0, error.0, normal.0));

    fx.begin(normal, scope);
    fx.print("normal-exit");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    fx.begin(error, scope);
    fx.print("error-exit");
    let err = fx.const_int(1, i64_ty);
    fx.end(fx.term(Op::Raise, err.0, NO_OPERAND, NO_OPERAND));

    fx.exit(normal, BlockId::NONE, ExitKind::Normal, &[scope]);
    fx.exit(error, BlockId::NONE, ExitKind::Error, &[scope]);

    run_fx(fx)
}

#[test]
fn errdefer_is_skipped_on_a_normal_exit() {
    // ch01 R23b: an `errdefer` body "runs on the ERROR exits of `B` ... and
    // NEVER on a normal exit."
    let (out, lines) = errdefer_fixture(false);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["normal-exit", "defer-2", "defer-0"]);
    assert!(!lines.iter().any(|l| l == "errdefer-1"));
}

#[test]
fn errdefer_runs_interleaved_on_an_error_exit() {
    // ch01 R23b: "`defer` and `errdefer` bodies pending in `B` run
    // INTERLEAVED, in one reverse textual order" — 2, then 1, then 0, not
    // "every defer, then every errdefer".
    let (out, lines) = errdefer_fixture(true);
    assert_eq!(out.exit, Exit::Raise);
    assert_eq!(lines, ["error-exit", "defer-2", "errdefer-1", "defer-0"]);
    assert_eq!(
        fors_interp::entry_exit(&out),
        fors_interp::ExitStatus::Status(1),
        "ch02 R17(c)"
    );
}

// -- `trap-runs-no-defer` / `10-std/defer-not-run-on-trap` -------------------

#[test]
fn a_trap_runs_no_deferred_body_and_has_no_successor() {
    // design §5.3: a trap "performs **no** deferred body (§3.8: there is
    // nothing pending to perform, because pending bodies are blocks on the
    // *exit edges*, and `trap` has no successor)"; ch01 R23f and R22d say
    // the same from the ownership side.
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let cleanup = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, cleanup, 0)],
        &[],
    );
    body(&mut fx, cleanup, scope, "cleanup");

    let site = fx.site(12, 5);
    fx.begin(entry, scope);
    fx.print("before");
    fx.end(fx.term_at(
        Op::Trap,
        TrapKind::Bounds as u32,
        NO_OPERAND,
        NO_OPERAND,
        site,
    ));
    // Deliberately NO exit edge: `verify()` rejects one on a
    // `trap`-terminated block (`TrapHasExitEdge`).

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Trap(TrapKind::Bounds));
    assert_eq!(lines, ["before"], "the pending body did not run");
    assert_eq!(out.site, Some((12, 5)));
    assert_eq!(
        fors_interp::trap_line(TrapKind::Bounds, "main.fors", 12, 5),
        "trap: bounds at main.fors:12:5\n"
    );
}

// -- the interpreter's own assertions ----------------------------------------

#[test]
fn an_errdefer_on_a_normal_edge_is_reported_never_silently_run() {
    // design §3.8's rule stated from the interpreter's side: it executes the
    // edge's list as carried and does NOT re-derive it, but a body ch01 R23b
    // forbids on this edge is a compiler bug and is named, not swallowed.
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let e0 = fx.reserve();
    let (scope, ids) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::ErrDefer, e0, 0)],
        &[],
    );
    body(&mut fx, e0, scope, "errdefer");
    fx.begin(entry, scope);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    // A normal edge carrying an `errdefer` body: exactly what `verify()`'s
    // `ExitEdgeWrongPendingMultiset` rejects, fed to the interpreter anyway.
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &ids,
        &[],
        &[],
    );

    let err = run_fx_unverified(fx).expect_err("a compiler bug, not a run");
    assert!(
        matches!(err, fors_interp::InterpError::MalformedExitEdge(_)),
        "{err:?}"
    );
}

// -- COUNTER: inlined-body growth ratio (risk R6) -----------------------------

/// Risk **R6**: `defer` is inlined at every exit edge (E3, ch01 R23a), so a
/// body pending at many exits is emitted many times. F4's named counter is
/// "inlined-body growth as a ratio of body size".
///
/// Measured here over a shape that maximises it for a small body: one scope
/// with two bodies and four exits.
#[test]
fn counter_inlined_body_growth_ratio() {
    let mut fx = Fx::new();
    let bool_ty = fx.ty(fors_fir::ty::PrimKind::Bool);
    let entry = fx.reserve();
    let a = fx.reserve();
    let b = fx.reserve();
    let c = fx.reserve();
    let d = fx.reserve();
    let b0 = fx.reserve();
    let b1 = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, b0, 0), (DeferKind::Defer, b1, 1)],
        &[],
    );
    body(&mut fx, b0, scope, "b0");
    body(&mut fx, b1, scope, "b1");

    fx.begin(entry, scope);
    let t = fx.emit(Op::ConstBool, 1, NO_OPERAND, NO_OPERAND, bool_ty);
    fx.end(fx.term(Op::CondBr, t.0, a.0, b.0));
    for exit_block in [a, b, c, d] {
        fx.begin(exit_block, scope);
        fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        fx.exit(exit_block, BlockId::NONE, ExitKind::Normal, &[scope]);
    }

    let (decl, _tys, _strings) = fx.finish();
    let ratio = growth_ratio(&decl);
    println!("COUNTER inlined-body growth ratio (risk R6): {ratio:.2}x");
    // Four exits, both bodies pending at each: a true inliner emits 8 copies
    // of 2 bodies.
    assert!(
        (ratio - 4.0).abs() < 1e-9,
        "expected 4x for four exits, got {ratio}"
    );
    // The guard the counter exists for: the ratio is EXACTLY the number of
    // exits a body is pending at, so it is bounded by the CFG, never
    // superlinear in the body.
    assert!(ratio <= 8.0, "growth above 8x should be a design review");
}

/// Instructions an inliner would emit for pending bodies, over the
/// instructions those bodies occupy once. design §3.8's third `DeferPool`
/// consumer — OIR's "emit one copy and jump to it" — is what caps this at
/// 1.0 later; F4 measures the uncapped figure.
fn growth_ratio(decl: &fors_fmir::decl::DeclFmir) -> f64 {
    let body_size =
        |b: BlockId| -> u32 { decl.blocks.try_row(b).map(|r| r.inst_len + 1).unwrap_or(0) };
    let mut once = 0u32;
    let n = decl.defers.len() as u32;
    for row in decl.defers.get(0..n) {
        once += body_size(row.body);
    }
    let mut inlined = 0u32;
    for (_, edge) in decl.exits.all_rows() {
        for id in decl.exits.pending(edge.pending.clone()) {
            if let Some(row) = decl.defers.get(id.0..id.0 + 1).first() {
                inlined += body_size(row.body);
            }
        }
    }
    if once == 0 {
        return 0.0;
    }
    f64::from(inlined) / f64::from(once)
}

// -- verifier-added cases: each distinguishes the required order from its
// -- nearest wrong alternative ----------------------------------------------

/// A deferred body that itself opens an inner scope with its own `defer`
/// (ch01 R23c allows nesting; `defer-nested-body-accepted` is the checker's
/// test). The inner scope's edge runs INSIDE the outer body, through the
/// per-frame stack of exits in progress, and the outer body then resumes.
#[test]
fn a_defer_nested_inside_a_deferred_body_runs_inside_it() {
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let outer_body = fx.reserve();
    let outer_tail = fx.reserve();
    let inner_body = fx.reserve();
    let (outer, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, outer_body, 0)],
        &[],
    );
    let (inner, _) = fx.scope(
        outer,
        BrandId::NONE,
        &[(DeferKind::Defer, inner_body, 0)],
        &[],
    );
    body(&mut fx, inner_body, inner, "inner");
    // The outer body's first block is IN the inner scope; leaving it for the
    // tail is the inner scope's exit edge.
    fx.begin(outer_body, inner);
    fx.print("outer-start");
    fx.end(fx.term(Op::Br, outer_tail.0, NO_OPERAND, NO_OPERAND));
    fx.exit(outer_body, outer_tail, ExitKind::Normal, &[inner]);
    body(&mut fx, outer_tail, outer, "outer-end");
    fx.begin(entry, outer);
    fx.print("main");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    fx.exit(entry, BlockId::NONE, ExitKind::Normal, &[outer]);
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["main", "outer-start", "inner", "outer-end"]);
}

/// Step 4's report points at the EXIT's terminator. Once a body has run the
/// current block is the body's last one, and its `br BODY_END` is not where
/// the leak is.
#[test]
fn a_linear_leak_report_points_at_the_exit_not_at_the_last_body() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);
    let owed = fx.decl.places.intern(0, &[], i64_ty);
    let entry = fx.reserve();
    let b0 = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, b0, 0)],
        &[owed],
    );
    let body_site = fx.site(5, 5);
    fx.begin(b0, scope);
    fx.print("body");
    fx.end(fx.term_at(Op::Br, BODY_END.0, NO_OPERAND, NO_OPERAND, body_site));
    let ret_site = fx.site(9, 9);
    fx.begin(entry, scope);
    fx.end(fx.term_at(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND, ret_site));
    let pending = fors_fmir::exit::expected_pending(
        &fx.decl.scopes,
        &fx.decl.defers,
        &[scope],
        ExitKind::Normal,
    );
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &pending,
        &[],
        &[],
    );
    let out = run_fx_unverified(fx).expect("a ub: report");
    assert_eq!(out.exit, Exit::Ub(fors_interp::UbClass::LinearLeak));
    assert_eq!(fixture::lines_of(&out), ["body"]);
    assert_eq!(out.site, Some((9, 9)));
}

/// Step 1 on a `ret` with an operand, observed through a CALL: the callee's
/// body overwrites the slot the result came from, and the caller still
/// receives the pre-body value. (`the_result_is_moved_before_the_first_body_runs`
/// observes the same rule on a `br` edge; a `ret` is the common case.)
#[test]
fn a_ret_operand_is_moved_before_the_body_as_seen_by_the_caller() {
    let mut callee = Fx::new();
    let i64_ty = callee.ty(fors_fir::ty::PrimKind::I64);
    let _ = callee.ty(fors_fir::ty::PrimKind::Bool);
    let entry = callee.reserve();
    let overwrite = callee.reserve();
    let (scope, _) = callee.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, overwrite, 0)],
        &[],
    );
    let slot = callee.decl.places.intern(0, &[], i64_ty);
    callee.begin(overwrite, scope);
    callee.print("body-ran");
    let nn = callee.const_int(99, i64_ty);
    callee.emit_void(
        Op::Init,
        slot.0,
        nn.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    callee.end(callee.term(Op::Br, BODY_END.0, NO_OPERAND, NO_OPERAND));
    callee.begin(entry, scope);
    let seven = callee.const_int(7, i64_ty);
    callee.emit_void(
        Op::Init,
        slot.0,
        seven.0,
        NO_OPERAND,
        fors_fmir::ids::SiteId(0),
    );
    let r = callee.emit(Op::CopyFrom, slot.0, NO_OPERAND, NO_OPERAND, i64_ty);
    callee.end(callee.term(Op::Ret, r.0, NO_OPERAND, NO_OPERAND));
    callee.exit(entry, BlockId::NONE, ExitKind::Normal, &[scope]);

    let mut main = Fx::new();
    let i64_ty = main.ty(fors_fir::ty::PrimKind::I64);
    let bool_ty = main.ty(fors_fir::ty::PrimKind::Bool);
    let entry = main.reserve();
    let ok = main.reserve();
    let bad = main.reserve();
    main.begin(entry, ScopeId(0));
    let got = fixture::call_callee(&mut main, i64_ty);
    let seven = main.const_int(7, i64_ty);
    let same = main.emit(
        Op::Icmp(fors_fmir::op::CmpPred::Eq),
        got.0,
        seven.0,
        NO_OPERAND,
        bool_ty,
    );
    main.end(main.term(Op::CondBr, same.0, ok.0, bad.0));
    main.begin(ok, ScopeId(0));
    main.print("result-is-pre-body");
    main.end(main.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    main.begin(bad, ScopeId(0));
    main.print("result-was-changed");
    main.end(main.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (prog, tys) = fixture::program2(main, callee);
    let out = fors_interp::run(&prog, &tys).expect("runs");
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(fixture::lines_of(&out), ["body-ran", "result-is-pre-body"]);
}

/// Two nested scopes, each holding a `defer` and an `errdefer`, left by one
/// terminator. The error exit runs the inner scope's two bodies first, each
/// scope's in ONE reverse `stmt_order` sequence; the normal exit skips the
/// `errdefer`s. Every nearest wrong alternative is a verifier rejection:
/// grouped by kind, outer scope's bodies first, the scopes LISTED
/// outer-first (which `expected_pending` alone would accept), an `errdefer`
/// on a normal edge, and a `raise` edge marked normal.
#[test]
fn two_scopes_run_innermost_first_each_interleaved_and_the_alternatives_are_rejected() {
    type Built = (
        Fx,
        ScopeId,
        ScopeId,
        BlockId,
        Vec<fors_fmir::ids::DeferId>,
        Vec<fors_fmir::ids::DeferId>,
    );
    fn build(raise: bool) -> Built {
        let mut fx = Fx::new();
        let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);
        let entry = fx.reserve();
        let a0 = fx.reserve();
        let a1 = fx.reserve();
        let b0 = fx.reserve();
        let b1 = fx.reserve();
        let (outer, b) = fx.scope(
            ScopeId::NONE,
            BrandId::NONE,
            &[(DeferKind::ErrDefer, b0, 0), (DeferKind::Defer, b1, 1)],
            &[],
        );
        let (inner, a) = fx.scope(
            outer,
            BrandId::NONE,
            &[(DeferKind::Defer, a0, 0), (DeferKind::ErrDefer, a1, 1)],
            &[],
        );
        body(&mut fx, a0, inner, "inner-defer-0");
        body(&mut fx, a1, inner, "inner-errdefer-1");
        body(&mut fx, b0, outer, "outer-errdefer-0");
        body(&mut fx, b1, outer, "outer-defer-1");
        fx.begin(entry, inner);
        fx.print("start");
        if raise {
            let e = fx.const_int(1, i64_ty);
            fx.end(fx.term(Op::Raise, e.0, NO_OPERAND, NO_OPERAND));
        } else {
            fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        }
        (fx, inner, outer, entry, a, b)
    }
    fn rejected_with(fx: Fx, code: fors_fmir::diag::DiagCode) {
        let (decl, _, _) = fx.finish();
        let diags = fors_fmir::verify::verify(&decl);
        assert!(
            diags.iter().any(|d| d.code == code),
            "expected {code:?}, got {:?}",
            diags
                .iter()
                .map(|d| (d.code, &d.message))
                .collect::<Vec<_>>()
        );
    }
    use fors_fmir::diag::DiagCode;

    let (mut fx, inner, outer, entry, _, _) = build(true);
    fx.exit(entry, BlockId::NONE, ExitKind::Error, &[inner, outer]);
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Raise);
    assert_eq!(
        lines,
        [
            "start",
            "inner-errdefer-1",
            "inner-defer-0",
            "outer-defer-1",
            "outer-errdefer-0"
        ]
    );

    let (mut fx, inner, outer, entry, _, _) = build(false);
    fx.exit(entry, BlockId::NONE, ExitKind::Normal, &[inner, outer]);
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["start", "inner-defer-0", "outer-defer-1"]);

    // Grouped by kind: every `defer`, then every `errdefer`.
    let (mut fx, inner, outer, entry, a, b) = build(true);
    let scopes = [inner, outer];
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Error,
        &scopes,
        &[a[0], b[1], a[1], b[0]],
        &[],
        &[],
    );
    rejected_with(fx, DiagCode::ExitEdgeWrongPendingOrder);

    // Outer scope's bodies first.
    let (mut fx, inner, outer, entry, a, b) = build(true);
    let scopes = [inner, outer];
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Error,
        &scopes,
        &[b[1], b[0], a[1], a[0]],
        &[],
        &[],
    );
    rejected_with(fx, DiagCode::ExitEdgeWrongPendingOrder);

    // The scopes LISTED outer-first, with a pending list to match: the
    // per-scope check alone passes this, and the interpreter would run the
    // outer scope's bodies first.
    let (mut fx, inner, outer, entry, a, b) = build(true);
    let scopes = [outer, inner];
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Error,
        &scopes,
        &[b[1], b[0], a[1], a[0]],
        &[],
        &[],
    );
    rejected_with(fx, DiagCode::ExitEdgeScopesNotAChain);

    // An `errdefer` on a normal exit.
    let (mut fx, inner, outer, entry, a, b) = build(false);
    let scopes = [inner, outer];
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &scopes,
        &[a[1], a[0], b[1], b[0]],
        &[],
        &[],
    );
    rejected_with(fx, DiagCode::ExitEdgeWrongPendingMultiset);

    // A `raise` edge marked normal, consistently omitting the `errdefer`s.
    let (mut fx, inner, outer, entry, a, b) = build(true);
    let scopes = [inner, outer];
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &scopes,
        &[a[0], b[1]],
        &[],
        &[],
    );
    rejected_with(fx, DiagCode::ExitEdgeWrongKind);
}

/// Step 3 after step 2: a body may still read a binding the edge drops, and
/// the successor may not. The wrong alternative (drops first) would make the
/// body's read `ub: use-after-move`.
#[test]
fn drops_run_after_the_bodies() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(fors_fir::ty::PrimKind::I64);
    let p = fx.decl.places.intern(0, &[], i64_ty);
    let entry = fx.reserve();
    let b0 = fx.reserve();
    let after = fx.reserve();
    let (scope, ids) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, b0, 0)],
        &[],
    );
    fx.begin(b0, scope);
    let _ = fx.emit(Op::CopyFrom, p.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("body-read-ok");
    fx.end(fx.term(Op::Br, BODY_END.0, NO_OPERAND, NO_OPERAND));
    fx.begin(entry, scope);
    let one = fx.const_int(1, i64_ty);
    fx.emit_void(Op::Init, p.0, one.0, NO_OPERAND, fors_fmir::ids::SiteId(0));
    fx.end(fx.term(Op::Br, after.0, NO_OPERAND, NO_OPERAND));
    fx.exit_raw(entry, after, ExitKind::Normal, &[scope], &ids, &[p], &[]);
    fx.begin(after, ScopeId(0));
    let site = fx.site(12, 1);
    let _ = fx.emit_at(Op::CopyFrom, p.0, NO_OPERAND, NO_OPERAND, i64_ty, site);
    fx.print("unreachable");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Ub(fors_interp::UbClass::UseAfterMove));
    assert_eq!(lines, ["body-read-ok"]);
    assert_eq!(out.site, Some((12, 1)));
}

/// A `trap` INSIDE a deferred body ends the process there (ch02 R7): the
/// bodies still pending on the same edge never run.
#[test]
fn a_trap_inside_a_body_stops_the_rest_of_the_sequence() {
    let mut fx = Fx::new();
    let entry = fx.reserve();
    let d0 = fx.reserve();
    let d1 = fx.reserve();
    let (scope, _) = fx.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, d0, 0), (DeferKind::Defer, d1, 1)],
        &[],
    );
    body(&mut fx, d0, scope, "d0-must-not-run");
    fx.begin(d1, scope);
    fx.print("d1-start");
    fx.end(fx.term(Op::Trap, TrapKind::Bounds as u32, NO_OPERAND, NO_OPERAND));
    fx.begin(entry, scope);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    fx.exit(entry, BlockId::NONE, ExitKind::Normal, &[scope]);
    // `verify()` demands a body REACH `br BODY_END`; this one never does, so
    // it is run unverified to observe the interpreter alone.
    let out = run_fx_unverified(fx).expect("runs");
    assert_eq!(out.exit, Exit::Trap(TrapKind::Bounds));
    assert_eq!(fixture::lines_of(&out), ["d1-start"]);
}

/// A `raise` out of a NON-entry frame with no `try_br` in the caller is
/// reported, not settled as if `main` had raised: that would skip the
/// caller's own pending bodies (ch01 R23a) and misreport ch02 R17's exit.
/// Propagation into a caller is F3's (design §3.6).
#[test]
fn a_raise_out_of_a_callee_without_try_br_is_reported_not_treated_as_mains() {
    let mut callee = Fx::new();
    let i64_ty = callee.ty(fors_fir::ty::PrimKind::I64);
    let entry = callee.reserve();
    callee.begin(entry, ScopeId(0));
    let e = callee.const_int(1, i64_ty);
    callee.end(callee.term(Op::Raise, e.0, NO_OPERAND, NO_OPERAND));

    let mut main = Fx::new();
    let i64_ty = main.ty(fors_fir::ty::PrimKind::I64);
    let entry = main.reserve();
    let d0 = main.reserve();
    let (scope, _) = main.scope(
        ScopeId::NONE,
        BrandId::NONE,
        &[(DeferKind::Defer, d0, 0)],
        &[],
    );
    body(&mut main, d0, scope, "main-defer");
    main.begin(entry, scope);
    let _ = fixture::call_callee(&mut main, i64_ty);
    main.print("after-call");
    main.end(main.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    main.exit(entry, BlockId::NONE, ExitKind::Normal, &[scope]);
    let (prog, tys) = fixture::program2(main, callee);
    match fors_interp::run(&prog, &tys) {
        Err(fors_interp::InterpError::UnhandledRaise(func)) => assert_eq!(func, "callee"),
        other => panic!("expected UnhandledRaise, got {other:?}"),
    }
}
