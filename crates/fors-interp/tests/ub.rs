//! **F6's interpreter half**: arenas, `Own`, allocators, linear obligations
//! and design §5.2's `ub:` detection list (design §3.5, §3.7, §5.1, §5.2;
//! ch01 R15-R18, R22-R22i).
//!
//! F6's LOWERING half needs checker increment I8b's `D8` plus I4/I5 and D12
//! ([HOLE-6], [HOLE-11]); design §4.2 lets the interpreter half be built and
//! tested against hand-written FMIR first, which is what these are.
//!
//! The named gates of §9's F6 paragraph are, by name:
//! [`ub_use_after_free`], [`ub_uninit_read_through_out`],
//! [`ub_allocator_mismatch`], [`ub_linear_leak_is_not_a_trap`],
//! [`arena_gen_wraps_safely`], and the two POSITIVE cases
//! [`ub_aliasing_accepts_two_let_borrows`] and
//! [`ub_aliasing_accepts_nested_let_under_let`] (ch01 R7, E14) — "ranked
//! above the positive detections", because a false report exits 70 and
//! would fail the corpus on ACCEPTED code.
//!
//! **HELD OUT**: the one corpus test F6's gate names,
//! `01-ownership/arena-generation-trap`. It is a Fors source file whose
//! `Arena`/`Ref` surface needs lowering of generic std bodies (I4's `Index`
//! impl on `Arena`, I5's brands) — none of which exists. The MECHANISM it
//! tests is covered end to end here by
//! [`arena_generation_trap_on_a_stale_ref`].

mod fixture;

use fixture::{Fx, run_fx, run_fx_unverified};
use fors_fir::ty::PrimKind;
use fors_fmir::exit::ExitKind;
use fors_fmir::ids::{BlockId, BrandId, ScopeId, SiteId};
use fors_fmir::op::{NO_OPERAND, Op, TrapKind};
use fors_fmir::place::Seg;
use fors_fmir::region::RegionKind;
use fors_interp::{Exit, ExitStatus, UB_EXIT_STATUS, UbClass, entry_exit, next_generation};

/// Every `ub:` outcome must satisfy all of this, whatever the class:
/// it is not a trap, it exits 70, and its record names the class AND the
/// instruction (the task's "every `ub:` report must name the detection class
/// and the instruction; none may be downgraded to a trap or swallowed").
fn assert_ub(out: &fors_interp::Outcome, class: UbClass) {
    assert_eq!(out.exit, Exit::Ub(class), "wrong class");
    assert!(!matches!(out.exit, Exit::Trap(_)), "a ub: is never a trap");
    assert_eq!(entry_exit(out), ExitStatus::Status(UB_EXIT_STATUS));
    let report = out.ub.as_ref().expect("a machine-readable record");
    assert_eq!(report.class, class);
    assert!(
        !TrapKind::KINDS.contains(&report.class.as_str()),
        "`{}` collides with one of ch02 R15's eight trap kinds",
        report.class.as_str()
    );
    let line = report.line("main.fors");
    assert!(
        line.starts_with(&format!("ub: {}", class.as_str())),
        "{line}"
    );
    assert!(
        line.contains("inst ") || line.contains("terminator"),
        "the report must name the instruction: {line}"
    );
}

// -- ub_use_after_free -------------------------------------------------------

/// design §5.2: "Use of a freed or reset allocation -> `ub: use-after-free`
/// (heap)". A heap block is `@alloc`-ed, `@free`-d, then read through.
#[test]
fn ub_use_after_free() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let slot = fx.decl.places.intern(0, &[], ptr_ty);
    let through = fx.decl.places.intern(0, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let size = fx.const_int(8, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, slot.0, p.0, NO_OPERAND, SiteId(0));
    let site = fx.site(21, 3);
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, site);
    let read_site = fx.site(22, 9);
    let _ = fx.emit_at(
        Op::CopyFrom,
        through.0,
        NO_OPERAND,
        NO_OPERAND,
        i64_ty,
        read_site,
    );
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UseAfterFree);
    assert_eq!(out.site, Some((22, 9)), "the report points at the READ");
}

/// Freeing twice is "use of a freed allocation" too — the same row, found at
/// the `free` rather than at a read.
#[test]
fn ub_double_free_is_use_after_free() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let size = fx.const_int(8, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UseAfterFree);
}

// -- ub_uninit_read_through_out ----------------------------------------------

/// design §5.2: "Uninitialised read (**incl. through `&out`**) ->
/// `ub: uninit-read`". `borrow_out` targets an uninitialised slot (design
/// §3.3: "`&out x` targets an *uninitialised* slot"), and a read through it
/// before the callee writes is the detection.
#[test]
fn ub_uninit_read_through_out() {
    let mut fx = Fx::new();
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let target = fx.decl.places.intern(1, &[], i64_ty);
    let holder = fx.decl.places.intern(0, &[], ptr_ty);
    let through = fx.decl.places.intern(0, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let out_ptr = fx.emit(Op::BorrowOut, target.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, holder.0, out_ptr.0, NO_OPERAND, SiteId(0));
    let site = fx.site(7, 11);
    let _ = fx.emit_at(
        Op::CopyFrom,
        through.0,
        NO_OPERAND,
        NO_OPERAND,
        i64_ty,
        site,
    );
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UninitRead);
    assert_eq!(out.site, Some((7, 11)));
}

/// The same `&out` pointer, written first: the write initialises the slot,
/// so the read is clean. Without this the test above would pass for a model
/// that simply reports every `&out` read.
#[test]
fn a_write_through_out_makes_the_later_read_clean() {
    let mut fx = Fx::new();
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let target = fx.decl.places.intern(1, &[], i64_ty);
    let holder = fx.decl.places.intern(0, &[], ptr_ty);
    let through = fx.decl.places.intern(0, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let out_ptr = fx.emit(Op::BorrowOut, target.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, holder.0, out_ptr.0, NO_OPERAND, SiteId(0));
    let v = fx.const_int(42, i64_ty);
    fx.emit_void(Op::Init, through.0, v.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, through.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("clean");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none());
    assert_eq!(lines, ["clean"]);
}

// -- ub_allocator_mismatch ---------------------------------------------------

/// ch01 R18: "`Own[T, A]` MUST record its producing allocator's brand `A`;
/// `deinit` with an allocator whose brand differs from `A` MUST be a compile
/// error." design §5.2 gives the interpreter the ERASED case:
/// `AllocKind::Heap(id)` versus the freeing allocator.
#[test]
fn ub_allocator_mismatch() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);

    // Two `with allocator` blocks, i.e. two brands (ch01 R15: "Each such
    // block in the source introduces exactly one fresh brand").
    let (producing, _) = fx.scope(ScopeId::NONE, BrandId(1), &[], &[]);
    let (freeing, _) = fx.scope(ScopeId::NONE, BrandId(2), &[], &[]);

    let entry = fx.reserve();
    let other = fx.reserve();
    fx.begin(entry, producing);
    let size = fx.const_int(16, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.end(fx.term(Op::Br, other.0, NO_OPERAND, NO_OPERAND));

    fx.begin(other, freeing);
    let site = fx.site(31, 2);
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, site);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::AllocatorMismatch);
    assert_eq!(out.site, Some((31, 2)));
    let detail = &out.ub.as_ref().unwrap().detail;
    assert!(detail.contains("freed by allocator brand 2"), "{detail}");
}

/// Freeing with the SAME brand is clean — the mismatch test above would
/// otherwise pass for a model that reports every `free`.
#[test]
fn freeing_with_the_producing_allocator_is_clean() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let (owner, _) = fx.scope(ScopeId::NONE, BrandId(1), &[], &[]);
    let entry = fx.reserve();
    fx.begin(entry, owner);
    let size = fx.const_int(16, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.print("freed");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none());
    assert_eq!(lines, ["freed"]);
}

// -- ub_linear_leak_is_not_a_trap --------------------------------------------

/// design §3.5: "in Miri mode a scope exit whose obligation has no discharge
/// record is the interpreter diagnostic `linear-leak`, **not a trap**. A leak
/// reaching the interpreter is a **compiler bug**, and a compiler bug must
/// not look like a program trap — there is no trap kind for it in ch02 R15's
/// closed list of eight, and inventing one would violate that rule."
#[test]
fn ub_linear_leak_is_not_a_trap() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let owed = fx.decl.places.intern(0, &[], i64_ty);
    let (scope, _) = fx.scope(ScopeId::NONE, BrandId::NONE, &[], &[owed]);

    let entry = fx.reserve();
    fx.begin(entry, scope);
    fx.print("before-exit");
    fx.end(fx.term_at(
        Op::Ret,
        NO_OPERAND,
        NO_OPERAND,
        NO_OPERAND,
        fx.decl.sites.try_row(SiteId(0)).map(|_| SiteId(0)).unwrap(),
    ));
    // The leak: an exit edge leaving a scope whose obligation has NO
    // discharge record. `verify()` finds the same thing statically
    // (`ExitEdgeMissingDischarge`), so the fixture is run unverified.
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &[],
        &[],
        &[],
    );

    let out = run_fx_unverified(fx).expect("a ub: report, not an interpreter error");
    assert_ub(&out, UbClass::LinearLeak);
    // ch02 R15's eight stay the only trap kinds: the leak is NOT one of them
    // and does not produce a signal status.
    assert!(!matches!(entry_exit(&out), ExitStatus::Trap(_)));
    let detail = &out.ub.as_ref().unwrap().detail;
    assert!(detail.contains("R22h"), "{detail}");
    assert!(detail.contains("compiler bug"), "{detail}");
}

/// The same scope, discharged: no report. ch01 R22d(iii) / R23d(b)'s
/// deferred consumption is the discharge shape a `defer p.deinit(&a);`
/// produces.
#[test]
fn a_discharged_obligation_is_clean() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let owed = fx.decl.places.intern(0, &[], i64_ty);
    let (scope, _) = fx.scope(ScopeId::NONE, BrandId::NONE, &[], &[owed]);
    let entry = fx.reserve();
    fx.begin(entry, scope);
    fx.print("consumed");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &[],
        &[],
        &[fors_fmir::exit::DischargeRow {
            place: owed,
            how: fors_fmir::scope::Discharge::Returned,
        }],
    );
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none());
    assert_eq!(lines, ["consumed"]);
}

/// design §5.2's second row: "Double consume of a linear value — obligation
/// record already discharged on this edge -> `ub: double-consume`".
#[test]
fn ub_double_consume_on_one_edge() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let owed = fx.decl.places.intern(0, &[], i64_ty);
    let (scope, _) = fx.scope(ScopeId::NONE, BrandId::NONE, &[], &[owed]);
    let entry = fx.reserve();
    fx.begin(entry, scope);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let twice = fors_fmir::exit::DischargeRow {
        place: owed,
        how: fors_fmir::scope::Discharge::Returned,
    };
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &[],
        &[],
        &[twice, twice],
    );
    let out = run_fx_unverified(fx).expect("a ub: report");
    assert_ub(&out, UbClass::DoubleConsume);
}

// -- arena_gen_wraps_safely ([HOLE-2]) ---------------------------------------

/// **[HOLE-2]** / engineering call **E9**, design §3.7: "`arena_reset` bumps
/// `gen` (wrapping is a verifier-rejected condition: `gen == u32::MAX` traps
/// `arena-generation` preemptively rather than aliasing an old generation —
/// ch01 R17 does not say what a wrapped counter does)". E9's reason: "wrapping
/// silently revalidates a stale `Ref`, which is the exact bug R17 exists to
/// prevent".
///
/// The property under test is that the wrap is **detected, never a silent
/// reuse**, which is a statement about the counter, not about 2^32 resets.
#[test]
fn arena_gen_wraps_safely() {
    // (a) The counter never produces a value it has produced before: at the
    // ceiling it traps rather than returning 0.
    assert_eq!(next_generation(u32::MAX - 1), Ok(u32::MAX));
    assert_eq!(next_generation(u32::MAX), Err(TrapKind::ArenaGeneration));
    assert_ne!(next_generation(u32::MAX), Ok(0), "no silent reuse");

    // (b) `ArenaVal::reset` goes through it, and a trapping reset leaves the
    // counter where it was rather than half-advancing.
    let mut a =
        fors_interp::ArenaVal::new(fors_interp::ArenaId(0), fors_interp::mem::AllocId(1), 64);
    let mut seen = std::collections::BTreeSet::new();
    seen.insert(a.generation);
    for _ in 0..8 {
        a.reset().expect("below the ceiling");
        assert!(seen.insert(a.generation), "a generation was reused");
    }
    a.generation = u32::MAX;
    assert_eq!(a.reset(), Err(TrapKind::ArenaGeneration));
    assert_eq!(a.generation, u32::MAX);
    assert_eq!(a.bump, 0);
}

/// The mechanism `01-ownership/arena-generation-trap` exercises from source,
/// end to end through the dispatch loop: a `Ref` minted before `reset` is
/// dereferenced after it, and ch01 R17 makes that a **program trap**
/// (`arena-generation`), not a `ub:` report — "in every build mode, never
/// elided by optimization level".
#[test]
fn arena_generation_trap_on_a_stale_ref() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let arena_slot = fx.decl.places.intern(0, &[], ptr_ty);
    let ref_slot = fx.decl.places.intern(1, &[], ptr_ty);
    let deref_slot = fx.decl.places.intern(2, &[], ptr_ty);
    let through = fx.decl.places.intern(2, &[Seg::Deref], i64_ty);

    let region = fx.region(RegionKind::WithArena);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let arena = fx.emit(Op::RegionEnter, region.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, arena_slot.0, arena.0, NO_OPERAND, SiteId(0));
    let size = fx.const_int(8, usize_ty);
    let r = fx.emit(Op::ArenaAlloc, arena.0, size.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, ref_slot.0, r.0, NO_OPERAND, SiteId(0));

    // Write, then read back through the live `Ref`: the happy path.
    let p = fx.emit(Op::ArenaDeref, r.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, deref_slot.0, p.0, NO_OPERAND, SiteId(0));
    let v = fx.const_int(1234, i64_ty);
    fx.emit_void(Op::Init, through.0, v.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, through.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("live-ref-ok");

    // ch01 R17: `reset` bumps the generation...
    fx.emit_void(Op::ArenaReset, arena.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    // ...and the `Ref` minted at the old one now traps on dereference.
    let stale = fx.emit(Op::CopyFrom, ref_slot.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let site = fx.site(44, 7);
    let _ = fx.emit_at(
        Op::ArenaDeref,
        stale.0,
        NO_OPERAND,
        NO_OPERAND,
        ptr_ty,
        site,
    );
    fx.print("unreachable");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Trap(TrapKind::ArenaGeneration));
    assert!(
        out.ub.is_none(),
        "R17 makes this a TRAP, not a `ub:` report"
    );
    assert_eq!(lines, ["live-ref-ok"]);
    assert_eq!(out.site, Some((44, 7)));
    assert_eq!(
        fors_interp::trap_line(TrapKind::ArenaGeneration, "main.fors", 44, 7),
        "trap: arena-generation at main.fors:44:7\n"
    );
}

/// `arena_reset` also forgets the bytes, so a fresh `Ref` into the reused
/// space reads as UNINITIALISED rather than as the previous occupant's value
/// (design §5.1's byte-granular `init` map).
#[test]
fn a_reset_arena_forgets_its_bytes() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let deref_slot = fx.decl.places.intern(2, &[], ptr_ty);
    let through = fx.decl.places.intern(2, &[Seg::Deref], i64_ty);

    let region = fx.region(RegionKind::WithArena);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let arena = fx.emit(Op::RegionEnter, region.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let size = fx.const_int(8, usize_ty);
    let r1 = fx.emit(Op::ArenaAlloc, arena.0, size.0, NO_OPERAND, ptr_ty);
    let p1 = fx.emit(Op::ArenaDeref, r1.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, deref_slot.0, p1.0, NO_OPERAND, SiteId(0));
    let v = fx.const_int(7, i64_ty);
    fx.emit_void(Op::Init, through.0, v.0, NO_OPERAND, SiteId(0));
    fx.emit_void(Op::ArenaReset, arena.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    // A FRESH `Ref` at the new generation, into the same bytes.
    let r2 = fx.emit(Op::ArenaAlloc, arena.0, size.0, NO_OPERAND, ptr_ty);
    let p2 = fx.emit(Op::ArenaDeref, r2.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, deref_slot.0, p2.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, through.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UninitRead);
}

// -- the two POSITIVE aliasing cases (ch01 R7, E14) --------------------------

/// ch01 R7: "Two overlapping `let` accesses MUST be ACCEPTED ... two
/// read-only accesses cannot race, and forbidding them would outlaw
/// `f(&x, &x)`-shaped calls that are plainly sound."
///
/// E14 is why this is a GATE and not an afterthought: a single-tag Stacked
/// Borrows would report UB here, and because a `ub:` report exits 70 that
/// would fail the corpus on ACCEPTED code.
#[test]
fn ub_aliasing_accepts_two_let_borrows() {
    let mut fx = Fx::new();
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let x = fx.decl.places.intern(0, &[], i64_ty);
    let pa = fx.decl.places.intern(1, &[], ptr_ty);
    let pb = fx.decl.places.intern(2, &[], ptr_ty);
    let via_a = fx.decl.places.intern(1, &[Seg::Deref], i64_ty);
    let via_b = fx.decl.places.intern(2, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let v = fx.const_int(5, i64_ty);
    fx.emit_void(Op::Init, x.0, v.0, NO_OPERAND, SiteId(0));
    // `f(&x, &x)`: both arguments borrow the same place, by `let`.
    let a = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let b = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, pa.0, a.0, NO_OPERAND, SiteId(0));
    fx.emit_void(Op::Init, pb.0, b.0, NO_OPERAND, SiteId(0));
    // Both stay usable, in either order, and a read pops nothing.
    let _ = fx.emit(Op::CopyFrom, via_a.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let _ = fx.emit(Op::CopyFrom, via_b.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let _ = fx.emit(Op::CopyFrom, via_a.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("two-let-borrows-accepted");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none(), "{:?}", out.ub);
    assert_eq!(lines, ["two-let-borrows-accepted"]);
}

/// The nested shape: a second `let` borrow is taken and used while the first
/// is still live, and the OUTER one is read again afterwards. A model that
/// popped on every new borrow would report the last read.
#[test]
fn ub_aliasing_accepts_nested_let_under_let() {
    let mut fx = Fx::new();
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let x = fx.decl.places.intern(0, &[], i64_ty);
    let outer = fx.decl.places.intern(1, &[], ptr_ty);
    let inner = fx.decl.places.intern(2, &[], ptr_ty);
    let via_outer = fx.decl.places.intern(1, &[Seg::Deref], i64_ty);
    let via_inner = fx.decl.places.intern(2, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let v = fx.const_int(9, i64_ty);
    fx.emit_void(Op::Init, x.0, v.0, NO_OPERAND, SiteId(0));
    let o = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, outer.0, o.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, via_outer.0, NO_OPERAND, NO_OPERAND, i64_ty);
    // ...the inner `let` opens and is used entirely inside the outer's
    // extent...
    let i = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, inner.0, i.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, via_inner.0, NO_OPERAND, NO_OPERAND, i64_ty);
    // ...and the outer is still live after it.
    let _ = fx.emit(Op::CopyFrom, via_outer.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("nested-let-accepted");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none(), "{:?}", out.ub);
    assert_eq!(lines, ["nested-let-accepted"]);
}

/// The matching NEGATIVE: ch01 R7's other half — "Two simultaneous
/// overlapping accesses MUST be rejected if either is `inout`, `sink`, or
/// `set`". A `let` borrow read after an `inout` borrow was taken over it is
/// `ub: aliasing`.
#[test]
fn ub_aliasing_rejects_a_let_read_after_an_inout_borrow() {
    let mut fx = Fx::new();
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let x = fx.decl.places.intern(0, &[], i64_ty);
    let shared = fx.decl.places.intern(1, &[], ptr_ty);
    let unique = fx.decl.places.intern(2, &[], ptr_ty);
    let via_shared = fx.decl.places.intern(1, &[Seg::Deref], i64_ty);
    let via_unique = fx.decl.places.intern(2, &[Seg::Deref], i64_ty);

    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let v = fx.const_int(1, i64_ty);
    fx.emit_void(Op::Init, x.0, v.0, NO_OPERAND, SiteId(0));
    let s = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, shared.0, s.0, NO_OPERAND, SiteId(0));
    let u = fx.emit(Op::BorrowMut, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, unique.0, u.0, NO_OPERAND, SiteId(0));
    let w = fx.const_int(2, i64_ty);
    fx.emit_void(Op::Init, via_unique.0, w.0, NO_OPERAND, SiteId(0));
    let site = fx.site(55, 4);
    let _ = fx.emit_at(
        Op::CopyFrom,
        via_shared.0,
        NO_OPERAND,
        NO_OPERAND,
        i64_ty,
        site,
    );
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));

    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::Aliasing);
    assert_eq!(out.site, Some((55, 4)));
}

// -- use after move (design §5.2's first row) --------------------------------

/// design §5.2: "Use after move — place slot's `live` bit, set false by
/// `move_from`". A compiler bug if it reaches here (ch01 R4a(a) is the
/// checker's), hence a `ub:` report rather than a trap.
#[test]
fn ub_use_after_move() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let x = fx.decl.places.intern(0, &[], i64_ty);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let v = fx.const_int(3, i64_ty);
    fx.emit_void(Op::Init, x.0, v.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::MoveFrom, x.0, NO_OPERAND, NO_OPERAND, i64_ty);
    let site = fx.site(60, 1);
    let _ = fx.emit_at(Op::CopyFrom, x.0, NO_OPERAND, NO_OPERAND, i64_ty, site);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UseAfterMove);
    assert_eq!(out.site, Some((60, 1)));
}

// -- the structural disciplines ----------------------------------------------

/// The task's standing requirement, as a test: the interpreter still has no
/// optimisation-level input (design §3.6, ch02 R10). F6 added allocation,
/// arena and borrow tables and no knob.
#[test]
fn interp_has_no_opt_level_input() {
    let c = fors_interp::Config {
        ptr_bits: 64,
        endian: fors_interp::Endian::Little,
    };
    assert_eq!(c, fors_interp::Config::v0_1());
    // ch01 R17's own words — "in every build mode, never elided by
    // optimization level" — hold because there is no mode to read.
    assert_eq!(c.ptr_bits, 64);
}

/// Owner **Q7**: the backtrace is excluded from the oracle record. Two runs
/// that differ only in the backtrace compare EQUAL under
/// `Outcome::oracle_record`.
#[test]
fn a_backtrace_is_never_part_of_the_oracle_record() {
    let mut fx = Fx::new();
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    fx.print("hello");
    fx.end(fx.term(Op::Trap, TrapKind::Bounds as u32, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    let mut with_backtrace = out.clone();
    with_backtrace.backtrace = vec![fors_interp::BacktraceFrame {
        func: "main".into(),
        line: 1,
        col: 1,
    }];
    assert_ne!(out, with_backtrace);
    assert_eq!(out.oracle_record(), with_backtrace.oracle_record());
}

// -- unchecked_* (design §5.5) -----------------------------------------------

/// design §5.5: "`unchecked_*` is wrapping **plus** a Miri-mode
/// `ub: unchecked-overflow` diagnostic when the true result is out of range
/// (ch03 R4 puts it behind `@unsafe(invariant:)`, so violating the invariant
/// is exactly a UB report, not a trap)."
#[test]
fn ub_unchecked_overflow() {
    let mut fx = Fx::new();
    let i32_ty = fx.ty(PrimKind::I32);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let max = fx.const_int(i64::from(i32::MAX) as u64, i32_ty);
    let one = fx.const_int(1, i32_ty);
    let site = fx.site(70, 2);
    let _ = fx.emit_at(
        Op::Add(fors_fmir::op::ArithMode::Unchecked),
        max.0,
        one.0,
        NO_OPERAND,
        i32_ty,
        site,
    );
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::UncheckedOverflow);
    assert_eq!(out.site, Some((70, 2)));
}

/// In range, the same `unchecked_` op is silent — `wrap_`-style arithmetic
/// with no report, which is what makes the test above meaningful.
#[test]
fn unchecked_in_range_is_silent() {
    let mut fx = Fx::new();
    let i32_ty = fx.ty(PrimKind::I32);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let a = fx.const_int(2, i32_ty);
    let b = fx.const_int(3, i32_ty);
    let _ = fx.emit(
        Op::Add(fors_fmir::op::ArithMode::Unchecked),
        a.0,
        b.0,
        NO_OPERAND,
        i32_ty,
    );
    fx.print("in-range");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, lines) = run_fx(fx);
    assert_eq!(out.exit, Exit::Return);
    assert!(out.ub.is_none());
    assert_eq!(lines, ["in-range"]);
}

// -- verifier-added cases: each detection beside its nearest near-miss ------

/// Heap: a freed object's pointer is rejected even after a FRESH allocation
/// has been made (object identity, not address, is what `AllocState` tracks),
/// and the fresh pointer is accepted.
#[test]
fn a_freed_pointer_is_rejected_after_reallocation_and_the_new_one_accepted() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let i64_ty = fx.ty(PrimKind::I64);
    let old = fx.decl.places.intern(0, &[], ptr_ty);
    let via_old = fx.decl.places.intern(0, &[Seg::Deref], i64_ty);
    let new = fx.decl.places.intern(1, &[], ptr_ty);
    let via_new = fx.decl.places.intern(1, &[Seg::Deref], i64_ty);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let size = fx.const_int(8, usize_ty);
    let align = fx.const_int(8, usize_ty);
    let p1 = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, old.0, p1.0, NO_OPERAND, SiteId(0));
    fx.emit_void(Op::Free, p1.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    let p2 = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, new.0, p2.0, NO_OPERAND, SiteId(0));
    let v = fx.const_int(5, i64_ty);
    fx.emit_void(Op::Init, via_new.0, v.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::CopyFrom, via_new.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.print("new-ok");
    let site = fx.site(3, 3);
    let _ = fx.emit_at(
        Op::CopyFrom,
        via_old.0,
        NO_OPERAND,
        NO_OPERAND,
        i64_ty,
        site,
    );
    fx.print("unreachable");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, lines) = run_fx(fx);
    assert_ub(&out, UbClass::UseAfterFree);
    assert_eq!(lines, ["new-ok"]);
    assert_eq!(out.site, Some((3, 3)));
}

/// Fresh heap bytes are uninitialised until written (design §5.1's
/// byte-granular `init` map), and a write makes the read clean.
#[test]
fn fresh_heap_bytes_are_uninitialised_until_written() {
    for write_first in [false, true] {
        let mut fx = Fx::new();
        let usize_ty = fx.ty(PrimKind::Usize);
        let ptr_ty = fx.ty(PrimKind::RawPtr);
        let i64_ty = fx.ty(PrimKind::I64);
        let slot = fx.decl.places.intern(0, &[], ptr_ty);
        let via = fx.decl.places.intern(0, &[Seg::Deref], i64_ty);
        let entry = fx.reserve();
        fx.begin(entry, ScopeId(0));
        let size = fx.const_int(8, usize_ty);
        let align = fx.const_int(8, usize_ty);
        let p = fx.emit(Op::Alloc, size.0, align.0, NO_OPERAND, ptr_ty);
        fx.emit_void(Op::Init, slot.0, p.0, NO_OPERAND, SiteId(0));
        if write_first {
            let v = fx.const_int(9, i64_ty);
            fx.emit_void(Op::Init, via.0, v.0, NO_OPERAND, SiteId(0));
        }
        let _ = fx.emit(Op::CopyFrom, via.0, NO_OPERAND, NO_OPERAND, i64_ty);
        fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        let (out, _) = run_fx(fx);
        if write_first {
            assert_eq!(out.exit, Exit::Return);
        } else {
            assert_ub(&out, UbClass::UninitRead);
        }
    }
}

/// Nested `with arena` regions (ch01 R15): leaving the OUTER region retires
/// the outer arena, not (again) the inner one, so a `Ref` into it traps
/// `arena-generation` afterwards (ch01 R17).
#[test]
fn leaving_an_outer_arena_region_retires_the_outer_arena() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let ra = fx.region(RegionKind::WithArena);
    let rb = fx.region(RegionKind::WithArena);
    let ref_a = fx.decl.places.intern(0, &[], ptr_ty);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let a = fx.emit(Op::RegionEnter, ra.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let size = fx.const_int(8, usize_ty);
    let r = fx.emit(Op::ArenaAlloc, a.0, size.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Init, ref_a.0, r.0, NO_OPERAND, SiteId(0));
    let b = fx.emit(Op::RegionEnter, rb.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let _ = fx.emit(Op::ArenaAlloc, b.0, size.0, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::RegionExit, rb.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.emit_void(Op::RegionExit, ra.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.print("both-left");
    let stale = fx.emit(Op::CopyFrom, ref_a.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let site = fx.site(8, 8);
    let _ = fx.emit_at(
        Op::ArenaDeref,
        stale.0,
        NO_OPERAND,
        NO_OPERAND,
        ptr_ty,
        site,
    );
    fx.print("unreachable");
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, lines) = run_fx(fx);
    assert_eq!(lines, ["both-left"]);
    assert_eq!(out.exit, Exit::Trap(TrapKind::ArenaGeneration));
    assert!(out.ub.is_none());
    assert_eq!(out.site, Some((8, 8)));
}

/// `arena_alloc` through a handle whose `with arena` block has ended is a
/// use of a reset ARENA allocation, which design §5.2's row sends to ch01
/// R17's program trap, not to `ub: use-after-free`.
#[test]
fn arena_alloc_after_the_region_exits_traps_arena_generation() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let ra = fx.region(RegionKind::WithArena);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let a = fx.emit(Op::RegionEnter, ra.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::RegionExit, ra.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    let size = fx.const_int(8, usize_ty);
    let _ = fx.emit(Op::ArenaAlloc, a.0, size.0, NO_OPERAND, ptr_ty);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    assert_eq!(out.exit, Exit::Trap(TrapKind::ArenaGeneration));
    assert!(out.ub.is_none());
}

/// `free` of a pointer an ARENA produced: no allocator made it, so it is
/// `ub: allocator-mismatch` (the erased case of ch01 R18).
#[test]
fn freeing_an_arena_pointer_is_an_allocator_mismatch() {
    let mut fx = Fx::new();
    let usize_ty = fx.ty(PrimKind::Usize);
    let ptr_ty = fx.ty(PrimKind::RawPtr);
    let ra = fx.region(RegionKind::WithArena);
    let entry = fx.reserve();
    fx.begin(entry, ScopeId(0));
    let a = fx.emit(Op::RegionEnter, ra.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    let size = fx.const_int(8, usize_ty);
    let r = fx.emit(Op::ArenaAlloc, a.0, size.0, NO_OPERAND, ptr_ty);
    let p = fx.emit(Op::ArenaDeref, r.0, NO_OPERAND, NO_OPERAND, ptr_ty);
    fx.emit_void(Op::Free, p.0, NO_OPERAND, NO_OPERAND, SiteId(0));
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    let (out, _) = run_fx(fx);
    assert_ub(&out, UbClass::AllocatorMismatch);
}

/// A write to the binding ITSELF pops every borrow above the root (design
/// §5.2: "only a write or a new unique tag pops"): a `let` borrow of `x`
/// read after `x` is assigned is `ub: aliasing`. The near-miss — the same
/// assignment AFTER the last read through the borrow — is clean.
#[test]
fn a_direct_write_to_the_owner_invalidates_an_outstanding_let_borrow() {
    fn build(write_before_read: bool) -> (fors_interp::Outcome, Vec<String>) {
        let mut fx = Fx::new();
        let i64_ty = fx.ty(PrimKind::I64);
        let ptr_ty = fx.ty(PrimKind::RawPtr);
        let x = fx.decl.places.intern(0, &[], i64_ty);
        let pa = fx.decl.places.intern(1, &[], ptr_ty);
        let via_a = fx.decl.places.intern(1, &[Seg::Deref], i64_ty);
        let entry = fx.reserve();
        fx.begin(entry, ScopeId(0));
        let one = fx.const_int(1, i64_ty);
        fx.emit_void(Op::Init, x.0, one.0, NO_OPERAND, SiteId(0));
        let a = fx.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
        fx.emit_void(Op::Init, pa.0, a.0, NO_OPERAND, SiteId(0));
        let two = fx.const_int(2, i64_ty);
        if write_before_read {
            fx.emit_void(Op::Init, x.0, two.0, NO_OPERAND, SiteId(0));
            let site = fx.site(4, 4);
            let _ = fx.emit_at(Op::CopyFrom, via_a.0, NO_OPERAND, NO_OPERAND, i64_ty, site);
        } else {
            let _ = fx.emit(Op::CopyFrom, via_a.0, NO_OPERAND, NO_OPERAND, i64_ty);
            fx.emit_void(Op::Init, x.0, two.0, NO_OPERAND, SiteId(0));
        }
        fx.print("done");
        fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        run_fx(fx)
    }
    let (out, lines) = build(false);
    assert_eq!(out.exit, Exit::Return);
    assert_eq!(lines, ["done"]);
    let (out, lines) = build(true);
    assert_ub(&out, UbClass::Aliasing);
    assert!(lines.is_empty());
    assert_eq!(out.site, Some((4, 4)));
}

/// A pointer to a RETURNED frame's local, dereferenced by the caller, is
/// design §5.2's "use of a freed allocation" on a stack slot: a `ub:`
/// report, never a panic — and never a silent read of whatever frame now
/// occupies that index (the second round makes a new call first).
#[test]
fn a_pointer_into_a_returned_frame_is_use_after_free() {
    for reuse_index in [false, true] {
        let mut callee = Fx::new();
        let i64_ty = callee.ty(PrimKind::I64);
        let ptr_ty = callee.ty(PrimKind::RawPtr);
        let x = callee.decl.places.intern(0, &[], i64_ty);
        let entry = callee.reserve();
        callee.begin(entry, ScopeId(0));
        let five = callee.const_int(5, i64_ty);
        callee.emit_void(Op::Init, x.0, five.0, NO_OPERAND, SiteId(0));
        let p = callee.emit(Op::Borrow, x.0, NO_OPERAND, NO_OPERAND, ptr_ty);
        callee.end(callee.term(Op::Ret, p.0, NO_OPERAND, NO_OPERAND));

        let mut main = Fx::new();
        let i64_ty = main.ty(PrimKind::I64);
        let ptr_ty = main.ty(PrimKind::RawPtr);
        let holder = main.decl.places.intern(0, &[], ptr_ty);
        let via = main.decl.places.intern(0, &[Seg::Deref], i64_ty);
        let entry = main.reserve();
        main.begin(entry, ScopeId(0));
        let got = fixture::call_callee(&mut main, ptr_ty);
        main.emit_void(Op::Init, holder.0, got.0, NO_OPERAND, SiteId(0));
        if reuse_index {
            let _ = fixture::call_callee(&mut main, ptr_ty);
        }
        let site = main.site(6, 6);
        let _ = main.emit_at(Op::CopyFrom, via.0, NO_OPERAND, NO_OPERAND, i64_ty, site);
        main.print("unreachable");
        main.end(main.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        let (prog, tys) = fixture::program2(main, callee);
        let out = fors_interp::run(&prog, &tys).expect("a clean diagnostic, not a panic");
        assert_ub(&out, UbClass::UseAfterFree);
        assert!(
            fixture::lines_of(&out).is_empty(),
            "reuse_index={reuse_index}"
        );
        assert_eq!(out.site, Some((6, 6)));
        let detail = &out.ub.as_ref().unwrap().detail;
        assert!(detail.contains("frame that has returned"), "{detail}");
    }
}

/// The interpreter ASSERTS discharge records (design §3.5): an obligation
/// that WAS moved out but has no `Discharge` row on the edge is still
/// `ub: linear-leak`, status 70, never exit 0 and never a trap.
#[test]
fn a_moved_obligation_with_no_discharge_record_is_still_a_leak() {
    let mut fx = Fx::new();
    let i64_ty = fx.ty(PrimKind::I64);
    let owed = fx.decl.places.intern(0, &[], i64_ty);
    let (scope, _) = fx.scope(ScopeId::NONE, BrandId::NONE, &[], &[owed]);
    let entry = fx.reserve();
    fx.begin(entry, scope);
    let one = fx.const_int(1, i64_ty);
    fx.emit_void(Op::Init, owed.0, one.0, NO_OPERAND, SiteId(0));
    let _ = fx.emit(Op::MoveFrom, owed.0, NO_OPERAND, NO_OPERAND, i64_ty);
    fx.end(fx.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND));
    fx.exit_raw(
        entry,
        BlockId::NONE,
        ExitKind::Normal,
        &[scope],
        &[],
        &[],
        &[],
    );
    let out = run_fx_unverified(fx).expect("a ub: report");
    assert_ub(&out, UbClass::LinearLeak);
    assert_eq!(entry_exit(&out), ExitStatus::Status(UB_EXIT_STATUS));
}
