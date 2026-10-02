//! I10b's gate: **no silent `TY_ERROR`** (design §10, "a node that cannot
//! be typed is reported, never absorbed").
//!
//! The sweep walks every `BodyFacts` of two builds — the whole `std/`
//! package, exactly as `fors-lower`'s `std_checks_clean` builds it, and
//! every conformance target the corpus marks `check-ok` or `run-ok` — and
//! asserts that no node the checker TYPED ended `TY_ERROR` inside a body
//! that produced no diagnostic. A body that spoke is exempt: design §10's
//! per-declaration budget stops the walk at the root cause, and the nodes
//! after it are honestly unvisited rather than absorbed.
//!
//! What remains open lives in [`ALLOWED`], one named row per node with the
//! rule, the reason and the owner — never a count, so a row that goes quiet
//! fails here and is deleted instead of left stale.

use std::fs;
use std::path::{Path, PathBuf};

use fors_fir::ty::TY_ERROR;
use fors_index::{Interner, Segments, module::is_legal_segment};
use fors_resolve::FileInput;
use fors_syntax::parse_file;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

/// One absorbed node: `target/module:line:col-line:col NodeKind`.
type Offender = String;

// ------------------------------------------- the reasons a row may carry
//
// Each is a rule, why the node is still absorbed, and who owns the fix. They
// are the ONLY reasons [`ALLOWED`] may cite: a new kind of absorption needs a
// new named constant here, written down before its rows are added.

/// ch10 R2 / ch08 R17. The prelude NAMES the eight std types `Allocator`,
/// `AllocError`, `PageAllocator`, `Buffer`, `Vec`, `Map`, `String` and
/// `Utf8Error`, but binds them to no declaration: `fors_fir::prelude`'s
/// `OPAQUE` row is `PreludeEntity::Opaque` and its own comment says "the
/// resolver binds them to real items" when package `std` is in the build —
/// which `fors_resolve`'s `build_prelude` does not do (every name in
/// `PRELUDE_TYPES5` becomes `Entity::PreludeType` unconditionally). So
/// `lower::head_of` answers `Head::Opaque`, `Vec[i32, A]` lowers to
/// `TY_ERROR`, and §7.10's absorbing `TY_ERROR` swallows every expression
/// over such a value — with std's real sources in the build, which this sweep
/// provides. Owner: the increment that binds ch10 R2's prelude names to
/// package `std`'s declarations; until then these rows are the inventory of
/// what it will unlock.
const R2_OPAQUE: &str = "ch10 R2: the prelude names this std type but binds it to no declaration \
                         (PreludeEntity::Opaque), so its type is TY_ERROR and §7.10 absorbs the \
                         expression; owner: ch10 R2's prelude binding";

/// R43 tier (2) on a RIGID receiver bounded by the PRELUDE trait
/// `Iterator`. `lookup_on_rigid` marks the table incomplete whenever a
/// candidate trait is a prelude one — its rows need not list every method,
/// since `Iterator`'s adaptors live in `std` — and answers
/// `LookupError::Silent`, so `it.count()` / `it.take(2)` on an `I: Iterator`
/// absorbs. Owner: the increment that gives `Iterator` its full prelude
/// surface (the same one `prelude_head_table_incomplete` waits for).
const R43_RIGID_ITERATOR: &str = "R43 tier (2) on a rigid receiver bounded by the prelude trait \
                                  `Iterator`: the prelude's rows do not list the adaptors, so \
                                  `lookup_on_rigid` stays silent; owner: `Iterator`'s prelude \
                                  surface";

/// R45's `Tr.name(..)` / `Tr[args].name(..)`: "that trait's function, with
/// `Self` determined like any parameter by Rule 38". `call.rs::
/// qualified_callee` accepts only a struct or enum head, so a trait head is
/// `Callee::Undecided` and the call absorbs. Owner: R45's trait-head form.
const R45_TRAIT_HEAD: &str = "R45: the qualified form on a TRAIT head, whose `Self` R38 \
                              determines, is not classified; owner: R45's trait-head form";

/// R7/R41: calling a value whose type is a callable PARAMETER (`F: fn(let T)
/// -> U`). `Wf::callable_of` reads a `fn` row off the type and a `Param` has
/// none, so `f(x)` inside the generic body is `Callee::Undecided`. Owner:
/// R41's callable parameters.
const R7_CALLABLE_PARAM: &str = "R7/R41: a call of a value whose type is a callable PARAMETER has \
                                 no `fn` row to read; owner: R41's callable parameters";

/// R43 on a `dyn Tr` receiver: `lookup_method` dispatches on the receiver's
/// tag and `TyTag::Dyn` falls into "anything else has no method table.
/// Silent", although a `dyn Tr`'s method table is exactly `Tr`'s. Owner:
/// R25/R43's dyn dispatch.
const R43_DYN: &str = "R43: a `dyn Tr` receiver has no method table in `lookup_method`, although \
                       it is exactly `Tr`'s; owner: R25/R43's dyn dispatch";

/// R40 / ch01 R15b's brand inference, the gap `call.rs::unbound_slot`
/// documents: a BRAND slot R38 could not determine is answered `is_brand` and
/// left silent on purpose, because R40 binds a brand "only from a receiver or
/// argument type" and `one.alloc(Node { val: 1 })` takes `A` from an expected
/// type step (c) does not have — a T0039 there would be the wrong diagnostic.
/// Re-checked for this increment and still open. Owner: ch01 R15b's brand
/// inference.
const R40_BRAND: &str = "R40/ch01 R15b: a brand slot R38 could not determine is silent by \
                         `unbound_slot`'s own carve-out (a T0039 would be the wrong \
                         diagnostic); owner: ch01 R15b's brand inference";

/// ch01 R15: a brand argument named by a VALUE parameter (`fn f(let a:
/// Arena, let x: Own[i32, a])`). The parameter's declared type does not lower
/// to a type this build has, so every read of it absorbs. Owner: ch01 R15's
/// brand-by-parameter form.
const R15_BRAND_PARAM: &str = "ch01 R15: a brand argument named by a VALUE parameter does not \
                               lower, so the parameter's type is TY_ERROR and reads of it absorb; \
                               owner: ch01 R15's brand-by-parameter form";

/// `expr::subsume`'s qualifier branch, by design: "Same bare type, different
/// qualifiers (`iso`/`imm`/`secret`): the qualifier discipline is ch01/ch05's
/// (I8b/I10's), not a judgement this increment owns. Silent and absorbing,
/// never a guess in either direction." Owner: ch01/ch05's qualifier
/// discipline.
const R11_QUALS: &str = "`subsume`: same bare type, different `iso`/`imm`/`secret` qualifiers is \
                         silent and absorbing by design; owner: ch01/ch05's qualifier discipline";

/// The nodes that are still typed `TY_ERROR` with nothing said, each with the
/// rule it belongs to, why it is open and who owns it. A row here is a
/// PROMISE that the node is still silent: the sweep asserts every row is
/// live, so a fix DELETES its row rather than leaving it stale. There is no
/// count anywhere — the list is the inventory.
///
/// Rows are `(target, module, "line:col-line:col", NodeKind, reason)` — the node's
/// own SPAN, which is what tells the nested calls of one chain apart.
const ALLOWED: &[(&str, &str, &str, &str, &str)] = &[
    (
        "01-ownership/closure-capture-keeps-local-in-chain-accepted.fors",
        "m",
        "11:50-11:58",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/closure-capture-keeps-local-in-chain-accepted.fors",
        "m",
        "11:50-11:78",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/defer-with-block-allocator-live-accepted.fors",
        "m",
        "10:30-10:41",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/defer-with-block-allocator-live-accepted.fors",
        "m",
        "10:30-10:42",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/defer-with-block-allocator-live-accepted.fors",
        "m",
        "11:15-11:31",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/linear-spawn-move-accepted.fors",
        "m",
        "21:22-21:33",
        "CallExpr",
        R11_QUALS,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-for-accepted.fors",
        "m",
        "10:14-10:22",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-for-accepted.fors",
        "m",
        "13:12-13:15",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-for-accepted.fors",
        "m",
        "13:5-13:6",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-for-accepted.fors",
        "m",
        "13:5-13:9",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-statement-accepted.fors",
        "m",
        "10:12-10:13",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-statement-accepted.fors",
        "m",
        "10:5-10:6",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-statement-accepted.fors",
        "m",
        "10:5-10:9",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-statement-accepted.fors",
        "m",
        "9:20-9:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-rvalue-extent-is-the-statement-accepted.fors",
        "m",
        "9:20-9:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-through-generic-sink-consumed-accepted.fors",
        "m",
        "9:12-9:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-through-generic-sink-consumed-accepted.fors",
        "m",
        "9:12-9:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-through-generic-sink-returned-under-scoped-accepted.fors",
        "m",
        "10:12-10:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/scoped-through-generic-sink-returned-under-scoped-accepted.fors",
        "m",
        "10:12-10:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:44",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:34",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:42",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "01-ownership/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:25-9:33",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "08-names/param-in-scope-in-later-param-type-accepted.fors",
        "m",
        "9:12-9:13",
        "NameExpr",
        R15_BRAND_PARAM,
    ),
    (
        "09-types/adaptor-annotated-binding-accepted.fors",
        "m",
        "12:61-12:69",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-annotated-binding-accepted.fors",
        "m",
        "12:61-12:81",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-annotated-binding-accepted.fors",
        "m",
        "12:61-12:89",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "10:14-10:25",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "10:14-10:33",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "11:20-11:31",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-for-then-reuse-accepted.fors",
        "m",
        "11:20-11:39",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:26",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:34",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-field-accepted.fors",
        "m",
        "11:12-11:42",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:23",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:31",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-by-ref-on-inout-accepted.fors",
        "m",
        "9:12-9:39",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-across-question-accepted.fors",
        "m",
        "13:20-13:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-across-question-accepted.fors",
        "m",
        "13:20-13:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-across-question-accepted.fors",
        "m",
        "13:20-13:44",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-as-for-iterable-accepted.fors",
        "m",
        "12:14-12:22",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-as-for-iterable-accepted.fors",
        "m",
        "12:14-12:34",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-as-for-iterable-accepted.fors",
        "m",
        "12:14-12:42",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-closure-accepted.fors",
        "m",
        "9:20-9:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-closure-accepted.fors",
        "m",
        "9:20-9:48",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-closure-accepted.fors",
        "m",
        "9:20-9:56",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-method-accepted.fors",
        "m",
        "12:12-12:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-method-accepted.fors",
        "m",
        "12:12-12:32",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-method-accepted.fors",
        "m",
        "12:12-12:46",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-method-accepted.fors",
        "m",
        "12:12-12:54",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-method-accepted.fors",
        "m",
        "12:12-12:62",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:22",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:30",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:42",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-on-adaptor-receiver-accepted.fors",
        "m",
        "9:12-9:50",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:12-11:32",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:12-11:40",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-chain-rigid-receiver-accepted.fors",
        "m",
        "11:19-11:31",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-name-clash-qualified-accepted.fors",
        "m",
        "9:12-9:37",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/adaptor-name-clash-qualified-accepted.fors",
        "m",
        "9:12-9:45",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/adaptor-stored-then-chained-accepted.fors",
        "m",
        "12:50-12:58",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/adaptor-stored-then-chained-accepted.fors",
        "m",
        "12:50-12:70",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/brand-inferred-for-callee-accepted.fors",
        "m",
        "12:38-12:64",
        "CallExpr",
        R40_BRAND,
    ),
    (
        "09-types/brand-inferred-for-callee-accepted.fors",
        "m",
        "12:48-12:63",
        "StructLit",
        R40_BRAND,
    ),
    (
        "09-types/callable-bound-closure-accepted.fors",
        "m",
        "8:69-8:73",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/concrete-to-dyn-accepted.fors",
        "m",
        "11:43-11:51",
        "CallExpr",
        R43_DYN,
    ),
    (
        "09-types/consumer-count-drops-items-accepted.fors",
        "m",
        "11:12-11:22",
        "CallExpr",
        R43_RIGID_ITERATOR,
    ),
    (
        "09-types/dyn-param-in-generic-body-accepted.fors",
        "m",
        "10:36-10:42",
        "CallExpr",
        R43_DYN,
    ),
    (
        "09-types/generic-raises-type-accepted.fors",
        "m",
        "8:94-8:98",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/generic-raises-type-accepted.fors",
        "m",
        "8:94-8:99",
        "TryExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/map-sum-closure-checked-accepted.fors",
        "m",
        "19:31-19:40",
        "CallExpr",
        R7_CALLABLE_PARAM,
    ),
    (
        "09-types/qualified-trait-call-accepted.fors",
        "m",
        "10:53-10:64",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/qualified-trait-call-accepted.fors",
        "m",
        "10:67-10:81",
        "CallExpr",
        R45_TRAIT_HEAD,
    ),
    (
        "09-types/try-fold-method-accepted.fors",
        "m",
        "16:12-16:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/try-fold-method-accepted.fors",
        "m",
        "16:12-16:37",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "09-types/try-fold-method-accepted.fors",
        "m",
        "16:12-16:38",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/adaptor-chain-accepted.fors",
        "m",
        "13:12-13:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/adaptor-chain-accepted.fors",
        "m",
        "13:12-13:32",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/adaptor-chain-accepted.fors",
        "m",
        "13:12-13:46",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/adaptor-chain-accepted.fors",
        "m",
        "13:12-13:54",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/adaptor-chain-accepted.fors",
        "m",
        "13:12-13:62",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/buffer-fields-public-accepted.fors",
        "m",
        "11:20-11:21",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/buffer-fields-public-accepted.fors",
        "m",
        "11:5-11:17",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "10-std/buffer-in-module-without-allocator-accepted.fors",
        "m",
        "10:12-10:21",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/buffer-in-module-without-allocator-accepted.fors",
        "m",
        "9:31-9:45",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-count-method-accepted.fors",
        "m",
        "10:5-10:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-count-method-accepted.fors",
        "m",
        "10:5-10:19",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-count-method-accepted.fors",
        "m",
        "9:20-9:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-count-method-accepted.fors",
        "m",
        "9:20-9:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-fold-method-accepted.fors",
        "m",
        "11:12-11:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/consumer-fold-method-accepted.fors",
        "m",
        "11:12-11:33",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/fixed-allocator-in-needs-empty-module-accepted.fors",
        "m",
        "11:36-11:45",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/fixed-allocator-in-needs-empty-module-accepted.fors",
        "m",
        "12:15-12:33",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/fixed-allocator-in-needs-empty-module-accepted.fors",
        "m",
        "13:9-13:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/fixed-allocator-in-needs-empty-module-accepted.fors",
        "m",
        "13:9-13:29",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/fs-name-dotdot-invalid-run-ok.fors",
        "app",
        "11:31-11:45",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "11:29-11:38",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "12:11-12:26",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "12:21-12:25",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:13-13:17",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:5-13:21",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/heap-brand-named-by-parameter-accepted.fors",
        "app",
        "13:5-13:22",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:11-10:12",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:16-10:17",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:16-10:20",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:16-10:24",
        "MulExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:18-10:19",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:23-10:24",
        "Literal",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:9-10:10",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "10:9-10:13",
        "Bracket",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "9:14-9:15",
        "Literal",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "9:14-9:27",
        "RangeExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/index-loop-mutates-accepted.fors",
        "m",
        "9:20-9:27",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "10:14-10:26",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "11:5-11:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "11:5-11:19",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "12:12-12:18",
        "UnaryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "12:17-12:18",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/linear-moved-to-caller-accepted.fors",
        "m",
        "9:26-9:35",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "11:29-11:43",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "11:29-11:44",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:17-12:23",
        "UnaryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:22-12:23",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/main-heap-parameter-accepted.fors",
        "app",
        "12:5-12:24",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/prelude-alloc-error-without-import-accepted.fors",
        "m",
        "9:23-9:43",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/prelude-page-allocator-without-import-accepted.fors",
        "m",
        "10:33-10:47",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/prelude-page-allocator-without-import-accepted.fors",
        "m",
        "10:33-10:48",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/prelude-page-allocator-without-import-accepted.fors",
        "m",
        "11:9-11:28",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/prelude-vec-without-import-accepted.fors",
        "m",
        "8:54-8:61",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-collect-into-is-free-function-accepted.fors",
        "m",
        "12:26-12:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-collect-into-is-free-function-accepted.fors",
        "m",
        "12:39-12:42",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-for-each-error-propagates-run-ok.fors",
        "app",
        "11:22-11:46",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-for-each-method-accepted.fors",
        "m",
        "13:5-13:13",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-for-each-method-accepted.fors",
        "m",
        "13:5-13:32",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/try-for-each-method-accepted.fors",
        "m",
        "13:5-13:33",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-defer-accepted.fors",
        "m",
        "10:11-10:23",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-defer-accepted.fors",
        "m",
        "11:5-11:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-defer-accepted.fors",
        "m",
        "11:5-11:19",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-defer-accepted.fors",
        "m",
        "9:26-9:35",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "10:14-10:26",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "11:5-11:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "11:5-11:19",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "12:5-12:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "12:5-12:19",
        "TryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "13:12-13:18",
        "UnaryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "13:17-13:18",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-consumed-by-errdefer-then-returned-accepted.fors",
        "m",
        "9:26-9:35",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-always-empty-deinit-accepted.fors",
        "m",
        "10:5-10:17",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-always-empty-deinit-accepted.fors",
        "m",
        "9:26-9:35",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "10:11-10:18",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "10:21-10:22",
        "Literal",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "11:15-11:22",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "12:30-12:46",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "16:5-16:23",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "9:34-9:40",
        "UnaryExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/vec-linear-element-pop-then-deinit-empty-accepted.fors",
        "m",
        "9:39-9:40",
        "NameExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:36",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-scoped-and-owned-accepted.fors",
        "m",
        "9:12-9:44",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:20",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:34",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:12-9:42",
        "CallExpr",
        R2_OPAQUE,
    ),
    (
        "10-std/zip-two-scoped-sources-local-accepted.fors",
        "m",
        "9:25-9:33",
        "CallExpr",
        R2_OPAQUE,
    ),
];

/// Byte offset to `line:col`, both 1-based, counting bytes in the column
/// (the corpus is ASCII, and a byte column is what every other harness in
/// this repo prints).
fn line_col(src: &[u8], at: u32) -> (usize, usize) {
    let at = (at as usize).min(src.len());
    let mut line = 1usize;
    let mut bol = 0usize;
    for (i, &b) in src[..at].iter().enumerate() {
        if b == b'\n' {
            line += 1;
            bol = i + 1;
        }
    }
    (line, at - bol + 1)
}

/// Resolves, checks, and reports every node that ended [`TY_ERROR`] inside a
/// body whose declaration produced no diagnostic.
fn sweep(
    build: &str,
    names: Vec<Segments>,
    sources: Vec<Vec<u8>>,
    root: Option<usize>,
    package: Option<&[u8]>,
    interner: &mut Interner,
) -> Vec<Offender> {
    let module_names: Vec<String> = names
        .iter()
        .map(|n| {
            n.iter()
                .map(|s| String::from_utf8_lossy(interner.resolve(*s)).into_owned())
                .collect::<Vec<_>>()
                .join(".")
        })
        .collect();
    let parsed: Vec<_> = sources.iter().map(|s| parse_file(s)).collect();
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve_in_package(interner, &inputs, root, package);
    let out = fors_check::check_build(&inputs, &resolved, interner);
    let Some(defs) = out.defs.as_ref() else {
        return Vec::new();
    };
    let mut offenders = Vec::new();
    for (def, facts) in &out.facts {
        let Some(row) = defs.get(*def) else { continue };
        let fi = row.file.index();
        if fi >= inputs.len() {
            continue;
        }
        let tree = inputs[fi].tree;
        let tokens = inputs[fi].tokens;
        let src = inputs[fi].source;
        let (start, end) = facts.range();
        if start as usize >= tree.len() {
            continue;
        }
        // The declaration's byte span, for attributing a diagnostic to this
        // body: §10's budget is per DECLARATION, so a signature-level
        // diagnostic exempts its body too.
        let (t0, t1) = tree.token_range(start as usize);
        let last = tokens.starts.len().saturating_sub(1);
        let b0 = tokens.starts.get(t0 as usize).copied().unwrap_or(0);
        let b1 = tokens
            .starts
            .get((t1 as usize).min(last))
            .copied()
            .unwrap_or(u32::MAX);
        let spoke = out
            .diagnostics
            .iter()
            .any(|d| d.file == row.file && d.start >= b0 && d.start <= b1);
        if spoke {
            continue;
        }
        for n in start..end.min(tree.len() as u32) {
            if facts.ty_of(n) != TY_ERROR {
                continue;
            }
            // The node's first and last REAL tokens: a node's token range
            // opens on the trivia before it, which would print the previous
            // line's end — and the SPAN is what tells the nested calls of
            // `v.iter().map(d).count()` apart, since they all start at the
            // same column.
            let (t_a, t_b) = tree.token_range(n as usize);
            let hi = (t_b as usize).min(tokens.kinds.len());
            let real: Vec<usize> = (t_a as usize..hi)
                .filter(|&i| !tokens.kinds[i].is_trivia())
                .collect();
            let first = real.first().copied().unwrap_or(t_a as usize);
            let last = real.last().copied().unwrap_or(first);
            let at = tokens.starts.get(first).copied().unwrap_or(0);
            let to = tokens
                .starts
                .get(last + 1)
                .copied()
                .unwrap_or_else(|| tokens.starts.get(last).copied().unwrap_or(0));
            let (line, col) = line_col(src, at);
            let (eline, ecol) = line_col(src, to);
            offenders.push(format!(
                "{build}/{}:{line}:{col}-{eline}:{ecol} {:?}",
                module_names[fi], tree.kinds[n as usize]
            ));
        }
    }
    offenders.sort();
    offenders
}

// --------------------------------------------------------------- the builds

/// Every `std/*.fors` module under the name ch08 R17's synthetic table gives
/// it — the same 15 files, in the same order, as `fors-lower`'s
/// `std_checks_clean`.
fn std_module_sources() -> Vec<(Vec<Vec<u8>>, Vec<u8>)> {
    let root = repo_root().join("std");
    let files: &[(&str, &[&str])] = &[
        ("io.fors", &["std", "io"]),
        ("mem.fors", &["std", "mem"]),
        ("mem/alloc.fors", &["std", "mem", "alloc"]),
        ("mem/vec.fors", &["std", "mem", "vec"]),
        ("mem/seq.fors", &["std", "mem", "seq"]),
        ("mem/text.fors", &["std", "mem", "text"]),
        ("mem/hashmap.fors", &["std", "mem", "hashmap"]),
        ("fs.fors", &["std", "fs"]),
        ("net.fors", &["std", "net"]),
        ("proc.fors", &["std", "proc"]),
        ("rand.fors", &["std", "rand"]),
        ("time.fors", &["std", "time"]),
        ("env.fors", &["std", "env"]),
        ("ffi.fors", &["std", "ffi"]),
        ("gpu.fors", &["std", "gpu"]),
    ];
    files
        .iter()
        .map(|(rel, segs)| {
            let src = fs::read(root.join(rel)).expect("std module reads");
            let segs: Vec<Vec<u8>> = segs.iter().map(|s| s.as_bytes().to_vec()).collect();
            (segs, src)
        })
        .collect()
}

fn std_offenders() -> Vec<Offender> {
    let mut interner = Interner::new();
    let mut names: Vec<Segments> = Vec::new();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    for (segs, s) in std_module_sources() {
        names.push(
            segs.iter()
                .map(|b| interner.intern(b))
                .collect::<Segments>(),
        );
        sources.push(s);
    }
    sweep("std", names, sources, None, None, &mut interner)
}

/// The `expect:` directive of a corpus target (`main.fors` for a directory).
fn expect_of(target: &Path) -> String {
    let src = if target.is_dir() {
        fs::read_to_string(target.join("main.fors")).unwrap_or_default()
    } else {
        fs::read_to_string(target).unwrap_or_default()
    };
    for line in src.lines() {
        let Some(rest) = line.strip_prefix("//!") else {
            break;
        };
        if let Some(v) = rest.trim().strip_prefix("expect:") {
            return v.split("--").next().unwrap_or(v).trim().to_string();
        }
    }
    String::new()
}

fn header_name(source: &[u8], interner: &mut Interner) -> Option<Segments> {
    let p = parse_file(source);
    if p.tree.is_empty() {
        return None;
    }
    let child = p.tree.children(0).next()?;
    if p.tree.kinds[child] != fors_syntax::NodeKind::ModuleHdr {
        return None;
    }
    let path_node = p.tree.children(child).next()?;
    let (first, end) = p.tree.token_range(path_node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if p.tokens.kinds[i] == fors_lex::TokenKind::Ident {
            out.push(interner.intern(p.tokens.text(i, source)));
        }
    }
    (!out.is_empty()).then_some(out)
}

/// Every chapter's targets: a `.fors` file or a multi-file directory.
fn corpus_targets() -> Vec<PathBuf> {
    let root = repo_root().join("tests/conformance");
    let mut chapters: Vec<PathBuf> = fs::read_dir(&root)
        .expect("the conformance corpus is present")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    chapters.sort();
    let mut out = Vec::new();
    for ch in chapters {
        let mut entries: Vec<PathBuf> = fs::read_dir(&ch)
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .collect();
        entries.sort();
        for p in entries {
            if p.is_dir() || p.extension().is_some_and(|e| e == "fors") {
                out.push(p);
            }
        }
    }
    out
}

fn corpus_offenders() -> (usize, Vec<Offender>) {
    let mut targets = 0usize;
    let mut offenders = Vec::new();
    for target in corpus_targets() {
        let expect = expect_of(&target);
        if expect != "check-ok" && expect != "run-ok" {
            continue;
        }
        targets += 1;
        let mut interner = Interner::new();
        let mut names: Vec<Segments> = Vec::new();
        let mut sources: Vec<Vec<u8>> = Vec::new();
        let mut root = None;
        if target.is_dir() {
            let mut paths = Vec::new();
            walk(&target, &mut paths);
            for p in &paths {
                let src = fs::read(p).unwrap();
                let rel = p.strip_prefix(&target).unwrap_or(p);
                let comps: Vec<_> = rel.components().collect();
                let mut segs = Vec::new();
                for (i, c) in comps.iter().enumerate() {
                    let os = c.as_os_str().to_string_lossy();
                    let seg = if i + 1 == comps.len() {
                        os.strip_suffix(".fors").unwrap_or(&os).to_string()
                    } else {
                        os.to_string()
                    };
                    segs.push(interner.intern(seg.as_bytes()));
                }
                if comps.len() == 1 && rel.file_stem().is_some_and(|s| s == "main") {
                    root = Some(sources.len());
                }
                names.push(segs);
                sources.push(src);
            }
        } else {
            let src = fs::read(&target).unwrap();
            let name = header_name(&src, &mut interner).unwrap_or_else(|| {
                let stem = target.file_stem().unwrap().to_string_lossy().into_owned();
                let stem = if is_legal_segment(stem.as_bytes()) {
                    stem
                } else {
                    "m".to_string()
                };
                vec![interner.intern(stem.as_bytes())]
            });
            names.push(name);
            sources.push(src);
            root = Some(0);
        }
        // `std/` goes in the build too, exactly as `fors-lower`'s
        // `build_and_run_with_std` does it. Without it there is no `impl Str`,
        // no `impl Slice` and no `seq`, so the documented carve-outs
        // (`prim_table_incomplete`, `prelude_head_table_incomplete`) make
        // silence the CORRECT answer for a hundred more nodes and the sweep
        // would be measuring the missing sources rather than the judgement.
        for (segs, s) in std_module_sources() {
            names.push(
                segs.iter()
                    .map(|b| interner.intern(b))
                    .collect::<Segments>(),
            );
            sources.push(s);
        }
        let label = target
            .strip_prefix(repo_root().join("tests/conformance"))
            .unwrap_or(&target)
            .to_string_lossy()
            .into_owned();
        let root = Some(root.unwrap_or(0));
        offenders.extend(
            sweep(&label, names, sources, root, None, &mut interner)
                .into_iter()
                // `std`'s own bodies are swept once, by `std_offenders`.
                .filter(|l| !l.contains("/std."))
                .collect::<Vec<_>>(),
        );
    }
    offenders.sort();
    (targets, offenders)
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            walk(&p, out);
        } else if p.extension().is_some_and(|e| e == "fors") {
            out.push(p);
        }
    }
}

// ---------------------------------------------------------------- the gate

/// Whether an offender line is one [`ALLOWED`] names, by target, module,
/// position AND node kind: a different node at the same place is a new
/// absorption and fails.
fn allowed(line: &str) -> Option<usize> {
    ALLOWED
        .iter()
        .position(|&(target, module, at, kind, _)| line == format!("{target}/{module}:{at} {kind}"))
}

#[test]
fn no_silent_ty_error_anywhere() {
    let mut offenders = std_offenders();
    let (targets, corpus) = corpus_offenders();
    assert!(
        targets >= 200,
        "only {targets} check-ok/run-ok corpus targets: the sweep found nothing to sweep"
    );
    offenders.extend(corpus);
    let mut hit = vec![false; ALLOWED.len()];
    let mut unexplained = Vec::new();
    for line in &offenders {
        match allowed(line) {
            Some(i) => hit[i] = true,
            None => unexplained.push(line.clone()),
        }
    }
    assert!(
        unexplained.is_empty(),
        "{} node(s) were typed TY_ERROR with nothing said (design §10: a node that cannot be \
         typed is REPORTED, never absorbed). Fix the judgement, or add a named row to \
         `ALLOWED` with its rule, reason and owner:\n{}",
        unexplained.len(),
        unexplained.join("\n")
    );
    for (i, row) in ALLOWED.iter().enumerate() {
        assert!(
            hit[i],
            "the ALLOWED row {row:?} is no longer silent: DELETE it instead of leaving it stale"
        );
    }
}
