//! Bodies: the per-declaration state the two judgements run in, the
//! statement forms of ch09 R31-R33, and the driver of design §7.1 phase 6.
//!
//! One body is one left-to-right pass (R1). Nothing a body creates outlives
//! it: `BodyCx` is dropped at the end of the declaration, the type store
//! only ever gains complete, normal rows, and no inference variable exists
//! at any point — `no_infer_variable_is_interned` is the statement of that
//! from the store's side.

use fors_fir::prelude::{gty, tr};
use fors_fir::sig::{Conv, SigKind};
use fors_fir::ty::{ArgsId, NO_TY, PrimKind, TY_ERROR, TY_NEVER, TY_UNIT, TyId, TyTag};
use fors_index::Symbol;
use fors_index::decl::DeclKind;
use fors_index::ids::{DefId, FileId};
use fors_lex::TokenKind;
use fors_resolve::paths::own_span;
use fors_syntax::NodeKind;

use crate::diag::t;
use crate::lower::{self, FileCtx, Lowered};
use crate::tape::{Cause, Seg, UseKind, UseTape};
use crate::wf::Wf;

/// What a body-local name denotes. Design §7.3's `local_kind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LocalKind {
    Value,
    TypeParam,
    ConstParam,
    BrandParam,
    Callable,
    SelfOfImpl,
    SelfOfTrait,
}

/// The mode a sub-expression was typed in — recorded so
/// `check_positions_match_ch03_r25` can compare the trace against
/// [`CHECK_SITES`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CheckSite {
    /// The syntactic parent that put the expression in CHECK mode.
    pub parent: NodeKind,
    /// Which slot of that parent (design §11: "(parent, slot, mode)").
    pub slot: Slot,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Slot {
    /// The initialiser of an annotated `let`/`var`/`const`.
    AnnotatedInit,
    /// The right side of an assignment.
    AssignRhs,
    /// A `return` operand.
    ReturnValue,
    /// A struct-literal field initialiser.
    FieldInit,
    /// A call argument whose parameter type mentions no parameter.
    Argument,
    /// An element of a CHECK-mode array literal, or any element after the
    /// first of a SYNTH-mode one.
    ArrayElement,
    /// The tail expression or arm of a CHECK-mode block, `if` or `match`.
    Tail,
    /// ch09's own additions to ch03 R25's list, each named by its rule.
    /// R29: the right operand of an operator, whose parameter type is the
    /// left operand's complete type.
    OperatorRhs,
    /// R29/R47: the index of `a[i]` when exactly one `Index` impl matched.
    IndexOperand,
    /// R30: an `if`/`while` condition, a `grain`, a `not`/`and`/`or`
    /// operand — a fixed `bool`/`usize`.
    Condition,
    /// R31: a `for`/`while`/`parallel`/`with`/attribute/`defer` body, and a
    /// non-tail statement-form `if`/`match`: all checked against `()`.
    UnitBody,
    /// R36: a handler block, checked against the call's success type.
    HandlerBlock,
    /// R31: `raise e`, checked against the enclosing `raises` type.
    RaiseValue,
}

/// ch03 R25's enumeration, plus the positions ch09's own rules add, each
/// with the rule that puts it there. The `corpus` flag marks the rows the
/// ch09 corpus is expected to exercise, so a row that silently stops being
/// reached fails the test rather than rotting.
pub struct CheckSiteRow {
    pub parent: NodeKind,
    pub slot: Slot,
    pub rule: u16,
    pub corpus: bool,
}

pub const CHECK_SITES: &[CheckSiteRow] = &[
    CheckSiteRow {
        parent: NodeKind::LetStmt,
        slot: Slot::AnnotatedInit,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::AssignStmt,
        slot: Slot::AssignRhs,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::ReturnStmt,
        slot: Slot::ReturnValue,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::RaiseStmt,
        slot: Slot::RaiseValue,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::FInit,
        slot: Slot::FieldInit,
        rule: 34,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::CallExpr,
        slot: Slot::Argument,
        rule: 38,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::StructLit,
        slot: Slot::Argument,
        rule: 34,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::ArrayLit,
        slot: Slot::ArrayElement,
        rule: 22,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::Block,
        slot: Slot::Tail,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::IfExpr,
        slot: Slot::Tail,
        rule: 32,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::MatchExpr,
        slot: Slot::Tail,
        rule: 32,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::AddExpr,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::MulExpr,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::BitExpr,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::CmpExpr,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::RangeExpr,
        slot: Slot::OperatorRhs,
        rule: 30,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::UnaryExpr,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::AssignStmt,
        slot: Slot::OperatorRhs,
        rule: 29,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::Bracket,
        slot: Slot::IndexOperand,
        rule: 29,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::IfExpr,
        slot: Slot::Condition,
        rule: 30,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::WhileStmt,
        slot: Slot::Condition,
        rule: 30,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::AndExpr,
        slot: Slot::Condition,
        rule: 30,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::OrExpr,
        slot: Slot::Condition,
        rule: 30,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::NotExpr,
        slot: Slot::Condition,
        rule: 30,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::ParallelForStmt,
        slot: Slot::Condition,
        rule: 30,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::ForStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::WhileStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::ParallelStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::ParallelForStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::SimdForStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::WithStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::AttrBlockStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: false,
    },
    CheckSiteRow {
        parent: NodeKind::DeferStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::ErrdeferStmt,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::Block,
        slot: Slot::UnitBody,
        rule: 31,
        corpus: true,
    },
    CheckSiteRow {
        parent: NodeKind::Handler,
        slot: Slot::HandlerBlock,
        rule: 36,
        corpus: true,
    },
];

/// One `defer`/`errdefer` body being typed (R33's round-6 clause).
pub struct DeferFrame {
    /// The `DeferStmt`/`ErrdeferStmt` node, for the diagnostic's wording.
    node: u32,
    errdefer: bool,
    /// `loop_depth` on entry: a `break` is legal only inside a loop opened
    /// after this point.
    loops_outside: u32,
}

/// Per-declaration typing state (design §7.3). Indexed by `node - start`,
/// so a lookup is one bounds check and no hashing; the vectors are sized
/// once from the declaration's own subtree.
pub struct BodyCx<'f, 'a> {
    pub f: &'a FileCtx<'f>,
    /// The declaration whose body this is.
    pub owner: DefId,
    /// The declaration a diagnostic is charged to (the same, for now).
    pub home: DefId,
    pub file: FileId,
    start: u32,
    end: u32,
    /// The declared result type the body is checked against.
    pub result: TyId,
    /// The declared `raises` type, or [`NO_TY`].
    pub raises: TyId,
    local_ty: Vec<TyId>,
    local_kind: Vec<LocalKind>,
    /// Bindings whose introducing node lies OUTSIDE this subtree: `Self`
    /// and the enclosing `impl`/`trait`'s generic parameters.
    outer: Vec<(u32, TyId, LocalKind)>,
    diagnosed: Vec<bool>,
    loop_depth: u32,
    defers: Vec<DeferFrame>,
    /// Depth of closure nesting: `return` inside a closure is R35's error,
    /// not R31's.
    pub closures: u32,
    // MARC: verification of I3 (2026-09-20). A closure body is a function
    // body of its own: `break`/`continue` inside it do not target the
    // enclosing loop, a `return` returns from the closure (R35: rejected in
    // SYNTH mode, checked against the `fn` type's result in CHECK mode),
    // and `?`/`raise` use the closure's `raises` type (none in SYNTH mode).
    // `enter_closure`/`leave_closure` swap the loop depth, the `defer`
    // frames and the result/`raises` pair for the closure's own.
    /// Innermost first: `true` for a SYNTH-mode closure.
    pub closure_synth: Vec<bool>,
    /// The `TryExpr` node whose immediate operand is the call being typed,
    /// set by the `?` arms of `synth`/`check` and taken by `call_expr`.
    pub under_try: Option<u32>,
    pub tape: UseTape,
    pub sites: Vec<CheckSite>,
    /// The lowering context for the body's own type annotations, built once
    /// per declaration (R11 and R61 apply to a `let`'s annotation exactly as
    /// they do to a parameter's).
    pub lcx: lower::Cx<'f, 'a>,
    pub nodes: u64,
    /// While non-zero, [`Wf::bemit`] says nothing: the sub-expression being
    /// typed is one this increment reads on speculation (R47's bracket,
    /// whose reading I4 decides), and a diagnostic from it would be a guess.
    pub quiet: u32,
}

impl<'f, 'a> BodyCx<'f, 'a> {
    fn new(
        f: &'a FileCtx<'f>,
        owner: DefId,
        file: FileId,
        decl: u32,
        lcx: lower::Cx<'f, 'a>,
    ) -> BodyCx<'f, 'a> {
        let end = f.tree.subtree_end(decl as usize) as u32;
        let n = (end - decl) as usize;
        BodyCx {
            f,
            owner,
            home: owner,
            file,
            start: decl,
            end,
            result: TY_UNIT,
            raises: NO_TY,
            local_ty: vec![NO_TY; n],
            local_kind: vec![LocalKind::Value; n],
            outer: Vec::new(),
            diagnosed: vec![false; n],
            loop_depth: 0,
            defers: Vec::new(),
            closures: 0,
            closure_synth: Vec::new(),
            under_try: None,
            tape: UseTape::new(),
            sites: Vec::new(),
            lcx,
            nodes: 0,
            quiet: 0,
        }
    }

    fn inside(&self, node: u32) -> bool {
        node >= self.start && node < self.end
    }

    pub fn bind(&mut self, node: u32, ty: TyId, kind: LocalKind) {
        if self.inside(node) {
            let i = (node - self.start) as usize;
            self.local_ty[i] = ty;
            self.local_kind[i] = kind;
        } else {
            self.outer.push((node, ty, kind));
        }
    }

    pub fn local(&self, node: u32) -> Option<(TyId, LocalKind)> {
        if self.inside(node) {
            let i = (node - self.start) as usize;
            let t = self.local_ty[i];
            if t == NO_TY {
                return None;
            }
            return Some((t, self.local_kind[i]));
        }
        self.outer
            .iter()
            .rev()
            .find(|&&(n, ..)| n == node)
            .map(|&(_, t, k)| (t, k))
    }

    /// Marks `node` as having produced a diagnostic; answers whether it had
    /// already (design §10's one-diagnostic-per-node bitset).
    fn mark(&mut self, node: usize) -> bool {
        let n = node as u32;
        if !self.inside(n) {
            return false;
        }
        let i = (n - self.start) as usize;
        let was = self.diagnosed[i];
        self.diagnosed[i] = true;
        was
    }

    /// [`BodyCx::mark`] for the modules that emit another chapter's code.
    pub fn mark_pub(&mut self, node: usize) -> bool {
        self.mark(node)
    }

    /// Whether the node being typed lies inside a `defer`/`errdefer` body
    /// (R33's round-6 clause).
    pub fn in_defer_body(&self) -> bool {
        !self.defers.is_empty()
    }

    /// The keyword of the innermost deferred body, for its diagnostic.
    pub fn defer_word(&self) -> &'static str {
        match self.defers.last() {
            Some(f) if f.errdefer => "errdefer",
            _ => "defer",
        }
    }

    /// Enters a closure body (see the field comment on `closure_synth`).
    /// Returns what `leave_closure` restores.
    pub fn enter_closure(
        &mut self,
        synth: bool,
        result: TyId,
        raises: TyId,
    ) -> (u32, Vec<DeferFrame>, TyId, TyId) {
        let saved = (
            self.loop_depth,
            std::mem::take(&mut self.defers),
            self.result,
            self.raises,
        );
        self.loop_depth = 0;
        self.result = result;
        self.raises = raises;
        self.closures += 1;
        self.closure_synth.push(synth);
        saved
    }

    pub fn leave_closure(&mut self, saved: (u32, Vec<DeferFrame>, TyId, TyId)) {
        self.loop_depth = saved.0;
        self.defers = saved.1;
        self.result = saved.2;
        self.raises = saved.3;
        self.closures -= 1;
        self.closure_synth.pop();
    }

    /// Whether the innermost enclosing closure is in SYNTH mode.
    pub fn in_synth_closure(&self) -> bool {
        self.closure_synth.last().copied().unwrap_or(false)
    }

    pub fn range(&self, node: usize) -> (u32, u32) {
        fors_resolve::paths::byte_range(self.f.tree, self.f.tokens, node)
    }

    pub fn kind(&self, node: usize) -> NodeKind {
        self.f.tree.kinds[node]
    }

    pub fn kids(&self, node: usize) -> Vec<usize> {
        self.f.tree.children(node).collect()
    }

    /// Records that `node` was typed in CHECK mode because of `parent`'s
    /// `slot` (design §11's `check_positions_match_ch03_r25`).
    pub fn site(&mut self, parent: NodeKind, slot: Slot) {
        // One row per distinct (parent, slot): the test compares SETS, and a
        // corpus of 900 targets would otherwise push millions of rows.
        if !self
            .sites
            .iter()
            .any(|s| s.parent == parent && s.slot == slot)
        {
            self.sites.push(CheckSite { parent, slot });
        }
    }
}

// --------------------------------------------------------------- driver

impl Wf<'_> {
    /// Design §7.1 phase 6: every body in declaration order.
    pub fn bodies(&mut self, low: &Lowered, files: &[FileCtx]) {
        let user: Vec<DefId> = self.defs.user_defs().map(|(d, _)| d).collect();
        for def in user {
            let row = *self.defs.get(def).expect("user def has a row");
            if row.kind != DeclKind::Fn {
                continue;
            }
            if self.already_spoke(low, def, row.parent) {
                self.bodies_skipped += 1;
                continue;
            }
            let f = &files[row.file.index()];
            let decl = row.node as usize;
            let Some(block) = f
                .tree
                .children(decl)
                .find(|&c| f.tree.kinds[c] == NodeKind::Block)
            else {
                continue;
            };
            self.sink.open();
            self.bodies_checked += 1;
            let mut lcx = lower::Cx::new(f, def);
            lcx.home = def;
            self.build_body_scope(&mut lcx, def, low);
            let mut cx = BodyCx::new(f, def, row.file, row.node, lcx);
            self.prepare_signature(&mut cx, decl);
            let want = cx.result;
            self.dep(def);
            self.check_block(&mut cx, block, want);
            let set = self.cur_deps.take();
            self.deps.push((def, set));
            self.body_nodes += cx.nodes;
            self.tape_events += cx.tape.len() as u64;
            for s in &cx.sites {
                if !self
                    .check_sites
                    .iter()
                    .any(|x| x.parent == s.parent && x.slot == s.slot)
                {
                    self.check_sites.push(*s);
                }
            }
        }
    }

    /// Whether this declaration (or its `impl`/`trait`) already produced a
    /// diagnostic, in which case its body is not typed: a signature that did
    /// not lower has no meaningful types to check a body against, and the
    /// corpus's "exactly one diagnostic per `check-error` test" is the same
    /// statement from the other side.
    fn already_spoke(&self, low: &Lowered, def: DefId, parent: DefId) -> bool {
        let p = |d: DefId| {
            d != fors_fir::NO_DEF
                && (low.poisoned.get(d.index()).copied().unwrap_or(false)
                    || self.spoke.get(d.index()).copied().unwrap_or(false))
        };
        p(def) || p(parent)
    }

    fn build_body_scope(&mut self, lcx: &mut lower::Cx, def: DefId, low: &Lowered) {
        let mut l = lower::Lowerer {
            sites: lower::Sites::default(),
            fir: self.fir,
            names: self.names,
            prelude: self.prelude,
            defs: self.defs,
            shapes: self.shapes,
            sink: self.sink,
        };
        l.build_scope(lcx, def, low);
    }

    /// Binds the receiver, the parameters and `Self`, and reads the result
    /// and `raises` types out of the signature this declaration already has.
    fn prepare_signature(&mut self, cx: &mut BodyCx, decl: usize) {
        let sig = self.fir.sigs.fn_sig(cx.owner);
        if sig != fors_fir::NO_FN_SIG {
            cx.result = self.fir.sigs.fn_sigs.result(sig);
            cx.raises = self.fir.sigs.fn_sigs.raises(sig);
        }
        let Some(fs) =
            cx.f.tree
                .children(decl)
                .find(|&c| cx.f.tree.kinds[c] == NodeKind::FnSig)
        else {
            return;
        };
        let Some(ps) =
            cx.f.tree
                .children(fs)
                .find(|&c| cx.f.tree.kinds[c] == NodeKind::Params)
        else {
            return;
        };
        let mut i = 0usize;
        for p in cx.f.tree.children(ps).collect::<Vec<_>>() {
            if cx.f.tree.kinds[p] != NodeKind::Param {
                continue;
            }
            let ty = if sig != fors_fir::NO_FN_SIG && i < self.fir.sigs.fn_sigs.count(sig) {
                self.fir.sigs.fn_sigs.param(sig, i).ty
            } else {
                TY_ERROR
            };
            cx.bind(p as u32, ty, LocalKind::Value);
            let place = cx.tape.intern(p as u32, &[]);
            cx.tape
                .push(p as u32, place, UseKind::Declare, Cause::Explicit(p as u32));
            i += 1;
        }
    }
}

// ----------------------------------------------------------- statements

impl Wf<'_> {
    /// A `Block` in CHECK mode (R31's last paragraph, R32's CHECK half).
    pub fn check_block(&mut self, cx: &mut BodyCx, node: usize, want: TyId) -> TyId {
        let kids = cx.kids(node);
        let (stmts, tail) = split_tail(cx, &kids);
        let mut never = false;
        for &s in stmts {
            if self.stmt(cx, s) == TY_NEVER {
                never = true;
            }
        }
        match tail {
            Some(e) => {
                cx.site(NodeKind::Block, Slot::Tail);
                self.check(cx, e, want)
            }
            None => {
                // A block whose last statement cannot fall through has type
                // `never` (R31's last sentence), whatever was expected: it
                // is R10(a) that makes the expectation hold, not the block.
                if never {
                    TY_NEVER
                } else if want == TY_UNIT || want == TY_ERROR || want == TY_NEVER {
                    want
                } else {
                    let s = self.show(TY_UNIT);
                    let w = self.show(want);
                    self.bemit(
                        cx,
                        node,
                        26,
                        31,
                        format!("expected `{w}`, found `{s}`: this block has no tail expression"),
                    );
                    TY_ERROR
                }
            }
        }
    }

    /// A `Block` in SYNTH mode.
    pub fn synth_block(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let (stmts, tail) = split_tail(cx, &kids);
        let mut never = false;
        for &s in stmts {
            if self.stmt(cx, s) == TY_NEVER {
                never = true;
            }
        }
        match tail {
            Some(e) => self.synth(cx, e),
            None if never => TY_NEVER,
            None => TY_UNIT,
        }
    }

    /// One statement. Returns [`TY_NEVER`] when control cannot continue past
    /// it (R31's "a block ends in `never`"), [`TY_UNIT`] otherwise.
    fn stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        cx.nodes += 1;
        match cx.kind(node) {
            NodeKind::LetStmt => self.let_stmt(cx, node),
            NodeKind::AssignStmt => self.assign_stmt(cx, node),
            NodeKind::ExprStmt => {
                let e = cx.kids(node);
                match e.first() {
                    // R31: an expression statement is SYNTHESISED and its
                    // value dropped.
                    Some(&x) => self.synth(cx, x),
                    None => TY_UNIT,
                }
            }
            NodeKind::ReturnStmt => self.return_stmt(cx, node),
            NodeKind::RaiseStmt => self.raise_stmt(cx, node),
            NodeKind::BreakStmt | NodeKind::ContinueStmt => {
                self.loop_exit(cx, node);
                TY_NEVER
            }
            NodeKind::ForStmt | NodeKind::ParallelForStmt | NodeKind::SimdForStmt => {
                self.for_stmt(cx, node)
            }
            NodeKind::WhileStmt => {
                let kids = cx.kids(node);
                if let Some(&c) = kids.first() {
                    cx.site(NodeKind::WhileStmt, Slot::Condition);
                    self.check_condition(cx, c, NodeKind::WhileStmt);
                }
                cx.loop_depth += 1;
                for &b in kids.iter().skip(1) {
                    cx.site(NodeKind::WhileStmt, Slot::UnitBody);
                    self.check(cx, b, TY_UNIT);
                }
                cx.loop_depth -= 1;
                TY_UNIT
            }
            NodeKind::DeferStmt | NodeKind::ErrdeferStmt => self.defer_stmt(cx, node),
            NodeKind::SpawnStmt => {
                // R37: `spawn e;` requires a call. The call itself is typed
                // as any other; the ch01 obligations are I8's.
                for c in cx.kids(node) {
                    let is_call = match cx.kind(c) {
                        NodeKind::CallExpr => true,
                        NodeKind::TryExpr => cx
                            .kids(c)
                            .first()
                            .is_some_and(|&k| cx.kind(k) == NodeKind::CallExpr),
                        _ => false,
                    };
                    if !is_call && cx.kind(c) != NodeKind::Error {
                        self.bemit(cx, c, 37, 37, "`spawn` takes a call".to_string());
                    }
                    self.synth(cx, c);
                }
                TY_UNIT
            }
            NodeKind::ConsumeStmt | NodeKind::DiscardStmt => {
                for c in cx.kids(node) {
                    let ty = self.synth(cx, c);
                    let _ = ty;
                    if let Some(p) = self.place_of(cx, c) {
                        cx.tape
                            .push(c as u32, p, UseKind::Move, Cause::Explicit(node as u32));
                    }
                }
                TY_UNIT
            }
            NodeKind::WithStmt => self.with_stmt(cx, node),
            NodeKind::ParallelStmt | NodeKind::AttrBlockStmt => {
                for c in cx.kids(node) {
                    if cx.kind(c) == NodeKind::Block {
                        let pk = cx.kind(node);
                        cx.site(pk, Slot::UnitBody);
                        self.check(cx, c, TY_UNIT);
                    }
                }
                TY_UNIT
            }
            NodeKind::Error => TY_UNIT,
            // A statement-form `if`/`match`/`comptime`/block that is not the
            // block's tail is checked against `()` (R31).
            k if is_expr_kind(k) => {
                cx.site(NodeKind::Block, Slot::UnitBody);
                let got = self.check(cx, node, TY_UNIT);
                if got == TY_NEVER { TY_NEVER } else { TY_UNIT }
            }
            _ => TY_UNIT,
        }
    }

    fn let_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&binding) = kids.first() else {
            return TY_UNIT;
        };
        let annot = kids
            .iter()
            .skip(1)
            .find(|&&c| is_type_node(cx.kind(c)))
            .copied();
        let init = kids
            .iter()
            .skip(1)
            .find(|&&c| is_expr_kind(cx.kind(c)))
            .copied();
        let declared = annot.map(|a| self.lower_annotation(cx, a));
        let ty = match (declared, init) {
            (Some(d), Some(e)) => {
                cx.site(NodeKind::LetStmt, Slot::AnnotatedInit);
                self.check(cx, e, d);
                self.use_value(cx, e, d, Cause::Explicit(node as u32));
                d
            }
            (Some(d), None) => d,
            (None, Some(e)) => {
                let s = self.synth(cx, e);
                self.use_value(cx, e, s, Cause::Explicit(node as u32));
                if s == TY_NEVER {
                    // R33: a binding must not be given `never` by synthesis.
                    self.bemit(cx, e, 33, 33, "a binding must not be given the type `never` by synthesis; annotate it if you meant the coercion".to_string());
                    TY_ERROR
                } else {
                    s
                }
            }
            (None, None) => {
                // R1: `let x;` — the type could only come from a later use.
                self.bemit(cx, node, 1, 1, "`let` with neither a type annotation nor an initialiser: a binding's type is never inferred from a later use".to_string());
                TY_ERROR
            }
        };
        self.bind_binding(cx, binding, ty);
        TY_UNIT
    }

    /// Binds a `Binding`/`TupleBinding` to `ty` (R31's tuple clause).
    fn bind_binding(&mut self, cx: &mut BodyCx, node: usize, ty: TyId) {
        match cx.kind(node) {
            NodeKind::Binding => {
                cx.bind(node as u32, ty, LocalKind::Value);
                let p = cx.tape.intern(node as u32, &[]);
                cx.tape.push(
                    node as u32,
                    p,
                    UseKind::Declare,
                    Cause::Explicit(node as u32),
                );
            }
            NodeKind::TupleBinding => {
                let kids = cx.kids(node);
                let parts: Vec<TyId> = if self.fir.tys.tag(ty) == TyTag::Tuple {
                    self.fir.tys.args(ArgsId(self.fir.tys.b(ty))).to_vec()
                } else {
                    Vec::new()
                };
                if !parts.is_empty() && parts.len() != kids.len() && ty != TY_ERROR {
                    let w = self.show(ty);
                    self.bemit(
                        cx,
                        node,
                        31,
                        31,
                        format!(
                            "a tuple binding needs a tuple type of the same arity; found `{w}`"
                        ),
                    );
                } else if parts.is_empty()
                    && kids.len() != 1
                    && ty != TY_ERROR
                    && ty != NO_TY
                    && ty != TY_NEVER
                {
                    // R31: a tuple binding needs a TUPLE type. (`(a)` is `a`
                    // by R4, so a one-element binding faces any type.)
                    let w = self.show(ty);
                    self.bemit(
                        cx,
                        node,
                        31,
                        31,
                        format!("a tuple binding needs a tuple type; found `{w}`"),
                    );
                }
                for (i, &k) in kids.iter().enumerate() {
                    self.bind_binding(cx, k, parts.get(i).copied().unwrap_or(TY_ERROR));
                }
            }
            _ => {}
        }
    }

    fn assign_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&place) = kids.first() else {
            return TY_UNIT;
        };
        let lhs = self.synth(cx, place);
        // `a op= b` is R29's: the trait of `op` must hold for the place's
        // type and `b` is checked against it.
        let compound = compound_op(cx, place);
        if let Some(op) = compound {
            self.require_operator(cx, place, lhs, op, 29);
        }
        for &rhs in kids.iter().skip(1) {
            cx.site(
                NodeKind::AssignStmt,
                if compound.is_some() {
                    Slot::OperatorRhs
                } else {
                    Slot::AssignRhs
                },
            );
            self.check(cx, rhs, lhs);
            self.use_value(cx, rhs, lhs, Cause::Explicit(node as u32));
        }
        if let Some(p) = self.place_of(cx, place) {
            cx.tape.push(
                place as u32,
                p,
                UseKind::Assign,
                Cause::Explicit(node as u32),
            );
        }
        TY_UNIT
    }

    fn return_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        if self.in_defer(cx, node, "return") {
            return TY_NEVER;
        }
        if cx.closures > 0 && cx.in_synth_closure() {
            // R35: `return` inside a SYNTH-mode closure is rejected (its
            // type is not yet known). Inside a CHECK-mode closure `cx.result`
            // is the `fn` type's result and the ordinary path applies.
            self.bemit(cx, node, 35, 35, "`return` inside a closure in SYNTH mode: the closure's result type is not yet known; annotate the binding with a `fn` type".to_string());
            for c in cx.kids(node) {
                self.synth(cx, c);
            }
            return TY_NEVER;
        }
        let kids = cx.kids(node);
        match kids.first() {
            Some(&e) => {
                cx.site(NodeKind::ReturnStmt, Slot::ReturnValue);
                let want = cx.result;
                self.check(cx, e, want);
                self.use_value(cx, e, want, Cause::Explicit(node as u32));
            }
            None => {
                if cx.result != TY_UNIT && cx.result != TY_ERROR && cx.result != NO_TY {
                    let w = self.show(cx.result);
                    self.bemit(
                        cx,
                        node,
                        26,
                        31,
                        format!("expected `{w}`, found `()`: `return;` requires a `()` result"),
                    );
                }
            }
        }
        TY_NEVER
    }

    fn raise_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        if self.in_defer(cx, node, "raise") {
            return TY_NEVER;
        }
        let kids = cx.kids(node);
        let want = cx.raises;
        if want == NO_TY && cx.result != NO_TY {
            // R36/ch02 R1: `raise` is legal only in a `raises E` function
            // (or a closure checked against a raising `fn` type).
            if cx.closures > 0 && cx.in_synth_closure() {
                self.bemit(cx, node, 35, 35, "`raise` inside a closure in SYNTH mode: a closure raises only when checked against a `fn ... raises E` type".to_string());
            } else {
                self.bemit(
                    cx,
                    node,
                    36,
                    36,
                    "`raise` in a function that does not declare `raises`".to_string(),
                );
            }
        }
        for &e in &kids {
            if want == NO_TY {
                self.synth(cx, e);
            } else {
                cx.site(NodeKind::RaiseStmt, Slot::RaiseValue);
                self.check(cx, e, want);
            }
        }
        TY_NEVER
    }

    fn loop_exit(&mut self, cx: &mut BodyCx, node: usize) {
        let word = if cx.kind(node) == NodeKind::BreakStmt {
            "break"
        } else {
            "continue"
        };
        if let Some(fr) = cx.defers.last()
            && cx.loop_depth <= fr.loops_outside
        {
            let kw = if fr.errdefer { "errdefer" } else { "defer" };
            self.bemit(
                cx,
                node,
                33,
                33,
                format!("a `{word}` inside this `{kw}` body targets a loop outside it (ch01 R23c)"),
            );
            return;
        }
        if cx.loop_depth == 0 {
            self.bemit(cx, node, 33, 33, format!("`{word}` outside a loop"));
        }
    }

    /// R33's round-6 clause: `return`, `raise` and `?` inside a deferred
    /// body are rejected, and the diagnostic names the enclosing statement.
    fn in_defer(&mut self, cx: &mut BodyCx, node: usize, what: &str) -> bool {
        let Some(fr) = cx.defers.last() else {
            return false;
        };
        let kw = if fr.errdefer { "errdefer" } else { "defer" };
        let line = fr.node;
        let _ = line;
        self.bemit(cx, node, 33, 33, format!("no `{what}` inside a `{kw}` body (ch01 R23c): the deferred body runs on the way out"));
        true
    }

    fn defer_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        cx.defers.push(DeferFrame {
            node: node as u32,
            errdefer: cx.kind(node) == NodeKind::ErrdeferStmt,
            loops_outside: cx.loop_depth,
        });
        let pk = cx.kind(node);
        for &c in &kids {
            cx.site(pk, Slot::UnitBody);
            self.check(cx, c, TY_UNIT);
        }
        cx.defers.pop();
        TY_UNIT
    }

    fn with_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let mut region = TY_ERROR;
        for &c in &kids {
            if is_type_node(cx.kind(c)) {
                region = self.lower_annotation(cx, c);
            }
        }
        // The region identifier's introducing node is the `WithStmt` itself.
        cx.bind(node as u32, region, LocalKind::Value);
        for &c in &kids {
            if cx.kind(c) == NodeKind::Block {
                cx.site(NodeKind::WithStmt, Slot::UnitBody);
                self.check(cx, c, TY_UNIT);
            }
        }
        TY_UNIT
    }

    /// R31's `for`. The element type comes from a range, an array, a slice
    /// or `Iterator`, and from nothing else.
    fn for_stmt(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let kids = cx.kids(node);
        let Some(&binding) = kids.first() else {
            return TY_UNIT;
        };
        let iter = kids.get(1).copied();
        let mut elem = TY_ERROR;
        if let Some(e) = iter {
            let s = self.synth(cx, e);
            // A `never` iterable: the loop is unreachable; the binding is
            // silently `TY_ERROR` (R10(a) has nothing to coerce it to).
            elem = if s == TY_NEVER {
                TY_ERROR
            } else {
                self.element_of(cx, e, s)
            };
            if let Some(p) = self.place_of(cx, e) {
                let kind = if self.copyable(s) {
                    UseKind::Copy
                } else {
                    UseKind::Move
                };
                cx.tape
                    .push(e as u32, p, kind, Cause::Iterable(node as u32));
            }
        }
        self.bind_binding(cx, binding, elem);
        cx.loop_depth += 1;
        for &b in kids.iter().skip(2) {
            if cx.kind(b) == NodeKind::Block {
                let pk = cx.kind(node);
                cx.site(pk, Slot::UnitBody);
                self.check(cx, b, TY_UNIT);
            } else {
                // `parallel for ... grain e`: R30 checks it against `usize`.
                let u = self.fir.tys.prim(PrimKind::Usize);
                cx.site(NodeKind::ParallelForStmt, Slot::Condition);
                self.check(cx, b, u);
            }
        }
        cx.loop_depth -= 1;
        TY_UNIT
    }

    /// The element type of `for p in e` (R31), or `TY_ERROR` after T0031.
    fn element_of(&mut self, cx: &mut BodyCx, node: usize, s: TyId) -> TyId {
        if s == TY_ERROR || s == NO_TY {
            return TY_ERROR;
        }
        let bare = self.fir.tys.unqual(s);
        if self.fir.tys.tag(bare) == TyTag::Nominal {
            let def = DefId(self.fir.tys.a(bare));
            if let Some(g) = self.prelude.generic_index(def) {
                let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare))).to_vec();
                match g {
                    gty::RANGE | gty::RANGEINCL | gty::ARRAY | gty::SLICE | gty::VECTOR => {
                        return args.first().copied().unwrap_or(TY_ERROR);
                    }
                    _ => {}
                }
            }
        }
        // Otherwise the type must implement `Iterator`, and the element is
        // its `Item` (neutral when the subject is rigid).
        let item = self.prelude.item_name;
        let mut unknown = false;
        for it in self.iterator_traits() {
            let want = self.fir.tys.intern_trait_ref(it, fors_fir::ty::NO_ARGS);
            match self.holds(bare, want) {
                crate::wf::Holds::Yes => return self.assoc_item(bare, it, item),
                crate::wf::Holds::Unknown => unknown = true,
                crate::wf::Holds::No => {}
            }
        }
        if unknown {
            return TY_ERROR;
        }
        let w = self.show(s);
        self.bemit(cx, node, 31, 31, format!("`{w}` is not a range, an `Array`, a `Slice` or an `Iterator`, so it cannot be iterated"));
        TY_ERROR
    }
}

// ------------------------------------------------------------- helpers

/// Splits a block's children into statements and an optional tail value.
fn split_tail<'k>(cx: &BodyCx, kids: &'k [usize]) -> (&'k [usize], Option<usize>) {
    match kids.last() {
        Some(&last) if is_expr_kind(cx.kind(last)) => (&kids[..kids.len() - 1], Some(last)),
        _ => (kids, None),
    }
}

/// Whether a node kind can be an expression (so, at the end of a block, a
/// tail value). Statement-only kinds are excluded.
pub fn is_expr_kind(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::OrExpr
            | NodeKind::AndExpr
            | NodeKind::NotExpr
            | NodeKind::CmpExpr
            | NodeKind::BitExpr
            | NodeKind::RangeExpr
            | NodeKind::AddExpr
            | NodeKind::MulExpr
            | NodeKind::CastExpr
            | NodeKind::UnaryExpr
            | NodeKind::CallExpr
            | NodeKind::Bracket
            | NodeKind::FieldExpr
            | NodeKind::TryExpr
            | NodeKind::Literal
            | NodeKind::DotLit
            | NodeKind::NameExpr
            | NodeKind::StructLit
            | NodeKind::TupleOrParen
            | NodeKind::ArrayLit
            | NodeKind::AsmExpr
            | NodeKind::Closure
            | NodeKind::IfExpr
            | NodeKind::MatchExpr
            | NodeKind::ComptimeBlock
            | NodeKind::Block
    )
}

pub fn is_type_node(k: NodeKind) -> bool {
    matches!(
        k,
        NodeKind::QualType
            | NodeKind::ScopedType
            | NodeKind::TypeApp
            | NodeKind::TupleType
            | NodeKind::FnType
            | NodeKind::DynType
    )
}

/// The compound-assignment operator of an `AssignStmt`, if any.
fn compound_op(cx: &BodyCx, place: usize) -> Option<TokenKind> {
    let start = cx.f.tree.token_range(place).1 as usize;
    let n = cx.f.tokens.kinds.len();
    (start..n)
        .map(|i| cx.f.tokens.kinds[i])
        .find(|k| !k.is_trivia())
        .and_then(|k| {
            matches!(
                k,
                TokenKind::PlusEq
                    | TokenKind::MinusEq
                    | TokenKind::StarEq
                    | TokenKind::SlashEq
                    | TokenKind::PercentEq
                    | TokenKind::AmpEq
                    | TokenKind::PipeEq
                    | TokenKind::CaretEq
                    | TokenKind::ShlEq
                    | TokenKind::ShrEq
            )
            .then_some(k)
        })
}

/// The first significant token strictly between two sibling nodes.
pub fn op_between(cx: &BodyCx, a: usize, b: usize) -> Option<TokenKind> {
    let start = cx.f.tree.token_range(a).1 as usize;
    let end = (cx.f.tree.token_range(b).0 as usize).min(cx.f.tokens.kinds.len());
    (start..end)
        .map(|i| cx.f.tokens.kinds[i])
        .find(|k| !k.is_trivia())
}

/// The first significant token a node owns directly, before its children.
pub fn own_first(cx: &BodyCx, node: usize) -> Option<TokenKind> {
    let (a, b) = own_span(cx.f.tree, node);
    (a as usize..(b as usize).min(cx.f.tokens.kinds.len()))
        .map(|i| cx.f.tokens.kinds[i])
        .find(|k| !k.is_trivia())
}

impl Wf<'_> {
    /// A body diagnostic: at most one per node and one per declaration.
    /// Emits a body diagnostic, and reports whether it did: a caller that
    /// wants to attach a fix must know whether the quiet flag, the
    /// one-per-node mark or the per-declaration budget swallowed it.
    pub fn bemit(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        code: u16,
        site: u16,
        msg: String,
    ) -> bool {
        if cx.quiet > 0 {
            return false;
        }
        if cx.mark(node) {
            return false;
        }
        let range = cx.range(node);
        let file = cx.file;
        let emitted = self.sink.emit(file, range, t(code), site, msg);
        self.spoke_at(cx.home);
        emitted
    }

    /// Lowers a type written inside a body (a `let` annotation, a `with`
    /// region, a cast target). The same R11/R15/R61 rules apply as in a
    /// signature — including ch01 R22b's linear-element clause, whose
    /// offending type the I2 increment could only see in signatures.
    pub fn lower_annotation(&mut self, cx: &mut BodyCx, node: usize) -> TyId {
        let (ty, elements) = {
            let mut l = lower::Lowerer {
                sites: lower::Sites::default(),
                fir: self.fir,
                names: self.names,
                prelude: self.prelude,
                defs: self.defs,
                shapes: self.shapes,
                sink: self.sink,
            };
            let ty = l.ty(&mut cx.lcx, node, lower::Pos::Value);
            (ty, std::mem::take(&mut l.sites).elements)
        };
        for (_, file, range, elem, container) in elements {
            if matches!(
                self.fir.tys.tag(elem),
                TyTag::Param | TyTag::Proj | TyTag::Error
            ) {
                continue;
            }
            if self.is_linear(elem) {
                let en = self.show(elem);
                let cn = String::from_utf8_lossy(self.names.resolve(container)).into_owned();
                if !cx.mark(node) {
                    self.sink.emit(file, range, t(11), 11, format!("`{cn}` may not have the linear element type `{en}`: an element could never leave it"));
                    self.spoke_at(cx.home);
                }
            }
        }
        ty
    }

    /// `Copyable` (R23), for the tape's `Move`-vs-`Copy` decision. Never a
    /// diagnostic: an unknown answer is "not copyable", which the flow pass
    /// treats conservatively.
    pub fn copyable(&mut self, ty: TyId) -> bool {
        if ty == TY_ERROR || ty == NO_TY {
            return true;
        }
        let bare = self.fir.tys.unqual(ty);
        let want = self
            .fir
            .tys
            .intern_trait_ref(self.prelude.traits[tr::COPYABLE], fors_fir::ty::NO_ARGS);
        matches!(self.holds(bare, want), crate::wf::Holds::Yes)
    }

    /// The right-hand side of `impl Tr for S { type Name = ...; }`, or a
    /// neutral projection when `S` is rigid and the bound supplies the
    /// trait. The only normalisation I3 needs (R20 proper is I6's).
    pub fn assoc_item(&mut self, subject: TyId, trait_def: DefId, name: Symbol) -> TyId {
        if matches!(self.fir.tys.tag(subject), TyTag::Param | TyTag::Proj) {
            let tref = self
                .fir
                .tys
                .intern_trait_ref(trait_def, fors_fir::ty::NO_ARGS);
            let key = self.fir.tys.intern_proj_key(tref, name);
            return self.fir.tys.proj(subject, key);
        }
        self.impl_scans += 1;
        self.dep(trait_def);
        let rows = self.impls.exact(trait_def, subject);
        for i in rows {
            let r = self.impls.row(i);
            self.dep(r.def);
            let a = self.fir.sigs.assoc(r.def);
            let rhs = self.fir.sigs.assocs.rhs_of(a, name);
            if rhs != NO_TY && rhs != TY_ERROR {
                return rhs;
            }
        }
        TY_ERROR
    }

    /// The place a value-use event names, when the expression is one
    /// (ch07 `place`: a binding or a projection path).
    pub fn place_of(&mut self, cx: &mut BodyCx, node: usize) -> Option<crate::tape::PlaceId> {
        let mut path: Vec<Seg> = Vec::new();
        let mut n = node;
        loop {
            match cx.kind(n) {
                NodeKind::FieldExpr => {
                    let name = cx
                        .f
                        .tokens
                        .kinds
                        .iter()
                        .enumerate()
                        .skip(cx.f.tree.token_range(n).0 as usize)
                        .take((cx.f.tree.token_range(n).1 - cx.f.tree.token_range(n).0) as usize)
                        .rfind(|&(_, &k)| k == TokenKind::Ident)
                        .map(|(i, _)| self.names.intern(cx.f.tokens.text(i, cx.f.source)));
                    path.push(Seg::Field(name.unwrap_or(Symbol(0))));
                    n = cx.f.tree.children(n).next()?;
                }
                NodeKind::Bracket => {
                    path.push(Seg::Index);
                    n = cx.f.tree.children(n).next()?;
                }
                NodeKind::UnaryExpr if own_first(cx, n) == Some(TokenKind::KwMove) => {
                    n = cx.f.tree.children(n).next()?;
                }
                NodeKind::NameExpr => {
                    let target = cx.f.uses.target_of(n as u32)?;
                    let root = match target {
                        fors_resolve::target::ResolvedTarget::Local { node } => node,
                        _ => return None,
                    };
                    // ch07's greedy `path`: `x.a.b` is one node, so its own
                    // deferred segments are the innermost steps of the place.
                    let nsegs = crate::member::path_segments(cx, n);
                    let consumed = crate::member::path_consumed(cx, n).max(1) as usize;
                    let mut own: Vec<Seg> = Vec::new();
                    for k in consumed..nsegs {
                        {
                            let s = self.segment_name(cx, n, k)?;
                            own.push(Seg::Field(s))
                        }
                    }
                    path.reverse();
                    let mut full = own;
                    full.extend_from_slice(&path);
                    return Some(cx.tape.intern(root, &full));
                }
                _ => return None,
            }
        }
    }

    /// Records the value use of an expression that was consumed by a `let`,
    /// an assignment, a `return` or an argument (design §7.9).
    pub fn use_value(&mut self, cx: &mut BodyCx, node: usize, ty: TyId, cause: Cause) {
        let Some(p) = self.place_of(cx, node) else {
            return;
        };
        let kind = if self.copyable(ty) {
            UseKind::Copy
        } else {
            UseKind::Move
        };
        cx.tape.push(node as u32, p, kind, cause);
    }
}

/// R16's `SigKind` guard, used where a callee's row must be a function.
pub fn is_fn_sig(k: SigKind) -> bool {
    matches!(k, SigKind::Fn | SigKind::ExternFn)
}

/// The convention a parameter was declared with, for the tape.
pub fn conv_use(c: Conv) -> UseKind {
    match c {
        Conv::Let => UseKind::Read,
        Conv::Inout => UseKind::MutBorrow,
        Conv::Sink => UseKind::Move,
        Conv::Set => UseKind::OutBorrow,
    }
}
