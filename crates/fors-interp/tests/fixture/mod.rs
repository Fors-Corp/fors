//! Hand-written FMIR fixtures for F4 and F6.
//!
//! Design §4.2 is explicit that these two interpreter halves "have no checker
//! dependency and can be built and tested against F0 textual FMIR first" —
//! their LOWERING halves need checker increment I8b's `D7`/`D8`, which does
//! not exist ([HOLE-11]). This module is the "hand-written FMIR" that stands
//! in for lowering.
//!
//! [decision: the fixtures are built through `fors-fmir`'s POOL API rather
//! than through `parse.rs`'s textual form. `dump.rs`'s own documented scope
//! names that as the second, equally valid provenance ("A hand-built
//! `DeclFmir` ... still exists and is `verify()`-checkable — it is just built
//! with `crates/fors-fmir`'s own pool API"), and the textual form cannot
//! express what these fixtures need at all: it carries no constant pool
//! (every observable fixture here prints a `const_str`), no `ScopePool`
//! rows, no `DeferPool` and no exit edges. Extending the one-pass textual
//! parser to cover four more pools is a change to F0's deliverable, not to
//! F4's or F6's.]

#![allow(dead_code)]

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::FnSigId;
use fors_fir::ty::{PrimKind, TyId, TyStore};
use fors_fmir::alias::AliasSeed;
use fors_fmir::block::BlockRow;
use fors_fmir::decl::DeclFmir;
use fors_fmir::exit::{DischargeRow, ExitEdgeRow, ExitKind};
use fors_fmir::ids::{BlockId, BrandId, DeferId, PlaceId, RegionId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow};
use fors_fmir::op::{NO_OPERAND, Op};
use fors_fmir::region::{RegionKind, RegionRow};
use fors_fmir::scope::{DeferKind, DeferRow, ScopeRow};
use fors_fmir::site::SiteRow;
use fors_fmir::value::{ValDef, ValRow};
use fors_index::interner::Symbol;
use fors_interp::{Config, Outcome, ProgFn, Program, run};

pub const STDOUT_WRITE_LINE: &str = "stdout_write_line";
const WRITE_LINE_SYM: u32 = 1;

/// One staged block. Instructions are appended to one flat list in EMISSION
/// order (so a `ValDef::Inst` index stays correct however the blocks are
/// filled), and each block records its own `first_inst`/`inst_len` window —
/// which `BlockRow` carries explicitly, so the windows need not be in
/// `BlockId` order.
struct Staged {
    scope: ScopeId,
    first_inst: u32,
    inst_len: u32,
    term: InstRow,
}

/// A fixture builder over `fors-fmir`'s pools.
pub struct Fx {
    pub tys: TyStore,
    pub decl: DeclFmir,
    blocks: Vec<Option<Staged>>,
    open: Option<BlockId>,
    all_insts: Vec<InstRow>,
    block_start: u32,
    scope: ScopeId,
    strings: Vec<(u32, Vec<u8>)>,
    next_const: u32,
}

impl Fx {
    pub fn new() -> Fx {
        let mut decl = DeclFmir::empty(DeclKeyId(7), FnSigId(9));
        // `DeclFmir::empty` seeds one block and one scope; the fixture owns
        // its own blocks, so the seed block is dropped in `finish`.
        decl.blocks = fors_fmir::block::BlockPool::new();
        Fx {
            tys: TyStore::new(),
            decl,
            blocks: Vec::new(),
            open: None,
            all_insts: Vec::new(),
            block_start: 0,
            scope: ScopeId(0),
            strings: Vec::new(),
            next_const: 0,
        }
    }

    pub fn ty(&mut self, p: PrimKind) -> TyId {
        self.tys.prim(p)
    }

    pub fn site(&mut self, line: u32, col: u32) -> SiteId {
        self.decl.sites.push(SiteRow { line, col })
    }

    // -- scopes, defers, obligations --------------------------------------

    /// A scope with `defers` (pushed contiguously, as `ScopeRow.defers`
    /// requires) and `obligations`. Returns the scope and its `DeferId`s in
    /// the order given.
    pub fn scope(
        &mut self,
        parent: ScopeId,
        brand: BrandId,
        defers: &[(DeferKind, BlockId, u16)],
        obligations: &[PlaceId],
    ) -> (ScopeId, Vec<DeferId>) {
        let start = self.decl.defers.len() as u32;
        let mut ids = Vec::new();
        for (kind, body, stmt_order) in defers {
            ids.push(self.decl.defers.push(DeferRow {
                kind: *kind,
                body: *body,
                stmt_order: *stmt_order,
            }));
        }
        let end = self.decl.defers.len() as u32;
        let obligations = self.decl.obligations.push_list(obligations);
        let id = self.decl.scopes.push(ScopeRow {
            parent,
            brand,
            defers: start..end,
            obligations,
            region: RegionId::NONE,
        });
        (id, ids)
    }

    pub fn region(&mut self, kind: RegionKind) -> RegionId {
        self.decl.regions.push(RegionRow {
            kind,
            captures: 0..0,
            brand: BrandId::NONE,
        })
    }

    // -- exit edges --------------------------------------------------------

    /// An exit edge whose pending list is the one ch01 R23a/R23b REQUIRE
    /// (computed by `fors_fmir::exit::expected_pending`, the same function
    /// `verify()` asserts against) — i.e. what a correct `fors-lower` would
    /// emit from I8b's D7.
    pub fn exit(
        &mut self,
        from: BlockId,
        to: BlockId,
        kind: ExitKind,
        leaving: &[ScopeId],
    ) -> fors_fmir::ids::ExitEdgeId {
        let pending =
            fors_fmir::exit::expected_pending(&self.decl.scopes, &self.decl.defers, leaving, kind);
        self.exit_raw(from, to, kind, leaving, &pending, &[], &[])
    }

    /// An exit edge with every list given literally — the form a NEGATIVE
    /// fixture needs (a wrong multiset, a missing discharge).
    #[allow(clippy::too_many_arguments)]
    pub fn exit_raw(
        &mut self,
        from: BlockId,
        to: BlockId,
        kind: ExitKind,
        leaving: &[ScopeId],
        pending: &[DeferId],
        drops: &[PlaceId],
        discharges: &[DischargeRow],
    ) -> fors_fmir::ids::ExitEdgeId {
        let scopes = self.decl.exits.push_scopes(leaving);
        let pending = self.decl.exits.push_pending(pending);
        let drops = self.decl.exits.push_drops(drops);
        let discharges = self.decl.exits.push_discharges(discharges);
        let mut row = ExitEdgeRow::plain(from, to, kind);
        row.scopes = scopes;
        row.pending = pending;
        row.drops = drops;
        row.discharges = discharges;
        self.decl.exits.push(row)
    }

    // -- blocks ------------------------------------------------------------

    /// Reserves a `BlockId` so a forward branch can name it before it is
    /// filled.
    pub fn reserve(&mut self) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(None);
        id
    }

    /// Opens a reserved block for emission, in `scope`.
    pub fn begin(&mut self, b: BlockId, scope: ScopeId) {
        assert!(self.open.is_none(), "block {:?} is still open", self.open);
        self.open = Some(b);
        self.scope = scope;
        self.block_start = self.all_insts.len() as u32;
    }

    /// Closes the open block with `term`.
    pub fn end(&mut self, term: InstRow) {
        let b = self.open.take().expect("no open block");
        self.blocks[b.index()] = Some(Staged {
            scope: self.scope,
            first_inst: self.block_start,
            inst_len: self.all_insts.len() as u32 - self.block_start,
            term,
        });
    }

    /// Opens a block, emits nothing, and closes it with `br to`.
    pub fn block_br(&mut self, b: BlockId, scope: ScopeId, to: BlockId) {
        self.begin(b, scope);
        self.end(self.term(Op::Br, to.0, NO_OPERAND, NO_OPERAND));
    }

    pub fn term(&self, op: Op, a: u32, b: u32, c: u32) -> InstRow {
        InstRow {
            op,
            a,
            b,
            c,
            ty: fors_fir::ty::TY_UNIT,
            site: SiteId(0),
        }
    }

    pub fn term_at(&self, op: Op, a: u32, b: u32, c: u32, site: SiteId) -> InstRow {
        InstRow {
            op,
            a,
            b,
            c,
            ty: fors_fir::ty::TY_UNIT,
            site,
        }
    }

    // -- instructions ------------------------------------------------------

    /// Emits an instruction that DEFINES a value.
    pub fn emit(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> ValId {
        self.emit_at(op, a, b, c, ty, SiteId(0))
    }

    pub fn emit_at(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId, site: SiteId) -> ValId {
        // `ValDef::Inst` is positional, and `finish` pushes the staged rows
        // in block order, so the instruction index must be the total pushed
        // so far plus this block's own staged count.
        let inst = self.next_inst_index();
        let v = self.decl.push_val(ValRow::new(
            ty,
            false,
            0,
            ValDef::Inst(fors_fmir::ids::InstId(inst)),
        ));
        self.all_insts.push(InstRow {
            op,
            a,
            b,
            c,
            ty,
            site,
        });
        v
    }

    /// Emits an instruction that defines nothing (`do <inst>`).
    pub fn emit_void(&mut self, op: Op, a: u32, b: u32, c: u32, site: SiteId) {
        self.all_insts.push(InstRow {
            op,
            a,
            b,
            c,
            ty: fors_fir::ty::TY_UNIT,
            site,
        });
    }

    fn next_inst_index(&self) -> u32 {
        self.all_insts.len() as u32
    }

    pub fn const_int(&mut self, v: u64, ty: TyId) -> ValId {
        self.emit(Op::ConstInt, v as u32, (v >> 32) as u32, NO_OPERAND, ty)
    }

    pub fn const_unit(&mut self) -> ValId {
        self.emit(
            Op::ConstUnit,
            NO_OPERAND,
            NO_OPERAND,
            NO_OPERAND,
            fors_fir::ty::TY_UNIT,
        )
    }

    /// `Stdout.write_line(text)` through F1's one host intrinsic — the only
    /// observable effect these fixtures have, and what pins ORDER.
    pub fn print(&mut self, text: &str) {
        let str_ty = self.ty(PrimKind::Str);
        let cid = self.next_const;
        self.next_const += 1;
        self.strings.push((cid, text.as_bytes().to_vec()));
        let recv = self.const_unit();
        let s = self.emit(Op::ConstStr, cid, NO_OPERAND, NO_OPERAND, str_ty);
        let args = self.decl.insts.push_plain_operands(&[recv, s]);
        let call = self.decl.insts.push_call(CallRow {
            callee: Callee::Intrinsic(Symbol(WRITE_LINE_SYM)),
            args,
        });
        self.emit_void(Op::Intrinsic, call, NO_OPERAND, NO_OPERAND, SiteId(0));
    }

    // -- finishing ---------------------------------------------------------

    pub fn finish(mut self) -> (DeclFmir, TyStore, Vec<(u32, Vec<u8>)>) {
        assert!(self.open.is_none(), "a block was left open");
        let staged: Vec<Staged> = self
            .blocks
            .into_iter()
            .enumerate()
            .map(|(i, s)| s.unwrap_or_else(|| panic!("block {i} was reserved but never filled")))
            .collect();
        for row in std::mem::take(&mut self.all_insts) {
            // ch05 R5 / design §3.4a: every memory-producing instruction
            // carries a seed, and `verify()` rejects one that does not.
            // These fixtures are about §5.2's detections rather than about
            // alias classes, so each gets the seed its opcode's SOURCE is
            // (affine ownership for a heap/own root, the arena brand for
            // arena traffic, the parameter convention for a borrow).
            let seed = match row.op {
                Op::Alloc => AliasSeed::Own(PlaceId(0)),
                Op::ArenaAlloc | Op::ArenaDeref => AliasSeed::Arena(BrandId(0)),
                Op::Borrow => AliasSeed::Conv(fors_fir::sig::Conv::Let),
                Op::BorrowMut => AliasSeed::Conv(fors_fir::sig::Conv::Inout),
                Op::BorrowOut => AliasSeed::Conv(fors_fir::sig::Conv::Set),
                Op::Index | Op::SliceRange => AliasSeed::Split {
                    parent: PlaceId(0),
                    side: 0,
                },
                _ => AliasSeed::None,
            };
            self.decl.push_inst(row, seed);
        }
        let mut pool = fors_fmir::block::BlockPool::new();
        for s in staged {
            pool.push(BlockRow {
                first_inst: s.first_inst,
                inst_len: s.inst_len,
                term: s.term,
                scope: s.scope,
            });
        }
        self.decl.blocks = pool;
        self.decl.entry = BlockId(0);
        (self.decl, self.tys, self.strings)
    }
}

/// Wraps one declaration as a runnable program whose entry is `main`.
pub fn program(decl: DeclFmir, strings: Vec<(u32, Vec<u8>)>) -> Program {
    Program {
        fns: vec![ProgFn {
            name: "main".into(),
            decl,
            strings,
            intrinsics: vec![(WRITE_LINE_SYM, STDOUT_WRITE_LINE.into())],
        }],
        entry: 0,
        config: Config::v0_1(),
        names: Default::default(),
    }
}

/// The declaration key [`call_callee`] names: the second function of a
/// [`program2`] program.
pub const CALLEE_KEY: DeclKeyId = DeclKeyId(8);

/// A two-function program: `main` (the entry) and `callee`, which `main`
/// reaches through [`call_callee`]. Both must verify. The two fixtures
/// must intern their primitive types in the same order, since one
/// `TyStore` serves the run.
pub fn program2(main: Fx, callee: Fx) -> (Program, TyStore) {
    let (mdecl, tys, mstrings) = main.finish();
    let (mut cdecl, _, cstrings) = callee.finish();
    cdecl.decl = CALLEE_KEY;
    for d in [&mdecl, &cdecl] {
        let diags = fors_fmir::verify::verify(d);
        assert!(
            diags.is_empty(),
            "fixture does not verify: {:?}",
            diags
                .iter()
                .map(|d| (d.code, &d.message))
                .collect::<Vec<_>>()
        );
    }
    let mut prog = program(mdecl, mstrings);
    prog.fns.push(ProgFn {
        name: "callee".into(),
        decl: cdecl,
        strings: cstrings,
        intrinsics: vec![(WRITE_LINE_SYM, STDOUT_WRITE_LINE.into())],
    });
    (prog, tys)
}

/// `call_direct` of [`program2`]'s callee with no arguments, defining a
/// value of `ty`.
pub fn call_callee(fx: &mut Fx, ty: TyId) -> ValId {
    let args = fx.decl.insts.push_plain_operands(&[]);
    let call = fx.decl.insts.push_call(CallRow {
        callee: Callee::Direct(CALLEE_KEY),
        args,
    });
    fx.emit(Op::CallDirect, call, NO_OPERAND, NO_OPERAND, ty)
}

/// The captured `Stdout` of an outcome, as lines.
pub fn lines_of(out: &Outcome) -> Vec<String> {
    String::from_utf8(out.stdout.clone())
        .expect("utf-8")
        .lines()
        .map(|s| s.to_string())
        .collect()
}

/// Builds, runs, and returns the outcome plus the captured `Stdout` lines.
pub fn run_fx(fx: Fx) -> (Outcome, Vec<String>) {
    let (decl, tys, strings) = fx.finish();
    let diags = fors_fmir::verify::verify(&decl);
    assert!(
        diags.is_empty(),
        "fixture does not verify: {:?}",
        diags
            .iter()
            .map(|d| (d.code, &d.message))
            .collect::<Vec<_>>()
    );
    let out = run(&program(decl, strings), &tys).expect("the fixture runs");
    let lines = String::from_utf8(out.stdout.clone())
        .expect("utf-8")
        .lines()
        .map(|s| s.to_string())
        .collect();
    (out, lines)
}

/// As [`run_fx`] but without the `verify()` precondition — for fixtures that
/// are deliberately malformed so the INTERPRETER's own assertion can be
/// observed.
pub fn run_fx_unverified(fx: Fx) -> Result<Outcome, fors_interp::InterpError> {
    let (decl, tys, strings) = fx.finish();
    run(&program(decl, strings), &tys)
}
