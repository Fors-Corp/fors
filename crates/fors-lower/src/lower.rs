//! The `BodyFacts`-driven lowering walk: CST + facts → FMIR.
//!
//! Every decision the checker made is READ, never remade: expression types
//! come from [`BodyFacts::ty_of`](fors_check::facts::BodyFacts::ty_of)
//! (D1), callees from `callee_of` (D2), receiver conventions from
//! `recv_conv_of` plus `arg_convs` (D3), field indices from `member_of`
//! (D4). Parameter types come from the FIR signature (lowering needs the
//! signature for every call target anyway; design §10.2 lists it as an
//! `fmir_of` input).
//!
//! FMIR conventions established here (all read back by `fors-interp`):
//! - `const_int`/`const_float` carry the 64-bit bit pattern split across
//!   `a` (low 32) and `b` (high 32). `const_bool` carries 0/1 in `a`.
//!   `const_str` carries the `FmirConstId` in `a`; the bytes live in
//!   [`LoweredFn::strings`].
//! - `agg_new` carries `a` = start, `b` = end into the spilled operands
//!   (the range reading `verify.rs` itself uses).
//! - Places (`copy_from`/`init`) use per-function local slots: parameters
//!   in signature order, then `let` bindings in encounter order.
//! - A method named `write_line` lowers to the `stdout_write_line`
//!   intrinsic (design §5.8, mechanism 2): until std exists with
//!   Fors-written `write_*` bodies over `@fd_write`, this is the one host
//!   door F1 programs can observe. Any other method lowers to
//!   `call_direct` on its `DeclKeyId`.
//!
//! Aggregates are reference-shared in F1: reading a struct-typed local
//! copies its cell handle, so an `inout` method mutating `self` is visible
//! to the caller. The copy/move distinction needs I8's flow data (D6) and
//! arrives with it; F1 documents the sharing rather than guessing moves.

use std::collections::{HashMap, HashSet};

use fors_check::CheckOutput;
use fors_check::defs::DefTable;
use fors_check::facts::{BodyFacts, FactCallee, MemberTarget};
use fors_fir::Fir;
use fors_fir::sig::Conv;
use fors_fir::ty::{ArgsId, ConstId, NO_TY, PrimKind, TY_ERROR, TY_UNIT, TyId, TyTag};
use fors_index::decl::DeclKind;
use fors_index::ids::DefId;
use fors_index::{Interner, Symbol};
use fors_lex::{TokenKind, Tokens};
use fors_resolve::FileInput;
use fors_syntax::{NodeKind, Tree};

use fors_fmir::alias::AliasSeed;
use fors_fmir::block::BlockRow;
use fors_fmir::decl::DeclFmir;
use fors_fmir::ids::{ABSENT, BlockId, PlaceId, ScopeId, SiteId, ValId};
use fors_fmir::inst::{CallRow, Callee, InstRow, ReduceRow};
use fors_fmir::op::{ArithMode, CmpPred, NO_OPERAND, Op, Policy};
use fors_fmir::place::Seg;
use fors_fmir::value::{ValDef, ValRow};

use crate::diag::{LowerDiag, LowerError};

/// One lowered function: FMIR plus the side tables the interpreter needs
/// alongside it (string bytes, intrinsic names). The caller assembles these
/// rows into a runnable program.
#[derive(Debug)]
pub struct LoweredFn {
    pub def: DefId,
    pub name: String,
    pub decl: DeclFmir,
    /// `(FmirConstId.0, bytes)` for every `const_str` in `decl`.
    pub strings: Vec<(u32, Vec<u8>)>,
    /// `(Symbol.0, name)` for every intrinsic `decl` names.
    pub intrinsics: Vec<(u32, String)>,
}

/// The whole build: lowered functions plus one diagnostic per skipped body.
#[derive(Debug, Default)]
pub struct LoweredBuild {
    pub fns: Vec<LoweredFn>,
    pub diags: Vec<LowerDiag>,
}

/// Lowers every checked body in `out.facts`. Total: bodies outside the F1
/// subset become [`LowerDiag`] rows, never panics.
pub fn lower_build(
    inputs: &[FileInput<'_>],
    out: &CheckOutput,
    interner: &mut Interner,
) -> LoweredBuild {
    let mut build = LoweredBuild::default();
    let Some(defs) = out.defs.as_ref() else {
        return build;
    };
    for (def, facts) in &out.facts {
        let row = defs.get(*def);
        let name = row
            .and_then(|r| r.name)
            .map(|s| String::from_utf8_lossy(interner.resolve(s)).into_owned())
            .unwrap_or_else(|| format!("def{}", def.0));
        match lower_one(inputs, &out.fir, defs, *def, &name, facts, interner) {
            Ok(f) => build.fns.push(f),
            Err(error) => build.diags.push(LowerDiag {
                def: *def,
                name,
                error,
            }),
        }
    }
    build
}

fn lower_one(
    inputs: &[FileInput<'_>],
    fir: &Fir,
    defs: &DefTable,
    def: DefId,
    name: &str,
    facts: &BodyFacts,
    interner: &mut Interner,
) -> Result<LoweredFn, LowerError> {
    let row = defs
        .get(def)
        .ok_or_else(|| LowerError::Unresolved(format!("def{}", def.0)))?;
    // Only `fn` bodies lower in F1. `const` bodies are comptime (F9);
    // anything else with facts is still diagnosed, never panicked on.
    match row.kind {
        DeclKind::Fn => {}
        DeclKind::Const => {
            return Err(LowerError::Comptime(
                "const bodies evaluate at comptime".into(),
            ));
        }
        _ => return Err(LowerError::Unsupported("non-function body".into())),
    }
    let file = inputs
        .get(row.file.0 as usize)
        .ok_or_else(|| LowerError::Unresolved(format!("file{}", row.file.0)))?;
    let decl_node = row.node as usize;
    prescan(file, decl_node, facts, fir)?;
    let mut fx = FnLower::new(fir, defs, facts, file, row.file.0, def, interner)?;
    fx.lower_fn(decl_node)?;
    Ok(fx.finish(def, name))
}

/// E11 (design §4.2, §11.2): until checker increment I10 lands D10
/// (`ContractPolicy` per declaration), `fors-lower` reads the module
/// header's `contracts:` clause itself. The corpus spells the value with a
/// leading dot (`contracts: .runtime;` / `.off;` — see
/// `02-failure/contract-off-no-check-run-ok.fors`), parsed by
/// `fors-syntax` into one `ContractsClause` child of the file root holding
/// a `DotLit`. Absent, or any spelling other than `.off`, defaults to
/// `Runtime` (ch02 R9's default; also the lenient stand-in for a value I10
/// will reject outright).
fn module_contract_policy(file: &FileInput<'_>) -> Policy {
    if file.tree.is_empty() {
        return Policy::Runtime;
    }
    for child in file.tree.children(0) {
        if file.tree.kinds[child] != NodeKind::ContractsClause {
            continue;
        }
        for c2 in file.tree.children(child) {
            if file.tree.kinds[c2] != NodeKind::DotLit {
                continue;
            }
            let (a, b) = file.tree.token_range(c2);
            for t in a..b {
                if file.tokens.kinds[t as usize] == TokenKind::Ident {
                    return match file.tokens.text(t as usize, file.source) {
                        b"off" => Policy::Off,
                        _ => Policy::Runtime,
                    };
                }
            }
        }
    }
    Policy::Runtime
}

/// The pre-walk rejections: type errors first (the checker speaks first),
/// then the increments F1 waits on, then the open-type scan over the facts.
fn prescan(
    file: &FileInput<'_>,
    decl_node: usize,
    facts: &BodyFacts,
    fir: &Fir,
) -> Result<(), LowerError> {
    let (start, end) = facts.range();
    // A poisoned body never lowers: every later read would be garbage —
    // EXCEPT the statement shapes `lower_let`/`lower_assign` special-case
    // as the F2 "minimal intrinsic-backed stub" (§5.8) for `trap-bounds`:
    // `Buffer`/`.slice` are ch10 R2 prelude-opaque without real `std`
    // sources in the build, which poisons every node of those two
    // statements with `TY_ERROR` even though nothing is actually wrong.
    // Real `Buffer`/`Slice` bodies are F7's; this bypasses `facts`
    // entirely for exactly those statements (see `buffer_stub_ranges`),
    // never for anything else.
    let mut stub_ranges = buffer_stub_ranges(file, decl_node);
    stub_ranges.extend(reduce_stub_ranges(file, decl_node));
    'scan: for n in start..end {
        for &(s, e) in &stub_ranges {
            if n >= s && n < e {
                continue 'scan;
            }
        }
        if facts.ty_of(n) == TY_ERROR {
            return Err(LowerError::CheckErrors);
        }
    }
    // I5/I6/I7/I8b/I10-owned forms, by CST kind over the declaration.
    if decl_node < file.tree.len() {
        let end_sub = file.tree.subtree_end(decl_node).min(file.tree.len());
        for n in decl_node..end_sub {
            match file.tree.kinds[n] {
                NodeKind::DeferStmt | NodeKind::ErrdeferStmt => return Err(LowerError::Defer),
                NodeKind::MatchExpr => return Err(LowerError::Match),
                NodeKind::TryExpr | NodeKind::Handler | NodeKind::RaiseStmt => {
                    return Err(LowerError::Failure);
                }
                NodeKind::Closure => return Err(LowerError::Closure),
                NodeKind::ForStmt
                | NodeKind::WhileStmt
                | NodeKind::ParallelForStmt
                | NodeKind::ParallelStmt
                | NodeKind::SimdForStmt
                | NodeKind::SpawnStmt
                | NodeKind::BreakStmt
                | NodeKind::ContinueStmt => return Err(LowerError::Loop),
                NodeKind::ComptimeBlock => {
                    return Err(LowerError::Comptime("comptime block".into()));
                }
                _ => {}
            }
        }
    }
    // A generic declaration is I5's, however it is used.
    if has_generic_params(file, decl_node) {
        return Err(LowerError::Generic("generic function".into()));
    }
    // Open types in the facts: rigid/projection/brand/dyn/fn/const.
    for n in start..end {
        let t = facts.ty_of(n);
        if t == NO_TY || t == TY_ERROR {
            continue;
        }
        match fir.tys.tag(fir.tys.unqual(t)) {
            TyTag::Param => return Err(LowerError::Generic("rigid parameter type".into())),
            TyTag::Proj => return Err(LowerError::Projection),
            TyTag::Dyn => return Err(LowerError::Unsupported("dyn type".into())),
            TyTag::Fn => return Err(LowerError::Closure),
            TyTag::Brand => return Err(LowerError::Generic("brand parameter".into())),
            TyTag::ConstVal => {
                return Err(LowerError::Comptime("comptime_int value".into()));
            }
            _ => {}
        }
    }
    Ok(())
}

/// The node ranges of statements `prescan` must NOT reject for `TY_ERROR`:
/// the two shapes `lower_let`/`lower_assign` lower as the `trap-bounds`
/// stand-in (see the comment on the call site). Detected structurally,
/// straight off the CST — the same two shapes those functions match —
/// never by reading `facts` (which is exactly what is unreliable here).
fn buffer_stub_ranges(file: &FileInput<'_>, decl_node: usize) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    if decl_node >= file.tree.len() {
        return out;
    }
    let Some(block) = file
        .tree
        .children(decl_node)
        .find(|&c| file.tree.kinds[c] == NodeKind::Block)
    else {
        return out;
    };
    for stmt in file.tree.children(block) {
        if is_buffer_fixed_let(file, stmt) || is_buffer_slice_assign(file, stmt) {
            out.push((stmt as u32, file.tree.subtree_end(stmt) as u32));
        }
    }
    out
}

/// Every `reduce(...)` call in the declaration, as `(start, end)` node
/// ranges `prescan` holds out of its `TY_ERROR` scan.
///
/// **[HOLE-7]** (design §11.3): *no checker increment types ch03 R11's
/// `reduce`* — it is a language primitive, not a function, and neither I3's
/// gate list nor I10's rule list claims it. So the checker leaves the call
/// poisoned and F5 hard-codes the typing in lowering, exactly as F2 did for
/// `Buffer.fixed` (design §5.8's "minimal intrinsic-backed stub"). The
/// hard-coding is deliberately confined to three places, all named here so
/// the adopting increment can find them in one grep for `HOLE-7`:
///   1. this hold-out (so `prescan` does not reject the body),
///   2. [`FnLower::lower_reduce`] (the element type comes from the operand,
///      the `op` from the declared binary operator, the optional identity
///      from the `identity:` argument), and
///   3. `fors-interp::reduce`'s `ReduceOp::resolve` (the executor end of
///      the opcode-name convention `reduce_op_name` writes).
///
/// The cheapest fix design §11.3 names is one line in I10's rule list: add
/// ch03 R11. When that lands, (1) and (2) delete and (3) stays.
fn reduce_stub_ranges(file: &FileInput<'_>, decl_node: usize) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    if decl_node >= file.tree.len() {
        return out;
    }
    let end = file.tree.subtree_end(decl_node).min(file.tree.len());
    for n in decl_node..end {
        if call_names_reduce(file.tree, file.tokens, file.source, n) {
            out.push((n as u32, file.tree.subtree_end(n) as u32));
        }
    }
    out
}

/// Is `call` a `CallExpr` whose callee is the bare prelude value `reduce`
/// (ch08 R17's `PRELUDE_VALUES`)? Matched by shape and spelling, like the
/// F2 `Buffer` stand-in, because there is no checker fact to read.
fn call_names_reduce(tree: &Tree, tokens: &Tokens, source: &[u8], call: usize) -> bool {
    if call >= tree.len() || tree.kinds[call] != NodeKind::CallExpr {
        return false;
    }
    let Some(callee) = tree.children(call).next() else {
        return false;
    };
    if tree.kinds[callee] != NodeKind::NameExpr {
        return false;
    }
    let (a, b) = tree.token_range(callee);
    let idents: Vec<&[u8]> = (a..b)
        .filter(|&t| tokens.kinds[t as usize] == TokenKind::Ident)
        .map(|t| tokens.text(t as usize, source))
        .collect();
    idents == [b"reduce".as_slice()]
}

/// The FMIR opcode spelling `fors-interp::reduce::ReduceOp::resolve` reads
/// back. The two ends of this convention are the whole of `reduce`'s
/// "which function does it apply" story in F5 ([HOLE-7]).
fn reduce_op_name(op: Op) -> Option<&'static str> {
    Some(match op {
        Op::Add(_) => "add",
        Op::Sub(_) => "sub",
        Op::Mul(_) => "mul",
        Op::Div(_) => "div",
        Op::Rem(_) => "rem",
        Op::Fadd(_) => "fadd",
        Op::Fsub(_) => "fsub",
        Op::Fmul(_) => "fmul",
        Op::Fdiv(_) => "fdiv",
        Op::Frem(_) => "frem",
        _ => return None,
    })
}

/// Significant `Ident` token texts `node` owns directly (not its
/// children's) — a free-function twin of `FnLower::own_tokens`/
/// `path_segments` for use where there is no `&mut Interner` (`prescan`
/// runs before a function's `FnLower` exists).
fn node_own_idents<'t>(file: &FileInput<'t>, node: usize) -> Vec<&'t [u8]> {
    let (a, b) = file.tree.token_range(node);
    let covered: Vec<(u32, u32)> = file
        .tree
        .children(node)
        .map(|c| file.tree.token_range(c))
        .collect();
    let mut out = Vec::new();
    for t in a..b {
        if covered.iter().any(|&(x, y)| t >= x && t < y) {
            continue;
        }
        if file.tokens.kinds[t as usize] == TokenKind::Ident {
            out.push(file.tokens.text(t as usize, file.source));
        }
    }
    out
}

/// `let <name>: Buffer[..] = Buffer.fixed(<n>);` — matched by shape, not by
/// type (see `buffer_stub_ranges`).
fn is_buffer_fixed_let(file: &FileInput<'_>, stmt: usize) -> bool {
    if file.tree.kinds[stmt] != NodeKind::LetStmt {
        return false;
    }
    for c in file.tree.children(stmt) {
        if file.tree.kinds[c] != NodeKind::CallExpr {
            continue;
        }
        if let Some(callee) = file.tree.children(c).next()
            && node_own_idents(file, callee) == [b"Buffer".as_slice(), b"fixed".as_slice()]
        {
            return true;
        }
    }
    false
}

/// `<name>.slice[<idx>] = <val>;` — matched by shape, not by type.
fn is_buffer_slice_assign(file: &FileInput<'_>, stmt: usize) -> bool {
    if file.tree.kinds[stmt] != NodeKind::AssignStmt {
        return false;
    }
    let Some(lhs) = file.tree.children(stmt).next() else {
        return false;
    };
    if file.tree.kinds[lhs] != NodeKind::Bracket {
        return false;
    }
    let Some(base) = file.tree.children(lhs).next() else {
        return false;
    };
    if file.tree.kinds[base] != NodeKind::NameExpr {
        return false;
    }
    let idents = node_own_idents(file, base);
    idents.len() == 2 && idents[1] == b"slice".as_slice()
}

/// Whether the `FnDecl` at `decl` declares generic parameters.
fn has_generic_params(file: &FileInput<'_>, decl: usize) -> bool {
    if file.tree.kinds.get(decl).copied() != Some(NodeKind::FnDecl) {
        return false;
    }
    for c in file.tree.children(decl) {
        if file.tree.kinds[c] == NodeKind::FnSig {
            for s in file.tree.children(c) {
                if file.tree.kinds[s] == NodeKind::Generics
                    && file.tree.children(s).next().is_some()
                {
                    return true;
                }
            }
        }
    }
    false
}

/// One block under construction: where its instructions start, its sealed
/// length and its terminator. `first` is recorded at `seal` time because
/// instructions are laid down in SEAL order, which is not block-id order
/// once control flow nests: an `if` inside a then-branch seals its own
/// three blocks before the enclosing else-block is even entered, so a
/// prefix sum over ids would hand the else-block the inner then-block's
/// instructions.
struct BlockDraft {
    first: usize,
    len: usize,
    term: Option<InstRow>,
}

const ROOT_SCOPE: ScopeId = ScopeId(0);
const SITE: SiteId = SiteId(0);

/// Per-function lowering state.
struct FnLower<'a> {
    fir: &'a Fir,
    defs: &'a DefTable,
    facts: &'a BodyFacts,
    tree: &'a Tree,
    tokens: &'a Tokens,
    source: &'a [u8],
    interner: &'a mut Interner,
    decl: DeclFmir,
    strings: Vec<(u32, Vec<u8>)>,
    intrinsics: Vec<(u32, String)>,
    /// Emitted instructions in final order (drafts index into this).
    insts: Vec<(InstRow, AliasSeed)>,
    blocks: Vec<BlockDraft>,
    cur: usize,
    /// Instructions already sealed into blocks. Emission is strictly
    /// sequential across blocks in creation order (lowering never emits
    /// into an older block after creating a newer one — `lower_if_stmt`
    /// only *seals* out of order), so at `seal` time every instruction
    /// since `emitted` belongs to the current block.
    emitted: usize,
    /// Symbol -> (local slot, type), innermost scope last.
    scopes: Vec<HashMap<Symbol, (u32, TyId)>>,
    next_root: u32,
    /// The file being lowered (for resolving struct heads).
    file_idx: u32,
    /// The module's contract-checking policy (E11, design §4.2): resolved
    /// once per file by `module_contract_policy`, carried unchanged
    /// through every function it lowers.
    policy: Policy,
    /// `post`/`invariant` clauses pending at every exit of the CURRENT
    /// function, in declaration order (`invariant` first, then `post`,
    /// mirroring entry's `pre`-then-`invariant` order). Emitted by
    /// `emit_exit_contracts` right before each `ret` this function builds.
    exit_contracts: Vec<(ContractKind, usize)>,
    /// Locals bound through the `Buffer.fixed(n)` stand-in (`lower_let`) —
    /// consulted only by `lower_assign`'s matching `.slice[i] = v` stand-in,
    /// so an unrelated `.slice[...]` on a real value still falls through to
    /// the ordinary (and ordinarily unsupported) assignment path.
    buffer_stub_locals: HashSet<Symbol>,
}

/// The three argument positions of a `reduce(...)` call, found by shape
/// (ch03 R11/R11a: a bare binary operator, the operand sequence, and the
/// optional `identity:`).
struct ReduceArgs {
    op_tok: Option<TokenKind>,
    xs: Option<usize>,
    identity: Option<usize>,
}

/// Which contract clause a `Contract` CST node spells — read off its own
/// leading keyword token, never inferred (design §3.6: `check_pre`/
/// `check_post`/`check_inv` are separate instructions).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ContractKind {
    Pre,
    Post,
    Inv,
}

impl<'a> FnLower<'a> {
    fn new(
        fir: &'a Fir,
        defs: &'a DefTable,
        facts: &'a BodyFacts,
        file: &FileInput<'a>,
        file_idx: u32,
        def: DefId,
        interner: &'a mut Interner,
    ) -> Result<FnLower<'a>, LowerError> {
        let decl_key = defs
            .get(def)
            .map(|r| r.key)
            .ok_or_else(|| LowerError::Unresolved(format!("def{}", def.0)))?;
        let sig = fir.sigs.fn_sig(def);
        if sig == fors_fir::NO_FN_SIG {
            return Err(LowerError::CheckErrors);
        }
        Ok(FnLower {
            fir,
            defs,
            facts,
            tree: file.tree,
            tokens: file.tokens,
            source: file.source,
            interner,
            decl: DeclFmir::empty(decl_key, sig),
            strings: Vec::new(),
            intrinsics: Vec::new(),
            insts: Vec::new(),
            blocks: vec![BlockDraft {
                first: 0,
                len: 0,
                term: None,
            }],
            cur: 0,
            emitted: 0,
            scopes: vec![HashMap::new()],
            next_root: 0,
            file_idx,
            // E11: the module's `contracts:` clause, read by `fors-lower`
            // itself (once per function, off the file root — cheap) until
            // I10's D10 supplies it per declaration.
            policy: module_contract_policy(file),
            exit_contracts: Vec::new(),
            buffer_stub_locals: HashSet::new(),
        })
    }

    fn finish(mut self, def: DefId, name: &str) -> LoweredFn {
        for (row, seed) in std::mem::take(&mut self.insts) {
            self.decl.push_inst(row, seed);
        }
        // Drop `DeclFmir::empty`'s sentinel block: drafts are the whole
        // CFG in creation order, so ids need no remap; each draft carries
        // its own `first` (recorded at `seal`), because emission order is
        // seal order, not id order (see `BlockDraft`).
        let mut blocks = fors_fmir::block::BlockPool::new();
        let mut covered = 0usize;
        for draft in std::mem::take(&mut self.blocks) {
            let term = draft.term.unwrap_or(InstRow {
                op: Op::Unreachable,
                a: NO_OPERAND,
                b: NO_OPERAND,
                c: NO_OPERAND,
                ty: TY_UNIT,
                site: SITE,
            });
            blocks.push(BlockRow {
                first_inst: draft.first as u32,
                inst_len: draft.len as u32,
                term,
                scope: ROOT_SCOPE,
            });
            covered += draft.len;
        }
        debug_assert_eq!(covered, self.decl.insts.len());
        self.decl.blocks = blocks;
        self.decl.entry = BlockId(0);
        LoweredFn {
            def,
            name: name.to_string(),
            decl: self.decl,
            strings: self.strings,
            intrinsics: self.intrinsics,
        }
    }

    // -- small helpers ----------------------------------------------------

    fn kids(&self, node: usize) -> Vec<usize> {
        self.tree.children(node).collect()
    }

    fn kind(&self, node: usize) -> NodeKind {
        self.tree.kinds[node]
    }

    fn ty_of(&self, node: usize) -> TyId {
        self.facts.ty_of(node as u32)
    }

    /// Significant tokens owned directly by `node` (its range minus its
    /// children's), in order: keywords, operators, delimiters.
    fn own_tokens(&self, node: usize) -> Vec<(usize, TokenKind)> {
        let (a, b) = self.tree.token_range(node);
        let mut covered: Vec<(u32, u32)> = Vec::new();
        for c in self.tree.children(node) {
            covered.push(self.tree.token_range(c));
        }
        let mut out = Vec::new();
        for t in a..b {
            if covered.iter().any(|&(x, y)| t >= x && t < y) {
                continue;
            }
            let k = self.tokens.kinds[t as usize];
            if k.is_trivia() {
                continue;
            }
            out.push((t as usize, k));
        }
        out
    }

    /// The operator tokens sitting between a flat n-ary node's children.
    fn gap_ops(&self, kids: &[usize]) -> Vec<TokenKind> {
        let mut ops = Vec::new();
        for pair in kids.windows(2) {
            let (_, lend) = self.tree.token_range(pair[0]);
            let (rstart, _) = self.tree.token_range(pair[1]);
            // token_range is (first, first+len): absolute end/start.
            for t in lend..rstart {
                let k = self.tokens.kinds[t as usize];
                if !k.is_trivia() {
                    ops.push(k);
                }
            }
        }
        ops
    }

    /// The single significant token of a leaf node.
    fn leaf_token(&self, node: usize) -> Option<(TokenKind, &[u8])> {
        let (a, b) = self.tree.token_range(node);
        for t in a..b {
            let k = self.tokens.kinds[t as usize];
            if !k.is_trivia() {
                return Some((k, self.tokens.text(t as usize, self.source)));
            }
        }
        None
    }

    /// The identifier segments a `NameExpr` owns (`p`, or `p, x`).
    fn path_segments(&mut self, node: usize) -> Vec<Symbol> {
        let (a, b) = self.tree.token_range(node);
        let mut covered: Vec<(u32, u32)> = Vec::new();
        for c in self.tree.children(node) {
            covered.push(self.tree.token_range(c));
        }
        let mut segs = Vec::new();
        for t in a..b {
            if covered.iter().any(|&(x, y)| t >= x && t < y) {
                continue;
            }
            if self.tokens.kinds[t as usize] == TokenKind::Ident {
                segs.push(
                    self.interner
                        .intern(self.tokens.text(t as usize, self.source)),
                );
            }
        }
        segs
    }

    fn prim_of(&self, ty: TyId) -> Option<PrimKind> {
        let bare = self.fir.tys.unqual(ty);
        if self.fir.tys.tag(bare) != TyTag::Prim {
            return None;
        }
        PrimKind::from_u8(self.fir.tys.a(bare) as u8)
    }

    fn is_float_ty(&self, ty: TyId) -> bool {
        self.prim_of(ty).is_some_and(|p| p.is_float())
    }

    fn is_int_ty(&self, ty: TyId) -> bool {
        self.prim_of(ty).is_some_and(|p| p.is_integer())
    }

    // -- FMIR emission -----------------------------------------------------

    fn emit(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId) -> u32 {
        let id = self.insts.len() as u32;
        self.insts.push((
            InstRow {
                op,
                a,
                b,
                c,
                ty,
                site: SITE,
            },
            AliasSeed::None,
        ));
        id
    }

    /// [`FnLower::emit`] for a memory-producing op, which `verify()`
    /// requires to carry an alias seed (design §3.4a).
    fn emit_seeded(&mut self, op: Op, a: u32, b: u32, c: u32, ty: TyId, seed: AliasSeed) -> u32 {
        let id = self.emit(op, a, b, c, ty);
        self.insts[id as usize].1 = seed;
        id
    }

    fn fresh(&mut self, ty: TyId, inst: u32) -> ValId {
        self.decl.push_val(ValRow::new(
            ty,
            false,
            0,
            ValDef::Inst(fors_fmir::ids::InstId(inst)),
        ))
    }

    fn fresh_param(&mut self, ty: TyId, ordinal: u16) -> ValId {
        self.decl
            .push_val(ValRow::new(ty, false, 0, ValDef::Param(ordinal)))
    }

    fn seal(&mut self, term: InstRow) {
        let cur = self.cur;
        let len = self.insts.len() - self.emitted;
        self.blocks[cur].first = self.emitted;
        self.blocks[cur].len = len;
        self.blocks[cur].term = Some(term);
        self.emitted += len;
    }

    fn is_open(&self) -> bool {
        self.blocks[self.cur].term.is_none()
    }

    /// Starts a fresh block and makes it current. The previous block must
    /// already be sealed. The start is fixed at `finish` time (prefix sums
    /// over sealed lengths); creation order is emission order.
    fn new_block(&mut self) -> BlockId {
        let id = self.blocks.len() as u32;
        self.blocks.push(BlockDraft {
            first: 0,
            len: 0,
            term: None,
        });
        self.cur = id as usize;
        BlockId(id)
    }

    /// Ensures the current block accepts instructions, opening a (dead)
    /// one after a terminator.
    fn ensure_open(&mut self) {
        if !self.is_open() {
            self.new_block();
        }
    }

    fn term(&self, op: Op, a: u32, b: u32, c: u32) -> InstRow {
        InstRow {
            op,
            a,
            b,
            c,
            ty: TY_UNIT,
            site: SITE,
        }
    }

    // -- places and locals ---------------------------------------------------

    fn lookup(&self, sym: Symbol) -> Option<(u32, TyId)> {
        self.scopes.iter().rev().find_map(|s| s.get(&sym).copied())
    }

    /// Resolves a value name: a bound local, or — failing that — a named
    /// `const` item, which is comptime (F9), not an unbound local. Anything
    /// else is still a diagnostic, never a panic.
    fn resolve_name(&self, sym: Symbol) -> Result<(u32, TyId), LowerError> {
        if let Some(found) = self.lookup(sym) {
            return Ok(found);
        }
        for (_, row) in self.defs.user_defs() {
            if row.kind == DeclKind::Const && row.name == Some(sym) {
                return Err(LowerError::Comptime(format!(
                    "const `{}`",
                    display_sym(&*self.interner, sym)
                )));
            }
        }
        Err(LowerError::Unresolved(display_sym(&*self.interner, sym)))
    }

    fn bind(&mut self, sym: Symbol, ty: TyId) -> u32 {
        let root = self.next_root;
        self.next_root += 1;
        self.scopes
            .last_mut()
            .expect("lowering always has a scope")
            .insert(sym, (root, ty));
        root
    }

    fn rebind(&mut self, sym: Symbol, ty: TyId) -> Option<u32> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(slot) = scope.get_mut(&sym) {
                slot.1 = ty;
                return Some(slot.0);
            }
        }
        None
    }

    fn intern_place(&mut self, root: u32, segs: &[Seg], ty: TyId) -> PlaceId {
        self.decl.places.intern(root, segs, ty)
    }

    /// `copy_from` a whole local slot.
    fn read_root(&mut self, root: u32, base_ty: TyId, result_ty: TyId) -> ValId {
        let pid = self.intern_place(root, &[], base_ty);
        let inst = self.emit(Op::CopyFrom, pid.0, NO_OPERAND, NO_OPERAND, result_ty);
        self.fresh(result_ty, inst)
    }

    /// `init` a whole local slot or one field of it.
    fn write_place(&mut self, root: u32, segs: &[Seg], place_ty: TyId, val: ValId) {
        let pid = self.intern_place(root, segs, place_ty);
        self.emit(Op::Init, pid.0, val.0, NO_OPERAND, TY_UNIT);
    }

    // -- function body -------------------------------------------------------

    fn lower_fn(&mut self, decl_node: usize) -> Result<(), LowerError> {
        // Params: names from the CST in order, types from the signature in
        // order. A mismatch is a diagnostic, never an index panic. Contract
        // clauses (`pre`/`post`/`invariant`) live on the same `FnSig`.
        let sig = self.fir.sigs.fn_sig(self.facts.owner);
        let nsig = self.fir.sigs.fn_sigs.count(sig);
        let mut params: Vec<(Symbol, usize)> = Vec::new();
        let mut contracts: Vec<(ContractKind, usize)> = Vec::new();
        for c in self.kids(decl_node) {
            if self.kind(c) != NodeKind::FnSig {
                continue;
            }
            for s in self.kids(c) {
                match self.kind(s) {
                    NodeKind::Params => {
                        for p in self.kids(s) {
                            let name = self
                                .own_tokens(p)
                                .into_iter()
                                .find(|&(_, k)| k == TokenKind::Ident)
                                .map(|(t, _)| {
                                    self.interner.intern(self.tokens.text(t, self.source))
                                });
                            params.push((name.unwrap_or(Symbol(0)), p));
                        }
                    }
                    NodeKind::Contract => {
                        if let Some(expr) = self.kids(s).into_iter().next() {
                            contracts.push((self.contract_kind(s), expr));
                        }
                    }
                    _ => {}
                }
            }
        }
        if params.len() != nsig {
            return Err(LowerError::Unresolved(format!(
                "signature has {nsig} params, body declares {}",
                params.len()
            )));
        }
        for (i, (sym, _)) in params.iter().enumerate() {
            let ty = self.fir.sigs.fn_sigs.param(sig, i).ty;
            self.fresh_param(ty, i as u16);
            self.bind(*sym, ty);
        }
        // Entry contracts (§3.6, §5.3): `pre` then an entry-time
        // `invariant`, policy `Runtime` only — `Off` emits nothing at all
        // (not even the condition), matching `contract-off-no-check-run-ok`
        // and E8's closed-table spirit: a disabled check has zero cost and
        // zero chance of a side effect of its own.
        if self.policy == Policy::Runtime {
            self.ensure_open();
            for &(kind, expr) in &contracts {
                if kind == ContractKind::Pre {
                    let cond = self.lower_expr(expr)?;
                    self.emit(
                        Op::CheckPre(Policy::Runtime),
                        cond.0,
                        NO_OPERAND,
                        NO_OPERAND,
                        TY_UNIT,
                    );
                }
            }
            for &(kind, expr) in &contracts {
                if kind == ContractKind::Inv {
                    let cond = self.lower_expr(expr)?;
                    self.emit(
                        Op::CheckInv(Policy::Runtime),
                        cond.0,
                        NO_OPERAND,
                        NO_OPERAND,
                        TY_UNIT,
                    );
                }
            }
        }
        self.exit_contracts = contracts
            .into_iter()
            .filter(|&(k, _)| k != ContractKind::Pre)
            .collect();
        // The body block: the `Block` child of the `FnDecl`.
        let mut body = None;
        for c in self.kids(decl_node) {
            if self.kind(c) == NodeKind::Block {
                body = Some(c);
            }
        }
        let Some(block) = body else {
            return Err(LowerError::Unsupported("bodiless function".into()));
        };
        self.lower_block_children(block)?;
        if self.is_open() {
            self.emit_exit_contracts()?;
            let ret = self.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND);
            self.seal(ret);
        }
        Ok(())
    }

    /// The keyword a `Contract` node's OWN first token spells (`contract()`
    /// in `fors-syntax` bumps it as the node's first token, before the
    /// condition expression child).
    fn contract_kind(&self, node: usize) -> ContractKind {
        let (a, _) = self.tree.token_range(node);
        match self.tokens.text(a as usize, self.source) {
            b"post" => ContractKind::Post,
            b"invariant" => ContractKind::Inv,
            _ => ContractKind::Pre,
        }
    }

    /// `invariant` then `post`, at every exit this function builds (an
    /// explicit `return` via `lower_return`, or the implicit fallthrough
    /// `ret` `lower_fn` adds). Policy `Off`: nothing, same as entry.
    fn emit_exit_contracts(&mut self) -> Result<(), LowerError> {
        if self.policy != Policy::Runtime {
            return Ok(());
        }
        self.ensure_open();
        for &(kind, expr) in &self.exit_contracts.clone() {
            if kind == ContractKind::Inv {
                let cond = self.lower_expr(expr)?;
                self.emit(
                    Op::CheckInv(Policy::Runtime),
                    cond.0,
                    NO_OPERAND,
                    NO_OPERAND,
                    TY_UNIT,
                );
            }
        }
        for &(kind, expr) in &self.exit_contracts.clone() {
            if kind == ContractKind::Post {
                let cond = self.lower_expr(expr)?;
                self.emit(
                    Op::CheckPost(Policy::Runtime),
                    cond.0,
                    NO_OPERAND,
                    NO_OPERAND,
                    TY_UNIT,
                );
            }
        }
        Ok(())
    }

    /// Lowers a `Block`'s children in statement position. Returns nothing;
    /// fall-through is read from `is_open`.
    fn lower_block_children(&mut self, block: usize) -> Result<(), LowerError> {
        for stmt in self.kids(block) {
            self.lower_child(stmt)?;
        }
        Ok(())
    }

    fn lower_child(&mut self, node: usize) -> Result<(), LowerError> {
        match self.kind(node) {
            NodeKind::LetStmt => self.lower_let(node),
            NodeKind::AssignStmt => self.lower_assign(node),
            NodeKind::ExprStmt => {
                let kids = self.kids(node);
                match kids.first() {
                    None => Ok(()),
                    Some(&e) if self.kind(e) == NodeKind::IfExpr => self.lower_if_stmt(e),
                    Some(&e) => {
                        self.ensure_open();
                        self.lower_expr(e).map(|_| ())
                    }
                }
            }
            NodeKind::ReturnStmt => self.lower_return(node),
            NodeKind::IfExpr => self.lower_if_stmt(node),
            NodeKind::Block => {
                self.scopes.push(HashMap::new());
                let r = self.lower_block_children(node);
                self.scopes.pop();
                r
            }
            _ => {
                // A tail expression in statement position: evaluate, drop.
                self.ensure_open();
                self.lower_expr(node).map(|_| ())
            }
        }
    }

    fn lower_let(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        let Some(&binding) = kids.first() else {
            return Ok(());
        };
        if self.kind(binding) != NodeKind::Binding {
            return Err(LowerError::Unsupported("tuple binding".into()));
        }
        let sym = self
            .leaf_token(binding)
            .filter(|(k, _)| *k == TokenKind::Ident)
            .map(|(_, t)| t.to_vec());
        let Some(bytes) = sym else {
            return Err(LowerError::Unresolved("let binding".into()));
        };
        let sym = self.interner.intern(&bytes);
        let init = kids
            .iter()
            .skip(1)
            .copied()
            .find(|&c| is_expr(self.kind(c)));
        // F2 "minimal intrinsic-backed stub" (design §5.8) for
        // `trap-bounds`, held out of real `Buffer`/`Slice` bodies (F7's):
        // `Buffer` is ch10 R2 prelude-opaque without real `std` sources in
        // the build, so `facts` is `TY_ERROR` throughout this statement
        // (see `buffer_stub_ranges`, which keeps `prescan` from rejecting
        // it first). Bypasses `facts`/`lower_expr` entirely: allocates an
        // N-cell aggregate of inert zero slots via the SAME `agg_new`
        // `fors-interp` already runs for a real struct literal.
        if let Some(e) = init
            && self.kind(e) == NodeKind::CallExpr
            && let Some(len) = self.buffer_fixed_len(e)
        {
            let mut vals = Vec::with_capacity(len as usize);
            for _ in 0..len {
                let inst = self.emit(Op::ConstInt, 0, 0, NO_OPERAND, TY_UNIT);
                vals.push(self.fresh(TY_UNIT, inst));
            }
            let range = self.decl.insts.push_plain_operands(&vals);
            let agg = self.emit(Op::AggNew, range.start, range.end, NO_OPERAND, TY_UNIT);
            let v = self.fresh(TY_UNIT, agg);
            let root = self.bind(sym, TY_UNIT);
            self.buffer_stub_locals.insert(sym);
            self.write_place(root, &[], TY_UNIT, v);
            return Ok(());
        }
        // The `LetStmt` node itself is not a `synth`/`check` return, so its
        // facts entry is `NO_TY`: the binding's type is the initialiser's
        // (or the annotation's, when there is no initialiser — either way a
        // placeholder is harmless, since the interpreter never reads a
        // place's declared type, only its current value).
        let bind_ty = match init {
            Some(e) => self.initialiser_ty(e),
            None => {
                let t = self.ty_of(node);
                if t == NO_TY { TY_UNIT } else { t }
            }
        };
        let root = self.bind(sym, bind_ty);
        if let Some(e) = init {
            let v = self.lower_expr(e)?;
            self.write_place(root, &[], bind_ty, v);
        }
        Ok(())
    }

    /// The type an initialiser produces. Normally the checker's answer; for
    /// a `reduce(...)` call the checker has none ([HOLE-7]), so the operand
    /// decides.
    fn initialiser_ty(&mut self, e: usize) -> TyId {
        if call_names_reduce(self.tree, self.tokens, self.source, e) {
            return self.reduce_elem_ty(e).unwrap_or(TY_UNIT);
        }
        let t = self.ty_of(e);
        if t == TY_ERROR || t == NO_TY {
            TY_UNIT
        } else {
            t
        }
    }

    fn lower_assign(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        if kids.len() != 2 {
            return Err(LowerError::Unsupported("assignment".into()));
        }
        let (lhs, rhs) = (kids[0], kids[1]);
        // F2 stand-in (§5.8), the write half of `lower_let`'s
        // `Buffer.fixed`: `<buf>.slice[<lit>] = <lit>;` against a local
        // THIS function bound through that stand-in (`buffer_stub_locals`
        // guards against hijacking an unrelated `.slice[...]`). Lowers
        // straight to a runtime-bounds-checked `Seg::Index` place write;
        // the trap itself is `fors-interp::exec`'s `write_place`, not
        // anything decided here.
        if self.kind(lhs) == NodeKind::Bracket
            && let Some((root, idx)) = self.buffer_slice_index(lhs)
            && let Some(val) = self.literal_int(rhs)
        {
            let idx_inst = self.emit(
                Op::ConstInt,
                idx as u32,
                (idx >> 32) as u32,
                NO_OPERAND,
                TY_UNIT,
            );
            let idx_v = self.fresh(TY_UNIT, idx_inst);
            let val_inst = self.emit(
                Op::ConstInt,
                val as u32,
                (val >> 32) as u32,
                NO_OPERAND,
                TY_UNIT,
            );
            let val_v = self.fresh(TY_UNIT, val_inst);
            self.write_place(root, &[Seg::Index(idx_v)], TY_UNIT, val_v);
            return Ok(());
        }
        let v = self.lower_expr(rhs)?;
        let rhs_ty = self.ty_of(rhs);
        // LHS places: a bare local, or one field of a local.
        if self.kind(lhs) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported("complex assignment target".into()));
        }
        let segs = self.path_segments(lhs);
        match segs.as_slice() {
            [base] => {
                let (root, _) = self.resolve_name(*base)?;
                self.rebind(*base, rhs_ty);
                self.write_place(root, &[], rhs_ty, v);
                Ok(())
            }
            [base, _field] => {
                let (root, _) = self.resolve_name(*base)?;
                let MemberTarget::Field { index, .. } = self.facts.member_of(lhs as u32) else {
                    return Err(LowerError::Unresolved("field assignment".into()));
                };
                let seg = Seg::Field(index as u16);
                self.write_place(root, &[seg], rhs_ty, v);
                Ok(())
            }
            _ => Err(LowerError::Unsupported("long projection".into())),
        }
    }

    fn lower_return(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        let value = match kids.first() {
            None => None,
            Some(&e) => Some(self.lower_expr(e)?),
        };
        self.emit_exit_contracts()?;
        let ret = match value {
            None => self.term(Op::Ret, NO_OPERAND, NO_OPERAND, NO_OPERAND),
            Some(v) => self.term(Op::Ret, v.0, NO_OPERAND, NO_OPERAND),
        };
        self.seal(ret);
        Ok(())
    }

    fn lower_if_stmt(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        if kids.len() < 2 || kids.len() > 3 {
            return Err(LowerError::Unsupported("if".into()));
        }
        let (cond, then_b) = (kids[0], kids[1]);
        let else_b = kids.get(2).copied();
        let c = self.lower_expr(cond)?;
        let src = self.cur;
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();
        // Seal the source block first (no instructions were emitted since
        // the condition, so its length is already exact).
        self.cur = src;
        self.seal(self.term(Op::CondBr, c.0, then_id.0, else_id.0));
        // Then branch, in its own scope.
        self.cur = then_id.0 as usize;
        self.scopes.push(HashMap::new());
        self.lower_block_children(then_b)?;
        self.scopes.pop();
        let falls_then = self.is_open();
        if falls_then {
            self.seal(self.term(Op::Br, join_id.0, NO_OPERAND, NO_OPERAND));
        }
        // Else branch (or straight to join).
        self.cur = else_id.0 as usize;
        let falls_else = match else_b {
            None => true,
            Some(e) => {
                self.scopes.push(HashMap::new());
                self.lower_block_children(e)?;
                self.scopes.pop();
                self.is_open()
            }
        };
        if falls_else {
            self.seal(self.term(Op::Br, join_id.0, NO_OPERAND, NO_OPERAND));
        }
        self.cur = join_id.0 as usize;
        Ok(())
    }

    // -- expressions ----------------------------------------------------------

    fn lower_expr(&mut self, node: usize) -> Result<ValId, LowerError> {
        // [HOLE-7]: a `reduce(...)` call is poisoned by the checker, so it
        // is intercepted before the `TY_ERROR` gate (see
        // `reduce_stub_ranges` for the whole hard-coding).
        if call_names_reduce(self.tree, self.tokens, self.source, node) {
            return self.lower_reduce(node);
        }
        let ty = self.ty_of(node);
        if ty == TY_ERROR {
            return Err(LowerError::CheckErrors);
        }
        if ty == NO_TY {
            return Err(LowerError::Unresolved(kind_name(self.kind(node)).into()));
        }
        match self.kind(node) {
            NodeKind::Literal => self.lower_literal(node, ty),
            NodeKind::NameExpr => self.lower_path(node, ty),
            NodeKind::AddExpr | NodeKind::MulExpr | NodeKind::BitExpr => {
                self.lower_binary(node, ty)
            }
            NodeKind::CmpExpr => self.lower_cmp(node, ty),
            NodeKind::AndExpr | NodeKind::OrExpr => self.lower_bool_bin(node, ty),
            NodeKind::NotExpr => {
                let kids = self.kids(node);
                let &[x] = kids.as_slice() else {
                    return Err(LowerError::Unsupported("not".into()));
                };
                let a = self.lower_expr(x)?;
                let inst = self.emit(Op::Not, a.0, NO_OPERAND, NO_OPERAND, ty);
                Ok(self.fresh(ty, inst))
            }
            NodeKind::UnaryExpr => self.lower_unary(node, ty),
            NodeKind::CastExpr => self.lower_cast(node, ty),
            NodeKind::CallExpr => self.lower_call(node, ty),
            NodeKind::StructLit => self.lower_struct_lit(node, ty),
            NodeKind::TupleOrParen => {
                let kids = self.kids(node);
                let &[x] = kids.as_slice() else {
                    return Err(LowerError::Unsupported("tuple".into()));
                };
                self.lower_expr(x)
            }
            NodeKind::IfExpr => Err(LowerError::Unsupported("value if".into())),
            NodeKind::MatchExpr => Err(LowerError::Match),
            NodeKind::Closure => Err(LowerError::Closure),
            NodeKind::TryExpr | NodeKind::Handler | NodeKind::RaiseStmt => Err(LowerError::Failure),
            NodeKind::ArrayLit => self.lower_array_lit(node, ty),
            NodeKind::Bracket => self.lower_slice_range(node, ty),
            NodeKind::RangeExpr => Err(LowerError::Unsupported("range".into())),
            _ => Err(LowerError::Unsupported(kind_name(self.kind(node)).into())),
        }
    }

    // -- sequences: array literals, slices, `reduce` ------------------------

    /// The element type of `Array[T, N]` / `Slice[T]` — both are `Nominal`
    /// with `T` first in the argument list (ch09's prelude generic types).
    fn seq_elem_ty(&self, ty: TyId) -> Option<TyId> {
        let bare = self.fir.tys.unqual(ty);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare)));
        args.first().copied()
    }

    /// The comptime length of `Array[T, N]`, which is `N` as a closed const
    /// argument (ch09 R13). `Slice[T]` has no second argument and therefore
    /// no comptime length — that distinction is exactly ch03 R12's
    /// "where `n` is comptime-known" (owner decision Q3, 2026-10-02).
    fn seq_const_len(&self, ty: TyId) -> Option<u32> {
        let bare = self.fir.tys.unqual(ty);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return None;
        }
        let args = self.fir.tys.args(ArgsId(self.fir.tys.b(bare)));
        let c = *args.get(1)?;
        if self.fir.tys.tag(c) != TyTag::ConstVal {
            return None;
        }
        let v = self
            .fir
            .tys
            .const_value(ConstId(self.fir.tys.a(c)))
            .as_int()?;
        u32::try_from(v).ok()
    }

    /// One element of an array literal: the checked type when there is one,
    /// otherwise the sequence's element type (the literal under a `reduce`
    /// stand-in may carry none).
    fn lower_elem(&mut self, node: usize, elem_ty: TyId) -> Result<ValId, LowerError> {
        let t = self.ty_of(node);
        if t != NO_TY && t != TY_ERROR {
            return self.lower_expr(node);
        }
        if self.kind(node) == NodeKind::Literal {
            return self.lower_literal(node, elem_ty);
        }
        Err(LowerError::Unresolved("array element".into()))
    }

    /// `[a, b, c]` and the repeat form `[v; n]` (ch07's `array_lit`) lower
    /// to one `agg_new` over the element values — the same cell aggregate
    /// `fors-interp` already runs for a struct literal. The repeat form
    /// evaluates `v` ONCE and names the resulting value `n` times, which is
    /// what the surface means and keeps `[1.0; 257]` at one instruction
    /// rather than 257.
    fn lower_array_lit(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let elem_ty = self.seq_elem_ty(ty).unwrap_or(TY_UNIT);
        let repeat = self
            .own_tokens(node)
            .iter()
            .any(|&(_, k)| k == TokenKind::Semi);
        let vals: Vec<ValId> = if repeat {
            let [v_node, n_node] = kids.as_slice() else {
                return Err(LowerError::Unsupported("array repeat literal".into()));
            };
            let n = self
                .seq_const_len(ty)
                .or_else(|| {
                    self.literal_int(*n_node)
                        .and_then(|v| u32::try_from(v).ok())
                })
                .ok_or_else(|| LowerError::Comptime("array repeat length".into()))?;
            let v = self.lower_elem(*v_node, elem_ty)?;
            vec![v; n as usize]
        } else {
            let mut out = Vec::with_capacity(kids.len());
            for &c in &kids {
                out.push(self.lower_elem(c, elem_ty)?);
            }
            out
        };
        let range = self.decl.insts.push_plain_operands(&vals);
        let inst = self.emit(Op::AggNew, range.start, range.end, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    /// `base[lo ..< hi]` (ch03 Rule 24) → `slice_range`, carrying the
    /// split-token alias seed design §3.4a requires of every
    /// memory-producing instruction. Plain `base[i]` indexing stays
    /// unsupported: nothing in F5's gate reads one, and the place-shaped
    /// form `lower_assign` already has covers the F2 `Buffer` stand-in.
    fn lower_slice_range(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let [base_node, idx_node] = kids.as_slice() else {
            return Err(LowerError::Unsupported("indexing".into()));
        };
        if self.kind(*idx_node) != NodeKind::RangeExpr {
            return Err(LowerError::Unsupported("indexing".into()));
        }
        // The seed names a PLACE (ch01 R19b's split provenance), so the
        // sliced base must be a local, not a temporary.
        if self.kind(*base_node) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported("slice of a temporary".into()));
        }
        let segs = self.path_segments(*base_node);
        let [base_sym] = segs.as_slice() else {
            return Err(LowerError::Unsupported("long projection".into()));
        };
        let (root, base_ty) = self.resolve_name(*base_sym)?;
        let base_val = self.read_root(root, base_ty, base_ty);
        let parent = self.intern_place(root, &[], base_ty);
        let rkids = self.kids(*idx_node);
        let [lo_node, hi_node] = rkids.as_slice() else {
            return Err(LowerError::Unsupported("open range".into()));
        };
        if !self.gap_ops(&rkids).contains(&TokenKind::DotDotLt) {
            return Err(LowerError::Unsupported("inclusive range".into()));
        }
        let lo = self.lower_range_bound(*lo_node)?;
        let hi = self.lower_range_bound(*hi_node)?;
        let result_ty = if ty == NO_TY || ty == TY_ERROR {
            TY_UNIT
        } else {
            ty
        };
        let inst = self.emit_seeded(
            Op::SliceRange,
            base_val.0,
            lo.0,
            hi.0,
            result_ty,
            AliasSeed::Split { parent, side: 0 },
        );
        Ok(self.fresh(result_ty, inst))
    }

    fn lower_range_bound(&mut self, node: usize) -> Result<ValId, LowerError> {
        let t = self.ty_of(node);
        if t != NO_TY && t != TY_ERROR {
            return self.lower_expr(node);
        }
        let v = self
            .literal_int(node)
            .ok_or_else(|| LowerError::Unsupported("range bound".into()))?;
        let inst = self.emit(
            Op::ConstInt,
            v as u32,
            (v >> 32) as u32,
            NO_OPERAND,
            TY_UNIT,
        );
        Ok(self.fresh(TY_UNIT, inst))
    }

    /// The three argument positions ch03 R11/R11a give `reduce`: the binary
    /// `op` (a bare operator token), the operand sequence, and the optional
    /// `identity:`.
    fn reduce_args(&mut self, node: usize) -> Result<ReduceArgs, LowerError> {
        let kids = self.kids(node);
        let mut out = ReduceArgs {
            op_tok: None,
            xs: None,
            identity: None,
        };
        for &a in kids.iter().skip(1) {
            match self.kind(a) {
                NodeKind::BareOp => {
                    let (t, _) = self
                        .leaf_token(a)
                        .ok_or_else(|| LowerError::Unresolved("reduce op".into()))?;
                    out.op_tok = Some(t);
                }
                NodeKind::NamedArg => {
                    let named = self
                        .own_tokens(a)
                        .into_iter()
                        .find(|&(_, k)| k == TokenKind::Ident)
                        .map(|(t, _)| self.tokens.text(t, self.source).to_vec());
                    if named.as_deref() != Some(b"identity".as_slice()) {
                        return Err(LowerError::Unsupported("reduce named argument".into()));
                    }
                    out.identity = self.kids(a).into_iter().next();
                }
                NodeKind::Closure => return Err(LowerError::Closure),
                _ => {
                    if out.xs.is_some() {
                        return Err(LowerError::Unsupported("reduce arity".into()));
                    }
                    out.xs = Some(a);
                }
            }
        }
        Ok(out)
    }

    /// The element type a `reduce(...)` call produces — read off the
    /// operand's own type, never from a checker fact ([HOLE-7]).
    fn reduce_elem_ty(&mut self, node: usize) -> Option<TyId> {
        let args = self.reduce_args(node).ok()?;
        let xs = args.xs?;
        if self.kind(xs) != NodeKind::NameExpr {
            return None;
        }
        let segs = self.path_segments(xs);
        let [base] = segs.as_slice() else {
            return None;
        };
        let (_, base_ty) = self.lookup(*base)?;
        self.seq_elem_ty(base_ty)
    }

    /// **[HOLE-7], site 2 of 3** (see [`reduce_stub_ranges`]): `reduce`'s
    /// whole typing, hard-coded here because no checker increment claims
    /// ch03 R11 — the element type is the operand's, the `op` is the
    /// declared binary operator, and the `identity:` is optional.
    ///
    /// Shape, per ch03 R12 as reworded by owner decision Q3 (2026-10-02):
    /// *"`reduce` MUST be given its final shape in FMIR, as a function of
    /// `(n, B, L)`, before parallel lowering; where `n` is comptime-known
    /// the tree MUST be explicit."* Both halves are here:
    /// - operand typed `Array[T, N]`: `n = N` is comptime-known, so the
    ///   EXPLICIT tree is emitted — a chain of `field` reads and binary ops
    ///   in exactly `fors_fmir::reduce::unrolled`'s order;
    /// - operand typed `Slice[T]`: `n` is a runtime value as far as FMIR is
    ///   concerned (design §3.9's [HOLE-3] case, and what every corpus
    ///   `reduce-n*` test is), so one `reduce_tree` instruction carries the
    ///   shape as a function of `(n, B, L)` with `B`/`L` as LITERAL
    ///   operands. The shape is fixed before parallel lowering either way,
    ///   which is what R12 buys.
    fn lower_reduce(&mut self, node: usize) -> Result<ValId, LowerError> {
        let args = self.reduce_args(node)?;
        let (Some(op_tok), Some(xs_node)) = (args.op_tok, args.xs) else {
            return Err(LowerError::Unsupported("reduce arguments".into()));
        };
        if self.kind(xs_node) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported("reduce over a temporary".into()));
        }
        let segs = self.path_segments(xs_node);
        let [base_sym] = segs.as_slice() else {
            return Err(LowerError::Unsupported("long projection".into()));
        };
        let (root, base_ty) = self.resolve_name(*base_sym)?;
        let elem_ty = self
            .seq_elem_ty(base_ty)
            .ok_or_else(|| LowerError::Unsupported("reduce over a non-sequence".into()))?;
        let binop = binop_for(op_tok, self.is_float_ty(elem_ty))
            .ok_or_else(|| LowerError::Unsupported("reduce operator".into()))?;
        let name = reduce_op_name(binop)
            .ok_or_else(|| LowerError::Unsupported("reduce operator".into()))?;
        let xs_val = self.read_root(root, base_ty, base_ty);
        let identity = match args.identity {
            Some(e) => Some(self.lower_elem(e, elem_ty)?),
            None => None,
        };

        // Comptime-known `n`: the explicit tree (ch03 R12 / Q3).
        if let Some(n) = self.seq_const_len(base_ty) {
            if n == 0 {
                // R11a with a statically empty operand: the identity IS the
                // answer, and without one the program traps.
                return match identity {
                    Some(v) => Ok(v),
                    None => Err(LowerError::Unsupported(
                        "comptime-empty reduce without an identity".into(),
                    )),
                };
            }
            let tree = fors_fmir::reduce::unrolled(
                n,
                fors_fmir::reduce::REDUCE_BLOCK,
                fors_fmir::reduce::REDUCE_LANES,
            )
            .expect("n >= 1 has an explicit tree");
            return Ok(self.emit_explicit_tree(&tree, xs_val, elem_ty, binop));
        }

        // Runtime `n`: the shape as a function of `(n, B, L)`.
        let sym = self.interner.intern(name.as_bytes());
        if !self.intrinsics.iter().any(|(id, _)| *id == sym.0) {
            self.intrinsics.push((sym.0, name.to_string()));
        }
        let red = self.decl.insts.push_reduce(ReduceRow {
            op: Callee::Intrinsic(sym),
            xs: xs_val,
            identity: identity.unwrap_or(ValId(ABSENT)),
            b: fors_fmir::reduce::REDUCE_BLOCK,
            l: fors_fmir::reduce::REDUCE_LANES,
        });
        let inst = self.emit(Op::ReduceTree, red, NO_OPERAND, NO_OPERAND, elem_ty);
        Ok(self.fresh(elem_ty, inst))
    }

    /// Emits `fors_fmir::reduce`'s explicit tree as straight-line FMIR:
    /// `Elem(i)` is a `field` read of the aggregate, `Op(l, r)` is one
    /// binary instruction with `l` on the LEFT (ch03 R11's operand order).
    fn emit_explicit_tree(
        &mut self,
        e: &fors_fmir::reduce::Expr,
        base: ValId,
        elem_ty: TyId,
        binop: Op,
    ) -> ValId {
        match e {
            fors_fmir::reduce::Expr::Elem(i) => {
                let inst = self.emit(Op::Field, base.0, *i, NO_OPERAND, elem_ty);
                self.fresh(elem_ty, inst)
            }
            fors_fmir::reduce::Expr::Op(l, r) => {
                let a = self.emit_explicit_tree(l, base, elem_ty, binop);
                let b = self.emit_explicit_tree(r, base, elem_ty, binop);
                let inst = self.emit(binop, a.0, b.0, NO_OPERAND, elem_ty);
                self.fresh(elem_ty, inst)
            }
        }
    }

    fn lower_literal(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let Some((tk, text)) = self.leaf_token(node) else {
            return Err(LowerError::Unresolved("literal".into()));
        };
        match tk {
            TokenKind::Int => {
                let v = fors_check::lower::parse_int_literal(text)
                    .ok_or_else(|| LowerError::Unresolved("integer literal".into()))?;
                // Narrow to the decided type's width: the checker owns the
                // range diagnostic; lowering never fails a clean body here.
                let bits = narrow_int(v, self.prim_of(ty));
                let inst = self.emit(
                    Op::ConstInt,
                    bits as u32,
                    (bits >> 32) as u32,
                    NO_OPERAND,
                    ty,
                );
                Ok(self.fresh(ty, inst))
            }
            TokenKind::Float => {
                let bits = parse_float_bits(text, self.prim_of(ty))?;
                let inst = self.emit(
                    Op::ConstFloat,
                    bits as u32,
                    (bits >> 32) as u32,
                    NO_OPERAND,
                    ty,
                );
                Ok(self.fresh(ty, inst))
            }
            TokenKind::Str => {
                let bytes = unescape_str(text)?;
                let sym = self.interner.intern(&bytes);
                let cid = self
                    .decl
                    .consts
                    .intern(fors_fmir::constpool::ConstValue::Str(sym));
                self.strings.push((cid.0, bytes));
                let inst = self.emit(Op::ConstStr, cid.0, NO_OPERAND, NO_OPERAND, ty);
                Ok(self.fresh(ty, inst))
            }
            TokenKind::KwTrue | TokenKind::KwFalse => {
                let b = (tk == TokenKind::KwTrue) as u32;
                let inst = self.emit(Op::ConstBool, b, NO_OPERAND, NO_OPERAND, ty);
                Ok(self.fresh(ty, inst))
            }
            _ => Err(LowerError::Unsupported("literal".into())),
        }
    }

    fn lower_path(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let segs = self.path_segments(node);
        match segs.as_slice() {
            [base] => {
                let (root, base_ty) = self.resolve_name(*base)?;
                Ok(self.read_root(root, base_ty, ty))
            }
            [base, _field] => {
                let (root, base_ty) = self.resolve_name(*base)?;
                match self.facts.member_of(node as u32) {
                    MemberTarget::Field { index, .. } => {
                        let b = self.read_root(root, base_ty, base_ty);
                        let inst = self.emit(Op::Field, b.0, index, NO_OPERAND, ty);
                        Ok(self.fresh(ty, inst))
                    }
                    MemberTarget::LenBuiltin { .. } => {
                        Err(LowerError::Unsupported("len builtin".into()))
                    }
                    MemberTarget::None => Err(LowerError::Unresolved("member".into())),
                }
            }
            _ => Err(LowerError::Unsupported("long projection".into())),
        }
    }

    fn lower_binary(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        if kids.len() < 2 {
            return Err(LowerError::Unsupported("binary".into()));
        }
        let ops = self.gap_ops(&kids);
        if ops.len() != kids.len() - 1 {
            return Err(LowerError::Unsupported("binary".into()));
        }
        let float = self.is_float_ty(ty);
        if !float && !self.is_int_ty(ty) {
            return Err(LowerError::Unsupported("non-numeric operator".into()));
        }
        let mut acc = self.lower_expr(kids[0])?;
        for (i, op) in ops.iter().enumerate() {
            let rhs = self.lower_expr(kids[i + 1])?;
            let fop =
                binop_for(*op, float).ok_or_else(|| LowerError::Unsupported("operator".into()))?;
            let inst = self.emit(fop, acc.0, rhs.0, NO_OPERAND, ty);
            acc = self.fresh(ty, inst);
        }
        Ok(acc)
    }

    fn lower_cmp(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let &[l, r] = kids.as_slice() else {
            return Err(LowerError::Unsupported("comparison chain".into()));
        };
        let ops = self.gap_ops(&kids);
        let &[op] = ops.as_slice() else {
            return Err(LowerError::Unsupported("comparison".into()));
        };
        let pred = match op {
            TokenKind::EqEq => CmpPred::Eq,
            TokenKind::NotEq => CmpPred::Ne,
            TokenKind::Lt => CmpPred::Lt,
            TokenKind::LtEq => CmpPred::Le,
            TokenKind::Gt => CmpPred::Gt,
            TokenKind::GtEq => CmpPred::Ge,
            _ => return Err(LowerError::Unsupported("comparison".into())),
        };
        let a = self.lower_expr(l)?;
        let b = self.lower_expr(r)?;
        // The comparison reads the OPERAND type, not the `bool` result.
        let oty = self.ty_of(l);
        let op = if self.is_float_ty(oty) {
            Op::Fcmp(pred)
        } else {
            Op::Icmp(pred)
        };
        let inst = self.emit(op, a.0, b.0, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    fn lower_bool_bin(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        if kids.len() < 2 {
            return Err(LowerError::Unsupported("boolean".into()));
        }
        let op = match self.kind(node) {
            NodeKind::AndExpr => Op::And,
            _ => Op::Or,
        };
        let mut acc = self.lower_expr(kids[0])?;
        for k in kids.iter().skip(1) {
            let rhs = self.lower_expr(*k)?;
            let inst = self.emit(op, acc.0, rhs.0, NO_OPERAND, ty);
            acc = self.fresh(ty, inst);
        }
        Ok(acc)
    }

    fn lower_unary(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let &[x] = kids.as_slice() else {
            return Err(LowerError::Unsupported("unary".into()));
        };
        let minus = self
            .own_tokens(node)
            .iter()
            .any(|&(_, k)| k == TokenKind::Minus);
        let plus = self
            .own_tokens(node)
            .iter()
            .any(|&(_, k)| k == TokenKind::Plus);
        if plus && !minus {
            return self.lower_expr(x);
        }
        if !minus {
            return Err(LowerError::Unsupported("unary".into()));
        }
        // Fold a negated literal: `-2147483648` is `MIN`, not a trap. The
        // fold reads the decided type, so it cannot miscompile.
        if self.kind(x) == NodeKind::Literal
            && let Some((tk, text)) = self.leaf_token(x)
        {
            match tk {
                TokenKind::Int => {
                    let v = fors_check::lower::parse_int_literal(text)
                        .ok_or_else(|| LowerError::Unresolved("integer literal".into()))?;
                    let bits = narrow_int(-v, self.prim_of(ty));
                    let inst = self.emit(
                        Op::ConstInt,
                        bits as u32,
                        (bits >> 32) as u32,
                        NO_OPERAND,
                        ty,
                    );
                    return Ok(self.fresh(ty, inst));
                }
                TokenKind::Float => {
                    let bits = parse_float_bits(text, self.prim_of(ty))?;
                    let neg = match self.prim_of(ty) {
                        Some(PrimKind::F32) => (-(f32::from_bits(bits as u32))).to_bits() as u64,
                        _ => (-f64::from_bits(bits)).to_bits(),
                    };
                    let inst = self.emit(
                        Op::ConstFloat,
                        neg as u32,
                        (neg >> 32) as u32,
                        NO_OPERAND,
                        ty,
                    );
                    return Ok(self.fresh(ty, inst));
                }
                _ => {}
            }
        }
        let a = self.lower_expr(x)?;
        let op = if self.is_float_ty(ty) {
            Op::Fneg(fors_fmir::op::Relax::NONE)
        } else if self.is_int_ty(ty) {
            Op::Neg(ArithMode::Trap)
        } else {
            return Err(LowerError::Unsupported("negation".into()));
        };
        let inst = self.emit(op, a.0, NO_OPERAND, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    fn lower_cast(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let Some(&x) = kids.first() else {
            return Err(LowerError::Unsupported("cast".into()));
        };
        let a = self.lower_expr(x)?;
        if num_kind_of(self.prim_of(self.ty_of(x))).is_none()
            || num_kind_of(self.prim_of(ty)).is_none()
        {
            return Err(LowerError::Unsupported("non-numeric cast".into()));
        }
        let inst = self.emit(Op::ConvChecked, a.0, NO_OPERAND, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    fn lower_call(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let Some(&callee_node) = kids.first() else {
            return Err(LowerError::Unsupported("call".into()));
        };
        if kids.iter().any(|&c| self.kind(c) == NodeKind::Handler) {
            return Err(LowerError::Failure);
        }
        let mut argv: Vec<ValId> = Vec::new();
        let mut convs: Vec<Conv> = Vec::new();
        for &a in kids.iter().skip(1) {
            match self.kind(a) {
                NodeKind::NamedArg => return Err(LowerError::Unsupported("named argument".into())),
                NodeKind::InoutArg | NodeKind::SetArg => {
                    return Err(LowerError::Unsupported("by-reference argument".into()));
                }
                _ => argv.push(self.lower_expr(a)?),
            }
        }
        let explicit: Vec<Conv> = self
            .facts
            .arg_convs
            .iter()
            .find(|(n, _)| *n == node as u32)
            .map(|(_, c)| c.clone())
            .unwrap_or_default();
        for i in 0..argv.len() {
            convs.push(explicit.get(i).copied().unwrap_or(Conv::Let));
        }
        match self.facts.callee_of(node as u32) {
            FactCallee::Direct(def) => {
                if self.kind(callee_node) != NodeKind::NameExpr
                    || self.path_segments(callee_node).len() != 1
                {
                    return Err(LowerError::Unresolved("call target".into()));
                }
                // I5 TYPES a call to a generic function, so the body is
                // checked-clean and reaches here; monomorphisation (ch03
                // R16-R18) is still not F1's, and the callee itself was
                // refused above as "generic function", so there would be
                // no body to call.
                if self
                    .fir
                    .sigs
                    .generics_store
                    .count(self.fir.sigs.generics(def))
                    > 0
                {
                    return Err(LowerError::Generic("call to a generic function".into()));
                }
                let key = self
                    .defs
                    .get(def)
                    .map(|r| r.key)
                    .ok_or_else(|| LowerError::Unresolved(format!("def{}", def.0)))?;
                Ok(self.emit_call(Callee::Direct(key), argv, convs, ty))
            }
            FactCallee::Method { def, owner: _ } => {
                let segs = self.path_segments(callee_node);
                if segs.len() < 2 {
                    return Err(LowerError::Unresolved("method target".into()));
                }
                let method = segs[segs.len() - 1];
                // Method position (`c.bump()`): the receiver is the first
                // segment and is a bound local. Qualified form
                // (`C.twice(c)`, R45): the first segment names the type and
                // the receiver is the first explicit argument (the
                // `arg_convs` row then carries its convention at [0]).
                if self.lookup(segs[0]).is_some() {
                    if segs.len() > 2 {
                        return Err(LowerError::Unsupported("long receiver".into()));
                    }
                    let recv_sym = segs[0];
                    let (root, base_ty) = self.resolve_name(recv_sym)?;
                    let recv = self.read_root(root, base_ty, base_ty);
                    let mut full_args = vec![recv];
                    full_args.extend(argv.iter().copied());
                    let mut full_convs =
                        vec![self.facts.recv_conv_of(node as u32).unwrap_or(Conv::Let)];
                    full_convs.extend(convs.iter().copied());
                    return self.emit_method_call(def, method, full_args, full_convs, ty);
                }
                if argv.is_empty() {
                    return Err(LowerError::Unresolved(display_sym(
                        &*self.interner,
                        segs[0],
                    )));
                }
                let mut full_convs =
                    vec![self.facts.recv_conv_of(node as u32).unwrap_or(Conv::Let)];
                full_convs.extend(convs.iter().skip(1).copied());
                self.emit_method_call(def, method, argv, full_convs, ty)
            }
            FactCallee::Variant { .. } => Err(LowerError::Unsupported("enum construction".into())),
            FactCallee::ValueFn => Err(LowerError::Closure),
            FactCallee::Undecided => Err(LowerError::Generic("unresolved call".into())),
            FactCallee::None => Err(LowerError::Unresolved("call".into())),
        }
    }

    fn emit_method_call(
        &mut self,
        def: DefId,
        method: Symbol,
        args: Vec<ValId>,
        convs: Vec<Conv>,
        ty: TyId,
    ) -> Result<ValId, LowerError> {
        // The §5.8 stand-in: any method spelled `write_line` is the line
        // writer, whatever its owner.
        if self.interner.resolve(method) == b"write_line" {
            let sym = self.interner.intern(b"stdout_write_line");
            if !self.intrinsics.iter().any(|(id, _)| *id == sym.0) {
                self.intrinsics.push((sym.0, "stdout_write_line".into()));
            }
            Ok(self.emit_call(Callee::Intrinsic(sym), args, convs, ty))
        } else {
            let key = self
                .defs
                .get(def)
                .map(|r| r.key)
                .ok_or_else(|| LowerError::Unresolved(format!("def{}", def.0)))?;
            Ok(self.emit_call(Callee::Direct(key), args, convs, ty))
        }
    }

    fn emit_call(&mut self, callee: Callee, args: Vec<ValId>, convs: Vec<Conv>, ty: TyId) -> ValId {
        let range = self.decl.insts.push_operands(&args, &convs);
        let call = self.decl.insts.push_call(CallRow {
            callee,
            args: range,
        });
        let op = match callee {
            Callee::Intrinsic(_) => Op::Intrinsic,
            _ => Op::CallDirect,
        };
        let inst = self.emit(op, call, NO_OPERAND, NO_OPERAND, ty);
        self.fresh(ty, inst)
    }

    fn lower_struct_lit(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let Some(&head) = kids.first() else {
            return Err(LowerError::Unsupported("struct literal".into()));
        };
        let _ = head;
        // Field order is the declaration order, NOT the source order:
        // resolve each `FInit` name against the `StructDecl`.
        let order = self.struct_field_order(ty)?;
        // Lower values in source order (side effects stay ordered), then
        // arrange positionally.
        let mut placed: Vec<Option<ValId>> = vec![None; order.len()];
        for &finit in kids.iter().skip(1) {
            if self.kind(finit) != NodeKind::FInit {
                return Err(LowerError::Unsupported("struct literal".into()));
            }
            let fname = self
                .own_tokens(finit)
                .into_iter()
                .find(|&(_, k)| k == TokenKind::Ident)
                .map(|(t, _)| self.interner.intern(self.tokens.text(t, self.source)))
                .ok_or_else(|| LowerError::Unresolved("field init".into()))?;
            let value = self
                .kids(finit)
                .into_iter()
                .next()
                .ok_or_else(|| LowerError::Unsupported("struct literal".into()))?;
            let v = self.lower_expr(value)?;
            let Some(idx) = order.iter().position(|s| *s == fname) else {
                return Err(LowerError::Unresolved("field init".into()));
            };
            placed[idx] = Some(v);
        }
        let mut vals: Vec<ValId> = Vec::with_capacity(order.len());
        for p in placed {
            vals.push(p.ok_or_else(|| LowerError::Unresolved("missing field init".into()))?);
        }
        let range = self.decl.insts.push_plain_operands(&vals);
        let inst = self.emit(Op::AggNew, range.start, range.end, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    /// The `Symbol` of each field of the struct `ty` names, in declaration
    /// order, read from the `StructDecl` CST. Cross-file heads are a later
    /// increment (every F1 gate test is single-file).
    fn struct_field_order(&mut self, ty: TyId) -> Result<Vec<Symbol>, LowerError> {
        let bare = self.fir.tys.unqual(ty);
        if self.fir.tys.tag(bare) != TyTag::Nominal {
            return Err(LowerError::Unsupported("struct literal".into()));
        }
        let head = DefId(self.fir.tys.a(bare));
        let (file, snode) = {
            let row = self
                .defs
                .get(head)
                .ok_or_else(|| LowerError::Unresolved(format!("def{}", head.0)))?;
            (row.file.0, row.node as usize)
        };
        if file != self.file_idx {
            return Err(LowerError::Unsupported("cross-file struct literal".into()));
        }
        let mut order = Vec::new();
        for c in self.kids(snode) {
            if self.kind(c) == NodeKind::Field {
                let name = self
                    .own_tokens(c)
                    .into_iter()
                    .find(|&(_, k)| k == TokenKind::Ident)
                    .map(|(t, _)| self.interner.intern(self.tokens.text(t, self.source)))
                    .ok_or_else(|| LowerError::Unresolved("struct field".into()))?;
                order.push(name);
            }
        }
        Ok(order)
    }

    // -- F2's `trap-bounds` stand-in (§5.8) -------------------------------

    /// Matches `Buffer.fixed(<int literal>)`: a qualified call textually
    /// spelled this way, regardless of what (if anything) it resolves to.
    /// `None` on any other shape, including a literal that fails to parse
    /// or a negative length.
    fn buffer_fixed_len(&mut self, call_node: usize) -> Option<u64> {
        let kids = self.kids(call_node);
        let &callee = kids.first()?;
        if self.kind(callee) != NodeKind::NameExpr {
            return None;
        }
        let segs = self.path_segments(callee);
        let &[a, b] = segs.as_slice() else {
            return None;
        };
        if self.interner.resolve(a) != b"Buffer" || self.interner.resolve(b) != b"fixed" {
            return None;
        }
        let &arg = kids.get(1)?;
        self.literal_int(arg)
    }

    /// Matches `<name>.slice[<int literal>]` where `<name>` is a local
    /// bound through [`FnLower::buffer_fixed_len`]'s stand-in. Returns the
    /// local's root slot and the index.
    fn buffer_slice_index(&mut self, bracket: usize) -> Option<(u32, u64)> {
        let kids = self.kids(bracket);
        let &[base, idx_node] = kids.as_slice() else {
            return None;
        };
        if self.kind(base) != NodeKind::NameExpr {
            return None;
        }
        let segs = self.path_segments(base);
        let &[buf_sym, field] = segs.as_slice() else {
            return None;
        };
        if self.interner.resolve(field) != b"slice" || !self.buffer_stub_locals.contains(&buf_sym) {
            return None;
        }
        let (root, _) = self.resolve_name(buf_sym).ok()?;
        let idx = self.literal_int(idx_node)?;
        Some((root, idx))
    }

    /// A bare integer `Literal` node's value, as `u64` (`None` for anything
    /// else, including a negative one).
    fn literal_int(&mut self, node: usize) -> Option<u64> {
        if self.kind(node) != NodeKind::Literal {
            return None;
        }
        let (tk, text) = self.leaf_token(node)?;
        if tk != TokenKind::Int {
            return None;
        }
        let v = fors_check::lower::parse_int_literal(text)?;
        u64::try_from(v).ok()
    }
}

/// Numeric-kind view for casts (mirrors `fors-interp`'s classification;
/// kept local so this crate never depends on the interpreter).
enum NumKind {
    Int,
    Float,
}

fn num_kind_of(p: Option<PrimKind>) -> Option<NumKind> {
    match p {
        Some(k) if k.is_integer() => Some(NumKind::Int),
        Some(k) if k.is_float() => Some(NumKind::Float),
        _ => None,
    }
}

/// Two's-complement narrowing of a literal value to its decided type.
fn narrow_int(v: i128, prim: Option<PrimKind>) -> u64 {
    let w = match prim {
        Some(PrimKind::I8) | Some(PrimKind::U8) => 8,
        Some(PrimKind::I16) | Some(PrimKind::U16) => 16,
        Some(PrimKind::I32) | Some(PrimKind::U32) => 32,
        _ => 64,
    };
    (v as u64) & if w == 64 { u64::MAX } else { (1u64 << w) - 1 }
}

fn parse_float_bits(text: &[u8], prim: Option<PrimKind>) -> Result<u64, LowerError> {
    let mut s = text;
    if s.ends_with(b"f32") || s.ends_with(b"f64") {
        s = &s[..s.len() - 3];
    }
    let clean: Vec<u8> = s.iter().copied().filter(|&c| c != b'_').collect();
    let s =
        std::str::from_utf8(&clean).map_err(|_| LowerError::Unresolved("float literal".into()))?;
    let v: f64 = s
        .parse()
        .map_err(|_| LowerError::Unresolved("float literal".into()))?;
    Ok(match prim {
        Some(PrimKind::F32) => (v as f32).to_bits() as u64,
        _ => v.to_bits(),
    })
}

/// `b"..."` (with quotes) to raw bytes: `\\ \" \n \r \t` plus `\xNN`.
fn unescape_str(text: &[u8]) -> Result<Vec<u8>, LowerError> {
    if text.len() < 2 || text[0] != b'"' {
        return Err(LowerError::Unresolved("string literal".into()));
    }
    let inner = &text[1..text.len() - 1];
    let mut out: Vec<u8> = Vec::with_capacity(inner.len());
    let mut i = 0;
    while i < inner.len() {
        let c = inner[i];
        if c != b'\\' {
            out.push(c);
            i += 1;
            continue;
        }
        i += 1;
        let e = *inner
            .get(i)
            .ok_or_else(|| LowerError::Unresolved("string escape".into()))?;
        match e {
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b't' => out.push(b'\t'),
            b'\\' => out.push(b'\\'),
            b'"' => out.push(b'"'),
            b'0' => out.push(0),
            b'x' => {
                let hi = *inner
                    .get(i + 1)
                    .ok_or_else(|| LowerError::Unresolved("string escape".into()))?;
                let lo = *inner
                    .get(i + 2)
                    .ok_or_else(|| LowerError::Unresolved("string escape".into()))?;
                let h =
                    hex_val(hi).ok_or_else(|| LowerError::Unresolved("string escape".into()))?;
                let l =
                    hex_val(lo).ok_or_else(|| LowerError::Unresolved("string escape".into()))?;
                out.push((h << 4) | l);
                i += 2;
            }
            _ => return Err(LowerError::Unsupported("string escape".into())),
        }
        i += 1;
    }
    Ok(out)
}

fn hex_val(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

fn display_sym(interner: &Interner, sym: Symbol) -> String {
    String::from_utf8_lossy(interner.resolve(sym)).into_owned()
}

fn kind_name(k: NodeKind) -> &'static str {
    match k {
        NodeKind::Literal => "literal",
        NodeKind::NameExpr => "name",
        NodeKind::AddExpr => "add",
        NodeKind::MulExpr => "mul",
        NodeKind::BitExpr => "bits",
        NodeKind::CmpExpr => "comparison",
        NodeKind::AndExpr => "and",
        NodeKind::OrExpr => "or",
        NodeKind::NotExpr => "not",
        NodeKind::UnaryExpr => "unary",
        NodeKind::CastExpr => "cast",
        NodeKind::CallExpr => "call",
        NodeKind::StructLit => "struct literal",
        NodeKind::TupleOrParen => "tuple",
        NodeKind::IfExpr => "if",
        _ => "expression",
    }
}

/// Maps one gap operator to its FMIR op (trapping mode; explicit modes are
/// a later increment's spelling).
fn binop_for(op: TokenKind, float: bool) -> Option<Op> {
    let trap = ArithMode::Trap;
    match (op, float) {
        (TokenKind::Plus, false) => Some(Op::Add(trap)),
        (TokenKind::Minus, false) => Some(Op::Sub(trap)),
        (TokenKind::Star, false) => Some(Op::Mul(trap)),
        (TokenKind::Slash, false) => Some(Op::Div(trap)),
        (TokenKind::Percent, false) => Some(Op::Rem(trap)),
        (TokenKind::Shl, false) => Some(Op::Shl(trap)),
        (TokenKind::Shr, false) => Some(Op::Shr(trap)),
        (TokenKind::Amp, false) => Some(Op::And),
        (TokenKind::Pipe, false) => Some(Op::Or),
        (TokenKind::Caret, false) => Some(Op::Xor),
        (TokenKind::Plus, true) => Some(Op::Fadd(fors_fmir::op::Relax::NONE)),
        (TokenKind::Minus, true) => Some(Op::Fsub(fors_fmir::op::Relax::NONE)),
        (TokenKind::Star, true) => Some(Op::Fmul(fors_fmir::op::Relax::NONE)),
        (TokenKind::Slash, true) => Some(Op::Fdiv(fors_fmir::op::Relax::NONE)),
        (TokenKind::Percent, true) => Some(Op::Frem(fors_fmir::op::Relax::NONE)),
        _ => None,
    }
}

/// Whether a CST kind is an expression (for `let` initialiser search).
fn is_expr(k: NodeKind) -> bool {
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
            | NodeKind::NameExpr
            | NodeKind::StructLit
            | NodeKind::TupleOrParen
            | NodeKind::ArrayLit
            | NodeKind::AsmExpr
            | NodeKind::Closure
            | NodeKind::IfExpr
            | NodeKind::MatchExpr
            | NodeKind::ComptimeBlock
    )
}

#[cfg(test)]
mod policy_reader_tests {
    //! E11's policy reader (`module_contract_policy`), unit-tested directly
    //! against `fors-syntax`'s real CST — the corpus spells the clause
    //! `contracts: .runtime;` / `.off;` (leading dot, trailing `;`), which
    //! is what `fors-syntax::parser::file`'s `ContractsClause` actually
    //! parses, not the raw-text grammar a stand-in might invent.

    use super::*;
    use fors_index::{Interner, Segments};
    use fors_syntax::parse_file;

    fn policy_of(src: &[u8]) -> Policy {
        let interner = &mut Interner::new();
        let parsed = parse_file(src);
        assert!(
            parsed.diags.is_empty(),
            "fixture must parse: {:?}",
            parsed.diags
        );
        let name: Segments = vec![interner.intern(b"m")];
        let file = FileInput {
            tree: &parsed.tree,
            tokens: &parsed.tokens,
            source: src,
            name,
        };
        module_contract_policy(&file)
    }

    #[test]
    fn explicit_runtime() {
        assert_eq!(
            policy_of(b"module m;\ncontracts: .runtime;\nfn main() { }\n"),
            Policy::Runtime
        );
    }

    #[test]
    fn explicit_off() {
        assert_eq!(
            policy_of(b"module m;\ncontracts: .off;\nfn main() { }\n"),
            Policy::Off
        );
    }

    #[test]
    fn absent_clause_defaults_to_runtime() {
        // ch02 R9: runtime-checked whenever the module's policy is
        // `.runtime` (default).
        assert_eq!(policy_of(b"fn main() { }\n"), Policy::Runtime);
        assert_eq!(policy_of(b"module m;\nfn main() { }\n"), Policy::Runtime);
    }

    #[test]
    fn policy_is_independent_of_module_path_shape() {
        // A multi-segment module path before the clause changes nothing.
        assert_eq!(
            policy_of(b"module app.calc;\ncontracts: .off;\nfn main() { }\n"),
            Policy::Off
        );
    }
}
