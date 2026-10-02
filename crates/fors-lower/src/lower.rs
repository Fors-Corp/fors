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
//!
//! Control flow is BLOCKS AND SLOTS, never SSA names: `if`, `while`, `for`
//! and `match` build a CFG whose loop-carried values live in frame-local
//! slots written with `init` and read with `copy_from`, so no phi nodes and
//! no block parameters are needed (design §3.1 gives FMIR places for
//! bindings). A `for`'s induction advance lives in its LATCH block, which
//! is also `continue`'s target, so `continue` advances exactly once.
//!
//! Three families are lowered by SPELLING rather than from a checker fact,
//! each because the checker does not type them yet and each confined and
//! named: `Buffer.fixed`/`<buf>.slice[i] = v` (F2's §5.8 stand-in),
//! `reduce` ([HOLE-7], F5), and ch03 Rules 4 and 6's language-known numeric
//! methods (`CH03_ARITH_OPS`). Only the last is the FINAL lowering — the
//! other two are stand-ins for bodies that will exist.

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
    stub_ranges.extend(ch03_prim_stub_ranges(file, facts, decl_node));
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
                NodeKind::TryExpr | NodeKind::Handler | NodeKind::RaiseStmt => {
                    return Err(LowerError::Failure);
                }
                NodeKind::Closure => return Err(LowerError::Closure),
                // `for`/`while`/`break`/`continue` and `match` lower from
                // F1-completion on; the M3 concurrency statements do not
                // (design §1.2 defers `spawn`/`parallel`/`simd for`).
                NodeKind::ParallelForStmt
                | NodeKind::ParallelStmt
                | NodeKind::SimdForStmt
                | NodeKind::SpawnStmt => return Err(LowerError::Loop),
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

/// ch03 Rule 4's `wrap_`/`sat_`/`unchecked_` counterpart of each Rule 2
/// trapping operator, and Rule 6's three lossy conversions: the SAME closed
/// family `fors-check`'s `methods.rs::CH03_PRIM_METHODS` lists, from the
/// other end. The checker cannot resolve these (they are declared by no
/// file, and `type-checker.md` §13 reaches ch03 at I10, so the lookup
/// answers `LookupError::Silent` and the call node stays `TY_ERROR`), which
/// makes them F1's to lower by SPELLING — the third instance of design
/// §5.8's "minimal intrinsic-backed stub" pattern, after `Buffer.fixed`
/// (F2) and `reduce` ([HOLE-7], F5).
///
/// Unlike those two this one is not a stand-in for a missing body: ch03
/// Rules 4 and 6 ARE the FMIR opcodes `ArithMode::{Wrap,Sat,Unchecked}` and
/// `conv_wrap`/`conv_sat`/`conv_trunc`, so the lowering here is the real and
/// final one. What I10 will supply is the TYPING (so `prescan` stops having
/// to hold the call out of its `TY_ERROR` scan and the operand types come
/// from `facts` instead of from the receiver).
const CH03_ARITH_OPS: &[(&[u8], TokenKind)] = &[
    (b"add", TokenKind::Plus),
    (b"sub", TokenKind::Minus),
    (b"mul", TokenKind::Star),
    (b"div", TokenKind::Slash),
    (b"rem", TokenKind::Percent),
    (b"shl", TokenKind::Shl),
    (b"shr", TokenKind::Shr),
];

/// The three conversion spellings of ch03 Rule 6, with the opcode each one
/// names. `as` itself is `conv_checked` (`lower_cast`).
const CH03_CONVS: &[(&[u8], Op)] = &[
    (b"wrap_as", Op::ConvWrap),
    (b"sat_as", Op::ConvSat),
    (b"trunc_as", Op::ConvTrunc),
];

/// Splits a ch03 Rule 4 method name into `(mode, operator token)`:
/// `wrap_add` → `(Wrap, +)`, `unchecked_neg` → `(Unchecked, -)` (unary).
/// `None` for anything outside the family.
fn ch03_arith_method(name: &[u8]) -> Option<(ArithMode, TokenKind, bool)> {
    const MODES: &[(&[u8], ArithMode)] = &[
        (b"wrap_", ArithMode::Wrap),
        (b"sat_", ArithMode::Sat),
        (b"unchecked_", ArithMode::Unchecked),
    ];
    let (mode, rest) = MODES
        .iter()
        .find_map(|&(prefix, m)| name.strip_prefix(prefix).map(|r| (m, r)))?;
    if rest == b"neg" {
        return Some((mode, TokenKind::Minus, true));
    }
    CH03_ARITH_OPS
        .iter()
        .find(|(n, _)| *n == rest)
        .map(|&(_, tok)| (mode, tok, false))
}

/// Is `name` one of ch03 Rules 4 and 6's language-known numeric methods?
fn is_ch03_prim_method(name: &[u8]) -> bool {
    ch03_arith_method(name).is_some() || CH03_CONVS.iter().any(|(n, _)| *n == name)
}

/// The last `Ident` of a `CallExpr`'s callee, when the callee is a method
/// path (`x.wrap_add`) or that path under an explicit type argument
/// (`x.wrap_as[u8]`). Structural, like [`call_names_reduce`].
fn call_method_name<'t>(file: &FileInput<'t>, call: usize) -> Option<&'t [u8]> {
    if call >= file.tree.len() || file.tree.kinds[call] != NodeKind::CallExpr {
        return None;
    }
    let callee = file.tree.children(call).next()?;
    let path = match file.tree.kinds[callee] {
        NodeKind::NameExpr => callee,
        // `x.wrap_as[u8]()`: the callee is `Bracket(NameExpr, targ)`.
        NodeKind::Bracket => file
            .tree
            .children(callee)
            .next()
            .filter(|&p| file.tree.kinds[p] == NodeKind::NameExpr)?,
        _ => return None,
    };
    let idents = node_own_idents(file, path);
    (idents.len() >= 2).then(|| *idents.last().expect("len >= 2"))
}

/// Is this call node one the ch03 Rule 4 / Rule 6 lowering owns? Two
/// conditions, and BOTH are needed:
///
/// 1. the callee path's last segment is in the closed family, and
/// 2. the checker resolved NO callee for it.
///
/// Condition 2 is what keeps a user method that merely shares a spelling
/// (`impl B { fn wrap_add(..) }`) running its own body — the same scoping
/// F7 gave `Str`'s byte stand-ins. The family is only ever reached through
/// `LookupError::Silent` on a PRIMITIVE receiver, which leaves
/// `FactCallee::Undecided`/`None`; a resolved `Method`/`Direct` callee means
/// the writer meant a real declaration and lowering must call it.
fn is_ch03_prim_site(file: &FileInput<'_>, facts: &BodyFacts, node: usize) -> bool {
    if !call_method_name(file, node).is_some_and(is_ch03_prim_method) {
        return false;
    }
    matches!(
        facts.callee_of(node as u32),
        FactCallee::Undecided | FactCallee::None
    )
}

/// Every ch03 Rule 4 / Rule 6 method call in the declaration, as `(start,
/// end)` node ranges `prescan` holds out of its `TY_ERROR` scan (see
/// [`CH03_ARITH_OPS`]).
fn ch03_prim_stub_ranges(
    file: &FileInput<'_>,
    facts: &BodyFacts,
    decl_node: usize,
) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    if decl_node >= file.tree.len() {
        return out;
    }
    let end = file.tree.subtree_end(decl_node).min(file.tree.len());
    for n in decl_node..end {
        if is_ch03_prim_site(file, facts, n) {
            out.push((n as u32, file.tree.subtree_end(n) as u32));
        }
    }
    out
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
    /// `@fastmath`'s per-instruction mask (design §5.6(6), ch03 R8): the
    /// mask of the innermost enclosing `@fastmath(...)` block, and
    /// [`Relax::NONE`] outside one. Every float instruction this walk emits
    /// carries it, which is exactly what `fastmath-scope-ends-run-ok` pins:
    /// the value AFTER the block is computed from `Relax::NONE`
    /// instructions. The interpreter ignores the mask and always computes
    /// the strict result (design E7), so the mask changes no M1 answer — it
    /// is carried for M2's backend, and dropping it would lose ch03 R8's
    /// permission before any backend could use it.
    relax: fors_fmir::op::Relax,
    /// The `continue`/`break` targets of the enclosing loops, innermost
    /// last. Empty in a non-loop context, which is what makes a stray
    /// `break` a named diagnostic rather than a panic (ch01 R8's own
    /// rejection is the checker's flow pass).
    loops: Vec<LoopTargets>,
    /// Does the declaration being lowered carry `@unsafe(invariant: ..)`?
    /// Read off the `FnDecl`'s own leading `Attribute` by `lower_fn`; the
    /// only thing that consults it is ch03 Rule 4's `unchecked_<op>` gate.
    unsafe_decl: bool,
}

/// One enclosing loop's two edges: where `continue` goes (the latch, which
/// is what advances a `for`'s induction variable) and where `break` goes.
#[derive(Clone, Copy)]
struct LoopTargets {
    latch: BlockId,
    exit: BlockId,
}

/// The three argument positions of a `reduce(...)` call, found by shape
/// (ch03 R11/R11a: a bare binary operator, the operand sequence, and the
/// optional `identity:`).
struct ReduceArgs {
    op_tok: Option<TokenKind>,
    xs: Option<usize>,
    identity: Option<usize>,
}

/// One ch03 Rule 4 / Rule 6 method call, by shape: the callee path's own
/// `Ident` segments (`[x, wrap_add]`) and the explicit type argument
/// `wrap_as`/`sat_as`/`trunc_as` carry (`x.wrap_as[u8]()`).
struct Ch03Site<'t> {
    targ: Option<usize>,
    segs: Vec<&'t [u8]>,
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
            relax: fors_fmir::op::Relax::NONE,
            loops: Vec::new(),
            unsafe_decl: false,
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

    /// The `TyId` the build already interned for the primitive `k`, found by
    /// scanning the `TyStore`'s rows.
    ///
    /// Lowering holds the `Fir` by SHARED reference — the checker is done,
    /// and `lower_build` must not be able to grow the type store behind the
    /// query engine's content hashes — so it cannot `intern` a type of its
    /// own. Every type lowering needs is therefore one the checker already
    /// interned, which is true of every primitive a program mentions:
    /// `x.wrap_as[u8]()`'s `u8` is named in the source, and a loop counter's
    /// `usize` is named by `Array`/`Slice`/`Index`'s own signatures. When it
    /// is NOT interned the caller reports (a named `LowerError`), never
    /// substitutes a wrong width.
    fn prim_ty(&self, k: PrimKind) -> Option<TyId> {
        (0..self.fir.tys.len() as u32).map(TyId).find(|&t| {
            self.fir.tys.tag(t) == TyTag::Prim
                && self.fir.tys.quals(t) == fors_fir::ty::Quals::NONE
                && self.fir.tys.a(t) == k as u32
        })
    }

    /// The integer type an induction variable and a sequence length get.
    /// `usize` is the right answer (ch09 R3: a length is a `usize`) and the
    /// only one `index`/`len` can mean; the fallbacks exist so a build that
    /// never mentions `usize` still gets a WIDE UNSIGNED counter rather than
    /// a wrong-width one, and a build with no integer type at all reports.
    fn index_ty(&self) -> Result<TyId, LowerError> {
        for k in [PrimKind::Usize, PrimKind::U64, PrimKind::I64] {
            if let Some(t) = self.prim_ty(k) {
                return Ok(t);
            }
        }
        Err(LowerError::Unresolved(
            "no `usize`/`u64`/`i64` type is interned in this build, so a loop \
             counter has no type"
                .into(),
        ))
    }

    /// A local slot with no surface name: a `for`'s induction variable, or
    /// the result slot of a `match` in value position. Invisible to
    /// `resolve_name`, so it can never shadow or be shadowed.
    fn fresh_root(&mut self) -> u32 {
        let root = self.next_root;
        self.next_root += 1;
        root
    }

    /// The `TyId` a TYPE-argument node names, for the one shape ch03 Rule 6
    /// needs: a bare primitive (`x.wrap_as[u8]()`). The parser leaves a
    /// bare-path type argument as a `NameExpr`/`TypeApp` leaf (see
    /// `node_kind.rs`'s note on `TypeApp`), so the name is read off the
    /// node's own `Ident` tokens; anything else is not a primitive and the
    /// caller reports.
    fn prim_type_arg(&self, node: usize) -> Option<PrimKind> {
        let (a, b) = self.tree.token_range(node);
        let mut name: Option<&[u8]> = None;
        for t in a..b {
            if self.tokens.kinds[t as usize] == TokenKind::Ident {
                if name.is_some() {
                    return None; // a dotted or applied type, not a primitive
                }
                name = Some(self.tokens.text(t as usize, self.source));
            }
        }
        prim_kind_named(name?)
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
        // Declarations own their leading `Attribute`s (fors-syntax
        // `node_kind.rs`): `@unsafe(invariant: "..")` is one of them.
        self.unsafe_decl = self.kids(decl_node).into_iter().any(|c| {
            self.kind(c) == NodeKind::Attribute
                && self.own_ident_texts(c).as_slice() == [b"unsafe".as_slice()]
        });
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
                    Some(&e) if self.kind(e) == NodeKind::MatchExpr => self.lower_match_stmt(e),
                    Some(&e) => {
                        self.ensure_open();
                        self.lower_expr(e).map(|_| ())
                    }
                }
            }
            NodeKind::ReturnStmt => self.lower_return(node),
            NodeKind::IfExpr => self.lower_if_stmt(node),
            NodeKind::AttrBlockStmt => self.lower_attr_block(node),
            NodeKind::ForStmt => self.lower_for(node),
            NodeKind::WhileStmt => self.lower_while(node),
            NodeKind::MatchExpr => self.lower_match_stmt(node),
            NodeKind::BreakStmt => self.lower_break(node),
            NodeKind::ContinueStmt => self.lower_continue(node),
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
        if self.ch03_method_call(e).is_some()
            && let Some(t) = self.ch03_result_ty(e)
        {
            return t;
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
        if self.kind(lhs) == NodeKind::Bracket {
            return self.lower_index_assign(lhs, rhs);
        }
        let v = self.lower_expr(rhs)?;
        // The RHS's type as `lower_let` would read it: the checker's answer,
        // or the operand's for the stand-ins the checker leaves `TY_ERROR`
        // (`reduce`, ch03 R4/R6). Never the raw `TY_ERROR` itself — a local
        // retyped to it stops being an integer for every later statement
        // (`total = total.wrap_add(b)` twice is ch03's own example).
        let rhs_ty = self.initialiser_ty(rhs);
        // LHS places: a bare local, or one field of a local.
        if self.kind(lhs) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported("complex assignment target".into()));
        }
        let segs = self.path_segments(lhs);
        match segs.as_slice() {
            [base] => {
                let (root, cur_ty) = self.resolve_name(*base)?;
                // A `var` has ONE declared type; an assignment never retypes
                // it. The RHS's type is taken only when the binding has no
                // real type yet (the F2/F5 stand-ins bind `TY_UNIT`).
                let ty = if cur_ty == TY_UNIT || cur_ty == NO_TY || cur_ty == TY_ERROR {
                    rhs_ty
                } else {
                    cur_ty
                };
                self.rebind(*base, ty);
                self.write_place(root, &[], ty, v);
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

    /// `base[i] = v` (and `base.field[i] = v`): one `init` to the element
    /// PLACE, whose runtime bounds check is ch02 R15's `bounds` trap. The
    /// base has to BE a place — a root, or one field of a root — because an
    /// FMIR place names a root slot plus projections; an element of a
    /// temporary has nowhere to be written back to.
    ///
    /// A user nominal receiver is a different lowering and is NOT this one:
    /// ch09 R29 routes it to the resolved `IndexMut::at_mut`, whose result
    /// is `scoped(self) Self.Output` — a PLACE, which no FMIR call opcode
    /// returns (design §3.10's four call forms all produce a value). That
    /// case reports rather than dropping the store.
    fn lower_index_assign(&mut self, lhs: usize, rhs: usize) -> Result<(), LowerError> {
        let kids = self.kids(lhs);
        let [base_node, idx_node] = kids.as_slice() else {
            return Err(LowerError::Unsupported("index assignment".into()));
        };
        if self.kind(*idx_node) == NodeKind::RangeExpr {
            return Err(LowerError::Unsupported(
                "assignment to a slice range".into(),
            ));
        }
        if matches!(
            self.facts.member_of(lhs as u32),
            MemberTarget::IndexImpl { .. }
        ) {
            return Err(LowerError::Unsupported(
                "`a[i] = v` through an `IndexMut` impl: `at_mut` returns a place \
                 (`scoped(self) Self.Output`), and no FMIR call opcode returns a \
                 place for the store to go through"
                    .into(),
            ));
        }
        if self.kind(*base_node) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported(
                "index assignment to a temporary".into(),
            ));
        }
        let segs = self.path_segments(*base_node);
        let (root, base_ty, prefix) = match segs.as_slice() {
            [base] => {
                let (root, t) = self.resolve_name(*base)?;
                (root, t, Vec::new())
            }
            [base, _field] => {
                let (root, _) = self.resolve_name(*base)?;
                let MemberTarget::Field { head, index } = self.facts.member_of(*base_node as u32)
                else {
                    return Err(LowerError::Unresolved("index assignment base".into()));
                };
                // The path node of an assignment TARGET carries no checker
                // type (`self.data` here is `NO_TY`; only the whole
                // `Bracket` is typed), so the field's type is read from the
                // declaration, never from `facts`.
                let field_ty = self.field_ty(head, index)?;
                (root, field_ty, vec![Seg::Field(index as u16)])
            }
            _ => return Err(LowerError::Unsupported("long projection".into())),
        };
        let elem_ty = self
            .seq_elem_ty(base_ty)
            .ok_or_else(|| LowerError::Unsupported("index assignment to a non-sequence".into()))?;
        let idx_ty = self.index_ty()?;
        let idx = self.lenient_operand(*idx_node, idx_ty)?;
        let v = self.lower_expr(rhs)?;
        let mut segs = prefix;
        segs.push(Seg::Index(idx));
        self.write_place(root, &segs, elem_ty, v);
        Ok(())
    }

    /// The declared type of field `index` of the struct `head`, from the
    /// FIR member table — the same row `fors-check::member` resolved the
    /// [`MemberTarget::Field`] fact from. Used where the CST node naming
    /// the field has no checker type of its own (an assignment target's
    /// path). A field whose type still mentions a parameter belongs to a
    /// generic struct, which is I5's instantiation, not F1's.
    fn field_ty(&self, head: DefId, index: u32) -> Result<TyId, LowerError> {
        let ms = self.fir.sigs.members(head);
        if index as usize >= self.fir.sigs.member_store.count(ms) {
            return Err(LowerError::Unresolved(format!(
                "field {index} of def{}",
                head.0
            )));
        }
        let m = self.fir.sigs.member_store.get(ms, index as usize);
        if m.kind != fors_fir::sig::MemberKind::Field {
            return Err(LowerError::Unresolved("field member".into()));
        }
        if !self.fir.tys.is_monomorphic(m.ty) {
            return Err(LowerError::Generic("field of a generic struct".into()));
        }
        Ok(m.ty)
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

    // -- `match` --------------------------------------------------------------

    /// `match <scalar> { <literal> => { .. } ... _ => { .. } }` in statement
    /// position, lowered to one `switch_discr` over the scrutinee's own bits
    /// (design §3.10's terminator table).
    ///
    /// **Scope, and why it stops here.** §4.2's contract is that lowering
    /// READS the checker's decisions and never remakes them, and I7 made
    /// every decision a general `match` lowering needs: which constructor a
    /// `PatPath` names, which component each binding takes, whether an arm
    /// is reachable. Those decisions live in `fors-check`'s own `PatStore`
    /// and are DISCARDED when `check_build` returns — `CheckOutput` carries
    /// `BodyFacts`, which has a per-node type, callee, receiver convention
    /// and member column and NO pattern column, so there is nothing for
    /// lowering to read. Deriving them again from the CST here would be the
    /// one thing §4.2 forbids, and on the ambiguous case it would be a
    /// guess: a single-segment `PatPath` is a fresh BINDING or a unit
    /// variant/`const` name depending on resolution, and nothing in the
    /// grammar tells the two apart.
    ///
    /// So this lowers exactly the subset the GRAMMAR decides on its own — a
    /// scalar scrutinee with literal and wildcard arms, where `PatLit` is a
    /// literal and `PatWild` is "everything else" whatever resolution says
    /// — and every other pattern form is [`LowerError::Match`], naming the
    /// missing fact. Enum and struct patterns (and `match` in value
    /// position) land with the `fors-check` increment that records the
    /// pattern facts in `BodyFacts`; the `switch_discr` machinery they need
    /// is here and executed.
    fn lower_match_stmt(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        let Some((&scrut, arms)) = kids.split_first() else {
            return Err(LowerError::Match);
        };
        let sty = self.ty_of(scrut);
        let scalar = self.is_int_ty(sty) || self.prim_of(sty) == Some(PrimKind::Bool);
        if !scalar {
            return Err(LowerError::Match);
        }
        // Read every arm's pattern FIRST: one unsupported form must leave no
        // half-built CFG behind.
        let mut cases: Vec<(Option<u64>, usize)> = Vec::new();
        for &arm in arms {
            if self.kind(arm) != NodeKind::Arm {
                return Err(LowerError::Match);
            }
            let akids = self.kids(arm);
            let [pat, body] = akids.as_slice() else {
                // A guard (`if` on an arm) is a third child: ch09's guard
                // reachability is I7's, and the facts are not carried.
                return Err(LowerError::Match);
            };
            if self.kind(*body) != NodeKind::Block {
                return Err(LowerError::Match);
            }
            match self.kind(*pat) {
                NodeKind::PatWild => cases.push((None, *body)),
                NodeKind::PatLit => {
                    let bits = self.pat_lit_bits(*pat, sty)?;
                    cases.push((Some(bits), *body));
                }
                _ => return Err(LowerError::Match),
            }
        }
        if cases.is_empty() {
            return Err(LowerError::Match);
        }
        // A `_` arm that is not LAST would be shadowed in the surface
        // reading but not in a `switch_discr` (whose arm table is consulted
        // before the default edge). ch09's unreachable-arm rule is the
        // checker's; lowering refuses the shape rather than silently
        // reordering it.
        if cases[..cases.len() - 1].iter().any(|(v, _)| v.is_none()) {
            return Err(LowerError::Match);
        }
        let d = self.lower_expr(scrut)?;
        let src = self.cur;
        let blocks: Vec<BlockId> = cases.iter().map(|_| self.new_block()).collect();
        let wildcard = cases.iter().position(|(v, _)| v.is_none());
        // Without a `_` arm the default edge is unreachable: ch09 R56 makes
        // the checker prove the arms exhaustive, so reaching it is a
        // compiler bug, which `unreachable` reports as one rather than
        // silently falling through to the join.
        let default = match wildcard {
            Some(i) => blocks[i],
            None => self.new_block(),
        };
        let join = self.new_block();
        let rows: Vec<fors_fmir::inst::SwitchArm> = cases
            .iter()
            .zip(&blocks)
            .filter_map(|(&(v, _), &b)| {
                v.map(|bits| fors_fmir::inst::SwitchArm {
                    value: bits as i64,
                    target: b,
                })
            })
            .collect();
        let range = self.decl.insts.push_switch_arms(&rows);
        let sw = self.decl.insts.push_switch(fors_fmir::inst::SwitchRow {
            discr: d,
            default,
            arms: range,
        });
        self.cur = src;
        self.seal(self.term(Op::SwitchDiscr, sw, NO_OPERAND, NO_OPERAND));
        for (i, &(_, body)) in cases.iter().enumerate() {
            self.cur = blocks[i].0 as usize;
            self.scopes.push(HashMap::new());
            let r = self.lower_block_children(body);
            self.scopes.pop();
            r?;
            if self.is_open() {
                self.seal(self.term(Op::Br, join.0, NO_OPERAND, NO_OPERAND));
            }
        }
        if wildcard.is_none() {
            self.cur = default.0 as usize;
            self.seal(self.term(Op::Unreachable, NO_OPERAND, NO_OPERAND, NO_OPERAND));
        }
        self.cur = join.0 as usize;
        Ok(())
    }

    /// A `PatLit`'s value as the scrutinee's own bit pattern, so the arm
    /// table compares equal to the zero-extended slot the interpreter
    /// reads. `[-] number`, `true` and `false` (ch07's `PatLit`); a string
    /// pattern is not a scalar one and reports.
    fn pat_lit_bits(&mut self, pat: usize, sty: TyId) -> Result<u64, LowerError> {
        let (a, b) = self.tree.token_range(pat);
        let mut neg = false;
        for t in a..b {
            let k = self.tokens.kinds[t as usize];
            if k.is_trivia() {
                continue;
            }
            let text = self.tokens.text(t as usize, self.source);
            match k {
                TokenKind::Minus => neg = true,
                TokenKind::Int => {
                    let v = fors_check::lower::parse_int_literal(text)
                        .ok_or_else(|| LowerError::Unresolved("pattern literal".into()))?;
                    return Ok(narrow_int(if neg { -v } else { v }, self.prim_of(sty)));
                }
                TokenKind::KwTrue => return Ok(1),
                TokenKind::KwFalse => return Ok(0),
                _ => return Err(LowerError::Match),
            }
        }
        Err(LowerError::Match)
    }

    // -- attribute blocks, loops ---------------------------------------------

    /// `@fastmath(<flag> {, <flag>}) { ... }` (ch03 Rule 8, design §5.6(6)):
    /// the flags become the per-instruction `relax` mask of every float
    /// instruction the BLOCK emits, and the mask is restored at the closing
    /// brace. That restoration is the whole of `fastmath-scope-ends-run-ok`:
    /// Rule 8 permits but never requires fusing INSIDE the block, so only
    /// the value after it is pinned, and after it the instructions carry
    /// `Relax::NONE` again.
    ///
    /// Any other attributed block (`@unsafe(invariant: ..)`) is a named
    /// diagnostic: its semantics are not F1's, and treating an unknown
    /// attribute as "no attribute" would silently drop a safety obligation.
    fn lower_attr_block(&mut self, node: usize) -> Result<(), LowerError> {
        let kids = self.kids(node);
        let attr = kids
            .iter()
            .copied()
            .find(|&c| self.kind(c) == NodeKind::Attribute)
            .ok_or_else(|| {
                LowerError::Unsupported("an attributed block with no attribute".into())
            })?;
        let block = kids
            .iter()
            .copied()
            .find(|&c| self.kind(c) == NodeKind::Block)
            .ok_or_else(|| LowerError::Unsupported("an attributed block with no body".into()))?;
        let name = self.own_ident_texts(attr);
        if name.as_slice() != [b"fastmath".as_slice()] {
            return Err(LowerError::Unsupported(format!(
                "`@{}` block",
                String::from_utf8_lossy(name.first().copied().unwrap_or(b"?"))
            )));
        }
        let mut mask = 0u8;
        let mut flags = 0usize;
        for arg in self.kids(attr) {
            if self.kind(arg) != NodeKind::AttrArg {
                continue;
            }
            for &f in &self.own_ident_texts(arg) {
                mask |= relax_flag(f).ok_or_else(|| {
                    LowerError::Unsupported(format!("`@fastmath({})`", String::from_utf8_lossy(f)))
                })?;
                flags += 1;
            }
            for p in self.kids(arg) {
                for &f in &self.own_ident_texts(p) {
                    mask |= relax_flag(f).ok_or_else(|| {
                        LowerError::Unsupported(format!(
                            "`@fastmath({})`",
                            String::from_utf8_lossy(f)
                        ))
                    })?;
                    flags += 1;
                }
            }
        }
        // A bare `@fastmath { .. }` names no flag, which ch03 Rule 8 reads
        // as every relaxation permitted. The mask changes no M1 answer (the
        // interpreter always computes strict, design E7), so this is a
        // carried permission, never a computed value.
        if flags == 0 {
            mask = fors_fmir::op::Relax::REASSOC
                | fors_fmir::op::Relax::CONTRACT
                | fors_fmir::op::Relax::NSZ
                | fors_fmir::op::Relax::FINITE
                | fors_fmir::op::Relax::RECIP;
        }
        let saved = self.relax;
        self.relax = fors_fmir::op::Relax(mask);
        self.scopes.push(HashMap::new());
        let r = self.lower_block_children(block);
        self.scopes.pop();
        self.relax = saved;
        r
    }

    /// The symbol a `Binding` names, or `None` for `_` (ch07's wildcard
    /// binding, which names nothing and so binds nothing).
    fn binding_symbol(&mut self, binding: usize) -> Option<Symbol> {
        let (k, text) = self.leaf_token(binding)?;
        if k != TokenKind::Ident {
            return None;
        }
        let text = text.to_vec();
        Some(self.interner.intern(&text))
    }

    /// `while <cond> { <body> }`: a header block that re-evaluates the
    /// condition every iteration, a body, a latch (`continue`'s target, and
    /// where a `for`'s induction variable advances) and an exit
    /// (`break`'s target).
    ///
    /// No block parameters and no phi nodes: every loop-carried value lives
    /// in a frame-local SLOT, written through `init` and read through
    /// `copy_from`, which is the same representation `let`/`var` already
    /// use (design §3.1 gives FMIR places, not SSA names, for bindings).
    /// An accumulator like `plain-for-accumulator-accepted-run-ok`'s `acc`
    /// therefore needs nothing of its own.
    fn lower_while(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        let [cond_node, body_node] = kids.as_slice() else {
            return Err(LowerError::Unsupported("while".into()));
        };
        if self.kind(*body_node) != NodeKind::Block {
            return Err(LowerError::Unsupported(
                "a while body that is not a block".into(),
            ));
        }
        let src = self.cur;
        let header = self.new_block();
        let body = self.new_block();
        let latch = self.new_block();
        let exit = self.new_block();
        self.cur = src;
        self.seal(self.term(Op::Br, header.0, NO_OPERAND, NO_OPERAND));
        self.cur = header.0 as usize;
        let c = self.lower_expr(*cond_node)?;
        self.seal(self.term(Op::CondBr, c.0, body.0, exit.0));
        self.cur = body.0 as usize;
        self.scopes.push(HashMap::new());
        let r = self.lower_loop_body_inner(*body_node, header, latch, exit, None);
        self.scopes.pop();
        r
    }

    /// What the latch block does besides jumping back. `while` passes
    /// `None`; `for` passes its induction-variable advance, which belongs
    /// HERE and not at the end of the body so that `continue` runs it
    /// exactly once per iteration (a `continue` that skipped the advance
    /// would spin forever). It is a parameter rather than a field because
    /// loops NEST: an inner `for`'s latch must not consume the outer's
    /// advance (`gate_nested_loops_break_the_inner_one_only`).
    fn lower_latch(&mut self, advance: Option<(u32, TyId, u64)>) -> Result<(), LowerError> {
        let Some((root, ty, step_lit)) = advance else {
            return Ok(());
        };
        let cur = self.read_root(root, ty, ty);
        let one = self.emit(
            Op::ConstInt,
            step_lit as u32,
            (step_lit >> 32) as u32,
            NO_OPERAND,
            ty,
        );
        let one = self.fresh(ty, one);
        // ch03 Rule 2's trapping `+`: an induction variable that would wrap
        // is a trap like any other overflow, never a silent wrap.
        let next = self.emit(Op::Add(ArithMode::Trap), cur.0, one.0, NO_OPERAND, ty);
        let next = self.fresh(ty, next);
        self.write_place(root, &[], ty, next);
        Ok(())
    }

    /// `for <binding> in <lo ..< hi> { .. }` and `for <binding> in <seq>
    /// { .. }` over an `Array[T, N]` or a `Slice[T]` (ch07's `for`; the
    /// `plain-for-accumulator-accepted-run-ok` gate is the slice form).
    ///
    /// Both forms become the SAME counted loop: an induction slot, a
    /// `header` comparing it against the bound, a body, and a `latch` that
    /// advances it. In the sequence form the loop variable is one `index`
    /// read per iteration; in the range form it is the counter's value.
    /// Iterator protocols (`mem.iter`, `Iterator.next`) are F7's surface
    /// over exactly this; `for` over an iterator VALUE is not lowered here
    /// and says so.
    fn lower_for(&mut self, node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let kids = self.kids(node);
        let [binding, iter_node, body_node] = kids.as_slice() else {
            return Err(LowerError::Unsupported("for".into()));
        };
        if self.kind(*binding) != NodeKind::Binding {
            return Err(LowerError::Unsupported(
                "a destructuring `for` binding".into(),
            ));
        }
        if self.kind(*body_node) != NodeKind::Block {
            return Err(LowerError::Unsupported(
                "a for body that is not a block".into(),
            ));
        }
        let var = self.binding_symbol(*binding);
        let range = self.kind(*iter_node) == NodeKind::RangeExpr;
        // The induction variable's own type and its two bounds.
        let (ity, start, bound, seq) = if range {
            let rkids = self.kids(*iter_node);
            let [lo_node, hi_node] = rkids.as_slice() else {
                return Err(LowerError::Unsupported("an open range in `for`".into()));
            };
            if !self.gap_ops(&rkids).contains(&TokenKind::DotDotLt) {
                return Err(LowerError::Unsupported(
                    "an inclusive range in `for`".into(),
                ));
            }
            let t = self.ty_of(*lo_node);
            let ity = if self.is_int_ty(t) {
                t
            } else {
                self.index_ty()?
            };
            let lo = self.lenient_operand(*lo_node, ity)?;
            let hi = self.lenient_operand(*hi_node, ity)?;
            (ity, lo, hi, None)
        } else {
            let seq_ty = self.ty_of(*iter_node);
            let elem_ty = self.seq_elem_ty(seq_ty).ok_or_else(|| {
                LowerError::Unsupported(
                    "`for` over something that is not an `Array`/`Slice` (an iterator \
                     value needs F7's `Iterator` protocol)"
                        .into(),
                )
            })?;
            let seqv = self.lower_expr(*iter_node)?;
            let ity = self.index_ty()?;
            let len = self.emit_seq_len(seqv, ity);
            let zero = self.emit(Op::ConstInt, 0, 0, NO_OPERAND, ity);
            let zero = self.fresh(ity, zero);
            (ity, zero, len, Some((seqv, elem_ty)))
        };
        let iroot = self.fresh_root();
        self.write_place(iroot, &[], ity, start);
        let src = self.cur;
        let header = self.new_block();
        let body = self.new_block();
        let latch = self.new_block();
        let exit = self.new_block();
        self.cur = src;
        self.seal(self.term(Op::Br, header.0, NO_OPERAND, NO_OPERAND));
        // Header: `i < bound`, unsigned or signed by the counter's own type.
        self.cur = header.0 as usize;
        let i = self.read_root(iroot, ity, ity);
        let bool_ty = self.bool_ty();
        let cmp = self.emit(Op::Icmp(CmpPred::Lt), i.0, bound.0, NO_OPERAND, bool_ty);
        let cmp = self.fresh(bool_ty, cmp);
        self.seal(self.term(Op::CondBr, cmp.0, body.0, exit.0));
        // Body: bind the loop variable, then the user's statements.
        self.cur = body.0 as usize;
        self.scopes.push(HashMap::new());
        let (value, vty) = match seq {
            None => (self.read_root(iroot, ity, ity), ity),
            Some((seqv, elem_ty)) => {
                let idx = self.read_root(iroot, ity, ity);
                (self.emit_index(seqv, idx, elem_ty, None), elem_ty)
            }
        };
        if let Some(sym) = var {
            let root = self.bind(sym, vty);
            self.write_place(root, &[], vty, value);
        }
        let r = self.lower_loop_body_inner(*body_node, header, latch, exit, Some((iroot, ity, 1)));
        self.scopes.pop();
        r
    }

    /// `lower_loop_body` with the body's own scope already pushed by the
    /// caller (the `for` form binds its loop variable in that scope).
    fn lower_loop_body_inner(
        &mut self,
        body_node: usize,
        header: BlockId,
        latch: BlockId,
        exit: BlockId,
        advance: Option<(u32, TyId, u64)>,
    ) -> Result<(), LowerError> {
        self.loops.push(LoopTargets { latch, exit });
        let r = self.lower_block_children(body_node);
        self.loops.pop();
        r?;
        if self.is_open() {
            self.seal(self.term(Op::Br, latch.0, NO_OPERAND, NO_OPERAND));
        }
        self.cur = latch.0 as usize;
        self.lower_latch(advance)?;
        self.seal(self.term(Op::Br, header.0, NO_OPERAND, NO_OPERAND));
        self.cur = exit.0 as usize;
        Ok(())
    }

    fn lower_break(&mut self, _node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let Some(t) = self.loops.last().copied() else {
            return Err(LowerError::Unresolved("`break` outside a loop".into()));
        };
        self.seal(self.term(Op::Br, t.exit.0, NO_OPERAND, NO_OPERAND));
        Ok(())
    }

    fn lower_continue(&mut self, _node: usize) -> Result<(), LowerError> {
        self.ensure_open();
        let Some(t) = self.loops.last().copied() else {
            return Err(LowerError::Unresolved("`continue` outside a loop".into()));
        };
        self.seal(self.term(Op::Br, t.latch.0, NO_OPERAND, NO_OPERAND));
        Ok(())
    }

    /// The `bool` type, for a comparison lowering synthesised rather than
    /// read off a source node. Only the BITS of a loop guard are observable
    /// (`cond_br` reads the slot, never its type), so a build with no `bool`
    /// row falls back to `TY_UNIT` exactly as the F2 `Buffer` stand-in's
    /// inert slots do.
    fn bool_ty(&self) -> TyId {
        self.prim_ty(PrimKind::Bool).unwrap_or(TY_UNIT)
    }

    /// `len(seq)` for an `Array`/`Slice`/`Buffer`-shaped value: ch10 Rule
    /// 42's `len` builtin, lowered to the `seq_len` intrinsic.
    ///
    /// design §5.8's "minimal intrinsic-backed stub" once more: FMIR has no
    /// `len` opcode (design §3.10's 71 do not include one — a real `Slice`
    /// is a `{ptr, len}` pair whose `len` is a `field` read), and the
    /// descriptor `slice_range` builds is this crate's stand-in until F7's
    /// real `Slice` representation lands. `seq_len` reads that descriptor's
    /// third cell, or an aggregate's own cell count.
    fn emit_seq_len(&mut self, seq: ValId, ity: TyId) -> ValId {
        let name = "seq_len";
        let sym = self.interner.intern(name.as_bytes());
        if !self.intrinsics.iter().any(|(id, _)| *id == sym.0) {
            self.intrinsics.push((sym.0, name.to_string()));
        }
        self.emit_call(Callee::Intrinsic(sym), vec![seq], vec![Conv::Let], ity)
    }

    /// One `index` instruction, with the alias seed design §3.4a requires of
    /// every memory-producing op: a SPLIT of the indexed place when the base
    /// is a named local (ch01 Rule 19b's split provenance — element `i` is
    /// one piece of that place), and otherwise the weakest honest seed,
    /// `Conv(Let)`, which ch01 Rule 7 says is not a no-alias fact.
    fn emit_index(
        &mut self,
        base: ValId,
        idx: ValId,
        elem_ty: TyId,
        parent: Option<PlaceId>,
    ) -> ValId {
        let seed = match parent {
            Some(p) => AliasSeed::Split { parent: p, side: 0 },
            None => AliasSeed::Conv(Conv::Let),
        };
        let inst = self.emit_seeded(Op::Index, base.0, idx.0, NO_OPERAND, elem_ty, seed);
        self.fresh(elem_ty, inst)
    }

    // -- expressions ----------------------------------------------------------

    fn lower_expr(&mut self, node: usize) -> Result<ValId, LowerError> {
        // [HOLE-7]: a `reduce(...)` call is poisoned by the checker, so it
        // is intercepted before the `TY_ERROR` gate (see
        // `reduce_stub_ranges` for the whole hard-coding).
        if call_names_reduce(self.tree, self.tokens, self.source, node) {
            return self.lower_reduce(node);
        }
        // ch03 Rules 4 and 6 (see `CH03_ARITH_OPS`): the checker's lookup is
        // silent on them, so the call node is `TY_ERROR` and this too has to
        // run before the gate below.
        if self.ch03_method_call(node).is_some() {
            return self.lower_ch03_prim_method(node);
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
            NodeKind::Bracket => self.lower_bracket(node, ty),
            NodeKind::RangeExpr => Err(LowerError::Unsupported("range".into())),
            _ => Err(LowerError::Unsupported(kind_name(self.kind(node)).into())),
        }
    }

    // -- sequences: array literals, slices, `reduce` ------------------------

    /// The element type of `Array[T, N]` / `Slice[T]` — both are `Nominal`
    /// with `T` first in the argument list (ch09's prelude generic types).
    fn seq_elem_ty(&self, ty: TyId) -> Option<TyId> {
        // `NO_TY` is not a row (`TyStore::unqual` would index past the
        // end): a node the checker left untyped — an assignment target's
        // path, a stand-in's operand — has no element type to read.
        if ty == NO_TY || ty == TY_ERROR {
            return None;
        }
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
        if ty == NO_TY || ty == TY_ERROR {
            return None;
        }
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

    /// A postfix `base[...]`: ch03 Rule 24's RANGE form (`slice_range`) or
    /// a scalar index. The two are told apart by the index expression's own
    /// shape, which is how the grammar distinguishes them.
    fn lower_bracket(&mut self, node: usize, ty: TyId) -> Result<ValId, LowerError> {
        let kids = self.kids(node);
        let [base_node, idx_node] = kids.as_slice() else {
            return Err(LowerError::Unsupported("indexing".into()));
        };
        if self.kind(*idx_node) == NodeKind::RangeExpr {
            return self.lower_slice_range(node, ty);
        }
        self.lower_index(node, *base_node, *idx_node, ty)
    }

    /// `base[i]` for a scalar `i`: the `index` opcode on an `Array`/`Slice`,
    /// or — when the checker recorded F7's [`MemberTarget::IndexImpl`] fact
    /// — a call to the resolved `Index::at` body of a USER nominal type
    /// (ch09 R29's unambiguous-impl case), which is what makes `Buffer`'s
    /// and `Vec`'s own `a[i]` run their own bounds logic rather than a
    /// built-in one this crate invented.
    fn lower_index(
        &mut self,
        node: usize,
        base_node: usize,
        idx_node: usize,
        ty: TyId,
    ) -> Result<ValId, LowerError> {
        if let MemberTarget::IndexImpl { at, .. } = self.facts.member_of(node as u32) {
            let name = self
                .defs
                .get(at)
                .and_then(|r| r.name)
                .ok_or_else(|| LowerError::Unresolved(format!("def{}", at.0)))?;
            let recv = self.lower_expr(base_node)?;
            let idx = self.lower_expr(idx_node)?;
            let recv_conv = self.facts.recv_conv_of(node as u32).unwrap_or(Conv::Let);
            return self.emit_method_call(
                at,
                name,
                vec![recv, idx],
                vec![recv_conv, Conv::Let],
                ty,
            );
        }
        // The base's type and value. A path under a `Bracket` (`self.data`
        // in `self.data[i]`) is NOT typed by the checker — it types the
        // `Bracket` and records the path's member fact — so a two-segment
        // base is read through that fact and the field's declared type,
        // the same way `lower_index_assign` writes it.
        let base_ty = self.ty_of(base_node);
        let untyped = base_ty == NO_TY || base_ty == TY_ERROR;
        let field_base = if untyped && self.kind(base_node) == NodeKind::NameExpr {
            let segs = self.path_segments(base_node);
            let [base_sym, _field] = segs.as_slice() else {
                return Err(LowerError::Unsupported("long projection".into()));
            };
            let MemberTarget::Field { head, index } = self.facts.member_of(base_node as u32) else {
                return Err(LowerError::Unresolved("index base".into()));
            };
            Some((*base_sym, head, index, self.field_ty(head, index)?))
        } else {
            None
        };
        let base_ty = match field_base {
            Some((_, _, _, fty)) => fty,
            None => base_ty,
        };
        let elem_ty = self.seq_elem_ty(base_ty).ok_or_else(|| {
            LowerError::Unsupported(
                "`a[i]` on a type with no `Index` impl the checker resolved and no \
                 `Array`/`Slice` element type"
                    .into(),
            )
        })?;
        let result_ty = if ty == NO_TY || ty == TY_ERROR {
            elem_ty
        } else {
            ty
        };
        // A named local is a PLACE, so element `i` gets ch01 R19b's split
        // seed naming it; anything else is a temporary with no place to
        // split (see `emit_index`).
        let parent = if field_base.is_none() && self.kind(base_node) == NodeKind::NameExpr {
            let segs = self.path_segments(base_node);
            match segs.as_slice() {
                [sym] => self
                    .lookup(*sym)
                    .map(|(root, t)| self.decl.places.intern(root, &[], t)),
                _ => None,
            }
        } else {
            None
        };
        let base = match field_base {
            Some((base_sym, _, index, fty)) => {
                let (root, rty) = self.resolve_name(base_sym)?;
                let b = self.read_root(root, rty, rty);
                let inst = self.emit(Op::Field, b.0, index, NO_OPERAND, fty);
                self.fresh(fty, inst)
            }
            None => self.lower_expr(base_node)?,
        };
        let idx_ty = self.index_ty()?;
        let idx = self.lenient_operand(idx_node, idx_ty)?;
        Ok(self.emit_index(base, idx, result_ty, parent))
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
        // sliced base must be a local or one field of one, not a temporary.
        if self.kind(*base_node) != NodeKind::NameExpr {
            return Err(LowerError::Unsupported("slice of a temporary".into()));
        }
        let segs = self.path_segments(*base_node);
        let (base_val, parent) = match segs.as_slice() {
            [base_sym] => {
                let (root, base_ty) = self.resolve_name(*base_sym)?;
                let v = self.read_root(root, base_ty, base_ty);
                let p = self.intern_place(root, &[], base_ty);
                (v, p)
            }
            // `self.data[0 ..< self.len]` — the shape every `Buffer`/`Vec`
            // body uses to hand out a window on its own storage.
            [base_sym, _field] => {
                let (root, outer_ty) = self.resolve_name(*base_sym)?;
                let MemberTarget::Field { index, .. } = self.facts.member_of(*base_node as u32)
                else {
                    return Err(LowerError::Unresolved("sliced field".into()));
                };
                let field_ty = self.ty_of(*base_node);
                let outer = self.read_root(root, outer_ty, outer_ty);
                let inst = self.emit(Op::Field, outer.0, index, NO_OPERAND, field_ty);
                let v = self.fresh(field_ty, inst);
                let p = self.intern_place(root, &[Seg::Field(index as u16)], field_ty);
                (v, p)
            }
            _ => return Err(LowerError::Unsupported("long projection".into())),
        };
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
        let binop = binop_for(op_tok, self.is_float_ty(elem_ty), self.relax)
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
                    // ch10 R42's `len` on an `Array`/`Slice`/`vector`: a
                    // MEMBER, not a method (the checker types `xs.len` as a
                    // `usize` with no call parens), lowered to the same
                    // `seq_len` intrinsic a `for` bound uses.
                    MemberTarget::LenBuiltin { .. } => {
                        let b = self.read_root(root, base_ty, base_ty);
                        Ok(self.emit_seq_len(b, ty))
                    }
                    MemberTarget::None => Err(LowerError::Unresolved("member".into())),
                    // F7's `a[i]` fact (member.rs::user_index) is set only
                    // on a `Bracket` node, never on a two-segment field
                    // path — this arm cannot be reached today.
                    MemberTarget::IndexImpl { .. } => Err(LowerError::Unresolved(
                        "index impl in a field projection".into(),
                    )),
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
            let fop = binop_for(*op, float, self.relax)
                .ok_or_else(|| LowerError::Unsupported("operator".into()))?;
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
            Op::Fneg(self.relax)
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
        // The operand's type: the checker's, or — for a ch03 R4/R6 call,
        // which `facts` leaves `TY_ERROR` — the one its receiver and type
        // argument decide (`x.wrap_as[u32]() as u64`).
        let xt = match self.ty_of(x) {
            t if t != TY_ERROR && t != NO_TY => t,
            _ => self
                .ch03_result_ty(x)
                .ok_or_else(|| LowerError::Unresolved("cast operand".into()))?,
        };
        if num_kind_of(self.prim_of(xt)).is_none() || num_kind_of(self.prim_of(ty)).is_none() {
            return Err(LowerError::Unsupported("non-numeric cast".into()));
        }
        let inst = self.emit(Op::ConvChecked, a.0, NO_OPERAND, NO_OPERAND, ty);
        Ok(self.fresh(ty, inst))
    }

    // -- ch03 Rules 4 and 6: explicit arithmetic and the lossy conversions --

    /// The `Ident` texts `node` owns directly, in order — [`node_own_idents`]
    /// without a `FileInput` and without interning (the ch03 family is
    /// matched against byte-string literals, so interning would be wasted).
    fn own_ident_texts(&self, node: usize) -> Vec<&'a [u8]> {
        let source = self.source;
        let (a, b) = self.tree.token_range(node);
        let covered: Vec<(u32, u32)> = self
            .tree
            .children(node)
            .map(|c| self.tree.token_range(c))
            .collect();
        let mut out = Vec::new();
        for t in a..b {
            if covered.iter().any(|&(x, y)| t >= x && t < y) {
                continue;
            }
            if self.tokens.kinds[t as usize] == TokenKind::Ident {
                out.push(self.tokens.text(t as usize, source));
            }
        }
        out
    }

    /// `node` as a ch03 Rule 4 / Rule 6 method call: the receiver-and-method
    /// path segments plus the optional explicit type argument. `None` for
    /// every other call — the shape test [`call_method_name`] runs in
    /// `prescan`, this is the same test from inside the walk.
    fn ch03_method_call(&self, node: usize) -> Option<Ch03Site<'a>> {
        if self.kind(node) != NodeKind::CallExpr {
            return None;
        }
        let callee = self.tree.children(node).next()?;
        let (path, targ) = match self.kind(callee) {
            NodeKind::NameExpr => (callee, None),
            NodeKind::Bracket => {
                let kids = self.kids(callee);
                let p = *kids.first()?;
                if self.kind(p) != NodeKind::NameExpr {
                    return None;
                }
                (p, kids.get(1).copied())
            }
            _ => return None,
        };
        let segs = self.own_ident_texts(path);
        if segs.len() < 2 || !is_ch03_prim_method(segs[segs.len() - 1]) {
            return None;
        }
        // Condition 2 of `is_ch03_prim_site`: a call the checker RESOLVED
        // is a real declaration's, whatever it is spelled.
        if !matches!(
            self.facts.callee_of(node as u32),
            FactCallee::Undecided | FactCallee::None
        ) {
            return None;
        }
        Some(Ch03Site { targ, segs })
    }

    /// The type a ch03 Rule 4 / Rule 6 method call produces: Rule 4's
    /// explicit arithmetic keeps the receiver's type, Rule 6's conversions
    /// take the explicit target type. Read from the receiver and the type
    /// argument rather than from `facts`, which has `TY_ERROR` here
    /// ([`CH03_ARITH_OPS`]).
    fn ch03_result_ty(&mut self, node: usize) -> Option<TyId> {
        let site = self.ch03_method_call(node)?;
        if site.segs.len() != 2 {
            return None;
        }
        let name = site.segs[1];
        if CH03_CONVS.iter().any(|(n, _)| *n == name) {
            let k = self.prim_type_arg(site.targ?)?;
            return self.prim_ty(k);
        }
        let sym = self.interner.intern(site.segs[0]);
        self.lookup(sym).map(|(_, t)| t)
    }

    /// ch03 Rule 4's `wrap_`/`sat_`/`unchecked_<op>` and Rule 6's
    /// `wrap_as`/`sat_as`/`trunc_as`, lowered to the FMIR mode field and the
    /// three conversion opcodes that ARE them (see [`CH03_ARITH_OPS`] for
    /// why lowering, not the checker, owns the spelling today).
    fn lower_ch03_prim_method(&mut self, node: usize) -> Result<ValId, LowerError> {
        let site = self
            .ch03_method_call(node)
            .ok_or_else(|| LowerError::Unresolved("explicit-arithmetic method".into()))?;
        if site.segs.len() != 2 {
            return Err(LowerError::Unsupported(
                "an explicit-arithmetic receiver that is a projection".into(),
            ));
        }
        let name = site.segs[1];
        let recv_sym = self.interner.intern(site.segs[0]);
        let (root, recv_ty) = self.resolve_name(recv_sym)?;
        let recv = self.read_root(root, recv_ty, recv_ty);
        let args: Vec<usize> = self.kids(node).into_iter().skip(1).collect();
        if args.iter().any(|&a| !is_expr(self.kind(a))) {
            return Err(LowerError::Unsupported(
                "a named or by-reference argument to an explicit-arithmetic method".into(),
            ));
        }
        if let Some((mode, tok, unary)) = ch03_arith_method(name) {
            if site.targ.is_some() {
                return Err(LowerError::Unsupported(
                    "a type argument on ch03 Rule 4 explicit arithmetic".into(),
                ));
            }
            // ch03 Rule 4: `unchecked_<op>` MUST NOT appear outside a
            // declaration carrying `@unsafe(invariant: "...")` (ch04 Rule
            // 10). The checker's rejection is I10's; until it speaks,
            // lowering does not build what the rule forbids — an
            // `unchecked_` op is wrapping plus a UB report (design §5.5),
            // and accepting it here would let the invariant-free form run.
            if mode == ArithMode::Unchecked && !self.unsafe_decl {
                return Err(LowerError::Unsupported(format!(
                    "`{}` outside a declaration carrying `@unsafe(invariant: ..)` \
                     (ch03 Rule 4, ch04 Rule 10)",
                    String::from_utf8_lossy(name)
                )));
            }
            // Rule 4 is the counterpart of Rule 2's TRAPPING operators,
            // which are the integer ones: a float has no wrapping form.
            if !self.is_int_ty(recv_ty) {
                return Err(LowerError::Unsupported(
                    "ch03 Rule 4 explicit arithmetic on a non-integer receiver".into(),
                ));
            }
            if unary {
                if !args.is_empty() {
                    return Err(LowerError::Unsupported(
                        "arguments to a unary explicit-arithmetic method".into(),
                    ));
                }
                let inst = self.emit(Op::Neg(mode), recv.0, NO_OPERAND, NO_OPERAND, recv_ty);
                return Ok(self.fresh(recv_ty, inst));
            }
            let op = arith_op_for(tok, mode)
                .ok_or_else(|| LowerError::Unsupported("explicit-arithmetic operator".into()))?;
            let [arg] = args.as_slice() else {
                return Err(LowerError::Unsupported(
                    "explicit-arithmetic method arity".into(),
                ));
            };
            let rhs = self.lenient_operand(*arg, recv_ty)?;
            let inst = self.emit(op, recv.0, rhs.0, NO_OPERAND, recv_ty);
            return Ok(self.fresh(recv_ty, inst));
        }
        let Some(&(_, conv)) = CH03_CONVS.iter().find(|(n, _)| *n == name) else {
            return Err(LowerError::Unresolved("explicit-arithmetic method".into()));
        };
        if !args.is_empty() {
            return Err(LowerError::Unsupported(
                "arguments to a ch03 Rule 6 conversion".into(),
            ));
        }
        let targ = site.targ.ok_or_else(|| {
            LowerError::Unsupported(
                "a ch03 Rule 6 conversion without its explicit target type".into(),
            )
        })?;
        let kind = self.prim_type_arg(targ).ok_or_else(|| {
            LowerError::Unsupported(
                "a ch03 Rule 6 conversion whose target type is not a primitive".into(),
            )
        })?;
        if num_kind_of(Some(kind)).is_none() || num_kind_of(self.prim_of(recv_ty)).is_none() {
            return Err(LowerError::Unsupported(
                "a non-numeric explicit conversion".into(),
            ));
        }
        let to = self.prim_ty(kind).ok_or_else(|| {
            LowerError::Unresolved(
                "the target type of an explicit conversion is not interned in this build".into(),
            )
        })?;
        let inst = self.emit(conv, recv.0, NO_OPERAND, NO_OPERAND, to);
        Ok(self.fresh(to, inst))
    }

    /// An operand inside a node range `prescan` held out of its `TY_ERROR`
    /// scan: the checker's type when it has one, else the two shapes a
    /// hard-coded stand-in can type itself from `hint` (a literal and a
    /// bound local). Anything else is reported, never defaulted.
    fn lenient_operand(&mut self, node: usize, hint: TyId) -> Result<ValId, LowerError> {
        let t = self.ty_of(node);
        if t != NO_TY && t != TY_ERROR {
            return self.lower_expr(node);
        }
        match self.kind(node) {
            NodeKind::Literal => self.lower_literal(node, hint),
            NodeKind::NameExpr => self.lower_path(node, hint),
            k => Err(LowerError::Unresolved(kind_name(k).into())),
        }
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
        // The §5.8 stand-in: any method spelled one of these names is the
        // matching writer, whatever its owner — `write_line` is F1's;
        // `write_uint` is F7's (needed by `str-index-is-bytes-run-ok`,
        // which prints a length with no trailing newline, so it cannot
        // reuse `write_line`'s intrinsic). Both wait on a real Fors
        // `io.Stdout` body over `@fd_write`, not F7's to build.
        //
        // F7's `Str` primitives are scoped tighter: only a method of
        // `Str`'s OWN inherent impl (`std/mem/text.fors`, the one module
        // ch10 R2 lets define it) is the byte reader. A user method that
        // merely shares the spelling (F7 verification: `impl B { fn
        // str_byte_len(..) }`) keeps its own body, as it must.
        let owner_is_str = self
            .defs
            .get(def)
            .map(|r| r.parent)
            .filter(|p| *p != fors_fir::NO_DEF)
            .map(|p| self.fir.sigs.self_ty(p))
            .filter(|t| *t != NO_TY)
            .and_then(|t| self.prim_of(t))
            == Some(PrimKind::Str);
        let intrinsic_name = match self.interner.resolve(method) {
            b"write_line" => Some("stdout_write_line"),
            b"write_uint" => Some("stdout_write_uint"),
            // F7's §5.8 byte-length/byte-at/byte-slice stand-ins for `Str`
            // (see `std/mem/text.fors`'s `Str.len`/`at`/`slice`).
            b"str_byte_len" if owner_is_str => Some("str_byte_len"),
            b"str_byte_at" if owner_is_str => Some("str_byte_at"),
            b"str_byte_slice" if owner_is_str => Some("str_byte_slice"),
            _ => None,
        };
        if let Some(name) = intrinsic_name {
            let sym = self.interner.intern(name.as_bytes());
            if !self.intrinsics.iter().any(|(id, _)| *id == sym.0) {
                self.intrinsics.push((sym.0, name.into()));
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

/// ch09 Rule 1's fifteen primitive spellings, by name. The one place
/// `fors-lower` maps a type NAME to a [`PrimKind`]: a type argument the
/// checker did not type (ch03 Rule 6's `wrap_as[u8]`, whose whole call it
/// leaves `TY_ERROR`). `Str`/`rawptr` are listed for completeness even
/// though no conversion names them — a caller that gets one still has to
/// find the conversion legal.
fn prim_kind_named(name: &[u8]) -> Option<PrimKind> {
    Some(match name {
        b"i8" => PrimKind::I8,
        b"i16" => PrimKind::I16,
        b"i32" => PrimKind::I32,
        b"i64" => PrimKind::I64,
        b"isize" => PrimKind::Isize,
        b"u8" => PrimKind::U8,
        b"u16" => PrimKind::U16,
        b"u32" => PrimKind::U32,
        b"u64" => PrimKind::U64,
        b"usize" => PrimKind::Usize,
        b"f32" => PrimKind::F32,
        b"f64" => PrimKind::F64,
        b"bool" => PrimKind::Bool,
        b"Str" => PrimKind::Str,
        b"rawptr" => PrimKind::RawPtr,
        _ => return None,
    })
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
    // ch10 R26: `Str` is ALWAYS valid UTF-8. The lexer validates only the
    // raw source bytes (`fors-syntax`'s own scan over the literal's own
    // text); `\xHH` decodes to an arbitrary byte and is never itself
    // checked, so a literal like `"\xc0\x80"` would otherwise materialise
    // an invalid-UTF-8 `Str` straight from a `const_str` value. Validate
    // the fully-decoded bytes once, here, after every escape (including
    // `\xHH`) has been applied.
    if let Err(e) = std::str::from_utf8(&out) {
        return Err(LowerError::InvalidUtf8Literal(e.to_string()));
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

/// Maps one gap operator to its FMIR op. Integer operators are ch03 Rule
/// 2's TRAPPING mode (Rule 4's explicit modes are method spellings, not
/// operators: see [`ch03_arith_method`]); float operators carry `relax`,
/// which is `Relax::NONE` outside an `@fastmath` block (design §5.6(6)).
/// One INTEGER operator in an explicit ch03 Rule 4 mode. Separate from
/// [`binop_for`] because Rule 4's forms are method spellings, never
/// operators, and because `&`/`|`/`^` have no mode (they cannot overflow).
fn arith_op_for(op: TokenKind, mode: ArithMode) -> Option<Op> {
    Some(match op {
        TokenKind::Plus => Op::Add(mode),
        TokenKind::Minus => Op::Sub(mode),
        TokenKind::Star => Op::Mul(mode),
        TokenKind::Slash => Op::Div(mode),
        TokenKind::Percent => Op::Rem(mode),
        TokenKind::Shl => Op::Shl(mode),
        TokenKind::Shr => Op::Shr(mode),
        _ => return None,
    })
}

fn binop_for(op: TokenKind, float: bool, relax: fors_fmir::op::Relax) -> Option<Op> {
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
        (TokenKind::Plus, true) => Some(Op::Fadd(relax)),
        (TokenKind::Minus, true) => Some(Op::Fsub(relax)),
        (TokenKind::Star, true) => Some(Op::Fmul(relax)),
        (TokenKind::Slash, true) => Some(Op::Fdiv(relax)),
        (TokenKind::Percent, true) => Some(Op::Frem(relax)),
        _ => None,
    }
}

/// One `@fastmath` flag name to its [`fors_fmir::op::Relax`] bit (design
/// §5.6(6)'s `{reassoc, contract, nsz, finite, recip}`). An unlisted flag
/// is a named diagnostic: a mask bit silently dropped is a permission the
/// backend never gets, and a flag this compiler does not know may be one
/// that changes results.
fn relax_flag(name: &[u8]) -> Option<u8> {
    Some(match name {
        b"reassoc" => fors_fmir::op::Relax::REASSOC,
        b"contract" => fors_fmir::op::Relax::CONTRACT,
        b"nsz" => fors_fmir::op::Relax::NSZ,
        b"finite" => fors_fmir::op::Relax::FINITE,
        b"recip" => fors_fmir::op::Relax::RECIP,
        _ => return None,
    })
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

#[cfg(test)]
mod utf8_literal_tests {
    //! F7 (ch10 R26): `unescape_str` decodes `\xHH` and MUST then validate
    //! the whole result as UTF-8 — the lexer validated only the raw source
    //! bytes of the literal, never what a `\xHH` escape decodes to.

    use super::{LowerError, unescape_str};

    fn lit(inner: &[u8]) -> Vec<u8> {
        let mut v = vec![b'"'];
        v.extend_from_slice(inner);
        v.push(b'"');
        v
    }

    #[test]
    fn two_byte_sequence_accepted() {
        // U+00E9 (é), the exact sequence `str-slice-non-boundary-raises-run-
        // ok.fors` writes as `\xc3\xa9`.
        assert_eq!(
            unescape_str(&lit(b"a\\xc3\\xa9b")).unwrap(),
            "aéb".as_bytes()
        );
    }

    #[test]
    fn three_byte_sequence_accepted() {
        // U+4E2D (中) = E4 B8 AD.
        assert_eq!(
            unescape_str(&lit(b"\\xe4\\xb8\\xad")).unwrap(),
            "中".as_bytes()
        );
    }

    #[test]
    fn four_byte_sequence_accepted() {
        // U+1F600 (😀) = F0 9F 98 80.
        assert_eq!(
            unescape_str(&lit(b"\\xf0\\x9f\\x98\\x80")).unwrap(),
            "😀".as_bytes()
        );
    }

    #[test]
    fn lone_continuation_byte_rejected() {
        // `0x80` on its own has no lead byte.
        assert!(matches!(
            unescape_str(&lit(b"\\x80abc")),
            Err(LowerError::InvalidUtf8Literal(_))
        ));
    }

    #[test]
    fn incomplete_two_byte_sequence_rejected() {
        // `0xc3` is a two-byte lead with nothing to continue it.
        assert!(matches!(
            unescape_str(&lit(b"a\\xc3")),
            Err(LowerError::InvalidUtf8Literal(_))
        ));
    }

    #[test]
    fn overlong_encoding_rejected() {
        // `\xc0\x80` is an overlong (4-byte-too-many) encoding of NUL.
        assert!(matches!(
            unescape_str(&lit(b"\\xc0\\x80")),
            Err(LowerError::InvalidUtf8Literal(_))
        ));
    }

    #[test]
    fn surrogate_half_rejected() {
        // `\xed\xa0\x80` encodes U+D800, a surrogate half: never a scalar
        // value.
        assert!(matches!(
            unescape_str(&lit(b"\\xed\\xa0\\x80")),
            Err(LowerError::InvalidUtf8Literal(_))
        ));
    }

    #[test]
    fn past_max_scalar_value_rejected() {
        // `\xf4\x90\x80\x80` encodes U+110000, past U+10FFFF.
        assert!(matches!(
            unescape_str(&lit(b"\\xf4\\x90\\x80\\x80")),
            Err(LowerError::InvalidUtf8Literal(_))
        ));
    }
}
