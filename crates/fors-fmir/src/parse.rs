//! The inverse of `dump.rs`, over the exact same grammar (see that module's
//! docs for the grammar and its documented scope: constants are not
//! parseable, nothing else the negative corpus or a representative positive
//! declaration needs is excluded).
//!
//! Two passes over `text.lines()`, both top to bottom: pass A assigns each
//! `block <name>` line's `BlockId` (declaration order = id order, matching
//! `dump.rs`'s own `bb<BlockId>` naming), so a forward branch (`do br
//! bb_later`) resolves even though `bb_later`'s own `block` line has not been
//! reached yet; pass B builds every pool, pushing instructions straight into
//! `InstPool` as each line is read (never into a staging buffer) — a
//! block's regular range is `first_inst..first_inst+inst_len`, and the ONE
//! extra row pushed at `first_inst+inst_len` (the line that turns out to be
//! last in the block) becomes `term` as well as staying physically present
//! in `InstPool`, exactly matching `block.rs`'s module docs on how "two
//! terminators" becomes representable at all: nothing here ever *removes* a
//! row from `InstPool` once pushed. A `%name` value must already be defined
//! when it is used (no forward references to values — a corpus file is
//! always written top to bottom).

use std::collections::HashMap;

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::TyId;

use crate::alias::AliasSeed;
use crate::block::BlockRow;
use crate::decl::DeclFmir;
use crate::flags::{CT_UNSPECIFIED, SECRET_UNSPECIFIED, ValFlags};
use crate::ids::{BlockId, BrandId, ScopeId, ValId};
use crate::inst::{CallRow, Callee, InstRow, SwitchArm, SwitchRow};
use crate::op::{ArithMode, CmpPred, Op, Policy, TrapKind};
use crate::place::Seg;
use crate::region::{CaptureRow, RegionKind, RegionRow};
use crate::value::{ValDef, ValRow};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}
impl std::error::Error for ParseError {}

fn err(line: usize, message: impl Into<String>) -> ParseError {
    ParseError {
        line,
        message: message.into(),
    }
}

fn strip_comment(line: &str) -> &str {
    match line.find("//") {
        Some(i) => &line[..i],
        None => line,
    }
}

struct Toks<'a> {
    line_no: usize,
    toks: Vec<&'a str>,
    pos: usize,
}

impl<'a> Toks<'a> {
    fn next(&mut self) -> Result<&'a str, ParseError> {
        let t = *self
            .toks
            .get(self.pos)
            .ok_or_else(|| err(self.line_no, "unexpected end of line"))?;
        self.pos += 1;
        Ok(t)
    }

    fn peek(&self) -> Option<&'a str> {
        self.toks.get(self.pos).copied()
    }

    fn u32(&mut self) -> Result<u32, ParseError> {
        let t = self.next()?;
        t.parse::<u32>()
            .map_err(|_| err(self.line_no, format!("expected a u32, got `{t}`")))
    }

    fn u16(&mut self) -> Result<u16, ParseError> {
        let t = self.next()?;
        t.parse::<u16>()
            .map_err(|_| err(self.line_no, format!("expected a u16, got `{t}`")))
    }
}

fn parse_conv(s: &str, line_no: usize) -> Result<Conv, ParseError> {
    Ok(match s {
        "let" => Conv::Let,
        "inout" => Conv::Inout,
        "sink" => Conv::Sink,
        "set" => Conv::Set,
        other => return Err(err(line_no, format!("unknown convention `{other}`"))),
    })
}

fn lookup_val(
    name: &str,
    vals: &HashMap<String, ValId>,
    line_no: usize,
) -> Result<ValId, ParseError> {
    vals.get(name)
        .copied()
        .ok_or_else(|| err(line_no, format!("unknown value `{name}`")))
}

fn lookup_block(
    name: &str,
    blocks: &HashMap<String, u32>,
    line_no: usize,
) -> Result<BlockId, ParseError> {
    blocks
        .get(name)
        .map(|v| BlockId(*v))
        .ok_or_else(|| err(line_no, format!("unknown block `{name}`")))
}

/// `secret`/`nosecret`/`?` and `ct=<u16>`/`ct=?`, in that order, at the tail
/// of a `val` line — see `dump.rs`'s grammar.
fn parse_secret_and_ct(t: &mut Toks, line_no: usize) -> Result<(ValFlags, u16), ParseError> {
    let secret_tok = t.next()?;
    let flags = match secret_tok {
        "secret" => ValFlags::new(true),
        "nosecret" => ValFlags::new(false),
        "?" => ValFlags(SECRET_UNSPECIFIED),
        other => {
            return Err(err(
                line_no,
                format!("expected `secret`/`nosecret`/`?`, got `{other}`"),
            ));
        }
    };
    let ct_tok = t.next()?;
    let ct = if ct_tok == "ct=?" {
        CT_UNSPECIFIED
    } else {
        ct_tok
            .strip_prefix("ct=")
            .ok_or_else(|| {
                err(
                    line_no,
                    format!("expected `ct=<u16>` or `ct=?`, got `{ct_tok}`"),
                )
            })?
            .parse::<u16>()
            .map_err(|_| err(line_no, format!("bad ct value in `{ct_tok}`")))?
    };
    Ok((flags, ct))
}

/// An optional trailing `seed <spec>` clause on a `val` line for a
/// memory-producing op. Absent entirely (not even the keyword) means
/// `AliasSeed::None` — exactly the condition `alias_seed_present_on_every_
/// memory_op`'s negative case constructs. `own<root>`/`split<root>,<side>`
/// intern a place with an empty projection path for that bare `root` number
/// (this format has no place-path syntax — see `dump.rs`'s scope note), so
/// `dump.rs::place_root`'s later `d.places.row(p)` always finds a real row
/// instead of panicking on a `PlaceId` nothing ever interned.
fn parse_optional_seed(
    t: &mut Toks,
    places: &mut crate::place::PlacePool,
    line_no: usize,
) -> Result<AliasSeed, ParseError> {
    if t.peek() != Some("seed") {
        return Ok(AliasSeed::None);
    }
    t.next()?;
    let spec = t.next()?;
    if let Some(rest) = spec.strip_prefix("conv-") {
        return Ok(AliasSeed::Conv(parse_conv(rest, line_no)?));
    }
    if let Some(rest) = spec.strip_prefix("own") {
        let root: u32 = rest
            .parse()
            .map_err(|_| err(line_no, format!("bad place root in `{spec}`")))?;
        return Ok(AliasSeed::Own(places.intern(root, &[], TyId(0))));
    }
    if let Some(rest) = spec.strip_prefix("arena") {
        let id: u32 = rest
            .parse()
            .map_err(|_| err(line_no, format!("bad brand id in `{spec}`")))?;
        return Ok(AliasSeed::Arena(BrandId(id)));
    }
    if let Some(rest) = spec.strip_prefix("split") {
        let (root, side) = rest.split_once(',').ok_or_else(|| {
            err(
                line_no,
                format!("expected `split<root>,<side>`, got `{spec}`"),
            )
        })?;
        let root: u32 = root
            .parse()
            .map_err(|_| err(line_no, format!("bad place root in `{spec}`")))?;
        let side: u8 = side
            .parse()
            .map_err(|_| err(line_no, format!("bad side in `{spec}`")))?;
        let parent = places.intern(root, &[], TyId(0));
        return Ok(AliasSeed::Split { parent, side });
    }
    Err(err(line_no, format!("unknown seed spec `{spec}`")))
}

fn parse_mnemonic(head: &str, line_no: usize) -> Result<Op, ParseError> {
    if let Some(base) = head.strip_prefix("tile.") {
        let _ = base;
        return Ok(Op::TileOp);
    }
    let (base, mode_tag) = head
        .split_once(':')
        .map_or((head, None), |(b, m)| (b, Some(m)));
    let arith = |m: ArithMode| Ok(m);
    let mode = match mode_tag {
        None | Some("trap") => arith(ArithMode::Trap)?,
        Some("wrap") => arith(ArithMode::Wrap)?,
        Some("sat") => arith(ArithMode::Sat)?,
        Some("unchecked") => arith(ArithMode::Unchecked)?,
        Some(other) => return Err(err(line_no, format!("unknown arithmetic mode `{other}`"))),
    };
    Ok(match base {
        "add" => Op::Add(mode),
        "sub" => Op::Sub(mode),
        "mul" => Op::Mul(mode),
        "div" => Op::Div(mode),
        "rem" => Op::Rem(mode),
        "shl" => Op::Shl(mode),
        "shr" => Op::Shr(mode),
        "neg" => Op::Neg(mode),
        "index" => Op::Index,
        "slice_range" => Op::SliceRange,
        "alloc" => Op::Alloc,
        "free" => Op::Free,
        "arena_alloc" => Op::ArenaAlloc,
        "arena_deref" => Op::ArenaDeref,
        "arena_reset" => Op::ArenaReset,
        "check_pre" => Op::CheckPre(Policy::Runtime),
        "check_post" => Op::CheckPost(Policy::Runtime),
        "check_inv" => Op::CheckInv(Policy::Runtime),
        "intrinsic" => Op::Intrinsic,
        "declassify" => Op::Declassify,
        "erase_to_dyn" => Op::EraseToDyn,
        "region_enter" => Op::RegionEnter,
        "region_exit" => Op::RegionExit,
        "spawn" => Op::Spawn,
        "sync" => Op::Sync,
        "br" => Op::Br,
        "cond_br" => Op::CondBr,
        "switch_discr" => Op::SwitchDiscr,
        "try_br" => Op::TryBr,
        "ret" => Op::Ret,
        "raise" => Op::Raise,
        "trap" => Op::Trap,
        "unreachable" => Op::Unreachable,
        other => {
            return Err(err(
                line_no,
                format!("unsupported mnemonic `{other}` (see dump.rs's scope note)"),
            ));
        }
    })
}

/// `check_pre policy=off` etc: an optional trailing `policy=off` token after
/// a contract check's condition operand, consumed separately from
/// `parse_operands` since it changes the `Op` itself (`CheckPre(Policy)`),
/// not `a`/`b`/`c`.
fn apply_trailing_policy(op: Op, t: &mut Toks) -> Op {
    if t.peek() != Some("policy=off") {
        return op;
    }
    let _ = t.next();
    match op {
        Op::CheckPre(_) => Op::CheckPre(Policy::Off),
        Op::CheckPost(_) => Op::CheckPost(Policy::Off),
        Op::CheckInv(_) => Op::CheckInv(Policy::Off),
        other => other,
    }
}

/// Operand-parsing context. No `PlacePool` handle: this format does not
/// parse place-taking ops (`move_from`/`copy_from`/`borrow*`/`init`) at all
/// — see `dump.rs`'s module docs for the scope this mirrors — so nothing
/// here ever needs to intern a place.
struct Ctx<'a> {
    vals: &'a HashMap<String, ValId>,
    blocks: &'a HashMap<String, u32>,
    insts: &'a mut crate::inst::InstPool,
}

/// Parses `op`'s operands per `op.rs`'s documented `a`/`b`/`c` convention,
/// pushing to any side table (`calls`, `switches`, `switch_arms`) the op
/// needs along the way.
fn parse_operands(
    op: Op,
    t: &mut Toks,
    ctx: &mut Ctx,
    line_no: usize,
) -> Result<(u32, u32, u32), ParseError> {
    let val = |t: &mut Toks, ctx: &Ctx| -> Result<u32, ParseError> {
        let tok = t.next()?;
        let name = tok
            .strip_prefix('%')
            .ok_or_else(|| err(line_no, format!("expected a `%value`, got `{tok}`")))?;
        Ok(lookup_val(&format!("%{name}"), ctx.vals, line_no)?.0)
    };
    let bb = |t: &mut Toks, ctx: &Ctx| -> Result<u32, ParseError> {
        let tok = t.next()?;
        Ok(lookup_block(tok, ctx.blocks, line_no)?.0)
    };
    match op {
        Op::Add(_)
        | Op::Sub(_)
        | Op::Mul(_)
        | Op::Div(_)
        | Op::Rem(_)
        | Op::Shl(_)
        | Op::Shr(_) => {
            let a = val(t, ctx)?;
            let b = val(t, ctx)?;
            Ok((a, b, crate::op::NO_OPERAND))
        }
        Op::Neg(_)
        | Op::ArenaDeref
        | Op::ArenaReset
        | Op::Free
        | Op::Declassify
        | Op::EraseToDyn => {
            let a = val(t, ctx)?;
            Ok((a, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::Index => {
            let a = val(t, ctx)?;
            let b = val(t, ctx)?;
            Ok((a, b, crate::op::NO_OPERAND))
        }
        Op::SliceRange => {
            let a = val(t, ctx)?;
            let b = val(t, ctx)?;
            let c = val(t, ctx)?;
            Ok((a, b, c))
        }
        Op::Alloc | Op::ArenaAlloc => {
            let a = val(t, ctx)?;
            let b = val(t, ctx)?;
            Ok((a, b, crate::op::NO_OPERAND))
        }
        Op::CheckPre(_) | Op::CheckPost(_) | Op::CheckInv(_) => {
            let a = val(t, ctx)?;
            Ok((a, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::Intrinsic => {
            let sym_tok = t.next()?;
            let sym = sym_tok
                .strip_prefix('@')
                .ok_or_else(|| err(line_no, format!("expected `@<symbol-id>`, got `{sym_tok}`")))?
                .parse::<u32>()
                .map_err(|_| err(line_no, "bad intrinsic symbol id"))?;
            let mut args = Vec::new();
            let mut convs = Vec::new();
            while let Some(tok) = t.peek() {
                if tok == "seed" || tok.starts_with("ty") {
                    break;
                }
                args.push(ValId(val(t, ctx)?));
                convs.push(Conv::Let);
            }
            let range = ctx.insts.push_operands(&args, &convs);
            let call_idx = ctx.insts.push_call(CallRow {
                callee: Callee::Intrinsic(fors_index::interner::Symbol(sym)),
                args: range,
            });
            Ok((call_idx, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::Br => {
            let a = bb(t, ctx)?;
            Ok((a, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::CondBr => {
            let a = val(t, ctx)?;
            let b = bb(t, ctx)?;
            let c = bb(t, ctx)?;
            Ok((a, b, c))
        }
        Op::TryBr => {
            let call_tok = t.next()?;
            let call_id: u32 = call_tok
                .strip_prefix('%')
                .and_then(|s| s.strip_prefix("inst"))
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| err(line_no, format!("expected `%inst<id>`, got `{call_tok}`")))?;
            let ok = bb(t, ctx)?;
            let errb = bb(t, ctx)?;
            Ok((call_id, ok, errb))
        }
        Op::SwitchDiscr => {
            let discr = ValId(val(t, ctx)?);
            let default = BlockId(bb(t, ctx)?);
            let arms_start = ctx.insts.switch_arms.len() as u32;
            while let Some(tok) = t.peek() {
                if tok.starts_with("ty") {
                    break;
                }
                let tok = t.next()?;
                let (value, target) = tok.split_once(':').ok_or_else(|| {
                    err(line_no, format!("expected `<i64>:bb<name>`, got `{tok}`"))
                })?;
                let value: i64 = value
                    .parse()
                    .map_err(|_| err(line_no, format!("bad case value in `{tok}`")))?;
                let target = lookup_block(target, ctx.blocks, line_no)?;
                ctx.insts.switch_arms.push(SwitchArm { value, target });
            }
            let arms = arms_start..(ctx.insts.switch_arms.len() as u32);
            let idx = ctx.insts.push_switch(SwitchRow {
                discr,
                default,
                arms,
            });
            Ok((idx, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::Ret | Op::Raise => {
            if let Some(tok) = t.peek()
                && tok.starts_with('%')
            {
                return Ok((val(t, ctx)?, crate::op::NO_OPERAND, crate::op::NO_OPERAND));
            }
            Ok((
                crate::op::NO_OPERAND,
                crate::op::NO_OPERAND,
                crate::op::NO_OPERAND,
            ))
        }
        Op::Trap => {
            let tok = t.next()?;
            let kind_str = tok
                .strip_prefix("kind=")
                .ok_or_else(|| err(line_no, format!("expected `kind=<trapkind>`, got `{tok}`")))?;
            let kind = TrapKind::parse_name(kind_str)
                .ok_or_else(|| err(line_no, format!("unknown trap kind `{kind_str}`")))?;
            Ok((kind as u32, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::Unreachable => Ok((
            crate::op::NO_OPERAND,
            crate::op::NO_OPERAND,
            crate::op::NO_OPERAND,
        )),
        Op::Spawn | Op::Sync | Op::RegionEnter | Op::RegionExit => {
            let tok = t.next()?;
            let id: u32 = tok
                .strip_prefix('r')
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| err(line_no, format!("expected `r<id>`, got `{tok}`")))?;
            Ok((id, crate::op::NO_OPERAND, crate::op::NO_OPERAND))
        }
        Op::TileOp => {
            // `tile.*`'s operand shape is undefined before M6 (design §1.2);
            // this crate exists only to be rejected by `verify()`, so any
            // remaining tokens up to `ty`/end of line are simply discarded.
            Ok((
                crate::op::NO_OPERAND,
                crate::op::NO_OPERAND,
                crate::op::NO_OPERAND,
            ))
        }
        other => Err(err(
            line_no,
            format!("`{other:?}` has no parser (see dump.rs's scope note)"),
        )),
    }
}

/// Parses `text` into a `DeclFmir`. `verify()` is a separate step by design
/// — the negative corpus's whole point is FMIR that parses cleanly but
/// fails `verify()`.
pub fn parse(text: &str) -> Result<DeclFmir, ParseError> {
    // Pass A: block name -> id, in declaration order.
    let mut block_ids: HashMap<String, u32> = HashMap::new();
    for (i, raw) in text.lines().enumerate() {
        let line = strip_comment(raw);
        let mut it = line.split_whitespace();
        if it.next() == Some("block") {
            let name = it
                .next()
                .ok_or_else(|| err(i + 1, "`block` needs a name"))?;
            if block_ids
                .insert(name.to_string(), block_ids.len() as u32)
                .is_some()
            {
                return Err(err(i + 1, format!("block `{name}` declared twice")));
            }
        }
    }

    let mut decl_key = DeclKeyId(0);
    let mut sig = FnSigId(0);
    let mut is_unsafe_invariant = false;
    let mut saw_decl_line = false;

    let mut scopes = crate::scope::ScopePool::new();
    let root_scope = scopes.push(crate::scope::ScopeRow::root(BrandId::NONE));
    debug_assert_eq!(root_scope, ScopeId(0));

    let mut vals = crate::value::ValPool::new();
    let mut insts = crate::inst::InstPool::new();
    let mut places = crate::place::PlacePool::new();
    let mut regions = crate::region::RegionPool::new();
    let mut val_names: HashMap<String, ValId> = HashMap::new();
    let mut blocks = crate::block::BlockPool::new();

    let mut current_block: Option<(String, u32)> = None; // (name, first_inst)

    for (i, raw) in text.lines().enumerate() {
        let line_no = i + 1;
        let line = strip_comment(raw);
        let toks: Vec<&str> = line.split_whitespace().collect();
        if toks.is_empty() {
            continue;
        }
        let mut t = Toks {
            line_no,
            toks,
            pos: 0,
        };
        match t.next()? {
            "decl" => {
                if saw_decl_line {
                    return Err(err(line_no, "duplicate `decl` line"));
                }
                saw_decl_line = true;
                decl_key = DeclKeyId(t.u32()?);
                if t.next()? != "sig" {
                    return Err(err(line_no, "expected `sig` after the decl id"));
                }
                sig = FnSigId(t.u32()?);
                if t.peek() == Some("unsafe") {
                    is_unsafe_invariant = true;
                }
            }
            "region" => {
                let _name = t.next()?;
                let kind = match t.next()? {
                    "spawn" => RegionKind::Spawn,
                    "parallel" => RegionKind::Parallel,
                    "with-arena" => RegionKind::WithArena,
                    other => return Err(err(line_no, format!("unknown region kind `{other}`"))),
                };
                let captures = if t.peek() == Some("captures") {
                    t.next()?;
                    let start = regions.captures.len() as u32;
                    while let Some(tok) = t.peek() {
                        t.next()?;
                        let (name, conv) = tok.split_once(':').ok_or_else(|| {
                            err(line_no, format!("expected `%name:conv`, got `{tok}`"))
                        })?;
                        let value = lookup_val(name, &val_names, line_no)?;
                        let conv = parse_conv(conv, line_no)?;
                        regions.captures.push(CaptureRow { value, conv });
                    }
                    start..(regions.captures.len() as u32)
                } else {
                    RegionRow::ABSENT_CAPTURES
                };
                regions.push(RegionRow {
                    kind,
                    captures,
                    brand: BrandId::NONE,
                });
            }
            "block" => {
                if let Some((name, first_inst)) = current_block.take() {
                    finish_block(&name, first_inst, &insts, &mut blocks, line_no)?;
                }
                let name = t.next()?.to_string();
                current_block = Some((name, insts.len() as u32));
            }
            "val" => {
                let name = t.next()?.to_string();
                if t.next()? != "=" {
                    return Err(err(line_no, "expected `=` after a value name"));
                }
                let head = t.next()?;
                if head == "param" {
                    let ordinal = t.u16()?;
                    let ty = TyId(parse_ty(&mut t, line_no)?);
                    let (flags, ct) = parse_secret_and_ct(&mut t, line_no)?;
                    let row = ValRow {
                        ty,
                        flags,
                        ct,
                        def: ValDef::Param(ordinal).encode(),
                    };
                    let id = vals.push(row);
                    val_names.insert(name, id);
                } else {
                    // Only the instruction-defining form needs a block to live
                    // in; `val %x = param N` is declaration-level (it defines
                    // no instruction), so it is legal before the first `block`
                    // line — which is where `dump` puts every parameter, since
                    // a `%name` must be introduced above its first use.
                    if current_block.is_none() {
                        return Err(err(line_no, "`val = <inst>` outside any `block`"));
                    }
                    let mut op = parse_mnemonic(head, line_no)?;
                    let mut ctx = Ctx {
                        vals: &val_names,
                        blocks: &block_ids,
                        insts: &mut insts,
                    };
                    let (a, b, c) = parse_operands(op, &mut t, &mut ctx, line_no)?;
                    op = apply_trailing_policy(op, &mut t);
                    let ty = TyId(parse_ty(&mut t, line_no)?);
                    let (flags, ct) = parse_secret_and_ct(&mut t, line_no)?;
                    let seed = parse_optional_seed(&mut t, &mut places, line_no)?;
                    let inst_id = insts.push(
                        InstRow {
                            op,
                            a,
                            b,
                            c,
                            ty,
                            site: crate::ids::SiteId(0),
                        },
                        seed,
                    );
                    let row = ValRow {
                        ty,
                        flags,
                        ct,
                        def: ValDef::Inst(inst_id).encode(),
                    };
                    let id = vals.push(row);
                    val_names.insert(name, id);
                }
            }
            "do" => {
                if current_block.is_none() {
                    return Err(err(line_no, "`do <inst>` outside any `block`"));
                }
                let head = t.next()?;
                let mut op = parse_mnemonic(head, line_no)?;
                let mut ctx = Ctx {
                    vals: &val_names,
                    blocks: &block_ids,
                    insts: &mut insts,
                };
                let (a, b, c) = parse_operands(op, &mut t, &mut ctx, line_no)?;
                op = apply_trailing_policy(op, &mut t);
                insts.push(
                    InstRow {
                        op,
                        a,
                        b,
                        c,
                        ty: fors_fir::ty::TY_UNIT,
                        site: crate::ids::SiteId(0),
                    },
                    AliasSeed::None,
                );
            }
            other => return Err(err(line_no, format!("unknown line kind `{other}`"))),
        }
    }
    if let Some((name, first_inst)) = current_block.take() {
        finish_block(&name, first_inst, &insts, &mut blocks, text.lines().count())?;
    }
    if !saw_decl_line {
        return Err(err(0, "missing `decl <id> sig <id>` header line"));
    }
    if blocks.is_empty() {
        return Err(err(0, "declaration has no blocks"));
    }

    Ok(DeclFmir {
        decl: decl_key,
        sig,
        vals,
        blocks,
        insts,
        scopes,
        places,
        regions,
        sites: crate::site::SitePool::new(),
        consts: crate::constpool::ConstPool::new(),
        obligations: crate::scope::PlaceListPool::new(),
        scoped_sources: crate::scope::PlaceListPool::new(),
        defers: crate::scope::DeferPool::new(),
        entry: BlockId(0),
        is_unsafe_invariant,
        fingerprint: 0,
    })
}

fn parse_ty(t: &mut Toks, line_no: usize) -> Result<u32, ParseError> {
    if t.next()? != "ty" {
        return Err(err(line_no, "expected `ty <u32>`"));
    }
    t.u32()
}

/// Turns `[block_first_inst, insts.len())` into a `BlockRow`: everything
/// except the last pushed row is the block's regular range, and the last
/// pushed row (still physically in `InstPool` — never removed) is `term`.
/// See this module's and `block.rs`'s docs for why a block that instead has
/// a stray terminator-class op *inside* its regular range (constructible by
/// simply not making that op the file's last line in the block) is exactly
/// `verify_rejects_two_terminators`'s target.
fn finish_block(
    name: &str,
    first_inst: u32,
    insts: &crate::inst::InstPool,
    blocks: &mut crate::block::BlockPool,
    line_no: usize,
) -> Result<(), ParseError> {
    let total = insts.len() as u32;
    if total <= first_inst {
        return Err(err(
            line_no,
            format!("block `{name}` has no instructions (needs at least a terminator)"),
        ));
    }
    let term = insts.row(crate::ids::InstId(total - 1));
    let inst_len = total - first_inst - 1;
    blocks.push(BlockRow {
        first_inst,
        inst_len,
        term,
        scope: ScopeId(0),
    });
    Ok(())
}

#[allow(dead_code)]
fn unused_type_markers(_: Seg, _: CmpPred) {}
