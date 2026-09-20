//! Canonical byte encoding + `fmir_hash` (task item 3): "the hash must be
//! invariant under basic-block renumbering and must change on any operand
//! edit."
//!
//! Two distinct entry points, deliberately:
//!
//! - [`to_bytes`]/[`from_bytes`]: a faithful, order-preserving serialization
//!   of every pool. `encode_decode_roundtrip` (the 10k-declaration gate test)
//!   uses these — round-tripping is checked by re-encoding the decoded
//!   result and comparing bytes (`DeclFmir` has no derived `PartialEq`: its
//!   pools are compared by what they *mean*, which is exactly what a byte
//!   encoding already gives for free), not by asserting the two `DeclFmir`
//!   values are struct-identical.
//! - [`fmir_hash`]: hashes a **canonicalized** encoding — blocks visited in a
//!   deterministic order from `entry` and renumbered to that order before
//!   anything is hashed — over [`fors_index::fingerprint::hash_bytes`], this
//!   workspace's one hash primitive (see `decl.rs`'s `fingerprint` field doc
//!   for why that is not literal BLAKE3).

use std::ops::Range;

use fors_fir::defpath::DeclKeyId;
use fors_fir::sig::{Conv, FnSigId};
use fors_fir::ty::TyId;
use fors_index::interner::Symbol;

use crate::alias::AliasSeed;
use crate::block::BlockRow;
use crate::constpool::ConstValue;
use crate::decl::DeclFmir;
use crate::flags::ValFlags;
use crate::ids::{BlockId, BrandId, PlaceId, RegionId, ScopeId, ValId};
use crate::inst::{CallRow, Callee, InstRow, ReduceRow, SwitchArm, SwitchRow};
use crate::op::Op;
use crate::place::Seg;
use crate::region::{CaptureRow, RegionKind, RegionRow};
use crate::scope::{DeferKind, DeferRow, ScopeRow};
use crate::site::SiteRow;
use crate::value::ValRow;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodeError(pub String);

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fors-fmir decode error: {}", self.0)
    }
}
impl std::error::Error for DecodeError {}

fn err(msg: impl Into<String>) -> DecodeError {
    DecodeError(msg.into())
}

/// Little-endian `u32`-word writer. `into_bytes` is the only way out, so
/// "canonical byte encoding" is not just a comment — the wire format really
/// is bytes.
struct Writer {
    words: Vec<u32>,
}

impl Writer {
    fn new() -> Self {
        Writer { words: Vec::new() }
    }

    fn u32(&mut self, v: u32) {
        self.words.push(v);
    }

    fn u16(&mut self, v: u16) {
        self.words.push(v as u32);
    }

    fn bool(&mut self, v: bool) {
        self.u32(v as u32);
    }

    fn i64(&mut self, v: i64) {
        self.u64(v as u64);
    }

    fn u64(&mut self, v: u64) {
        self.u32(v as u32);
        self.u32((v >> 32) as u32);
    }

    fn range(&mut self, r: Range<u32>) {
        self.u32(r.start);
        self.u32(r.end);
    }

    fn into_bytes(self) -> Vec<u8> {
        self.words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }
}

struct Reader<'a> {
    words: &'a [u32],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn u32(&mut self) -> Result<u32, DecodeError> {
        let v = *self
            .words
            .get(self.pos)
            .ok_or_else(|| err("unexpected end of input"))?;
        self.pos += 1;
        Ok(v)
    }

    fn u16(&mut self) -> Result<u16, DecodeError> {
        let v = self.u32()?;
        u16::try_from(v).map_err(|_| err("value out of range for u16"))
    }

    fn u8(&mut self) -> Result<u8, DecodeError> {
        let v = self.u32()?;
        u8::try_from(v).map_err(|_| err("value out of range for u8"))
    }

    fn bool(&mut self) -> Result<bool, DecodeError> {
        Ok(self.u32()? != 0)
    }

    fn u64(&mut self) -> Result<u64, DecodeError> {
        let lo = self.u32()? as u64;
        let hi = self.u32()? as u64;
        Ok(lo | (hi << 32))
    }

    fn i64(&mut self) -> Result<i64, DecodeError> {
        Ok(self.u64()? as i64)
    }

    fn range(&mut self) -> Result<Range<u32>, DecodeError> {
        let start = self.u32()?;
        let end = self.u32()?;
        Ok(start..end)
    }
}

fn conv_to_u32(c: Conv) -> u32 {
    match c {
        Conv::Let => 0,
        Conv::Inout => 1,
        Conv::Sink => 2,
        Conv::Set => 3,
    }
}

fn conv_from_u32(v: u32) -> Result<Conv, DecodeError> {
    Ok(match v {
        0 => Conv::Let,
        1 => Conv::Inout,
        2 => Conv::Sink,
        3 => Conv::Set,
        _ => return Err(err("bad Conv tag")),
    })
}

fn write_inst_row(w: &mut Writer, row: InstRow) {
    w.u32(row.op.discriminant());
    w.u32(row.op.payload());
    w.u32(row.a);
    w.u32(row.b);
    w.u32(row.c);
    w.u32(row.ty.0);
    w.u32(row.site.0);
}

fn read_inst_row(r: &mut Reader) -> Result<InstRow, DecodeError> {
    let discr = r.u32()?;
    let payload = r.u32()?;
    let op = Op::from_parts(discr, payload).ok_or_else(|| err("bad Op discriminant"))?;
    let a = r.u32()?;
    let b = r.u32()?;
    let c = r.u32()?;
    let ty = TyId(r.u32()?);
    let site = crate::ids::SiteId(r.u32()?);
    Ok(InstRow {
        op,
        a,
        b,
        c,
        ty,
        site,
    })
}

fn write_callee(w: &mut Writer, callee: Callee) {
    match callee {
        Callee::Direct(k) => {
            w.u32(0);
            w.u32(k.0);
            w.u32(0);
        }
        Callee::Witness { table, method } => {
            w.u32(1);
            w.u32(table);
            w.u32(method as u32);
        }
        Callee::Closure(v) => {
            w.u32(2);
            w.u32(v.0);
            w.u32(0);
        }
        Callee::Intrinsic(s) => {
            w.u32(3);
            w.u32(s.0);
            w.u32(0);
        }
    }
}

fn read_callee(r: &mut Reader) -> Result<Callee, DecodeError> {
    let tag = r.u32()?;
    let x = r.u32()?;
    let y = r.u32()?;
    Ok(match tag {
        0 => Callee::Direct(DeclKeyId(x)),
        1 => Callee::Witness {
            table: x,
            method: u16::try_from(y).map_err(|_| err("method ordinal too large"))?,
        },
        2 => Callee::Closure(ValId(x)),
        3 => Callee::Intrinsic(Symbol(x)),
        _ => return Err(err("bad Callee tag")),
    })
}

/// A faithful, order-preserving encoding of every pool: `decode(encode(d))`
/// re-encodes to exactly the same bytes as `encode(d)` for any `d` this
/// crate's own builder/generator can produce (`encode_decode_roundtrip`).
pub fn to_bytes(d: &DeclFmir) -> Vec<u8> {
    let mut w = Writer::new();
    w.u32(d.decl.0);
    w.u32(d.sig.0);
    w.u32(d.entry.0);
    w.bool(d.is_unsafe_invariant);

    w.u32(d.vals.len() as u32);
    for (_, row) in d.vals.all_rows() {
        w.u32(row.ty.0);
        w.u32(row.flags.0 as u32);
        w.u16(row.ct);
        w.u32(row.def);
    }
    for i in 0..d.vals.len() {
        match d.vals.scoped_sources(ValId(i as u32)) {
            None => w.bool(false),
            Some(range) => {
                w.bool(true);
                w.range(range);
            }
        }
    }

    w.u32(d.places.len() as u32);
    for (id, row) in d.places.all_rows() {
        w.u32(row.root);
        w.u32(row.ty.0);
        let segs = d.places.segs(id);
        w.u32(segs.len() as u32);
        for seg in segs {
            match *seg {
                Seg::Field(i) => {
                    w.u32(0);
                    w.u32(i as u32);
                }
                Seg::Index(v) => {
                    w.u32(1);
                    w.u32(v.0);
                }
                Seg::Deref => {
                    w.u32(2);
                    w.u32(0);
                }
            }
        }
    }

    w.u32(d.insts.len() as u32);
    for (_, row) in d.insts.all_rows() {
        write_inst_row(&mut w, row);
    }
    for seed in d.insts.aliases.as_slice() {
        write_alias_seed(&mut w, *seed);
    }
    w.u32(d.insts.operands.len() as u32);
    for v in &d.insts.operands {
        w.u32(v.0);
    }
    w.u32(d.insts.arg_convs.len() as u32);
    for c in &d.insts.arg_convs {
        w.u32(conv_to_u32(*c));
    }
    w.u32(d.insts.calls.len() as u32);
    for call in &d.insts.calls {
        write_callee(&mut w, call.callee);
        w.range(call.args.clone());
    }
    w.u32(d.insts.reduces.len() as u32);
    for red in &d.insts.reduces {
        write_callee(&mut w, red.op);
        w.u32(red.xs.0);
        w.u32(red.identity.0);
        w.u32(red.b);
        w.u32(red.l);
    }
    w.u32(d.insts.switches.len() as u32);
    for sw in &d.insts.switches {
        w.u32(sw.discr.0);
        w.u32(sw.default.0);
        w.range(sw.arms.clone());
    }
    w.u32(d.insts.switch_arms.len() as u32);
    for arm in &d.insts.switch_arms {
        w.i64(arm.value);
        w.u32(arm.target.0);
    }

    w.u32(d.blocks.len() as u32);
    for (_, row) in d.blocks.all_rows() {
        w.u32(row.first_inst);
        w.u32(row.inst_len);
        write_inst_row(&mut w, row.term);
        w.u32(row.scope.0);
    }

    w.u32(d.scopes.len() as u32);
    for (_, row) in d.scopes.all_rows() {
        w.u32(row.parent.0);
        w.u32(row.brand.0);
        w.range(row.defers.clone());
        w.range(row.obligations.clone());
        w.u32(row.region.0);
    }

    let defer_count = d.defers.len() as u32;
    w.u32(defer_count);
    for row in d.defers.get(0..defer_count) {
        w.u32(matches!(row.kind, DeferKind::ErrDefer) as u32);
        w.u32(row.body.0);
        w.u16(row.stmt_order);
    }

    w.u32(d.regions.len() as u32);
    for (_, row) in d.regions.all_rows() {
        w.u32(region_kind_to_u32(row.kind));
        w.range(row.captures.clone());
        w.u32(row.brand.0);
    }
    let cap_count = d.regions.captures.len() as u32;
    w.u32(cap_count);
    for cap in d.regions.captures.get(0..cap_count) {
        w.u32(cap.value.0);
        w.u32(conv_to_u32(cap.conv));
    }

    w.u32(d.sites.len() as u32);
    for i in 0..d.sites.len() {
        let row = d.sites.row(crate::ids::SiteId(i as u32));
        w.u32(row.line);
        w.u32(row.col);
    }

    write_const_pool(&mut w, d);

    w.u32(d.obligations.as_slice().len() as u32);
    for p in d.obligations.as_slice() {
        w.u32(p.0);
    }
    w.u32(d.scoped_sources.as_slice().len() as u32);
    for p in d.scoped_sources.as_slice() {
        w.u32(p.0);
    }

    w.into_bytes()
}

fn write_const_pool(w: &mut Writer, d: &DeclFmir) {
    w.u32(d.consts.len() as u32);
    for i in 0..d.consts.len() {
        match d.consts.row(crate::ids::FmirConstId(i as u32)) {
            ConstValue::Int(v) => {
                w.u32(0);
                w.i64(v);
            }
            ConstValue::FloatBits(v) => {
                w.u32(1);
                w.u64(v);
            }
            ConstValue::Bool(v) => {
                w.u32(2);
                w.u64(v as u64);
            }
            ConstValue::Unit => {
                w.u32(3);
                w.u64(0);
            }
            ConstValue::Str(s) => {
                w.u32(4);
                w.u64(s.0 as u64);
            }
        }
    }
}

fn region_kind_to_u32(k: RegionKind) -> u32 {
    match k {
        RegionKind::Spawn => 0,
        RegionKind::Parallel => 1,
        RegionKind::WithArena => 2,
    }
}

fn region_kind_from_u32(v: u32) -> Result<RegionKind, DecodeError> {
    Ok(match v {
        0 => RegionKind::Spawn,
        1 => RegionKind::Parallel,
        2 => RegionKind::WithArena,
        _ => return Err(err("bad RegionKind tag")),
    })
}

fn write_alias_seed(w: &mut Writer, s: AliasSeed) {
    match s {
        AliasSeed::None => {
            w.u32(0);
            w.u32(0);
            w.u32(0);
        }
        AliasSeed::Conv(c) => {
            w.u32(1);
            w.u32(conv_to_u32(c));
            w.u32(0);
        }
        AliasSeed::Own(p) => {
            w.u32(2);
            w.u32(p.0);
            w.u32(0);
        }
        AliasSeed::Arena(b) => {
            w.u32(3);
            w.u32(b.0);
            w.u32(0);
        }
        AliasSeed::Split { parent, side } => {
            w.u32(4);
            w.u32(parent.0);
            w.u32(side as u32);
        }
    }
}

fn read_alias_seed(r: &mut Reader) -> Result<AliasSeed, DecodeError> {
    let tag = r.u32()?;
    let x = r.u32()?;
    Ok(match tag {
        0 => {
            r.u32()?; // the unused third word every tag reserves, for a fixed row width
            AliasSeed::None
        }
        1 => {
            r.u32()?;
            AliasSeed::Conv(conv_from_u32(x)?)
        }
        2 => {
            r.u32()?;
            AliasSeed::Own(PlaceId(x))
        }
        3 => {
            r.u32()?;
            AliasSeed::Arena(BrandId(x))
        }
        4 => AliasSeed::Split {
            parent: PlaceId(x),
            side: r.u8()?,
        },
        _ => return Err(err("bad AliasSeed tag")),
    })
}

/// The inverse of [`to_bytes`].
pub fn from_bytes(bytes: &[u8]) -> Result<DeclFmir, DecodeError> {
    if !bytes.len().is_multiple_of(4) {
        return Err(err("byte length is not a multiple of 4"));
    }
    let words: Vec<u32> = bytes
        .as_chunks::<4>()
        .0
        .iter()
        .map(|c| u32::from_le_bytes(*c))
        .collect();
    let mut r = Reader {
        words: &words,
        pos: 0,
    };

    let decl_key = DeclKeyId(r.u32()?);
    let sig = FnSigId(r.u32()?);
    let entry = BlockId(r.u32()?);
    let is_unsafe_invariant = r.bool()?;

    let mut vals = crate::value::ValPool::new();
    let n_vals = r.u32()?;
    for _ in 0..n_vals {
        let ty = TyId(r.u32()?);
        let flags = ValFlags(r.u16()?);
        let ct = r.u16()?;
        let def = r.u32()?;
        vals.push(ValRow { ty, flags, ct, def });
    }
    for i in 0..n_vals {
        if r.bool()? {
            let range = r.range()?;
            vals.set_scoped_sources(ValId(i), range);
        }
    }

    let mut places = crate::place::PlacePool::new();
    let n_places = r.u32()?;
    for expected in 0..n_places {
        let root = r.u32()?;
        let ty = TyId(r.u32()?);
        let n_segs = r.u32()?;
        let mut segs = Vec::with_capacity(n_segs as usize);
        for _ in 0..n_segs {
            let tag = r.u32()?;
            let x = r.u32()?;
            segs.push(match tag {
                0 => Seg::Field(u16::try_from(x).map_err(|_| err("field index out of range"))?),
                1 => Seg::Index(ValId(x)),
                2 => Seg::Deref,
                _ => return Err(err("bad Seg tag")),
            });
        }
        let got = places.intern(root, &segs, ty);
        if got.0 != expected {
            return Err(err(
                "place pool did not replay to the same ids (non-canonical input)",
            ));
        }
    }

    let mut insts = crate::inst::InstPool::new();
    let n_insts = r.u32()?;
    let mut rows = Vec::with_capacity(n_insts as usize);
    for _ in 0..n_insts {
        rows.push(read_inst_row(&mut r)?);
    }
    let mut seeds = Vec::with_capacity(n_insts as usize);
    for _ in 0..n_insts {
        seeds.push(read_alias_seed(&mut r)?);
    }
    for (row, seed) in rows.into_iter().zip(seeds) {
        insts.push(row, seed);
    }
    let n_operands = r.u32()?;
    for _ in 0..n_operands {
        insts.operands.push(ValId(r.u32()?));
    }
    let n_convs = r.u32()?;
    for _ in 0..n_convs {
        insts.arg_convs.push(conv_from_u32(r.u32()?)?);
    }
    let n_calls = r.u32()?;
    for _ in 0..n_calls {
        let callee = read_callee(&mut r)?;
        let args = r.range()?;
        insts.calls.push(CallRow { callee, args });
    }
    let n_reduces = r.u32()?;
    for _ in 0..n_reduces {
        let op = read_callee(&mut r)?;
        let xs = ValId(r.u32()?);
        let identity = ValId(r.u32()?);
        let b = r.u32()?;
        let l = r.u32()?;
        insts.reduces.push(ReduceRow {
            op,
            xs,
            identity,
            b,
            l,
        });
    }
    let n_switches = r.u32()?;
    for _ in 0..n_switches {
        let discr = ValId(r.u32()?);
        let default = BlockId(r.u32()?);
        let arms = r.range()?;
        insts.switches.push(SwitchRow {
            discr,
            default,
            arms,
        });
    }
    let n_arms = r.u32()?;
    for _ in 0..n_arms {
        let value = r.i64()?;
        let target = BlockId(r.u32()?);
        insts.switch_arms.push(SwitchArm { value, target });
    }

    let mut blocks = crate::block::BlockPool::new();
    let n_blocks = r.u32()?;
    for _ in 0..n_blocks {
        let first_inst = r.u32()?;
        let inst_len = r.u32()?;
        let term = read_inst_row(&mut r)?;
        let scope = ScopeId(r.u32()?);
        blocks.push(BlockRow {
            first_inst,
            inst_len,
            term,
            scope,
        });
    }

    let mut scopes = crate::scope::ScopePool::new();
    let n_scopes = r.u32()?;
    for _ in 0..n_scopes {
        let parent = ScopeId(r.u32()?);
        let brand = BrandId(r.u32()?);
        let defers = r.range()?;
        let obligations = r.range()?;
        let region = RegionId(r.u32()?);
        scopes.push(ScopeRow {
            parent,
            brand,
            defers,
            obligations,
            region,
        });
    }

    let mut defers = crate::scope::DeferPool::new();
    let n_defers = r.u32()?;
    for _ in 0..n_defers {
        let kind = if r.u32()? != 0 {
            DeferKind::ErrDefer
        } else {
            DeferKind::Defer
        };
        let body = BlockId(r.u32()?);
        let stmt_order = r.u16()?;
        defers.push(DeferRow {
            kind,
            body,
            stmt_order,
        });
    }

    let mut regions = crate::region::RegionPool::new();
    let n_regions = r.u32()?;
    for _ in 0..n_regions {
        let kind = region_kind_from_u32(r.u32()?)?;
        let captures = r.range()?;
        let brand = BrandId(r.u32()?);
        regions.push(RegionRow {
            kind,
            captures,
            brand,
        });
    }
    let n_caps = r.u32()?;
    for _ in 0..n_caps {
        let value = ValId(r.u32()?);
        let conv = conv_from_u32(r.u32()?)?;
        regions.captures.push(CaptureRow { value, conv });
    }

    let mut sites = crate::site::SitePool::new();
    let n_sites = r.u32()?;
    for _ in 0..n_sites {
        let line = r.u32()?;
        let col = r.u32()?;
        sites.push(SiteRow { line, col });
    }

    let mut consts = crate::constpool::ConstPool::new();
    let n_consts = r.u32()?;
    for _ in 0..n_consts {
        let tag = r.u32()?;
        let v = match tag {
            0 => ConstValue::Int(r.i64()?),
            1 => ConstValue::FloatBits(r.u64()?),
            2 => ConstValue::Bool(r.u64()? != 0),
            3 => {
                r.u64()?;
                ConstValue::Unit
            }
            4 => ConstValue::Str(Symbol(
                u32::try_from(r.u64()?).map_err(|_| err("symbol id out of range"))?,
            )),
            _ => return Err(err("bad ConstValue tag")),
        };
        consts.intern(v);
    }

    let n_obligation_items = r.u32()?;
    let mut obligation_items = Vec::with_capacity(n_obligation_items as usize);
    for _ in 0..n_obligation_items {
        obligation_items.push(PlaceId(r.u32()?));
    }
    let obligations = crate::scope::PlaceListPool::from_raw(obligation_items);

    let n_source_items = r.u32()?;
    let mut source_items = Vec::with_capacity(n_source_items as usize);
    for _ in 0..n_source_items {
        source_items.push(PlaceId(r.u32()?));
    }
    let scoped_sources = crate::scope::PlaceListPool::from_raw(source_items);

    if r.pos != words.len() {
        return Err(err("trailing bytes after a complete decode"));
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
        sites,
        consts,
        obligations,
        scoped_sources,
        defers,
        entry,
        is_unsafe_invariant,
        fingerprint: 0,
    })
}

/// A canonical block traversal from `entry`: BFS in `br`/`cond_br`/
/// `switch_discr`/`try_br` target order, falling back to appending any block
/// unreachable from `entry` in its original storage order (so `fmir_hash`
/// stays total over hand-built/negative-corpus FMIR that is not always fully
/// connected). Returns `old BlockId -> canonical index`.
fn canonical_block_order(d: &DeclFmir) -> Vec<u32> {
    let n = d.blocks.len();
    let mut order = Vec::with_capacity(n);
    let mut seen = vec![false; n];
    let mut queue = std::collections::VecDeque::new();
    // `entry` is a plain field any caller can set (and a decoded or fuzzed
    // declaration may set past the end, or to 0 with no blocks at all), so the
    // BFS is only seeded when it names a real block; every block then reaches
    // the "unreachable from entry" fallback below in storage order, keeping
    // `fmir_hash` total (see `safe_remap`).
    if d.entry.index() < n {
        queue.push_back(d.entry);
        seen[d.entry.index()] = true;
    }
    while let Some(id) = queue.pop_front() {
        order.push(id.0);
        for target in successors(&d.blocks.row(id).term, &d.insts) {
            let idx = target.index();
            if idx < n && !seen[idx] {
                seen[idx] = true;
                queue.push_back(target);
            }
        }
    }
    for (i, seen_i) in seen.iter().enumerate() {
        if !seen_i {
            order.push(i as u32);
        }
    }
    // `old_to_canonical[old_id] = canonical_index`
    let mut old_to_canonical = vec![0u32; n];
    for (canonical, old) in order.iter().enumerate() {
        old_to_canonical[*old as usize] = canonical as u32;
    }
    old_to_canonical
}

fn successors(term: &InstRow, insts: &crate::inst::InstPool) -> Vec<BlockId> {
    match term.op {
        Op::Br => vec![BlockId(term.a)],
        Op::CondBr => vec![BlockId(term.b), BlockId(term.c)],
        Op::TryBr => vec![BlockId(term.b), BlockId(term.c)],
        // `term.a` is a side-table index (into `insts.switches`), not a
        // `BlockId`; like every other data-carried index in this file, an
        // arbitrary/fuzzed `DeclFmir` is not guaranteed to keep it in range
        // (`safe_remap`'s doc comment gives the full reasoning) — treated as
        // "no successors known" rather than panicking.
        Op::SwitchDiscr if (term.a as usize) >= insts.switches.len() => Vec::new(),
        Op::SwitchDiscr => {
            let sw = &insts.switches[term.a as usize];
            let mut targets = vec![sw.default];
            for arm in &insts.switch_arms[sw.arms.start as usize..sw.arms.end as usize] {
                targets.push(arm.target);
            }
            targets
        }
        _ => Vec::new(),
    }
}

/// `old_to_canonical[raw]`, or `raw` unchanged if it is out of range. Every
/// caller here is remapping a `BlockId` embedded in instruction/side-table
/// *data*, which — unlike a `BlockId` this crate's own iteration produced —
/// is not guaranteed in range for arbitrary (fuzzed, hand-built or corrupt)
/// FMIR; `fmir_hash` must stay total (never panic) over any `DeclFmir` this
/// crate's own types can express, `verify()`-clean or not, since callers
/// such as a future delta-debugging reducer (design §7.3) may hash
/// candidates before they are known to verify. [decision: out-of-range
/// stays unchanged rather than being an error — `fmir_hash` has no
/// `Result`-returning form, and design gives it none]
fn safe_remap(old_to_canonical: &[u32], raw: u32) -> u32 {
    old_to_canonical.get(raw as usize).copied().unwrap_or(raw)
}

/// Every place a raw `BlockId` is embedded outside `BlockPool`'s own row
/// order: a terminator's branch targets, and a `switch_discr`'s default/arm
/// targets (`DeferRow.body` is a third — handled directly in
/// [`canonicalize`], since `DeferPool` has no in-place row mutator).
fn remap_terminator(mut row: InstRow, old_to_canonical: &[u32]) -> InstRow {
    match row.op {
        Op::Br => row.a = safe_remap(old_to_canonical, row.a),
        Op::CondBr | Op::TryBr => {
            row.b = safe_remap(old_to_canonical, row.b);
            row.c = safe_remap(old_to_canonical, row.c);
        }
        _ => {}
    }
    row
}

/// Produces a structurally-equivalent `DeclFmir` whose blocks are stored in
/// [`canonical_block_order`] and whose `entry` is therefore always block 0 —
/// every OTHER field is an untouched clone. Hashing this (via [`to_bytes`],
/// which already covers every pool) is what makes [`fmir_hash`] invariant
/// under the original's block numbering while still changing on any other
/// edit, without a second, parallel, partial copy of `to_bytes`'s field
/// list. [decision: canonicalize-then-reuse-`to_bytes`, not a bespoke
/// "canonical writer"]
fn canonicalize(d: &DeclFmir) -> DeclFmir {
    let old_to_canonical = canonical_block_order(d);
    let mut out = d.clone();
    out.entry = BlockId(safe_remap(&old_to_canonical, d.entry.0));

    // `by_canonical` is only as long as `d.blocks.len()`, which every REAL
    // block index (`old_id`, from `d.blocks.all_rows()` itself) fits by
    // construction — unlike the data-carried references above, this index
    // needs no defensive form.
    let mut by_canonical: Vec<Option<BlockRow>> = vec![None; d.blocks.len()];
    for (old_id, mut row) in d.blocks.all_rows() {
        row.term = remap_terminator(row.term, &old_to_canonical);
        by_canonical[old_to_canonical[old_id.index()] as usize] = Some(row);
    }
    let mut new_blocks = crate::block::BlockPool::new();
    for slot in by_canonical {
        new_blocks.push(slot.expect("`old_to_canonical` is a bijection over 0..n"));
    }
    out.blocks = new_blocks;

    for sw in &mut out.insts.switches {
        sw.default = BlockId(safe_remap(&old_to_canonical, sw.default.0));
    }
    for arm in &mut out.insts.switch_arms {
        arm.target = BlockId(safe_remap(&old_to_canonical, arm.target.0));
    }

    let defer_count = out.defers.len() as u32;
    let mut new_defers = crate::scope::DeferPool::new();
    for row in out.defers.get(0..defer_count) {
        let mut row = *row;
        row.body = BlockId(safe_remap(&old_to_canonical, row.body.0));
        new_defers.push(row);
    }
    out.defers = new_defers;

    out
}

/// `fmir_hash`: `hash_bytes` over [`to_bytes`] of the [`canonicalize`]d form
/// (design §9's own name for this gate; `DeclFmir::fingerprint` is the same
/// value once computed). Because `canonicalize` is the *only* difference
/// from `to_bytes`'s own encoding, and it touches nothing but `BlockId`
/// values and block storage order, `fmir_hash` is invariant under block
/// renumbering (two isomorphic declarations that differ only in which raw
/// `BlockId` names which block canonicalize to byte-identical output) and
/// still changes on any operand edit (`to_bytes` covers every pool, so does
/// this).
pub fn fmir_hash(d: &DeclFmir) -> u128 {
    let bytes = to_bytes(&canonicalize(d));
    fors_index::fingerprint::hash_bytes(&bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decl::DeclFmir;
    use crate::value::ValDef;
    use fors_fir::defpath::DeclKeyId;
    use fors_fir::sig::FnSigId;
    use fors_fir::ty::TY_UNIT;

    #[test]
    fn empty_decl_round_trips() {
        let decl = DeclFmir::empty(DeclKeyId(3), FnSigId(4));
        let bytes = to_bytes(&decl);
        let decoded = from_bytes(&bytes).unwrap();
        assert_eq!(to_bytes(&decoded), bytes);
    }

    #[test]
    fn a_value_round_trips() {
        let mut decl = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        decl.push_val(ValRow::new(TY_UNIT, true, 5, ValDef::Param(2)));
        let bytes = to_bytes(&decl);
        let decoded = from_bytes(&bytes).unwrap();
        assert_eq!(to_bytes(&decoded), bytes);
    }

    #[test]
    fn hash_changes_on_operand_edit() {
        let mut a = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        a.push_val(ValRow::new(TY_UNIT, false, 0, ValDef::Param(0)));
        let mut b = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        b.push_val(ValRow::new(TY_UNIT, true, 0, ValDef::Param(0)));
        assert_ne!(fmir_hash(&a), fmir_hash(&b));
    }

    #[test]
    fn hash_is_stable_for_the_same_decl() {
        let decl = DeclFmir::empty(DeclKeyId(1), FnSigId(2));
        assert_eq!(fmir_hash(&decl), fmir_hash(&decl));
    }

    /// `fmir_hash` invariant under basic-block renumbering (design item 3 /
    /// F0 gate `fmir_hash`): build the same three-block shape twice with the
    /// non-entry blocks pushed in opposite storage order (so their raw
    /// `BlockId`s differ) and confirm the hash agrees.
    #[test]
    fn hash_is_invariant_under_block_renumbering() {
        use crate::block::BlockRow;
        use crate::ids::ScopeId;

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

        fn br_to(target: BlockId) -> InstRow {
            InstRow {
                op: Op::Br,
                a: target.0,
                b: crate::op::NO_OPERAND,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            }
        }
        fn leaf_row() -> BlockRow {
            BlockRow {
                first_inst: 0,
                inst_len: 0,
                term: plain(Op::Unreachable),
                scope: ScopeId(0),
            }
        }

        // Shape A: pushed [leaf=0, mid=1, entry=2]; entry --br--> mid --br--> leaf.
        let mut a = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut blocks = crate::block::BlockPool::new();
        let leaf = blocks.push(leaf_row());
        let mid = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: br_to(leaf),
            scope: ScopeId(0),
        });
        let entry = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: br_to(mid),
            scope: ScopeId(0),
        });
        a.blocks = blocks;
        a.entry = entry;

        // Shape B: the identical graph, but pushed [mid=0, leaf=1, entry=2] —
        // `mid` and `leaf` swap raw `BlockId`s relative to shape A.
        let mut b = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
        let mut blocks = crate::block::BlockPool::new();
        let mid_id = BlockId(0);
        let leaf_id = BlockId(1);
        let _ = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: br_to(leaf_id),
            scope: ScopeId(0),
        });
        let _ = blocks.push(leaf_row());
        let entry = blocks.push(BlockRow {
            first_inst: 0,
            inst_len: 0,
            term: br_to(mid_id),
            scope: ScopeId(0),
        });
        b.blocks = blocks;
        b.entry = entry;

        assert_eq!(
            fmir_hash(&a),
            fmir_hash(&b),
            "isomorphic graphs with different raw BlockIds must hash equal"
        );
    }

    #[test]
    fn hash_changes_when_a_call_argument_changes() {
        use fors_index::interner::Symbol;

        fn build(arg: ValId) -> DeclFmir {
            let mut d = DeclFmir::empty(DeclKeyId(0), FnSigId(0));
            let args = d.insts.push_operands(&[arg], &[Conv::Let]);
            let call_idx = d.insts.push_call(CallRow {
                callee: Callee::Intrinsic(Symbol(0)),
                args,
            });
            let inst = InstRow {
                op: Op::Intrinsic,
                a: call_idx,
                b: crate::op::NO_OPERAND,
                c: crate::op::NO_OPERAND,
                ty: TY_UNIT,
                site: crate::ids::SiteId(0),
            };
            d.push_inst(inst, AliasSeed::None);
            d
        }
        let a = build(ValId(0));
        let b = build(ValId(1));
        assert_ne!(fmir_hash(&a), fmir_hash(&b));
    }
}
