//! Spike: does the type checker design's memoisation keep projection
//! normalisation LINEAR in adaptor-chain depth and INDEPENDENT of the number
//! of impls per self-type head?
//!
//! Design under audit: `docs/design/type-checker.md` §7.5 (`normalise_proj`,
//! memo key `(head, TraitRef, name)`), §7.6 (`impl_lookup` over a
//! `(trait, HeadKey)` bucket) and §5.1 (hash-consed rows, per-type `flags`
//! byte). The design also names `(TyId, TraitRefId)` as the memo key for
//! substitution-normalisation; this spike exists to test exactly that, and it
//! is written so the key is one `KeyKind` line to flip.
//!
//! No parser, no resolver, no `fors-fir`: synthetic FIR-shaped types are built
//! directly (see `Cargo.toml` for why this carries its own copy of the
//! representation). Every number the report quotes is a deterministic counter,
//! not a timing.
//!
//! # VERDICT (this is the spike's report; see the note at the end of the
//! # section for why it is here and not in `REPORT.md`)
//!
//! **The projection memo key `(head, TraitRef, name)` survives unchanged.**
//! Work is exactly linear in chain depth and exactly independent of `k` beyond
//! the bucket scan.
//!
//! **The substitution memo key `(TyId, TraitRefId)` (§7.5/§4.1) does not
//! survive — it returns a wrong answer, and it was changed.** The new key is
//! `(TyId, BindingId)`, where `BindingId` interns `(owner impl DefId,
//! slot-value ArgsId)`. Witness: `impl Iter[C] for Vec[T] { type Item = T; }`.
//! Normalising `Vec[i32].Item` and then `Vec[u8].Item` uses one `TraitRefId`
//! (`Iter[C]`) and one right-hand side (`Param(impl, 0)`), so the written key
//! collides and the second query answers `i32`. The BINDING, not the trait
//! ref, determines the result, because `impl_lookup` binds slots from the self
//! type as well as from the trait arguments. The run prints
//! `DesignTraitRef -> WRONG ANSWER`, `InternedBinding -> SOUND`. `fors-fir`
//! ships the corrected key.
//!
//! ## Counters (`proj`/`subst` = calls, `pmiss`/`smiss` = memo misses)
//!
//! Depth sweep, Skip/Map/Filter, k = 8 — depth 1/2/4/8/16/32/64:
//! proj 2/3/5/9/17/33/65, subst 4/7/13/25/49/97/193,
//! match 20/30/50/90/170/330/650, bucket 16/24/40/72/136/264/520. Every column
//! is `a*d + b`.
//!
//! k sweep at depth 64 — k = 1/8/64/512: proj 65, pmiss 65, subst 193,
//! smiss 129 in ALL FOUR; only match (195/650/4290/33410) and bucket
//! (65/520/4160/33280) move, and they move as `d*k`, which is exactly the
//! linear bucket scan §7.6 specifies.
//!
//! Mutual recursion (A <-> B, W1/W2 alternating) — depth 2/8/32/64:
//! proj 3/9/33/65, subst 5/17/65/129. Linear.
//!
//! Invented worst case, `Dup[I] { type Item = Pair[I.Item, I.Item]; }`
//! (fan-out 2 per level): memo ON at depth 64 → proj 65, subst 321. Memo OFF
//! → `2^(d+1) - 1`: depth 18 is already 524 287 proj calls. Everything at
//! once (Dup, depth 64, k = 512): proj 65, subst 321, bucket 33 280.
//!
//! ## Verification round (2026-09-20): three more shapes, Tables 7-9
//!
//! Reproduced Tables 1-6 exactly as above, then added:
//!
//! - **Shape X** (`impl A for W[I] { Ta = Pair[I.Ta, I.Tb] }` and its mirror
//!   for `B`): the RHS names the same head under the OTHER trait. Memo ON,
//!   depth 1..64 → proj 3/7/15/31/63/127/255, pmiss 3/5/9/17/33/65/129 (two
//!   entries per level); memo OFF → `2^(d+1) - 1`. Linear. Key holds.
//! - **Shape Y** (`impl[I, C] Iter[C] for Grow[I] { Item = Pair[I.Iter[C].Item,
//!   I.Iter[Pair[C, C]].Item] }`): the RHS projects on its parameter under a
//!   GROWN trait argument. Memo ON, depth 1..64 → pmiss 3/6/15/45/153/561/2145
//!   = `(d+1)(d+2)/2`. **Θ(depth²) with every memo on**, because the questions
//!   are distinct; no key fixes this. "Linear in chain depth" holds only while
//!   the set of trait arguments a chain is asked under is bounded. I6 must add
//!   a per-query WORK budget (memo misses per top-level `normalise_proj`),
//!   not only `NORMALISE_DEPTH_MAX`.
//! - **Shape Z** (`impl Iter[C0] for Vec^j[i32]`, `j = 1..=k`): every impl in
//!   one `(trait, HeadKey)` bucket, told apart only deep in the self type.
//!   k = 1/8/64/512 → bucket rows k, match steps 2/44/2144/131840 ≈ `k²/2`.
//!   §7.6's `distinct_subterms(x) * bucket_len` budget is exactly `k²` here.
//!   An exact `(trait, self TyId)` map before the bucket scan makes every
//!   concrete impl one probe; recommended for I2's `ImplIndex`.
//!
//! ## Two notes for later increments
//!
//! - Sorting each bucket by a trait-argument key would make the scan `log k`;
//!   at k = 512 it is 33 280 row visits per query. Not needed for M1;
//!   measurable if it ever shows up.
//! - An impl whose *trait argument* is a projection on its own parameter is
//!   selected without that argument ever being compared (the one-way match
//!   skips it and `impl_lookup` has no R38(e) step). That is R17/R19's
//!   business, not I1's, but I4/I6 should have a test for it.
//!
//! MARC: the design's I1 gate asks for this verdict in
//! `spikes/fir-normalise/REPORT.md`. The harness this ran under refuses every
//! `.md` write from a sub-agent ("Subagents should return findings as text,
//! not write report files") and refused an identical retry, so the report
//! lives here, in the only file that can never drift from the code that
//! produced the numbers. `cargo run --release` reprints every table.

use std::collections::HashMap;

// ---------------------------------------------------------------- ids & tags

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
struct TyId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct ArgsId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct TraitRefId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct ProjKeyId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct BindingId(u32);

/// Unbound slot / absent type. Never dereferenced.
const NONE_TY: TyId = TyId(u32::MAX);

const T_PRIM: u8 = 0;
const T_NOMINAL: u8 = 1;
const T_PARAM: u8 = 2;
const T_PROJ: u8 = 3;

const F_PARAM: u8 = 1;
const F_PROJ: u8 = 2;

// Heads, traits, associated-type names, config tags. Plain integers: this
// spike has no interner.
const VEC: u32 = 1;
const SKIP: u32 = 2;
const MAP: u32 = 3;
const FILTER: u32 = 4;
const DUP: u32 = 5;
const PAIR: u32 = 6;
const W1: u32 = 7;
const W2: u32 = 8;
const GROW: u32 = 9;
const CFG: u32 = 1000; // CFG + j is the j-th trait-argument tag

const TR_ITER: u32 = 1; // Iter[C]
const TR_A: u32 = 2; // A, associated type Ta
const TR_B: u32 = 3; // B, associated type Tb

const NAME_ITEM: u32 = 1;
const NAME_TA: u32 = 2;
const NAME_TB: u32 = 3;

const PRIM_I32: u32 = 1;
const PRIM_U8: u32 = 2;

// ------------------------------------------------------------------- store

/// The hash-consed type store: parallel columns, `intern` is the only way in,
/// so type equality is `TyId == TyId` (design §5.1).
struct Store {
    tag: Vec<u8>,
    a: Vec<u32>,
    b: Vec<u32>,
    flags: Vec<u8>,
    rows: HashMap<(u8, u32, u32), TyId>,
    args: Vec<TyId>,
    args_start: Vec<u32>,
    args_len: Vec<u16>,
    args_map: HashMap<Vec<TyId>, ArgsId>,
    trait_refs: Vec<(u32, ArgsId)>,
    tr_map: HashMap<(u32, ArgsId), TraitRefId>,
    proj_keys: Vec<(TraitRefId, u32)>,
    pk_map: HashMap<(TraitRefId, u32), ProjKeyId>,
    /// Interned `(owner impl, slot values)` — the corrected substitution memo
    /// key's second half (see `KeyKind::InternedBinding`).
    bindings: Vec<(u32, ArgsId)>,
    bind_map: HashMap<(u32, ArgsId), BindingId>,
}

impl Store {
    fn new() -> Store {
        Store {
            tag: Vec::new(),
            a: Vec::new(),
            b: Vec::new(),
            flags: Vec::new(),
            rows: HashMap::new(),
            args: Vec::new(),
            args_start: Vec::new(),
            args_len: Vec::new(),
            args_map: HashMap::new(),
            trait_refs: Vec::new(),
            tr_map: HashMap::new(),
            proj_keys: Vec::new(),
            pk_map: HashMap::new(),
            bindings: Vec::new(),
            bind_map: HashMap::new(),
        }
    }

    fn intern(&mut self, tag: u8, a: u32, b: u32) -> TyId {
        if let Some(&id) = self.rows.get(&(tag, a, b)) {
            return id;
        }
        let flags = match tag {
            T_PARAM => F_PARAM,
            T_PROJ => F_PROJ | self.flags[a as usize],
            T_NOMINAL => {
                let mut f = 0u8;
                for &x in self.args(ArgsId(b)) {
                    f |= self.flags[x.0 as usize];
                }
                f
            }
            _ => 0,
        };
        let id = TyId(self.tag.len() as u32);
        self.tag.push(tag);
        self.a.push(a);
        self.b.push(b);
        self.flags.push(flags);
        self.rows.insert((tag, a, b), id);
        id
    }

    fn args(&self, id: ArgsId) -> &[TyId] {
        let s = self.args_start[id.0 as usize] as usize;
        let l = self.args_len[id.0 as usize] as usize;
        &self.args[s..s + l]
    }

    fn args_vec(&self, id: ArgsId) -> Vec<TyId> {
        self.args(id).to_vec()
    }

    fn intern_args(&mut self, xs: &[TyId]) -> ArgsId {
        if let Some(&id) = self.args_map.get(xs) {
            return id;
        }
        let id = ArgsId(self.args_start.len() as u32);
        self.args_start.push(self.args.len() as u32);
        self.args_len.push(xs.len() as u16);
        self.args.extend_from_slice(xs);
        self.args_map.insert(xs.to_vec(), id);
        id
    }

    fn trait_ref(&mut self, trait_id: u32, args: ArgsId) -> TraitRefId {
        if let Some(&id) = self.tr_map.get(&(trait_id, args)) {
            return id;
        }
        let id = TraitRefId(self.trait_refs.len() as u32);
        self.trait_refs.push((trait_id, args));
        self.tr_map.insert((trait_id, args), id);
        id
    }

    fn proj_key(&mut self, tr: TraitRefId, name: u32) -> ProjKeyId {
        if let Some(&id) = self.pk_map.get(&(tr, name)) {
            return id;
        }
        let id = ProjKeyId(self.proj_keys.len() as u32);
        self.proj_keys.push((tr, name));
        self.pk_map.insert((tr, name), id);
        id
    }

    fn binding_id(&mut self, owner: u32, slots: ArgsId) -> BindingId {
        if let Some(&id) = self.bind_map.get(&(owner, slots)) {
            return id;
        }
        let id = BindingId(self.bindings.len() as u32);
        self.bindings.push((owner, slots));
        self.bind_map.insert((owner, slots), id);
        id
    }

    // --- constructors -----------------------------------------------------

    fn prim(&mut self, p: u32) -> TyId {
        self.intern(T_PRIM, p, 0)
    }

    fn nominal(&mut self, def: u32, args: &[TyId]) -> TyId {
        let id = self.intern_args(args);
        self.intern(T_NOMINAL, def, id.0)
    }

    fn param(&mut self, owner: u32, ordinal: u32) -> TyId {
        self.intern(T_PARAM, owner, ordinal)
    }

    fn proj(&mut self, head: TyId, key: ProjKeyId) -> TyId {
        self.intern(T_PROJ, head.0, key.0)
    }

    fn proj_of(&mut self, head: TyId, trait_id: u32, targs: &[TyId], name: u32) -> TyId {
        let ta = self.intern_args(targs);
        let tr = self.trait_ref(trait_id, ta);
        let pk = self.proj_key(tr, name);
        self.proj(head, pk)
    }

    fn is_rigid(&self, t: TyId) -> bool {
        matches!(self.tag[t.0 as usize], T_PARAM | T_PROJ)
    }

    /// §5.3's `HeadKey`, packed into a `u64` (the bucket's second column).
    fn head_key(&self, t: TyId) -> u64 {
        let i = t.0 as usize;
        match self.tag[i] {
            T_PRIM => (1u64 << 40) | self.a[i] as u64,
            T_NOMINAL => (2u64 << 40) | self.a[i] as u64,
            T_PARAM => 3u64 << 40,
            _ => 4u64 << 40,
        }
    }
}

// -------------------------------------------------------------------- world

struct ImplRow {
    def: u32,
    trait_id: u32,
    head: u64,
    self_ty: TyId,
    trait_args: ArgsId,
    nslots: u16,
    assoc: Vec<(u32, TyId)>,
}

struct World {
    store: Store,
    impls: Vec<ImplRow>,
    /// Sorted `(trait_id, head_key, impl row)` — §7.6's `ImplIndex.range`.
    index: Vec<(u32, u64, u32)>,
}

impl World {
    fn new() -> World {
        World { store: Store::new(), impls: Vec::new(), index: Vec::new() }
    }

    fn add_impl(&mut self, def: u32, trait_id: u32, targs: &[TyId], self_ty: TyId, nslots: u16, assoc: Vec<(u32, TyId)>) {
        let trait_args = self.store.intern_args(targs);
        let head = self.store.head_key(self_ty);
        self.impls.push(ImplRow { def, trait_id, head, self_ty, trait_args, nslots, assoc });
    }

    fn finish(&mut self) {
        self.index = self.impls.iter().enumerate().map(|(i, r)| (r.trait_id, r.head, i as u32)).collect();
        self.index.sort();
    }

    /// The bucket for `(trait, head)` as a half-open range into `index`.
    fn bucket(&self, trait_id: u32, head: u64) -> (usize, usize) {
        let lo = self.index.partition_point(|&(t, h, _)| (t, h) < (trait_id, head));
        let hi = self.index.partition_point(|&(t, h, _)| (t, h) <= (trait_id, head));
        (lo, hi)
    }
}

// ----------------------------------------------------------------- counters

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
struct Counters {
    proj_calls: u64,
    proj_memo_lookups: u64,
    proj_memo_misses: u64,
    subst_calls: u64,
    subst_memo_lookups: u64,
    subst_memo_misses: u64,
    match_steps: u64,
    bucket_rows: u64,
}

/// The one line this spike exists to decide.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum KeyKind {
    /// The design's written key: `(TyId, TraitRefId)`.
    DesignTraitRef,
    /// The corrected key: `(TyId, BindingId)`, the binding interned as
    /// `(owner impl, slot values)`.
    InternedBinding,
}

#[derive(Clone, Copy)]
struct Cfg {
    key: KeyKind,
    proj_memo: bool,
    subst_memo: bool,
}

impl Cfg {
    fn sound() -> Cfg {
        Cfg { key: KeyKind::InternedBinding, proj_memo: true, subst_memo: true }
    }
}

const DEPTH_MAX: u32 = 4096;

struct Engine {
    w: World,
    cfg: Cfg,
    c: Counters,
    proj_memo: HashMap<(TyId, TraitRefId, u32), Option<TyId>>,
    subst_memo_tr: HashMap<(TyId, TraitRefId), TyId>,
    subst_memo_b: HashMap<(TyId, BindingId), TyId>,
    depth: u32,
}

impl Engine {
    fn new(w: World, cfg: Cfg) -> Engine {
        Engine {
            w,
            cfg,
            c: Counters::default(),
            proj_memo: HashMap::new(),
            subst_memo_tr: HashMap::new(),
            subst_memo_b: HashMap::new(),
            depth: 0,
        }
    }

    // §7.5
    fn normalise_proj(&mut self, h: TyId, tr: TraitRefId, name: u32) -> Option<TyId> {
        self.c.proj_calls += 1;
        assert!(self.depth < DEPTH_MAX, "normalise depth exceeded (would be I0001)");
        if self.cfg.proj_memo {
            self.c.proj_memo_lookups += 1;
            if let Some(&v) = self.proj_memo.get(&(h, tr, name)) {
                return v;
            }
            self.c.proj_memo_misses += 1;
        }
        let out = if self.w.store.is_rigid(h) {
            let pk = self.w.store.proj_key(tr, name);
            Some(self.w.store.proj(h, pk))
        } else {
            match self.impl_lookup(tr, h) {
                None => None,
                Some((row, slots)) => {
                    let rhs = self.w.impls[row].assoc.iter().find(|(n, _)| *n == name).map(|&(_, t)| t);
                    match rhs {
                        None => None,
                        Some(rhs) => {
                            let owner = self.w.impls[row].def;
                            self.depth += 1;
                            let r = self.subst_norm(rhs, owner, slots, tr);
                            self.depth -= 1;
                            r
                        }
                    }
                }
            }
        };
        if self.cfg.proj_memo {
            self.proj_memo.insert((h, tr, name), out);
        }
        out
    }

    // §5.1's flags byte + §4.1's `subst_norm`.
    fn subst_norm(&mut self, ty: TyId, owner: u32, slots: ArgsId, tr: TraitRefId) -> Option<TyId> {
        self.c.subst_calls += 1;
        // The whole point of the flags byte: a monomorphic type is one load.
        if self.w.store.flags[ty.0 as usize] == 0 {
            return Some(ty);
        }
        let bind = self.w.store.binding_id(owner, slots);
        if self.cfg.subst_memo {
            self.c.subst_memo_lookups += 1;
            let hit = match self.cfg.key {
                KeyKind::DesignTraitRef => self.subst_memo_tr.get(&(ty, tr)).copied(),
                KeyKind::InternedBinding => self.subst_memo_b.get(&(ty, bind)).copied(),
            };
            if let Some(t) = hit {
                return Some(t);
            }
            self.c.subst_memo_misses += 1;
        }
        let out = self.subst_uncached(ty, owner, slots, tr)?;
        if self.cfg.subst_memo {
            match self.cfg.key {
                KeyKind::DesignTraitRef => {
                    self.subst_memo_tr.insert((ty, tr), out);
                }
                KeyKind::InternedBinding => {
                    self.subst_memo_b.insert((ty, bind), out);
                }
            }
        }
        Some(out)
    }

    fn subst_uncached(&mut self, ty: TyId, owner: u32, slots: ArgsId, tr: TraitRefId) -> Option<TyId> {
        let i = ty.0 as usize;
        let (tag, a, b) = (self.w.store.tag[i], self.w.store.a[i], self.w.store.b[i]);
        match tag {
            T_PARAM => {
                if a == owner {
                    let v = self.w.store.args(slots)[b as usize];
                    if v == NONE_TY { None } else { Some(v) }
                } else {
                    Some(ty) // a rigid parameter of some other declaration
                }
            }
            T_NOMINAL => {
                let mut xs = self.w.store.args_vec(ArgsId(b));
                for x in xs.iter_mut() {
                    *x = self.subst_norm(*x, owner, slots, tr)?;
                }
                Some(self.w.store.nominal(a, &xs))
            }
            T_PROJ => {
                let head = TyId(a);
                let (ptr, name) = self.w.store.proj_keys[b as usize];
                let (trait_id, targs) = self.w.store.trait_refs[ptr.0 as usize];
                let mut ts = self.w.store.args_vec(targs);
                for t in ts.iter_mut() {
                    *t = self.subst_norm(*t, owner, slots, tr)?;
                }
                let ta2 = self.w.store.intern_args(&ts);
                let ptr2 = self.w.store.trait_ref(trait_id, ta2);
                let h2 = self.subst_norm(head, owner, slots, tr)?;
                if self.w.store.is_rigid(h2) {
                    let pk = self.w.store.proj_key(ptr2, name);
                    Some(self.w.store.proj(h2, pk))
                } else {
                    self.normalise_proj(h2, ptr2, name)
                }
            }
            _ => Some(ty),
        }
    }

    // §7.6
    fn impl_lookup(&mut self, tr: TraitRefId, x: TyId) -> Option<(usize, ArgsId)> {
        let (trait_id, targs) = self.w.store.trait_refs[tr.0 as usize];
        let hk = self.w.store.head_key(x);
        let (lo, hi) = self.w.bucket(trait_id, hk);
        for slot in lo..hi {
            self.c.bucket_rows += 1;
            let row = self.w.index[slot].2 as usize;
            let nslots = self.w.impls[row].nslots as usize;
            let owner = self.w.impls[row].def;
            let i_targs = self.w.impls[row].trait_args;
            let self_ty = self.w.impls[row].self_ty;
            let mut bound = vec![NONE_TY; nslots];
            let ok = self.match_list(i_targs, targs, owner, &mut bound)
                && self.one_way_match(self_ty, x, owner, &mut bound);
            if ok && bound.iter().all(|s| *s != NONE_TY) {
                let id = self.w.store.intern_args(&bound);
                return Some((row, id));
            }
        }
        None
    }

    fn match_list(&mut self, p: ArgsId, a: ArgsId, owner: u32, bound: &mut Vec<TyId>) -> bool {
        let ps = self.w.store.args_vec(p);
        let as_ = self.w.store.args_vec(a);
        if ps.len() != as_.len() {
            return false;
        }
        for k in 0..ps.len() {
            if !self.one_way_match(ps[k], as_[k], owner, bound) {
                return false;
            }
        }
        true
    }

    /// ch09 Definitions, one-way match: unbound parameters of `owner` in `p`
    /// bind to the facing subterm of `a`; anything else must be equal; a
    /// projection on a still-unbound parameter faces anything and binds
    /// nothing; nothing in `a` is ever bound.
    fn one_way_match(&mut self, p: TyId, a: TyId, owner: u32, bound: &mut Vec<TyId>) -> bool {
        self.c.match_steps += 1;
        if p == a {
            return true; // hash-consing makes equality one integer compare
        }
        let i = p.0 as usize;
        let (ptag, pa, pb) = (self.w.store.tag[i], self.w.store.a[i], self.w.store.b[i]);
        match ptag {
            T_PARAM if pa == owner => {
                let s = &mut bound[pb as usize];
                if *s == NONE_TY {
                    *s = a;
                    true
                } else {
                    *s == a
                }
            }
            T_PROJ => {
                if self.proj_head_unbound(p, owner, bound) {
                    true // skipped; R38(e) compares it later
                } else {
                    false // p == a was already tested
                }
            }
            T_NOMINAL => {
                let j = a.0 as usize;
                if self.w.store.tag[j] != T_NOMINAL || self.w.store.a[j] != pa {
                    return false;
                }
                self.match_list(ArgsId(pb), ArgsId(self.w.store.b[j]), owner, bound)
            }
            _ => false,
        }
    }

    fn proj_head_unbound(&self, mut p: TyId, owner: u32, bound: &[TyId]) -> bool {
        loop {
            let i = p.0 as usize;
            match self.w.store.tag[i] {
                T_PROJ => p = TyId(self.w.store.a[i]),
                T_PARAM => {
                    let (o, ord) = (self.w.store.a[i], self.w.store.b[i]);
                    return o == owner && bound[ord as usize] == NONE_TY;
                }
                _ => return false,
            }
        }
    }
}

// ---------------------------------------------------------------- scenarios

/// `Iter[C_j]` world: `Vec[T]`, and the `Skip`/`Map`/`Filter`/`Dup` adaptors,
/// each with `k` impl rows in its bucket (one per config tag `C_j`, which is
/// the trait's own argument — R19-legal, since the trait arguments differ).
fn adaptor_world(k: usize) -> World {
    let mut w = World::new();
    let mut def = 10_000u32;
    for j in 0..k {
        let c = w.store.nominal(CFG + j as u32, &[]);
        // impl Iter[C_j] for Vec[T] { type Item = T; }
        let t = w.store.param(def, 0);
        let self_ty = w.store.nominal(VEC, &[t]);
        w.add_impl(def, TR_ITER, &[c], self_ty, 1, vec![(NAME_ITEM, t)]);
        def += 1;
        // impl Iter[C_j] for Skip/Map/Filter[I] { type Item = I.Item; }
        for head in [SKIP, MAP, FILTER] {
            let i = w.store.param(def, 0);
            let self_ty = w.store.nominal(head, &[i]);
            let rhs = w.store.proj_of(i, TR_ITER, &[c], NAME_ITEM);
            w.add_impl(def, TR_ITER, &[c], self_ty, 1, vec![(NAME_ITEM, rhs)]);
            def += 1;
        }
        // impl Iter[C_j] for Dup[I] { type Item = Pair[I.Item, I.Item]; }
        // The invented fan-out: the right-hand side names the SAME projection
        // twice, so an unmemoised normaliser is 2^depth.
        let i = w.store.param(def, 0);
        let self_ty = w.store.nominal(DUP, &[i]);
        let inner = w.store.proj_of(i, TR_ITER, &[c], NAME_ITEM);
        let rhs = w.store.nominal(PAIR, &[inner, inner]);
        w.add_impl(def, TR_ITER, &[c], self_ty, 1, vec![(NAME_ITEM, rhs)]);
        def += 1;
    }
    w.finish();
    w
}

/// Two mutually recursive traits: `impl A for W1[X] { type Ta = X.Tb; }` and
/// `impl B for W2[Y] { type Tb = Y.Ta; }`, grounded on `Vec[T]`.
fn mutual_world() -> World {
    let mut w = World::new();
    let mut def = 20_000u32;
    for (tr, name) in [(TR_A, NAME_TA), (TR_B, NAME_TB)] {
        let t = w.store.param(def, 0);
        let self_ty = w.store.nominal(VEC, &[t]);
        w.add_impl(def, tr, &[], self_ty, 1, vec![(name, t)]);
        def += 1;
    }
    // A for W1 goes through B; B for W2 goes through A.
    let x = w.store.param(def, 0);
    let self_ty = w.store.nominal(W1, &[x]);
    let rhs = w.store.proj_of(x, TR_B, &[], NAME_TB);
    w.add_impl(def, TR_A, &[], self_ty, 1, vec![(NAME_TA, rhs)]);
    def += 1;
    let y = w.store.param(def, 0);
    let self_ty = w.store.nominal(W2, &[y]);
    let rhs = w.store.proj_of(y, TR_A, &[], NAME_TA);
    w.add_impl(def, TR_B, &[], self_ty, 1, vec![(NAME_TB, rhs)]);
    w.finish();
    w
}

// MARC (verification round, 2026-09-20): three shapes the implementer did not
// try, added by the adversarial verifier. Each is a question the memo keys
// must answer correctly AND cheaply; the counters below say which they do.

/// Shape X — a right-hand side that names the SAME head under a DIFFERENT
/// trait: `impl A for W[I] { type Ta = Pair[I.Ta, I.Tb]; }` and
/// `impl B for W[I] { type Tb = Pair[I.Tb, I.Ta]; }`, grounded on `Vec[T]`.
/// Every level asks both associated types of its subterm, so an unmemoised
/// normaliser is `2^depth`; the `(head, TraitRef, name)` key must hold two
/// entries per level and no more.
fn cross_trait_world() -> World {
    let mut w = World::new();
    let mut def = 30_000u32;
    for (tr, name) in [(TR_A, NAME_TA), (TR_B, NAME_TB)] {
        let t = w.store.param(def, 0);
        let self_ty = w.store.nominal(VEC, &[t]);
        w.add_impl(def, tr, &[], self_ty, 1, vec![(name, t)]);
        def += 1;
    }
    for (tr, name) in [(TR_A, NAME_TA), (TR_B, NAME_TB)] {
        let i = w.store.param(def, 0);
        let self_ty = w.store.nominal(W1, &[i]);
        let mine = w.store.proj_of(i, tr, &[], name);
        let (other_tr, other_name) = if tr == TR_A { (TR_B, NAME_TB) } else { (TR_A, NAME_TA) };
        let theirs = w.store.proj_of(i, other_tr, &[], other_name);
        let rhs = w.store.nominal(PAIR, &[mine, theirs]);
        w.add_impl(def, tr, &[], self_ty, 1, vec![(name, rhs)]);
        def += 1;
    }
    w.finish();
    w
}

fn run_cross(depth: usize, cfg: Cfg) -> Run {
    let mut w = cross_trait_world();
    let i32_ty = w.store.prim(PRIM_I32);
    let mut t = w.store.nominal(VEC, &[i32_ty]);
    for _ in 0..depth {
        t = w.store.nominal(W1, &[t]);
    }
    let empty = w.store.intern_args(&[]);
    let tr = w.store.trait_ref(TR_A, empty);
    let mut e = Engine::new(w, cfg);
    let result = e.normalise_proj(t, tr, NAME_TA);
    Run { c: e.c, result }
}

/// Shape Y — a right-hand side that projects on its own parameter under a
/// GROWN trait argument. With the trait argument generic (a blanket trait
/// parameter, which R19 permits because the self type is still nominal):
/// `impl[I, C] Iter[C] for Grow[I] { type Item = Pair[I.Iter[C].Item,
/// I.Iter[Pair[C, C]].Item]; }`, grounded on `impl[T, C] Iter[C] for Vec[T] {
/// type Item = T; }`. Level `j` of a depth-`d` chain is asked under every
/// argument `Pair^m[C]` for `m <= d - j`, so there are `d^2 / 2` DISTINCT
/// `(head, TraitRef, name)` questions. No memo key can make that linear:
/// the questions really are different. This is the shape that bounds
/// "linear in chain depth" to "linear when the set of trait arguments a chain
/// is asked under is bounded" — and the reason I6 needs a per-query work
/// budget, not only a depth counter.
fn grown_arg_world() -> World {
    let mut w = World::new();
    let def = 40_000u32;
    let t = w.store.param(def, 0);
    let c = w.store.param(def, 1);
    let self_ty = w.store.nominal(VEC, &[t]);
    w.add_impl(def, TR_ITER, &[c], self_ty, 2, vec![(NAME_ITEM, t)]);
    let def = def + 1;
    let i = w.store.param(def, 0);
    let c = w.store.param(def, 1);
    let self_ty = w.store.nominal(GROW, &[i]);
    let same = w.store.proj_of(i, TR_ITER, &[c], NAME_ITEM);
    let cc = w.store.nominal(PAIR, &[c, c]);
    let grown = w.store.proj_of(i, TR_ITER, &[cc], NAME_ITEM);
    let rhs = w.store.nominal(PAIR, &[same, grown]);
    w.add_impl(def, TR_ITER, &[c], self_ty, 2, vec![(NAME_ITEM, rhs)]);
    w.finish();
    w
}

fn run_grown(depth: usize, cfg: Cfg) -> Run {
    let mut w = grown_arg_world();
    let i32_ty = w.store.prim(PRIM_I32);
    let mut t = w.store.nominal(VEC, &[i32_ty]);
    for _ in 0..depth {
        t = w.store.nominal(GROW, &[t]);
    }
    let c = w.store.nominal(CFG, &[]);
    let ca = w.store.intern_args(&[c]);
    let tr = w.store.trait_ref(TR_ITER, ca);
    let mut e = Engine::new(w, cfg);
    let result = e.normalise_proj(t, tr, NAME_ITEM);
    Run { c: e.c, result }
}

/// Shape Z — every impl in the bucket has the SAME `(trait, HeadKey)` and the
/// same trait arguments, differing only deep inside the self type:
/// `impl Iter[C0] for Vec^j[i32] { type Item = i32; }` for `j = 1..=k`.
/// `HeadKey::Nominal(Vec)` cannot tell them apart, so the scan visits all `k`
/// rows, and a row that does NOT match costs a walk down to the first
/// differing subterm, i.e. `min(j, k)` steps — `k^2 / 2` match steps for one
/// query. The equal row is one integer compare (hash-consing), so an exact
/// `(trait, self TyId)` pre-lookup before the bucket scan would make every
/// concrete impl O(1). §7.6's `distinct_subterms(x) * bucket_len` budget is
/// exactly `k * k` here, so the design already bounds it; the counters say
/// how close a plain corpus can get to that bound.
fn colliding_bucket_world(k: usize) -> (World, TyId) {
    let mut w = World::new();
    let c = w.store.nominal(CFG, &[]);
    let i32_ty = w.store.prim(PRIM_I32);
    let mut t = w.store.nominal(VEC, &[i32_ty]);
    let mut deepest = t;
    for j in 0..k {
        w.add_impl(50_000 + j as u32, TR_ITER, &[c], t, 0, vec![(NAME_ITEM, i32_ty)]);
        deepest = t;
        t = w.store.nominal(VEC, &[t]);
    }
    w.finish();
    (w, deepest)
}

fn run_colliding(k: usize, cfg: Cfg) -> Run {
    let (mut w, deepest) = colliding_bucket_world(k);
    let c = w.store.nominal(CFG, &[]);
    let ca = w.store.intern_args(&[c]);
    let tr = w.store.trait_ref(TR_ITER, ca);
    let mut e = Engine::new(w, cfg);
    let result = e.normalise_proj(deepest, tr, NAME_ITEM);
    Run { c: e.c, result }
}

fn chain(w: &mut World, depth: usize, heads: &[u32]) -> TyId {
    let i32_ty = w.store.prim(PRIM_I32);
    let mut t = w.store.nominal(VEC, &[i32_ty]);
    for d in 0..depth {
        t = w.store.nominal(heads[d % heads.len()], &[t]);
    }
    t
}

struct Run {
    c: Counters,
    result: Option<TyId>,
}

fn run_adaptor(depth: usize, k: usize, heads: &[u32], cfg: Cfg) -> Run {
    let mut w = adaptor_world(k);
    let t = chain(&mut w, depth, heads);
    // Ask for the LAST config tag so the bucket scan is worst case.
    let c = w.store.nominal(CFG + (k as u32 - 1), &[]);
    let ca = w.store.intern_args(&[c]);
    let tr = w.store.trait_ref(TR_ITER, ca);
    let mut e = Engine::new(w, cfg);
    let result = e.normalise_proj(t, tr, NAME_ITEM);
    Run { c: e.c, result }
}

fn run_mutual(depth: usize, cfg: Cfg) -> Run {
    let mut w = mutual_world();
    let i32_ty = w.store.prim(PRIM_I32);
    let mut t = w.store.nominal(VEC, &[i32_ty]);
    // Alternate W1/W2 so each level crosses to the other trait.
    for d in 0..depth {
        t = w.store.nominal(if d % 2 == 0 { W2 } else { W1 }, &[t]);
    }
    let want_trait = if depth % 2 == 0 { TR_A } else { TR_A };
    let empty = w.store.intern_args(&[]);
    let tr = w.store.trait_ref(want_trait, empty);
    let name = NAME_TA;
    let mut e = Engine::new(w, cfg);
    // The outermost wrapper is W1 when depth is even>0 ... resolve whichever
    // trait actually has an impl for the outermost head.
    let outer = e.w.store.a[t.0 as usize];
    let (tr, name) = if outer == W2 {
        let empty = e.w.store.intern_args(&[]);
        (e.w.store.trait_ref(TR_B, empty), NAME_TB)
    } else {
        (tr, name)
    };
    let result = e.normalise_proj(t, tr, name);
    Run { c: e.c, result }
}

// ------------------------------------------------------------- the witness

/// Two self types, ONE trait ref: the case the design's written substitution
/// memo key cannot tell apart.
fn soundness_witness(key: KeyKind) -> (Option<TyId>, Option<TyId>, TyId, TyId) {
    let mut w = adaptor_world(1);
    let i32_ty = w.store.prim(PRIM_I32);
    let u8_ty = w.store.prim(PRIM_U8);
    let v_i32 = w.store.nominal(VEC, &[i32_ty]);
    let v_u8 = w.store.nominal(VEC, &[u8_ty]);
    let c = w.store.nominal(CFG, &[]);
    let ca = w.store.intern_args(&[c]);
    let tr = w.store.trait_ref(TR_ITER, ca);
    let mut e = Engine::new(w, Cfg { key, proj_memo: true, subst_memo: true });
    let first = e.normalise_proj(v_i32, tr, NAME_ITEM);
    let second = e.normalise_proj(v_u8, tr, NAME_ITEM);
    (first, second, i32_ty, u8_ty)
}

// ------------------------------------------------------------------- report

fn row(label: String, c: Counters) -> String {
    format!(
        "| {:<22} | {:>6} | {:>6} | {:>7} | {:>7} | {:>7} | {:>7} |",
        label, c.proj_calls, c.proj_memo_misses, c.subst_calls, c.subst_memo_misses, c.match_steps, c.bucket_rows
    )
}

fn header(title: &str) {
    println!("\n{}", title);
    println!(
        "| {:<22} | {:>6} | {:>6} | {:>7} | {:>7} | {:>7} | {:>7} |",
        "case", "proj", "pmiss", "subst", "smiss", "match", "bucket"
    );
    println!("|{:-<24}|{:-<8}|{:-<8}|{:-<9}|{:-<9}|{:-<9}|{:-<9}|", "", "", "", "", "", "", "");
}

fn main() {
    let cfg = Cfg::sound();
    let mut failures: Vec<String> = Vec::new();

    // --- 1. linearity in chain depth -------------------------------------
    header("Table 1 — Skip/Map/Filter chain, k = 8 impls per (trait, head)");
    let mut depth_rows: Vec<(usize, Counters)> = Vec::new();
    for &d in &[1usize, 2, 4, 8, 16, 32, 64] {
        let r = run_adaptor(d, 8, &[SKIP, MAP, FILTER], cfg);
        if r.result.is_none() {
            failures.push(format!("chain depth {d}: no result"));
        }
        println!("{}", row(format!("depth {d}"), r.c));
        depth_rows.push((d, r.c));
    }
    // Linear means doubling the depth roughly doubles the work, never squares it.
    for wnd in depth_rows.windows(2) {
        let (d0, c0) = wnd[0];
        let (d1, c1) = wnd[1];
        if d1 == 2 * d0 {
            let ratio = c1.subst_calls as f64 / c0.subst_calls as f64;
            if ratio > 2.6 {
                failures.push(format!("subst_calls superlinear from depth {d0} to {d1}: x{ratio:.2}"));
            }
            let ratio = c1.proj_calls as f64 / c0.proj_calls as f64;
            if ratio > 2.6 {
                failures.push(format!("proj_calls superlinear from depth {d0} to {d1}: x{ratio:.2}"));
            }
        }
    }

    // --- 2. independence of k --------------------------------------------
    header("Table 2 — depth 64 chain, k impls per (trait, head)");
    let mut k_rows: Vec<(usize, Counters)> = Vec::new();
    for &k in &[1usize, 8, 64, 512] {
        let r = run_adaptor(64, k, &[SKIP, MAP, FILTER], cfg);
        if r.result.is_none() {
            failures.push(format!("k = {k}: no result"));
        }
        println!("{}", row(format!("k = {k}"), r.c));
        k_rows.push((k, r.c));
    }
    let base = k_rows[0].1;
    for &(k, c) in &k_rows {
        if (c.proj_calls, c.proj_memo_misses, c.subst_calls, c.subst_memo_misses)
            != (base.proj_calls, base.proj_memo_misses, base.subst_calls, base.subst_memo_misses)
        {
            failures.push(format!("k = {k}: normalisation counters moved with k"));
        }
    }

    // --- 3. mutual recursion across two traits ---------------------------
    header("Table 3 — mutually recursive impls across traits A and B");
    for &d in &[2usize, 8, 32, 64] {
        let r = run_mutual(d, cfg);
        if r.result.is_none() {
            failures.push(format!("mutual depth {d}: no result"));
        }
        println!("{}", row(format!("depth {d}"), r.c));
    }

    // --- 4. the invented worst case: fan-out 2 per level ----------------
    header("Table 4 — Dup chain (RHS names the same projection twice), memo ON");
    for &d in &[4usize, 8, 16, 32, 64] {
        let r = run_adaptor(d, 8, &[DUP], cfg);
        if r.result.is_none() {
            failures.push(format!("dup depth {d}: no result"));
        }
        println!("{}", row(format!("depth {d}"), r.c));
    }
    header("Table 5 — the same chain with the projection memo OFF (2^depth)");
    for &d in &[4usize, 8, 12, 16, 18] {
        let r = run_adaptor(d, 8, &[DUP], Cfg { key: KeyKind::InternedBinding, proj_memo: false, subst_memo: false });
        println!("{}", row(format!("depth {d}"), r.c));
    }

    // --- 5. the worst case, everything at once ---------------------------
    header("Table 6 — worst case: Dup fan-out, depth 64, k = 512");
    let worst = run_adaptor(64, 512, &[DUP], cfg);
    println!("{}", row("depth 64, k = 512".to_string(), worst.c));
    if worst.result.is_none() {
        failures.push("worst case: no result".to_string());
    }

    // --- 7. (verifier) same head under a different trait -----------------
    header("Table 7 — Shape X: RHS names the same head under the other trait, memo ON");
    let mut x_rows: Vec<(usize, Counters)> = Vec::new();
    for &d in &[1usize, 2, 4, 8, 16, 32, 64] {
        let r = run_cross(d, cfg);
        if r.result.is_none() {
            failures.push(format!("shape X depth {d}: no result"));
        }
        println!("{}", row(format!("depth {d}"), r.c));
        x_rows.push((d, r.c));
    }
    for wnd in x_rows.windows(2) {
        let (d0, c0) = wnd[0];
        let (d1, c1) = wnd[1];
        let ratio = c1.proj_calls as f64 / c0.proj_calls as f64;
        if ratio > 2.6 {
            failures.push(format!("shape X proj_calls superlinear from depth {d0} to {d1}: x{ratio:.2}"));
        }
    }
    header("Table 7b — Shape X with the projection memo OFF (2^depth)");
    for &d in &[4usize, 8, 12, 16] {
        let r = run_cross(d, Cfg { key: KeyKind::InternedBinding, proj_memo: false, subst_memo: false });
        println!("{}", row(format!("depth {d}"), r.c));
    }

    // --- 8. (verifier) grown trait argument: inherently quadratic --------
    header("Table 8 — Shape Y: RHS projects under a GROWN trait argument, memo ON");
    let mut y_rows: Vec<(usize, Counters)> = Vec::new();
    for &d in &[1usize, 2, 4, 8, 16, 32, 64] {
        let r = run_grown(d, cfg);
        if r.result.is_none() {
            failures.push(format!("shape Y depth {d}: no result"));
        }
        println!("{}", row(format!("depth {d}"), r.c));
        y_rows.push((d, r.c));
    }
    // The finding, pinned: distinct memo misses are Θ(d²) — (d+1)(d+2)/2 —
    // because the questions are distinct. A memo that made this linear would
    // be answering a question it was not asked.
    for &(d, c) in &y_rows {
        let expect = ((d + 1) * (d + 2) / 2) as u64;
        if c.proj_memo_misses != expect {
            failures.push(format!(
                "shape Y depth {d}: expected exactly {expect} distinct projection questions, saw {}",
                c.proj_memo_misses
            ));
        }
    }
    println!("FINDING: shape Y is Θ(depth²) in DISTINCT questions with every memo on — linear-in-depth holds only");
    println!("         while the set of trait arguments a chain is asked under stays bounded. I6 needs a per-query");
    println!("         work budget (memo misses per top-level normalise), not only NORMALISE_DEPTH_MAX.");

    // --- 9. (verifier) every impl in one bucket --------------------------
    header("Table 9 — Shape Z: k impls in ONE (trait, HeadKey) bucket, distinguished only deep in the self type");
    for &k in &[1usize, 8, 64, 512] {
        let r = run_colliding(k, cfg);
        if r.result.is_none() {
            failures.push(format!("shape Z k = {k}: no result"));
        }
        println!("{}", row(format!("k = {k}"), r.c));
        // Bucket rows = k; match steps ≈ k²/2 (each non-matching row walks to
        // the first differing subterm). Pin the shape so a future ImplIndex
        // that adds an exact pre-lookup shows up as a change here.
        if r.c.bucket_rows != k as u64 {
            failures.push(format!("shape Z k = {k}: bucket rows {} != k", r.c.bucket_rows));
        }
        let lower = (k * (k - 1) / 2) as u64;
        if r.c.match_steps < lower {
            failures.push(format!("shape Z k = {k}: match steps {} below the k(k-1)/2 the scan implies", r.c.match_steps));
        }
    }
    println!("FINDING: shape Z costs k²/2 match steps per query (k = 512 → see above) against a bucket of k rows;");
    println!("         an exact (trait, self TyId) map consulted before the scan makes every concrete impl one probe.");

    // --- 6. the memo-key witness ----------------------------------------
    println!("\nMemo-key soundness witness — `Vec[i32].Item` then `Vec[u8].Item`,");
    println!("one trait ref `Iter[C_0]`, two self types:");
    for key in [KeyKind::DesignTraitRef, KeyKind::InternedBinding] {
        let (a, b, i32_ty, u8_ty) = soundness_witness(key);
        let ok = a == Some(i32_ty) && b == Some(u8_ty);
        println!("  {:<18} -> first = {:?}, second = {:?}  {}", format!("{key:?}"), a, b, if ok { "SOUND" } else { "WRONG ANSWER" });
        if key == KeyKind::DesignTraitRef && ok {
            failures.push("the (TyId, TraitRefId) key did NOT misbehave — witness is stale".to_string());
        }
        if key == KeyKind::InternedBinding && !ok {
            failures.push("the (TyId, BindingId) key gave a wrong answer".to_string());
        }
    }

    println!();
    if failures.is_empty() {
        println!("VERDICT: all assertions hold.");
    } else {
        for f in &failures {
            println!("FAILURE: {f}");
        }
        std::process::exit(1);
    }
}
