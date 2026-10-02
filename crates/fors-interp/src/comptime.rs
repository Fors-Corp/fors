//! Comptime mode (design §6; ch04 R11-R15; ch06; ch10 R42) — F9.
//!
//! **One engine** (ch04 R11, PLAN R8): comptime is this interpreter's own
//! dispatch loop with a different environment, never a second evaluator. The
//! comptime [`ComptimeEnv`] differs from run mode in exactly design §6's
//! rows:
//!
//! | Aspect | Comptime |
//! |---|---|
//! | Capability table | **empty**: the entry shim constructs nothing, and a root-capability parameter of the enclosing function has no comptime value |
//! | Intrinsics | only the table rows whose `comptime` cell is `Allowed` ([`crate::intrinsic`]); a `Forbidden` one is [`ComptimeFault::ForbiddenIntrinsic`], a build error naming it and the site — never a host call |
//! | Declared inputs | [`DeclaredInputs`]: the module header's `inputs { ... };` paths, read ONCE by the build and content-hashed BEFORE evaluation; `input_read` reads only this map |
//! | Budgets | [`crate::budget`]: steps per instruction, bytes per allocation, and the build-wide cap |
//! | Address observation | tracked; the value observed is SYNTHETIC — `(AllocId << 32) \| offset` — and sets [`Evaluation::observed_address`], the tier-up bar of ch04 R15 |
//! | Result | a content-addressed [`MemoEntry`] keyed by [`memo_key`] |
//!
//! **No host is read in comptime mode** (ch04 R12, ch06): the oracle a
//! comptime machine holds is [`crate::host::Oracle::sealed`] (an empty
//! replay: no real clock or entropy CAN be read), the forbidden doors never
//! run, and this file opens no file — the declared inputs arrive as bytes the
//! build already read. `comptime_reads_no_host` asserts the counters after
//! every evaluation; `comptime_module_opens_no_file` greps this source.
//!
//! **The memo is content-addressed** ([`memo_key`]): `hash(target_hash ‖
//! fmir_hash of every declaration in the evaluation's transitive call graph,
//! in reach order, with its string and intrinsic side tables ‖ every
//! declared input's (path, content hash) ‖ the per-evaluation budget)`. No
//! name, path on disk, timestamp or process state enters it, so two
//! processes building the same sources compute the same key and the
//! byte-identical [`MemoEntry::to_bytes`].

use fors_fir::DeclKeyId;
use fors_fir::ty::TyStore;
use fors_fmir::inst::Callee;
use fors_index::diag::Code;

use crate::budget::{BuildMeter, Exceeded, Limits, Meter};
use crate::exec::{Exit, InterpError};
use crate::program::{Config, Endian, Program};

/// The layout rule's version (owner Q1, `fors-layout`): part of
/// [`target_hash`], because `@size_of` and every aggregate's shape depend on
/// it, so a memo row computed under one rule must not answer for another.
pub const LAYOUT_RULE_VERSION: u32 = 1;

/// One declared comptime input: its header path, its bytes, and their
/// content hash (ch04 R13's content-hashed build-graph edge).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DeclaredInput {
    pub path: Vec<u8>,
    pub bytes: Vec<u8>,
    pub hash: u128,
}

/// A module's declared inputs, resolved to bytes and hashes before any
/// evaluation (design §6's "resolved to content hashes before evaluation").
/// Sorted by path, so the memo key does not depend on header order.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct DeclaredInputs {
    rows: Vec<DeclaredInput>,
}

impl DeclaredInputs {
    /// No declared inputs (a module with no `inputs` clause).
    pub fn empty() -> DeclaredInputs {
        DeclaredInputs::default()
    }

    /// `(path, bytes)` pairs the build read, each exactly once. A path given
    /// twice keeps its first bytes (the build reads each path once).
    pub fn new(pairs: Vec<(Vec<u8>, Vec<u8>)>) -> DeclaredInputs {
        let mut rows: Vec<DeclaredInput> = Vec::with_capacity(pairs.len());
        for (path, bytes) in pairs {
            if rows.iter().any(|r| r.path == path) {
                continue;
            }
            let hash = fors_index::fingerprint::hash_bytes(&bytes);
            rows.push(DeclaredInput { path, bytes, hash });
        }
        rows.sort_by(|a, b| a.path.cmp(&b.path));
        DeclaredInputs { rows }
    }

    pub fn get(&self, path: &[u8]) -> Option<&DeclaredInput> {
        self.rows.iter().find(|r| r.path == path)
    }

    pub fn rows(&self) -> &[DeclaredInput] {
        &self.rows
    }
}

/// The comptime environment one evaluation runs in (design §6's table).
pub struct ComptimeEnv<'e> {
    /// The enclosing module's declared inputs.
    pub inputs: &'e DeclaredInputs,
    pub limits: Limits,
    /// `(key, name)` of every `extern` declaration in the build: a
    /// `call_direct` to one of these is a SEALED operation (ch04 R2a), which
    /// comptime never reaches (R2a: "sealing never exempts comptime").
    pub externs: &'e [(DeclKeyId, String)],
}

/// The comptime half of the machine's state, owned by the machine for one
/// evaluation.
pub(crate) struct CtState {
    pub(crate) meter: Meter,
    pub(crate) inputs: DeclaredInputs,
    pub(crate) externs: Vec<(DeclKeyId, String)>,
    pub(crate) observed_address: bool,
    /// Declared paths `input_read` served, in first-read order.
    pub(crate) inputs_read: Vec<Vec<u8>>,
}

/// A fault only comptime mode raises. Carried out of the dispatch loop as
/// [`InterpError::Comptime`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ComptimeFault {
    /// ch04 R12: an intrinsic whose `comptime` column is `Forbidden`.
    ForbiddenIntrinsic {
        intrinsic: String,
        design: &'static str,
        /// The function the door was reached in.
        func: String,
        /// That instruction's `(line, col)` (0:0 for lowered FMIR, whose
        /// instructions carry `SiteId(0)` today).
        site: (u32, u32),
    },
    /// ch04 R13: `input_read` of a path the module header does not declare.
    UndeclaredInput {
        path: String,
        func: String,
        site: (u32, u32),
    },
    /// ch04 R14 / owner Q6: a budget tripped.
    Budget(Exceeded),
    /// ch04 R2a, R12: a call to an `extern` (sealed, `ffi`) function.
    SealedCall { callee: String, func: String },
}

impl std::fmt::Display for ComptimeFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComptimeFault::ForbiddenIntrinsic {
                intrinsic,
                design,
                func,
                site,
            } => write!(
                f,
                "reached intrinsic `{intrinsic}` ({design}) in `{func}` at {}:{}, which the \
                 intrinsic table forbids at comptime: no capability value, \
                 clock, RNG, env read or ambient I/O is reachable (ch04 R12)",
                site.0, site.1
            ),
            ComptimeFault::UndeclaredInput { path, func, site } => write!(
                f,
                "read the comptime input \"{path}\" (intrinsic `input_read` in `{func}` at {}:{}), \
                 which is not declared in the module header's `inputs {{ ... }};` clause (ch04 R13)",
                site.0, site.1
            ),
            ComptimeFault::Budget(e) => write!(f, "{}", describe_exceeded(e)),
            ComptimeFault::SealedCall { callee, func } => write!(
                f,
                "reached the sealed operation `{callee}` (an `extern` \
                 function, called from `{func}`); sealing never exempts comptime (ch04 R2a, R12)"
            ),
        }
    }
}

fn describe_exceeded(e: &Exceeded) -> String {
    match e {
        Exceeded::Steps { steps, limit } => format!(
            "exceeded COMPTIME_STEP_BUDGET: {steps} steps charged against a budget of {limit} \
             (ch04 R14)"
        ),
        Exceeded::Bytes { bytes, limit } => format!(
            "exceeded COMPTIME_ALLOC_BUDGET: {bytes} bytes charged against a budget of {limit} \
             (ch04 R14)"
        ),
        Exceeded::Build {
            build_steps,
            limit,
            most_expensive,
        } => {
            let who = most_expensive
                .as_ref()
                .map(|(d, s)| format!("; the most expensive declaration is `{d}` at {s} steps"))
                .unwrap_or_default();
            format!(
                "exceeded COMPTIME_BUILD_STEP_BUDGET: the build charged {build_steps} comptime \
                 steps against a cap of {limit}{who} (owner Q6)"
            )
        }
    }
}

/// One successful evaluation: the canonical result plus its counters.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Evaluation {
    /// The canonical encoding of the result ([`encode`]'s format).
    pub value: Vec<u8>,
    pub steps: u64,
    pub bytes: u64,
    /// ch04 R15: did the evaluation observe an address (a pointer-to-
    /// integer conversion or a cross-allocation pointer comparison)?
    pub observed_address: bool,
    /// `(path, content hash)` of every declared input the evaluation read.
    pub inputs_read: Vec<(Vec<u8>, u128)>,
}

impl Evaluation {
    /// ch04 R15 / design §6: a body may tier up iff no address was observed
    /// over its whole transitive comptime call graph — which is exactly one
    /// evaluation, because the evaluation runs that whole graph.
    pub fn tier_up_eligible(&self) -> bool {
        !self.observed_address
    }
}

/// Why a comptime evaluation is a build error. Every variant is NAMED: a
/// shape the engine cannot evaluate is reported, never deferred to run time.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ErrorKind {
    Fault(ComptimeFault),
    /// A ch02 R15 trap during evaluation.
    Trap {
        kind: fors_fmir::op::TrapKind,
        site: (u32, u32),
    },
    /// A design §5.2 `ub:` report during evaluation — e.g. a read of a
    /// run-time parameter, which has no comptime value.
    Ub(crate::ub::UbReport),
    /// An error left the comptime block.
    Raise,
    /// The interpreter cannot evaluate this shape (an opcode outside its
    /// subset, a malformed program).
    Interp(InterpError),
    /// The result has no canonical encoding in this increment.
    Unencodable(String),
}

/// A comptime build error: which declaration, why, and the counts.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ComptimeError {
    /// The declaration whose comptime block was being evaluated.
    pub decl: String,
    pub kind: ErrorKind,
    pub steps: u64,
    pub bytes: u64,
}

impl ComptimeError {
    /// The ch04 rule this error is a violation of, as a diagnostic code.
    pub fn code(&self) -> Code {
        match &self.kind {
            ErrorKind::Fault(ComptimeFault::ForbiddenIntrinsic { .. }) => Code::A(12),
            ErrorKind::Fault(ComptimeFault::UndeclaredInput { .. }) => Code::A(13),
            ErrorKind::Fault(ComptimeFault::Budget(_)) => Code::A(14),
            ErrorKind::Fault(ComptimeFault::SealedCall { .. }) => Code::A(2),
            // ch04 R11: the one engine could not evaluate it.
            _ => Code::A(11),
        }
    }

    pub fn message(&self) -> String {
        let what = match &self.kind {
            ErrorKind::Fault(f) => f.to_string(),
            ErrorKind::Trap { kind, site } => {
                format!("trapped `{}` at {}:{}", kind.as_str(), site.0, site.1)
            }
            ErrorKind::Ub(r) => format!(
                "hit `ub: {}`: {} (a run-time binding has no comptime value; ch04 R12)",
                r.class.as_str(),
                r.detail
            ),
            ErrorKind::Raise => "an error left the comptime block".to_string(),
            ErrorKind::Interp(e) => format!("the comptime engine cannot evaluate this: {e}"),
            ErrorKind::Unencodable(w) => format!("the comptime result cannot be encoded: {w}"),
        };
        format!(
            "comptime evaluation of `{}`: {what} [steps {}, bytes {}]",
            self.decl, self.steps, self.bytes
        )
    }
}

/// `target_hash` (design §6): the `Target` (pointer width, endianness) and
/// the layout rule's version.
pub fn target_hash(cfg: &Config) -> u128 {
    let mut b = b"fors-target 1\0".to_vec();
    b.push(cfg.ptr_bits);
    b.push(match cfg.endian {
        Endian::Little => 0,
    });
    b.extend_from_slice(&LAYOUT_RULE_VERSION.to_le_bytes());
    fors_index::fingerprint::hash_bytes(&b)
}

/// A memo key: the content address of one evaluation.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct MemoKey(pub u128);

impl MemoKey {
    /// 32 lowercase hex digits.
    pub fn hex(self) -> String {
        format!("{:032x}", self.0)
    }
}

/// The program's functions reachable from `prog.entry` by `call_direct`, in
/// breadth-first reach order (deterministic: call rows are visited in pool
/// order). Unknown keys (an `extern`) are skipped — they have no FMIR.
fn reach(prog: &Program) -> Vec<usize> {
    let mut order = vec![prog.entry];
    let mut i = 0;
    while i < order.len() {
        let decl = &prog.fns[order[i]].decl;
        for row in &decl.insts.calls {
            if let Callee::Direct(key) = row.callee
                && let Some(t) = prog.fns.iter().position(|f| f.decl.decl == key)
                && !order.contains(&t)
            {
                order.push(t);
            }
        }
        i += 1;
    }
    order
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u64).to_le_bytes());
    out.extend_from_slice(b);
}

/// The content address of evaluating `prog.entry` under `inputs` and
/// `limits` on `target` (design §6's key; see the module docs).
pub fn memo_key(prog: &Program, target: u128, inputs: &DeclaredInputs, limits: &Limits) -> MemoKey {
    let mut b = b"fors-comptime-key 1\0".to_vec();
    b.extend_from_slice(&target.to_le_bytes());
    let order = reach(prog);
    b.extend_from_slice(&(order.len() as u64).to_le_bytes());
    for fi in order {
        let f = &prog.fns[fi];
        b.extend_from_slice(&fors_fmir::encode::fmir_hash(&f.decl).to_le_bytes());
        let mut strings = f.strings.clone();
        strings.sort();
        b.extend_from_slice(&(strings.len() as u64).to_le_bytes());
        for (id, bytes) in &strings {
            b.extend_from_slice(&id.to_le_bytes());
            put_bytes(&mut b, bytes);
        }
        let mut intr = f.intrinsics.clone();
        intr.sort();
        b.extend_from_slice(&(intr.len() as u64).to_le_bytes());
        for (sym, name) in &intr {
            b.extend_from_slice(&sym.to_le_bytes());
            put_bytes(&mut b, name.as_bytes());
        }
    }
    b.extend_from_slice(&(inputs.rows().len() as u64).to_le_bytes());
    for r in inputs.rows() {
        put_bytes(&mut b, &r.path);
        b.extend_from_slice(&r.hash.to_le_bytes());
    }
    b.extend_from_slice(&limits.step.to_le_bytes());
    b.extend_from_slice(&limits.alloc.to_le_bytes());
    MemoKey(fors_index::fingerprint::hash_bytes(&b))
}

/// One memo row: the key and what the evaluation produced.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MemoEntry {
    pub key: MemoKey,
    pub value: Vec<u8>,
    pub steps: u64,
    pub bytes: u64,
    pub observed_address: bool,
    pub inputs_read: Vec<(Vec<u8>, u128)>,
}

const MEMO_MAGIC: &[u8; 8] = b"FORSCTM1";

impl MemoEntry {
    pub fn new(key: MemoKey, ev: &Evaluation) -> MemoEntry {
        MemoEntry {
            key,
            value: ev.value.clone(),
            steps: ev.steps,
            bytes: ev.bytes,
            observed_address: ev.observed_address,
            inputs_read: ev.inputs_read.clone(),
        }
    }

    /// The canonical bytes: identical across processes and machines for
    /// the same key (every field is a deterministic function of it).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = MEMO_MAGIC.to_vec();
        out.extend_from_slice(&self.key.0.to_le_bytes());
        put_bytes(&mut out, &self.value);
        out.extend_from_slice(&self.steps.to_le_bytes());
        out.extend_from_slice(&self.bytes.to_le_bytes());
        out.push(self.observed_address as u8);
        out.extend_from_slice(&(self.inputs_read.len() as u64).to_le_bytes());
        for (p, h) in &self.inputs_read {
            put_bytes(&mut out, p);
            out.extend_from_slice(&h.to_le_bytes());
        }
        out
    }

    /// Decodes [`MemoEntry::to_bytes`]; any malformation is a named error
    /// (a memo row that does not decode is a miss, never a guess).
    pub fn from_bytes(bytes: &[u8]) -> Result<MemoEntry, String> {
        let mut r = Rd { b: bytes, at: 0 };
        if r.take(8)? != MEMO_MAGIC {
            return Err("not a comptime memo entry (bad magic)".into());
        }
        let key = MemoKey(u128::from_le_bytes(r.array::<16>()?));
        let value = r.blob()?;
        let steps = u64::from_le_bytes(r.array::<8>()?);
        let nbytes = u64::from_le_bytes(r.array::<8>()?);
        let observed_address = match r.take(1)?[0] {
            0 => false,
            1 => true,
            x => return Err(format!("bad observed_address byte {x}")),
        };
        let n = u64::from_le_bytes(r.array::<8>()?);
        let mut inputs_read = Vec::new();
        for _ in 0..n {
            let p = r.blob()?;
            let h = u128::from_le_bytes(r.array::<16>()?);
            inputs_read.push((p, h));
        }
        if r.at != bytes.len() {
            return Err("trailing bytes after the memo entry".into());
        }
        Ok(MemoEntry {
            key,
            value,
            steps,
            bytes: nbytes,
            observed_address,
            inputs_read,
        })
    }
}

struct Rd<'b> {
    b: &'b [u8],
    at: usize,
}

impl<'b> Rd<'b> {
    fn take(&mut self, n: usize) -> Result<&'b [u8], String> {
        let end = self.at.checked_add(n).ok_or("length overflow")?;
        let s = self.b.get(self.at..end).ok_or("truncated memo entry")?;
        self.at = end;
        Ok(s)
    }
    fn array<const N: usize>(&mut self) -> Result<[u8; N], String> {
        let s = self.take(N)?;
        let mut a = [0u8; N];
        a.copy_from_slice(s);
        Ok(a)
    }
    fn blob(&mut self) -> Result<Vec<u8>, String> {
        let n = u64::from_le_bytes(self.array::<8>()?);
        let n = usize::try_from(n).map_err(|_| "blob length does not fit".to_string())?;
        Ok(self.take(n)?.to_vec())
    }
}

/// The in-memory content-addressed memo (design §10.3: LRU-evictable; a
/// miss is correct, just slow). Persistence is the build's: it stores
/// [`MemoEntry::to_bytes`] under [`MemoKey::hex`].
#[derive(Clone, Debug, Default)]
pub struct Memo {
    rows: std::collections::BTreeMap<MemoKey, MemoEntry>,
    pub hits: u64,
    pub misses: u64,
}

impl Memo {
    pub fn new() -> Memo {
        Memo::default()
    }

    /// Looks `key` up, counting a hit or a miss.
    pub fn lookup(&mut self, key: MemoKey) -> Option<MemoEntry> {
        match self.rows.get(&key) {
            Some(e) => {
                self.hits += 1;
                Some(e.clone())
            }
            None => {
                self.misses += 1;
                None
            }
        }
    }

    /// Adds a row (an entry the build loaded from its store, or a fresh
    /// evaluation). Content-addressed: re-inserting a key keeps the first.
    pub fn insert(&mut self, e: MemoEntry) {
        self.rows.entry(e.key).or_insert(e);
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Hits over lookups, or `None` before any lookup.
    pub fn hit_rate(&self) -> Option<f64> {
        let n = self.hits + self.misses;
        (n > 0).then(|| self.hits as f64 / n as f64)
    }
}

/// Evaluates `prog.entry` — a comptime block's thunk, whose parameters (the
/// enclosing function's run-time bindings) get NO value — in comptime mode,
/// charging `build`. `decl` names the declaration in every error.
pub fn evaluate(
    prog: &Program,
    tys: &TyStore,
    env: &ComptimeEnv<'_>,
    build: &mut BuildMeter,
    decl: &str,
) -> Result<Evaluation, ComptimeError> {
    let err = |kind: ErrorKind, steps: u64, bytes: u64| ComptimeError {
        decl: decl.to_string(),
        kind,
        steps,
        bytes,
    };
    if build.remaining() == 0 {
        return Err(err(
            ErrorKind::Fault(ComptimeFault::Budget(build.exceeded())),
            0,
            0,
        ));
    }
    let ct = CtState {
        meter: Meter::new(&env.limits, build.remaining()),
        inputs: env.inputs.clone(),
        externs: env.externs.to_vec(),
        observed_address: false,
        inputs_read: Vec::new(),
    };
    let mut oracle = crate::host::Oracle::sealed();
    let (res, ct) = crate::exec::run_comptime(prog, tys, &mut oracle, ct);
    // ch04 R12 / ch06, asserted rather than promised: the sealed oracle
    // served nothing and no fs/net door was reached.
    let c = oracle.counters();
    assert!(
        oracle.events().is_empty()
            && c.clock_reads == 0
            && c.entropy_draws == 0
            && c.live_reads == 0
            && c.fs_host_calls == 0
            && c.net_host_calls == 0,
        "comptime evaluation of `{decl}` touched the host: {c:?}"
    );
    let (steps, bytes) = (ct.meter.steps, ct.meter.bytes);
    build.charge(decl, steps);
    let (outcome, value) = match res {
        Ok(v) => v,
        Err(InterpError::Comptime(ComptimeFault::Budget(Exceeded::Build { .. }))) => {
            return Err(err(
                ErrorKind::Fault(ComptimeFault::Budget(build.exceeded())),
                steps,
                bytes,
            ));
        }
        Err(InterpError::Comptime(f)) => return Err(err(ErrorKind::Fault(f), steps, bytes)),
        Err(e) => return Err(err(ErrorKind::Interp(e), steps, bytes)),
    };
    match outcome.exit {
        Exit::Return => {}
        Exit::Trap(kind) => {
            return Err(err(
                ErrorKind::Trap {
                    kind,
                    site: outcome.site.unwrap_or((0, 0)),
                },
                steps,
                bytes,
            ));
        }
        Exit::Ub(_) => {
            let report = outcome.ub.ok_or_else(|| {
                err(
                    ErrorKind::Interp(InterpError::TypeMismatch(
                        "a ub exit carried no report".into(),
                    )),
                    steps,
                    bytes,
                )
            })?;
            return Err(err(ErrorKind::Ub(report), steps, bytes));
        }
        Exit::Raise => return Err(err(ErrorKind::Raise, steps, bytes)),
    }
    let value = value.map_err(|w| err(ErrorKind::Unencodable(w), steps, bytes))?;
    let inputs_read = ct
        .inputs_read
        .iter()
        .filter_map(|p| env.inputs.get(p).map(|r| (r.path.clone(), r.hash)))
        .collect();
    Ok(Evaluation {
        value,
        steps,
        bytes,
        observed_address: ct.observed_address,
        inputs_read,
    })
}

/// Evaluation through the memo: a hit returns the stored row and runs
/// nothing (the step counters stay untouched); a miss evaluates and stores.
/// Returns the row and whether it was a hit.
pub fn evaluate_memoized(
    prog: &Program,
    tys: &TyStore,
    env: &ComptimeEnv<'_>,
    build: &mut BuildMeter,
    memo: &mut Memo,
    decl: &str,
) -> Result<(MemoEntry, bool), ComptimeError> {
    let key = memo_key(prog, target_hash(&prog.config), env.inputs, &env.limits);
    if let Some(hit) = memo.lookup(key) {
        return Ok((hit, true));
    }
    let ev = evaluate(prog, tys, env, build, decl)?;
    let entry = MemoEntry::new(key, &ev);
    memo.insert(entry.clone());
    Ok((entry, false))
}

/// The canonical encoding of a comptime result (tag byte, then payload):
/// `0` unit; `1` bool + 1 byte; `2` integer + width-in-bits byte + signed
/// byte + 8 LE bytes; `3` float + width byte + 8 LE bit-pattern bytes; `4`
/// `Str` + length-prefixed bytes.
pub mod encode {
    pub const UNIT: u8 = 0;
    pub const BOOL: u8 = 1;
    pub const INT: u8 = 2;
    pub const FLOAT: u8 = 3;
    pub const STR: u8 = 4;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn declared_inputs_are_sorted_and_read_once() {
        let d = DeclaredInputs::new(vec![
            (b"b".to_vec(), b"2".to_vec()),
            (b"a".to_vec(), b"1".to_vec()),
            (b"b".to_vec(), b"other".to_vec()),
        ]);
        let paths: Vec<_> = d.rows().iter().map(|r| r.path.clone()).collect();
        assert_eq!(paths, vec![b"a".to_vec(), b"b".to_vec()]);
        assert_eq!(d.get(b"b").map(|r| r.bytes.clone()), Some(b"2".to_vec()));
    }

    #[test]
    fn a_memo_entry_round_trips_byte_for_byte() {
        let e = MemoEntry {
            key: MemoKey(0x1234_5678_9abc_def0_0fed_cba9_8765_4321),
            value: vec![encode::INT, 64, 1, 42, 0, 0, 0, 0, 0, 0, 0],
            steps: 77,
            bytes: 16,
            observed_address: true,
            inputs_read: vec![(b".config".to_vec(), 99)],
        };
        let b = e.to_bytes();
        assert_eq!(MemoEntry::from_bytes(&b), Ok(e.clone()));
        assert_eq!(MemoEntry::from_bytes(&b).map(|x| x.to_bytes()), Ok(b));
        assert!(MemoEntry::from_bytes(b"FORSCTM1").is_err());
    }

    #[test]
    fn target_hash_covers_the_pointer_width() {
        let a = Config::v0_1();
        let b = Config {
            ptr_bits: 32,
            ..Config::v0_1()
        };
        assert_ne!(target_hash(&a), target_hash(&b));
        assert_eq!(target_hash(&a), target_hash(&Config::v0_1()));
    }

    /// ch04 R12 / ch06: this module performs no file I/O and reads no
    /// environment or clock — the declared inputs arrive as bytes.
    #[test]
    fn comptime_module_opens_no_file() {
        let src = include_str!("comptime.rs");
        let code = src.split("#[cfg(test)]").next().unwrap_or(src);
        // Spelled in pieces so this test does not trip host.rs's own grep.
        let banned = [
            concat!("std::", "fs"),
            concat!("std::", "env"),
            concat!("System", "Time"),
            concat!("Instant::", "now"),
            concat!("File", "::"),
        ];
        for banned in banned {
            assert!(
                !code.contains(banned),
                "comptime.rs must not reach the host (`{banned}`)"
            );
        }
    }
}
