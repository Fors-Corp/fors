//! The checking harness: one source text through parse, resolve and
//! `check_build` (with the panic caught and the use-tape swept for silent
//! `TY_ERROR`), plus the query path for the agreement sample.

use std::cell::{Cell, RefCell};
use std::panic::{self, AssertUnwindSafe};
use std::sync::Once;

use fors_fir::ty::TY_ERROR;
use fors_index::Interner;
use fors_resolve::FileInput;
use fors_syntax::parse_file;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diag {
    pub code: String,
    pub start: u32,
    pub end: u32,
    pub site: u16,
    pub msg: String,
}

#[derive(Default, Debug)]
pub struct CheckResult {
    pub parse: Vec<String>,
    pub resolve: Vec<String>,
    pub resolve_at: Vec<(String, u32)>,
    pub diags: Vec<Diag>,
    /// Nodes the checker typed `TY_ERROR` inside a body that raised no
    /// diagnostic (`tests/silent.rs`'s sweep), one `line:col Kind` each.
    pub silent: Vec<String>,
    pub panic: Option<String>,
}

thread_local! {
    static QUIET: Cell<bool> = const { Cell::new(false) };
    static LAST: RefCell<String> = const { RefCell::new(String::new()) };
}
static HOOK: Once = Once::new();

/// Swallows (and remembers) a panic raised while a check runs on this
/// thread; every other panic still reaches libtest's reporting.
pub fn install_quiet_hook() {
    HOOK.call_once(|| {
        let prev = panic::take_hook();
        panic::set_hook(Box::new(move |info| {
            if QUIET.with(|q| q.get()) {
                LAST.with(|l| *l.borrow_mut() = info.to_string());
            } else {
                prev(info);
            }
        }));
    });
}

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

/// Checks `src` as the single module `m`. Never panics.
pub fn check(src: &str, sweep: bool) -> CheckResult {
    install_quiet_hook();
    QUIET.with(|q| q.set(true));
    let r = panic::catch_unwind(AssertUnwindSafe(|| check_inner(src, sweep)));
    QUIET.with(|q| q.set(false));
    match r {
        Ok(res) => res,
        Err(payload) => {
            let text = LAST.with(|l| std::mem::take(&mut *l.borrow_mut()));
            let msg = if text.is_empty() {
                payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_else(|| "panic".to_string())
            } else {
                text
            };
            CheckResult {
                panic: Some(msg),
                ..Default::default()
            }
        }
    }
}

fn check_inner(src: &str, sweep: bool) -> CheckResult {
    let mut res = CheckResult::default();
    let p = parse_file(src.as_bytes());
    for d in &p.diags {
        let (l, c) = line_col(src.as_bytes(), d.start);
        res.parse
            .push(format!("{} at {l}:{c}: {}", d.code.as_str(), d.message));
    }
    let mut interner = Interner::new();
    let name = vec![interner.intern(b"m")];
    let inputs = [FileInput {
        tree: &p.tree,
        tokens: &p.tokens,
        source: src.as_bytes(),
        name,
    }];
    let resolved = fors_resolve::resolve(&mut interner, &inputs, Some(0));
    for f in &resolved.files {
        for d in &f.diagnostics {
            let (l, c) = line_col(src.as_bytes(), d.start);
            res.resolve
                .push(format!("{} at {l}:{c}: {}", d.code.as_string(), d.message));
            res.resolve_at.push((d.code.as_string(), d.start));
        }
    }
    if !res.parse.is_empty() {
        // The checker's input is not a program; stop at the parser.
        return res;
    }
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    res.diags = out
        .diagnostics
        .iter()
        .map(|d| Diag {
            code: d.code.as_string(),
            start: d.start,
            end: d.end,
            site: d.site,
            msg: d.message.clone(),
        })
        .collect();
    if sweep {
        res.silent = silent_nodes(&inputs[0], &out);
    }
    res
}

/// `tests/silent.rs`'s sweep over one file: every node the checker TYPED
/// that ended `TY_ERROR` inside a declaration whose own span carries no
/// diagnostic.
fn silent_nodes(input: &FileInput, out: &fors_check::CheckOutput) -> Vec<String> {
    let Some(defs) = out.defs.as_ref() else {
        return Vec::new();
    };
    let tree = input.tree;
    let tokens = input.tokens;
    let src = input.source;
    let mut offenders = Vec::new();
    for (def, facts) in &out.facts {
        let Some(row) = defs.get(*def) else { continue };
        if row.file.index() != 0 {
            continue;
        }
        let (start, end) = facts.range();
        if start as usize >= tree.len() {
            continue;
        }
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
            let (t_a, t_b) = tree.token_range(n as usize);
            let hi = (t_b as usize).min(tokens.kinds.len());
            let real: Vec<usize> = (t_a as usize..hi)
                .filter(|&i| !tokens.kinds[i].is_trivia())
                .collect();
            let first = real.first().copied().unwrap_or(t_a as usize);
            let at = tokens.starts.get(first).copied().unwrap_or(0);
            let (line, col) = line_col(src, at);
            offenders.push(format!("{line}:{col} {:?}", tree.kinds[n as usize]));
        }
    }
    offenders.sort();
    offenders
}

/// The same module through the query DAG, as sorted
/// `start-end code site message` rows; `Err` is a panic's message.
pub fn query_rows(src: &str) -> Result<Vec<String>, String> {
    guarded(|| {
        let mut qb = fors_check::queries::QueryBuild::new();
        qb.set_root(Some(0));
        let segs = vec![qb.interner_mut().intern(b"m")];
        qb.add_file("m.fors", segs, src.as_bytes().to_vec());
        qb.recheck().expect("never cancelled");
        let mut v: Vec<String> = qb
            .diagnostics()
            .iter()
            .map(|d| {
                format!(
                    "{}-{} {} site {} {}",
                    d.start,
                    d.end,
                    d.code.as_string(),
                    d.site,
                    d.message
                )
            })
            .collect();
        v.sort();
        v
    })
}

/// `check_build`'s diagnostics in the same row format as [`query_rows`].
pub fn build_rows(res: &CheckResult) -> Vec<String> {
    let mut v: Vec<String> = res
        .diags
        .iter()
        .map(|d| format!("{}-{} {} site {} {}", d.start, d.end, d.code, d.site, d.msg))
        .collect();
    v.sort();
    v
}

/// Runs `f`, turning a panic into its message (and keeping it off stderr).
pub fn guarded<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    install_quiet_hook();
    QUIET.with(|q| q.set(true));
    let r = panic::catch_unwind(AssertUnwindSafe(f));
    QUIET.with(|q| q.set(false));
    r.map_err(|payload| {
        let text = LAST.with(|l| std::mem::take(&mut *l.borrow_mut()));
        if text.is_empty() {
            payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "panic".to_string())
        } else {
            text
        }
    })
}
