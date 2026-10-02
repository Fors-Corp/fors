//! `fors build`: the build step — check, lower, and evaluate every
//! `comptime` block in comptime mode (F9; design `fmir-interpreter.md` §6,
//! ch04 R11-R15, ch10 R42).
//!
//! ```text
//! fors build [--std <dir>] [--memo-dir <dir>] [--counters] <file.fors>
//! ```
//!
//! **What runs.** parse -> resolve -> check -> lower -> for every
//! `comptime` block of the program, its thunk is evaluated by the FMIR
//! interpreter in comptime mode (one engine, ch04 R11). The checker's
//! diagnostics and the comptime evaluator's are reported TOGETHER, in that
//! order, one line each as `path:line:col: error[CODE]: message`; a
//! comptime error's code is the ch04 rule it violates (`A0012` a forbidden
//! intrinsic, `A0013` an undeclared or unreadable input, `A0014` a budget,
//! `A0002` a sealed operation, `A0011` a shape the engine cannot evaluate)
//! and its position is the `comptime` keyword's. A checker error does not
//! stop comptime evaluation: an authority error is not a type error, the
//! body still lowers, and the comptime machine is sandboxed (no capability,
//! no host door, budgets), so the build reports everything it can find.
//!
//! **Declared inputs** (ch04 R13). The module header's `inputs { "p", ...
//! };` paths are read ONCE each, relative to the declaring file's
//! directory, BEFORE any evaluation, and content-hashed; the comptime
//! machine sees only those bytes. A listed path that cannot be read is a
//! build error (ch10 R42: total, "a missing or unreadable input is a BUILD
//! error"). Nothing else is ever read for comptime.
//!
//! **Memo** (design §6, §10.2). Every evaluation is keyed by
//! [`fors_interp::memo_key`] — the target hash, the `fmir_hash` of every
//! declaration the block can reach, the declared inputs' content hashes and
//! the budget. `--memo-dir <dir>` persists each entry as `<dir>/<key>.fcm`
//! ([`fors_interp::MemoEntry::to_bytes`]) and consults the directory first,
//! so an unchanged block is never re-evaluated.
//!
//! **Counters** (`--counters`, stdout): one line per evaluation — steps,
//! bytes, memo hit or miss, the key and the ch04 R15 tier-up answer — and a
//! final memo hit-rate line.
//!
//! **Exit status.** 0 clean; [`crate::run::EXIT_BUILD`] for any diagnostic;
//! [`crate::run::EXIT_USAGE`] / [`crate::run::EXIT_IO`] for the tool's own
//! failures.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fors_index::{Interner, Segments, module::is_legal_segment};

use crate::run::{EXIT_BUILD, EXIT_IO, EXIT_USAGE};

/// Build-step options.
#[derive(Default, Clone)]
pub struct Opts {
    pub memo_dir: Option<PathBuf>,
    pub counters: bool,
}

/// What a build produced.
pub struct Compiled {
    /// Rendered diagnostics: the checker's, then the comptime evaluator's.
    pub errors: Vec<String>,
    /// `--counters` lines.
    pub counters: Vec<String>,
    /// The runnable program parts, when lowering got that far.
    pub program: Option<(fors_interp::Program, fors_fir::ty::TyStore)>,
    /// `main` lowering diagnostics (for `fors run`'s refusal).
    pub main_diags: Vec<String>,
}

fn usage(msg: &str) -> ExitCode {
    eprintln!(
        "fors build: {msg}\nusage: fors build [--std <dir>] [--memo-dir <dir>] [--counters] \
         <file.fors>"
    );
    ExitCode::from(EXIT_USAGE)
}

pub fn run_build(args: &[String]) -> ExitCode {
    let mut std_dir: Option<PathBuf> = None;
    let mut opts = Opts::default();
    let mut file: Option<PathBuf> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--std" => match it.next() {
                Some(d) => std_dir = Some(PathBuf::from(d)),
                None => return usage("`--std` needs a directory"),
            },
            "--memo-dir" => match it.next() {
                Some(d) => opts.memo_dir = Some(PathBuf::from(d)),
                None => return usage("`--memo-dir` needs a directory"),
            },
            "--counters" => opts.counters = true,
            s if s.starts_with("--") => return usage(&format!("unknown flag `{s}`")),
            s => {
                if file.is_some() {
                    return usage("exactly one program file");
                }
                file = Some(PathBuf::from(s));
            }
        }
    }
    let Some(file) = file else {
        return usage("no program file");
    };
    let std_dir = std_dir.unwrap_or_else(crate::run::default_std_dir);
    let source = match std::fs::read(&file) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("fors build: cannot read {}: {e}", file.display());
            return ExitCode::from(EXIT_IO);
        }
    };
    let std_srcs = match crate::run::std_modules(&std_dir) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("fors build: cannot read std at {}: {e}", std_dir.display());
            return ExitCode::from(EXIT_IO);
        }
    };
    if let Some(d) = &opts.memo_dir
        && let Err(e) = std::fs::create_dir_all(d)
    {
        eprintln!("fors build: cannot create {}: {e}", d.display());
        return ExitCode::from(EXIT_IO);
    }
    let display = file.display().to_string();
    let out = compile(&display, &file, &source, std_srcs, &opts);
    for l in &out.counters {
        println!("{l}");
    }
    for l in &out.errors {
        eprintln!("{l}");
    }
    if out.errors.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(EXIT_BUILD)
    }
}

/// The module name of the root file: its header, else its stem (a
/// conformance file's hyphenated stem is `main`).
fn root_name(file: &Path, source: &[u8], interner: &mut Interner) -> Segments {
    match crate::real_header_segments(source, interner) {
        Some(s) => s,
        None => {
            let stem = file
                .file_stem()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            let stem = if is_legal_segment(stem.as_bytes()) {
                stem
            } else {
                "main".to_string()
            };
            vec![interner.intern(stem.as_bytes())]
        }
    }
}

/// parse -> resolve -> check -> lower -> comptime, with `std` in the build.
pub fn compile(
    display: &str,
    file: &Path,
    source: &[u8],
    std_srcs: Vec<(Vec<Vec<u8>>, Vec<u8>)>,
    opts: &Opts,
) -> Compiled {
    let mut out = Compiled {
        errors: Vec::new(),
        counters: Vec::new(),
        program: None,
        main_diags: Vec::new(),
    };
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![source.to_vec()];
    let mut names: Vec<Segments> = vec![root_name(file, source, &mut interner)];
    for (segs, src) in std_srcs {
        names.push(segs.iter().map(|b| interner.intern(b)).collect());
        sources.push(src);
    }
    let parsed: Vec<_> = sources.iter().map(|s| fors_syntax::parse_file(s)).collect();
    let index = fors_diag::LineIndex::new(source);
    let at = |start: u32| {
        let (l, c) = index.line_col(start);
        format!("{display}:{l}:{c}")
    };
    for d in &parsed[0].diags {
        out.errors.push(format!(
            "{}: error[{}]: {}",
            at(d.start),
            d.code.as_str(),
            d.message
        ));
    }
    if !out.errors.is_empty() {
        return out;
    }
    let inputs: Vec<fors_resolve::FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| fors_resolve::FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    if let Some(f) = resolved.files.first() {
        for d in &f.diagnostics {
            out.errors.push(format!(
                "{}: error[{}]: {}",
                at(d.start),
                d.code.as_string(),
                d.message
            ));
        }
    }
    if !out.errors.is_empty() {
        return out;
    }
    let checked = fors_check::check_build(&inputs, &resolved, &mut interner);
    for d in checked.diagnostics.iter().filter(|d| d.file.index() == 0) {
        out.errors.push(format!(
            "{}: error[{}]: {}",
            at(d.start),
            d.code.as_string(),
            d.message
        ));
    }
    let lowered = fors_lower::lower_build(&inputs, &checked, &mut interner);
    out.main_diags = lowered
        .diags
        .iter()
        .filter(|d| d.name == "main")
        .map(|d| format!("{display}: `main` does not lower: {:?}", d.error))
        .collect();
    let thunks = lowered.comptime.clone();
    let externs = lowered.externs.clone();
    let fns: Vec<fors_interp::ProgFn> = lowered
        .fns
        .into_iter()
        .map(|f| fors_interp::ProgFn {
            name: f.name,
            decl: f.decl,
            strings: f.strings,
            intrinsics: f.intrinsics,
        })
        .collect();
    let tys = lowered.tys;
    let type_names = lowered.names;
    let base = file
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    let mut prog = fors_interp::Program {
        fns,
        entry: 0,
        config: fors_interp::Config::v0_1(),
        names: type_names,
    };
    let step = Step {
        thunks: &thunks,
        externs: &externs,
        tys: &tys,
        base: &base,
        opts,
        at: &at,
    };
    run_comptime(&step, &mut prog, &mut out);
    out.program = Some((prog, tys));
    out
}

/// The comptime half's read-only inputs.
struct Step<'s> {
    thunks: &'s [fors_lower::ComptimeThunk],
    externs: &'s [(fors_fir::DeclKeyId, String)],
    tys: &'s fors_fir::ty::TyStore,
    /// The root file's directory: what its `inputs` paths are relative to.
    base: &'s Path,
    opts: &'s Opts,
    at: &'s dyn Fn(u32) -> String,
}

/// The comptime half of the build step: every thunk, through the memo.
fn run_comptime(step: &Step<'_>, prog: &mut fors_interp::Program, out: &mut Compiled) {
    let Step {
        thunks,
        externs,
        tys,
        base,
        opts,
        at,
    } = *step;
    let limits = fors_interp::Limits::default();
    let mut build = fors_interp::BuildMeter::new(&limits);
    let mut memo = fors_interp::Memo::new();
    // Each declared path is read once per build (ch04 R13), whichever
    // blocks name it.
    let mut read_cache: Vec<(Vec<u8>, Result<Vec<u8>, String>)> = Vec::new();
    for t in thunks {
        let pos = if t.file == 0 {
            at(t.offset)
        } else {
            format!("<std file {}>:{}", t.file, t.offset)
        };
        if let Some(e) = &t.error {
            out.errors.push(format!(
                "{pos}: error[A0011]: the comptime block in `{}` cannot be handed to the \
                 comptime engine: {e} (ch04 R11: comptime runs only on the FMIR interpreter, and \
                 a shape it cannot take is a build error, never deferred to run time)",
                t.enclosing
            ));
            continue;
        }
        // Declared inputs, resolved to bytes and hashes BEFORE evaluation.
        let mut pairs = Vec::new();
        let mut unreadable = false;
        for p in &t.inputs {
            let got = match read_cache.iter().find(|(k, _)| k == p) {
                Some((_, r)) => r.clone(),
                None => {
                    let path = base.join(String::from_utf8_lossy(p).as_ref());
                    let r = std::fs::read(&path).map_err(|e| e.to_string());
                    read_cache.push((p.clone(), r.clone()));
                    r
                }
            };
            match got {
                Ok(bytes) => pairs.push((p.clone(), bytes)),
                Err(e) => {
                    unreadable = true;
                    out.errors.push(format!(
                        "{pos}: error[A0013]: the declared comptime input \"{}\" cannot be read \
                         ({e}); a missing or unreadable input is a build error (ch04 R13, ch10 \
                         R42)",
                        String::from_utf8_lossy(p)
                    ));
                }
            }
        }
        if unreadable {
            continue;
        }
        let declared = fors_interp::DeclaredInputs::new(pairs);
        let Some(entry) = prog.fns.iter().position(|f| f.name == t.name) else {
            out.errors.push(format!(
                "{pos}: error[A0011]: the comptime block in `{}` has no lowered thunk",
                t.enclosing
            ));
            continue;
        };
        prog.entry = entry;
        let env = fors_interp::ComptimeEnv {
            inputs: &declared,
            limits,
            externs,
        };
        // The persisted memo first: an entry on disk under this key is the
        // same evaluation, by content address.
        let key = fors_interp::memo_key(
            prog,
            fors_interp::target_hash(&prog.config),
            &declared,
            &limits,
        );
        if let Some(dir) = &opts.memo_dir {
            let path = dir.join(format!("{}.fcm", key.hex()));
            if let Ok(bytes) = std::fs::read(&path)
                && let Ok(e) = fors_interp::MemoEntry::from_bytes(&bytes)
                && e.key == key
            {
                memo.insert(e);
            }
        }
        match fors_interp::evaluate_memoized(prog, tys, &env, &mut build, &mut memo, &t.enclosing) {
            Ok((entry, hit)) => {
                if !hit && let Some(dir) = &opts.memo_dir {
                    let path = dir.join(format!("{}.fcm", entry.key.hex()));
                    if let Err(e) = std::fs::write(&path, entry.to_bytes()) {
                        out.errors.push(format!(
                            "{pos}: error: cannot write the comptime memo entry {}: {e}",
                            path.display()
                        ));
                    }
                }
                if opts.counters {
                    out.counters.push(format!(
                        "comptime {pos} `{}`: steps={} bytes={} memo={} key={} tier_up={}",
                        t.enclosing,
                        entry.steps,
                        entry.bytes,
                        if hit { "hit" } else { "miss" },
                        entry.key.hex(),
                        if entry.observed_address { "no" } else { "yes" }
                    ));
                }
            }
            Err(e) => {
                if opts.counters {
                    out.counters.push(format!(
                        "comptime {pos} `{}`: steps={} bytes={} memo=miss error={}",
                        t.enclosing,
                        e.steps,
                        e.bytes,
                        e.code().as_string()
                    ));
                }
                out.errors.push(format!(
                    "{pos}: error[{}]: {}",
                    e.code().as_string(),
                    e.message()
                ));
            }
        }
    }
    if opts.counters && !thunks.is_empty() {
        let rate = memo
            .hit_rate()
            .map(|r| format!("{:.3}", r))
            .unwrap_or_else(|| "n/a".into());
        out.counters.push(format!(
            "comptime memo: hits={} misses={} hit_rate={rate} build_steps={}",
            memo.hits, memo.misses, build.steps
        ));
    }
}
