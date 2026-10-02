//! `fors run`: build one program with the `std` package, lower it to FMIR
//! and run it under the interpreter (design `fmir-interpreter.md` §5, §7.2;
//! F8).
//!
//! ```text
//! fors run [--std <dir>] [--oracle-record <file> | --oracle-replay <file>] <file.fors>
//! ```
//!
//! **Oracle flags (design §7.2).** `--oracle-record <file>` writes the run's
//! capability-response log — every clock read and entropy draw, in order, in
//! `fors_interp::host`'s record format — after the run, whatever its exit.
//! `--oracle-replay <file>` serves every response from such a log and reads
//! NO real clock or entropy, so the run is deterministic: its stdout and exit
//! status are byte-identical to the recorded run's. A run that diverges from
//! the record (asks for a different response, more responses, or fewer) is
//! the named oracle error, exit [`EXIT_INTERP`], never a silent divergence.
//!
//! **Exit status.** The program's own: 0 / 1 (an error left `main`, ch02
//! R17) / 2 (`Stdout` latched, ch10 R40(d)) / a `SIGTRAP` signal status for a
//! trap (after the `trap: <kind> at <file>:<L>:<C>` line, design §7.2a) / 70
//! for a `ub:` report. The tool's own failures use statuses the program
//! cannot produce: [`EXIT_USAGE`], [`EXIT_BUILD`] (the program does not
//! build: diagnostics, or `main` did not lower), [`EXIT_INTERP`] (a named
//! interpreter refusal: an oracle mismatch, a host door M1 does not open, an
//! unsupported shape) and [`EXIT_IO`] (a record file could not be read or
//! written).

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fors_index::{Interner, Segments, module::is_legal_segment};

pub const EXIT_USAGE: u8 = 64;
pub const EXIT_BUILD: u8 = 65;
pub const EXIT_INTERP: u8 = 69;
pub const EXIT_IO: u8 = 74;

enum OracleFlag {
    None,
    Record(PathBuf),
    Replay(PathBuf),
}

fn usage(msg: &str) -> ExitCode {
    eprintln!(
        "fors run: {msg}\nusage: fors run [--std <dir>] [--oracle-record <file> | \
         --oracle-replay <file>] <file.fors>"
    );
    ExitCode::from(EXIT_USAGE)
}

/// The `std` source root: `--std`, else `FORS_STD`, else this checkout's.
fn default_std_dir() -> PathBuf {
    match std::env::var_os("FORS_STD") {
        Some(d) => PathBuf::from(d),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std"),
    }
}

/// Every `.fors` file under `dir`, named `std.<path>` (ch08 R17's module
/// names for `std`), sorted so the build is deterministic.
fn std_modules(dir: &Path) -> std::io::Result<Vec<(Vec<Vec<u8>>, Vec<u8>)>> {
    let mut paths = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d)? {
            let p = e?.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().and_then(|x| x.to_str()) == Some("fors") {
                paths.push(p);
            }
        }
    }
    paths.sort();
    let mut out = Vec::new();
    for p in paths {
        let rel = p.strip_prefix(dir).unwrap_or(&p);
        let mut segs: Vec<Vec<u8>> = vec![b"std".to_vec()];
        let comps: Vec<_> = rel.components().collect();
        for (i, c) in comps.iter().enumerate() {
            let os = c.as_os_str().to_string_lossy();
            let seg = if i + 1 == comps.len() {
                os.strip_suffix(".fors").unwrap_or(&os).to_string()
            } else {
                os.to_string()
            };
            segs.push(seg.into_bytes());
        }
        out.push((segs, std::fs::read(&p)?));
    }
    Ok(out)
}

pub fn run_run(args: &[String]) -> ExitCode {
    let mut std_dir: Option<PathBuf> = None;
    let mut oracle_flag = OracleFlag::None;
    let mut file: Option<PathBuf> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--std" => match it.next() {
                Some(d) => std_dir = Some(PathBuf::from(d)),
                None => return usage("`--std` needs a directory"),
            },
            "--oracle-record" | "--oracle-replay" => {
                let Some(f) = it.next() else {
                    return usage(&format!("`{a}` needs a file"));
                };
                if !matches!(oracle_flag, OracleFlag::None) {
                    return usage("`--oracle-record` and `--oracle-replay` are exclusive");
                }
                oracle_flag = if a == "--oracle-record" {
                    OracleFlag::Record(PathBuf::from(f))
                } else {
                    OracleFlag::Replay(PathBuf::from(f))
                };
            }
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
    let std_dir = std_dir.unwrap_or_else(default_std_dir);

    // The oracle first: a replay log that cannot be read or parsed is
    // refused before anything runs.
    let mut oracle = match &oracle_flag {
        OracleFlag::Replay(p) => {
            let bytes = match std::fs::read(p) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("fors run: cannot read {}: {e}", p.display());
                    return ExitCode::from(EXIT_IO);
                }
            };
            match fors_interp::Oracle::replay(&bytes) {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("fors run: {}: oracle: {e}", p.display());
                    return ExitCode::from(EXIT_INTERP);
                }
            }
        }
        _ => fors_interp::Oracle::live(),
    };

    let source = match std::fs::read(&file) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("fors run: cannot read {}: {e}", file.display());
            return ExitCode::from(EXIT_IO);
        }
    };
    let std_srcs = match std_modules(&std_dir) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("fors run: cannot read std at {}: {e}", std_dir.display());
            return ExitCode::from(EXIT_IO);
        }
    };
    let display = file.display().to_string();
    let (prog, tys) = match build(&display, &file, &source, std_srcs) {
        Ok(p) => p,
        Err(lines) => {
            for l in lines {
                eprintln!("{l}");
            }
            return ExitCode::from(EXIT_BUILD);
        }
    };

    // The entry shim's process-level half (ch02 R17, ch10 R40(d)): `SIGPIPE`
    // ignored, and the program's streams are this process's descriptors.
    fors_interp::install_sigpipe_ignore();
    let host = fors_interp::HostEnv {
        stdout_fd: Some(1),
        stderr_fd: Some(2),
    };
    let result = fors_interp::run_with_oracle(&prog, &tys, &host, &mut oracle);

    if let OracleFlag::Record(p) = &oracle_flag
        && let Err(e) = std::fs::write(p, oracle.log_bytes())
    {
        eprintln!("fors run: cannot write {}: {e}", p.display());
        return ExitCode::from(EXIT_IO);
    }

    let outcome = match result {
        Ok(o) => o,
        Err(e) => {
            eprintln!("fors run: interpreter: {e}");
            return ExitCode::from(EXIT_INTERP);
        }
    };
    match fors_interp::entry_exit(&outcome) {
        fors_interp::ExitStatus::Status(code) => {
            if let (fors_interp::Exit::Ub(_), Some(report)) = (outcome.exit, &outcome.ub) {
                let _ = fors_interp::report_ub(
                    &mut std::io::stderr(),
                    report,
                    &display,
                    &outcome.backtrace,
                );
            }
            ExitCode::from(u8::try_from(code).unwrap_or(EXIT_INTERP))
        }
        fors_interp::ExitStatus::Trap(kind) => {
            let (line, col) = outcome.site.unwrap_or((0, 0));
            let _ = fors_interp::report_trap(
                &mut std::io::stderr(),
                kind,
                &display,
                line,
                col,
                &outcome.backtrace,
            );
            fors_interp::shim::die_by_trap_signal()
        }
    }
}

/// parse -> resolve -> check -> lower, with `std` in the build. `Err` is the
/// rendered refusal lines (the ROOT file's diagnostics, or why `main` did
/// not lower). `std`'s own diagnostics are not the program's: the known
/// owner-decision conflicts stay there, and anything that keeps a `std`
/// body from lowering surfaces as that callee's named refusal.
fn build(
    display: &str,
    file: &Path,
    source: &[u8],
    std_srcs: Vec<(Vec<Vec<u8>>, Vec<u8>)>,
) -> Result<(fors_interp::Program, fors_fir::ty::TyStore), Vec<String>> {
    let mut interner = Interner::new();
    let root_name: Segments = match crate::real_header_segments(source, &mut interner) {
        Some(s) => s,
        None => {
            let stem = file
                .file_stem()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            // The conformance corpus's hyphenated test names are not module
            // names (tests/conformance/README.md); such a file is `main`.
            let stem = if is_legal_segment(stem.as_bytes()) {
                stem
            } else {
                "main".to_string()
            };
            vec![interner.intern(stem.as_bytes())]
        }
    };
    let mut sources: Vec<Vec<u8>> = vec![source.to_vec()];
    let mut names: Vec<Segments> = vec![root_name];
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
    let mut errors: Vec<String> = parsed[0]
        .diags
        .iter()
        .map(|d| format!("{}: error[{}]: {}", at(d.start), d.code.as_str(), d.message))
        .collect();
    if !errors.is_empty() {
        return Err(errors);
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
            errors.push(format!(
                "{}: error[{}]: {}",
                at(d.start),
                d.code.as_string(),
                d.message
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let checked = fors_check::check_build(&inputs, &resolved, &mut interner);
    for d in checked.diagnostics.iter().filter(|d| d.file.index() == 0) {
        errors.push(format!(
            "{}: error[{}]: {}",
            at(d.start),
            d.code.as_string(),
            d.message
        ));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let lowered = fors_lower::lower_build(&inputs, &checked, &mut interner);
    if !lowered.fns.iter().any(|f| f.name == "main") {
        let mut lines: Vec<String> = lowered
            .diags
            .iter()
            .filter(|d| d.name == "main")
            .map(|d| format!("{display}: `main` does not lower: {:?}", d.error))
            .collect();
        if lines.is_empty() {
            lines.push(format!("{display}: no `main` to run"));
        }
        return Err(lines);
    }
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
    let prog = fors_interp::Program::entry_by_name(fns, "main", fors_interp::Config::v0_1())
        .ok_or_else(|| vec![format!("{display}: no `main` to run")])?
        .with_names(lowered.names);
    Ok((prog, lowered.tys))
}
