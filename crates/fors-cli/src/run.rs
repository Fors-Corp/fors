//! `fors run`: build one program with the `std` package, lower it to FMIR
//! and run it under the interpreter (design `fmir-interpreter.md` §5, §7.2;
//! F8).
//!
//! ```text
//! fors run [--std <dir>] [--oracle-record <file> | --oracle-replay <file>]
//!          [--oracle-run-record <file>] <file.fors>
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
//! **F10's full record.** `--oracle-run-record <file>` writes the run's
//! complete [`fors_interp::OracleRecord`] (design §7.1: program digest, every
//! host observation, exact stdout/stderr bytes, exit, step count) after the
//! run, whatever its exit. `--oracle-replay` accepts such a record as well as
//! an F8 response log (told apart by the first line): it serves the record's
//! host section and, after the run, compares the new run's record with it —
//! any field that differs is `oracle: record mismatch: <field>`, exit
//! [`EXIT_INTERP`].
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
         --oracle-replay <file>] [--oracle-run-record <file>] <file.fors>"
    );
    ExitCode::from(EXIT_USAGE)
}

/// The `std` source root: `--std`, else `FORS_STD`, else this checkout's.
pub(crate) fn default_std_dir() -> PathBuf {
    match std::env::var_os("FORS_STD") {
        Some(d) => PathBuf::from(d),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std"),
    }
}

/// Every `.fors` file under `dir`, named `std.<path>` (ch08 R17's module
/// names for `std`), sorted so the build is deterministic.
pub(crate) fn std_modules(dir: &Path) -> std::io::Result<Vec<(Vec<Vec<u8>>, Vec<u8>)>> {
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
    let mut run_record: Option<PathBuf> = None;
    let mut file: Option<PathBuf> = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--std" => match it.next() {
                Some(d) => std_dir = Some(PathBuf::from(d)),
                None => return usage("`--std` needs a directory"),
            },
            "--oracle-run-record" => match it.next() {
                Some(f) if run_record.is_none() => run_record = Some(PathBuf::from(f)),
                Some(_) => return usage("`--oracle-run-record` given twice"),
                None => return usage("`--oracle-run-record` needs a file"),
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
    // refused before anything runs. A full F10 record replays its host
    // section and is kept for the after-run comparison.
    let mut replayed_record: Option<fors_interp::OracleRecord> = None;
    let mut oracle = match &oracle_flag {
        OracleFlag::Replay(p) => {
            let bytes = match std::fs::read(p) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("fors run: cannot read {}: {e}", p.display());
                    return ExitCode::from(EXIT_IO);
                }
            };
            if bytes.starts_with(fors_interp::RUN_RECORD_HEADER.as_bytes()) {
                match fors_interp::OracleRecord::from_bytes(&bytes) {
                    Ok(r) => {
                        let o = fors_interp::Oracle::replay_events(r.host.clone());
                        replayed_record = Some(r);
                        o
                    }
                    Err(e) => {
                        eprintln!("fors run: {}: oracle: {e}", p.display());
                        return ExitCode::from(EXIT_INTERP);
                    }
                }
            } else {
                match fors_interp::Oracle::replay(&bytes) {
                    Ok(o) => o,
                    Err(e) => {
                        eprintln!("fors run: {}: oracle: {e}", p.display());
                        return ExitCode::from(EXIT_INTERP);
                    }
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
    let record = fors_interp::OracleRecord::of(&prog, &outcome, oracle.events());
    if let Some(p) = &run_record
        && let Err(e) = std::fs::write(p, record.to_bytes())
    {
        eprintln!("fors run: cannot write {}: {e}", p.display());
        return ExitCode::from(EXIT_IO);
    }
    if let Some(want) = &replayed_record
        && let Some(field) = want.first_difference(&record)
    {
        eprintln!(
            "fors run: oracle: record mismatch: `{field}` differs from the replayed record \
             (recorded {}, replayed {})",
            want.id(),
            record.id()
        );
        return ExitCode::from(EXIT_INTERP);
    }
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

/// parse -> resolve -> check -> lower -> comptime (F9's build step,
/// [`crate::build::compile`]), with `std` in the build. `Err` is the rendered
/// refusal lines: the ROOT file's diagnostics and every comptime build
/// error (a program whose comptime evaluation fails does not run), or why
/// `main` did not lower. `std`'s own diagnostics are not the program's: the
/// known owner-decision conflicts stay there, and anything that keeps a
/// `std` body from lowering surfaces as that callee's named refusal.
fn build(
    display: &str,
    file: &Path,
    source: &[u8],
    std_srcs: Vec<(Vec<Vec<u8>>, Vec<u8>)>,
) -> Result<(fors_interp::Program, fors_fir::ty::TyStore), Vec<String>> {
    let out = crate::build::compile(
        display,
        file,
        source,
        std_srcs,
        &crate::build::Opts::default(),
    );
    if !out.errors.is_empty() {
        return Err(out.errors);
    }
    let Some((mut prog, tys)) = out.program else {
        return Err(vec![format!("{display}: no `main` to run")]);
    };
    let Some(main) = prog.fns.iter().position(|f| f.name == "main") else {
        let mut lines = out.main_diags;
        if lines.is_empty() {
            lines.push(format!("{display}: no `main` to run"));
        }
        return Err(lines);
    };
    prog.entry = main;
    Ok((prog, tys))
}
