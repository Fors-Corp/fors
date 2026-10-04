//! `fors`: the Fors compiler frontend CLI.
//!
//! `fors parse <file>...` parses each file and reports diagnostics; exit 0
//! and no output when every file is clean, exit 1 and one line per
//! diagnostic (`path:line:col: error[Pxxxx]: message`) otherwise.
//! `fors parse --tree <file>` additionally dumps the tree, indented, one
//! node per line.
//!
//! `fors check <path>...` runs name resolution (ch08) and the ch04 rules
//! it owns on each `path`: a directory is a package source root (modules
//! named from their path under it, ch08 R1); a single file is a one-
//! module package (the conformance corpus's convention — see
//! `tests/conformance/README.md`). Prints every diagnostic as
//! `path:line:col: error[CODE]: message`, sorted by file then byte
//! offset; exit 0 when every given path is clean. `std` is always in the
//! build (ch08 R17's prelude names denote `std`'s items whether or not the
//! program wrote `use std...;`): every package but `std` itself is checked
//! with the `std` source root beside it, and only the package's own
//! diagnostics are printed.
//!
//! `fors run [--oracle-record <file> | --oracle-replay <file>] [--oracle-run-record <file>] <file>`
//! builds one program with `std`, lowers it and runs it under the FMIR
//! interpreter; see [`run`].
//!
//! `fors build [--memo-dir <dir>] [--counters] <file>` is the build step:
//! check, lower, and evaluate every `comptime` block in comptime mode,
//! reporting the comptime diagnostics with the checker's; see [`build`].

mod build;
mod run;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fors_index::{Interner, Segments, module::is_legal_segment};

/// The `line:col` every writer here reports; see `fors_diag`'s crate docs
/// for the unit of each (col counts BYTES).
use fors_diag::LineIndex;

fn run_parse(args: &[String]) -> ExitCode {
    let mut show_tree = false;
    let mut files: Vec<&str> = Vec::new();
    for a in args {
        if a == "--tree" {
            show_tree = true;
        } else {
            files.push(a);
        }
    }
    if files.is_empty() {
        eprintln!("fors parse: no input files");
        return ExitCode::from(1);
    }

    let mut any_diag = false;
    let stdout = std::io::stdout();
    let mut out = stdout.lock();

    for path in files {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("{path}: error: {e}");
                any_diag = true;
                continue;
            }
        };
        let parsed = fors_syntax::parse_file(&bytes);
        let lines = (!parsed.diags.is_empty()).then(|| LineIndex::new(&bytes));
        for d in &parsed.diags {
            any_diag = true;
            let (line, col) = lines.as_ref().map_or((1, 1), |ix| ix.line_col(d.start));
            let _ = writeln!(
                out,
                "{path}:{line}:{col}: error[{}]: {}",
                d.code.as_str(),
                d.message
            );
        }
        if show_tree {
            let mut dump = String::new();
            fors_syntax::dump_tree(&parsed.tree, &parsed.tokens, &bytes, &mut dump);
            let _ = write!(out, "{dump}");
        }
    }

    if any_diag {
        ExitCode::from(1)
    } else {
        ExitCode::from(0)
    }
}

/// One resolved file of a package: its disk path, source bytes and
/// canonical module name (ch08 Rule 1).
struct PkgFile {
    display: String,
    source: Vec<u8>,
    name: Segments,
    /// Extra diagnostics decided while building the package (Rule 24
    /// file-name legality, duplicate module names) — not byte-positioned
    /// inside the file, so reported at its very start.
    extra: Vec<(u32, u32, &'static str, String)>,
}

fn walk_fors_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().collect();
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let Ok(ft) = entry.file_type() else { continue };
        if ft.is_dir() {
            walk_fors_files(&path, out);
        } else if ft.is_file() && path.extension().is_some_and(|e| e == "fors") {
            out.push(path);
        }
    }
}

/// Builds one package from a CLI path: a directory (its files, named by
/// path under it) or a single file (a one-module package, ch08 R24's
/// name check waived per the conformance corpus's convention: a `module`
/// header names it, else its file stem does, validated).
fn build_package(path: &Path, interner: &mut Interner) -> Option<(Vec<PkgFile>, Option<usize>)> {
    if path.is_dir() {
        let mut paths = Vec::new();
        walk_fors_files(path, &mut paths);
        let mut files = Vec::with_capacity(paths.len());
        let mut root = None;
        for p in &paths {
            let source = std::fs::read(p).ok()?;
            let rel = p.strip_prefix(path).unwrap_or(p);
            let mut segs_bytes: Vec<Vec<u8>> = Vec::new();
            let mut extra = Vec::new();
            let comps: Vec<_> = rel.components().collect();
            for (i, c) in comps.iter().enumerate() {
                let os = c.as_os_str().to_string_lossy();
                let seg = if i + 1 == comps.len() {
                    os.strip_suffix(".fors").unwrap_or(&os).to_string()
                } else {
                    os.to_string()
                };
                if !is_legal_segment(seg.as_bytes()) {
                    extra.push((
                        0,
                        0,
                        "N0024",
                        format!("illegal file/directory name segment `{seg}`"),
                    ));
                }
                segs_bytes.push(seg.into_bytes());
            }
            if comps.len() == 1 && segs_bytes.first().map(|s| s.as_slice()) == Some(b"main") {
                root = Some(files.len());
            }
            let name: Segments = segs_bytes.iter().map(|s| interner.intern(s)).collect();
            files.push(PkgFile {
                display: p.display().to_string(),
                source,
                name,
                extra,
            });
        }
        if root.is_none() && files.len() == 1 {
            root = Some(0);
        }
        // Rule 24: two files mapping to one module name.
        for i in 0..files.len() {
            for j in (i + 1)..files.len() {
                if files[i].name == files[j].name {
                    let other = files[j].display.clone();
                    let mname = fors_index::module::join_dotted(interner, &files[i].name);
                    files[i].extra.push((
                        0,
                        0,
                        "N0024",
                        format!("also names module `{mname}` as `{other}`"),
                    ));
                }
            }
        }
        Some((files, root))
    } else {
        // A single file is a one-module package (conformance corpus
        // convention: the hyphenated disk name is the *test's* name, not
        // the module's — see `tests/conformance/README.md`). Its `module`
        // header names it when present; only absent a header does its
        // file stem have to obey ch08 R24.
        let source = std::fs::read(path).ok()?;
        let mut extra = Vec::new();
        let name: Segments = match real_header_segments(&source, interner) {
            Some(segs) => segs,
            None => {
                let stem = path
                    .file_stem()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_else(|| "main".to_string());
                if !is_legal_segment(stem.as_bytes()) {
                    extra.push((0, 0, "N0024", format!("illegal file name `{stem}`")));
                }
                vec![interner.intern(stem.as_bytes())]
            }
        };
        Some((
            vec![PkgFile {
                display: path.display().to_string(),
                source,
                name,
                extra,
            }],
            Some(0),
        ))
    }
}

/// Item 47(a): `std` is ALWAYS in a build. ch08 R17's prelude names
/// (`Vec`, `Buffer`, ...) denote `std`'s items whether or not the program
/// wrote `use std...;`, so every package but `std` itself is checked with
/// the `std` source root beside it. The std files come AFTER the package's
/// own (`files[..own]`) and are never printed: `std`'s own diagnostics are
/// `std`'s, not the program's. Returns the number of the package's own files.
fn append_std(
    path: &Path,
    files: &mut Vec<PkgFile>,
    interner: &mut Interner,
) -> Result<usize, String> {
    let own = files.len();
    if path.is_dir() && path.file_name().is_some_and(|n| n == "std") {
        return Ok(own);
    }
    let dir = run::default_std_dir();
    let srcs =
        run::std_modules(&dir).map_err(|e| format!("cannot read std at {}: {e}", dir.display()))?;
    for (segs, source) in srcs {
        let name: Segments = segs.iter().map(|s| interner.intern(s)).collect();
        let dotted: Vec<String> = segs
            .iter()
            .map(|s| String::from_utf8_lossy(s).into_owned())
            .collect();
        files.push(PkgFile {
            display: format!("<{}>", dotted.join(".")),
            source,
            name,
            extra: Vec::new(),
        });
    }
    Ok(own)
}

/// One rendered diagnostic plus the sort key `fors check` has always
/// sorted by: the file's display path, then the byte offset the
/// diagnostic starts at. The rendering is done eagerly, in the format
/// this run asked for, so that only one of the two writers ever runs.
struct Line {
    path: String,
    start: u32,
    text: String,
}

/// Which writer `fors check` prints with. Text is the default and is a
/// frozen baseline: it must not change by one byte.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Format {
    Text,
    Json,
}

fn push_line(
    out: &mut Vec<Line>,
    format: Format,
    path: &str,
    index: &LineIndex,
    start: u32,
    end: u32,
    code: String,
    message: String,
    fixes: Vec<fors_diag::Fix>,
) {
    let r = fors_diag::Rendered {
        path: path.to_string(),
        start: index.pos(start),
        end: index.pos(end),
        code,
        message,
        fixes,
    };
    let mut text = String::new();
    match format {
        Format::Json => fors_diag::json::diagnostic_line(&r, index, &mut text),
        Format::Text => fors_diag::write_text(&r, &mut text),
    }
    out.push(Line {
        path: r.path,
        start: r.start.byte,
        text,
    })
}

/// Reads `--format json|text` (and `--format=json`) out of `args`,
/// returning the format and the remaining arguments. An unknown format is
/// the caller's exit-2 error.
fn take_format(args: &[String]) -> Result<(Format, Vec<String>), String> {
    let mut format = Format::Text;
    let mut rest = Vec::with_capacity(args.len());
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let value = if a == "--format" {
            i += 1;
            match args.get(i) {
                Some(v) => Some(v.as_str()),
                None => return Err("--format needs a value (json or text)".to_string()),
            }
        } else {
            a.strip_prefix("--format=")
        };
        match value {
            Some("json") => format = Format::Json,
            Some("text") => format = Format::Text,
            Some(other) => return Err(format!("unknown --format `{other}` (json or text)")),
            None => rest.push(args[i].clone()),
        }
        i += 1;
    }
    Ok((format, rest))
}

fn run_check(args: &[String]) -> ExitCode {
    // MARC: design §12 asks for `fors check --count` to print the
    // deterministic counters the near-linearity gate reads. It is a flag on
    // this command rather than a subcommand of its own because the numbers
    // are a property of a check, not a separate operation, and the gate
    // wants them for the same run whose diagnostics it is reading.
    let count = args.iter().any(|a| a == "--count");
    // MARC: design §9 asks the query engine for `--stats`. It is a flag on
    // `fors check` for the same reason `--count` is: the numbers describe a
    // check, not a separate operation. It runs the same package through
    // `fors_check::queries::QueryBuild` — the content-hash DAG — and prints
    // what the engine did. The diagnostic LINES above it are still the frozen
    // text baseline produced by `check_build`; `query_path_agrees_with_check_build`
    // in this file's tests is the assertion that the two never disagree.
    let stats = args.iter().any(|a| a == "--stats");
    let args: Vec<String> = args
        .iter()
        .filter(|a| a.as_str() != "--count" && a.as_str() != "--stats")
        .cloned()
        .collect();
    let (format, args) = match take_format(&args) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("fors check: {e}");
            return ExitCode::from(2);
        }
    };
    if args.is_empty() {
        eprintln!("fors check: no input paths");
        return ExitCode::from(2);
    }
    let mut lines: Vec<Line> = Vec::new();
    let mut any = false;
    let mut file_count = 0usize;
    let mut totals = fors_check::Counters::default();

    for arg in &args {
        let path = Path::new(arg);
        let mut interner = Interner::new();
        let Some((mut files, root)) = build_package(path, &mut interner) else {
            eprintln!("{arg}: error: could not read package");
            any = true;
            continue;
        };
        let own = match append_std(path, &mut files, &mut interner) {
            Ok(n) => n,
            Err(e) => {
                eprintln!("{arg}: error: {e}");
                any = true;
                continue;
            }
        };
        file_count += own;
        let parsed: Vec<fors_syntax::Parse> = files
            .iter()
            .map(|f| fors_syntax::parse_file(&f.source))
            .collect();
        let inputs: Vec<fors_resolve::FileInput> = files
            .iter()
            .zip(parsed.iter())
            .map(|(f, p)| fors_resolve::FileInput {
                tree: &p.tree,
                tokens: &p.tokens,
                source: &f.source,
                name: f.name.clone(),
            })
            .collect();
        // The package name comes from the manifest (ch08 Rule 1), which has no
        // chapter yet, so infer it from the source root's directory name. It
        // matters only for `std` itself: inside package `std` the module paths
        // carry no `std` segment, so nothing else could tell that an `impl` of
        // a prelude type is at home (ch08 Rule 21, ch10 Rule 1).
        let package = std::path::Path::new(path)
            .file_name()
            .map(|n| n.as_encoded_bytes().to_vec());
        let output =
            fors_resolve::resolve_in_package(&mut interner, &inputs, root, package.as_deref());
        // Design §4.4/§13: `fors check` runs the checker after resolution
        // and merges its diagnostics into the same sorted line list. As of
        // I2 that is signature lowering and whole-head well-formedness
        // (T-codes); bodies are I3 onward's.
        let checked = fors_check::check_build(&inputs, &output, &mut interner);

        // One line index per file, built the first time that file has a
        // diagnostic to place: a clean file never pays for one.
        let indexes: Vec<std::cell::OnceCell<LineIndex>> =
            files.iter().map(|_| std::cell::OnceCell::new()).collect();
        let index_of = |i: usize| indexes[i].get_or_init(|| LineIndex::new(&files[i].source));

        for (i, f) in files.iter().enumerate().take(own) {
            for d in &parsed[i].diags {
                any = true;
                push_line(
                    &mut lines,
                    format,
                    &f.display,
                    index_of(i),
                    d.start,
                    d.end,
                    d.code.as_str().to_string(),
                    d.message.to_string(),
                    d.fixes.clone(),
                );
            }
            for (_, _, code, msg) in &f.extra {
                any = true;
                // Not positioned inside the file (a file-name or duplicate-
                // module fact), so it is reported at its very start.
                push_line(
                    &mut lines,
                    format,
                    &f.display,
                    index_of(i),
                    0,
                    0,
                    (*code).to_string(),
                    msg.clone(),
                    Vec::new(),
                );
            }
            for d in &output.files[i].diagnostics {
                any = true;
                push_line(
                    &mut lines,
                    format,
                    &f.display,
                    index_of(i),
                    d.start,
                    d.end,
                    d.code.as_string(),
                    d.message.clone(),
                    d.fixes.clone(),
                );
            }
        }
        for d in &checked.diagnostics {
            let Some(f) = files.get(d.file.index()).filter(|_| d.file.index() < own) else {
                continue;
            };
            any = true;
            push_line(
                &mut lines,
                format,
                &f.display,
                index_of(d.file.index()),
                d.start,
                d.end,
                d.code.as_string(),
                d.message.clone(),
                d.fixes.clone(),
            );
        }
        let c = checked.counters;
        totals.nodes_visited += c.nodes_visited;
        totals.synths += c.synths;
        totals.checks += c.checks;
        totals.subst_norm_calls += c.subst_norm_calls;
        totals.holds_probes += c.holds_probes;
        totals.holds_misses += c.holds_misses;
        totals.impl_scans += c.impl_scans;
        totals.tape_events += c.tape_events;
        totals.types_interned += c.types_interned;
        totals.bodies_checked += c.bodies_checked;
        totals.bodies_skipped += c.bodies_skipped;
    }

    lines.sort_by(|a, b| (a.path.as_str(), a.start).cmp(&(b.path.as_str(), b.start)));
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for l in &lines {
        let _ = writeln!(out, "{}", l.text);
    }

    if stats {
        for arg in &args {
            let path = Path::new(arg);
            let mut interner = Interner::new();
            let Some((mut files, root)) = build_package(path, &mut interner) else {
                continue;
            };
            if append_std(path, &mut files, &mut interner).is_err() {
                continue;
            }
            let package = std::path::Path::new(path)
                .file_name()
                .map(|n| n.as_encoded_bytes().to_vec());
            let mut qb = fors_check::queries::QueryBuild::new();
            qb.set_root(root);
            qb.set_package(package);
            for f in &files {
                let segs: Vec<fors_index::Symbol> = f
                    .name
                    .iter()
                    .map(|s| qb.interner_mut().intern(interner.resolve(*s)))
                    .collect();
                qb.add_file(&f.display, segs, f.source.clone());
            }
            match qb.recheck() {
                Ok(()) => {
                    let _ = writeln!(out, "--- {arg}: query DAG");
                    let _ = write!(out, "{}", qb.render_stats());
                }
                Err(_) => {
                    let _ = writeln!(out, "--- {arg}: query DAG cancelled");
                }
            }
        }
    }

    let t = &totals;
    let counters: [(&str, u64); 11] = [
        ("bodies_checked", t.bodies_checked),
        ("bodies_skipped", t.bodies_skipped),
        ("nodes_visited", t.nodes_visited),
        ("synth_calls", t.synths),
        ("check_calls", t.checks),
        ("subst_norm_calls", t.subst_norm_calls),
        ("holds_probes", t.holds_probes),
        ("holds_memo_misses", t.holds_misses),
        ("impl_index_probes", t.impl_scans),
        ("use_tape_events", t.tape_events),
        ("types_interned", t.types_interned),
    ];
    match format {
        Format::Json => {
            let mut s = String::new();
            fors_diag::json::summary_line(
                lines.len(),
                file_count,
                count.then_some(&counters[..]),
                &mut s,
            );
            let _ = writeln!(out, "{s}");
        }
        Format::Text if count => {
            let _ = writeln!(out, "bodies checked       {}", t.bodies_checked);
            let _ = writeln!(out, "bodies skipped       {}", t.bodies_skipped);
            let _ = writeln!(out, "nodes visited        {}", t.nodes_visited);
            let _ = writeln!(out, "synth calls          {}", t.synths);
            let _ = writeln!(out, "check calls          {}", t.checks);
            let _ = writeln!(out, "subst_norm calls     {}", t.subst_norm_calls);
            let _ = writeln!(out, "holds probes         {}", t.holds_probes);
            let _ = writeln!(out, "holds memo misses    {}", t.holds_misses);
            let _ = writeln!(out, "impl-index probes    {}", t.impl_scans);
            let _ = writeln!(out, "use-tape events      {}", t.tape_events);
            let _ = writeln!(out, "types interned       {}", t.types_interned);
        }
        Format::Text => {}
    }

    if any {
        ExitCode::from(1)
    } else {
        ExitCode::from(0)
    }
}

/// `fors explain <CODE>` / `fors explain --list`: the normative rule behind
/// a stable diagnostic code, offline, from the chapters this binary
/// embeds. Exit 2 (and one line on stderr) for a code that does not exist —
/// an agent that mistypes a code must not read silence as "no such rule".
fn run_explain(args: &[String]) -> ExitCode {
    let (format, args) = match take_format(args) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("fors explain: {e}");
            return ExitCode::from(2);
        }
    };
    let list = args.iter().any(|a| a == "--list");
    let codes: Vec<&String> = args.iter().filter(|a| !a.starts_with("--")).collect();
    let stdout = std::io::stdout();
    let mut out = stdout.lock();

    if list {
        for (code, summary) in fors_diag::list() {
            let _ = match format {
                Format::Json => writeln!(
                    out,
                    "{}",
                    fors_diag::explain::render_list_json(&code, &summary)
                ),
                Format::Text => writeln!(out, "{code}  {summary}"),
            };
        }
        return ExitCode::SUCCESS;
    }

    let [code] = codes.as_slice() else {
        eprintln!("usage: fors explain [--format json|text] <CODE>\n       fors explain --list");
        return ExitCode::from(2);
    };
    let upper = code.to_ascii_uppercase();
    let Some(e) = fors_diag::explain(&upper) else {
        eprintln!("fors explain: unknown diagnostic code `{code}` (try `fors explain --list`)");
        return ExitCode::from(2);
    };
    let _ = match format {
        Format::Json => writeln!(out, "{}", fors_diag::explain::render_json(&e)),
        Format::Text => write!(out, "{}", fors_diag::explain::render_text(&e)),
    };
    ExitCode::SUCCESS
}

fn real_header_segments(source: &[u8], interner: &mut Interner) -> Option<Segments> {
    let parsed = fors_syntax::parse_file(source);
    if parsed.tree.is_empty() {
        return None;
    }
    let child = parsed.tree.children(0).next()?;
    if parsed.tree.kinds[child] != fors_syntax::NodeKind::ModuleHdr {
        return None;
    }
    let path_node = parsed.tree.children(child).next()?;
    let (first, end) = parsed.tree.token_range(path_node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if parsed.tokens.kinds[i] == fors_lex::TokenKind::Ident {
            out.push(interner.intern(parsed.tokens.text(i, source)));
        }
    }
    if out.is_empty() { None } else { Some(out) }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("parse") => run_parse(&args[1..]),
        Some("check") => run_check(&args[1..]),
        Some("explain") => run_explain(&args[1..]),
        Some("run") => run::run_run(&args[1..]),
        Some("build") => build::run_build(&args[1..]),
        // Two streams (CONTRIBUTING.md): the compiler's own version, and the
        // language version it implements.
        Some("--version" | "-V") => {
            println!(
                "fors {} (language {})",
                env!("CARGO_PKG_VERSION"),
                include_str!("../../../docs/spec/VERSION").trim()
            );
            ExitCode::SUCCESS
        }
        _ => {
            eprintln!(
                "usage: fors parse [--tree] <file>...\n\
                 \x20      fors check [--format json|text] [--count] [--stats] <path>...\n\
                 \x20      fors explain [--format json|text] <CODE>\n\
                 \x20      fors explain [--format json|text] --list\n\
                 \x20      fors run [--oracle-record <file> | --oracle-replay <file>]\n\
                 \x20               [--oracle-run-record <file>] <file>\n\
                 \x20      fors build [--memo-dir <dir>] [--counters] <file>\n\
                 \x20      fors --version"
            );
            ExitCode::from(2)
        }
    }
}
