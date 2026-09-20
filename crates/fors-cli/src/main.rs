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
//! offset; exit 0 when every given path is clean.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fors_index::{Interner, Segments, module::is_legal_segment};

fn line_col(source: &[u8], byte_offset: u32) -> (u32, u32) {
    let offset = (byte_offset as usize).min(source.len());
    let mut line = 1u32;
    let mut col = 1u32;
    for &b in &source[..offset] {
        if b == b'\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

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
        for d in &parsed.diags {
            any_diag = true;
            let (line, col) = line_col(&bytes, d.start);
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

fn run_check(args: &[String]) -> ExitCode {
    // MARC: design §12 asks for `fors check --count` to print the
    // deterministic counters the near-linearity gate reads. It is a flag on
    // this command rather than a subcommand of its own because the numbers
    // are a property of a check, not a separate operation, and the gate
    // wants them for the same run whose diagnostics it is reading.
    let count = args.iter().any(|a| a == "--count");
    let args: Vec<String> = args
        .iter()
        .filter(|a| a.as_str() != "--count")
        .cloned()
        .collect();
    if args.is_empty() {
        eprintln!("fors check: no input paths");
        return ExitCode::from(2);
    }
    let mut lines: Vec<(String, u32, u32, String)> = Vec::new();
    let mut any = false;
    let mut totals = fors_check::Counters::default();

    for arg in &args {
        let path = Path::new(arg);
        let mut interner = Interner::new();
        let Some((files, root)) = build_package(path, &mut interner) else {
            eprintln!("{arg}: error: could not read package");
            any = true;
            continue;
        };
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

        for (i, f) in files.iter().enumerate() {
            for d in &parsed[i].diags {
                any = true;
                let (l, c) = line_col(&f.source, d.start);
                lines.push((
                    f.display.clone(),
                    d.start,
                    d.start,
                    format!("{l}:{c}: error[{}]: {}", d.code.as_str(), d.message),
                ));
            }
            for (_, _, code, msg) in &f.extra {
                any = true;
                lines.push((
                    f.display.clone(),
                    0,
                    0,
                    format!("1:1: error[{code}]: {msg}"),
                ));
            }
            for d in &output.files[i].diagnostics {
                any = true;
                let (l, c) = line_col(&f.source, d.start);
                lines.push((
                    f.display.clone(),
                    d.start,
                    d.start,
                    format!("{l}:{c}: error[{}]: {}", d.code.as_string(), d.message),
                ));
            }
        }
        for d in &checked.diagnostics {
            let Some(f) = files.get(d.file.index()) else {
                continue;
            };
            any = true;
            let (l, c) = line_col(&f.source, d.start);
            lines.push((
                f.display.clone(),
                d.start,
                d.start,
                format!("{l}:{c}: error[{}]: {}", d.code.as_string(), d.message),
            ));
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

    lines.sort_by(|a, b| (a.0.as_str(), a.1).cmp(&(b.0.as_str(), b.1)));
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for (path, _, _, rest) in &lines {
        let _ = writeln!(out, "{path}:{rest}");
    }

    if count {
        let t = &totals;
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

    if any {
        ExitCode::from(1)
    } else {
        ExitCode::from(0)
    }
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
        _ => {
            eprintln!("usage: fors parse [--tree] <file>...\n       fors check <path>...");
            ExitCode::from(2)
        }
    }
}
