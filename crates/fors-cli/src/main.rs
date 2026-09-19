//! `fors`: the Fors compiler frontend CLI.
//!
//! `fors parse <file>...` parses each file and reports diagnostics; exit 0
//! and no output when every file is clean, exit 1 and one line per
//! diagnostic (`path:line:col: error[Pxxxx]: message`) otherwise.
//! `fors parse --tree <file>` additionally dumps the tree, indented, one
//! node per line.

use std::io::Write;
use std::process::ExitCode;

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
            let _ = writeln!(out, "{path}:{line}:{col}: error[{}]: {}", d.code.as_str(), d.message);
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

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("parse") => run_parse(&args[1..]),
        _ => {
            eprintln!("usage: fors parse [--tree] <file>...");
            ExitCode::from(2)
        }
    }
}
