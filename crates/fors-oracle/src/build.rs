//! Source -> runnable [`Candidate`]: parse, resolve, check, lower (through a
//! caller-supplied lowering, so the seeded-miscompile harness can pass its
//! hooked one), verify. `std` is ALWAYS in the build (item 47(a)): ch08
//! R17's prelude names denote `std`'s items whether or not the program wrote
//! `use std...;`, so every program is built with the whole `std/` package
//! beside it, named `std.<path>` as `fors run` names it.

use fors_check::CheckOutput;
use fors_index::{Interner, Segments};
use fors_lower::LoweredBuild;
use fors_resolve::FileInput;

use crate::Candidate;

/// A lowering: [`fors_lower::lower_build`] or a hooked twin.
pub type Lowerer<'a> = &'a dyn Fn(&[FileInput<'_>], &CheckOutput, &mut Interner) -> LoweredBuild;

/// Every `.fors` file under `std/`, as `(path segments after `std`, source)`,
/// sorted so the build is deterministic. Read once per process.
fn std_modules() -> &'static [(Vec<String>, Vec<u8>)] {
    static STD: std::sync::OnceLock<Vec<(Vec<String>, Vec<u8>)>> = std::sync::OnceLock::new();
    STD.get_or_init(|| {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std");
        let mut paths = Vec::new();
        let mut stack = vec![root.clone()];
        while let Some(d) = stack.pop() {
            let entries =
                std::fs::read_dir(&d).unwrap_or_else(|e| panic!("reading {}: {e}", d.display()));
            for e in entries {
                let p = e.expect("a std directory entry").path();
                if p.is_dir() {
                    stack.push(p);
                } else if p.extension().and_then(|x| x.to_str()) == Some("fors") {
                    paths.push(p);
                }
            }
        }
        paths.sort();
        paths
            .into_iter()
            .map(|p| {
                let rel = p.strip_prefix(&root).expect("under std").with_extension("");
                let segs = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                let src =
                    std::fs::read(&p).unwrap_or_else(|e| panic!("reading {}: {e}", p.display()));
                (segs, src)
            })
            .collect()
    })
}

/// Builds `src` (module name from its header, else `m`) and returns the
/// program whose entry is `main`, or the first reason it does not build.
pub fn build_source(src: &str, lower: Lowerer<'_>) -> Result<Candidate, String> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.as_bytes().to_vec()];
    let mut names: Vec<Segments> = vec![vec![interner.intern(b"m")]];
    for (segs, bytes) in std_modules() {
        let mut name: Segments = vec![interner.intern(b"std")];
        name.extend(segs.iter().map(|s| interner.intern(s.as_bytes())));
        sources.push(bytes.clone());
        names.push(name);
    }
    // The program is file 0; `std`'s own diagnostics are `std`'s, not the
    // program's (its two owner-decision conflicts stay there).
    let own = 1usize;
    let parsed: Vec<_> = sources.iter().map(|s| fors_syntax::parse_file(s)).collect();
    if let Some(p) = parsed.iter().find(|p| !p.diags.is_empty()) {
        return Err(format!("parse: {:?}", p.diags.first()));
    }
    let inputs: Vec<FileInput> = parsed
        .iter()
        .zip(sources.iter())
        .zip(names.iter())
        .map(|((p, s), n)| FileInput {
            tree: &p.tree,
            tokens: &p.tokens,
            source: s,
            name: n.clone(),
        })
        .collect();
    let resolved = fors_resolve::resolve_in_package(&mut interner, &inputs, Some(0), None);
    if let Some(d) = resolved
        .files
        .iter()
        .take(own)
        .flat_map(|f| f.diagnostics.iter())
        .next()
    {
        return Err(format!("resolve: {}", d.code.as_string()));
    }
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    if let Some(d) = out.diagnostics.iter().find(|d| d.file.index() < own) {
        return Err(format!("check: {} {}", d.code.as_string(), d.message));
    }
    let lowered = lower(&inputs, &out, &mut interner);
    if !lowered.fns.iter().any(|f| f.name == "main") {
        return Err(format!(
            "lower: {:?}",
            lowered.diags.first().map(|d| &d.error)
        ));
    }
    for f in &lowered.fns {
        let diags = fors_fmir::verify::verify(&f.decl);
        if let Some(d) = diags.first() {
            return Err(format!("verify {}: {}", f.name, d.message));
        }
    }
    let tys = lowered.tys;
    let names = lowered.names;
    let fns: Vec<_> = lowered
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
        .ok_or("no main")?
        .with_names(names);
    Ok(Candidate { prog, tys })
}
