//! Source -> runnable [`Candidate`]: parse, resolve, check, lower (through a
//! caller-supplied lowering, so the seeded-miscompile harness can pass its
//! hooked one), verify. A program that writes through `io.Stdout` names
//! `use std.io;` and is built with `std/io.fors` beside it, as the F2 gate
//! harness does; nothing else from `std` enters the build.

use fors_check::CheckOutput;
use fors_index::{Interner, Segments};
use fors_lower::LoweredBuild;
use fors_resolve::FileInput;

use crate::Candidate;

/// A lowering: [`fors_lower::lower_build`] or a hooked twin.
pub type Lowerer<'a> = &'a dyn Fn(&[FileInput<'_>], &CheckOutput, &mut Interner) -> LoweredBuild;

fn std_io() -> &'static [u8] {
    static IO: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    IO.get_or_init(|| {
        let p = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../std/io.fors");
        std::fs::read(&p).unwrap_or_else(|e| panic!("reading {}: {e}", p.display()))
    })
}

/// Builds `src` (module name from its header, else `m`) and returns the
/// program whose entry is `main`, or the first reason it does not build.
pub fn build_source(src: &str, lower: Lowerer<'_>) -> Result<Candidate, String> {
    let mut interner = Interner::new();
    let mut sources: Vec<Vec<u8>> = vec![src.as_bytes().to_vec()];
    let mut names: Vec<Segments> = vec![vec![interner.intern(b"m")]];
    if src.contains("use std.io;") {
        sources.push(std_io().to_vec());
        names.push(vec![interner.intern(b"std"), interner.intern(b"io")]);
    }
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
        .flat_map(|f| f.diagnostics.iter())
        .next()
    {
        return Err(format!("resolve: {}", d.code.as_string()));
    }
    let out = fors_check::check_build(&inputs, &resolved, &mut interner);
    if let Some(d) = out.diagnostics.first() {
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
