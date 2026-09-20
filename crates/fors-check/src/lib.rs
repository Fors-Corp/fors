//! `fors-check`: lowering and the two type-checking judgements (design
//! `docs/design/type-checker.md` §4.2). Depends on `fors-lex`,
//! `fors-syntax`, `fors-index`, `fors-resolve` and `fors-fir`.
//!
//! Increment I2 (§13) landed the signature half: [`defs`] (the build-wide
//! `DefTable`), the prelude rows and the impl index, [`lower`] (CST +
//! resolver output -> FIR signatures) and [`wf`] (whole-head
//! well-formedness).
//!
//! Increment I3 adds bodies with nothing to determine: [`body`] (the
//! per-declaration state, the statement forms and the driver), [`expr`]
//! (the two judgements), [`call`] (R38 with zero parameters to determine),
//! [`member`] (R42/R47/R49), [`show`] (types in diagnostics) and [`tape`]
//! (the use tape the flow pass will consume). `pat.rs`/`exhaust.rs` (I7),
//! `flow.rs` (I8) and `facts.rs` (I9) are still to come.

pub mod body;
pub mod call;
pub mod defs;
pub mod deps;
pub mod diag;
pub mod expr;
pub mod lower;
pub mod member;
pub mod rules;
pub mod show;
pub mod tape;
pub mod wf;

pub use diag::Diagnostic;

use fors_index::ids::{FileId, ModuleId};
use fors_resolve::{FileInput, ResolveOutput};

/// The result of type-checking a whole build.
#[derive(Default)]
pub struct CheckOutput {
    pub diagnostics: Vec<Diagnostic>,
    /// The build's FIR: every type, signature and declaration key, frozen
    /// (§7.1 phase 5) with `sig_hash` filled. I3 types bodies against it; a
    /// test reads `sigs.sig_hash(def)` from it.
    pub fir: fors_fir::Fir,
    /// `DefId` per declaration, for a caller that has a `(file, decl)`.
    pub defs: Option<defs::DefTable>,
    /// Deterministic counters (design §12): what the near-linearity gate
    /// reads. Every field is a count of work done, never a duration.
    pub types_interned: usize,
    pub decls_lowered: usize,
    pub counters: Counters,
    /// The distinct CHECK positions this build's bodies used (design §11's
    /// `check_positions_match_ch03_r25`).
    pub check_sites: Vec<body::CheckSite>,
    /// Per typed body: the declarations whose signature it read (design
    /// §9). I9's query engine keys `check_body` on these.
    pub deps: Vec<(fors_index::ids::DefId, deps::DepSet)>,
}

/// The counters `fors check --count` prints and the near-linearity gate
/// (design §12) compares across corpus sizes. A layout mistake shows up
/// here as a counter that grows faster than the source does.
#[derive(Default, Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counters {
    /// Body CST nodes visited by `synth`/`check`.
    pub nodes_visited: u64,
    pub synths: u64,
    pub checks: u64,
    /// `subst_norm` calls (design §7.5).
    pub subst_norm_calls: u64,
    /// `holds` probes (design §7.6).
    pub holds_probes: u64,
    pub holds_misses: u64,
    /// Impl-index probes: `exact` hits and bucket scans.
    pub impl_scans: u64,
    /// Events appended to the use tape (design §7.9).
    pub tape_events: u64,
    /// Rows in the type store at the end of the build.
    pub types_interned: u64,
    /// Bodies typed, and bodies skipped because the declaration already
    /// had a diagnostic (design §10: one root cause per declaration).
    pub bodies_checked: u64,
    pub bodies_skipped: u64,
}

// MARC: design §4.2/§4.4 gives `check_build`'s signature as
// `check_build(&ResolveOutput, ...) -> CheckOutput` without spelling out the
// `...`. Lowering reads the CST, which `ResolveOutput` does not carry, and
// interns member and associated-type names, which needs `&mut Interner`
// (design §1, corrected point 6: "the signature phase, sequential and with
// `&mut Interner`, closes that gap before any body is checked"). So the
// parameters are the same `&[FileInput]` the caller already built for
// `resolve` plus that interner.
/// Type-checks a whole resolved build (design §7.1's phases 1-5; phases 6-7
/// are I3 onward's). `inputs` is the same slice handed to
/// [`fors_resolve::resolve`], in the same order.
pub fn check_build(inputs: &[FileInput], resolved: &ResolveOutput, interner: &mut fors_index::Interner) -> CheckOutput {
    // `FORS_PHASES=1` prints the elapsed time at each phase boundary of §7.1.
    // Read once per process, not once per phase: `check_build` runs 900 times
    // in the conformance harness.
    static PHASES: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let _t = std::time::Instant::now();
    macro_rules! phase {
        ($n:literal) => {
            if *PHASES.get_or_init(|| std::env::var_os("FORS_PHASES").is_some()) {
                eprintln!("  {}: {:?}", $n, _t.elapsed());
            }
        };
    }
    let mut fir = fors_fir::Fir::new();
    // 1-2. The prelude, before any user signature (design §7.1).
    let prelude = fors_fir::prelude::build(&mut fir, interner);

    // 1. `DefTable` from every file's `DeclTable`.
    let mut file_to_module: Vec<ModuleId> = vec![ModuleId(0); inputs.len()];
    for (m, &f) in resolved.modules.file.iter().enumerate() {
        if f.index() < file_to_module.len() {
            file_to_module[f.index()] = ModuleId(m as u32);
        }
    }
    let modules: Vec<defs::FileModule> = (0..inputs.len())
        .map(|i| {
            let id = file_to_module[i];
            let segs: Vec<fors_index::Symbol> =
                resolved.modules.name.get(id.index()).cloned().unwrap_or_else(|| inputs[i].name.clone());
            let path = fir.keys.paths.intern(&segs);
            defs::FileModule { id, path }
        })
        .collect();
    let decls: Vec<&fors_index::DeclTable> = resolved.files.iter().map(|f| &f.decls).collect();
    let def_table = defs::build(&mut fir, &decls, &modules);

    let files: Vec<lower::FileCtx> = inputs
        .iter()
        .enumerate()
        .zip(resolved.files.iter())
        .map(|((i, inp), fr)| lower::FileCtx {
            file: FileId(i as u32),
            tree: inp.tree,
            tokens: inp.tokens,
            source: inp.source,
            uses: &fr.name_uses,
        })
        .collect();

    // Pass A: arities and kinds, with no type.
    phase!("defs");
    let shapes = lower::shapes(&fir, &def_table, &prelude, interner, &files);
    phase!("shapes");

    let mut sink = diag::Sink::new();
    // 3. Lowering.
    let mut low = {
        let mut l = lower::Lowerer {
            sites: lower::Sites::default(),
            fir: &mut fir,
            names: interner,
            prelude: &prelude,
            defs: &def_table,
            shapes: &shapes,
            sink: &mut sink,
        };
        l.run(&files)
    };
    phase!("lower");
    // R22's built-in impls join the index before any bound is asked about.
    fors_fir::prelude::push_builtin_impls(&mut fir, &prelude, &mut low.impls);
    low.impls.finish();
    let decls_lowered = def_table.len() - def_table.first_user.index();

    // 4-6. Whole-head well-formedness, the freeze, then every body. All
    // three read the same tables, so they share one context: `holds`, the
    // impl index and the linearity memo are built once (design §7.1).
    let (counters, check_sites, deps) = {
        let mut w = wf::Wf::new(&mut fir, interner, &prelude, &def_table, &shapes, &mut sink);
        w.spoke = vec![false; w.fir.sigs.len()];
        w.impls = std::mem::take(&mut low.impls);
        w.run(&low, &files);
        phase!("wf");
        // 5. Freeze: every signature's canonical hash (§5.4), derived,
        // never an input. Body checking may still intern body-local types;
        // it never touches a signature, so the hashes stay the ones the
        // query DAG keys on.
        w.freeze(&def_table);
        phase!("hash");
        // 6. Bodies.
        w.bodies(&low, &files);
        let c = Counters {
            nodes_visited: w.body_nodes,
            synths: w.synths,
            checks: w.checks,
            subst_norm_calls: w.subst_calls,
            holds_probes: w.holds_probes,
            holds_misses: w.holds_misses,
            impl_scans: w.impl_scans,
            tape_events: w.tape_events,
            types_interned: 0,
            bodies_checked: w.bodies_checked,
            bodies_skipped: w.bodies_skipped,
        };
        (c, std::mem::take(&mut w.check_sites), std::mem::take(&mut w.deps))
    };
    phase!("bodies");

    phase!("wf");
    let types_interned = fir.tys.len();
    CheckOutput {
        diagnostics: sink.finish(),
        fir,
        defs: Some(def_table),
        types_interned,
        decls_lowered,
        counters: Counters { types_interned: types_interned as u64, ..counters },
        check_sites,
        deps,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_index::Interner;
    use fors_syntax::parse_file;

    fn check(src: &[u8]) -> Vec<String> {
        let mut interner = Interner::new();
        let parsed = parse_file(src);
        let name = vec![interner.intern(b"m")];
        let inputs = [FileInput {
            tree: &parsed.tree,
            tokens: &parsed.tokens,
            source: src,
            name,
        }];
        let resolved = fors_resolve::resolve(&mut interner, &inputs, None);
        let out = check_build(&inputs, &resolved, &mut interner);
        out.diagnostics.iter().map(|d| d.code.as_string()).collect()
    }

    #[test]
    fn check_build_on_an_empty_package_emits_nothing() {
        assert!(check(b"module m;\n").is_empty());
    }

    #[test]
    fn a_plain_struct_and_fn_lower_clean() {
        assert!(check(b"module m;\nstruct P { x: i32, y: i32 }\nfn f(let p: P) -> i32 { return p.x; }\n").is_empty());
    }

    #[test]
    fn arity_mismatch_is_t0011() {
        assert_eq!(check(b"module m;\nfn f(let x: Option[i32, i32]) { }\n"), ["T0011"]);
    }
}
