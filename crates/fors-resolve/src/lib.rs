//! `fors-resolve`: name resolution (spec ch08) and the ch04 rules
//! decidable from names and the module graph alone, for the Fors
//! compiler. Std only, data-oriented: every table is struct-of-arrays
//! columns indexed by a `u32` newtype (reusing [`fors_index::ids`]),
//! names are interned `Symbol`s, and each file's own work — its item
//! table, then its bodies' local scopes — depends only on that file's
//! tree/tokens plus the whole-build module graph and name tables
//! ([`items::build_universe`], the one step that is not per-file, per
//! ch08 Rule 7's dependency ordering). Never panics: every failure is a
//! [`diag::Diagnostic`] with a byte range and a stable `N00xx`/`A00xx`
//! code. Output is deterministic: no iteration over a `HashMap` ever
//! decides diagnostic order or a `Symbol`/`DefId` value — every table
//! here is either index-ordered or explicitly sorted by interned bytes.

pub mod authority;
pub mod diag;
pub mod items;
pub mod paths;
pub mod prelude;
pub mod scope;
pub mod target;

pub use diag::{Code, Diagnostic};
pub use target::{Entity, NameUseTable, ResolvedTarget};

use fors_index::{DeclTable, FileId, Interner, ModuleTable, Segments};
use fors_lex::Tokens;
use fors_syntax::Tree;

/// One file to resolve as part of a build: an already-parsed tree plus
/// its canonical module name (ch08 Rule 1), which only the caller can
/// derive (it depends on the package's manifest/source-root layout).
pub struct FileInput<'a> {
    pub tree: &'a Tree,
    pub tokens: &'a Tokens,
    pub source: &'a [u8],
    pub name: Segments,
}

/// One file's resolution result.
pub struct FileResult {
    pub decls: DeclTable,
    pub diagnostics: Vec<Diagnostic>,
    pub name_uses: NameUseTable,
}

pub struct ResolveOutput {
    pub modules: ModuleTable,
    pub files: Vec<FileResult>,
    /// Per-module scopes and export tables, for the checker's member
    /// lookups and the query engine's dependency tracking.
    pub universe: items::Universe,
}

impl ResolveOutput {
    /// Module `file`'s export table as sorted text: the whole of what any
    /// other module's resolution can depend on.
    pub fn export_signature(&self, file: usize, interner: &Interner) -> Vec<String> {
        self.universe.scope(FileId(file as u32)).map(|s| s.export_signature(interner)).unwrap_or_default()
    }
}

fn index_diag_rule(code: fors_index::DiagCode) -> u16 {
    match code {
        fors_index::DiagCode::HeaderPathMismatch => 1,
        fors_index::DiagCode::ImportCycle => 7,
        fors_index::DiagCode::SelfImport => 8,
        fors_index::DiagCode::IllegalFileName => 24,
    }
}

/// Resolves a whole build (one package's files; `root` is the index of
/// its root module, ch04 Rule 8 — `None` when the build has none, e.g. a
/// library with no `main`). Runs the whole-build linking step once
/// ([`fors_index::build_module_graph`], [`items::build_universe`]), then
/// resolves each file's bodies (ch08 R14-R20, R25-R26) and the ch04 rules
/// this phase owns (needs vocabulary, `main`).
pub fn resolve(interner: &mut Interner, inputs: &[FileInput], root: Option<usize>) -> ResolveOutput {
    let n = inputs.len();
    let decls: Vec<DeclTable> = inputs.iter().map(|f| fors_index::build_decl_table(f.tree, f.tokens, f.source, interner)).collect();
    let facts: Vec<fors_index::FileFacts> = inputs.iter().map(|f| fors_index::extract_module_facts(f.tree, f.tokens, f.source, interner)).collect();

    let graph_input: Vec<(FileId, Segments, fors_index::FileFacts)> =
        facts.into_iter().enumerate().map(|(i, fa)| (FileId(i as u32), inputs[i].name.clone(), fa)).collect();
    let (modules, edges, mod_diags) = fors_index::build_module_graph(interner, graph_input);

    let mut per_file: Vec<Vec<Diagnostic>> = (0..n).map(|_| Vec::new()).collect();
    for d in &mod_diags {
        let Some(slot) = per_file.get_mut(d.file.index()) else { continue };
        slot.push(Diagnostic::new(d.start, d.end, Code::N(index_diag_rule(d.code)), d.message.clone()));
    }

    for (i, inp) in inputs.iter().enumerate() {
        authority::check_needs_vocabulary(inp.tree, inp.tokens, inp.source, &mut per_file[i]);
    }
    if let Some(r) = root.filter(|&r| r < n) {
        authority::check_main(interner, inputs[r].tree, inputs[r].tokens, inputs[r].source, &decls[r], &mut per_file[r]);
    }

    let file_ctxs: Vec<items::FileCtx> = inputs
        .iter()
        .zip(decls.iter())
        .map(|(inp, d)| items::FileCtx { tree: inp.tree, tokens: inp.tokens, source: inp.source, decls: d })
        .collect();
    let (universe, item_diags) = items::build_universe(interner, &modules, &edges, &file_ctxs);
    for (i, d) in item_diags {
        per_file[i].push(d);
    }

    let mut name_uses: Vec<NameUseTable> = (0..n).map(|_| NameUseTable::default()).collect();
    for (i, inp) in inputs.iter().enumerate() {
        if inp.tree.is_empty() {
            continue;
        }
        resolve_file_bodies(interner, &modules, &universe, FileId(i as u32), inp, &decls[i], &mut per_file[i], &mut name_uses[i]);
    }

    let files = per_file
        .into_iter()
        .zip(decls)
        .zip(name_uses)
        .map(|((diagnostics, decls), name_uses)| FileResult { decls, diagnostics, name_uses })
        .collect();
    ResolveOutput { modules, files, universe }
}

fn resolve_file_bodies(
    interner: &mut Interner,
    modules: &ModuleTable,
    universe: &items::Universe,
    file: FileId,
    inp: &FileInput,
    decls: &DeclTable,
    diags: &mut Vec<Diagnostic>,
    uses: &mut NameUseTable,
) {
    use fors_syntax::NodeKind;
    let Some(module_scope) = universe.scope(file) else { return };
    let mut ctx = scope::BodyCtx::new(inp.tree, inp.tokens, inp.source, interner, modules, universe.exports(), universe.prelude(), file, module_scope, diags, uses);

    for i in 0..decls.len() {
        if decls.parent[i] != fors_index::decl::NO_PARENT {
            continue;
        }
        let node = decls.node[i] as usize;
        match decls.kind[i] {
            fors_index::DeclKind::Fn | fors_index::DeclKind::ExternFn => {
                ctx.push_frame_pub();
                resolve_fn_sig_and_body(&mut ctx, node);
                ctx.pop_frame_pub();
            }
            fors_index::DeclKind::Const => {
                ctx.push_frame_pub();
                for c in inp.tree.children(node) {
                    ctx.walk(c);
                }
                ctx.pop_frame_pub();
            }
            fors_index::DeclKind::Struct => {
                ctx.push_frame_pub();
                let children: Vec<usize> = inp.tree.children(node).collect();
                if let Some(&g) = children.iter().find(|&&c| inp.tree.kinds[c] == NodeKind::Generics) {
                    ctx.resolve_generics(g);
                    ctx.walk_bounds(g);
                }
                for &c in &children {
                    if inp.tree.kinds[c] == NodeKind::Generics {
                        continue;
                    }
                    ctx.walk(c);
                }
                ctx.pop_frame_pub();
            }
            fors_index::DeclKind::Enum => {
                ctx.push_frame_pub();
                let children: Vec<usize> = inp.tree.children(node).collect();
                if let Some(&g) = children.iter().find(|&&c| inp.tree.kinds[c] == NodeKind::Generics) {
                    ctx.resolve_generics(g);
                    ctx.walk_bounds(g);
                }
                for &c in &children {
                    if inp.tree.kinds[c] == NodeKind::Generics {
                        continue;
                    }
                    for gc in inp.tree.children(c) {
                        ctx.walk(gc);
                    }
                }
                ctx.pop_frame_pub();
            }
            fors_index::DeclKind::Trait | fors_index::DeclKind::Impl => {
                ctx.push_frame_pub();
                let children: Vec<usize> = inp.tree.children(node).collect();
                let generics_node = children.iter().copied().find(|&c| inp.tree.kinds[c] == NodeKind::Generics);
                if let Some(g) = generics_node {
                    ctx.resolve_generics(g);
                    ctx.walk_bounds(g);
                }
                // Header types (the impl's target/trait types) see the
                // impl's own gparams but not `Self` (Rule 26).
                let header_types: Vec<usize> = children
                    .iter()
                    .copied()
                    .filter(|&c| Some(c) != generics_node && !matches!(inp.tree.kinds[c], NodeKind::FnDecl | NodeKind::TraitItem | NodeKind::Attribute | NodeKind::Error | NodeKind::AssocTypeDecl | NodeKind::AssocTypeDef))
                    .collect();
                let mut header_targets: Vec<Option<ResolvedTarget>> = Vec::new();
                for &c in &header_types {
                    let mark = ctx.uses.node.len();
                    ctx.walk(c);
                    // A `TypeApp` records its own head first, before its
                    // type arguments; any other type form has no head.
                    header_targets.push(ctx.target_at(mark, c));
                }
                if decls.kind[i] == fors_index::DeclKind::Impl {
                    check_impl_orphan(&mut ctx, file, node, &header_types, &header_targets);
                }
                ctx.declare_self(node);
                // Rule 26 (round 4): an associated-type bound / right-hand
                // side sees the impl's or trait's parameters and `Self`.
                for &c in &children {
                    if matches!(inp.tree.kinds[c], NodeKind::AssocTypeDecl | NodeKind::AssocTypeDef) {
                        for t in inp.tree.children(c) {
                            ctx.walk(t);
                        }
                    }
                }
                for &c in &children {
                    if matches!(inp.tree.kinds[c], NodeKind::FnDecl | NodeKind::TraitItem) {
                        ctx.push_frame_pub();
                        resolve_fn_sig_and_body(&mut ctx, c);
                        ctx.pop_frame_pub();
                    }
                }
                ctx.pop_frame_pub();
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Home {
    Module(FileId),
    /// A prelude type or trait: defined in package `std`.
    Std,
    /// A tuple, `fn`, `dyn` or generic-parameter type: no defining module.
    Nowhere,
    /// The head did not resolve (already diagnosed): not decided here.
    Unknown,
}

/// Ch08 Rule 21's orphan rule. Names only: which module an `impl` may
/// appear in follows from what its header paths resolve to.
fn check_impl_orphan(
    ctx: &mut scope::BodyCtx,
    file: FileId,
    node: usize,
    header_types: &[usize],
    header_targets: &[Option<ResolvedTarget>],
) {
    fn home(t: Option<ResolvedTarget>) -> Home {
        match t {
            Some(ResolvedTarget::Entity(Entity::Item { file, .. } | Entity::Variant { file, .. })) => Home::Module(file),
            Some(ResolvedTarget::Entity(Entity::PreludeType(_) | Entity::PreludeValue(_))) => Home::Std,
            Some(ResolvedTarget::Local { .. }) | None => Home::Nowhere,
            Some(_) => Home::Unknown,
        }
    }
    let (fs, fe) = ctx.tree.token_range(node);
    let body_start = ctx.tree.children(node).find(|&c| matches!(ctx.tree.kinds[c], fors_syntax::NodeKind::FnDecl)).map_or(fe, |c| ctx.tree.token_range(c).0);
    let has_for = (fs as usize..body_start as usize).any(|t| ctx.tokens.kinds.get(t) == Some(&fors_lex::TokenKind::KwFor));

    let homes: Vec<Home> = if has_for && header_types.len() >= 2 {
        vec![home(header_targets[0]), home(header_targets[1])]
    } else if !has_for && header_types.len() == 1 {
        vec![home(header_targets[0])]
    } else {
        return; // malformed header: the parser already reported it
    };
    if homes.contains(&Home::Unknown) {
        return;
    }
    let in_std = ctx.module.in_std();
    if homes.iter().any(|&h| h == Home::Module(file) || (h == Home::Std && in_std)) {
        return;
    }
    let mut permitted: Vec<String> = Vec::new();
    for h in &homes {
        let name = match *h {
            Home::Module(f) => ctx.modules.name.get(f.index()).map(|n| fors_index::module::join_dotted(ctx.interner, n)).unwrap_or_default(),
            Home::Std => "package `std`".to_string(),
            _ => continue,
        };
        if !permitted.contains(&name) {
            permitted.push(name);
        }
    }
    let msg = if permitted.is_empty() {
        "`impl` of a type that has no defining module".to_string()
    } else {
        format!("`impl` must appear in the module defining its trait or its type: {}", permitted.join(" or "))
    };
    let (s, e) = header_types.first().map_or_else(|| paths::byte_range(ctx.tree, ctx.tokens, node), |&h| {
        let last = header_types.last().copied().unwrap_or(h);
        (paths::byte_range(ctx.tree, ctx.tokens, h).0, paths::byte_range(ctx.tree, ctx.tokens, last).1)
    });
    ctx.push_diag(Diagnostic::new(s, e, Code::N(21), msg));
}

fn resolve_fn_sig_and_body(ctx: &mut scope::BodyCtx, fn_node: usize) {
    use fors_syntax::NodeKind;
    let tree = ctx.tree;
    let children: Vec<usize> = tree.children(fn_node).collect();
    let Some(sig_node) = children.iter().copied().find(|&c| tree.kinds[c] == NodeKind::FnSig) else { return };
    let block_node = children.iter().copied().find(|&c| tree.kinds[c] == NodeKind::Block);

    let sig_children: Vec<usize> = tree.children(sig_node).collect();
    let generics_node = sig_children.iter().copied().find(|&c| tree.kinds[c] == NodeKind::Generics);
    if let Some(g) = generics_node {
        ctx.resolve_generics(g);
    }
    let Some(params_node) = sig_children.iter().copied().find(|&c| tree.kinds[c] == NodeKind::Params) else { return };
    // `resolve_params` already walks each parameter's own type before
    // declaring it (round 3, D3), so it is not repeated here.
    let params = ctx.resolve_params(params_node);
    let param_syms = ctx.param_symbols(&params);

    if let Some(g) = generics_node {
        for gp in tree.children(g) {
            for bound in tree.children(gp) {
                ctx.walk(bound);
            }
        }
    }
    let saved = ctx.set_fn_params(param_syms);
    for &c in &sig_children {
        if Some(c) == generics_node || c == params_node || tree.kinds[c] == NodeKind::Contract {
            continue;
        }
        ctx.walk(c);
    }
    ctx.set_fn_params(saved);

    if let Some(b) = block_node {
        ctx.walk(b);
    }
}
