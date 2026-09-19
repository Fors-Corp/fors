//! `fors-index`: per-file declaration index and cross-file module graph
//! for the Fors compiler (spec ch08). Std only, data-oriented: every
//! table is struct-of-arrays columns indexed by a `u32` newtype (see
//! [`ids`]), names are interned [`Symbol`]s, and per-file work
//! ([`decl::build_decl_table`], [`module::extract_module_facts`])
//! depends only on that file's [`fors_syntax::Tree`] and
//! [`fors_lex::Tokens`], so it can run in parallel and be cached per
//! file. Linking those per-file facts into one module graph
//! ([`module::build_module_graph`]) is the one whole-build step, because
//! ch08 Rule 4's "is this prefix a module" test needs the full module
//! name set. Never panics: every failure is a [`diag::Diagnostic`] with a
//! byte range and a stable code.

pub mod decl;
pub mod diag;
pub mod fingerprint;
pub mod ids;
pub mod interner;
pub mod module;

pub use decl::{build_decl_table, DeclKind, DeclTable, Visibility};
pub use diag::{DiagCode, Diagnostic};
pub use fingerprint::{decl_fingerprint, hash_tokens, NO_BODY};
pub use ids::{DeclId, DefId, FileId, ModuleId, ScopeId};
pub use interner::{Interner, Symbol};
pub use module::{build_module_graph, extract_module_facts, module_segments, FileFacts, ModuleTable, Segments};

/// Indexes one file in the single pass the crate's design commits to:
/// its declaration table plus the module facts (header/`use` paths) a
/// later whole-build step links into the module graph.
pub struct FileIndex {
    pub decls: DeclTable,
    pub module_facts: FileFacts,
}

/// Builds a [`FileIndex`] from an already-parsed file. Callers own
/// parsing (`fors_syntax::parse_file`) since a file's `Parse` is also
/// needed by later phases; this never re-parses.
pub fn index_file(
    tree: &fors_syntax::Tree,
    tokens: &fors_lex::Tokens,
    source: &[u8],
    interner: &mut Interner,
) -> FileIndex {
    let decls = build_decl_table(tree, tokens, source, interner);
    let module_facts = extract_module_facts(tree, tokens, source, interner);
    FileIndex { decls, module_facts }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_syntax::parse_file;

    #[test]
    fn index_file_smoke() {
        let src = "module m;\nuse other;\npub fn f() -> i32 { return 1; }\n";
        let p = parse_file(src.as_bytes());
        let mut interner = Interner::new();
        let idx = index_file(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        assert_eq!(idx.decls.len(), 3); // module header, use, fn
        assert!(idx.module_facts.header.is_some());
        assert_eq!(idx.module_facts.uses.len(), 1);
    }
}
