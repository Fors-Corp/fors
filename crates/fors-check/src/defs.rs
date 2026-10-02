//! `DefTable`: the build-wide declaration table (design §4.2, §5.3).
//!
//! `fors-index` gives every file a `DeclTable` whose `DeclId` is a per-file
//! row index that renumbers on insertion; `fors-fir` keys everything on a
//! name-based `DeclKeyId` and numbers the build's rows with `DefId`. This
//! table is the join: one row per declaration in the build, in
//! `(module bytes, DeclKey bytes)` order, plus the `def_of[file][decl]` map
//! `Entity::Item { file, decl }` needs.

use fors_fir::Fir;
use fors_fir::defpath::{DeclKey, DeclKeyId, ModulePathId, NO_DECL_KEY, NO_DEF};
use fors_index::decl::{DeclKind, NO_PARENT, Visibility};
use fors_index::ids::{DeclId, DefId, FileId, ModuleId};
use fors_index::{DeclTable, Symbol};
use fors_lex::{TokenKind, Tokens};
use fors_syntax::Tree;

/// Design §3 fork 13's impl disambiguator: "a 32-bit fold of the header
/// tokens (edit-local, order-independent)".
///
/// MARC: I2 used `splitmix64((range_start << 32) | range_end)` — the
/// declaration's TOKEN POSITIONS — which is neither edit-local nor
/// order-independent: inserting anything above an impl moved its `DeclKey`,
/// and therefore the canonical `sig_hash` of the impl AND of every member
/// whose signature names its owner. I9's oracle
/// (`fors_check::queries`, `check_output_identical_cold_vs_incremental`)
/// caught it as a stale-accept risk the moment a memo depended on the key
/// surviving an edit. This is fork 13's version: the header's own tokens,
/// from `impl` up to the body's opening brace, by kind and text. Everything
/// inside the body — a method, an associated-type definition — is therefore
/// NOT part of the impl's identity, which is what makes
/// `assoc_type_def_edit_is_signature_level` a signature edit rather than a
/// new declaration.
pub fn impl_header_fold(tree: &Tree, tokens: &Tokens, source: &[u8], node: u32) -> u32 {
    let (first, end) = tree.token_range(node as usize);
    let mut stop = end;
    for i in first..end {
        if tokens.kinds[i as usize] == TokenKind::LBrace {
            stop = i;
            break;
        }
    }
    // A header cannot contain a `{`: generics are bracketed, bounds are
    // colon-separated.
    fors_index::hash_tokens(tokens, source, first, stop.max(first)) as u32
}

/// One build-wide declaration.
#[derive(Clone, Copy)]
pub struct DefRow {
    pub file: FileId,
    pub decl: DeclId,
    pub module: ModuleId,
    pub kind: DeclKind,
    pub name: Option<Symbol>,
    pub vis: Visibility,
    /// The enclosing `impl`/`trait`'s `DefId`, or [`NO_DEF`].
    pub parent: DefId,
    pub key: DeclKeyId,
    /// The declaration's CST node in its own file's tree.
    pub node: u32,
}

/// Build-wide, indexed by `DefId` (design §4.2 `defs.rs`). Rows below
/// `first_user` are the prelude's and have no file.
pub struct DefTable {
    rows: Vec<Option<DefRow>>,
    /// `def_of[file][decl]`.
    def_of: Vec<Vec<DefId>>,
    /// `(file, tree node) -> DefId`, sorted: the map a member list needs to
    /// turn an `impl`/`trait` body's `fn` node into its own row.
    by_node: Vec<(u32, u32, DefId)>,
    /// The lowest `DefId` that belongs to user source.
    pub first_user: DefId,
}

impl DefTable {
    pub fn get(&self, def: DefId) -> Option<&DefRow> {
        self.rows.get(def.index()).and_then(|r| r.as_ref())
    }

    /// The declaration whose CST node is `node` in `file`.
    pub fn def_at(&self, file: FileId, node: u32) -> DefId {
        match self
            .by_node
            .binary_search_by_key(&(file.0, node), |&(f, n, _)| (f, n))
        {
            Ok(i) => self.by_node[i].2,
            Err(_) => NO_DEF,
        }
    }

    pub fn def_of(&self, file: FileId, decl: DeclId) -> DefId {
        self.def_of
            .get(file.index())
            .and_then(|f| f.get(decl.index()))
            .copied()
            .unwrap_or(NO_DEF)
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// Every user declaration, in `DefId` order.
    pub fn user_defs(&self) -> impl Iterator<Item = (DefId, &DefRow)> {
        self.rows
            .iter()
            .enumerate()
            .skip(self.first_user.index())
            .filter_map(|(i, r)| r.as_ref().map(|r| (DefId(i as u32), r)))
    }
}

/// A file's module path as a [`ModulePathId`], plus its `ModuleId`.
pub struct FileModule {
    pub id: ModuleId,
    pub path: ModulePathId,
}

/// Builds the table. `decls[f]` is file `f`'s declaration table,
/// `modules[f]` its module and `files[f]` its CST (read only for an `impl`'s
/// header fold, [`impl_header_fold`]); `first_user` is `fir.sigs.len()` at
/// entry (every row already present is the prelude's).
pub fn build(
    fir: &mut Fir,
    decls: &[&DeclTable],
    modules: &[FileModule],
    files: &[crate::lower::FileCtx],
) -> DefTable {
    let first_user = DefId(fir.sigs.len() as u32);
    let mut rows: Vec<Option<DefRow>> = (0..fir.sigs.len()).map(|_| None).collect();
    let mut def_of: Vec<Vec<DefId>> = Vec::with_capacity(decls.len());
    let mut by_node: Vec<(u32, u32, DefId)> = Vec::new();

    // An impl has no name, so `DeclKey.disamb` separates two impls of one
    // module: a 32-bit fold of the header's own byte range, then +1 per
    // duplicate in source order (§5.3).
    for (f, table) in decls.iter().enumerate() {
        let file = FileId(f as u32);
        let path = modules[f].path;
        let mut per_file: Vec<DefId> = vec![NO_DEF; table.len()];
        let mut seen_disamb: Vec<(ModulePathId, DeclKeyId, u32)> = Vec::new();
        for d in 0..table.len() {
            let kind = table.kind[d];
            if !matches!(
                kind,
                DeclKind::Fn
                    | DeclKind::ExternFn
                    | DeclKind::Struct
                    | DeclKind::Enum
                    | DeclKind::Trait
                    | DeclKind::Impl
                    | DeclKind::Const
            ) {
                continue;
            }
            let parent_decl = table.parent[d];
            let parent_key = if parent_decl == NO_PARENT {
                NO_DECL_KEY
            } else {
                let p = per_file[parent_decl as usize];
                if p == NO_DEF {
                    NO_DECL_KEY
                } else {
                    fir.defs.key_of(p)
                }
            };
            let mut disamb = 0u32;
            if kind != DeclKind::Impl {
                // Two declarations with the same name, kind and parent are
                // already ch08 R27's error; they must still get one row each,
                // or a member list would name a `DefId` that belongs to the
                // other one. The disambiguator is what keeps the key injective.
                let mut probe = DeclKey {
                    parent: parent_key,
                    module: path,
                    kind,
                    name: table.name[d],
                    disamb,
                };
                while fir
                    .keys
                    .try_find(probe)
                    .is_some_and(|k| fir.defs.def_of(k) != NO_DEF)
                {
                    disamb = disamb.wrapping_add(1);
                    probe.disamb = disamb;
                }
            }
            if kind == DeclKind::Impl {
                // Fork 13's content fold, not a position: two impls with
                // identical headers differ only by source order, which the +1
                // below supplies.
                disamb = impl_header_fold(
                    files[f].tree,
                    files[f].tokens,
                    files[f].source,
                    table.node[d],
                );
                while seen_disamb
                    .iter()
                    .any(|&(m, p, x)| m == path && p == parent_key && x == disamb)
                {
                    disamb = disamb.wrapping_add(1);
                }
                seen_disamb.push((path, parent_key, disamb));
            }
            let key = fir.keys.intern(DeclKey {
                parent: parent_key,
                module: path,
                kind,
                name: table.name[d],
                disamb,
            });
            let def = fir.declare(key, kind_to_sig(kind));
            per_file[d] = def;
            by_node.push((file.0, table.node[d], def));
            while rows.len() <= def.index() {
                rows.push(None);
            }
            rows[def.index()] = Some(DefRow {
                file,
                decl: DeclId(d as u32),
                module: modules[f].id,
                kind,
                name: table.name[d],
                vis: table.vis[d],
                parent: if parent_decl == NO_PARENT {
                    NO_DEF
                } else {
                    per_file[parent_decl as usize]
                },
                key,
                node: table.node[d],
            });
        }
        def_of.push(per_file);
    }
    while rows.len() < fir.sigs.len() {
        rows.push(None);
    }
    by_node.sort_unstable_by_key(|&(f, n, _)| (f, n));
    by_node.dedup_by_key(|&mut (f, n, _)| (f, n));
    DefTable {
        rows,
        def_of,
        by_node,
        first_user,
    }
}

fn kind_to_sig(k: DeclKind) -> fors_fir::sig::SigKind {
    use fors_fir::sig::SigKind as S;
    match k {
        DeclKind::Fn => S::Fn,
        DeclKind::ExternFn => S::ExternFn,
        DeclKind::Struct => S::Struct,
        DeclKind::Enum => S::Enum,
        DeclKind::Trait => S::Trait,
        DeclKind::Impl => S::Impl,
        DeclKind::Const => S::Const,
        _ => S::Absent,
    }
}
