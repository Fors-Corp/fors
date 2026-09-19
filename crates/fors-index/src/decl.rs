//! The per-file declaration table: one pass over a [`fors_syntax::Tree`],
//! columns indexed by [`DeclId`]. Depends only on that file's tokens and
//! tree (per-file, parallelisable, cacheable per declaration).

use fors_lex::{TokenKind, Tokens};
use fors_syntax::{NodeKind, Tree};

use crate::fingerprint::decl_fingerprint;
use crate::ids::DeclId;
use crate::interner::{Interner, Symbol};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeclKind {
    Fn,
    ExternFn,
    Struct,
    Enum,
    Trait,
    Impl,
    Const,
    Use,
    ModuleHeader,
    Needs,
    Inputs,
    Contracts,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Visibility {
    Public,
    Private,
}

pub const MOD_PUB: u8 = 1 << 0;
pub const MOD_SOA: u8 = 1 << 1;

/// No enclosing declaration (a top-level entry).
pub const NO_PARENT: u32 = u32::MAX;

/// Struct-of-arrays declaration table for one file. A `fn` nested in an
/// `impl`/`trait` body is its own row with `parent` set to that row's
/// [`DeclId`], so its fingerprint can be recomputed and cached
/// independently of its container's signature.
#[derive(Default)]
pub struct DeclTable {
    pub kind: Vec<DeclKind>,
    pub name: Vec<Option<Symbol>>,
    pub vis: Vec<Visibility>,
    /// Bitset of `MOD_PUB` / `MOD_SOA`.
    pub modifiers: Vec<u8>,
    /// Index of the declaration's node in the file's `Tree`.
    pub node: Vec<u32>,
    /// Raw token range `[start, end)`, including leading trivia
    /// (comments and whitespace immediately above the declaration).
    pub range_start: Vec<u32>,
    pub range_end: Vec<u32>,
    /// Signature/body fingerprint (see `fingerprint::decl_fingerprint`).
    pub sig_hash: Vec<u128>,
    pub body_hash: Vec<u128>,
    /// `NO_PARENT`, or the enclosing `impl`/`trait`'s `DeclId.0`.
    pub parent: Vec<u32>,
    /// `[attr_start[i], attr_end[i])` into `attr_names`: this
    /// declaration's attribute names, in source order.
    pub attr_start: Vec<u32>,
    pub attr_end: Vec<u32>,
    pub attr_names: Vec<Symbol>,
}

impl DeclTable {
    pub fn len(&self) -> usize {
        self.kind.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kind.is_empty()
    }

    #[allow(clippy::too_many_arguments)]
    fn push(
        &mut self,
        kind: DeclKind,
        name: Option<Symbol>,
        vis: Visibility,
        modifiers: u8,
        node: u32,
        range: (u32, u32),
        hashes: (u128, u128),
        parent: Option<DeclId>,
        attrs: &[Symbol],
    ) -> DeclId {
        let id = DeclId(self.kind.len() as u32);
        self.kind.push(kind);
        self.name.push(name);
        self.vis.push(vis);
        self.modifiers.push(modifiers);
        self.node.push(node);
        self.range_start.push(range.0);
        self.range_end.push(range.1);
        self.sig_hash.push(hashes.0);
        self.body_hash.push(hashes.1);
        self.parent.push(parent.map_or(NO_PARENT, |p| p.0));
        let start = self.attr_names.len() as u32;
        self.attr_names.extend_from_slice(attrs);
        self.attr_start.push(start);
        self.attr_end.push(self.attr_names.len() as u32);
        id
    }
}

fn is_sig(tokens: &Tokens, i: usize) -> bool {
    !tokens.kinds[i].is_trivia()
}

fn first_sig(tokens: &Tokens, mut i: usize, end: usize) -> Option<usize> {
    while i < end {
        if is_sig(tokens, i) {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn next_sig(tokens: &Tokens, i: usize, end: usize) -> Option<usize> {
    first_sig(tokens, i + 1, end)
}

/// Builds the declaration table for one parsed file in a single pass over
/// `tree`'s top-level children (plus, for each `impl`/`trait`, one more
/// pass over its own children for member `fn`s).
pub fn build_decl_table(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner) -> DeclTable {
    let mut t = DeclTable::default();
    if tree.is_empty() {
        return t;
    }
    for child in tree.children(0) {
        visit(&mut t, tree, tokens, source, interner, child, None);
    }
    t
}

fn visit(
    t: &mut DeclTable,
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    i: usize,
    parent: Option<DeclId>,
) {
    use NodeKind::*;
    match tree.kinds[i] {
        ModuleHdr => push_header(t, tree, i, DeclKind::ModuleHeader),
        ContractsClause => push_header(t, tree, i, DeclKind::Contracts),
        NeedsClause => push_header(t, tree, i, DeclKind::Needs),
        InputsClause => push_header(t, tree, i, DeclKind::Inputs),
        UseDecl => push_header(t, tree, i, DeclKind::Use),
        FnDecl | ExternFnDecl | StructDecl | EnumDecl | TraitDecl | ImplDecl | ConstDecl | TraitItem => {
            let kind = match tree.kinds[i] {
                FnDecl | TraitItem => DeclKind::Fn,
                ExternFnDecl => DeclKind::ExternFn,
                StructDecl => DeclKind::Struct,
                EnumDecl => DeclKind::Enum,
                TraitDecl => DeclKind::Trait,
                ImplDecl => DeclKind::Impl,
                ConstDecl => DeclKind::Const,
                _ => return,
            };
            let id = build_decl(t, tree, tokens, source, interner, i, kind, parent);
            if matches!(tree.kinds[i], ImplDecl | TraitDecl) {
                for member in tree.children(i) {
                    if matches!(tree.kinds[member], FnDecl | TraitItem) {
                        visit(t, tree, tokens, source, interner, member, Some(id));
                    }
                }
            }
        }
        _ => {}
    }
}

/// A header clause or `use`: no name, the whole node is its signature, no
/// separate body.
fn push_header(t: &mut DeclTable, tree: &Tree, i: usize, kind: DeclKind) {
    let range = tree.token_range(i);
    t.push(
        kind,
        None,
        Visibility::Private,
        0,
        i as u32,
        range,
        (crate::fingerprint::NO_BODY, crate::fingerprint::NO_BODY),
        None,
        &[],
    );
}

const KEYWORD_KINDS: [TokenKind; 4] = [TokenKind::KwStruct, TokenKind::KwEnum, TokenKind::KwTrait, TokenKind::KwConst];

#[allow(clippy::too_many_arguments)]
fn build_decl(
    t: &mut DeclTable,
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    i: usize,
    kind: DeclKind,
    parent: Option<DeclId>,
) -> DeclId {
    let (first, end) = tree.token_range(i);
    let children: Vec<usize> = tree.children(i).collect();
    let attr_count = children.iter().take_while(|&&c| tree.kinds[c] == NodeKind::Attribute).count();
    let (attr_kids, rest) = children.split_at(attr_count);

    let mut attrs = Vec::with_capacity(attr_kids.len());
    for &a in attr_kids {
        let (as_, ae) = tree.token_range(a);
        if let Some(at) = first_sig(tokens, as_ as usize, ae as usize) {
            if let Some(name_tok) = next_sig(tokens, at, ae as usize) {
                if tokens.kinds[name_tok] == TokenKind::Ident {
                    attrs.push(interner.intern(tokens.text(name_tok, source)));
                }
            }
        }
    }

    let gap_start = attr_kids.last().map_or(first, |&a| tree.token_range(a).1);
    let gap_end = rest.first().map_or(end, |&c| tree.token_range(c).0);

    let mut has_pub = false;
    let mut has_soa = false;
    let mut keyword_at: Option<usize> = None;
    {
        let mut p = gap_start as usize;
        let g_end = gap_end as usize;
        while let Some(s) = first_sig(tokens, p, g_end) {
            let k = tokens.kinds[s];
            if k == TokenKind::KwPub {
                has_pub = true;
            } else if k == TokenKind::Ident && tokens.text(s, source) == b"soa" {
                has_soa = true;
            } else if KEYWORD_KINDS.contains(&k) {
                keyword_at = Some(s);
            }
            p = s + 1;
        }
    }

    let name = match kind {
        DeclKind::Fn | DeclKind::ExternFn => rest
            .iter()
            .find(|&&c| tree.kinds[c] == NodeKind::FnSig)
            .and_then(|&fs| {
                let (fs_first, fs_end) = tree.token_range(fs);
                let fn_tok = first_sig(tokens, fs_first as usize, fs_end as usize)?;
                let name_tok = next_sig(tokens, fn_tok, fs_end as usize)?;
                (tokens.kinds[name_tok] == TokenKind::Ident).then(|| interner.intern(tokens.text(name_tok, source)))
            }),
        DeclKind::Struct | DeclKind::Enum | DeclKind::Trait | DeclKind::Const => keyword_at.and_then(|k| {
            let name_tok = next_sig(tokens, k, gap_end as usize)?;
            (tokens.kinds[name_tok] == TokenKind::Ident).then(|| interner.intern(tokens.text(name_tok, source)))
        }),
        DeclKind::Impl => None,
        _ => None,
    };

    let (sig_range, body_range) = match kind {
        DeclKind::Fn | DeclKind::ExternFn => match rest.iter().find(|&&c| tree.kinds[c] == NodeKind::Block) {
            Some(&block) => {
                let block_range = tree.token_range(block);
                ((first, block_range.0), Some(block_range))
            }
            None => ((first, end), None),
        },
        DeclKind::Const => match rest.len() {
            0 | 1 => ((first, end), None),
            _ => {
                let split = tree.token_range(rest[1]).0;
                ((first, split), Some((split, end)))
            }
        },
        DeclKind::Struct | DeclKind::Enum | DeclKind::Trait | DeclKind::Impl => ((first, end), None),
        DeclKind::Use | DeclKind::ModuleHeader | DeclKind::Needs | DeclKind::Inputs | DeclKind::Contracts => {
            ((first, end), None)
        }
    };
    let hashes = decl_fingerprint(tokens, source, sig_range, body_range);

    let modifiers = if has_pub { MOD_PUB } else { 0 } | if has_soa { MOD_SOA } else { 0 };
    let vis = if has_pub { Visibility::Public } else { Visibility::Private };

    t.push(kind, name, vis, modifiers, i as u32, (first, end), hashes, parent, &attrs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_syntax::parse_file;

    fn index(src: &str) -> (DeclTable, Interner) {
        let p = parse_file(src.as_bytes());
        let mut interner = Interner::new();
        let t = build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        (t, interner)
    }

    fn name_str(t: &DeclTable, interner: &Interner, i: usize) -> Option<String> {
        t.name[i].map(|s| String::from_utf8_lossy(interner.resolve(s)).into_owned())
    }

    #[test]
    fn one_pass_fn_struct_const() {
        let src = "pub fn f() -> i32 { return 1; }\nstruct S { x: i32 }\nconst C: i32 = 1;\n";
        let (t, interner) = index(src);
        assert_eq!(t.len(), 3);
        assert_eq!(t.kind[0], DeclKind::Fn);
        assert_eq!(name_str(&t, &interner, 0).as_deref(), Some("f"));
        assert_eq!(t.vis[0], Visibility::Public);
        assert_eq!(t.kind[1], DeclKind::Struct);
        assert_eq!(name_str(&t, &interner, 1).as_deref(), Some("S"));
        assert_eq!(t.kind[2], DeclKind::Const);
        assert_eq!(name_str(&t, &interner, 2).as_deref(), Some("C"));
    }

    #[test]
    fn soa_struct_modifier() {
        let (t, _) = index("soa struct P { x: i32 }\n");
        assert_eq!(t.kind[0], DeclKind::Struct);
        assert_ne!(t.modifiers[0] & MOD_SOA, 0);
    }

    #[test]
    fn impl_nests_member_fns() {
        let src = "struct S { x: i32 }\nimpl S { pub fn get(let self: S) -> i32 { return self.x; } }\n";
        let (t, interner) = index(src);
        let impl_idx = t.kind.iter().position(|&k| k == DeclKind::Impl).unwrap();
        let fn_idx = t.kind.iter().position(|&k| k == DeclKind::Fn).unwrap();
        assert_eq!(t.parent[fn_idx], impl_idx as u32);
        assert_eq!(name_str(&t, &interner, fn_idx).as_deref(), Some("get"));
    }

    #[test]
    fn attribute_names_recorded() {
        let (t, interner) = index("@inline\nfn f() {}\n");
        let (s, e) = (t.attr_start[0] as usize, t.attr_end[0] as usize);
        assert_eq!(e - s, 1);
        assert_eq!(String::from_utf8_lossy(interner.resolve(t.attr_names[s])), "inline");
    }

    #[test]
    fn range_includes_leading_trivia() {
        let src = "// doc\nfn f() {}\n";
        let (t, _) = index(src);
        assert_eq!(t.range_start[0], 0);
    }
}
