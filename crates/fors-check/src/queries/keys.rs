//! Stable declaration keys: the identity a query node keeps across
//! revisions (design §5.3, §9: "query keys are name-based `DeclKey`s").
//!
//! `fors-fir`'s `DeclKeyId` is an interning slot and `DefId` is a build row
//! number; both renumber when a declaration is inserted, so neither can name
//! a memo entry that must survive an edit. What survives is the key's
//! *content*: the module path, the declaration kind, the name, the parent
//! chain and an edit-local disambiguator, folded to 64 bits.
//!
//! The disambiguator matters. An `impl` has no name, so design §3 fork 13
//! makes its disambiguator "a 32-bit fold of the header tokens (edit-local,
//! order-independent)" — [`crate::defs::impl_header_fold`], the same function
//! the FIR `DeclKey` uses, so the query key and the canonical signature hash
//! agree on what an impl IS. For everything else the disambiguator is the
//! duplicate index among declarations agreeing on parent, kind and name (ch08
//! R27's error, which still has to produce one row each).

use fors_index::decl::{DeclKind, NO_PARENT};
use fors_index::{DeclTable, Interner, Segments};
use fors_lex::Tokens;
use fors_syntax::Tree;

/// A declaration's identity across revisions.
pub type StableKey = u64;

/// Every declaration of one file, indexed by `DeclId` (`0` for a row with no
/// key, which cannot happen for the kinds `defs::build` keeps).
pub fn file_decl_keys(
    module: &Segments,
    decls: &DeclTable,
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &Interner,
) -> Vec<StableKey> {
    let mut out = vec![0u64; decls.len()];
    let mut module_bytes: Vec<u8> = Vec::new();
    for &seg in module {
        module_bytes.extend_from_slice(interner.resolve(seg));
        module_bytes.push(0xFF);
    }
    // (parent row, kind byte, name or header fold) -> how many have been seen.
    // `defs::build` does the same bump for the same reason: two declarations
    // that agree on everything the key is made of must still get one row each,
    // and two impls of one module CAN agree on their whole header (they differ
    // only in their associated-type definitions, which ch09 R19 rejects — but
    // the diagnostic has to be attributed to ONE of them, and a shared key
    // would print it twice).
    let mut seen: Vec<((u32, u8, u64), u32)> = Vec::new();
    let mut enc: Vec<u8> = Vec::new();
    for d in 0..decls.len() {
        let parent = decls.parent[d];
        let parent_key = if parent == NO_PARENT {
            0u64
        } else {
            out[parent as usize]
        };
        let kind = decls.kind[d] as u8;
        let own = if decls.kind[d] == DeclKind::Impl {
            crate::defs::impl_header_fold(tree, tokens, source, decls.node[d]) as u64
        } else {
            decls.name[d].map_or(u64::MAX, |s| s.0 as u64)
        };
        let base = if decls.kind[d] == DeclKind::Impl {
            own
        } else {
            0
        };
        let k = (parent, kind, own);
        let bump = match seen.iter_mut().find(|(x, _)| *x == k) {
            Some((_, n)) => {
                *n += 1;
                *n as u64
            }
            None => {
                seen.push((k, 0));
                0
            }
        };
        let disamb = base.wrapping_add(bump);
        enc.clear();
        enc.extend_from_slice(&module_bytes);
        enc.push(0xFE);
        enc.push(kind);
        match decls.name[d] {
            Some(s) => enc.extend_from_slice(interner.resolve(s)),
            None => enc.push(0x00),
        }
        enc.push(0xFE);
        enc.extend_from_slice(&disamb.to_le_bytes());
        enc.extend_from_slice(&parent_key.to_le_bytes());
        out[d] = fors_index::hash_bytes(&enc) as u64;
    }
    out
}

/// The byte at which `decl`'s first significant token starts: the origin
/// every cached diagnostic of that declaration is stored relative to, so an
/// edit earlier in the file does not move a green declaration's
/// diagnostics.
pub fn decl_origin(tree: &Tree, tokens: &Tokens, node: u32) -> u32 {
    let (first, _) = tree.token_range(node as usize);
    tokens.starts.get(first as usize).copied().unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_syntax::parse_file;

    fn keys(src: &str) -> (Vec<StableKey>, DeclTable, Interner) {
        let mut interner = Interner::new();
        let p = parse_file(src.as_bytes());
        assert!(p.diags.is_empty(), "{:?}", p.diags);
        let decls = fors_index::build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        let module = vec![interner.intern(b"m")];
        let k = file_decl_keys(
            &module,
            &decls,
            &p.tree,
            &p.tokens,
            src.as_bytes(),
            &interner,
        );
        (k, decls, interner)
    }

    fn named(src: &str, want: &str) -> StableKey {
        let (k, decls, interner) = keys(src);
        for (d, &key) in k.iter().enumerate() {
            if decls.name[d].map(|s| interner.resolve(s).to_vec()) == Some(want.as_bytes().to_vec())
            {
                return key;
            }
        }
        panic!("no declaration named {want}");
    }

    #[test]
    fn inserting_a_declaration_above_does_not_move_a_key() {
        let a = named("module m;\nfn f() { }\n", "f");
        let b = named("module m;\nfn before() { }\nfn f() { }\n", "f");
        assert_eq!(a, b);
    }

    #[test]
    fn an_impls_key_survives_an_insertion_above_it() {
        let one = "module m;\nstruct S { x: i32 }\ntrait Tr { fn go(let self) -> i32; }\nimpl Tr for S { fn go(let self: S) -> i32 { return self.x; } }\n";
        let two = "module m;\nstruct S { x: i32 }\nconst K: i32 = 1;\ntrait Tr { fn go(let self) -> i32; }\nimpl Tr for S { fn go(let self: S) -> i32 { return self.x; } }\n";
        let (ka, da, _) = keys(one);
        let (kb, db, _) = keys(two);
        let a = (0..da.len())
            .find(|&d| da.kind[d] == DeclKind::Impl)
            .map(|d| ka[d])
            .expect("an impl");
        let b = (0..db.len())
            .find(|&d| db.kind[d] == DeclKind::Impl)
            .map(|d| kb[d])
            .expect("an impl");
        assert_eq!(a, b, "an impl key must be edit-local (design §3 fork 13)");
    }

    #[test]
    fn an_impls_key_ignores_its_method_bodies() {
        let one = "module m;\nstruct S { x: i32 }\nimpl S { fn go(let self: S) -> i32 { return self.x; } }\n";
        let two = "module m;\nstruct S { x: i32 }\nimpl S { fn go(let self: S) -> i32 { return self.x + 1; } }\n";
        let (ka, da, _) = keys(one);
        let (kb, db, _) = keys(two);
        let pick = |k: &Vec<StableKey>, d: &DeclTable| {
            (0..d.len())
                .find(|&i| d.kind[i] == DeclKind::Impl)
                .map(|i| k[i])
                .expect("an impl")
        };
        assert_eq!(
            pick(&ka, &da),
            pick(&kb, &db),
            "an impl's identity must not depend on its members' bodies"
        );
    }

    #[test]
    fn re_heading_an_impl_is_a_new_key() {
        let one = "module m;\nstruct S { x: i32 }\nstruct T { x: i32 }\nimpl S { fn go(let self: S) -> i32 { return self.x; } }\n";
        let two = "module m;\nstruct S { x: i32 }\nstruct T { x: i32 }\nimpl T { fn go(let self: T) -> i32 { return self.x; } }\n";
        let (ka, da, _) = keys(one);
        let (kb, db, _) = keys(two);
        let pick = |k: &Vec<StableKey>, d: &DeclTable| {
            (0..d.len())
                .find(|&i| d.kind[i] == DeclKind::Impl)
                .map(|i| k[i])
                .expect("an impl")
        };
        assert_ne!(pick(&ka, &da), pick(&kb, &db));
    }

    #[test]
    fn a_body_edit_does_not_move_a_key() {
        let a = named("module m;\nfn f() -> i32 { return 1; }\n", "f");
        let b = named("module m;\nfn f() -> i32 { return 2; }\n", "f");
        assert_eq!(a, b);
    }

    #[test]
    fn two_declarations_never_share_a_key() {
        let (k, decls, _) = keys(
            "module m;\nfn f() { }\nfn g() { }\nstruct S { x: i32 }\ntrait T { fn h(let self); }\n",
        );
        let mut v: Vec<u64> = (0..decls.len()).map(|d| k[d]).collect();
        let n = v.len();
        v.sort_unstable();
        v.dedup();
        assert_eq!(v.len(), n, "keys must be injective over a file");
    }

    #[test]
    fn a_method_key_depends_on_its_container() {
        let one = "module m;\nstruct A { x: i32 }\nstruct B { x: i32 }\nimpl A { fn go(let self: A) -> i32 { return self.x; } }\nimpl B { fn go(let self: B) -> i32 { return self.x; } }\n";
        let (k, decls, interner) = keys(one);
        let gos: Vec<u64> = (0..decls.len())
            .filter(|&d| {
                decls.name[d].map(|s| interner.resolve(s).to_vec()) == Some(b"go".to_vec())
            })
            .map(|d| k[d])
            .collect();
        assert_eq!(gos.len(), 2);
        assert_ne!(gos[0], gos[1]);
    }

    #[test]
    fn the_same_name_in_two_modules_is_two_keys() {
        let mut interner = Interner::new();
        let src = "module m;\nfn f() { }\n";
        let p = parse_file(src.as_bytes());
        let decls = fors_index::build_decl_table(&p.tree, &p.tokens, src.as_bytes(), &mut interner);
        let m1 = vec![interner.intern(b"a")];
        let m2 = vec![interner.intern(b"b")];
        let k1 = file_decl_keys(&m1, &decls, &p.tree, &p.tokens, src.as_bytes(), &interner);
        let k2 = file_decl_keys(&m2, &decls, &p.tree, &p.tokens, src.as_bytes(), &interner);
        assert_ne!(k1[0], k2[0]);
    }
}
