//! Ch04 rules decidable from names and the module graph alone: the
//! `needs` capability vocabulary (Rule 1) and `main`'s structural/
//! parameter rules (Rule 8, the closed type list of Rule 21). Anything
//! needing a type or the manifest (the requirement/policy subset check,
//! sealed capabilities, comptime, `asm`) is out of scope here.

use fors_index::{DeclTable, Interner};
use fors_lex::{TokenKind, Tokens};
use fors_syntax::{NodeKind, Tree};

use crate::diag::{Code, Diagnostic};
use crate::paths::byte_range;

/// The `needs` capability vocabulary (ch04 Definitions).
const CAPABILITIES: [&[&[u8]]; 14] = [
    &[b"fs", b"read"],
    &[b"fs", b"write"],
    &[b"net"],
    &[b"exec"],
    &[b"ffi"],
    &[b"clock"],
    &[b"rng"],
    &[b"env"],
    &[b"io", b"stdout"],
    &[b"io", b"stderr"],
    &[b"io", b"stdin"],
    &[b"gpu"],
    &[b"asm"],
    &[b"syscall"],
];

/// Ch04 Rule 21's closed root-capability list: `main` parameter type ->
/// the capability it requires in root `needs`.
const MAIN_PARAM_TYPES: [(&[&[u8]], &[&[u8]]); 11] = [
    (&[b"io", b"Stdout"], &[b"io", b"stdout"]),
    (&[b"io", b"Stderr"], &[b"io", b"stderr"]),
    (&[b"io", b"Stdin"], &[b"io", b"stdin"]),
    (&[b"fs", b"Dir"], &[b"fs", b"read"]), // or fs.write; checked specially below
    (&[b"net", b"Net"], &[b"net"]),
    (&[b"proc", b"Exec"], &[b"exec"]),
    (&[b"time", b"Clock"], &[b"clock"]),
    (&[b"rand", b"Rng"], &[b"rng"]),
    (&[b"env", b"Env"], &[b"env"]),
    (&[b"env", b"Args"], &[b"env"]),
    (&[b"gpu", b"Device"], &[b"gpu"]),
];

fn is_sig(tokens: &Tokens, i: usize) -> bool {
    !tokens.kinds[i].is_trivia()
}

fn eq_words(a: &[Vec<u8>], b: &[&[u8]]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.as_slice() == *y)
}

fn words(tree: &Tree, tokens: &Tokens, source: &[u8], node: usize) -> Vec<Vec<u8>> {
    let (first, end) = tree.token_range(node);
    let mut out = Vec::new();
    for i in first as usize..end as usize {
        if is_sig(tokens, i) && matches!(tokens.kinds[i], TokenKind::Ident | TokenKind::KwAsm) {
            out.push(tokens.text(i, source).to_vec());
        }
    }
    out
}

/// Ch04 Rule 1's needs vocabulary: every path in a `NeedsClause` must
/// spell one of the fourteen capability words.
pub fn check_needs_vocabulary(tree: &Tree, tokens: &Tokens, source: &[u8], diags: &mut Vec<Diagnostic>) {
    if tree.is_empty() {
        return;
    }
    for child in tree.children(0) {
        if tree.kinds[child] != NodeKind::NeedsClause {
            continue;
        }
        for path_node in tree.children(child) {
            let w = words(tree, tokens, source, path_node);
            if !CAPABILITIES.iter().any(|c| eq_words(&w, c)) {
                let r = byte_range(tree, tokens, path_node);
                diags.push(Diagnostic::new(r.0, r.1, Code::A(1), "not a declared capability word".to_string()));
            }
        }
    }
}

/// The words named in a module's `needs { ... };` (empty if absent, ch04
/// Rule 1: "An absent `needs` clause MUST mean `needs {};`").
fn needs_words(tree: &Tree, tokens: &Tokens, source: &[u8]) -> Vec<Vec<Vec<u8>>> {
    if tree.is_empty() {
        return Vec::new();
    }
    for child in tree.children(0) {
        if tree.kinds[child] == NodeKind::NeedsClause {
            return tree.children(child).map(|p| words(tree, tokens, source, p)).collect();
        }
    }
    Vec::new()
}

/// Ch04 Rule 8/21: `main`'s structural and parameter rules, checked only
/// for the function literally named `main` in the build's root module
/// (`root` is that file's already-parsed tree/tokens/source/decls).
pub fn check_main(
    interner: &mut Interner,
    root_tree: &Tree,
    root_tokens: &Tokens,
    root_source: &[u8],
    root_decls: &DeclTable,
    diags: &mut Vec<Diagnostic>,
) {
    let main_sym = interner.intern(b"main");
    let Some(row) = (0..root_decls.len()).find(|&i| {
        root_decls.parent[i] == fors_index::decl::NO_PARENT
            && matches!(root_decls.kind[i], fors_index::DeclKind::Fn | fors_index::DeclKind::ExternFn)
            && root_decls.name[i] == Some(main_sym)
    }) else {
        return;
    };
    let range = (root_decls.range_start[row], root_decls.range_end[row]);
    if root_decls.kind[row] == fors_index::DeclKind::ExternFn {
        diags.push(Diagnostic::new(range.0, range.1, Code::A(8), "`main` must not be `extern`".to_string()));
        return;
    }
    let node = root_decls.node[row] as usize;
    let Some(sig) = root_tree.children(node).find(|&c| root_tree.kinds[c] == NodeKind::FnSig) else { return };
    let sig_children: Vec<usize> = root_tree.children(sig).collect();
    if sig_children.iter().any(|&c| root_tree.kinds[c] == NodeKind::Generics) {
        diags.push(Diagnostic::new(range.0, range.1, Code::A(8), "`main` must not be generic".to_string()));
    }
    let needs = needs_words(root_tree, root_tokens, root_source);
    let Some(&params_node) = sig_children.iter().find(|&&c| root_tree.kinds[c] == NodeKind::Params) else { return };
    let mut seen_types: Vec<&[&[u8]]> = Vec::new();
    for param in root_tree.children(params_node) {
        let Some(ty) = root_tree.children(param).next() else { continue };
        if root_tree.kinds[ty] != NodeKind::TypeApp {
            diags.push(Diagnostic::new(range.0, range.1, Code::A(8), "`main` parameter type is not one of the eleven root-capability types".to_string()));
            continue;
        }
        let has_targs = root_tree.children(ty).next().is_some();
        let w = words(root_tree, root_tokens, root_source, ty);
        let matched = MAIN_PARAM_TYPES.iter().find(|(t, _)| eq_words(&w, t));
        match matched {
            Some((t, mapped_cap)) if !has_targs => {
                if seen_types.contains(t) {
                    diags.push(Diagnostic::new(range.0, range.1, Code::A(8), "two `main` parameters of the same root-capability type".to_string()));
                }
                seen_types.push(t);
                let cap: &[&[u8]] = if eq_words(&[b"fs".to_vec(), b"Dir".to_vec()], t) {
                    if needs.iter().any(|n| eq_words(n, &[b"fs", b"read"])) || needs.iter().any(|n| eq_words(n, &[b"fs", b"write"])) {
                        continue;
                    }
                    &[b"fs", b"read"]
                } else {
                    mapped_cap
                };
                let has_cap = needs.iter().any(|n| eq_words(n, cap));
                if !has_cap {
                    // Rule 8 sends this case to Rule 1 ("MUST be declared in
                    // the root module's `needs` (Rule 1)"): one cause, one code.
                    diags.push(Diagnostic::new(range.0, range.1, Code::A(1), "the capability of this `main` parameter's type is not declared in the root module's `needs`".to_string()));
                }
            }
            _ => {
                diags.push(Diagnostic::new(range.0, range.1, Code::A(8), "`main` parameter type is not one of the eleven root-capability types".to_string()));
            }
        }
    }
}
