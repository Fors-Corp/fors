//! ch04 (authority) and ch01's brand and `Shared` forms in the checker —
//! increment I10, half B (`docs/design/type-checker.md` §8's ch04 and ch01
//! rows, §13's I10).
//!
//! Codes are the rule number under the chapter's letter (design §14 Q1):
//! `A00nn` for ch04, `O00nn` for ch01. What the resolver already decides
//! from names and the module graph alone — the `needs` vocabulary (A0001)
//! and `main`'s shape (A0008) — stays in `fors_resolve::authority`; this
//! module is the part that needs a type, a callee, a lexical region or a
//! declaration's attributes.
//!
//! - **A0002** (R2a): a sealed operation (inline `asm`, a call to an
//!   `extern` function) inside a generic function or a `comptime` block,
//!   or a call to an `extern` function from a module whose own `needs`
//!   does not declare `ffi`.
//! - **A0007** (R7): a struct literal of one of the twelve root-capability
//!   types — they have no constructor, in any module.
//! - **A0010** (R10): `@unsafe` without exactly one non-empty
//!   `invariant: "..."` argument, written on a block, or the `unsafe { }`
//!   block form ch07 parses as a struct literal.
//! - **A0012** (R12): a `comptime` block that reaches a run-time binding of
//!   its enclosing body (a parameter — a capability value — or a local).
//! - **A0013** (R13): `fs.read_to_string` in a `comptime` block whose path
//!   the module header's `inputs { ... };` clause does not list.
//! - **A0022**, **A0023**, **A0027** (R22, R23, R27): inline assembly only
//!   in an `@unsafe` declaration of a module holding `asm`, a syscall-class
//!   instruction only with `syscall` too, and the CHECK-only typing of an
//!   `asm_expr`.
//! - **O0015** (ch01 R15a): an arena or allocator value constructed by a
//!   struct literal, or moved as a whole.
//! - **O0016** (ch01 R16): an arena subscript with a `Ref` of another
//!   brand.
//! - **O0018** (ch01 R18): `deinit` of an `Own` through an allocator of a
//!   different brand.
//! - **O0021** (ch01 R21, R21a): an `atomic[T]` field of a type that does
//!   not implement `Shared`; an `impl Shared` whose field-wise check fails.
//!
//! What stays open, and why, is in the harness's `PENDING_04` and the
//! summary of the increment: the manifest policy (R2b, R3), the comptime
//! step budget (R14, an EVALUATION fact, FMIR F9's) and lockfile pinning.

use fors_fir::defpath::{HeadKey, NO_DEF};
use fors_fir::impls::ImplRow;
use fors_fir::prelude::{gty, tr};
use fors_fir::sig::{MemberKind, PayloadKind};
use fors_fir::subst::Binding;
use fors_fir::ty::{ArgsId, NO_ARGS, NO_TY, PrimKind, TY_ERROR, TY_UNIT, TyId, TyTag};
use fors_index::decl::DeclKind;
use fors_index::diag::Code;
use fors_index::ids::{DefId, FileId};
use fors_lex::TokenKind;
use fors_resolve::target::{DeferReason, Entity, ResolvedTarget};
use fors_syntax::NodeKind;

use crate::body::BodyCx;
use crate::lower::{FileCtx, Lowered};
use crate::numerics::attr_is;
use crate::wf::{Holds, Wf};

/// ch04 R21's closed root-capability list, as `(std module, type)`.
pub(crate) const ROOT_CAP_TYPES: [(&[u8], &[u8]); 12] = [
    (b"io", b"Stdout"),
    (b"io", b"Stderr"),
    (b"io", b"Stdin"),
    (b"fs", b"Dir"),
    (b"net", b"Net"),
    (b"proc", b"Exec"),
    (b"time", b"Clock"),
    (b"rand", b"Rng"),
    (b"env", b"Env"),
    (b"env", b"Args"),
    (b"gpu", b"Device"),
    (b"mem", b"Heap"),
];

/// ch04 R23's syscall-class instruction mnemonics.
const SYSCALL_CLASS: [&[u8]; 4] = [b"svc", b"syscall", b"sysenter", b"int"];

// ------------------------------------------------------- syntactic reads

/// The identifiers a node owns directly (before its first child), as text.
fn own_words<'s>(f: &FileCtx<'s>, node: usize) -> Vec<&'s [u8]> {
    let (a, b) = fors_resolve::paths::own_span(f.tree, node);
    (a as usize..(b as usize).min(f.tokens.kinds.len()))
        .filter(|&i| matches!(f.tokens.kinds[i], TokenKind::Ident | TokenKind::KwAsm))
        .map(|i| f.tokens.text(i, f.source))
        .collect()
}

/// Every identifier inside a node, in order.
fn all_words<'s>(f: &FileCtx<'s>, node: usize) -> Vec<&'s [u8]> {
    let (a, b) = f.tree.token_range(node);
    (a as usize..(b as usize).min(f.tokens.kinds.len()))
        .filter(|&i| matches!(f.tokens.kinds[i], TokenKind::Ident | TokenKind::KwAsm))
        .map(|i| f.tokens.text(i, f.source))
        .collect()
}

/// The significant tokens of a node.
fn sig_tokens(f: &FileCtx, node: usize) -> Vec<usize> {
    let (a, b) = f.tree.token_range(node);
    (a as usize..(b as usize).min(f.tokens.kinds.len()))
        .filter(|&i| !f.tokens.kinds[i].is_trivia())
        .collect()
}

/// A string literal token's contents, quotes stripped (`None` for a
/// multi-line string, which no rule here reads).
fn str_contents<'s>(f: &FileCtx<'s>, tok: usize) -> Option<&'s [u8]> {
    if f.tokens.kinds[tok] != TokenKind::Str {
        return None;
    }
    let t = f.tokens.text(tok, f.source);
    (t.len() >= 2).then(|| &t[1..t.len() - 1])
}

/// The header clause of kind `k` (`NeedsClause`, `InputsClause`), if any.
fn header_clause(f: &FileCtx, k: NodeKind) -> Option<usize> {
    if f.tree.is_empty() {
        return None;
    }
    f.tree.children(0).find(|&c| f.tree.kinds[c] == k)
}

/// Whether this module's OWN `needs` declares `cap` (ch04 R1: an absent
/// clause is `needs { };`).
pub(crate) fn needs_has(f: &FileCtx, cap: &[&[u8]]) -> bool {
    let Some(clause) = header_clause(f, NodeKind::NeedsClause) else {
        return false;
    };
    f.tree.children(clause).any(|p| {
        let w = all_words(f, p);
        w.len() == cap.len() && w.iter().zip(cap.iter()).all(|(a, b)| a == b)
    })
}

/// The paths the module header's `inputs { ... };` clause lists.
fn inputs_listed<'s>(f: &FileCtx<'s>) -> Vec<&'s [u8]> {
    let Some(clause) = header_clause(f, NodeKind::InputsClause) else {
        return Vec::new();
    };
    sig_tokens(f, clause)
        .into_iter()
        .filter_map(|i| str_contents(f, i))
        .collect()
}

/// The std module this file's own `use std.<m> [as h];` binds the word
/// `head` to (ch08 R4: the alias, else the last segment). Round 5 (D3)
/// made every std module an explicit import, so this is exactly how a
/// root module names one; a user module that merely spells `io` is not
/// reached through `std` and is never answered here.
fn std_module_of_head<'s>(f: &FileCtx<'s>, head: &[u8]) -> Option<&'s [u8]> {
    if f.tree.is_empty() {
        return None;
    }
    for u in f.tree.children(0) {
        if f.tree.kinds[u] != NodeKind::UseDecl {
            continue;
        }
        for item in f.tree.children(u) {
            if f.tree.kinds[item] != NodeKind::UseItem {
                continue;
            }
            let Some(path) = f.tree.children(item).next() else {
                continue;
            };
            let segs = all_words(f, path);
            if segs.len() != 2 || segs[0] != b"std" {
                continue;
            }
            // `as w`: the identifier after the path, inside the item.
            let alias = sig_tokens(f, item)
                .windows(2)
                .find(|w| f.tokens.kinds[w[0]] == TokenKind::KwAs)
                .map(|w| f.tokens.text(w[1], f.source));
            if alias.unwrap_or(segs[1]) == head {
                return Some(segs[1]);
            }
        }
    }
    None
}

/// A two-segment value or type path `m.X` whose head names std module `m`
/// through this file's imports: `Some((m, X))`. A path the resolver bound
/// to a local is never one.
pub(crate) fn std_path<'s>(f: &FileCtx<'s>, node: usize) -> Option<(&'s [u8], &'s [u8])> {
    if f.tree.kinds[node] != NodeKind::NameExpr {
        return None;
    }
    match f.uses.target_of(node as u32) {
        Some(ResolvedTarget::Entity(Entity::Item { .. }))
        | Some(ResolvedTarget::Deferred {
            reason: DeferReason::StdAbsent,
        }) => {}
        _ => return None,
    }
    let w = own_words(f, node);
    if w.len() != 2 {
        return None;
    }
    let m = std_module_of_head(f, w[0])?;
    Some((m, w[1]))
}

/// Whether `node` (a fn declaration) or the `impl`/`trait` it sits in
/// declares generic parameters.
fn generic_decl(f: &FileCtx, node: usize, parent: Option<usize>) -> bool {
    let has = |n: usize| {
        f.tree.children(n).any(|c| {
            f.tree.kinds[c] == NodeKind::Generics
                || (f.tree.kinds[c] == NodeKind::FnSig
                    && f.tree
                        .children(c)
                        .any(|g| f.tree.kinds[g] == NodeKind::Generics))
        })
    };
    has(node) || parent.is_some_and(has)
}

/// Whether the declaration (or the `impl` it sits in) carries `@unsafe`.
fn unsafe_decl(f: &FileCtx, node: usize, parent: Option<usize>) -> bool {
    crate::numerics::decl_has_attr(f, node, b"unsafe")
        || parent.is_some_and(|p| crate::numerics::decl_has_attr(f, p, b"unsafe"))
}

/// ch04 R10's form: `@unsafe(invariant: "...")`, exactly one argument, a
/// non-empty string. `None` when well-formed, else what is wrong.
fn unsafe_form_fault(f: &FileCtx, attr: usize) -> Option<&'static str> {
    let args: Vec<usize> = f
        .tree
        .children(attr)
        .filter(|&c| f.tree.kinds[c] == NodeKind::AttrArg)
        .collect();
    let [arg] = args.as_slice() else {
        return Some(if args.is_empty() {
            "it names no invariant"
        } else {
            "it takes exactly one argument, `invariant:`"
        });
    };
    let toks = sig_tokens(f, *arg);
    let labelled = toks.len() == 3
        && f.tokens.kinds[toks[0]] == TokenKind::Ident
        && f.tokens.text(toks[0], f.source) == b"invariant"
        && f.tokens.kinds[toks[1]] == TokenKind::Colon;
    if !labelled {
        return Some("its one argument must be labelled `invariant:`");
    }
    match str_contents(f, toks[2]) {
        Some(s) if !s.iter().all(u8::is_ascii_whitespace) => None,
        Some(_) => Some("the invariant string is empty"),
        None => Some("the invariant must be a string literal"),
    }
}

impl Wf<'_> {
    fn decl_parent_node(&self, cx: &BodyCx) -> Option<usize> {
        let row = self.defs.get(cx.owner)?;
        let p = self.defs.get(row.parent)?;
        Some(p.node as usize)
    }

    fn in_generic_fn(&self, cx: &BodyCx) -> bool {
        let parent = self.decl_parent_node(cx);
        generic_decl(cx.f, cx.decl_node(), parent)
    }

    fn in_unsafe_decl(&self, cx: &BodyCx) -> bool {
        let parent = self.decl_parent_node(cx);
        unsafe_decl(cx.f, cx.decl_node(), parent)
    }

    fn def_text(&self, def: DefId) -> String {
        self.defs
            .get(def)
            .and_then(|r| r.name)
            .map(|s| String::from_utf8_lossy(self.names.resolve(s)).into_owned())
            .unwrap_or_else(|| "this function".to_string())
    }

    // ------------------------------------------------- body: struct literals

    /// ch04 R7, R10 and ch01 R15a at a struct literal, before its head is
    /// looked up: `true` when the literal was reported (the caller types its
    /// field values and answers `TY_ERROR`).
    pub(crate) fn authority_struct_lit(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        head: usize,
    ) -> bool {
        // ch04 R10: ch07 parses `unsafe { }` as a struct literal of a type
        // named `unsafe`; the rule says there is no block form at all.
        if cx.kind(head) == NodeKind::NameExpr && own_words(cx.f, head) == [b"unsafe".as_slice()] {
            let resolved = matches!(
                cx.f.uses.target_of(head as u32),
                Some(ResolvedTarget::Entity(_)) | Some(ResolvedTarget::Local { .. })
            );
            if !resolved {
                self.bemit_code(
                    cx,
                    node,
                    Code::A(10),
                    34,
                    "there is no `unsafe { }` block: `@unsafe(invariant: \"...\")` is a declaration \
                     attribute only, never a block or statement form (ch04 R10)"
                        .to_string(),
                );
                return true;
            }
        }
        // `Arena[T, A] { }`: the head is the bracketed instantiation.
        let path = if cx.kind(head) == NodeKind::Bracket {
            match cx.kids(head).first() {
                Some(&p) => p,
                None => return false,
            }
        } else {
            head
        };
        if let Some((m, x)) = std_path(cx.f, path)
            && ROOT_CAP_TYPES.iter().any(|&(rm, rx)| rm == m && rx == x)
        {
            let shown = format!(
                "{}.{}",
                String::from_utf8_lossy(m),
                String::from_utf8_lossy(x)
            );
            self.bemit_code(
                cx,
                node,
                Code::A(7),
                34,
                format!(
                    "`{shown}` is a root-capability type and has no constructor: a value of it is \
                     only ever a parameter of `main`, handed down or narrowed from one (ch04 R7)"
                ),
            );
            return true;
        }
        if let Some(ResolvedTarget::Entity(Entity::PreludeType(sym))) =
            cx.f.uses.target_of(path as u32)
        {
            let word = self.names.resolve(sym).to_vec();
            let arena = match self.prelude.lookup(sym) {
                Some(fors_fir::prelude::PreludeEntity::Generic { def, .. }) => {
                    def == self.prelude.generics[gty::ARENA]
                }
                _ => false,
            };
            if arena || word == b"PageAllocator" {
                let w = String::from_utf8_lossy(&word).into_owned();
                self.bemit_code(
                    cx,
                    node,
                    Code::O(15),
                    34,
                    format!(
                        "`{w}` has no constructor: an arena or allocator value exists only as the \
                         binding of a `with` block (ch01 R15a)"
                    ),
                );
                return true;
            }
        }
        false
    }

    // ------------------------------------------------------- body: calls

    /// ch04 R2a and R13 at a call whose callee is classified, plus ch01
    /// R18's `deinit` through a `with` allocator. Reports at most one thing
    /// (the declaration's budget is one diagnostic).
    pub(crate) fn authority_call(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        callee_node: usize,
        callee_fn: Option<DefId>,
        args: &[usize],
    ) {
        let comptime = cx.in_region(NodeKind::ComptimeBlock).is_some();
        if let Some(def) = callee_fn
            && self
                .defs
                .get(def)
                .is_some_and(|r| r.kind == DeclKind::ExternFn)
        {
            let name = self.def_text(def);
            let why = if comptime {
                Some(format!(
                    "comptime evaluation would reach a sealed operation, the call to the extern \
                     function `{name}`; sealing never exempts comptime (ch04 R2a, R12)"
                ))
            } else if self.in_generic_fn(cx) {
                Some(format!(
                    "a sealed operation, the call to the extern function `{name}`, must not appear \
                     in a generic function: its bytes must be emitted in the holder's own object \
                     (ch04 R2a)"
                ))
            } else if !needs_has(cx.f, &[b"ffi"]) {
                Some(format!(
                    "calling the extern function `{name}` is a use of the sealed capability `ffi` \
                     by this module, and its own `needs` does not declare `ffi` (ch04 R2a, R1)"
                ))
            } else {
                None
            };
            if let Some(msg) = why {
                self.bemit_code(cx, node, Code::A(2), 38, msg);
            }
            return;
        }
        if comptime && std_path(cx.f, callee_node) == Some((b"fs", b"read_to_string")) {
            let listed = inputs_listed(cx.f);
            let lit = args.first().and_then(|&a| {
                let v = if cx.kind(a) == NodeKind::NamedArg {
                    cx.kids(a).first().copied()?
                } else {
                    a
                };
                if cx.kind(v) != NodeKind::Literal {
                    return None;
                }
                let toks = sig_tokens(cx.f, v);
                (toks.len() == 1)
                    .then(|| str_contents(cx.f, toks[0]))
                    .flatten()
            });
            let msg = match lit {
                Some(p) if listed.contains(&p) => None,
                Some(p) => Some(format!(
                    "this comptime file read of \"{}\" is not declared: list the path in the \
                     module header's `inputs {{ \"{}\" }};` clause (ch04 R13)",
                    String::from_utf8_lossy(p),
                    String::from_utf8_lossy(p)
                )),
                None => Some(
                    "a comptime file read's path must be a string literal the module header's \
                     `inputs { ... };` clause lists (ch04 R13)"
                        .to_string(),
                ),
            };
            if let Some(msg) = msg {
                self.bemit_code(cx, node, Code::A(13), 38, msg);
            }
            return;
        }
        // ch01 R18: `x.deinit(o)` where `x` is a `with` block's allocator
        // and `o` an `Own` of another brand. Read off the bindings' declared
        // types: nothing is synthesised twice.
        if cx.kind(callee_node) == NodeKind::NameExpr
            && own_words(cx.f, callee_node).last() == Some(&b"deinit".as_slice())
            && let Some(ResolvedTarget::Local { node: intro }) =
                cx.f.uses.target_of(callee_node as u32)
            && cx.kind(intro as usize) == NodeKind::WithStmt
            && let Some(brand) = cx.lcx.fresh_brand(intro)
        {
            for &a in args {
                let Some(t) = self.peek_local_ty(cx, a) else {
                    continue;
                };
                let bare = self.fir.tys.unqual(t);
                if self.fir.tys.tag(bare) != TyTag::Nominal
                    || DefId(self.fir.tys.a(bare)) != self.prelude.generics[gty::OWN]
                {
                    continue;
                }
                let xs = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(bare)));
                if let Some(&b) = xs.get(1)
                    && self.fir.tys.tag(b) == TyTag::Brand
                    && b != brand
                {
                    let shown = self.show(t);
                    self.bemit_code(
                        cx,
                        node,
                        Code::O(18),
                        38,
                        format!(
                            "`deinit` of a value of type `{shown}` through an allocator of a \
                             different brand: an `Own` is released only by the allocator whose \
                             brand it records (ch01 R18)"
                        ),
                    );
                    return;
                }
            }
        }
    }

    /// The declared type of the local an argument names (`x`, `move x`,
    /// `&x`), without typing anything.
    fn peek_local_ty(&self, cx: &BodyCx, arg: usize) -> Option<TyId> {
        let mut n = arg;
        for _ in 0..3 {
            match cx.kind(n) {
                NodeKind::NameExpr => break,
                NodeKind::UnaryExpr | NodeKind::InoutArg | NodeKind::NamedArg => {
                    n = *cx.kids(n).first()?;
                }
                _ => return None,
            }
        }
        if cx.kind(n) != NodeKind::NameExpr {
            return None;
        }
        match cx.f.uses.target_of(n as u32)? {
            ResolvedTarget::Local { node } => cx.local(node).map(|(t, _)| t),
            _ => None,
        }
    }

    /// Whether `s` and `want` have the same shape and differ only in brand
    /// arguments (ch01 R15: a brand equals only itself).
    pub(crate) fn brand_only_mismatch(&self, s: TyId, want: TyId, depth: u32) -> bool {
        fn walk(w: &Wf<'_>, a: TyId, b: TyId, depth: u32, differ: &mut bool) -> bool {
            if a == b {
                return true;
            }
            if depth > 16 {
                return false;
            }
            let (a, b) = (w.fir.tys.unqual(a), w.fir.tys.unqual(b));
            let (ta, tb) = (w.fir.tys.tag(a), w.fir.tys.tag(b));
            if ta != tb {
                return false;
            }
            match ta {
                TyTag::Brand => {
                    *differ = true;
                    true
                }
                TyTag::Nominal | TyTag::Tuple => {
                    if ta == TyTag::Nominal && w.fir.tys.a(a) != w.fir.tys.a(b) {
                        return false;
                    }
                    let xa = w.fir.tys.args_vec(ArgsId(w.fir.tys.b(a)));
                    let xb = w.fir.tys.args_vec(ArgsId(w.fir.tys.b(b)));
                    xa.len() == xb.len()
                        && xa
                            .iter()
                            .zip(xb.iter())
                            .all(|(&x, &y)| walk(w, x, y, depth + 1, differ))
                }
                _ => false,
            }
        }
        let mut differ = false;
        walk(self, s, want, depth, &mut differ) && differ
    }

    // ------------------------------------------------------ body: moves

    /// ch01 R15a: an arena or allocator value is never moved as a whole —
    /// the `with` binding itself, or any value of an `Arena` type.
    pub(crate) fn arena_move(&mut self, cx: &mut BodyCx, node: usize, operand: usize, ty: TyId) {
        let with_binding = cx.kind(operand) == NodeKind::NameExpr
            && matches!(
                cx.f.uses.target_of(operand as u32),
                Some(ResolvedTarget::Local { node: intro }) if cx.kind(intro as usize) == NodeKind::WithStmt
            );
        let bare = self.fir.tys.unqual(ty);
        let arena = self.fir.tys.tag(bare) == TyTag::Nominal
            && DefId(self.fir.tys.a(bare)) == self.prelude.generics[gty::ARENA];
        if with_binding || arena {
            self.bemit_code(
                cx,
                node,
                Code::O(15),
                40,
                "an arena or allocator value is never moved as a whole: it is passed only as \
                 `let` or `inout` (ch01 R15a)"
                    .to_string(),
            );
        }
    }

    // ------------------------------------------------- body: arena index

    /// ch01 R16: `a[r]` on an `Arena[T, A]` takes a `Ref[T, A]` of the SAME
    /// brand and yields the `T` it refers to.
    pub(crate) fn arena_index(
        &mut self,
        cx: &mut BodyCx,
        node: usize,
        args: &[TyId],
        index: Option<usize>,
    ) -> TyId {
        let elem = args.first().copied().unwrap_or(TY_ERROR);
        let brand = args.get(1).copied().unwrap_or(TY_ERROR);
        let Some(i) = index else {
            return elem;
        };
        let s = self.synth(cx, i);
        if s == TY_ERROR || s == NO_TY || elem == TY_ERROR || brand == TY_ERROR {
            return if s == TY_ERROR { TY_ERROR } else { elem };
        }
        let bare = self.fir.tys.unqual(s);
        let rdef = self.prelude.generics[gty::REF];
        if self.fir.tys.tag(bare) == TyTag::Nominal && DefId(self.fir.tys.a(bare)) == rdef {
            let xs = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(bare)));
            if let Some(&b) = xs.get(1)
                && self.fir.tys.tag(b) == TyTag::Brand
                && self.fir.tys.tag(brand) == TyTag::Brand
                && b != brand
            {
                let shown = self.show(s);
                self.bemit_code(
                    cx,
                    node,
                    Code::O(16),
                    29,
                    format!(
                        "a value of type `{shown}` is usable only against an arena of its own \
                         brand, and this arena's brand differs (ch01 R16: brands are compared by \
                         equality, per use)"
                    ),
                );
                return TY_ERROR;
            }
        }
        let want = self.fir.tys.nominal_of(rdef, &[elem, brand]);
        if self.subsume(cx, i, s, want) == TY_ERROR {
            return TY_ERROR;
        }
        elem
    }

    // ------------------------------------------------- body: comptime

    /// ch04 R12: a `comptime` block reaches nothing of the run time — a
    /// parameter (every capability value arrives as one) or a local of the
    /// body around it.
    pub(crate) fn comptime_reach(&mut self, cx: &mut BodyCx, node: usize, intro: u32) {
        let Some(region) = cx.in_region(NodeKind::ComptimeBlock) else {
            return;
        };
        let end = cx.f.tree.subtree_end(region as usize) as u32;
        if intro >= region && intro < end {
            return;
        }
        let what = match cx.kind(intro as usize) {
            NodeKind::Param => "parameter",
            NodeKind::WithStmt => "`with` binding",
            _ => "local",
        };
        let name = own_words(cx.f, node)
            .first()
            .map(|w| String::from_utf8_lossy(w).into_owned())
            .unwrap_or_default();
        self.bemit_code(
            cx,
            node,
            Code::A(12),
            37,
            format!(
                "a `comptime` block cannot reach the run-time {what} `{name}`: comptime is pure and \
                 deterministic, so no capability value, clock, RNG, env read or ambient I/O is \
                 reachable from it (ch04 R12)"
            ),
        );
    }

    // ------------------------------------------------------ body: asm

    /// ch04 R22, R23, R2a and R27 at an `asm_expr`: `want` is the CHECK
    /// mode's expected type, `None` in SYNTH mode.
    pub(crate) fn asm_expr(&mut self, cx: &mut BodyCx, node: usize, want: Option<TyId>) -> TyId {
        let mut outs = 0usize;
        let mut mnemonics: Vec<Vec<u8>> = Vec::new();
        for item in cx.kids(node) {
            if cx.kind(item) != NodeKind::AsmItem {
                continue;
            }
            let toks = sig_tokens(cx.f, item);
            let Some(&first) = toks.first() else {
                continue;
            };
            match cx.f.tokens.kinds[first] {
                TokenKind::Str | TokenKind::MultilineStr => {
                    let text = str_contents(cx.f, first).unwrap_or(b"");
                    let m: Vec<u8> = text
                        .iter()
                        .copied()
                        .skip_while(u8::is_ascii_whitespace)
                        .take_while(|b| !b.is_ascii_whitespace())
                        .map(|b| b.to_ascii_lowercase())
                        .collect();
                    mnemonics.push(m);
                }
                TokenKind::KwIn => {
                    // The operand is an ordinary value: typed, never absorbed.
                    for e in cx.kids(item) {
                        self.synth(cx, e);
                    }
                }
                TokenKind::Ident if cx.f.tokens.text(first, cx.f.source) == b"out" => outs += 1,
                _ => {}
            }
        }
        let fault: Option<(u16, String)> = if !needs_has(cx.f, &[b"asm"]) {
            Some((
                22,
                "inline assembly needs the sealed capability `asm` in this module's own `needs` \
                 (ch04 R22)"
                    .to_string(),
            ))
        } else if !self.in_unsafe_decl(cx) {
            Some((
                22,
                "inline assembly may appear only inside a declaration marked \
                 `@unsafe(invariant: \"...\")` (ch04 R22, R10)"
                    .to_string(),
            ))
        } else if let Some(m) = mnemonics
            .iter()
            .find(|m| SYSCALL_CLASS.contains(&m.as_slice()))
            && !needs_has(cx.f, &[b"syscall"])
        {
            Some((
                23,
                format!(
                    "`{}` is a syscall-class instruction: it needs the sealed capability `syscall` \
                     in this module's own `needs` as well as `asm` (ch04 R23)",
                    String::from_utf8_lossy(m)
                ),
            ))
        } else if cx.in_region(NodeKind::ComptimeBlock).is_some() {
            Some((
                2,
                "comptime evaluation would reach a sealed operation, inline assembly (ch04 R2a, R12)"
                    .to_string(),
            ))
        } else if self.in_generic_fn(cx) {
            Some((
                2,
                "inline assembly is a sealed operation and must not appear in a generic function \
                 (ch04 R2a)"
                    .to_string(),
            ))
        } else {
            None
        };
        if let Some((rule, msg)) = fault {
            self.bemit_code(cx, node, Code::A(rule), 27, msg);
            return TY_ERROR;
        }
        let Some(want) = want else {
            self.bemit_code(
                cx,
                node,
                Code::A(27),
                27,
                "an `asm` expression takes its type only from an expected type: annotate the \
                 binding, or use it as a statement (ch04 R27)"
                    .to_string(),
            );
            return TY_ERROR;
        };
        if want == TY_ERROR || want == NO_TY {
            return TY_ERROR;
        }
        let ok = match outs {
            0 => want == TY_UNIT,
            1 => self.register_ty(want),
            n => {
                let bare = self.fir.tys.unqual(want);
                self.fir.tys.tag(bare) == TyTag::Tuple && {
                    let xs = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(bare)));
                    xs.len() == n && xs.iter().all(|&x| self.register_ty(x))
                }
            }
        };
        if ok {
            return want;
        }
        let shown = self.show(want);
        let shape = match outs {
            0 => "`()`, since it has no `out` item".to_string(),
            1 => "a scalar or pointer type that fits its one `out` register".to_string(),
            n => format!("a tuple of {n} scalar or pointer types, one per `out` item"),
        };
        self.bemit_code(
            cx,
            node,
            Code::A(27),
            27,
            format!("this `asm` expression is expected to be `{shown}`, but its type must be {shape} (ch04 R27)"),
        );
        TY_ERROR
    }

    /// A scalar or pointer type: what fits one register (ch04 R27).
    fn register_ty(&self, t: TyId) -> bool {
        let bare = self.fir.tys.unqual(t);
        self.fir.tys.tag(bare) == TyTag::Prim
            && PrimKind::from_u8(self.fir.tys.a(bare) as u8).is_some_and(|p| {
                p.is_integer() || p.is_float() || matches!(p, PrimKind::Bool | PrimKind::RawPtr)
            })
    }

    /// ch04 R10 at an attribute block statement: `@unsafe` is never a block.
    pub(crate) fn unsafe_block_form(&mut self, cx: &mut BodyCx, node: usize) {
        let attrs: Vec<usize> = cx
            .kids(node)
            .into_iter()
            .filter(|&c| cx.kind(c) == NodeKind::Attribute)
            .collect();
        if attrs.iter().any(|&a| attr_is(cx.f, a, b"unsafe")) {
            self.bemit_code(
                cx,
                node,
                Code::A(10),
                34,
                "`@unsafe(invariant: \"...\")` is a declaration attribute only, never a block or \
                 statement form (ch04 R10)"
                    .to_string(),
            );
        }
    }

    // ------------------------------------------- whole build: declarations

    /// The signature phase's ch04 R10 and ch01 R21/R21a passes.
    pub(crate) fn authority_decls(&mut self, low: &Lowered, files: &[FileCtx]) {
        self.unsafe_attributes(low, files);
        self.atomic_fields(low, files);
        self.shared_impls(low, files);
    }

    fn emit_code(
        &mut self,
        home: DefId,
        file: FileId,
        range: (u32, u32),
        code: Code,
        site: u16,
        msg: String,
    ) {
        self.sink.open();
        self.sink.emit(file, range, code, site, msg);
        self.spoke_at(home);
    }

    /// ch04 R10: every declaration attribute `@unsafe` carries exactly one
    /// non-empty `invariant: "..."`.
    fn unsafe_attributes(&mut self, low: &Lowered, files: &[FileCtx]) {
        for f in files {
            let n = f.tree.len();
            for node in 0..n {
                if f.tree.kinds[node] != NodeKind::Attribute || !attr_is(f, node, b"unsafe") {
                    continue;
                }
                // The parent: the nearest earlier node whose subtree holds it.
                let Some(decl) = (0..node).rev().find(|&p| f.tree.subtree_end(p) > node) else {
                    continue;
                };
                if f.tree.kinds[decl] == NodeKind::AttrBlockStmt {
                    continue; // the body phase reports the block form
                }
                let home = self.defs.def_at(f.file, decl as u32);
                if home == NO_DEF || low.poisoned.get(home.index()).copied().unwrap_or(false) {
                    continue;
                }
                if let Some(why) = unsafe_form_fault(f, node) {
                    let range = fors_resolve::paths::byte_range(f.tree, f.tokens, node);
                    self.emit_code(
                        home,
                        f.file,
                        range,
                        Code::A(10),
                        10,
                        format!(
                            "`@unsafe` must be written `@unsafe(invariant: \"...\")` with a \
                             non-empty invariant, and {why} (ch04 R10)"
                        ),
                    );
                }
            }
        }
    }

    /// The type of every field and payload component of `def`, substituted
    /// with `args` when they are given.
    fn components(&mut self, def: DefId, args: &[TyId]) -> Vec<(fors_index::Symbol, TyId)> {
        let ms = self.fir.sigs.members(def);
        let n = self.fir.sigs.member_store.count(ms);
        let mut out = Vec::new();
        for i in 0..n {
            let m = self.fir.sigs.member_store.get(ms, i);
            match m.kind {
                MemberKind::Field => out.push((m.name, m.ty)),
                MemberKind::Variant => match m.payload {
                    PayloadKind::Tuple => {
                        for t in self.fir.tys.args_vec(m.args) {
                            out.push((m.name, t));
                        }
                    }
                    PayloadKind::Record => {
                        let k = self.fir.sigs.member_store.count(m.sub);
                        for j in 0..k {
                            let s = self.fir.sigs.member_store.get(m.sub, j);
                            out.push((s.name, s.ty));
                        }
                    }
                    PayloadKind::None => {}
                },
                MemberKind::Item => {}
            }
        }
        let arity = self
            .fir
            .sigs
            .generics_store
            .count(self.fir.sigs.generics(def));
        if arity > 0 && args.len() == arity {
            let mut b = Binding::new(&[(def, arity as u16)]);
            for (i, a) in args.iter().enumerate() {
                b.bind(def, i as u16, *a);
            }
            for (_, f) in &mut out {
                if let Some(s) = self.subst_norm_n(*f, &b) {
                    *f = s;
                }
            }
        }
        out
    }

    fn mentions_atomic(&self, t: TyId, depth: u32) -> bool {
        if depth > 16 || t == TY_ERROR || t == NO_TY {
            return false;
        }
        let bare = self.fir.tys.unqual(t);
        match self.fir.tys.tag(bare) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(bare));
                if def == self.prelude.generics[gty::ATOMIC] {
                    return true;
                }
                // Through a tuple or `Array` the component is still a field
                // of THIS type (ch01 R21a's componentwise reading).
                def == self.prelude.generics[gty::ARRAY]
                    && self
                        .fir
                        .tys
                        .args(ArgsId(self.fir.tys.b(bare)))
                        .first()
                        .is_some_and(|&e| self.mentions_atomic(e, depth + 1))
            }
            TyTag::Tuple => self
                .fir
                .tys
                .args(ArgsId(self.fir.tys.b(bare)))
                .iter()
                .any(|&e| self.mentions_atomic(e, depth + 1)),
            _ => false,
        }
    }

    /// Whether `def` implements `Shared` — or MIGHT: an `impl Shared` whose
    /// self type did not lower could be `def`'s, and a definite-only pass
    /// does not guess (the module's own header comment, `wf.rs`).
    fn implements_shared(&self, def: DefId) -> bool {
        let shared = self.prelude.traits[tr::SHARED];
        self.impls.rows().iter().any(|r| {
            r.trait_def == shared && (r.head == HeadKey::Nominal(def) || r.self_ty == TY_ERROR)
        })
    }

    /// ch01 R21: `atomic[T]` only as a field of a type implementing
    /// `Shared`.
    fn atomic_fields(&mut self, low: &Lowered, files: &[FileCtx]) {
        // Definite-only: an `impl` whose head or trait did not lower has no
        // row at all, and it might be some type's `impl Shared`. Then no
        // "does not implement `Shared`" is certain, and the pass is silent
        // (the unresolved name was already reported where it was written).
        let impl_defs: Vec<DefId> = self
            .defs
            .user_defs()
            .filter(|(_, r)| r.kind == DeclKind::Impl)
            .map(|(d, _)| d)
            .collect();
        if impl_defs
            .iter()
            .any(|&d| !self.impls.rows().iter().any(|r| r.def == d))
        {
            return;
        }
        let users: Vec<(DefId, DeclKind)> = self
            .defs
            .user_defs()
            .map(|(d, r)| (d, r.kind))
            .filter(|(_, k)| matches!(k, DeclKind::Struct | DeclKind::Enum))
            .collect();
        for (def, _) in users {
            self.wf_scope = def;
            if low.poisoned.get(def.index()).copied().unwrap_or(false)
                || self.spoke.get(def.index()).copied().unwrap_or(false)
            {
                continue;
            }
            let comps = self.components(def, &[]);
            let Some(&(field, _)) = comps.iter().find(|&&(_, t)| self.mentions_atomic(t, 0)) else {
                continue;
            };
            if self.implements_shared(def) {
                continue;
            }
            let Some((file, range)) = self.decl_head(files, def) else {
                continue;
            };
            let ty = self.def_text(def);
            let fname = String::from_utf8_lossy(self.names.resolve(field)).into_owned();
            self.emit_code(
                def,
                file,
                range,
                Code::O(21),
                21,
                format!(
                    "`{ty}.{fname}` is an `atomic` field, which may appear only in a type that \
                     implements `Shared`; `{ty}` does not (ch01 R21)"
                ),
            );
        }
        self.wf_scope = NO_DEF;
    }

    fn decl_head(&self, files: &[FileCtx], def: DefId) -> Option<(FileId, (u32, u32))> {
        let row = self.defs.get(def)?;
        let f = files.get(row.file.index())?;
        Some((row.file, f.header_range(row.node as usize)))
    }

    /// ch01 R21a: `impl Shared for T {}` is checked field-wise unless the
    /// impl carries `@unsafe(invariant: "...")` (R21c). A blanket impl is
    /// already ch09 R18's and ch08 R21's (T0018, N0021), and the
    /// defining-module requirement is ch08 R21's orphan rule exactly
    /// (`Shared` is a prelude trait, so its impl lives with `T`).
    fn shared_impls(&mut self, low: &Lowered, files: &[FileCtx]) {
        let shared = self.prelude.traits[tr::SHARED];
        let rows: Vec<ImplRow> = self.impls.rows().to_vec();
        for r in rows {
            if r.trait_def != shared || r.self_ty == TY_ERROR || r.inherent {
                continue;
            }
            self.wf_scope = r.def;
            if low.poisoned.get(r.def.index()).copied().unwrap_or(false)
                || self.spoke.get(r.def.index()).copied().unwrap_or(false)
            {
                continue;
            }
            let bare = self.fir.tys.unqual(r.self_ty);
            if self.fir.tys.tag(bare) != TyTag::Nominal {
                continue;
            }
            let Some(row) = self.defs.get(r.def) else {
                continue;
            };
            let Some(f) = files.get(row.file.index()) else {
                continue;
            };
            if crate::numerics::decl_has_attr(f, row.node as usize, b"unsafe") {
                continue; // R21c: the audited escape hatch skips the check
            }
            let head = DefId(self.fir.tys.a(bare));
            let args = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(bare)));
            let comps = self.components(head, &args);
            let mut bad = None;
            for (name, t) in comps {
                if !self.conforms_shared(t, 0) {
                    bad = Some((name, t));
                    break;
                }
            }
            let Some((name, t)) = bad else {
                continue;
            };
            let Some((file, range)) = self.decl_head(files, r.def) else {
                continue;
            };
            let ty = self.def_text(head);
            let shown = self.show(t);
            let fname = String::from_utf8_lossy(self.names.resolve(name)).into_owned();
            self.emit_code(
                r.def,
                file,
                range,
                Code::O(21),
                21,
                format!(
                    "`impl Shared for {ty}` fails the field-wise check at `{fname}: {shown}`, which \
                     is neither `atomic[U]`, `imm`, nor a type that implements `Shared` (ch01 R21a)"
                ),
            );
        }
        self.wf_scope = NO_DEF;
    }

    /// One component under ch01 R21a: `atomic[U]`, `imm`, a type that
    /// implements `Shared` (a parameter through its declared bound), or a
    /// tuple / `Array` whose components all conform.
    fn conforms_shared(&mut self, t: TyId, depth: u32) -> bool {
        if depth > 16 || t == TY_ERROR || t == NO_TY {
            return true; // undecidable here: silence, never a guess
        }
        if self.fir.tys.quals(t).is_imm() {
            return true;
        }
        let bare = self.fir.tys.unqual(t);
        match self.fir.tys.tag(bare) {
            TyTag::Nominal => {
                let def = DefId(self.fir.tys.a(bare));
                if def == self.prelude.generics[gty::ATOMIC] {
                    return true;
                }
                if def == self.prelude.generics[gty::ARRAY] {
                    let e = self
                        .fir
                        .tys
                        .args(ArgsId(self.fir.tys.b(bare)))
                        .first()
                        .copied()
                        .unwrap_or(TY_ERROR);
                    return self.conforms_shared(e, depth + 1);
                }
                let want = self
                    .fir
                    .tys
                    .intern_trait_ref(self.prelude.traits[tr::SHARED], NO_ARGS);
                self.holds(bare, want) != Holds::No
            }
            TyTag::Tuple => {
                let xs = self.fir.tys.args_vec(ArgsId(self.fir.tys.b(bare)));
                xs.into_iter().all(|x| self.conforms_shared(x, depth + 1))
            }
            TyTag::Param | TyTag::Proj => {
                let want = self
                    .fir
                    .tys
                    .intern_trait_ref(self.prelude.traits[tr::SHARED], NO_ARGS);
                self.holds(bare, want) == Holds::Yes
            }
            TyTag::Error | TyTag::Brand | TyTag::ConstVal => true,
            // a scalar, `()`, `never`, `dyn`, `fn`: only if `imm`.
            _ => matches!(self.fir.tys.tag(bare), TyTag::Unit | TyTag::Never),
        }
    }
}
