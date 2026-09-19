//! Local resolution: lexical scopes, no-shadowing and segment-by-segment
//! path resolution inside one file's declarations (ch08 R14, R16, R18-R20,
//! R25, R26). Depends only on this file's tree/tokens plus the already-
//! linked [`crate::items::Universe`], so it runs (and can be cached) per
//! declaration once the whole-build linking step (`items::build_universe`)
//! is done.

use fors_index::{FileId, Interner, ModuleTable, Symbol};
use fors_lex::{TokenKind, Tokens};
use fors_syntax::{NodeKind, Tree};

use crate::diag::{Code, Diagnostic};
use crate::items::{binder_name, Export, Exports, ModuleScope, Prelude};
use crate::paths::{byte_range, own_span, segments_with_ranges};
use crate::target::{Entity, NameUseTable, ResolvedTarget};

pub struct BodyCtx<'a> {
    pub tree: &'a Tree,
    pub tokens: &'a Tokens,
    pub source: &'a [u8],
    pub interner: &'a mut Interner,
    pub modules: &'a ModuleTable,
    /// Other modules, as export tables only: nothing here can observe
    /// another module's bodies, trees or private imports.
    exports: Exports<'a>,
    prelude: &'a Prelude,
    pub file: FileId,
    pub module: &'a ModuleScope,
    pub diags: &'a mut Vec<Diagnostic>,
    pub uses: &'a mut NameUseTable,
    frames: Vec<Vec<(Symbol, u32)>>,
    /// The enclosing `fn_sig`'s own parameter names, for `scoped(p)`
    /// (Rule 20), which is looked up there and nowhere else.
    fn_params: Vec<Symbol>,
    self_sym: Symbol,
}

enum Found<'a> {
    Local(u32),
    Entity(Entity, &'a [Symbol]),
}

impl<'a> BodyCtx<'a> {
    pub fn new(
        tree: &'a Tree,
        tokens: &'a Tokens,
        source: &'a [u8],
        interner: &'a mut Interner,
        modules: &'a ModuleTable,
        exports: Exports<'a>,
        prelude: &'a Prelude,
        file: FileId,
        module: &'a ModuleScope,
        diags: &'a mut Vec<Diagnostic>,
        uses: &'a mut NameUseTable,
    ) -> Self {
        let self_sym = interner.intern(b"Self");
        BodyCtx { tree, tokens, source, interner, modules, exports, prelude, file, module, diags, uses, frames: Vec::new(), fn_params: Vec::new(), self_sym }
    }

    fn push_frame(&mut self) {
        self.frames.push(Vec::new());
    }
    fn pop_frame(&mut self) {
        self.frames.pop();
    }
    pub fn push_frame_pub(&mut self) {
        self.push_frame();
    }
    pub fn pop_frame_pub(&mut self) {
        self.pop_frame();
    }

    pub fn param_symbols(&mut self, params: &[usize]) -> Vec<Symbol> {
        params.iter().filter_map(|&p| binder_name(self.tree, self.tokens, self.source, self.interner, p).map(|(s, _)| s)).collect()
    }

    fn lookup(&self, name: Symbol) -> Option<Found<'a>> {
        for frame in self.frames.iter().rev() {
            if let Some(&(_, node)) = frame.iter().find(|&&(n, _)| n == name) {
                return Some(Found::Local(node));
            }
        }
        let module: &'a ModuleScope = self.module;
        if let Some(row) = module.lookup(name) {
            return Some(Found::Entity(row.entity, row.variants));
        }
        self.prelude.get(module, name).map(|e| Found::Entity(e, &[]))
    }

    /// Ch08 Rule 18: declares `name` (introduced at `node`) in the
    /// innermost open frame, after checking it against every enclosing
    /// scope (locals, params, gparams, `Self`, module scope, prelude) and
    /// against every other binding already declared in that same frame
    /// (pairwise-distinct groups: one `params`, one `generics`, one tuple
    /// `binding`, one closure's `cparam`s, one match arm's pattern). A
    /// function-local binding may share a name with a prelude name (owner
    /// decision 2026-09-19, round 3, D3); every caller of this method
    /// declares exactly that kind of binding, so the exception always
    /// applies here. [`Self::declare_gparam`] is the one caller that must
    /// not get it.
    fn declare(&mut self, name: Symbol, node: usize, range: (u32, u32)) {
        self.declare_coded(name, node, range, 18, true)
    }

    /// Ch08 Rule 18, for a generic parameter: unlike [`Self::declare`],
    /// shadowing a prelude name is still an error (owner decision
    /// 2026-09-19, round 3, D3: "a generic parameter MAY NOT shadow a
    /// prelude name — type-level names stay unambiguous").
    fn declare_gparam(&mut self, name: Symbol, node: usize, range: (u32, u32)) {
        self.declare_coded(name, node, range, 18, false)
    }

    /// Shared implementation of [`Self::declare`]/[`Self::declare_gparam`].
    /// `allow_prelude_shadow` is round 3's D3 carve-out in Rule 18: true
    /// for every function-local binding kind (`let`/`var`, `for`, `param`,
    /// `cparam`, a `"let" ident` pattern binding, a `with arena`/
    /// `allocator` identifier), false for a generic parameter. Every other
    /// shadow case (locals, module-scope items/imports, `Self`) is an
    /// error regardless.
    fn declare_coded(&mut self, name: Symbol, node: usize, range: (u32, u32), rule: u16, allow_prelude_shadow: bool) {
        if name == self.self_sym {
            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(13), "no item, import or binding may be named `Self`".to_string()));
            return;
        }
        if let Some(f) = self.frames.last() {
            if f.iter().any(|&(n, _)| n == name) {
                self.diags.push(Diagnostic::new(range.0, range.1, Code::N(rule), "binding reuses a name already declared in this group".to_string()));
                return;
            }
        }
        // A shadowing binding is reported once and then bound anyway, so
        // that its later uses mean what the author meant instead of each
        // becoming a second error against the shadowed entity.
        if self.frames.iter().rev().skip(1).any(|f| f.iter().any(|&(n, _)| n == name)) {
            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(rule), "binding shadows a binding of an enclosing scope".to_string()));
        } else if self.module.lookup(name).is_some() {
            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(rule), "binding shadows a module-scope name (item or import)".to_string()));
        } else if !allow_prelude_shadow && self.prelude.get(self.module, name).is_some() {
            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(rule), "binding shadows a prelude name".to_string()));
        }
        if self.frames.is_empty() {
            self.frames.push(Vec::new());
        }
        if let Some(f) = self.frames.last_mut() {
            f.push((name, node as u32));
        }
    }

    fn record(&mut self, node: usize, target: ResolvedTarget) {
        self.uses.push(node as u32, target);
    }

    /// Ch08 Rule 16: resolves a dotted path node (`NameExpr`, `TypeApp`,
    /// or a multi-segment/payload `PatPath`) segment by segment, recording
    /// one table entry at `node` for the whole path — the resolved head
    /// once the algorithm stops, or `Deferred` for an unresolved-by-design
    /// tail (member/field/method names, which need a type).
    fn resolve_path(&mut self, node: usize) {
        let segs = segments_with_ranges(self.tree, self.tokens, self.source, self.interner, node);
        if segs.is_empty() {
            return;
        }
        let (name0, range0) = segs[0];
        let Some(found) = self.lookup(name0) else {
            self.diags.push(Diagnostic::new(range0.0, range0.1, Code::N(14), "unresolved name".to_string()));
            self.record(node, ResolvedTarget::Deferred);
            return;
        };
        let (mut head, mut variants) = match found {
            Found::Local(n) => {
                // Further segments of a local are the checker's (Rule 22).
                self.record(node, ResolvedTarget::Local { node: n });
                return;
            }
            Found::Entity(e, v) => (e, v),
        };
        let mut idx = 1usize;
        loop {
            match head {
                Entity::Module(mid) => {
                    let Some(&(sn, sr)) = segs.get(idx) else {
                        let r = byte_range(self.tree, self.tokens, node);
                        self.diags.push(Diagnostic::new(r.0, r.1, Code::N(16), "the path ends on a module; a module is not a value or a type".to_string()));
                        self.record(node, ResolvedTarget::Deferred);
                        return;
                    };
                    match self.exports.get(mid, sn) {
                        Some(Export::Public(row)) => {
                            head = row.entity;
                            variants = row.variants;
                            idx += 1;
                        }
                        other => {
                            let mname = self.modules.name.get(mid.index()).map(|n| fors_index::module::join_dotted(self.interner, n)).unwrap_or_default();
                            let (code, msg) = if other.is_some() {
                                (Code::N(10), format!("this item of module `{mname}` is not `pub`"))
                            } else {
                                (Code::N(16), format!("module `{mname}` has no `pub` module-scope name at this segment"))
                            };
                            self.diags.push(Diagnostic::new(sr.0, sr.1, code, msg));
                            self.record(node, ResolvedTarget::Deferred);
                            return;
                        }
                    }
                }
                Entity::PreludeModule(_, Some(mid)) if idx < segs.len() => head = Entity::Module(mid),
                // `std` is not part of this build: the rest is left to
                // the checker rather than guessed.
                Entity::PreludeModule(_, None) if idx < segs.len() => {
                    self.record(node, ResolvedTarget::Deferred);
                    return;
                }
                Entity::PreludeModule(..) => {
                    let r = byte_range(self.tree, self.tokens, node);
                    self.diags.push(Diagnostic::new(r.0, r.1, Code::N(16), "the path ends on a module; a module is not a value or a type".to_string()));
                    self.record(node, ResolvedTarget::Deferred);
                    return;
                }
                Entity::Poisoned => {
                    self.record(node, ResolvedTarget::Deferred);
                    return;
                }
                Entity::Item { file, decl } => {
                    // Rule 16, enum item: a variant if the next segment
                    // names one; any other tail is deferred (Rule 22).
                    let variant = segs.get(idx).and_then(|&(sn, _)| variants.iter().position(|&v| v == sn));
                    let target = match variant {
                        Some(i) => Entity::Variant { file, decl, index: i as u32 },
                        None => head,
                    };
                    self.record(node, ResolvedTarget::Entity(target));
                    return;
                }
                _ => {
                    self.record(node, ResolvedTarget::Entity(head));
                    return;
                }
            }
        }
    }

    /// Generic recursive walk: resolves every name-use position it knows
    /// about and, for anything else, just recurses into the children —
    /// which is exactly right here, since every non-name token (Rule 23)
    /// is owned directly by its node rather than living in a child.
    pub fn walk(&mut self, node: usize) {
        use NodeKind::*;
        match self.tree.kinds[node] {
            NameExpr | TypeApp => {
                self.resolve_path(node);
                for c in self.tree.children(node) {
                    self.walk(c);
                }
            }
            ScopedType => {
                if let Some((name, range)) = scoped_ident(self.tree, self.tokens, self.source, self.interner, node) {
                    if self.fn_params.contains(&name) {
                        self.record(node, ResolvedTarget::Local { node: node as u32 });
                    } else {
                        self.diags.push(Diagnostic::new(range.0, range.1, Code::N(20), "`scoped(...)` must name a parameter of this function".to_string()));
                    }
                }
                for c in self.tree.children(node) {
                    self.walk(c);
                }
            }
            Contract => {} // ch02's (Rule 26)
            Attribute => {} // not names (Rule 23)
            Block => {
                self.push_frame();
                for c in self.tree.children(node) {
                    self.walk(c);
                }
                self.pop_frame();
            }
            LetStmt => {
                let children: Vec<usize> = self.tree.children(node).collect();
                for &c in children.iter().skip(1) {
                    self.walk(c);
                }
                if let Some(&binding) = children.first().filter(|&&c| matches!(self.tree.kinds[c], Binding | TupleBinding)) {
                    self.declare_binding_tree(binding);
                }
            }
            ForStmt | SimdForStmt | ParallelForStmt => {
                // Rule 26: the binding is in scope in the loop block only,
                // not in the iterable or `grain` expression. A malformed
                // loop (parse error) may lack any of the three parts.
                let children: Vec<usize> = self.tree.children(node).collect();
                let binding = children.first().copied().filter(|&c| matches!(self.tree.kinds[c], Binding | TupleBinding));
                let block = children.last().copied().filter(|&c| self.tree.kinds[c] == Block);
                for &c in &children {
                    if Some(c) != binding && Some(c) != block {
                        self.walk(c);
                    }
                }
                self.push_frame();
                if let Some(b) = binding {
                    self.declare_binding_tree(b);
                }
                if let Some(b) = block {
                    self.walk(b);
                }
                self.pop_frame();
            }
            WithStmt => {
                // Rule 19: the binding is in scope in the header type too.
                let children: Vec<usize> = self.tree.children(node).collect();
                self.push_frame();
                if let Some((name, range)) = with_ident(self.tree, self.tokens, self.source, self.interner, node) {
                    self.declare(name, node, range);
                }
                for c in children {
                    self.walk(c);
                }
                self.pop_frame();
            }
            Closure => {
                let children: Vec<usize> = self.tree.children(node).collect();
                let cparam_count = children.iter().take_while(|&&c| self.tree.kinds[c] == CParam).count();
                let (cparams, body) = children.split_at(cparam_count);
                self.push_frame();
                for &cp in cparams {
                    if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, cp) {
                        self.declare(name, cp, range);
                    }
                }
                for &cp in cparams {
                    for c in self.tree.children(cp) {
                        self.walk(c);
                    }
                }
                for &b in body {
                    self.walk(b);
                }
                self.pop_frame();
            }
            Handler => {
                let children: Vec<usize> = self.tree.children(node).collect();
                self.push_frame();
                if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, node) {
                    self.declare(name, node, range);
                }
                for c in children {
                    self.walk(c);
                }
                self.pop_frame();
            }
            MatchExpr => {
                let children: Vec<usize> = self.tree.children(node).collect();
                if let Some(&scrutinee) = children.first() {
                    self.walk(scrutinee);
                }
                for &arm in children.iter().skip(1) {
                    self.push_frame();
                    let arm_children: Vec<usize> = self.tree.children(arm).collect();
                    if let Some(&pat) = arm_children.first() {
                        self.walk_pattern(pat);
                    }
                    for &c in arm_children.iter().skip(1) {
                        self.walk(c);
                    }
                    self.pop_frame();
                }
            }
            PatWild | PatLit | PatLet | PatPath | PatDot | PatTuple | FPat | Payload => {
                self.walk_pattern(node);
            }
            _ => {
                for c in self.tree.children(node) {
                    self.walk(c);
                }
            }
        }
    }

    fn declare_binding_tree(&mut self, node: usize) {
        if self.tree.kinds[node] == NodeKind::TupleBinding {
            for c in self.tree.children(node) {
                self.declare_binding_tree(c);
            }
            return;
        }
        if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, node) {
            self.declare(name, node, range);
        }
    }

    /// Ch08 Rule 25: patterns. Owner decision 2026-09-19, round 3 (D1):
    /// the only way a pattern binds is `"let" ident` (`PatLet`, or the
    /// `FPat` form with no `pattern` child); a bare one-segment `PatPath`
    /// with no payload is now always a reference.
    fn walk_pattern(&mut self, node: usize) {
        use NodeKind::*;
        match self.tree.kinds[node] {
            PatWild | PatLit => {}
            PatLet => {
                if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, node) {
                    self.declare(name, node, range);
                }
            }
            PatPath => {
                let segs = segments_with_ranges(self.tree, self.tokens, self.source, self.interner, node);
                let has_payload = self.tree.children(node).any(|c| self.tree.kinds[c] == Payload);
                if segs.len() == 1 && !has_payload {
                    let (name, range) = segs[0];
                    match self.lookup(name) {
                        Some(Found::Entity(Entity::Module(_) | Entity::PreludeModule(..), _)) => {
                            // Rule 16 applies to a pattern path like any
                            // other: a path that ends on a module is an
                            // error, not a constant to compare against.
                            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(16), "the path ends on a module; a module is not a value or a type".to_string()));
                            self.record(node, ResolvedTarget::Deferred);
                        }
                        Some(Found::Entity(e, _)) => self.record(node, ResolvedTarget::Entity(e)),
                        Some(Found::Local(_)) => {
                            // Rule 25: a bare pattern name that resolves to
                            // a local binding, parameter or generic
                            // parameter is a compile error directly (a
                            // pattern compares against compile-time
                            // entities only) — not a fresh binding.
                            self.diags.push(Diagnostic::new(
                                range.0,
                                range.1,
                                Code::N(25),
                                "a pattern names a local binding, parameter or generic parameter; write \"let n\" to bind a fresh name instead".to_string(),
                            ));
                            self.record(node, ResolvedTarget::Deferred);
                        }
                        None => {
                            self.diags.push(Diagnostic::new(range.0, range.1, Code::N(14), "unresolved name (to bind, write \"let n\")".to_string()));
                            self.record(node, ResolvedTarget::Deferred);
                        }
                    }
                } else {
                    self.resolve_path(node);
                }
                for c in self.tree.children(node) {
                    self.walk_pattern(c);
                }
            }
            PatDot => {
                self.record(node, ResolvedTarget::Deferred);
                for c in self.tree.children(node) {
                    self.walk_pattern(c);
                }
            }
            PatTuple | Payload => {
                for c in self.tree.children(node) {
                    self.walk_pattern(c);
                }
            }
            FPat => {
                let children: Vec<usize> = self.tree.children(node).collect();
                if let Some(&sub) = children.first() {
                    // `x: pattern` -- `x` is a field name only (Rule 23);
                    // whatever `pattern` binds is its own affair.
                    self.walk_pattern(sub);
                } else if let Some((name, range)) = fpat_let_name(self.tree, self.tokens, self.source, self.interner, node) {
                    // `"let" x` -- shorthand for `x: let x` (D1): binds
                    // `x`, under the same Rule 18 as any other binding.
                    self.declare(name, node, range);
                }
            }
            _ => self.walk(node),
        }
    }

    pub fn resolve_generics(&mut self, generics: usize) -> Vec<usize> {
        let gparams: Vec<usize> = self.tree.children(generics).collect();
        for &g in &gparams {
            if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, g) {
                // Round 3, D3: unlike other bindings, a generic parameter
                // may not shadow a prelude name.
                self.declare_gparam(name, g, range);
            }
        }
        gparams
    }

    pub fn declare_self(&mut self, node: usize) {
        let sym = self.self_sym;
        if let Some(f) = self.frames.last_mut() {
            f.push((sym, node as u32));
        }
    }

    /// Resolves and declares each parameter in order, one at a time: a
    /// parameter's own type annotation is walked (and so resolved)
    /// *before* that parameter is declared, so it cannot see itself in
    /// scope — owner decision 2026-09-19, round 3 (D3): `fn f(let net:
    /// net.Net)` resolves the `net.Net` type against the prelude module
    /// `net`, and only after that is the parameter `net` in scope (for
    /// later parameters' types and the body).
    pub fn resolve_params(&mut self, params_node: usize) -> Vec<usize> {
        let params: Vec<usize> = self.tree.children(params_node).collect();
        for &p in &params {
            for c in self.tree.children(p) {
                self.walk(c);
            }
            if let Some((name, range)) = binder_name(self.tree, self.tokens, self.source, self.interner, p) {
                self.declare(name, p, range);
            }
        }
        params
    }

    pub fn set_fn_params(&mut self, params: Vec<Symbol>) -> Vec<Symbol> {
        std::mem::replace(&mut self.fn_params, params)
    }

    /// The target recorded for `node` at row `mark` of the use table, if
    /// walking `node` recorded its own head there (ch08 R21).
    pub fn target_at(&self, mark: usize, node: usize) -> Option<ResolvedTarget> {
        (self.uses.node.get(mark) == Some(&(node as u32))).then(|| self.uses.target.get(mark).copied()).flatten()
    }

    pub fn push_diag(&mut self, d: Diagnostic) {
        self.diags.push(d);
    }
}

/// `scoped ( ident )`: `scoped` itself lexes as `Ident`, so the target is
/// the *second* `Ident` token in the node's own span.
fn scoped_ident(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner, node: usize) -> Option<(Symbol, (u32, u32))> {
    let (first, end) = own_span(tree, node);
    let mut idents = Vec::new();
    for i in first as usize..end as usize {
        if tokens.kinds[i] == TokenKind::Ident {
            idents.push(i);
        }
    }
    let &tok = idents.get(1)?;
    Some((interner.intern(tokens.text(tok, source)), tokens.range(tok)))
}

/// `with arena|allocator IDENT : T { ... }`: `arena`/`allocator` also lex
/// as `Ident`, so the region name is the identifier right after that word.
fn with_ident(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner, node: usize) -> Option<(Symbol, (u32, u32))> {
    let (first, end) = own_span(tree, node);
    let mut i = first as usize;
    let end = end as usize;
    while i < end {
        if tokens.kinds[i] == TokenKind::Ident && matches!(tokens.text(i, source), b"arena" | b"allocator") {
            let mut j = i + 1;
            while j < end && tokens.kinds[j].is_trivia() {
                j += 1;
            }
            if j < end && tokens.kinds[j] == TokenKind::Ident {
                return Some((interner.intern(tokens.text(j, source)), tokens.range(j)));
            }
            return None;
        }
        i += 1;
    }
    None
}

/// The bound name of an `FPat`'s `"let" ident` form (D1): `binder_name`
/// already skips the leading `let` looking for the first `Ident`/`_`.
fn fpat_let_name(tree: &Tree, tokens: &Tokens, source: &[u8], interner: &mut Interner, node: usize) -> Option<(Symbol, (u32, u32))> {
    binder_name(tree, tokens, source, interner, node)
}

