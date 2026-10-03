//! Renders a [`Program`] to Fors source text and records the byte span of
//! every node under its [`Id`]. Operands are parenthesised by an explicit
//! precedence table (ch07's operator table), so the printed text parses to
//! exactly the tree that was built.

use std::collections::HashMap;
use std::fmt::Write as _;

use crate::ast::*;

pub struct Rendered {
    pub text: String,
    pub spans: HashMap<Id, (u32, u32)>,
}

pub fn render(p: &Program) -> Rendered {
    let mut w = W {
        s: String::new(),
        ind: 0,
        spans: HashMap::new(),
    };
    w.s.push_str("module m;\n");
    for h in &p.header {
        w.s.push_str(h);
        w.s.push('\n');
    }
    for it in &p.items {
        w.s.push('\n');
        w.item(it);
    }
    Rendered {
        text: w.s,
        spans: w.spans,
    }
}

pub fn ty_str(t: &Ty) -> String {
    match t {
        Ty::Prim(p) => p.name().to_string(),
        Ty::Unit => "()".to_string(),
        Ty::Adt(n, args) => {
            if args.is_empty() {
                n.clone()
            } else {
                format!("{n}[{}]", join_tys(args))
            }
        }
        Ty::Option(t) => format!("Option[{}]", ty_str(t)),
        Ty::Tuple(ts) => {
            if ts.len() == 1 {
                format!("({},)", ty_str(&ts[0]))
            } else {
                format!("({})", join_tys(ts))
            }
        }
        Ty::Array(t, n) => format!("Array[{}, {n}]", ty_str(t)),
        Ty::Param(n) => n.clone(),
    }
}

fn join_tys(ts: &[Ty]) -> String {
    ts.iter().map(ty_str).collect::<Vec<_>>().join(", ")
}

/// ch07's binding levels, with the three "needs parentheses anywhere"
/// forms at 0.
fn prec(e: &Expr) -> u8 {
    match &e.kind {
        EK::If(..) | EK::Match(..) => 0,
        EK::Call(c) | EK::Method(_, c) if matches!(c.flow, Flow::Handler { .. }) => 0,
        EK::Binary(op, ..) => match op {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Range => 5,
            BinOp::Add | BinOp::Sub => 6,
            BinOp::Mul | BinOp::Div | BinOp::Rem => 7,
            _ => 4,
        },
        EK::Unary(UnOp::Not, _) => 3,
        EK::Cast(..) => 8,
        EK::Unary(UnOp::Neg, _) | EK::Move(_) => 9,
        _ => 10,
    }
}

/// Whether `e` would, printed bare, put a struct literal where ch07's
/// Disambiguation 1 switches struct literals off (`if` conditions, `for`
/// iterables, `match` scrutinees).
fn has_open_struct(e: &Expr) -> bool {
    match &e.kind {
        EK::StructLit { .. } => true,
        EK::Variant {
            payload: VPayload::Rec(_),
            ..
        } => true,
        EK::If(..) | EK::Match(..) => true,
        EK::Field(r, _) | EK::Index(r, _) | EK::Method(r, _) => has_open_struct(r),
        EK::Binary(_, a, b) => has_open_struct(a) || has_open_struct(b),
        EK::Unary(_, a) | EK::Cast(a, _) | EK::Move(a) => has_open_struct(a),
        _ => false,
    }
}

struct W {
    s: String,
    ind: usize,
    spans: HashMap<Id, (u32, u32)>,
}

impl W {
    fn pos(&self) -> u32 {
        self.s.len() as u32
    }
    fn close(&mut self, id: Id, start: u32) {
        let end = self.pos();
        self.spans.insert(id, (start, end));
    }
    fn nl(&mut self) {
        self.s.push('\n');
        for _ in 0..self.ind {
            self.s.push_str("    ");
        }
    }
    fn line_start(&mut self) {
        for _ in 0..self.ind {
            self.s.push_str("    ");
        }
    }

    // ------------------------------------------------------------- items

    fn item(&mut self, it: &Item) {
        let st = self.pos();
        match it {
            Item::Struct(d) => self.struct_decl(d),
            Item::Enum(d) => self.enum_decl(d),
            Item::Trait(d) => self.trait_decl(d),
            Item::Impl(d) => self.impl_decl(d),
            Item::Fn(d) => self.fn_decl(d),
            Item::Const(d) => {
                let _ = write!(self.s, "const {}: {} = ", d.name, ty_str(&d.ty));
                self.expr(&d.value);
                self.s.push(';');
            }
            Item::Raw { text, .. } => self.s.push_str(text.trim_end_matches('\n')),
        }
        self.s.push('\n');
        // The newline is not part of the declaration.
        let end = self.pos() - 1;
        self.spans.insert(it.id(), (st, end));
    }

    fn generics(&mut self, gs: &[GParam]) {
        if gs.is_empty() {
            return;
        }
        self.s.push('[');
        for (i, g) in gs.iter().enumerate() {
            if i > 0 {
                self.s.push_str(", ");
            }
            let st = self.pos();
            self.s.push_str(&g.name);
            if !g.bounds.is_empty() {
                let _ = write!(self.s, ": {}", g.bounds.join(" + "));
            }
            self.close(g.id, st);
        }
        self.s.push(']');
    }

    fn struct_decl(&mut self, d: &StructDecl) {
        let _ = write!(self.s, "struct {}", d.name);
        self.generics(&d.generics);
        self.s.push_str(" {");
        self.ind += 1;
        for f in &d.fields {
            self.nl();
            let _ = write!(self.s, "{}: {},", f.name, ty_str(&f.ty));
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
    }

    fn enum_decl(&mut self, d: &EnumDecl) {
        let _ = write!(self.s, "enum {}", d.name);
        self.generics(&d.generics);
        self.s.push_str(" {");
        self.ind += 1;
        for v in &d.variants {
            self.nl();
            self.s.push_str(&v.name);
            match &v.shape {
                VShape::Unit => {}
                VShape::Tuple(ts) => {
                    let _ = write!(self.s, "({})", join_tys(ts));
                }
                VShape::Record(fs) => {
                    let body = fs
                        .iter()
                        .map(|f| format!("{}: {}", f.name, ty_str(&f.ty)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let _ = write!(self.s, " {{ {body} }}");
                }
            }
            self.s.push(',');
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
    }

    fn trait_decl(&mut self, d: &TraitDecl) {
        let _ = write!(self.s, "trait {} {{", d.name);
        self.ind += 1;
        for m in &d.methods {
            self.nl();
            self.fn_decl(m);
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
    }

    fn impl_decl(&mut self, d: &ImplDecl) {
        let st = self.pos();
        self.s.push_str("impl");
        self.generics(&d.generics);
        self.s.push(' ');
        match &d.trait_name {
            Some(t) => {
                self.s.push_str(t);
                if !d.trait_args.is_empty() {
                    let _ = write!(self.s, "[{}]", join_tys(&d.trait_args));
                }
                let _ = write!(self.s, " for {}", ty_str(&d.self_ty));
            }
            None => self.s.push_str(&ty_str(&d.self_ty)),
        }
        self.close(d.head_id, st);
        if d.assoc.is_empty() && d.methods.is_empty() {
            self.s.push_str(" { }");
            return;
        }
        self.s.push_str(" {");
        self.ind += 1;
        for (n, t) in &d.assoc {
            self.nl();
            let _ = write!(self.s, "type {n} = {};", ty_str(t));
        }
        for m in &d.methods {
            self.nl();
            self.fn_decl(m);
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
    }

    fn fn_decl(&mut self, d: &FnDecl) {
        let st = self.pos();
        for a in &d.attrs {
            self.s.push_str(a);
            self.nl();
        }
        let sig_st = self.pos();
        self.s.push_str("fn ");
        let ns = self.pos();
        self.s.push_str(&d.name);
        self.close(d.name_id, ns);
        self.generics(&d.generics);
        self.s.push('(');
        for (i, p) in d.params.iter().enumerate() {
            if i > 0 {
                self.s.push_str(", ");
            }
            let ps = self.pos();
            match &p.ty {
                None => {
                    let _ = write!(self.s, "{} {}", p.conv.word(), p.name);
                }
                Some(t) => {
                    let _ = write!(self.s, "{} {}: ", p.conv.word(), p.name);
                    let ts = self.pos();
                    self.s.push_str(&ty_str(t));
                    self.close(p.ty_id, ts);
                }
            }
            self.close(p.id, ps);
        }
        self.s.push(')');
        if d.ret != Ty::Unit {
            self.s.push_str(" -> ");
            let rs = self.pos();
            self.s.push_str(&ty_str(&d.ret));
            self.close(d.ret_id, rs);
        }
        if let Some(r) = &d.raises {
            let _ = write!(self.s, " raises {}", ty_str(r));
        }
        self.close(d.sig_id, sig_st);
        match &d.body {
            None => self.s.push(';'),
            Some(b) => {
                self.s.push(' ');
                self.block(b);
            }
        }
        self.close(d.id, st);
    }

    // ---------------------------------------------------------- statements

    fn block(&mut self, b: &Block) {
        let st = self.pos();
        self.s.push('{');
        self.ind += 1;
        for s in &b.stmts {
            self.nl();
            self.stmt(s);
        }
        if let Some(t) = &b.tail {
            self.nl();
            self.expr(t);
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
        self.close(b.id, st);
    }

    fn stmt(&mut self, s: &Stmt) {
        let st = self.pos();
        match &s.kind {
            SK::Let {
                var,
                name,
                ty,
                ty_id,
                init,
            } => {
                let _ = write!(self.s, "{} {name}", if *var { "var" } else { "let" });
                if let Some(t) = ty {
                    self.s.push_str(": ");
                    let ts = self.pos();
                    self.s.push_str(&ty_str(t));
                    self.close(*ty_id, ts);
                }
                if let Some(e) = init {
                    self.s.push_str(" = ");
                    self.expr(e);
                }
                self.s.push(';');
            }
            SK::Assign(place, op, rhs) => {
                self.expr(place);
                self.s.push_str(match op {
                    AssignOp::Set => " = ",
                    AssignOp::Add => " += ",
                    AssignOp::Sub => " -= ",
                    AssignOp::Mul => " *= ",
                });
                self.expr(rhs);
                self.s.push(';');
            }
            SK::Expr(e) => {
                self.expr(e);
                self.s.push(';');
            }
            SK::If { cond, then, els } => {
                self.s.push_str("if ");
                self.expr_ns(cond);
                self.s.push(' ');
                self.block(then);
                if let Some(e) = els {
                    self.s.push_str(" else ");
                    self.block(e);
                }
            }
            SK::Match { scrut, arms } => {
                self.s.push_str("match ");
                self.expr_ns(scrut);
                self.arms(arms);
            }
            SK::For { var, iter, body } => {
                let _ = write!(self.s, "for {var} in ");
                self.expr_ns(iter);
                self.s.push(' ');
                self.block(body);
            }
            SK::While { cond, body } => {
                self.s.push_str("while ");
                self.expr_ns(cond);
                self.s.push(' ');
                self.block(body);
            }
            SK::Return(e) => {
                self.s.push_str("return");
                if let Some(e) = e {
                    self.s.push(' ');
                    self.expr(e);
                }
                self.s.push(';');
            }
            SK::Raise(e) => {
                self.s.push_str("raise ");
                self.expr(e);
                self.s.push(';');
            }
            SK::Defer { err, body } => {
                self.s.push_str(if *err { "errdefer " } else { "defer " });
                self.block(body);
            }
            SK::Break => self.s.push_str("break;"),
            SK::Continue => self.s.push_str("continue;"),
            SK::Raw(t) => self.s.push_str(t),
        }
        self.close(s.id, st);
    }

    fn arms(&mut self, arms: &[Arm]) {
        self.s.push_str(" {");
        self.ind += 1;
        for a in arms {
            self.nl();
            let st = self.pos();
            self.pat(&a.pat);
            self.s.push_str(" => ");
            match &a.body {
                ArmBody::Expr(e) => {
                    self.expr(e);
                    self.s.push(',');
                }
                ArmBody::Block(b) => self.block(b),
            }
            self.close(a.id, st);
        }
        self.ind -= 1;
        self.nl();
        self.s.push('}');
    }

    fn pat(&mut self, p: &Pat) {
        let st = self.pos();
        match &p.kind {
            PK::Wild => self.s.push('_'),
            PK::Int(n) => {
                let _ = write!(self.s, "{n}");
            }
            PK::Bool(b) => self.s.push_str(if *b { "true" } else { "false" }),
            PK::Bind(n) => {
                let _ = write!(self.s, "let {n}");
            }
            PK::Bare(n) => self.s.push_str(n),
            PK::Variant {
                adt,
                variant,
                dot,
                sub,
            } => {
                if *dot {
                    let _ = write!(self.s, ".{variant}");
                } else {
                    let _ = write!(self.s, "{adt}.{variant}");
                }
                match sub {
                    PSub::Unit => {}
                    PSub::Tuple(ps) => {
                        self.s.push('(');
                        for (i, q) in ps.iter().enumerate() {
                            if i > 0 {
                                self.s.push_str(", ");
                            }
                            self.pat(q);
                        }
                        self.s.push(')');
                    }
                    PSub::Rec(fs) => {
                        self.s.push_str(" { ");
                        for (i, (n, q)) in fs.iter().enumerate() {
                            if i > 0 {
                                self.s.push_str(", ");
                            }
                            let _ = write!(self.s, "{n}: ");
                            self.pat(q);
                        }
                        self.s.push_str(" }");
                    }
                }
            }
            PK::Some(q) => {
                self.s.push_str("some(");
                self.pat(q);
                self.s.push(')');
            }
            PK::None => self.s.push_str("none"),
        }
        self.close(p.id, st);
    }

    // --------------------------------------------------------- expressions

    /// `e` where struct literals are disabled.
    fn expr_ns(&mut self, e: &Expr) {
        if has_open_struct(e) {
            self.paren(e);
        } else {
            self.expr(e);
        }
    }

    /// `(e)`. The parentheses belong to `e`'s span: the checker reports an
    /// operator at the parenthesised node, which starts at the `(`.
    fn paren(&mut self, e: &Expr) {
        let st = self.pos();
        self.s.push('(');
        self.expr(e);
        self.s.push(')');
        self.close(e.id, st);
    }

    /// `e`, parenthesised when its binding level is below `min`.
    fn operand(&mut self, e: &Expr, min: u8) {
        if prec(e) < min {
            self.paren(e);
        } else {
            self.expr(e);
        }
    }

    /// A receiver of `.field`, `[i]` or `.method()`.
    fn receiver(&mut self, e: &Expr) {
        let bad = prec(e) < 10
            || matches!(
                e.kind,
                EK::StructLit { .. }
                    | EK::Variant { .. }
                    | EK::Int(..)
                    | EK::Float(..)
                    | EK::Raw(_)
            );
        if bad {
            self.paren(e);
        } else {
            self.expr(e);
        }
    }

    fn args(&mut self, c: &Call) {
        self.s.push('(');
        for (i, a) in c.args.iter().enumerate() {
            if i > 0 {
                self.s.push_str(", ");
            }
            let st = self.pos();
            if let Some(l) = &a.label {
                let _ = write!(self.s, "{l}: ");
            }
            match a.marker {
                Marker::None => {}
                Marker::Inout => self.s.push('&'),
                Marker::Set => self.s.push_str("&out "),
            }
            self.expr(&a.e);
            self.close(a.id, st);
        }
        self.s.push(')');
    }

    fn call_tail(&mut self, c: &Call) {
        if !c.targs.is_empty() {
            let _ = write!(self.s, "[{}]", join_tys(&c.targs));
        }
        self.args(c);
        match &c.flow {
            Flow::Plain => {}
            Flow::Try => self.s.push('?'),
            Flow::Handler { binder, block } => {
                let _ = write!(self.s, " else |{binder}| ");
                self.block(block);
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        let st = self.pos();
        match &e.kind {
            EK::Int(v, suf) => {
                let _ = write!(self.s, "{v}");
                if let Some(p) = suf {
                    self.s.push_str(p.name());
                }
            }
            EK::Float(t, suf) => {
                self.s.push_str(t);
                if let Some(p) = suf {
                    self.s.push_str(p.name());
                }
            }
            EK::Bool(b) => self.s.push_str(if *b { "true" } else { "false" }),
            EK::UnitLit => self.s.push_str("()"),
            EK::Local(n) | EK::Const(n) => self.s.push_str(n),
            EK::Field(r, f) => {
                self.receiver(r);
                let _ = write!(self.s, ".{f}");
            }
            EK::Index(r, i) => {
                self.receiver(r);
                self.s.push('[');
                self.expr(i);
                self.s.push(']');
            }
            EK::Call(c) => {
                self.s.push_str(&c.callee);
                self.call_tail(c);
            }
            EK::Method(r, c) => {
                self.receiver(r);
                let _ = write!(self.s, ".{}", c.callee);
                self.call_tail(c);
            }
            EK::StructLit {
                name,
                targs,
                fields,
            } => {
                self.s.push_str(name);
                if !targs.is_empty() {
                    let _ = write!(self.s, "[{}]", join_tys(targs));
                }
                self.s.push_str(" { ");
                for (i, (n, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.s.push_str(", ");
                    }
                    let _ = write!(self.s, "{n}: ");
                    self.expr(v);
                }
                self.s.push_str(" }");
            }
            EK::Variant {
                adt,
                variant,
                dot,
                payload,
            } => {
                if *dot {
                    let _ = write!(self.s, ".{variant}");
                } else {
                    let _ = write!(self.s, "{adt}.{variant}");
                }
                match payload {
                    VPayload::Unit => {}
                    VPayload::Tuple(es) => {
                        self.s.push('(');
                        for (i, v) in es.iter().enumerate() {
                            if i > 0 {
                                self.s.push_str(", ");
                            }
                            self.expr(v);
                        }
                        self.s.push(')');
                    }
                    VPayload::Rec(fs) => {
                        self.s.push_str(" { ");
                        for (i, (n, v)) in fs.iter().enumerate() {
                            if i > 0 {
                                self.s.push_str(", ");
                            }
                            let _ = write!(self.s, "{n}: ");
                            self.expr(v);
                        }
                        self.s.push_str(" }");
                    }
                }
            }
            EK::Some(v) => {
                self.s.push_str("some(");
                self.expr(v);
                self.s.push(')');
            }
            EK::None => self.s.push_str("none"),
            EK::Tuple(es) => {
                self.s.push('(');
                for (i, v) in es.iter().enumerate() {
                    if i > 0 {
                        self.s.push_str(", ");
                    }
                    self.expr(v);
                }
                if es.len() == 1 {
                    self.s.push(',');
                }
                self.s.push(')');
            }
            EK::Array(es) => {
                self.s.push('[');
                for (i, v) in es.iter().enumerate() {
                    if i > 0 {
                        self.s.push_str(", ");
                    }
                    self.expr(v);
                }
                self.s.push(']');
            }
            EK::Unary(op, v) => match op {
                UnOp::Neg => {
                    self.s.push('-');
                    self.operand(v, 10);
                }
                UnOp::Not => {
                    self.s.push_str("not ");
                    self.operand(v, 3);
                }
            },
            EK::Binary(op, a, b) => {
                let p = prec(e);
                let min = if op.is_bit() { 8 } else { p + 1 };
                // A comparison's operands are range-level or tighter.
                let min = if op.is_cmp() { 5 } else { min };
                self.operand(a, min);
                let _ = write!(self.s, " {} ", op.text());
                self.operand(b, min);
            }
            EK::Cast(v, t) => {
                self.operand(v, 9);
                let _ = write!(self.s, " as {}", ty_str(t));
            }
            EK::Move(v) => {
                self.s.push_str("move ");
                self.operand(v, 10);
            }
            EK::If(c, t, f) => {
                self.s.push_str("if ");
                self.expr_ns(c);
                self.s.push(' ');
                self.block(t);
                self.s.push_str(" else ");
                self.block(f);
            }
            EK::Match(s, arms) => {
                self.s.push_str("match ");
                self.expr_ns(s);
                self.arms(arms);
            }
            EK::Raw(t) => self.s.push_str(t),
        }
        self.close(e.id, st);
    }

    #[allow(dead_code)]
    fn debug_indent(&mut self) {
        self.line_start();
    }
}
