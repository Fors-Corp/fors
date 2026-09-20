//! Adversarial tests for ch07's numbered disambiguation rules, the operator
//! table and the contextual-keyword slots: accept/reject plus the tree
//! shape the rule promises.

mod common;
use common::*;

#[test]
fn operator_table_levels() {
    // 4 over 5, both flat and left to right
    assert_eq!(body_shape("a + b * c - d;"), "ExprStmt(AddExpr(NameExpr MulExpr(NameExpr NameExpr) NameExpr))");
    // 2 over 3 over 4: `-1 as i8` is `(-1) as i8`, `-x.abs()` is `-(x.abs())`
    assert_eq!(body_shape("-1 as i8 * 2;"), "ExprStmt(MulExpr(CastExpr(UnaryExpr(Literal) TypeApp) Literal))");
    assert_eq!(body_shape("-x.abs();"), "ExprStmt(UnaryExpr(CallExpr(NameExpr)))");
    assert_eq!(body_shape("x as A as B;"), "ExprStmt(CastExpr(NameExpr TypeApp TypeApp))");
    assert_eq!(body_shape("x - -1;"), "ExprStmt(AddExpr(NameExpr UnaryExpr(Literal)))");
    assert_eq!(body_shape("move move w.net;"), "ExprStmt(UnaryExpr(UnaryExpr(NameExpr)))");
    // 6 under 5, 7a under 6, single use
    assert_eq!(body_shape("a + 1 ..< b * 2;"), "ExprStmt(RangeExpr(AddExpr(NameExpr Literal) MulExpr(NameExpr Literal)))");
    assert_eq!(body_shape("a ..< b == c ..= d;"), "ExprStmt(CmpExpr(RangeExpr(NameExpr NameExpr) RangeExpr(NameExpr NameExpr)))");
    assert_eq!(body_codes("a ..< b ..< c;"), ["P0010"]);
    assert_eq!(body_codes("a < b < c;"), ["P0006"]);
    assert_eq!(body_codes("a == b != c;"), ["P0006"]);
    // 8 over 9 over 10
    assert_eq!(
        body_shape("not a == b and c or d and not not e;"),
        "ExprStmt(OrExpr(AndExpr(NotExpr(CmpExpr(NameExpr NameExpr)) NameExpr) AndExpr(NameExpr NotExpr(NotExpr(NameExpr)))))"
    );
    rejects("a == not b;");
    assert_eq!(body_codes("a == not b;").len(), 1);
    rejects("a + not b;");
    // no node where no operator fires
    assert_eq!(body_shape("1;"), "ExprStmt(Literal)");
}

#[test]
fn rule12_bitwise_tier() {
    assert_eq!(body_shape("a & b & c;"), "ExprStmt(BitExpr(NameExpr NameExpr NameExpr))");
    assert_eq!(body_shape("a << 2;"), "ExprStmt(BitExpr(NameExpr Literal))");
    // operands are level 3: prefix and `as` bind inside, `not/and/or` outside
    assert_eq!(body_shape("-a as u8 | b as u8;"), "ExprStmt(BitExpr(CastExpr(UnaryExpr(NameExpr) TypeApp) CastExpr(NameExpr TypeApp)))");
    assert_eq!(body_shape("not a & b and c | d;"), "ExprStmt(AndExpr(NotExpr(BitExpr(NameExpr NameExpr)) BitExpr(NameExpr NameExpr)))");
    assert_eq!(body_shape("(a & m) != 0;"), "ExprStmt(CmpExpr(TupleOrParen(BitExpr(NameExpr NameExpr)) Literal))");
    for bad in [
        "a + b & c;", "a & b + c;", "a * b & c;", "a & b * c;", "a & b | c;", "a | b & c;", "a ^ b | c;", "a & b == c;",
        "a == b & c;", "a << b << c;", "a << b >> c;", "a >> b & c;", "a & b << c;", "a ..< b & c;", "a & b ..< c;",
        "a < b | c;", "x = a + b & c;",
    ] {
        assert_eq!(body_codes(bad), ["P0005"], "{bad}");
    }
    accepts("let x = (a + b) & c; let y = a | b | c; let z = a ^ b ^ c;");
}

#[test]
fn rule1_struct_literal_vs_block() {
    assert_eq!(body_shape("if p { }"), "IfExpr(NameExpr Block)");
    assert_eq!(body_codes("if P { x: 0 } { }").len(), 1);
    assert_eq!(body_codes("while P { x: 0 } { }").len(), 1);
    assert_eq!(body_codes("for i in P { x: 0 } { }").len(), 1);
    assert_eq!(body_codes("match P { x: 0 } { }").len(), 1);
    // the flag is cleared inside ( ) [ ] { } nested in the head and restored after
    accepts("if (P { x: 0 }).ok { }");
    accepts("if f(P { x: 0 }) == p { }");
    accepts("if xs[P { x: 0 }.x] { }");
    accepts("while f(|a| P { x: a }) { }");
    accepts("for i in g(Q[T] { lo: 0 }) { }");
    accepts("parallel for i in xs grain P.n { }");
    rejects("parallel for i in xs grain P { n: 1 } { }");
    assert_eq!(body_shape("if a { } else if b { } else { }"), "IfExpr(NameExpr Block NameExpr Block Block)");
    // contracts are heads too
    assert!(codes("fn f(let i: usize) pre i < s.len post r == P.x { }").is_empty());
    assert!(codes("struct S invariant lo <= hi { lo: u8, hi: u8 }").is_empty());
    assert!(!codes("fn f() pre P { x: 1 } { }").is_empty());
    // normal mode: `path {` and `path [args] {` only
    assert_eq!(body_shape("P { x: 1 };"), "ExprStmt(StructLit(NameExpr FInit(Literal)))");
    assert_eq!(body_shape("m.P[T] { x: 1, };"), "ExprStmt(StructLit(Bracket(NameExpr NameExpr) FInit(Literal)))");
    rejects("P[T][U] { x: 1 };");
    rejects("f() { x: 1 };");
    rejects("a?.b { x: 1 };");
}

#[test]
fn rule2_rule3_pipe_and_else() {
    assert_eq!(body_shape("f(|x| x + 1);"), "ExprStmt(CallExpr(NameExpr Closure(CParam AddExpr(NameExpr Literal))))");
    // closure body is greedy
    assert_eq!(body_shape("let g = |a| a | b;"), "LetStmt(Binding Closure(CParam BitExpr(NameExpr NameExpr)))");
    assert_eq!(body_shape("let g = || { };"), "LetStmt(Binding Closure(Block))");
    assert_eq!(body_shape("reduce(|, xs);"), "ExprStmt(CallExpr(NameExpr BareOp NameExpr))");
    assert_eq!(body_shape("f(|y| y, |);"), "ExprStmt(CallExpr(NameExpr Closure(CParam NameExpr) BareOp))");
    assert_eq!(
        body_shape("g() else |e| { raise e; };"),
        "ExprStmt(CallExpr(NameExpr Handler(Block(RaiseStmt(NameExpr)))))"
    );
    accepts("let v = a.b(1) else |e| { 0 }.c;");
    rejects("g()? else |e| { };");
    rejects("g[1] else |e| { };");
    rejects("{ } else |e| { }");
    rejects("if a { } else |e| { }");
}

#[test]
fn rule4_rule6_rule7_argument_markers() {
    assert_eq!(
        body_shape("f(&x, &out y, &out, &out.len, &out[i], a: &b.c, n: 1);"),
        "ExprStmt(CallExpr(NameExpr InoutArg(NameExpr) SetArg(NameExpr) InoutArg(NameExpr) InoutArg(NameExpr) \
         InoutArg(Bracket(NameExpr NameExpr)) NamedArg(InoutArg(NameExpr)) NamedArg(Literal)))"
    );
    assert_eq!(body_shape("f(&out out);"), "ExprStmt(CallExpr(NameExpr SetArg(NameExpr)))");
    assert_eq!(body_shape("reduce(&, xs); reduce(-, xs); f(-x);").matches("BareOp").count(), 2);
    assert_eq!(body_shape("reduce(+, xs, identity: 0.0);"), "ExprStmt(CallExpr(NameExpr BareOp NameExpr NamedArg(Literal)))");
    accepts("f(and, or, ==, <=, <<, %, op: *);");
    assert_eq!(body_codes("let y = &x;").len(), 1);
    assert_eq!(body_codes("let y = a + &x;").len(), 1);
    rejects("f(&x + 1);");
    rejects("f(&(x));");
    rejects("f(&x());");
    rejects("f(not);");
    rejects("f(+ x);");
    // a label is `ident :` only
    rejects("f(a.b: 1);");
    rejects("let z = (a: 1);");
}

#[test]
fn rule5_bracket_roles() {
    assert_eq!(body_shape("xs[i] = [1, 2, 3][0];"), "AssignStmt(Bracket(NameExpr NameExpr) Bracket(ArrayLit(Literal Literal Literal) Literal))");
    assert_eq!(body_shape("let a = [0; n];"), "LetStmt(Binding ArrayLit(Literal NameExpr))");
    // a statement-form `if` ends at `}`: the `[` starts a new statement
    assert_eq!(body_shape("if a { } [1, 2].len;"), "IfExpr(NameExpr Block) ExprStmt(FieldExpr(ArrayLit(Literal Literal)))");
    assert_eq!(file_shape("impl[T] A[T] for B { }"), "ImplDecl(Generics(GParam) TypeApp(TypeApp) TypeApp)");
    assert_eq!(codes("fn f() { @a[x] { } }").len(), 1);
    assert!(!codes("fn g[]() { }").is_empty());
    assert!(!codes("fn g() { let v: Vec[] = x; }").is_empty());
}

#[test]
fn rule8_rule9_statement_start() {
    assert_eq!(body_shape("x - 1"), "AddExpr(NameExpr Literal)");
    assert_eq!(body_shape("a.b[i].c += 1;"), "AssignStmt(FieldExpr(Bracket(NameExpr NameExpr)) Literal)");
    for bad in ["f() = 1;", "(a) = 1;", "a? = 1;", "a.b() = 2;", "-a = 1;", "a + b = 1;", "P { } = 1;"] {
        assert_eq!(body_codes(bad), ["P0004"], "{bad}");
    }
    rejects("a = b = c;");
    // statement-form if/match/comptime are not continued by an operator
    rejects("if a { } + 1;");
    rejects("match a { } ?;");
    assert_eq!(body_shape("if a { } - 1;"), "IfExpr(NameExpr Block) ExprStmt(UnaryExpr(Literal))");
    assert_eq!(body_shape("comptime { } (a);"), "ComptimeBlock(Block) ExprStmt(TupleOrParen(NameExpr))");
    // ... and are the tail value when last
    assert_eq!(body_shape("f(); match a { _ => 1 }"), "ExprStmt(CallExpr(NameExpr)) MatchExpr(NameExpr Arm(PatWild Literal))");
    accepts("return if a { 1 } else { 2 }; ");
    accepts("return match a { _ => 1 };");
    accepts("let t = (); let u = (a,); let v = (a, b,);");
}

#[test]
fn rule10_contextual_keywords_only_in_their_slot() {
    accepts(
        "let arena = 1; let brand = 2; let out = 3; let set = 4; let scoped = 5; let needs = 6; let pre = 7; \
         let grain = 8; let contracts = 9; let soa = 10; let allocator = 11; let post = 12; let invariant = 13; \
         out[i] = set + grain; arena.alloc(pre, post); scoped(a); soa.x = needs;",
    );
    rejects("let secret = 1;");
    rejects("let in = 1;");
    rejects("let import = 1;");
    rejects("let recover = 1;");
    // `set` closure parameter: convention iff followed by a name (LA 2)
    assert_eq!(body_shape("let f = |set, set x, set: T, set _| 0;").matches("CParam").count(), 4);
    assert!(codes("fn f(set: T) { }").len() == 1, "in a param the first token is always the convention");
    assert!(codes("fn f(set set: T, inout arena: A, let out: B) { }").is_empty());
    // `scoped` only before `(` in a return type
    assert!(codes("fn f() -> scoped { }").is_empty());
    assert_eq!(file_shape("fn f() -> (scoped(a) iso T, scoped) { }"), "FnDecl(FnSig(Params TupleType(ScopedType(QualType(TypeApp)) TypeApp)) Block)");
    assert!(!codes("fn f(let x: scoped(a) T) { }").is_empty());
    // `brand` only right after the gparam colon; `soa` only before `struct`
    assert!(codes("struct S[B: brand, T: brands.Tr + U] { }").is_empty());
    assert!(!codes("struct S[T: brand.Tr] { }").is_empty(), "a trait named brand cannot be a bound");
    assert!(!codes("soa enum E { A }").is_empty());
    assert_eq!(file_shape("@x pub soa struct S { a: u8 }"), "StructDecl(Attribute Field(TypeApp))");
    // header words are identifiers once declarations started
    assert!(!codes("fn f() { } needs { io };").is_empty());
    assert!(codes("module a.b; contracts: .strict; needs { io, net.tcp, }; pub use x, y; use z;").is_empty());
    assert!(!codes("needs { io }; contracts: .strict;").is_empty());
    assert!(codes("fn f() { with arena arena: Arena { } with allocator allocator: A { } }").is_empty());
    assert_eq!(codes("fn f() { with region r: R { } }").len(), 1);
}

#[test]
fn rule11_generic_arguments() {
    assert_eq!(
        body_shape("let v: Array[T, N + 1] = x;"),
        "LetStmt(Binding TypeApp(TypeApp AddExpr(NameExpr Literal)) NameExpr)"
    );
    assert_eq!(body_shape("let v: A[T, N * 2 - 1, -1, 8, true, m.K];").matches("TypeApp").count(), 3);
    assert_eq!(body_shape("let v: A[N * 2 - 1];"), "LetStmt(Binding TypeApp(AddExpr(MulExpr(NameExpr Literal) Literal)))");
    assert_eq!(body_shape("let v: A[fn() -> T, (A, B), dyn C, iso D];").matches("TypeApp").count(), 6);
    for bad in ["let v: Array[T, (N + 1)];", "let v: A[N[1] + 1];", "let v: A[N as u8];", "let v: A[N == 1];"] {
        assert!(!body_codes(bad).is_empty(), "{bad}");
    }
    assert_eq!(body_shape("f[iso Buf, x]();"), "ExprStmt(CallExpr(Bracket(NameExpr QualType(TypeApp) NameExpr)))");
    accepts("x.wrap_as[u8](); f[Vec[T]](); f[(i32, u8)](); f[fn(let T) -> U](); f[dyn X]();");
}

#[test]
fn rule13_rule14_rule15_paths_fn_types_pub() {
    assert_eq!(body_shape("a.b.c().d;"), "ExprStmt(FieldExpr(CallExpr(NameExpr)))");
    assert_eq!(body_shape("let v = .some(1);"), "LetStmt(Binding CallExpr(DotLit Literal))");
    rejects("let v = a . . b;");
    rejects("let v = .5;");
    assert_eq!(body_codes("let v = .5;").len(), 1);
    assert_eq!(
        body_shape("let f: fn() -> fn(let A) -> T raises E;"),
        "LetStmt(Binding FnType(FnType(FParam(TypeApp) TypeApp Raises(TypeApp))))"
    );
    assert_eq!(
        file_shape("pub use a.b, c; pub fn f() { }"),
        "UseDecl(UseItem(Path) UseItem(Path)) FnDecl(FnSig(Params) Block)"
    );
    assert_eq!(file_shape("use a.b as c;"), "UseDecl(UseItem(Path))");
    rejects("use a.b as;");
    assert!(!codes("fn f() { } use a;").is_empty());
}

#[test]
fn minimum_list_lengths_and_patterns() {
    for bad in ["enum E { }", "enum E { A() }", "enum E { A { } }", "struct S[] { }"] {
        assert!(!codes(bad).is_empty(), "{bad}");
    }
    rejects("match x { .a() => 1 }");
    rejects("match x { a { } => 1 }");
    rejects("match x { a => 1 b => 2 }");
    assert_eq!(
        body_shape(
            "match x { .a => 1, m.B(y, _) => { } .c { let f, g: -1 } => 2, (a, \"s\") => 3 }"
        ),
        "MatchExpr(NameExpr Arm(PatDot Literal) Arm(PatPath(Payload(PatPath PatWild)) Block) \
         Arm(PatDot(Payload(FPat FPat(PatLit))) Literal) Arm(PatTuple(PatPath PatLit) Literal))"
    );
    // round 3, D1: the bare fpat shorthand is removed, "let" is the only
    // way a pattern binds, and "var" is not a pattern alternative.
    assert_eq!(body_shape("match x { let n => n }"), "MatchExpr(NameExpr Arm(PatLet NameExpr))");
    rejects("match x { P { f } => f }");
    rejects("match x { var n => n }");
}

#[test]
fn declarations_own_their_attributes_and_pub() {
    let src = "// doc\n@inline @cfg(x: 1)\npub fn f() { }\n\n/* c */ @a pub extern \"c\" fn g();\nconst X: u8 = 1;\n";
    let p = parse_checked(src.as_bytes());
    assert!(p.diags.is_empty());
    let decls: Vec<usize> = p.tree.children(0).collect();
    assert_eq!(decls.len(), 3);
    // contiguous, gap-free, in order: decl k ends exactly where decl k+1 starts
    let mut next = 0;
    for &d in &decls {
        let (a, b) = p.tree.token_range(d);
        assert_eq!(a, next);
        next = b;
    }
    assert_eq!(shape_of(&p.tree, decls[0]), "FnDecl(Attribute Attribute(AttrArg(Literal)) FnSig(Params) Block)");
    assert_eq!(shape_of(&p.tree, decls[1]), "ExternFnDecl(Attribute FnSig(Params))");
    assert_eq!(file_shape("impl A { @x pub fn f() { } }"), "ImplDecl(TypeApp FnDecl(Attribute FnSig(Params) Block))");
}

#[test]
fn recovery_is_one_diagnostic() {
    assert_eq!(body_codes("let a = 1 let b = 2;"), ["P0002"]);
    assert_eq!(body_codes("f() g();"), ["P0001"]);
    assert_eq!(body_codes("let a = 1 2 3; let b = 2;"), ["P0001"]);
    assert_eq!(body_codes("f(a b, c); g();"), ["P0001"]);
    assert_eq!(body_codes("let a = ;"), ["P0001"]);
    assert_eq!(body_codes("let a = 1.5q;"), ["P0008"]);
    assert_eq!(body_codes("let a = $ 1;"), ["P0008"]);
    assert_eq!(codes("fn f() { let a = (1 + 2; }\nfn g() { }"), ["P0001"]);
    // a missing closer at a declaration or EOF names the opener, once
    for (src, open) in [
        ("fn f() { g(1, \nstruct S { }", "("),
        ("fn f() { if a { b(); \nfn g() { }", "{"),
        ("fn f() { let v = [1, 2\n", "["),
        ("trait T { fn a();\nimpl T for U { }", "{"),
        ("fn f() { match x { a => 1,\nconst X: u8 = 1;", "{"),
    ] {
        let p = parse_checked(src.as_bytes());
        assert_eq!(p.diags.len(), 1, "{src:?}: {:?}", p.diags);
        assert_eq!(p.diags[0].code.as_str(), "P0003");
        assert_eq!(&src[p.diags[0].start as usize..p.diags[0].end as usize], open, "{src:?}");
    }
}

#[test]
fn missing_brace_never_damages_the_next_declaration() {
    let src = "fn f() {\n    let a = g(1,\n\n@inline(always)\npub fn h() { }\nstruct S { x: u8 }\n";
    let p = parse_checked(src.as_bytes());
    assert_eq!(p.diags.len(), 1, "{:?}", p.diags);
    let kinds: Vec<_> = p.tree.children(0).map(|c| shape_of(&p.tree, c)).collect();
    assert_eq!(kinds[1], "FnDecl(Attribute(AttrArg(Path)) FnSig(Params) Block)");
    assert_eq!(kinds[2], "StructDecl(Field(TypeApp))");
    // inside an impl, `fn` resumes in the impl's item list; other items close it
    let src = "impl A {\n fn a() { let x = 1;\n fn b() { }\n}\nenum E { V }";
    let p = parse_checked(src.as_bytes());
    assert_eq!(p.diags.len(), 1, "{:?}", p.diags);
    let top: Vec<_> = p.tree.children(0).map(|c| p.tree.kinds[c]).collect();
    assert_eq!(top, [fors_syntax::NodeKind::ImplDecl, fors_syntax::NodeKind::EnumDecl]);
    assert_eq!(p.tree.children(p.tree.children(0).next().unwrap()).filter(|&c| p.tree.kinds[c] == fors_syntax::NodeKind::FnDecl).count(), 2);
}

// ---- round 4 (owner decisions 2026-09-19): associated types, constraint
// entries, `type` reserved (ch07 Disambiguation 19-20, Error recovery) ----

#[test]
fn assoc_type_items() {
    assert_eq!(
        file_shape("trait It { type Item; fn next(inout self: Self) -> Option[Self.Item]; }"),
        "TraitDecl(AssocTypeDecl TraitItem(FnSig(Params(Param(TypeApp)) TypeApp(TypeApp))))"
    );
    assert_eq!(file_shape("trait K { type Key: Eq + Ord; }"), "TraitDecl(AssocTypeDecl(TypeApp TypeApp))");
    assert_eq!(
        file_shape("impl[I: It] It for Skip[I] { type Item = I.Item; fn next(inout self: Skip[I]) -> Option[I.Item] { return none; } }"),
        "ImplDecl(Generics(GParam(TypeApp)) TypeApp TypeApp(TypeApp) AssocTypeDef(TypeApp) FnDecl(FnSig(Params(Param(TypeApp(TypeApp))) TypeApp(TypeApp)) Block(ReturnStmt(NameExpr))))"
    );
    // the two forms are not interchangeable, and take no attribute/pub/generics
    for bad in [
        "trait T { type A = i32; }",
        "impl T for S { type A; }",
        "impl T for S { type A: B; }",
        "impl T for S { pub type A = i32; }",
        "trait T { @x type A; }",
        "trait T { type A[U]; }",
        "trait T { type A + B; }",
    ] {
        assert_eq!(codes(bad).len(), 1, "{bad:?}: {:?}", codes(bad));
    }
}

#[test]
fn generics_constraint_entry() {
    assert_eq!(
        file_shape("fn f[I: It, I.Item: Add + Copyable,]() { }"),
        "FnDecl(FnSig(Generics(GParam(TypeApp) GConstraint(TypeApp TypeApp)) Params) Block)"
    );
    assert_eq!(file_shape("fn g[Self.Item: Eq]() { }"), "FnDecl(FnSig(Generics(GConstraint(TypeApp)) Params) Block)");
    assert_eq!(file_shape("struct S[I: It, I.Item: Eq] { }"), "StructDecl(Generics(GParam(TypeApp) GConstraint(TypeApp)))");
    // `brand` is contextual in the gparam slot only: here it is a type path
    assert_eq!(file_shape("fn f[I.Item: brand + Eq]() { }"), "FnDecl(FnSig(Generics(GConstraint(TypeApp TypeApp)) Params) Block)");
    assert_eq!(codes("fn f[I.Item]() { }"), ["P0001"]);
    assert_eq!(codes("fn f[I.Item.X: Eq]() { }"), ["P0001"]);
    // equality bounds: the fixed message, one diagnostic, recovery at `,`/`]`
    for bad in ["fn f[I: It, I.Item = i64]() { }", "fn f[T = i64, U]() { }", "fn f[I.Item = i64, J: It]() { }"] {
        assert_eq!(codes(bad), ["P0009"], "{bad:?}");
        let p = parse_checked(bad.as_bytes());
        assert!(p.diags[0].message.contains("equality bounds do not exist"), "{bad:?}: {}", p.diags[0].message);
    }
}

#[test]
fn type_reserved_word() {
    rejects("let type = 1;");
    rejects("x.type;");
    rejects("f(type: 1);");
    assert_eq!(codes("struct S { type: i32 }").len(), 1);
    // file level: fixed message, exactly one diagnostic, next declaration intact
    let src = "type A = i32;\nfn f() -> i32 { return 0; }\n";
    let p = parse_checked(src.as_bytes());
    assert_eq!(p.diags.len(), 1, "{:?}", p.diags);
    assert!(p.diags[0].message.contains("type aliases do not exist"));
    let kinds: Vec<_> = p.tree.children(0).map(|c| shape_of(&p.tree, c)).collect();
    assert_eq!(kinds.last().map(String::as_str), Some("FnDecl(FnSig(Params TypeApp) Block(ReturnStmt(Literal)))"));
}

#[test]
fn recover_assoc_type_item() {
    for src in ["impl T for S { type A = ; fn f() { } }", "impl T for S { type A i32; fn f() { } }", "trait T { type ; fn f(); }"] {
        let p = parse_checked(src.as_bytes());
        assert_eq!(p.diags.len(), 1, "{src:?}: {:?}", p.diags);
        let top = p.tree.children(0).next().unwrap();
        let members: Vec<_> = p.tree.children(top).map(|c| p.tree.kinds[c]).collect();
        assert!(
            members.contains(&fors_syntax::NodeKind::FnDecl) || members.contains(&fors_syntax::NodeKind::TraitItem),
            "{src:?}: {members:?}"
        );
    }
}

#[test]
fn round6_defer_errdefer_statements() {
    // ch07 `defer_stmt`/`errdefer_stmt` (Disambiguation 9): the keyword
    // selects the statement and the next token alone selects the body.
    assert_eq!(body_shape("defer f();"), "DeferStmt(CallExpr(NameExpr))");
    assert_eq!(body_shape("errdefer f();"), "ErrdeferStmt(CallExpr(NameExpr))");
    assert_eq!(body_shape("defer { f(); }"), "DeferStmt(Block(ExprStmt(CallExpr(NameExpr))))");
    // `defer P { x: 1 };` is the expr form holding a struct literal, not a block.
    assert!(body_shape("defer P { x: 1 };").starts_with("DeferStmt(StructLit"));
    // an assignment is a stmt, not an expr: parse error at `=`, one diagnostic
    rejects("defer x = 1;");
    assert_eq!(body_codes("defer x = 1;").len(), 1);
    rejects("errdefer x = 1;");
    // both words are reserved
    rejects("let defer = 1;");
    rejects("let errdefer = 1;");
    // missing `;` recovers on the statement sync set: one diagnostic, both statements kept
    assert_eq!(body_codes("defer f() defer g();").len(), 1);
}
