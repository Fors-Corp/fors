// aarch64 Mach-O backend feasibility spike — Rung 1: own codegen from the
// fors-syntax CST to arm64 assembly TEXT, assembled/linked by `cc`
// (which drives the system `as`/`ld`). See REPORT.md.
//
// Language subset supported: fn decls with i64 params, let/var i64
// locals, assignment, + - * / % (wrapping), comparisons, if/else,
// while, return, calls (incl. recursion), integer literals, and a
// `main(inout out: io.Stdout) raises io.Error { ... }` whose body may
// call exactly `out.write_line(STRING)?;` and `out.write_int(EXPR)?;`,
// implemented by hand-emitted runtime routines that use the write(2)
// syscall directly (no libc I/O). `?` is accepted syntactically and
// otherwise ignored: this spike never fails those two calls.

use std::env;
use std::fs;
use std::process::Command;
use std::time::Instant;

use fors_lex::{TokenKind as TK, Tokens};
use fors_syntax::{NodeKind as NK, Tree};

// ---------- token/text helpers ----------

fn is_sig(k: TK) -> bool {
    !matches!(k, TK::Whitespace | TK::LineComment | TK::BlockComment)
}

/// First significant token kind strictly between the end of `a` and the
/// start of `b` (both raw token indices) — used to recover the operator
/// sitting between two operands of a flat n-ary expression node.
fn op_between(tokens: &Tokens, a_end: u32, b_start: u32) -> TK {
    for t in a_end..b_start {
        if is_sig(tokens.kinds[t as usize]) {
            return tokens.kinds[t as usize];
        }
    }
    TK::Eof
}

/// A node's leaf text with all whitespace stripped (handles the leading
/// trivia/newlines a leaf's raw range carries, and dotted names like
/// `out.write_line`).
fn leaf_text(tree: &Tree, tokens: &Tokens, source: &[u8], i: usize) -> String {
    let (a, b) = tree.token_range(i);
    let bs = tokens.range(a as usize).0;
    let be = if b > a { tokens.range(b as usize - 1).1 } else { bs };
    String::from_utf8_lossy(&source[bs as usize..be as usize])
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect()
}

/// Scans a node's own raw token range (its "gap" tokens: keywords,
/// names, punctuation not owned by a child) for the first Ident,
/// skipping the given node's children's ranges.
fn direct_ident(tree: &Tree, tokens: &Tokens, source: &[u8], node: usize) -> Option<String> {
    let (first, last) = tree.token_range(node);
    let children: Vec<usize> = tree.children(node).collect();
    let mut t = first;
    while t < last {
        let mut skipped = false;
        for &c in &children {
            let (cf, cl) = tree.token_range(c);
            if t >= cf && t < cl {
                t = cl;
                skipped = true;
                break;
            }
        }
        if skipped {
            continue;
        }
        if tokens.kinds[t as usize] == TK::Ident {
            let (bs, be) = tokens.range(t as usize);
            return Some(String::from_utf8_lossy(&source[bs as usize..be as usize]).into_owned());
        }
        t += 1;
    }
    None
}

// ---------- IR ----------

struct Func {
    name: String,
    is_main: bool,
    // parameter names, in order (i64 params only; main's io param is
    // dropped since it never occupies a local slot)
    params: Vec<String>,
    body: usize, // Block node index
}

fn collect_functions(tree: &Tree, tokens: &Tokens, source: &[u8]) -> Vec<Func> {
    let mut out = Vec::new();
    for i in tree.children(0) {
        if tree.kinds[i] != NK::FnDecl {
            continue;
        }
        let sig = tree.children(i).find(|&c| tree.kinds[c] == NK::FnSig).unwrap();
        let name = direct_ident(tree, tokens, source, sig)
            .expect("fn decl must name a function");
        let is_main = name == "main";
        let mut params = Vec::new();
        if let Some(ps) = tree.children(sig).find(|&c| tree.kinds[c] == NK::Params) {
            for p in tree.children(ps) {
                if tree.kinds[p] != NK::Param {
                    continue;
                }
                // Skip non-i64 params (e.g. main's `out: io.Stdout`):
                // any Param whose TypeApp text is not "i64".
                let ty = tree
                    .children(p)
                    .find(|&c| tree.kinds[c] == NK::TypeApp)
                    .map(|c| leaf_text(tree, tokens, source, c));
                if ty.as_deref() != Some("i64") {
                    continue;
                }
                if let Some(pname) = direct_ident(tree, tokens, source, p) {
                    params.push(pname);
                }
            }
        }
        let body = tree.children(i).find(|&c| tree.kinds[c] == NK::Block).unwrap();
        out.push(Func { name, is_main, params, body });
    }
    out
}

/// Recursively collects every local (`let`/`var`) binding name declared
/// anywhere in a function body, in the order codegen will visit them —
/// so codegen can pre-assign stack slots with a first pass.
fn collect_locals(tree: &Tree, tokens: &Tokens, source: &[u8], node: usize, out: &mut Vec<String>) {
    match tree.kinds[node] {
        NK::LetStmt => {
            let b = tree.children(node).next().unwrap();
            out.push(leaf_text(tree, tokens, source, b));
        }
        _ => {}
    }
    for c in tree.children(node) {
        collect_locals(tree, tokens, source, c, out);
    }
}

// ---------- codegen ----------

struct Codegen<'a> {
    tree: &'a Tree,
    tokens: &'a Tokens,
    source: &'a [u8],
    out: String,
    label_id: u32,
    strings: Vec<(String, Vec<u8>)>,
    syms: std::collections::HashMap<String, i32>, // name -> offset (positive, used as [x29, #-off])
    epilogue: String,
}

impl<'a> Codegen<'a> {
    fn new_label(&mut self, base: &str) -> String {
        self.label_id += 1;
        format!("L{}_{}", base, self.label_id)
    }

    fn load_imm(&mut self, reg: &str, v: i64) {
        let u = v as u64;
        let chunks = [
            (u & 0xffff) as u16,
            ((u >> 16) & 0xffff) as u16,
            ((u >> 32) & 0xffff) as u16,
            ((u >> 48) & 0xffff) as u16,
        ];
        let mut first = true;
        for (i, &c) in chunks.iter().enumerate() {
            if c == 0 && !(first && i == 3) {
                continue;
            }
            if first {
                self.out.push_str(&format!("    movz {reg}, #{c}, lsl #{}\n", i * 16));
                first = false;
            } else {
                self.out.push_str(&format!("    movk {reg}, #{c}, lsl #{}\n", i * 16));
            }
        }
        if first {
            // v == 0
            self.out.push_str(&format!("    movz {reg}, #0\n"));
        }
    }

    fn push(&mut self, reg: &str) {
        self.out.push_str(&format!("    sub sp, sp, #16\n    str {reg}, [sp]\n"));
    }
    fn pop(&mut self, reg: &str) {
        self.out.push_str(&format!("    ldr {reg}, [sp]\n    add sp, sp, #16\n"));
    }

    fn slot(&self, name: &str) -> i32 {
        *self.syms.get(name).unwrap_or_else(|| panic!("undefined name `{name}`"))
    }

    // Emits code that leaves the i64 value of node `n` in x0.
    fn expr(&mut self, n: usize) {
        match self.tree.kinds[n] {
            NK::Literal => {
                let t = leaf_text(self.tree, self.tokens, self.source, n);
                let v: i64 = t.parse().expect("integer literal");
                self.load_imm("x0", v);
            }
            NK::NameExpr => {
                let name = leaf_text(self.tree, self.tokens, self.source, n);
                let off = self.slot(&name);
                self.out.push_str(&format!("    ldr x0, [x29, #-{off}]\n"));
            }
            NK::TupleOrParen | NK::TryExpr => {
                let c = self.tree.children(n).next().expect("parenthesized/try expr has an inner expr");
                self.expr(c);
            }
            NK::UnaryExpr => {
                let (first, _) = self.tree.token_range(n);
                let neg = self.tokens.kinds[first as usize] == TK::Minus;
                let c = self.tree.children(n).next().unwrap();
                self.expr(c);
                if neg {
                    self.out.push_str("    neg x0, x0\n");
                }
            }
            NK::AddExpr | NK::MulExpr | NK::CmpExpr => {
                let children: Vec<usize> = self.tree.children(n).collect();
                self.expr(children[0]);
                for w in 1..children.len() {
                    let prev_end = self.tree.token_range(children[w - 1]).1;
                    let cur_start = self.tree.token_range(children[w]).0;
                    let op = op_between(self.tokens, prev_end, cur_start);
                    self.push("x0");
                    self.expr(children[w]);
                    self.out.push_str("    mov x1, x0\n");
                    self.pop("x0");
                    match op {
                        TK::Plus => self.out.push_str("    add x0, x0, x1\n"),
                        TK::Minus => self.out.push_str("    sub x0, x0, x1\n"),
                        TK::Star => self.out.push_str("    mul x0, x0, x1\n"),
                        TK::Slash => self.out.push_str("    sdiv x0, x0, x1\n"),
                        TK::Percent => {
                            self.out.push_str("    sdiv x2, x0, x1\n");
                            self.out.push_str("    msub x0, x2, x1, x0\n");
                        }
                        TK::Lt => self.out.push_str("    cmp x0, x1\n    cset x0, lt\n"),
                        TK::Gt => self.out.push_str("    cmp x0, x1\n    cset x0, gt\n"),
                        TK::LtEq => self.out.push_str("    cmp x0, x1\n    cset x0, le\n"),
                        TK::GtEq => self.out.push_str("    cmp x0, x1\n    cset x0, ge\n"),
                        TK::EqEq => self.out.push_str("    cmp x0, x1\n    cset x0, eq\n"),
                        TK::NotEq => self.out.push_str("    cmp x0, x1\n    cset x0, ne\n"),
                        other => panic!("unsupported binary operator token {other:?}"),
                    }
                }
            }
            NK::CallExpr => {
                let mut it = self.tree.children(n);
                let callee = it.next().unwrap();
                let name = leaf_text(self.tree, self.tokens, self.source, callee);
                let args: Vec<usize> = it.collect();
                for &a in &args {
                    self.expr(a);
                    self.push("x0");
                }
                let regs = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"];
                for i in (0..args.len()).rev() {
                    self.pop(regs[i]);
                }
                self.out.push_str(&format!("    bl _{name}\n"));
            }
            other => panic!("unsupported expression node {other:?}"),
        }
    }

    fn string_literal_bytes(&self, n: usize) -> Vec<u8> {
        let t = leaf_text_raw(self.tree, self.tokens, self.source, n);
        // t is like "\"hello\"" (whitespace-stripping in leaf_text would
        // also eat spaces *inside* the string, so this uses the raw,
        // untouched slice and only trims the surrounding quotes).
        let inner = &t[1..t.len() - 1];
        inner.as_bytes().to_vec()
    }

    // Emits one statement. Handles the two builtin I/O calls specially
    // when it recognizes `out.write_line(...)` / `out.write_int(...)`.
    fn stmt(&mut self, n: usize) {
        match self.tree.kinds[n] {
            NK::Block => {
                for c in self.tree.children(n) {
                    self.stmt(c);
                }
            }
            NK::LetStmt => {
                let mut it = self.tree.children(n);
                let binding = it.next().unwrap();
                let name = leaf_text(self.tree, self.tokens, self.source, binding);
                let init = it.find(|&c| self.tree.kinds[c] != NK::TypeApp);
                if let Some(init) = init {
                    self.expr(init);
                } else {
                    self.out.push_str("    mov x0, #0\n");
                }
                let off = self.slot(&name);
                self.out.push_str(&format!("    str x0, [x29, #-{off}]\n"));
            }
            NK::AssignStmt => {
                let mut it = self.tree.children(n);
                let place = it.next().unwrap();
                let value = it.next().unwrap();
                let name = leaf_text(self.tree, self.tokens, self.source, place);
                self.expr(value);
                let off = self.slot(&name);
                self.out.push_str(&format!("    str x0, [x29, #-{off}]\n"));
            }
            NK::WhileStmt => {
                let mut it = self.tree.children(n);
                let cond = it.next().unwrap();
                let body = it.next().unwrap();
                let start = self.new_label("while_start");
                let end = self.new_label("while_end");
                self.out.push_str(&format!("{start}:\n"));
                self.expr(cond);
                self.out.push_str(&format!("    cmp x0, #0\n    b.eq {end}\n"));
                self.stmt(body);
                self.out.push_str(&format!("    b {start}\n{end}:\n"));
            }
            NK::IfExpr => {
                let children: Vec<usize> = self.tree.children(n).collect();
                let cond = children[0];
                let then_b = children[1];
                let else_b = children.get(2).copied();
                let l_else = self.new_label("if_else");
                let l_end = self.new_label("if_end");
                self.expr(cond);
                self.out.push_str(&format!("    cmp x0, #0\n    b.eq {l_else}\n"));
                self.stmt(then_b);
                self.out.push_str(&format!("    b {l_end}\n{l_else}:\n"));
                if let Some(eb) = else_b {
                    self.stmt(eb);
                }
                self.out.push_str(&format!("{l_end}:\n"));
            }
            NK::ReturnStmt => {
                if let Some(e) = self.tree.children(n).next() {
                    self.expr(e);
                }
                self.out.push_str(&format!("    b {}\n", self.epilogue));
            }
            NK::ExprStmt => {
                let c = self.tree.children(n).next().unwrap();
                self.io_or_expr(c);
            }
            other => panic!("unsupported statement node {other:?}"),
        }
    }

    // Recognizes `out.write_line(STRING)?` / `out.write_int(EXPR)?` at
    // statement position; otherwise falls back to a plain (discarded)
    // expression evaluation.
    fn io_or_expr(&mut self, n: usize) {
        let inner = if self.tree.kinds[n] == NK::TryExpr {
            self.tree.children(n).next().unwrap()
        } else {
            n
        };
        if self.tree.kinds[inner] == NK::CallExpr {
            let mut it = self.tree.children(inner);
            let callee = it.next().unwrap();
            let name = leaf_text(self.tree, self.tokens, self.source, callee);
            let args: Vec<usize> = it.collect();
            if name == "out.write_line" {
                let bytes = self.string_literal_bytes(args[0]);
                let mut data = bytes;
                data.push(b'\n');
                let label = format!("Lstr{}", self.strings.len());
                let len = data.len();
                self.strings.push((label.clone(), data));
                self.out.push_str(&format!(
                    "    adrp x0, {label}@PAGE\n    add x0, x0, {label}@PAGEOFF\n    mov x1, #{len}\n    bl _rt_write_str\n"
                ));
                return;
            }
            if name == "out.write_int" {
                self.expr(args[0]);
                self.out.push_str("    bl _rt_write_int\n");
                return;
            }
        }
        self.expr(inner);
    }
}

fn leaf_text_raw(tree: &Tree, tokens: &Tokens, source: &[u8], i: usize) -> String {
    let (a, b) = tree.token_range(i);
    let bs = tokens.range(a as usize).0;
    let be = if b > a { tokens.range(b as usize - 1).1 } else { bs };
    String::from_utf8_lossy(&source[bs as usize..be as usize])
        .trim()
        .to_string()
}

const RUNTIME_ASM: &str = r#"
.text
// Hand-emitted runtime: the two library operations the subset supports,
// using the write(2) syscall directly (macOS arm64: x16=4, x0=fd,
// x1=buf, x2=len, svc #0x80). No libc I/O is used.
.globl _rt_write_str
_rt_write_str:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    mov x2, x1
    mov x1, x0
    mov x0, #1
    mov x16, #4
    svc #0x80
    ldp x29, x30, [sp], #16
    ret

.globl _rt_write_int
_rt_write_int:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    sub sp, sp, #48
    mov x2, x0
    mov x3, #0
    cmp x2, #0
    b.ge Lwi_pos
    mov x3, #1
    neg x2, x2
Lwi_pos:
    add x4, sp, #38
    mov w7, #10
    strb w7, [sp, #39]
    mov x6, #0
    mov x5, #10
    cmp x2, #0
    b.ne Lwi_loop
    mov w9, #48
    strb w9, [x4]
    sub x4, x4, #1
    add x6, x6, #1
    b Lwi_sign
Lwi_loop:
    cmp x2, #0
    b.eq Lwi_sign
    udiv x8, x2, x5
    msub x9, x8, x5, x2
    add w9, w9, #48
    strb w9, [x4]
    sub x4, x4, #1
    add x6, x6, #1
    mov x2, x8
    b Lwi_loop
Lwi_sign:
    cmp x3, #0
    b.eq Lwi_done
    mov w9, #45
    strb w9, [x4]
    sub x4, x4, #1
    add x6, x6, #1
Lwi_done:
    add x10, x4, #1
    add x6, x6, #1
    mov x0, #1
    mov x1, x10
    mov x2, x6
    mov x16, #4
    svc #0x80
    mov sp, x29
    ldp x29, x30, [sp], #16
    ret
"#;

fn round16(n: i32) -> i32 {
    (n + 15) / 16 * 16
}

fn compile_function(tree: &Tree, tokens: &Tokens, source: &[u8], f: &Func, label_base: u32) -> (String, u32) {
    let mut locals = Vec::new();
    collect_locals(tree, tokens, source, f.body, &mut locals);

    let mut syms = std::collections::HashMap::new();
    let mut slots: Vec<String> = Vec::new();
    if !f.is_main {
        for p in &f.params {
            slots.push(p.clone());
        }
    }
    slots.extend(locals);
    for (idx, name) in slots.iter().enumerate() {
        syms.insert(name.clone(), ((idx as i32) + 1) * 8);
    }
    let frame = round16((slots.len() as i32) * 8);

    let fname = if f.is_main { "main".to_string() } else { f.name.clone() };
    let epilogue = format!("Lepi_{fname}");
    let mut cg = Codegen {
        tree,
        tokens,
        source,
        out: String::new(),
        label_id: label_base,
        strings: Vec::new(),
        syms,
        epilogue: epilogue.clone(),
    };

    cg.out.push_str(&format!(".text\n.globl _{fname}\n_{fname}:\n"));
    cg.out.push_str("    stp x29, x30, [sp, #-16]!\n    mov x29, sp\n");
    if frame > 0 {
        cg.out.push_str(&format!("    sub sp, sp, #{frame}\n"));
    }
    if !f.is_main {
        let regs = ["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"];
        for (i, p) in f.params.iter().enumerate() {
            let off = cg.slot(p);
            cg.out.push_str(&format!("    str {}, [x29, #-{off}]\n", regs[i]));
        }
    }
    cg.stmt(f.body);
    if f.is_main {
        cg.out.push_str("    mov x0, #0\n");
    }
    cg.out.push_str(&format!("{epilogue}:\n"));
    if frame > 0 {
        cg.out.push_str("    mov sp, x29\n");
    }
    cg.out.push_str("    ldp x29, x30, [sp], #16\n    ret\n");

    let mut data = String::new();
    if !cg.strings.is_empty() {
        data.push_str(".section __TEXT,__const\n");
        for (label, bytes) in &cg.strings {
            data.push_str(&format!("{label}:\n    .byte "));
            let parts: Vec<String> = bytes.iter().map(|b| b.to_string()).collect();
            data.push_str(&parts.join(","));
            data.push('\n');
        }
    }
    (format!("{}{}", cg.out, data), cg.label_id)
}

fn compile(source: &[u8]) -> String {
    let p = fors_syntax::parse_file(source);
    if !p.diags.is_empty() {
        for d in &p.diags {
            eprintln!("parse diagnostic: {:?}", d);
        }
        panic!("source did not parse cleanly");
    }
    let funcs = collect_functions(&p.tree, &p.tokens, source);
    let mut asm = String::new();
    asm.push_str(".text\n");
    let mut label_base = 0u32;
    for f in &funcs {
        let (code, next_base) = compile_function(&p.tree, &p.tokens, source, f, label_base);
        label_base = next_base;
        asm.push_str(&code);
        asm.push('\n');
    }
    asm.push_str(RUNTIME_ASM);
    asm
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() >= 3 && args[1] == "dumptree" {
        let src = fs::read(&args[2]).expect("read file");
        let p = fors_syntax::parse_file(&src);
        let mut out = String::new();
        fors_syntax::dump_tree(&p.tree, &p.tokens, &src, &mut out);
        print!("{out}");
        return;
    }

    if args.len() >= 3 && args[1] == "measure" {
        let src_path = &args[2];
        let source = fs::read(src_path).expect("read source");
        let n = 20;
        let mut parse_ms = Vec::new();
        let mut codegen_ms = Vec::new();
        let mut link_ms = Vec::new();
        let mut size = 0u64;
        for _ in 0..n {
            let t0 = Instant::now();
            let p = fors_syntax::parse_file(&source);
            parse_ms.push(t0.elapsed().as_secs_f64() * 1000.0);

            let t1 = Instant::now();
            let funcs = collect_functions(&p.tree, &p.tokens, &source);
            let mut asm = String::new();
            asm.push_str(".text\n");
            let mut label_base = 0u32;
            for f in &funcs {
                let (code, next_base) = compile_function(&p.tree, &p.tokens, &source, f, label_base);
                label_base = next_base;
                asm.push_str(&code);
                asm.push('\n');
            }
            asm.push_str(RUNTIME_ASM);
            codegen_ms.push(t1.elapsed().as_secs_f64() * 1000.0);

            let asm_path = "/tmp/spike_measure.s";
            let out_path = "/tmp/spike_measure_bin";
            fs::write(asm_path, &asm).unwrap();
            let t2 = Instant::now();
            let status = Command::new("cc")
                .args(["-arch", "arm64", "-o", out_path, asm_path])
                .status()
                .unwrap();
            assert!(status.success());
            link_ms.push(t2.elapsed().as_secs_f64() * 1000.0);
            size = fs::metadata(out_path).unwrap().len();
        }
        fn median(v: &mut Vec<f64>) -> f64 {
            v.sort_by(|a, b| a.partial_cmp(b).unwrap());
            v[v.len() / 2]
        }
        println!(
            "{}: parse={:.3}ms codegen={:.3}ms assemble+link={:.3}ms total={:.3}ms size={}B",
            src_path,
            median(&mut parse_ms),
            median(&mut codegen_ms),
            median(&mut link_ms),
            median(&mut parse_ms) + median(&mut codegen_ms) + median(&mut link_ms),
            size
        );
        return;
    }

    // cargo run --release -- <rung> <file.fors> -o <out>
    if args.len() < 5 || args[3] != "-o" {
        eprintln!("usage: spike <rung> <file.fors> -o <out>");
        std::process::exit(2);
    }
    let rung: u32 = args[1].parse().expect("rung must be 1, 2 or 3");
    let src_path = &args[2];
    let out_path = &args[4];
    let source = fs::read(src_path).expect("read source");

    if rung != 1 {
        eprintln!("rung {rung} not implemented in this build; only rung 1 (assembly text + cc) is wired up");
        std::process::exit(2);
    }

    let asm = compile(&source);
    let asm_path = format!("{out_path}.s");
    fs::write(&asm_path, &asm).expect("write asm");

    let status = Command::new("cc")
        .args(["-arch", "arm64", "-o", out_path, &asm_path])
        .status()
        .expect("run cc");
    if !status.success() {
        eprintln!("cc failed");
        std::process::exit(1);
    }
}
