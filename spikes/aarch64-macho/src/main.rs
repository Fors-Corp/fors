// aarch64 Mach-O backend feasibility spike.
//
// Rung 1: own codegen from the fors-syntax CST to arm64 assembly TEXT,
// assembled/linked by `cc` (which drives the system `as`/`ld`).
// Rung 2: the SAME codegen instead builds a small in-memory instruction
// IR (`ir::Inst`), which is fed to our own encoder (`encode.rs`) and our
// own Mach-O relocatable-object writer (`macho.rs`); `cc`/`ld` still do
// the final link.
// Rung 3: see `exec.rs` — our own MH_EXECUTE writer, no `ld`, no
// `codesign` tool, no external process at all.
//
// See REPORT.md.
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

mod encode;
mod exec;
mod ir;
mod macho;
mod runtime_blob;
mod sha256;

use ir::{Cond, Function, Inst, Item};

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

// ---------- IR front end ----------

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

// ---------- codegen (emits `ir::Item`, shared by both back ends) ----------

struct Codegen<'a> {
    tree: &'a Tree,
    tokens: &'a Tokens,
    source: &'a [u8],
    items: Vec<Item>,
    label_id: u32,
    strings: Vec<(String, Vec<u8>)>,
    syms: std::collections::HashMap<String, i32>, // name -> offset (positive, used as [x29, #-off])
    epilogue: String,
    fname: String,
}

impl<'a> Codegen<'a> {
    fn emit(&mut self, i: Inst) {
        self.items.push(Item::Inst(i));
    }
    fn label(&mut self, l: &str) {
        self.items.push(Item::Label(l.to_string()));
    }
    fn new_label(&mut self, base: &str) -> String {
        self.label_id += 1;
        format!("L{}_{}", base, self.label_id)
    }

    fn load_imm(&mut self, rd: u8, v: i64) {
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
                self.emit(Inst::Movz { rd, imm16: c, hw: i as u8 });
                first = false;
            } else {
                self.emit(Inst::Movk { rd, imm16: c, hw: i as u8 });
            }
        }
        if first {
            self.emit(Inst::Movz { rd, imm16: 0, hw: 0 });
        }
    }

    fn push(&mut self, reg: u8) {
        self.emit(Inst::AddSubImm { sub: true, rd: ir::SP, rn: ir::SP, imm12: 16 });
        self.emit(Inst::StrSp0 { rt: reg });
    }
    fn pop(&mut self, reg: u8) {
        self.emit(Inst::LdrSp0 { rt: reg });
        self.emit(Inst::AddSubImm { sub: false, rd: ir::SP, rn: ir::SP, imm12: 16 });
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
                self.load_imm(0, v);
            }
            NK::NameExpr => {
                let name = leaf_text(self.tree, self.tokens, self.source, n);
                let off = self.slot(&name);
                self.emit(Inst::LdurFp { rt: 0, offset: off as i16 });
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
                    self.emit(Inst::Neg { rd: 0, rm: 0 });
                }
            }
            NK::AddExpr | NK::MulExpr | NK::CmpExpr => {
                let children: Vec<usize> = self.tree.children(n).collect();
                self.expr(children[0]);
                for w in 1..children.len() {
                    let prev_end = self.tree.token_range(children[w - 1]).1;
                    let cur_start = self.tree.token_range(children[w]).0;
                    let op = op_between(self.tokens, prev_end, cur_start);
                    self.push(0);
                    self.expr(children[w]);
                    self.emit(Inst::MovReg { rd: 1, rm: 0 });
                    self.pop(0);
                    match op {
                        TK::Plus => self.emit(Inst::AddSubReg { sub: false, rd: 0, rn: 0, rm: 1 }),
                        TK::Minus => self.emit(Inst::AddSubReg { sub: true, rd: 0, rn: 0, rm: 1 }),
                        TK::Star => self.emit(Inst::Mul { rd: 0, rn: 0, rm: 1 }),
                        TK::Slash => self.emit(Inst::Sdiv { rd: 0, rn: 0, rm: 1 }),
                        TK::Percent => {
                            self.emit(Inst::Sdiv { rd: 2, rn: 0, rm: 1 });
                            self.emit(Inst::Msub { rd: 0, rn: 2, rm: 1, ra: 0 });
                        }
                        TK::Lt => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Lt });
                        }
                        TK::Gt => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Gt });
                        }
                        TK::LtEq => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Le });
                        }
                        TK::GtEq => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Ge });
                        }
                        TK::EqEq => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Eq });
                        }
                        TK::NotEq => {
                            self.emit(Inst::CmpReg { rn: 0, rm: 1 });
                            self.emit(Inst::Cset { rd: 0, cond: Cond::Ne });
                        }
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
                    self.push(0);
                }
                for i in (0..args.len()).rev() {
                    self.pop(i as u8);
                }
                self.emit(Inst::Bl { func: name });
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
                    self.load_imm(0, 0);
                }
                let off = self.slot(&name);
                self.emit(Inst::SturFp { rt: 0, offset: off as i16 });
            }
            NK::AssignStmt => {
                let mut it = self.tree.children(n);
                let place = it.next().unwrap();
                let value = it.next().unwrap();
                let name = leaf_text(self.tree, self.tokens, self.source, place);
                self.expr(value);
                let off = self.slot(&name);
                self.emit(Inst::SturFp { rt: 0, offset: off as i16 });
            }
            NK::WhileStmt => {
                let mut it = self.tree.children(n);
                let cond = it.next().unwrap();
                let body = it.next().unwrap();
                let start = self.new_label("while_start");
                let end = self.new_label("while_end");
                self.label(&start);
                self.expr(cond);
                self.emit(Inst::CmpImm { rn: 0, imm12: 0 });
                self.emit(Inst::Bcond { cond: Cond::Eq, label: end.clone() });
                self.stmt(body);
                self.emit(Inst::B { label: start });
                self.label(&end);
            }
            NK::IfExpr => {
                let children: Vec<usize> = self.tree.children(n).collect();
                let cond = children[0];
                let then_b = children[1];
                let else_b = children.get(2).copied();
                let l_else = self.new_label("if_else");
                let l_end = self.new_label("if_end");
                self.expr(cond);
                self.emit(Inst::CmpImm { rn: 0, imm12: 0 });
                self.emit(Inst::Bcond { cond: Cond::Eq, label: l_else.clone() });
                self.stmt(then_b);
                self.emit(Inst::B { label: l_end.clone() });
                self.label(&l_else);
                if let Some(eb) = else_b {
                    self.stmt(eb);
                }
                self.label(&l_end);
            }
            NK::ReturnStmt => {
                if let Some(e) = self.tree.children(n).next() {
                    self.expr(e);
                }
                self.emit(Inst::B { label: self.epilogue.clone() });
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
                let label = format!("Lstr_{}_{}", self.fname, self.strings.len());
                let len = data.len();
                self.strings.push((label.clone(), data));
                self.emit(Inst::AdrpLabel { rd: 0, label: label.clone() });
                self.emit(Inst::AddPageoff { rd: 0, rn: 0, label });
                self.load_imm(1, len as i64);
                self.emit(Inst::Bl { func: "rt_write_str".to_string() });
                return;
            }
            if name == "out.write_int" {
                self.expr(args[0]);
                self.emit(Inst::Bl { func: "rt_write_int".to_string() });
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

fn round16(n: i32) -> i32 {
    (n + 15) / 16 * 16
}

/// Compiles one function to an `ir::Function` plus its string-literal
/// data. Shared by both back ends: the printer walks `Function::items`
/// to text, the encoder walks the same items to machine code.
fn compile_function(tree: &Tree, tokens: &Tokens, source: &[u8], f: &Func, label_base: u32) -> (Function, Vec<(String, Vec<u8>)>, u32) {
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
        items: Vec::new(),
        label_id: label_base,
        strings: Vec::new(),
        syms,
        epilogue: epilogue.clone(),
        fname: fname.clone(),
    };

    cg.emit(Inst::StpPreSp { rt1: 29, rt2: 30, imm: -16 });
    cg.emit(Inst::MovSp { rd: 29, rn: ir::SP });
    if frame > 0 {
        cg.emit(Inst::AddSubImm { sub: true, rd: ir::SP, rn: ir::SP, imm12: frame as u16 });
    }
    if !f.is_main {
        for (i, p) in f.params.iter().enumerate() {
            let off = cg.slot(p);
            cg.emit(Inst::SturFp { rt: i as u8, offset: off as i16 });
        }
    }
    cg.stmt(f.body);
    if f.is_main {
        cg.load_imm(0, 0);
    }
    cg.label(&epilogue);
    if frame > 0 {
        cg.emit(Inst::MovSp { rd: ir::SP, rn: 29 });
    }
    cg.emit(Inst::LdpPostSp { rt1: 29, rt2: 30, imm: 16 });
    cg.emit(Inst::Ret);

    (Function { name: fname, is_global: f.is_main, items: cg.items }, cg.strings, cg.label_id)
}

struct Program {
    funcs: Vec<Function>,
    data: Vec<(String, Vec<u8>)>,
}

fn compile_ir(source: &[u8]) -> Program {
    let p = fors_syntax::parse_file(source);
    if !p.diags.is_empty() {
        for d in &p.diags {
            eprintln!("parse diagnostic: {:?}", d);
        }
        panic!("source did not parse cleanly");
    }
    let funcs = collect_functions(&p.tree, &p.tokens, source);
    let mut out_funcs = Vec::new();
    let mut out_data = Vec::new();
    let mut label_base = 0u32;
    for f in &funcs {
        let (irf, data, next_base) = compile_function(&p.tree, &p.tokens, source, f, label_base);
        label_base = next_base;
        out_funcs.push(irf);
        out_data.extend(data);
    }
    Program { funcs: out_funcs, data: out_data }
}

// ---------- rung 1 back end: assembly text ----------

fn print_asm(prog: &Program) -> String {
    let mut asm = String::new();
    for f in &prog.funcs {
        ir::print_function(f, &mut asm);
        asm.push('\n');
    }
    if !prog.data.is_empty() {
        asm.push_str(".section __TEXT,__const\n");
        for (label, bytes) in &prog.data {
            asm.push_str(&format!("{label}:\n    .byte "));
            let parts: Vec<String> = bytes.iter().map(|b| b.to_string()).collect();
            asm.push_str(&parts.join(","));
            asm.push('\n');
        }
    }
    asm.push_str(runtime_blob::RUNTIME_ASM_TEXT);
    asm
}

fn compile_rung1(source: &[u8]) -> String {
    print_asm(&compile_ir(source))
}

// ---------- macOS build-version discovery (for LC_BUILD_VERSION) ----------

fn discover_platform_version() -> (u32, u32) {
    // Copy platform/minos/sdk from a cc-produced object, as instructed:
    // avoids hand-guessing the running SDK's encoded version.
    let tmp = std::env::temp_dir().join("spike_probe.o");
    let src = std::env::temp_dir().join("spike_probe.s");
    fs::write(&src, ".text\n.globl _p\n_p:\n ret\n").unwrap();
    let ok = Command::new("cc").args(["-arch", "arm64", "-c", "-o"]).arg(&tmp).arg(&src).status().map(|s| s.success()).unwrap_or(false);
    if ok {
        if let Ok(bytes) = fs::read(&tmp) {
            if let Some(v) = find_build_version(&bytes) {
                return v;
            }
        }
    }
    (0x001a0000, 0) // fallback: 26.0.0, sdk n/a
}

fn find_build_version(data: &[u8]) -> Option<(u32, u32)> {
    let ncmds = u32::from_le_bytes(data[16..20].try_into().ok()?);
    let mut off = 32usize;
    for _ in 0..ncmds {
        let cmd = u32::from_le_bytes(data[off..off + 4].try_into().ok()?);
        let cmdsize = u32::from_le_bytes(data[off + 4..off + 8].try_into().ok()?) as usize;
        if cmd == 0x32 {
            let minos = u32::from_le_bytes(data[off + 12..off + 16].try_into().ok()?);
            let sdk = u32::from_le_bytes(data[off + 16..off + 20].try_into().ok()?);
            return Some((minos, sdk));
        }
        off += cmdsize;
    }
    None
}

// ---------- rung 2 back end: our encoder + our object writer, linked by `cc`/`ld` ----------

fn compile_rung2_object(source: &[u8]) -> Vec<u8> {
    let prog = compile_ir(source);
    let extra = vec![("rt_write_str".to_string(), runtime_blob::RT_WRITE_STR_OFF as u32), ("rt_write_int".to_string(), runtime_blob::RT_WRITE_INT_OFF as u32)];
    let mut enc = encode::encode_program(&prog.funcs, &extra);
    enc.text.extend_from_slice(runtime_blob::RUNTIME_BLOB);
    // rt_write_str/_int are called via `bl`, which we've already resolved
    // as ordinary internal pc-relative branches (encode_program treated
    // them as function symbols at code_len+offset); they still need a
    // symtab entry each, matching the "local function symbols" wording:
    enc.func_syms.push(("rt_write_str".to_string(), (prog_text_len(&prog)) as u32, false));
    enc.func_syms.push(("rt_write_int".to_string(), (prog_text_len(&prog) + runtime_blob::RT_WRITE_INT_OFF) as u32, false));
    let plat = discover_platform_version();
    macho::build_object(&enc, &prog.data, plat)
}

fn prog_text_len(prog: &Program) -> usize {
    prog.funcs.iter().map(|f| f.items.iter().filter(|it| matches!(it, Item::Inst(_))).count()).sum::<usize>() * 4
}

// ---------- differential test: our encoder vs the system assembler ----------

fn otool_text_bytes(obj_path: &str) -> Vec<u8> {
    let out = Command::new("otool").args(["-s", "__TEXT", "__text", obj_path]).output().expect("run otool");
    let text = String::from_utf8_lossy(&out.stdout);
    let mut bytes = Vec::new();
    for line in text.lines().skip(1) {
        let mut cols = line.split_whitespace();
        cols.next(); // address
        for hexword in cols {
            if hexword.len() != 8 || !hexword.chars().all(|c| c.is_ascii_hexdigit()) {
                continue;
            }
            let v = u32::from_str_radix(hexword, 16).unwrap();
            bytes.extend_from_slice(&v.to_le_bytes());
        }
    }
    bytes
}

fn difftest(path: &str) -> bool {
    let source = fs::read(path).expect("read source");
    let prog = compile_ir(&source);
    let asm = print_asm(&prog);
    let tmp_s = std::env::temp_dir().join("spike_difftest.s");
    let tmp_o = std::env::temp_dir().join("spike_difftest.o");
    fs::write(&tmp_s, &asm).unwrap();
    let status = Command::new("cc").args(["-arch", "arm64", "-c", "-o"]).arg(&tmp_o).arg(&tmp_s).status().expect("cc -c");
    assert!(status.success(), "cc -c failed for {path}");
    let want = otool_text_bytes(tmp_o.to_str().unwrap());

    let extra = vec![("rt_write_str".to_string(), runtime_blob::RT_WRITE_STR_OFF as u32), ("rt_write_int".to_string(), runtime_blob::RT_WRITE_INT_OFF as u32)];
    let mut enc = encode::encode_program(&prog.funcs, &extra);
    // The RUNTIME_ASM text is assembled too (it's appended by print_asm),
    // so `want` includes it; append our frozen blob correspondingly.
    enc.text.extend_from_slice(runtime_blob::RUNTIME_BLOB);
    let got = enc.text;

    if got.len() != want.len() {
        println!("{path}: LENGTH MISMATCH ours={} theirs={}", got.len(), want.len());
        return false;
    }
    for (i, (a, b)) in got.iter().zip(want.iter()).enumerate() {
        if a != b {
            let instr_idx = i / 4;
            println!(
                "{path}: MISMATCH at byte {i} (instr #{instr_idx}): ours=0x{:02x} theirs=0x{:02x}",
                a, b
            );
            return false;
        }
    }
    println!("{path}: OK ({} bytes, {} instructions match byte-for-byte)", got.len(), got.len() / 4);
    true
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

    if args.len() >= 3 && args[1] == "difftest" {
        let mut all_ok = true;
        for src_path in &args[2..] {
            all_ok &= difftest(src_path);
        }
        std::process::exit(if all_ok { 0 } else { 1 });
    }

    if args.len() >= 3 && args[1] == "measure" {
        run_measure(&args[2]);
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

    match rung {
        1 => {
            let asm = compile_rung1(&source);
            let asm_path = format!("{out_path}.s");
            fs::write(&asm_path, &asm).expect("write asm");
            let status = Command::new("cc").args(["-arch", "arm64", "-o", out_path, &asm_path]).status().expect("run cc");
            if !status.success() {
                eprintln!("cc failed");
                std::process::exit(1);
            }
        }
        2 => {
            let obj = compile_rung2_object(&source);
            let obj_path = format!("{out_path}.o");
            fs::write(&obj_path, &obj).expect("write object");
            let status = Command::new("cc").args(["-arch", "arm64", "-o", out_path, &obj_path]).status().expect("run cc/ld");
            if !status.success() {
                eprintln!("ld failed");
                std::process::exit(1);
            }
        }
        3 => {
            let prog = compile_ir(&source);
            let extra = vec![("rt_write_str".to_string(), runtime_blob::RT_WRITE_STR_OFF as u32), ("rt_write_int".to_string(), runtime_blob::RT_WRITE_INT_OFF as u32)];
            let mut enc = encode::encode_program(&prog.funcs, &extra);
            enc.text.extend_from_slice(runtime_blob::RUNTIME_BLOB);
            let out_name = std::path::Path::new(out_path).file_name().unwrap().to_str().unwrap().to_string();
            let bin = exec::build_executable(&enc, &prog.data, &out_name);
            exec::write_atomically(out_path, &bin);
        }
        other => {
            eprintln!("rung {other} not implemented");
            std::process::exit(2);
        }
    }
}

fn run_measure(src_path: &str) {
    let source = fs::read(src_path).expect("read source");
    let n = 20;

    // rung 1
    let mut r1: Vec<(f64, f64, f64, u64)> = Vec::new();
    for _ in 0..n {
        let t0 = Instant::now();
        let prog = compile_ir(&source);
        let parse_codegen = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = Instant::now();
        let asm = print_asm(&prog);
        let codegen = t1.elapsed().as_secs_f64() * 1000.0;
        let asm_path = std::env::temp_dir().join("spike_measure.s");
        let out_path = std::env::temp_dir().join("spike_measure_bin");
        fs::write(&asm_path, &asm).unwrap();
        let t2 = Instant::now();
        let status = Command::new("cc").args(["-arch", "arm64", "-o"]).arg(&out_path).arg(&asm_path).status().unwrap();
        assert!(status.success());
        let link = t2.elapsed().as_secs_f64() * 1000.0;
        let size = fs::metadata(&out_path).unwrap().len();
        r1.push((parse_codegen, codegen, link, size));
    }

    // rung 2
    let plat = discover_platform_version(); // shells out to `cc` ONCE, outside the timing loop
    let mut r2: Vec<(f64, f64, f64, u64)> = Vec::new();
    for _ in 0..n {
        let t0 = Instant::now();
        let prog = compile_ir(&source);
        let parse = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = Instant::now();
        let extra = vec![("rt_write_str".to_string(), runtime_blob::RT_WRITE_STR_OFF as u32), ("rt_write_int".to_string(), runtime_blob::RT_WRITE_INT_OFF as u32)];
        let mut enc = encode::encode_program(&prog.funcs, &extra);
        enc.text.extend_from_slice(runtime_blob::RUNTIME_BLOB);
        let obj = macho::build_object(&enc, &prog.data, plat);
        let encode_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let obj_path = std::env::temp_dir().join("spike_measure2.o");
        let out_path = std::env::temp_dir().join("spike_measure2_bin");
        fs::write(&obj_path, &obj).unwrap();
        let t2 = Instant::now();
        let status = Command::new("cc").args(["-arch", "arm64", "-o"]).arg(&out_path).arg(&obj_path).status().unwrap();
        assert!(status.success());
        let link = t2.elapsed().as_secs_f64() * 1000.0;
        let size = fs::metadata(&out_path).unwrap().len();
        r2.push((parse, encode_ms, link, size));
    }

    // rung 3: no external process at all
    let mut r3: Vec<(f64, f64, f64, u64)> = Vec::new();
    for _ in 0..n {
        let t0 = Instant::now();
        let prog = compile_ir(&source);
        let parse = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = Instant::now();
        let extra = vec![("rt_write_str".to_string(), runtime_blob::RT_WRITE_STR_OFF as u32), ("rt_write_int".to_string(), runtime_blob::RT_WRITE_INT_OFF as u32)];
        let mut enc = encode::encode_program(&prog.funcs, &extra);
        enc.text.extend_from_slice(runtime_blob::RUNTIME_BLOB);
        let encode_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let t2 = Instant::now();
        let out_path = std::env::temp_dir().join("spike_measure3_bin");
        let bin = exec::build_executable(&enc, &prog.data, out_path.file_name().unwrap().to_str().unwrap());
        exec::write_atomically(out_path.to_str().unwrap(), &bin);
        let write_sign = t2.elapsed().as_secs_f64() * 1000.0;
        let size = bin.len() as u64;
        r3.push((parse, encode_ms, write_sign, size));
    }

    fn median4(v: &mut Vec<(f64, f64, f64, u64)>, idx: usize) -> f64 {
        let mut xs: Vec<f64> = v.iter().map(|t| match idx { 0 => t.0, 1 => t.1, _ => t.2 }).collect();
        xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        xs[xs.len() / 2]
    }
    let size1 = r1[0].3;
    let size2 = r2[0].3;
    let size3 = r3[0].3;
    println!(
        "{src_path} rung1: parse+codegen={:.3}ms print={:.3}ms assemble+link={:.3}ms total={:.3}ms size={}B",
        median4(&mut r1, 0),
        median4(&mut r1, 1),
        median4(&mut r1, 2),
        median4(&mut r1, 0) + median4(&mut r1, 1) + median4(&mut r1, 2),
        size1
    );
    println!(
        "{src_path} rung2: parse={:.3}ms encode+write.o={:.3}ms link(cc/ld)={:.3}ms total={:.3}ms size={}B",
        median4(&mut r2, 0),
        median4(&mut r2, 1),
        median4(&mut r2, 2),
        median4(&mut r2, 0) + median4(&mut r2, 1) + median4(&mut r2, 2),
        size2
    );
    println!(
        "{src_path} rung3: parse={:.3}ms encode={:.3}ms write+sign={:.3}ms total={:.3}ms size={}B",
        median4(&mut r3, 0),
        median4(&mut r3, 1),
        median4(&mut r3, 2),
        median4(&mut r3, 0) + median4(&mut r3, 1) + median4(&mut r3, 2),
        size3
    );
}
