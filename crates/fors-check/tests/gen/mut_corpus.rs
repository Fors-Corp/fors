//! Mutations by injection of a known-bad declaration. The subject of most
//! of ch01-ch04's rules (a linear type, a trait impl that overlaps another, a
//! `contracts: .proved` module, an `asm` block) is not something the
//! generator's own programs contain, so each such rule is exercised by
//! dropping one minimal rejected program from the conformance corpus into a
//! generated one. The corpus is the oracle for these: a template is used only
//! if, standing alone, it is rejected with exactly the one code its
//! `rule:` / `detail:` names. The names it declares are renamed to be unique,
//! so the template cannot clash with the generated declarations around it.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use crate::ast::*;
use crate::mutate::*;
use crate::rng::Rng;
use crate::run;

/// One conformance test turned into an injectable template.
#[derive(Clone, Debug)]
pub struct Template {
    /// `09-types/duplicate-method-across-impls-rejected.fors`.
    pub file: String,
    pub chapter: u8,
    pub rule: u16,
    pub code: String,
    /// Module-level directives (`needs { };`, `contracts: .proved;`).
    pub header: Vec<String>,
    pub text: String,
    /// The top-level names the template declares.
    pub declared: Vec<String>,
}

#[derive(Default, Debug)]
pub struct Harvest {
    pub usable: Vec<Template>,
    /// `(file, why)` for every check-error test that is not injectable.
    pub unusable: Vec<(String, String)>,
}

const DIRS: [(&str, u8, char); 5] = [
    ("01-ownership", 1, 'O'),
    ("02-failure", 2, 'F'),
    ("03-numerics", 3, 'D'),
    ("04-authority", 4, 'A'),
    ("09-types", 9, 'T'),
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn is_ident_start(c: u8) -> bool {
    c.is_ascii_alphabetic() || c == b'_'
}

fn is_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// The name a top-level declaration line declares.
fn decl_name(line: &str) -> Option<String> {
    if line.starts_with(' ') || line.starts_with('\t') {
        return None;
    }
    let mut rest = line.trim_start();
    loop {
        let mut progressed = false;
        for w in ["pub ", "unsafe ", "comptime ", "extern \"c\" "] {
            if let Some(r) = rest.strip_prefix(w) {
                rest = r;
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    for kw in [
        "struct ", "enum ", "trait ", "fn ", "const ", "type ", "union ",
    ] {
        if let Some(r) = rest.strip_prefix(kw) {
            let n: String = r
                .bytes()
                .take_while(|&b| is_ident(b))
                .map(|b| b as char)
                .collect();
            if !n.is_empty() {
                return Some(n);
            }
        }
    }
    None
}

/// `text` with every whole-word occurrence of a declared name suffixed with
/// `_z<k>`, except after a `.` (member access) and inside string literals.
pub fn rename(text: &str, declared: &[String], k: u32) -> String {
    let b = text.as_bytes();
    let mut out = String::with_capacity(text.len() + 32);
    let mut i = 0;
    let mut in_str = false;
    while i < b.len() {
        let c = b[i];
        if in_str {
            out.push(c as char);
            if c == b'\\' && i + 1 < b.len() {
                out.push(b[i + 1] as char);
                i += 2;
                continue;
            }
            if c == b'"' {
                in_str = false;
            }
            i += 1;
            continue;
        }
        if c == b'"' {
            in_str = true;
            out.push('"');
            i += 1;
            continue;
        }
        if is_ident_start(c) {
            let st = i;
            while i < b.len() && is_ident(b[i]) {
                i += 1;
            }
            let w = &text[st..i];
            let after_dot = st > 0 && b[st - 1] == b'.';
            out.push_str(w);
            if !after_dot && declared.iter().any(|d| d == w) {
                out.push_str(&format!("_z{k}"));
            }
            continue;
        }
        // Non-ASCII bytes are copied through whole.
        let ch_len = text[i..].chars().next().map_or(1, |c| c.len_utf8());
        out.push_str(&text[i..i + ch_len]);
        i += ch_len;
    }
    out
}

fn parse_template(
    rel: &str,
    chapter: u8,
    letter: char,
    src: &str,
) -> Result<Option<Template>, String> {
    let (mut rule, mut expect, mut detail) = (None, String::new(), String::new());
    let mut body: Vec<&str> = Vec::new();
    for line in src.lines() {
        if let Some(rest) = line.strip_prefix("//!") {
            let rest = rest.trim();
            if let Some(v) = rest.strip_prefix("rule:") {
                let v = v.trim();
                if let Some((_, r)) = v.split_once('.')
                    && let Some(k) = r.strip_prefix('R').or_else(|| r.strip_prefix('S'))
                {
                    let digits: String = k.chars().take_while(|c| c.is_ascii_digit()).collect();
                    rule = digits.parse::<u16>().ok();
                }
            } else if let Some(v) = rest.strip_prefix("expect:") {
                expect = v.split("--").next().unwrap_or(v).trim().to_string();
            } else if let Some(v) = rest.strip_prefix("detail:") {
                detail = v.trim().to_string();
            }
        } else {
            body.push(line);
        }
    }
    if expect != "check-error" {
        return Ok(None);
    }
    let Some(rule) = rule else {
        return Err("no `rule:` directive".into());
    };
    // The expected code: the detail's, when it opens with one; else the
    // chapter's letter and the rule's number.
    let code = {
        let d = detail.as_bytes();
        if d.len() >= 5 && d[0].is_ascii_uppercase() && d[1..5].iter().all(|c| c.is_ascii_digit()) {
            detail[..5].to_string()
        } else {
            format!("{letter}{rule:04}")
        }
    };
    // An optional `module X;`, then single-line directives, then the items.
    let mut it = body.iter().copied().peekable();
    while let Some(l) = it.peek() {
        let t = l.trim_start();
        if t.is_empty() || t.starts_with("//") {
            it.next();
        } else if t.starts_with("module ") && t.trim_end().ends_with(';') {
            it.next();
            break;
        } else {
            break;
        }
    }
    let mut header = Vec::new();
    let mut rest: Vec<&str> = Vec::new();
    let mut in_items = false;
    for l in it {
        if !in_items {
            let t = l.trim();
            if t.is_empty() || t.starts_with("//") {
                continue;
            }
            if t.starts_with("needs") || t.starts_with("contracts") {
                if !t.ends_with(';') {
                    return Err("a multi-line module directive".into());
                }
                header.push(t.to_string());
                continue;
            }
            in_items = true;
        }
        rest.push(l);
    }
    let text = rest.join("\n").trim_end().to_string();
    if text.is_empty() {
        return Err("no items".into());
    }
    for l in text.lines() {
        let t = l.trim_start();
        if t.starts_with("use ") || t.starts_with("import ") {
            return Err("imports a module (the generator is std-free)".into());
        }
    }
    // `main` is the entry point, not a name of ours to rename.
    let declared: Vec<String> = text
        .lines()
        .filter_map(decl_name)
        .filter(|n| n != "main")
        .collect();
    Ok(Some(Template {
        file: rel.to_string(),
        chapter,
        rule,
        code,
        header,
        text,
        declared,
    }))
}

fn standalone(t: &Template) -> String {
    let mut s = String::from("module m;\n");
    for h in &t.header {
        s.push_str(h);
        s.push('\n');
    }
    s.push('\n');
    s.push_str(&rename(&t.text, &t.declared, 0));
    s.push('\n');
    s
}

/// Templates written by hand for rules the corpus has no standalone,
/// std-free rejected program for (`(file label, chapter, rule, code, header,
/// text)`). They go through the same standalone validation as the corpus's.
const HAND: &[(&str, u8, u16, &str, &[&str], &str)] = &[
    (
        "hand/reduce-arity-rejected",
        3,
        11,
        "D0011",
        &[],
        "fn zred(let xs: Array[i32, 4]) -> i32 {\n    return reduce(+, xs, xs);\n}",
    ),
    (
        "hand/reduce-non-sequence-rejected",
        3,
        11,
        "D0011",
        &[],
        "fn zred(let xs: i32) -> i32 {\n    return reduce(+, xs);\n}",
    ),
    (
        "hand/specialize-required-in-simd-rejected",
        3,
        18,
        "D0018",
        &[],
        "fn zadd[T: Copyable + Add](let a: T, let b: T) -> T {\n    return a + b;\n}\n\nfn zsimd(let v: vector[f32, 8]) -> vector[f32, 8] {\n    simd for i in 0 ..< 8 {\n        var r: f32 = zadd(v[i], v[i]);\n    }\n    return v;\n}",
    ),
    (
        "hand/lane-count-not-a-power-of-two-rejected",
        3,
        19,
        "D0019",
        &[],
        "fn zlane(let v: vector[f32, 3]) {\n}",
    ),
    (
        "hand/unsafe-without-invariant-rejected",
        4,
        10,
        "A0010",
        &[],
        "@unsafe\nfn zu(let x: i32) {\n}",
    ),
    (
        "hand/unsafe-empty-invariant-rejected",
        4,
        10,
        "A0010",
        &[],
        "@unsafe(invariant: \"\")\nfn zu(let x: i32) {\n}",
    ),
    (
        "hand/comptime-reaches-runtime-binding-rejected",
        4,
        12,
        "A0012",
        &[],
        "fn zc(let n: i32) -> i32 {\n    return comptime { n };\n}",
    ),
    (
        "hand/asm-outside-unsafe-rejected",
        4,
        22,
        "A0022",
        &["needs { asm };"],
        "fn zasm() {\n    asm(aarch64) { \"nop\" };\n}",
    ),
    (
        "hand/syscall-asm-without-syscall-rejected",
        4,
        23,
        "A0023",
        &["needs { asm };"],
        "@unsafe(invariant: \"a bare svc\")\nfn zasm() {\n    asm(aarch64) { \"svc 0\" };\n}",
    ),
    (
        "hand/asm-expression-in-synth-rejected",
        4,
        27,
        "A0027",
        &["needs { asm };"],
        "@unsafe(invariant: \"a nop\")\nfn zasm() {\n    let x = asm(aarch64) { \"nop\" };\n}",
    ),
];

/// Every check-error test of the corpus that is injectable.
pub fn harvest() -> &'static Harvest {
    static H: OnceLock<Harvest> = OnceLock::new();
    H.get_or_init(|| {
        let mut h = Harvest::default();
        for (dir, chapter, letter) in DIRS {
            let d = repo_root().join("tests/conformance").join(dir);
            let mut files: Vec<PathBuf> = match std::fs::read_dir(&d) {
                Ok(rd) => rd
                    .filter_map(|e| e.ok())
                    .map(|e| e.path())
                    .filter(|p| p.extension().is_some_and(|x| x == "fors"))
                    .collect(),
                Err(_) => continue,
            };
            files.sort();
            for f in files {
                let rel = format!(
                    "{dir}/{}",
                    f.file_name().and_then(|n| n.to_str()).unwrap_or("?")
                );
                let Ok(src) = std::fs::read_to_string(&f) else {
                    continue;
                };
                match parse_template(&rel, chapter, letter, &src) {
                    Ok(None) => {}
                    Err(why) => h.unusable.push((rel, why)),
                    Ok(Some(t)) => {
                        let res = run::check(&standalone(&t), false);
                        if let Some(p) = &res.panic {
                            h.unusable.push((
                                rel,
                                format!("panics standalone: {}", p.lines().next().unwrap_or("")),
                            ));
                        } else if !res.parse.is_empty() || !res.resolve.is_empty() {
                            h.unusable
                                .push((rel, "does not parse or resolve standalone".into()));
                        } else if res.diags.len() != 1 || res.diags[0].code != t.code {
                            let got: Vec<&str> =
                                res.diags.iter().map(|d| d.code.as_str()).collect();
                            h.unusable.push((
                                rel,
                                format!("standalone it yields {got:?}, not exactly [{}]", t.code),
                            ));
                        } else {
                            h.usable.push(t);
                        }
                    }
                }
            }
        }
        for &(file, chapter, rule, code, header, text) in HAND {
            let t = Template {
                file: file.to_string(),
                chapter,
                rule,
                code: code.to_string(),
                header: header.iter().map(|s| s.to_string()).collect(),
                text: text.to_string(),
                declared: text.lines().filter_map(decl_name).collect(),
            };
            let res = run::check(&standalone(&t), false);
            if res.panic.is_none()
                && res.parse.is_empty()
                && res.resolve.is_empty()
                && res.diags.len() == 1
                && res.diags[0].code == t.code
            {
                h.usable.push(t);
            } else {
                h.unusable.push((
                    file.to_string(),
                    "a hand template that is not rejected standalone with its code".into(),
                ));
            }
        }
        h.usable.truncate(255);
        h
    })
}

/// Injects template number `variant` into `p`.
pub fn m_template(p: &mut Program, rng: &mut Rng, variant: u8) -> Option<Applied> {
    let t = harvest().usable.get(variant as usize)?.clone();
    let k = p.id();
    let text = rename(&t.text, &t.declared, k);
    for h in &t.header {
        if !p.header.contains(h) {
            p.header.push(h.clone());
        }
    }
    let id = p.id();
    let at = rng.below(p.items.len() + 1);
    p.items.insert(at, Item::Raw { id, text });
    ap(id, format!("the conformance test {}", t.file))
}

/// One catalogue row per usable template.
pub fn defs() -> Vec<MutDef> {
    harvest()
        .usable
        .iter()
        .enumerate()
        .map(|(i, t)| {
            let stem = t.file.trim_end_matches(".fors");
            MutDef {
                name: Box::leak(format!("corpus/{stem}").into_boxed_str()),
                chapter: t.chapter,
                rule: t.rule,
                code: Box::leak(t.code.clone().into_boxed_str()),
                variant: i as u8,
                f: m_template,
                inject: true,
            }
        })
        .collect()
}
