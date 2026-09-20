//! `fors explain <CODE>`: the normative rule behind a diagnostic code,
//! offline.
//!
//! An agent that has never seen Fors cannot look a code up, and the spec is
//! the only thing entitled to say what a rule means. So the chapters are
//! embedded verbatim with `include_str!` and the rule item is extracted from
//! that text AT RUNTIME: nothing here paraphrases a rule, and a rule edited
//! in `docs/spec/` changes this output on the next build with no second
//! place to update.
//!
//! The one exception is `P`/`L` — parser and lexer codes number no rule in
//! any chapter's rule list, so they are a hand table here, mirroring the
//! doc comments on `fors_syntax::DiagCode` and `fors_lex::DiagCode`.

/// The footer every explanation ends with: the chapters are the spec's
/// text, reproduced under its licence.
pub const FOOTER: &str = "Fors specification, CC-BY-4.0";

struct Chapter {
    /// The code letter whose number is a rule number in this chapter.
    letter: u8,
    /// The file stem under `docs/spec/`, which is also what the JSON
    /// diagnostic record reports as `rule.chapter`.
    stem: &'static str,
    text: &'static str,
}

/// Code letter to chapter (type-checker design §3 fork 15: the letter
/// names the chapter, the number IS that chapter's rule number).
static CHAPTERS: [Chapter; 7] = [
    Chapter {
        letter: b'O',
        stem: "01-ownership",
        text: include_str!("../../../docs/spec/01-ownership.md"),
    },
    Chapter {
        letter: b'F',
        stem: "02-failure",
        text: include_str!("../../../docs/spec/02-failure.md"),
    },
    Chapter {
        letter: b'D',
        stem: "03-numerics-determinism",
        text: include_str!("../../../docs/spec/03-numerics-determinism.md"),
    },
    Chapter {
        letter: b'A',
        stem: "04-authority",
        text: include_str!("../../../docs/spec/04-authority.md"),
    },
    Chapter {
        letter: b'N',
        stem: "08-names",
        text: include_str!("../../../docs/spec/08-names.md"),
    },
    Chapter {
        letter: b'T',
        stem: "09-types",
        text: include_str!("../../../docs/spec/09-types.md"),
    },
    Chapter {
        letter: b'S',
        stem: "10-std",
        text: include_str!("../../../docs/spec/10-std.md"),
    },
];

/// Chapter 7 owns the lexer and the grammar; its `P`/`L` diagnostics are
/// not numbered rule items, so only its title and path are used.
static GRAMMAR: &str = include_str!("../../../docs/spec/07-grammar.md");

/// `fors_lex::DiagCode`, in discriminant order.
static LEX_CODES: [(&str, &str); 8] = [
    (
        "L0000",
        "A block comment was never closed: `/*` reached the end of the file at nesting depth greater than zero (ch07 §2).",
    ),
    (
        "L0001",
        "A `\"...\"` string hit a raw newline or the end of the file before its closing quote (ch07 §5).",
    ),
    (
        "L0002",
        "An escape inside a `\"...\"` string is not one of `\\n \\r \\t \\0 \\\\ \\\" \\xHH \\u{H..}` (ch07 §5).",
    ),
    (
        "L0003",
        "An identifier run glued directly onto a number literal is not one of the legal width suffixes (ch07 §4).",
    ),
    (
        "L0004",
        "`..` is not immediately followed by `<` or `=`; the range operators are `..<` and `..=` (ch07 §7).",
    ),
    (
        "L0005",
        "A byte that starts no token at all: stray punctuation, or a bare non-ASCII byte outside a comment or string.",
    ),
    (
        "L0006",
        "The source is larger than the lexer's `MAX_SOURCE_LEN`; lexing stops after one error token.",
    ),
    (
        "L0007",
        "The source is not valid UTF-8 inside a comment or string literal (elsewhere the bytes are already L0005). Reported once per file.",
    ),
];

/// `fors_syntax::DiagCode`, in discriminant order.
static PARSE_CODES: [(&str, &str); 10] = [
    (
        "P0001",
        "A production expected a specific token (or one of a small set) and found something else. The message names what was expected.",
    ),
    (
        "P0002",
        "A `;` was expected and the next token is a statement or declaration boundary, so one virtual `;` was inserted and parsing continued. The reported range is the end of the previous token, which is where the `;` belongs.",
    ),
    (
        "P0003",
        "A `{`, `(` or `[` was never closed before a declaration-sync token or the end of the file; every open construct up to the enclosing item list was force-closed. The range is the opening delimiter.",
    ),
    (
        "P0004",
        "The left-hand side of an assignment operator does not have the shape of a `place`.",
    ),
    (
        "P0005",
        "Ch07 rule 12: mixing a bitwise operator with arithmetic, range, comparison or a different bitwise operator needs parentheses.",
    ),
    (
        "P0006",
        "Ch07: comparison operators do not chain; write the two comparisons and an `and`.",
    ),
    (
        "P0007",
        "The recursion and nesting depth limit was hit; parsing of the construct stopped rather than risking a stack overflow.",
    ),
    (
        "P0008",
        "A lexical error (the message names which `L` code); the token was skipped.",
    ),
    (
        "P0009",
        "Tokens that start no declaration or item; the range covers what was skipped to resynchronise.",
    ),
    (
        "P0010",
        "Ch07 operator table level 6: the range operators are single use and do not chain.",
    ),
];

/// One code's explanation: everything both renderers print.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Explanation {
    pub code: String,
    pub chapter_title: String,
    /// Repository-relative path of the chapter the text was taken from.
    pub spec_path: String,
    /// The rule number inside that chapter, or `None` for a `P`/`L` code,
    /// which numbers no rule.
    pub rule: Option<u16>,
    /// The rule item VERBATIM, as the chapter writes it (or, for `P`/`L`,
    /// this crate's hand table).
    pub text: String,
}

/// Splits `"N0014"` into `(b'N', 14)`, and a LETTERED SUB-RULE citation
/// into the rule that owns it: `"O0019C"` is `(b'O', 19)`. The spec numbers
/// sub-rules `19a.`/`19c.` and the pack's rule index cites them that way, so
/// an agent reading the pack types one — and [`rule_item`] already returns a
/// rule with its sub-rules attached, so the base rule IS the answer for
/// both. `None` for anything that is not a letter, four digits and at most
/// one trailing letter.
fn split_code(code: &str) -> Option<(u8, u16)> {
    let b = code.as_bytes();
    let core: &[u8] = match b.len() {
        5 => b,
        6 if b[5].is_ascii_alphabetic() => &b[..5],
        _ => return None,
    };
    if !core[0].is_ascii_uppercase() || !core[1..].iter().all(u8::is_ascii_digit) {
        return None;
    }
    let n = code[1..5].parse::<u16>().ok()?;
    Some((core[0], n))
}

/// The chapter and rule number a diagnostic code cites, or `None` for a
/// `P`/`L` code (and for anything unrecognised). The chapter is the
/// `docs/spec/` file stem.
pub fn rule_of(code: &str) -> Option<(&'static str, u16)> {
    let (letter, n) = split_code(code)?;
    CHAPTERS
        .iter()
        .find(|c| c.letter == letter)
        .map(|c| (c.stem, n))
}

fn lines_with_offsets(text: &str) -> impl Iterator<Item = (usize, &str)> {
    let mut off = 0usize;
    text.split('\n').map(move |l| {
        let at = off;
        off += l.len() + 1;
        (at, l)
    })
}

/// The chapter's title: its first `# ` heading.
fn title_of(text: &str) -> String {
    text.lines()
        .find(|l| l.starts_with("# "))
        .map(|l| l[2..].trim().to_string())
        .unwrap_or_default()
}

/// The body of the chapter's `## Rules` section: everything between that
/// heading and the next level-two heading (`### ` subheadings inside it
/// are part of the section).
fn rules_section(text: &str) -> &str {
    let mut begin: Option<usize> = None;
    for (at, line) in lines_with_offsets(text) {
        match begin {
            None => {
                if line.trim_end() == "## Rules" {
                    begin = Some((at + line.len() + 1).min(text.len()));
                }
            }
            Some(b) => {
                if line.starts_with("## ") {
                    return &text[b..at];
                }
            }
        }
    }
    begin.map_or("", |b| &text[b..])
}

/// Whether `line` opens a new numbered rule item (`"20. "`). A lettered
/// sub-rule (`"19a. "`) deliberately does NOT, so it stays part of the
/// rule it qualifies.
fn is_rule_head(line: &str) -> bool {
    let b = line.as_bytes();
    let digits = b.iter().take_while(|c| c.is_ascii_digit()).count();
    digits > 0 && b.len() > digits + 1 && b[digits] == b'.' && b[digits + 1] == b' '
}

fn heads_rule(line: &str, k: u16) -> bool {
    let mut head = k.to_string();
    head.push_str(". ");
    line.starts_with(&head)
}

/// Rule `k` of `section`, verbatim, including any `ka.`/`kb.` sub-rules
/// that follow it as items of their own.
fn rule_item(section: &str, k: u16) -> Option<String> {
    let mut begin: Option<usize> = None;
    let mut end = section.len();
    for (at, line) in lines_with_offsets(section) {
        if begin.is_none() {
            if heads_rule(line, k) {
                begin = Some(at);
            }
        } else if line.starts_with('#') || is_rule_head(line) {
            end = at;
            break;
        }
    }
    let b = begin?;
    let s = section[b..end].trim_end();
    if s.is_empty() {
        None
    } else {
        Some(s.to_string())
    }
}

/// Every rule number the chapter's rule list actually contains, ascending
/// and deduplicated.
fn rule_numbers(section: &str) -> Vec<u16> {
    let mut out: Vec<u16> = Vec::new();
    for (_, line) in lines_with_offsets(section) {
        if !is_rule_head(line) {
            continue;
        }
        let digits: String = line.chars().take_while(|c| c.is_ascii_digit()).collect();
        if let Ok(n) = digits.parse::<u16>()
            && !out.contains(&n)
        {
            out.push(n);
        }
    }
    out.sort_unstable();
    out
}

/// The explanation of `code`, or `None` when no such code exists.
pub fn explain(code: &str) -> Option<Explanation> {
    let (letter, n) = split_code(code)?;
    if letter == b'P' || letter == b'L' {
        let table: &[(&str, &str)] = if letter == b'L' {
            &LEX_CODES
        } else {
            &PARSE_CODES
        };
        let (_, text) = table.iter().find(|(c, _)| *c == code)?;
        return Some(Explanation {
            code: code.to_string(),
            chapter_title: title_of(GRAMMAR),
            spec_path: "docs/spec/07-grammar.md".to_string(),
            rule: None,
            text: (*text).to_string(),
        });
    }
    let ch = CHAPTERS.iter().find(|c| c.letter == letter)?;
    let text = rule_item(rules_section(ch.text), n)?;
    Some(Explanation {
        // The base code, even when a sub-rule was asked for: it is the one
        // `--list` names, and the sub-rule is inside `text`.
        code: format!("{}{n:04}", letter as char),
        chapter_title: title_of(ch.text),
        spec_path: format!("docs/spec/{}.md", ch.stem),
        rule: Some(n),
        text,
    })
}

/// Every explainable code, in a stable order (`L`, then `P`, then the
/// chapters in spec order), each with the first sentence of its rule.
pub fn list() -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    for (code, text) in LEX_CODES.iter().chain(PARSE_CODES.iter()) {
        out.push(((*code).to_string(), first_sentence(text)));
    }
    // Spec order, not code-letter order: a reader scanning the list is
    // reading the specification's table of contents.
    let mut chapters: Vec<&Chapter> = CHAPTERS.iter().collect();
    chapters.sort_by_key(|c| c.stem);
    for ch in chapters {
        let section = rules_section(ch.text);
        for n in rule_numbers(section) {
            let Some(item) = rule_item(section, n) else {
                continue;
            };
            out.push((
                format!("{}{n:04}", ch.letter as char),
                first_sentence(&item),
            ));
        }
    }
    out
}

/// The first sentence of a rule item, with its `"14. **N0014** — "` label
/// removed and its wrapped lines joined — enough for `--list` to be
/// readable, never a substitute for the rule.
fn first_sentence(item: &str) -> String {
    let mut s = item.trim_start();
    // Drop the list number.
    if let Some(p) = s.find(". ")
        && s[..p].bytes().all(|b| b.is_ascii_digit())
    {
        s = s[p + 2..].trim_start();
    }
    // Drop the `**N0014** —` label when the chapter writes one.
    if let Some(rest) = s.strip_prefix("**")
        && let Some(p) = rest.find("**")
    {
        let after = rest[p + 2..].trim_start();
        s = after
            .strip_prefix('—')
            .or_else(|| after.strip_prefix('-'))
            .map_or(after, |t| t.trim_start());
    }
    let mut flat = String::with_capacity(s.len().min(400));
    let mut space = false;
    for c in s.chars() {
        if c.is_whitespace() {
            space = !flat.is_empty();
        } else {
            if space {
                flat.push(' ');
            }
            space = false;
            flat.push(c);
        }
        if flat.len() > 400 {
            break;
        }
    }
    let cut = flat
        .char_indices()
        .find(|&(i, c)| c == '.' && flat[i + 1..].starts_with(' '))
        .map(|(i, _)| i + 1);
    let mut s = match cut {
        Some(i) => flat[..i].to_string(),
        None => flat,
    };
    if s.len() > 240 {
        let mut end = 240;
        while end > 0 && !s.is_char_boundary(end) {
            end -= 1;
        }
        s.truncate(end);
        s.push('…');
    }
    s
}

/// The human rendering: header, spec path, the rule verbatim, footer.
pub fn render_text(e: &Explanation) -> String {
    let mut out = String::new();
    out.push_str(&e.code);
    out.push_str(" — ");
    out.push_str(&e.chapter_title);
    if let Some(r) = e.rule {
        out.push_str(&format!(", Rule {r}"));
    }
    out.push('\n');
    out.push_str(&e.spec_path);
    out.push_str("\n\n");
    out.push_str(&e.text);
    out.push_str("\n\n");
    out.push_str(FOOTER);
    out.push('\n');
    out
}

/// The machine rendering: one JSON object, one line.
pub fn render_json(e: &Explanation) -> String {
    let mut out = String::new();
    out.push_str("{\"schema\":1,\"kind\":\"explain\",\"code\":");
    out.push_str(&crate::json::quoted(&e.code));
    out.push_str(",\"chapter\":{\"title\":");
    out.push_str(&crate::json::quoted(&e.chapter_title));
    out.push_str(",\"path\":");
    out.push_str(&crate::json::quoted(&e.spec_path));
    out.push_str("},\"rule\":");
    match e.rule {
        Some(r) => crate::push_u32(u32::from(r), &mut out),
        None => out.push_str("null"),
    }
    out.push_str(",\"text\":");
    out.push_str(&crate::json::quoted(&e.text));
    out.push_str(",\"license\":");
    out.push_str(&crate::json::quoted(FOOTER));
    out.push('}');
    out
}

/// One `--list` row as JSON.
pub fn render_list_json(code: &str, summary: &str) -> String {
    let mut out = String::new();
    out.push_str("{\"schema\":1,\"kind\":\"code\",\"code\":");
    out.push_str(&crate::json::quoted(code));
    out.push_str(",\"summary\":");
    out.push_str(&crate::json::quoted(summary));
    out.push('}');
    out
}
