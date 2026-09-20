//! Inputs the corpus lacks, each of which exposed or guards a specific
//! behaviour. Every case is checked for the same properties as the corpus
//! (status, losslessness, idempotence, no trailing whitespace) and then for
//! the exact shape it was written to pin down.

use fors_fmt::{MARGIN, Status, check_source, format_source, same_tokens};

/// Formats, checks the properties, returns the text.
fn fmt(src: &str) -> String {
    let once = format_source(src.as_bytes());
    assert_eq!(once.status, Status::Formatted, "declined: {src}");
    assert!(same_tokens(src.as_bytes(), &once.text), "tokens changed for: {src}");
    let twice = format_source(&once.text);
    assert_eq!(twice.status, Status::Formatted);
    assert_eq!(
        String::from_utf8_lossy(&twice.text),
        String::from_utf8_lossy(&once.text),
        "not idempotent for: {src}"
    );
    for line in once.text.split(|&b| b == b'\n') {
        assert!(!line.ends_with(b" ") && !line.ends_with(b"\t") && !line.contains(&b'\r'), "trailing ws: {src}");
    }
    let c = check_source(src.as_bytes());
    let mut patched = src.as_bytes().to_vec();
    for e in c.edits.iter().rev() {
        patched.splice(e.start as usize..e.end as usize, e.new_text.iter().copied());
    }
    assert_eq!(patched, once.text, "check edits do not reproduce the format: {src}");
    String::from_utf8(once.text).unwrap()
}

#[test]
fn a_comment_between_every_pair_of_tokens_in_a_signature() {
    // exposed: a block comment after the last token before the signature's
    // tail group broke landed at the start of the next line and was then
    // read as a standalone comment on the second pass (not idempotent)
    let out = fmt("fn /*a*/ f /*b*/ [ /*c*/ T /*d*/ ] /*e*/ ( /*f*/ let /*g*/ x /*h*/ : /*i*/ T /*j*/ ) /*k*/ -> /*l*/ T /*m*/ raises /*n*/ E /*o*/ { /*p*/ return /*q*/ x /*r*/ ; /*s*/ } /*t*/\n");
    assert!(out.contains("x /*h*/ : /*i*/ T"), "{out}"); // spaced on both sides
    assert!(out.contains("/*o*/ {"), "{out}");
    let out = fmt("fn // a\nf // b\n( // c\nlet x: i32 // d\n) // e\n-> i32 // f\n{ // g\nreturn x; // h\n} // i\n");
    assert_eq!(out, "fn // a\nf // b\n( // c\n    let x: i32 // d\n) // e\n-> i32 // f\n{ // g\n    return x; // h\n} // i\n");
}

#[test]
fn a_comment_inside_an_empty_block_struct_match_and_list() {
    let out = fmt("fn f() {\n    // only a comment\n}\nstruct S { /* nothing */ }\nfn g(let x: i32) {\n    match x {\n        // no arms\n    }\n    let a = [ /* empty */ ];\n    let b = f( /* none */ );\n}\n");
    assert_eq!(
        out,
        "fn f() {\n    // only a comment\n}\nstruct S { /* nothing */ }\nfn g(let x: i32) {\n    match x {\n        // no arms\n    }\n    let a = [ /* empty */ ];\n    let b = f( /* none */ );\n}\n"
    );
}

#[test]
fn a_doc_comment_on_a_field_and_on_a_match_arm() {
    let src = "struct P {\n    /// the x coordinate\n    x: i32,\n    /// the y coordinate\n    y: i32,\n}\nfn g(let x: i32) -> i32 {\n    match x {\n        /// zero case\n        0 => 1,\n        /// everything else\n        _ => 2,\n    }\n}\n";
    assert_eq!(fmt(src), src);
}

#[test]
fn a_line_at_exactly_100_columns_stays_and_101_breaks() {
    let body = "    let x = f(aaaaaaaa, ";
    let mk = |n: usize| format!("fn g() {{\n{body}{});\n}}\n", "b".repeat(n - body.len() - 2));
    let at100 = mk(MARGIN);
    assert_eq!(at100.lines().nth(1).unwrap().len(), MARGIN);
    assert_eq!(fmt(&at100), at100);
    let at101 = mk(MARGIN + 1);
    let out = fmt(&at101);
    assert!(out.contains("f(\n        aaaaaaaa,\n        bbb"), "{out}");
}

#[test]
fn a_chain_of_twelve_adaptors_with_closures_containing_chains() {
    let calls: Vec<String> =
        (0..12).map(|i| format!("map(|x| x.iter().map(|y| y + {i}).filter(|z| z > {i}).count())")).collect();
    let src = format!("fn g(let v: Vec[i32, A]) -> usize {{\n    return v.iter().{}.count();\n}}\n", calls.join("."));
    let out = fmt(&src);
    // one call per line, dot leading, the inner chains flat
    assert!(out.contains("    return v.iter()\n        .map(|x| x.iter().map(|y| y + 0).filter(|z| z > 0).count())\n"), "{out}");
    assert!(out.contains("\n        .count();\n"), "{out}");
    assert_eq!(out.lines().filter(|l| l.trim_start().starts_with(".map(")).count(), 12);
}

#[test]
fn deeply_nested_generics_with_constraint_entries_that_cannot_fit() {
    let gens: Vec<String> = (0..6)
        .map(|i| format!("T{i}: Iterator + Show + Copyable"))
        .chain((0..6).map(|i| format!("T{i}.Item: Show + Copyable + Eq")))
        .collect();
    let ty = "Map[Vec[Map[Vec[T0, A], Vec[T1, A], A], A], Vec[Map[Vec[T2, A], Vec[T3, A], A], A], A]";
    let src = format!("fn g[{}](let a: {ty}) -> {ty} raises SomeVeryLongErrorTypeName {{\n    return a;\n}}\n", gens.join(", "));
    let out = fmt(&src);
    assert!(out.starts_with("fn g[\n    T0: Iterator + Show + Copyable,\n"), "{out}");
    assert!(out.contains("    T5.Item: Show + Copyable + Eq\n](\n    let a: Map["), "{out}");
    assert!(out.contains("\n    raises SomeVeryLongErrorTypeName\n{\n    return a;\n}\n"), "{out}");
}

#[test]
fn a_string_literal_with_braces_a_comment_marker_and_an_escaped_newline() {
    let src = "fn g() {\n    let s = \"{ } // not a comment \\n { {\";\n    let t = \"\\\"\";\n}\n";
    assert_eq!(fmt(src), src);
}

#[test]
fn a_multibyte_identifier_is_a_lexical_error_and_the_file_is_untouched() {
    // the lexer allows ASCII identifiers only: the file does not parse and
    // must come back byte-identical, never "formatted"
    let src = "fn g() {\n    let café = 1;\n}\n";
    let out = format_source(src.as_bytes());
    assert_eq!(out.status, Status::ParseFailed);
    assert_eq!(out.text, src.as_bytes());
    // a multi-byte character inside a string is fine, and one column wide
    let src = "fn g() {\n    let s = \"日本語😀\";\n}\n";
    assert_eq!(fmt(src), src);
}

#[test]
fn crlf_line_endings_become_lf() {
    // exposed: the CR before the newline that ends a line comment is part
    // of the comment token, so it survived as trailing whitespace and the
    // file came out with mixed line endings
    let out = fmt("fn g() {\r\n    let x = 1;\r\n\r\n\r\n    let y = 2; // c\r\n}\r\n");
    assert_eq!(out, "fn g() {\n    let x = 1;\n\n    let y = 2; // c\n}\n");
    // already canonical apart from the line endings still counts as changed
    assert!(format_source(b"fn g() {}\r\n").changed);
    assert!(!format_source(b"fn g() {}\n").changed);
    // a lone CR that does not precede a newline is left alone
    assert!(same_tokens(b"fn g() {}\r\n", b"fn g() {}\n"));
}

#[test]
fn a_file_with_no_trailing_newline_gets_exactly_one() {
    assert_eq!(fmt("fn g() {\n    let x = 1;\n}"), "fn g() {\n    let x = 1;\n}\n");
    assert_eq!(fmt("fn g() {}\n\n\n\n"), "fn g() {}\n");
}

#[test]
fn a_file_that_is_only_comments_or_only_whitespace() {
    assert_eq!(fmt("// just a comment\n\n\n// and another\n/* block */\n"), "// just a comment\n\n// and another\n/* block */\n");
    assert_eq!(fmt("\n\n   \n"), "");
    assert_eq!(fmt("/* a */"), "/* a */\n");
}

#[test]
fn a_single_block_closure_argument_hugs_the_parens() {
    let out = fmt("fn g() {\n    v.each(|x| { print(x); });\n    v.each(|x| { print(x); }, 1);\n    v.each(|x| { print(x); },);\n}\n");
    assert_eq!(
        out,
        "fn g() {\n    v.each(|x| {\n        print(x);\n    });\n    v.each(\n        |x| {\n            print(x);\n        },\n        1\n    );\n    v.each(\n        |x| {\n            print(x);\n        },\n    );\n}\n"
    );
}

#[test]
fn a_one_megabyte_file_formats_in_bounded_time() {
    // one unit is ~1.6 KB of chains, wide generics, control flow and doc
    // comments; 600 of them is a megabyte
    let unit = "fn g{n}(let v: Vec[i32, A]) -> usize {\n    return v.iter().map(|x| x.iter().map(|y| y + 1).filter(|z| z > 1).count()).map(|x| x.iter().map(|y| y + 2).filter(|z| z > 2).count()).count();\n}\nfn h{n}[T0: Iterator + Show + Copyable, T1: Iterator + Show + Copyable, T0.Item: Show + Copyable + Eq, T1.Item: Show + Copyable + Eq](let a: Map[Vec[Map[Vec[T0, A], Vec[T1, A], A], A], Vec[Map[Vec[T0, A], Vec[T1, A], A], A], A]) -> usize raises SomeVeryLongErrorTypeName {\n    return 0;\n}\nfn k{n}(let x: i32) {\n    if x { a(); } else if y { b(); } else { c(); }\n    while x { break; }\n    for i in 0..<n { continue; }\n    defer { close(); }\n    errdefer { undo(); }\n}\nstruct P{n} {\n    /// the x coordinate\n    x: i32,\n    /// the y coordinate\n    y: i32,\n}\nfn m{n}(let x: i32) -> i32 {\n    match x {\n        /// zero case\n        0 => aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n        _ => 2,\n    }\n}\n";
    let mut src = String::new();
    let mut n = 0;
    while src.len() < 1 << 20 {
        src.push_str(&unit.replace("{n}", &n.to_string()));
        n += 1;
    }
    let t = std::time::Instant::now();
    let out = format_source(src.as_bytes());
    let format_ms = t.elapsed().as_millis();
    assert_eq!(out.status, Status::Formatted);
    let t = std::time::Instant::now();
    let c = check_source(src.as_bytes());
    let check_ms = t.elapsed().as_millis();
    assert!(!c.formatted);
    let t = std::time::Instant::now();
    let twice = format_source(&out.text);
    let second_ms = t.elapsed().as_millis();
    assert_eq!(twice.text, out.text);
    eprintln!("1 MB ({} bytes, {n} units): format {format_ms} ms, check {check_ms} ms, second pass {second_ms} ms", src.len());
    // a debug build of an unoptimised linear pipeline: seconds, not minutes
    assert!(format_ms < 30_000 && check_ms < 30_000, "format {format_ms} ms, check {check_ms} ms");
}
