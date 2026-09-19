//! Single-threaded parse benchmark. `#[ignore]`d so `cargo test` stays
//! fast; run explicitly with:
//!
//!     cargo test -p fors-syntax --test bench -- --ignored --nocapture
//!
//! Generates ~100k lines of valid Fors (functions mixing arithmetic,
//! calls, if/else and a couple of struct declarations), parses it
//! single-threaded (lex + parse, best of 5), and prints milliseconds,
//! throughput, and the resident size of the token and tree columns.

use std::mem::size_of;
use std::time::Instant;

fn generate(target_lines: usize) -> String {
    let mut s = String::new();
    s.push_str("struct Point { x: i32, y: i32 }\nstruct Line { a: Point, b: Point }\n\n");
    let mut lines = 3;
    let mut i: u32 = 0;
    while lines < target_lines {
        s.push_str(&format!(
            "fn f{i}(let a: i32, let b: i32, let p: Point) -> i32 {{\n\
             \x20   let c = a + b * 2 - 1;\n\
             \x20   let d = (a - b) * (a + b) / 3 + 7;\n\
             \x20   if c > 0 {{\n\
             \x20       c = c + f{prev}(a, b, p);\n\
             \x20   }} else {{\n\
             \x20       c = c - d + p.x - p.y;\n\
             \x20   }}\n\
             \x20   return c;\n\
             }}\n\n",
            i = i,
            prev = if i == 0 { 0 } else { i - 1 }
        ));
        lines += 10;
        i += 1;
    }
    s
}

#[test]
#[ignore]
fn bench_100k_lines() {
    let src = generate(100_000);
    let bytes = src.as_bytes();
    eprintln!("generated {} lines, {} bytes", src.lines().count(), bytes.len());

    // best of 5: the first run pays for page faults on fresh allocations
    let mut best = std::time::Duration::MAX;
    let mut parsed = fors_syntax::parse_file(bytes);
    for _ in 0..5 {
        let start = Instant::now();
        parsed = fors_syntax::parse_file(bytes);
        best = best.min(start.elapsed());
    }
    let elapsed = best;
    let (tree, tokens, diags) = (&parsed.tree, &parsed.tokens, &parsed.diags);

    assert!(diags.is_empty(), "generated source must be diagnostic-free: {:?}", &diags[..diags.len().min(5)]);

    let ms = elapsed.as_secs_f64() * 1000.0;
    let mib = 1024.0 * 1024.0;
    let mib_per_s = (bytes.len() as f64 / mib) / elapsed.as_secs_f64();
    let node_count = tree.kinds.len();

    let tree_bytes = node_count * (size_of::<fors_syntax::NodeKind>() + 3 * size_of::<u32>());
    let token_bytes = tokens.kinds.len() * size_of::<fors_lex::TokenKind>() + tokens.starts.len() * size_of::<u32>();

    println!(
        "lex+parse: {:.2} ms, {:.1} MiB/s, {:.2} M lines/s | {} tokens, {} nodes ({:.1} M nodes/s) | tree {:.2} MiB = {:.2} bytes/source byte, tokens {:.2} MiB = {:.2} bytes/source byte, total {:.2} MiB",
        ms,
        mib_per_s,
        src.lines().count() as f64 / elapsed.as_secs_f64() / 1e6,
        tokens.kinds.len(),
        node_count,
        node_count as f64 / elapsed.as_secs_f64() / 1e6,
        tree_bytes as f64 / mib,
        tree_bytes as f64 / bytes.len() as f64,
        token_bytes as f64 / mib,
        token_bytes as f64 / bytes.len() as f64,
        (tree_bytes + token_bytes) as f64 / mib,
    );
}
