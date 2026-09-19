//! Throughput benchmark, `#[ignore]`d by default: `cargo test -p fors-lex
//! --release -- --ignored bench_100k_lines`.

use std::time::Instant;

/// Generates a deterministic ~100k-line synthetic Fors-shaped source: no
/// need for it to parse, only to exercise every lexer state (idents,
/// keywords, numbers, strings, comments, operators) at realistic density.
fn generate_source(target_lines: usize) -> Vec<u8> {
    let mut out = String::with_capacity(target_lines * 32);
    for i in 0..target_lines {
        match i % 6 {
            0 => out.push_str(&format!("fn f{i}(let x: i32) -> i32 {{\n")),
            1 => out.push_str(&format!("    let y{i} = x + {i} * 2 - 1_000;\n")),
            2 => out.push_str("    // a line comment with some words in it\n"),
            3 => out.push_str(&format!("    let s{i} = \"hello \\n world {i}\";\n")),
            4 => out.push_str(&format!("    if x <= {i} {{ return x; }} else {{ return {i}; }}\n")),
            _ => out.push_str("}\n\n"),
        }
    }
    out.into_bytes()
}

#[test]
#[ignore]
fn bench_100k_lines() {
    let src = generate_source(100_000);
    let mib = src.len() as f64 / (1024.0 * 1024.0);

    // one warm-up pass
    let (_tokens, _diags) = fors_lex::lex(&src);

    let start = Instant::now();
    let (tokens, _diags) = fors_lex::lex(&src);
    let elapsed = start.elapsed();

    let ms = elapsed.as_secs_f64() * 1000.0;
    let mib_per_s = mib / elapsed.as_secs_f64();
    println!(
        "lexed {} bytes ({:.2} MiB) into {} tokens in {:.3} ms ({:.1} MiB/s)",
        src.len(),
        mib,
        tokens.len(),
        ms,
        mib_per_s
    );
}
