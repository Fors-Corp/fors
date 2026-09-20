//! `cargo run -p fors-fmt --example fmt -- <file>...`
//!
//! Prints one line per file: `formatted|canonical|parse-error  <path>`, and
//! writes the formatted text back only when `--write` is given. It exists so
//! the formatter can be driven before `fors fmt` is wired into the CLI, and so
//! CI can assert that every `.fors` file in the repository is canonical.
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let write = args.iter().any(|a| a == "--write");
    let mut dirty = 0usize;
    for path in args.iter().filter(|a| !a.starts_with("--")) {
        let Ok(src) = std::fs::read(path) else {
            println!("unreadable       {path}");
            continue;
        };
        let out = fors_fmt::format_source(&src);
        let tag = match out.status {
            fors_fmt::Status::ParseFailed => "parse-error",
            _ if out.changed => "formatted",
            _ => "canonical",
        };
        if out.changed {
            dirty += 1;
            if write {
                let _ = std::fs::write(path, &out.text);
            }
        }
        println!("{tag:<12} {path}");
    }
    if dirty > 0 && !write {
        std::process::exit(1);
    }
}
