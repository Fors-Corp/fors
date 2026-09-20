//! Development audit: the widest formatted lines, and which files decline.
fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    let mut e: Vec<_> = rd.filter_map(|e| e.ok()).map(|e| e.path()).collect();
    e.sort();
    for p in e {
        if p.is_dir() { walk(&p, out) } else if p.extension().is_some_and(|x| x == "fors") { out.push(p) }
    }
}
fn main() {
    let mut files = Vec::new();
    for a in std::env::args().skip(1) { walk(std::path::Path::new(&a), &mut files) }
    let mut wide: Vec<(usize, String, String)> = Vec::new();
    let mut failed: Vec<String> = Vec::new();
    for p in &files {
        let src = std::fs::read(p).unwrap();
        let f = fors_fmt::format_source(&src);
        if f.status != fors_fmt::Status::Formatted { failed.push(p.display().to_string()); continue }
        for line in f.text.split(|&b| b == b'\n') {
            let w = line.iter().filter(|b| (**b & 0xC0) != 0x80).count();
            if w > fors_fmt::MARGIN {
                wide.push((w, p.display().to_string(), String::from_utf8_lossy(&line[..line.len().min(160)]).to_string()));
            }
        }
    }
    wide.sort_by(|a, b| b.0.cmp(&a.0));
    println!("over margin: {} lines", wide.len());
    for (w, p, l) in wide.iter().filter(|(_,_,l)| !l.trim_start().starts_with("//")).take(20) { println!("{w:4} {p}\n     {l}"); }
    println!("declined: {}", failed.len());
    for p in failed.iter() { println!("  {p}") }
}
