//! Line diff and text edits: what `fors fmt --check` prints and what the
//! LSP sends back for a formatting request.
//!
//! Line-granular Myers, over 64-bit line hashes, with a bounded edit
//! distance. Formatting output is close to its input, so `d` is small in
//! practice; past the bound the whole differing region becomes one edit,
//! which is still correct, just coarser.

/// A replacement of `source[start..end]` by `new_text`. Byte offsets are
/// into the ORIGINAL buffer and edits never overlap, so a consumer may
/// apply them in any order as long as it applies them from the back.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub start: u32,
    pub end: u32,
    pub new_text: Vec<u8>,
}

/// Byte offset of the start of each line, plus a final sentinel equal to
/// the buffer length: line `i` is `src[starts[i]..starts[i + 1]]`,
/// terminator included.
fn line_starts(src: &[u8]) -> Vec<usize> {
    let mut v = Vec::with_capacity(src.len() / 24 + 2);
    v.push(0);
    for (i, &b) in src.iter().enumerate() {
        if b == b'\n' {
            v.push(i + 1);
        }
    }
    // a buffer that ends with a newline has no empty trailing line
    if v.last().copied() != Some(src.len()) {
        v.push(src.len());
    }
    v
}

fn hashes(src: &[u8], starts: &[usize]) -> Vec<u64> {
    let mut v = Vec::with_capacity(starts.len().saturating_sub(1));
    for w in starts.windows(2) {
        let mut h: u64 = 0xcbf29ce484222325;
        for &b in &src[w[0]..w[1]] {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        v.push(h);
    }
    v
}

/// Matched line pairs, as `(a_index, b_index)`, in increasing order.
///
/// MARC: the trace keeps only the `2d + 1` diagonals round `d` can touch,
/// not a copy of the whole `v` per round. The whole-`v` version is
/// O(d * (n + m)) memory, which on a 1 MB unformatted file (60k lines,
/// d up to the 2048 bound) is two gigabytes; this is O(d^2), 32 MB at
/// the bound.
fn myers(a: &[u64], b: &[u64], max_d: usize) -> Option<Vec<(usize, usize)>> {
    let n = a.len();
    let m = b.len();
    let max = n + m;
    let offset = max as isize;
    let mut v = vec![0isize; 2 * max + 2];
    // trace[d] holds v[offset - d ..= offset + d] as it was at the start
    // of round d, so a backtrack at round dd reads index (k + dd).
    let mut trace: Vec<Vec<isize>> = Vec::new();
    for d in 0..=max.min(max_d) {
        trace.push(v[(offset - d as isize) as usize..=(offset + d as isize) as usize].to_vec());
        let di = d as isize;
        let mut k = -di;
        while k <= di {
            let idx = (k + offset) as usize;
            let mut x = if k == -di || (k != di && v[idx - 1] < v[idx + 1]) {
                v[idx + 1]
            } else {
                v[idx - 1] + 1
            };
            let mut y = x - k;
            while (x as usize) < n && (y as usize) < m && a[x as usize] == b[y as usize] {
                x += 1;
                y += 1;
            }
            v[idx] = x;
            if x as usize >= n && y as usize >= m {
                // backtrack
                let mut pairs = Vec::new();
                let mut px = n as isize;
                let mut py = m as isize;
                for dd in (0..=d).rev() {
                    let vv = &trace[dd];
                    let ddi = dd as isize;
                    // the window is indexed by k + dd; k - 1 and k + 1 can
                    // fall outside it only where the branch never reads them
                    let at = |k: isize| -> isize {
                        let i = k + ddi;
                        if i < 0 || i as usize >= vv.len() {
                            0
                        } else {
                            vv[i as usize]
                        }
                    };
                    let kk = px - py;
                    let prev_k = if kk == -ddi || (kk != ddi && at(kk - 1) < at(kk + 1)) {
                        kk + 1
                    } else {
                        kk - 1
                    };
                    let prev_x = at(prev_k);
                    let prev_y = prev_x - prev_k;
                    while px > prev_x && py > prev_y {
                        px -= 1;
                        py -= 1;
                        pairs.push((px as usize, py as usize));
                    }
                    px = prev_x;
                    py = prev_y;
                }
                pairs.reverse();
                return Some(pairs);
            }
            k += 2;
        }
    }
    None
}

/// The edits that turn `old` into `new`, one per changed run of lines.
pub fn diff(old: &[u8], new: &[u8]) -> Vec<TextEdit> {
    if old == new {
        return Vec::new();
    }
    let oa = line_starts(old);
    let nb = line_starts(new);
    let ha = hashes(old, &oa);
    let hb = hashes(new, &nb);
    let n = ha.len();
    let m = hb.len();
    let bound = 2048;
    let pairs = match myers(&ha, &hb, bound) {
        Some(p) => p,
        // Too different to diff cheaply: one edit for the whole buffer.
        None => {
            return vec![TextEdit {
                start: 0,
                end: old.len() as u32,
                new_text: new.to_vec(),
            }];
        }
    };
    let mut edits = Vec::new();
    let mut ai = 0usize;
    let mut bi = 0usize;
    let flush = |ai: usize, aj: usize, bi: usize, bj: usize, edits: &mut Vec<TextEdit>| {
        if ai == aj && bi == bj {
            return;
        }
        let start = oa[ai];
        let end = oa[aj];
        let text = new[nb[bi]..nb[bj]].to_vec();
        edits.push(TextEdit {
            start: start as u32,
            end: end as u32,
            new_text: text,
        });
    };
    for (x, y) in pairs {
        flush(ai, x, bi, y, &mut edits);
        ai = x + 1;
        bi = y + 1;
    }
    flush(ai, n, bi, m, &mut edits);
    edits
}

/// A unified-diff-style rendering for a CI gate's output.
pub fn render_diff(old: &[u8], new: &[u8], path: &str) -> String {
    let edits = diff(old, new);
    if edits.is_empty() {
        return String::new();
    }
    let starts = line_starts(old);
    let mut out = format!("--- {path}\n+++ {path} (formatted)\n");
    for e in &edits {
        let line = starts.partition_point(|&s| s <= e.start as usize);
        out.push_str(&format!("@@ line {line} @@\n"));
        for l in String::from_utf8_lossy(&old[e.start as usize..e.end as usize]).lines() {
            out.push('-');
            out.push_str(l);
            out.push('\n');
        }
        for l in String::from_utf8_lossy(&e.new_text).lines() {
            out.push('+');
            out.push_str(l);
            out.push('\n');
        }
    }
    out
}
