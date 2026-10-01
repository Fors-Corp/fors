use std::env;
use std::thread;

// Tuned axis vs naive matmul: cache blocking (kk/ii/jj tiles, i-k-j inside).
// Same BLOCK = 64 in every language.
const BLOCK: usize = 64;

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let mut threads: usize = args[2].parse().unwrap();
    if threads < 1 {
        threads = 1;
    }
    if threads > n {
        threads = n;
    }

    let mut a = vec![0.0f64; n * n];
    let mut b = vec![0.0f64; n * n];
    for i in 0..n {
        for j in 0..n {
            a[i * n + j] = (((i * j) % 7) + 1) as f64;
            b[i * n + j] = (((i + j) % 5) + 1) as f64;
        }
    }

    let mut c = vec![0.0f64; n * n];

    let base = n / threads;
    let rem = n % threads;
    let mut bounds = Vec::with_capacity(threads + 1);
    let mut row = 0usize;
    bounds.push(row);
    for t in 0..threads {
        let count = base + if t < rem { 1 } else { 0 };
        row += count;
        bounds.push(row);
    }

    {
        let a_ref = &a;
        let b_ref = &b;
        let mut remaining = &mut c[..];
        thread::scope(|s| {
            for t in 0..threads {
                let row_start = bounds[t];
                let row_end = bounds[t + 1];
                let rows_here = row_end - row_start;
                let (chunk, rest) = remaining.split_at_mut(rows_here * n);
                remaining = rest;
                s.spawn(move || {
                    for i in 0..rows_here {
                        // Row slices + zip: one bounds check per row instead of per element,
                        // which is what lets safe Rust vectorize this loop like C does.
                        chunk[i * n..(i + 1) * n].fill(0.0);
                    }
                    let mut kk = 0;
                    while kk < n {
                        let k_end = (kk + BLOCK).min(n);
                        let mut ii = row_start;
                        while ii < row_end {
                            let i_end = (ii + BLOCK).min(row_end);
                            let mut jj = 0;
                            while jj < n {
                                let j_end = (jj + BLOCK).min(n);
                                for i in ii..i_end {
                                    let c_row = &mut chunk[(i - row_start) * n..(i - row_start + 1) * n];
                                    let c_tile = &mut c_row[jj..j_end];
                                    for k in kk..k_end {
                                        let av = a_ref[i * n + k];
                                        let b_row = &b_ref[k * n..(k + 1) * n];
                                        let b_tile = &b_row[jj..j_end];
                                        for (c, &bv) in c_tile.iter_mut().zip(b_tile) {
                                            *c += av * bv;
                                        }
                                    }
                                }
                                jj += BLOCK;
                            }
                            ii += BLOCK;
                        }
                        kk += BLOCK;
                    }
                });
            }
        });
    }

    let mut sum = 0.0f64;
    let mut trace = 0.0f64;
    for i in 0..n {
        for j in 0..n {
            sum += c[i * n + j];
        }
        trace += c[i * n + i];
    }

    println!("{:.0}", sum);
    println!("{:.0}", trace);
}
