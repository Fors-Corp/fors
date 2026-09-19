use std::env;
use std::thread;

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
                        let global_i = row_start + i;
                        // Row slices + zip: one bounds check per row instead of per element,
                        // which is what lets safe Rust vectorize this loop like C does.
                        let c_row = &mut chunk[i * n..(i + 1) * n];
                        c_row.fill(0.0);
                        for k in 0..n {
                            let av = a_ref[global_i * n + k];
                            let b_row = &b_ref[k * n..(k + 1) * n];
                            for (c, &bv) in c_row.iter_mut().zip(b_row) {
                                *c += av * bv;
                            }
                        }
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
