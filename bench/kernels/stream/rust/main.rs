use std::env;
use std::thread;

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let r: u64 = args[2].parse().unwrap();
    let mut threads: usize = args[3].parse().unwrap();
    if threads < 1 {
        threads = 1;
    }
    if threads > n {
        threads = n;
    }

    let mut a = vec![0.0f64; n];
    let mut b = vec![0.0f64; n];
    let mut c = vec![0.0f64; n];
    let s: f64 = 3.0;

    let base = n / threads;
    let rem = n % threads;
    let mut bounds = Vec::with_capacity(threads + 1);
    let mut idx = 0usize;
    bounds.push(idx);
    for t in 0..threads {
        let count = base + if t < rem { 1 } else { 0 };
        idx += count;
        bounds.push(idx);
    }

    {
        let mut a_rem = &mut a[..];
        let mut b_rem = &mut b[..];
        let mut c_rem = &mut c[..];
        thread::scope(|sc| {
            for t in 0..threads {
                let start = bounds[t];
                let end = bounds[t + 1];
                let len = end - start;
                let (a_chunk, a_rest) = a_rem.split_at_mut(len);
                a_rem = a_rest;
                let (b_chunk, b_rest) = b_rem.split_at_mut(len);
                b_rem = b_rest;
                let (c_chunk, c_rest) = c_rem.split_at_mut(len);
                c_rem = c_rest;
                sc.spawn(move || {
                    // First-touch: this thread initialises its own block of all three arrays.
                    // Block slices (not indexing into the full array) mean the bounds check
                    // for each of a/b/c happens once, at slice-construction time, not per element.
                    for (i, (bv, cv)) in b_chunk.iter_mut().zip(c_chunk.iter_mut()).enumerate() {
                        *bv = ((start + i) % 7 + 1) as f64;
                        *cv = ((start + i) % 5 + 1) as f64;
                    }
                    for av in a_chunk.iter_mut() {
                        *av = 0.0;
                    }
                    for _ in 0..r {
                        for ((av, bv), cv) in
                            a_chunk.iter_mut().zip(b_chunk.iter()).zip(c_chunk.iter())
                        {
                            *av = *bv + s * *cv;
                        }
                    }
                });
            }
        });
    }

    let sum: f64 = a.iter().sum();
    println!("{:.0}", sum);
}
