use std::env;
use std::thread;

fn count_rows(n: i64, row_start: i64, row_end: i64) -> i64 {
    let mut count: i64 = 0;
    for py in row_start..row_end {
        let ci0 = 2.0 * py as f64 / n as f64 - 1.0;
        for px in 0..n {
            let cr = 2.0 * px as f64 / n as f64 - 1.5;
            let mut zr = 0.0f64;
            let mut zi = 0.0f64;
            let mut iter = 0;
            while iter < 50 && zr * zr + zi * zi <= 4.0 {
                let tr = zr * zr - zi * zi + cr;
                let ti = 2.0 * zr * zi + ci0;
                zr = tr;
                zi = ti;
                iter += 1;
            }
            if iter == 50 {
                count += 1;
            }
        }
    }
    count
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: i64 = args[1].parse().unwrap();
    let num_threads: i64 = args[2].parse().unwrap();
    let num_threads = if num_threads < 1 { 1 } else { num_threads };

    let total: i64 = thread::scope(|s| {
        let mut handles = Vec::new();
        for t in 0..num_threads {
            let row_start = n * t / num_threads;
            let row_end = n * (t + 1) / num_threads;
            handles.push(s.spawn(move || count_rows(n, row_start, row_end)));
        }
        handles.into_iter().map(|h| h.join().unwrap()).sum()
    });

    println!("{}", total);
}
