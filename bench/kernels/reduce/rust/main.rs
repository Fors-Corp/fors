use std::env;
use std::thread;

fn lowbias32(mut x: u32) -> u32 {
    x ^= x >> 16;
    x = x.wrapping_mul(0x7feb352d);
    x ^= x >> 15;
    x = x.wrapping_mul(0x846ca68b);
    x ^= x >> 16;
    x
}

fn partial_sum(start: i64, end: i64) -> u64 {
    let mut sum: u64 = 0;
    for i in start..end {
        let mut x = i as u32;
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        sum += (x % 1000) as u64;
    }
    sum
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: i64 = args[1].parse().unwrap();
    let num_threads: i64 = args[2].parse().unwrap();
    let num_threads = if num_threads < 1 { 1 } else { num_threads };

    let total: u64 = thread::scope(|s| {
        let mut handles = Vec::new();
        for t in 0..num_threads {
            let start = n * t / num_threads;
            let end = n * (t + 1) / num_threads;
            handles.push(s.spawn(move || partial_sum(start, end)));
        }
        handles.into_iter().map(|h| h.join().unwrap()).sum()
    });

    println!("{}", total);
}
