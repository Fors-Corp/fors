use std::collections::HashMap;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: i64 = args[1].parse().unwrap();

    let mut counts_int: HashMap<i64, i64> = HashMap::new();
    let mut counts_str: HashMap<String, i64> = HashMap::new();

    let mut x: u64 = 42;
    let mod1: i64 = n / 4 + 1;
    for _ in 0..n {
        x = (x * 48271) % 2147483647;
        let key = (x % (mod1 as u64)) as i64;
        *counts_int.entry(key).or_insert(0) += 1;
    }

    let n2 = n / 4;
    let mod2: i64 = n / 16 + 1;
    for _ in 0..n2 {
        x = (x * 48271) % 2147483647;
        let num = (x % (mod2 as u64)) as i64;
        let key = format!("k{}", num);
        *counts_str.entry(key).or_insert(0) += 1;
    }

    const MODULO: i64 = 1_000_000_007;
    let mut checksum: i64 = 0;
    for (k, c) in &counts_int {
        checksum = (checksum + (*k % MODULO) * (*c % MODULO)) % MODULO;
    }
    for (k, c) in &counts_str {
        let num: i64 = k[1..].parse().unwrap();
        checksum = (checksum + (num % MODULO) * (*c % MODULO)) % MODULO;
    }

    println!("{}", counts_int.len());
    println!("{}", counts_str.len());
    println!("{}", checksum);
}
