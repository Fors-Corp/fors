use std::env;

fn eval_a(i: i64, j: i64) -> f64 {
    let ij = i + j;
    1.0 / ((ij * (ij + 1)) / 2 + i + 1) as f64
}

fn eval_a_times_u(n: i64, u: &[f64], au: &mut [f64]) {
    for i in 0..n {
        let mut sum = 0.0;
        for j in 0..n {
            sum += eval_a(i, j) * u[j as usize];
        }
        au[i as usize] = sum;
    }
}

fn eval_at_times_u(n: i64, u: &[f64], au: &mut [f64]) {
    for i in 0..n {
        let mut sum = 0.0;
        for j in 0..n {
            sum += eval_a(j, i) * u[j as usize];
        }
        au[i as usize] = sum;
    }
}

fn eval_ata_times_u(n: i64, u: &[f64], at_au: &mut [f64], tmp: &mut [f64]) {
    eval_a_times_u(n, u, tmp);
    eval_at_times_u(n, tmp, at_au);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: i64 = args[1].parse().unwrap();
    let n_usize = n as usize;

    let mut u = vec![1.0f64; n_usize];
    let mut v = vec![0.0f64; n_usize];
    let mut tmp = vec![0.0f64; n_usize];

    for _ in 0..10 {
        eval_ata_times_u(n, &u, &mut v, &mut tmp);
        eval_ata_times_u(n, &v, &mut u, &mut tmp);
    }

    let mut v_bv = 0.0;
    let mut vv = 0.0;
    for i in 0..n_usize {
        v_bv += u[i] * v[i];
        vv += v[i] * v[i];
    }

    println!("{:.9}", (v_bv / vv).sqrt());
}
