use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    let n: usize = args[1].parse().unwrap();

    let mut perm: Vec<i32> = vec![0; n];
    let mut perm1: Vec<i32> = (0..n as i32).collect();
    let mut count: Vec<i32> = vec![0; n];

    let mut r = n;
    let mut checksum: i64 = 0;
    let mut maxflips: i32 = 0;
    let mut sign: i64 = 1;

    loop {
        while r != 1 {
            count[r - 1] = r as i32;
            r -= 1;
        }
        perm.copy_from_slice(&perm1);

        let mut flips = 0;
        loop {
            let k = perm[0];
            if k == 0 {
                break;
            }
            let k = k as usize;
            let k2 = (k + 1) >> 1;
            for i in 0..k2 {
                perm.swap(i, k - i);
            }
            flips += 1;
        }

        checksum += sign * flips as i64;
        if flips > maxflips {
            maxflips = flips;
        }

        let mut done = false;
        loop {
            if r == n {
                done = true;
                break;
            }
            let perm0 = perm1[0];
            for i in 0..r {
                perm1[i] = perm1[i + 1];
            }
            perm1[r] = perm0;
            count[r] -= 1;
            if count[r] > 0 {
                break;
            }
            r += 1;
        }
        if done {
            break;
        }
        sign = -sign;
    }

    println!("{}", checksum);
    println!("Pfannkuchen({}) = {}", n, maxflips);
}
