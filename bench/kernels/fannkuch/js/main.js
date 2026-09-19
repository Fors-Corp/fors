const n = parseInt(process.argv[2], 10);

const perm = new Int32Array(n);
const perm1 = new Int32Array(n);
const count = new Int32Array(n);
for (let i = 0; i < n; i++) perm1[i] = i;

let r = n;
let checksum = 0;
let maxflips = 0;
let sign = 1;

for (;;) {
    while (r !== 1) {
        count[r - 1] = r;
        r--;
    }
    perm.set(perm1);

    let flips = 0;
    for (;;) {
        const k = perm[0];
        if (k === 0) break;
        const k2 = (k + 1) >> 1;
        for (let i = 0; i < k2; i++) {
            const t = perm[i];
            perm[i] = perm[k - i];
            perm[k - i] = t;
        }
        flips++;
    }

    checksum += sign * flips;
    if (flips > maxflips) maxflips = flips;

    let done = false;
    for (;;) {
        if (r === n) {
            done = true;
            break;
        }
        const perm0 = perm1[0];
        for (let i = 0; i < r; i++) perm1[i] = perm1[i + 1];
        perm1[r] = perm0;
        count[r]--;
        if (count[r] > 0) break;
        r++;
    }
    if (done) break;
    sign = -sign;
}

console.log(String(checksum));
console.log(`Pfannkuchen(${n}) = ${maxflips}`);
