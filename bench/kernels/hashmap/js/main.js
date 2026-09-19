const args = process.argv.slice(2);
const n = Number(args[0]);

const countsInt = new Map();
const countsStr = new Map();

let x = 42;
const mod1 = Math.floor(n / 4) + 1;
for (let i = 0; i < n; i++) {
  x = (x * 48271) % 2147483647;
  const key = x % mod1;
  countsInt.set(key, (countsInt.get(key) || 0) + 1);
}

const n2 = Math.floor(n / 4);
const mod2 = Math.floor(n / 16) + 1;
for (let i = 0; i < n2; i++) {
  x = (x * 48271) % 2147483647;
  const num = x % mod2;
  const key = "k" + num;
  countsStr.set(key, (countsStr.get(key) || 0) + 1);
}

const MOD = 1000000007n;
let checksum = 0n;
for (const [k, c] of countsInt) {
  checksum = (checksum + (BigInt(k) % MOD) * (BigInt(c) % MOD)) % MOD;
}
for (const [k, c] of countsStr) {
  const num = BigInt(k.slice(1));
  checksum = (checksum + (num % MOD) * (BigInt(c) % MOD)) % MOD;
}

console.log(countsInt.size);
console.log(countsStr.size);
console.log(checksum.toString());
