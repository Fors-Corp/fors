import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { fileURLToPath } from "node:url";

function computeBlock(r, a, b, c, start, end) {
    const s = 3.0;
    for (let i = start; i < end; i++) {
        b[i] = (i % 7) + 1;
        c[i] = (i % 5) + 1;
        a[i] = 0.0;
    }
    for (let rep = 0; rep < r; rep++) {
        for (let i = start; i < end; i++) {
            a[i] = b[i] + s * c[i];
        }
    }
}

function blockBounds(n, threads) {
    const base = Math.floor(n / threads);
    const rem = n % threads;
    const bounds = new Array(threads + 1);
    let idx = 0;
    bounds[0] = 0;
    for (let t = 0; t < threads; t++) {
        const count = base + (t < rem ? 1 : 0);
        idx += count;
        bounds[t + 1] = idx;
    }
    return bounds;
}

async function main() {
    const args = process.argv.slice(2);
    const n = parseInt(args[0], 10);
    const r = parseInt(args[1], 10);
    let threads = parseInt(args[2], 10);
    if (!(threads >= 1)) threads = 1;
    if (threads > n) threads = n;

    const sabA = new SharedArrayBuffer(n * 8);
    const sabB = new SharedArrayBuffer(n * 8);
    const sabC = new SharedArrayBuffer(n * 8);
    const a = new Float64Array(sabA);

    const bounds = blockBounds(n, threads);
    const selfPath = fileURLToPath(import.meta.url);

    const workers = [];
    for (let t = 0; t < threads; t++) {
        const start = bounds[t];
        const end = bounds[t + 1];
        workers.push(
            new Promise((resolve, reject) => {
                const w = new Worker(selfPath, {
                    workerData: { r, sabA, sabB, sabC, start, end },
                });
                w.on("message", () => resolve());
                w.on("error", reject);
                w.on("exit", (code) => {
                    if (code !== 0) reject(new Error(`worker exited ${code}`));
                });
            })
        );
    }
    await Promise.all(workers);

    let sum = 0.0;
    for (let i = 0; i < n; i++) sum += a[i];
    console.log(sum.toFixed(0));
}

if (isMainThread) {
    main();
} else {
    const { r, sabA, sabB, sabC, start, end } = workerData;
    const a = new Float64Array(sabA);
    const b = new Float64Array(sabB);
    const c = new Float64Array(sabC);
    computeBlock(r, a, b, c, start, end);
    parentPort.postMessage("done");
}
