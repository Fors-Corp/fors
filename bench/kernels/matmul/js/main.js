import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { fileURLToPath } from "node:url";

function buildMatrices(n) {
    const a = new Float64Array(n * n);
    const b = new Float64Array(n * n);
    for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
            a[i * n + j] = ((i * j) % 7) + 1;
            b[i * n + j] = ((i + j) % 5) + 1;
        }
    }
    return { a, b };
}

function computeBlock(n, a, b, c, rowStart, rowEnd) {
    for (let i = rowStart; i < rowEnd; i++) {
        for (let j = 0; j < n; j++) {
            c[i * n + j] = 0.0;
        }
        for (let k = 0; k < n; k++) {
            const av = a[i * n + k];
            for (let j = 0; j < n; j++) {
                c[i * n + j] += av * b[k * n + j];
            }
        }
    }
}

function rowBounds(n, threads) {
    const base = Math.floor(n / threads);
    const rem = n % threads;
    const bounds = new Array(threads + 1);
    let row = 0;
    bounds[0] = 0;
    for (let t = 0; t < threads; t++) {
        const count = base + (t < rem ? 1 : 0);
        row += count;
        bounds[t + 1] = row;
    }
    return bounds;
}

async function main() {
    const args = process.argv.slice(2);
    const n = parseInt(args[0], 10);
    let threads = parseInt(args[1], 10);
    if (!(threads >= 1)) threads = 1;
    if (threads > n) threads = n;

    const { a, b } = buildMatrices(n);
    const sab = new SharedArrayBuffer(n * n * 8);
    const c = new Float64Array(sab);

    const bounds = rowBounds(n, threads);
    const selfPath = fileURLToPath(import.meta.url);

    const workers = [];
    for (let t = 0; t < threads; t++) {
        const rowStart = bounds[t];
        const rowEnd = bounds[t + 1];
        workers.push(
            new Promise((resolve, reject) => {
                const w = new Worker(selfPath, {
                    workerData: { n, a, b, sab, rowStart, rowEnd },
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
    let trace = 0.0;
    for (let i = 0; i < n; i++) {
        for (let j = 0; j < n; j++) {
            sum += c[i * n + j];
        }
        trace += c[i * n + i];
    }

    console.log(sum.toFixed(0));
    console.log(trace.toFixed(0));
}

if (isMainThread) {
    main();
} else {
    const { n, a, b, sab, rowStart, rowEnd } = workerData;
    const c = new Float64Array(sab);
    computeBlock(n, a, b, c, rowStart, rowEnd);
    parentPort.postMessage("done");
}
