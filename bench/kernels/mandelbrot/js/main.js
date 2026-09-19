import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { fileURLToPath } from "node:url";

function countRows(n, rowStart, rowEnd) {
    let count = 0;
    for (let py = rowStart; py < rowEnd; py++) {
        const ci0 = (2.0 * py) / n - 1.0;
        for (let px = 0; px < n; px++) {
            const cr = (2.0 * px) / n - 1.5;
            let zr = 0.0;
            let zi = 0.0;
            let iter = 0;
            while (iter < 50 && zr * zr + zi * zi <= 4.0) {
                const tr = zr * zr - zi * zi + cr;
                const ti = 2.0 * zr * zi + ci0;
                zr = tr;
                zi = ti;
                iter++;
            }
            if (iter === 50) {
                count++;
            }
        }
    }
    return count;
}

if (isMainThread) {
    const n = parseInt(process.argv.slice(2)[0], 10);
    let numThreads = parseInt(process.argv.slice(2)[1], 10);
    if (numThreads < 1) numThreads = 1;

    const selfPath = fileURLToPath(import.meta.url);
    const results = new Array(numThreads).fill(0);
    let remaining = numThreads;

    await new Promise((resolve, reject) => {
        for (let t = 0; t < numThreads; t++) {
            const rowStart = Math.floor((n * t) / numThreads);
            const rowEnd = Math.floor((n * (t + 1)) / numThreads);
            const worker = new Worker(selfPath, {
                workerData: { n, rowStart, rowEnd },
            });
            worker.on("message", (msg) => {
                results[t] = msg;
                remaining--;
                if (remaining === 0) resolve();
            });
            worker.on("error", reject);
        }
    });
    const total = results.reduce((a, b) => a + b, 0);
    console.log(String(total));
} else {
    const { n, rowStart, rowEnd } = workerData;
    const count = countRows(n, rowStart, rowEnd);
    parentPort.postMessage(count);
}
