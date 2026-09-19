import { Worker, isMainThread, parentPort, workerData } from "node:worker_threads";
import { fileURLToPath } from "node:url";

function lowbias32(x) {
    x ^= x >>> 16;
    x = Math.imul(x, 0x7feb352d) >>> 0;
    x ^= x >>> 15;
    x = Math.imul(x, 0x846ca68b) >>> 0;
    x ^= x >>> 16;
    return x >>> 0;
}

function partialSum(start, end) {
    let sum = 0;
    for (let i = start; i < end; i++) {
        let x = i >>> 0;
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        sum += x % 1000;
    }
    return sum;
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
            const start = Math.floor((n * t) / numThreads);
            const end = Math.floor((n * (t + 1)) / numThreads);
            const worker = new Worker(selfPath, {
                workerData: { start, end },
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
    const { start, end } = workerData;
    const sum = partialSum(start, end);
    parentPort.postMessage(sum);
}
