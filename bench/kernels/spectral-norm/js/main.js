function evalA(i, j) {
    const ij = i + j;
    return 1.0 / (((ij * (ij + 1)) / 2 + i + 1));
}

function evalATimesU(n, u, au) {
    for (let i = 0; i < n; i++) {
        let sum = 0.0;
        for (let j = 0; j < n; j++) {
            sum += evalA(i, j) * u[j];
        }
        au[i] = sum;
    }
}

function evalAtTimesU(n, u, au) {
    for (let i = 0; i < n; i++) {
        let sum = 0.0;
        for (let j = 0; j < n; j++) {
            sum += evalA(j, i) * u[j];
        }
        au[i] = sum;
    }
}

function evalAtATimesU(n, u, atAu, tmp) {
    evalATimesU(n, u, tmp);
    evalAtTimesU(n, tmp, atAu);
}

function main() {
    const args = process.argv.slice(2);
    const n = parseInt(args[0], 10);

    let u = new Float64Array(n).fill(1.0);
    let v = new Float64Array(n);
    let tmp = new Float64Array(n);

    for (let i = 0; i < 10; i++) {
        evalAtATimesU(n, u, v, tmp);
        evalAtATimesU(n, v, u, tmp);
    }

    let vBv = 0.0;
    let vv = 0.0;
    for (let i = 0; i < n; i++) {
        vBv += u[i] * v[i];
        vv += v[i] * v[i];
    }

    console.log((Math.sqrt(vBv / vv)).toFixed(9));
}

main();
