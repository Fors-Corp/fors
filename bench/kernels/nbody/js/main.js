const N_BODIES = 5;
const SOLAR_MASS = 4.0 * Math.PI * Math.PI;
const DAYS_PER_YEAR = 365.24;

function initialBodies() {
    return {
        x: [0.0, 4.84143144246472090e+00, 8.34336671824457987e+00, 1.28943695621391310e+01, 1.53796971148509165e+01],
        y: [0.0, -1.16032004402742839e+00, 4.12479856412430479e+00, -1.51111514016986312e+01, -2.59193146099879641e+01],
        z: [0.0, -1.03622044471123109e-01, -4.03523417114321381e-01, -2.23307578892655734e-01, 1.79258772950371181e-01],
        vx: [
            0.0,
            1.66007664274403694e-03 * DAYS_PER_YEAR,
            -2.76742510726862411e-03 * DAYS_PER_YEAR,
            2.96460137564761618e-03 * DAYS_PER_YEAR,
            2.68067772490389322e-03 * DAYS_PER_YEAR,
        ],
        vy: [
            0.0,
            7.69901118419740425e-03 * DAYS_PER_YEAR,
            4.99852801234917238e-03 * DAYS_PER_YEAR,
            2.37847173959480950e-03 * DAYS_PER_YEAR,
            1.62824170038242295e-03 * DAYS_PER_YEAR,
        ],
        vz: [
            0.0,
            -6.90460016972063023e-05 * DAYS_PER_YEAR,
            2.30417297573763929e-05 * DAYS_PER_YEAR,
            -2.96589568540237556e-05 * DAYS_PER_YEAR,
            -9.51592254519715870e-05 * DAYS_PER_YEAR,
        ],
        mass: [
            SOLAR_MASS,
            9.54791938424326609e-04 * SOLAR_MASS,
            2.85885980666130812e-04 * SOLAR_MASS,
            4.36624404335156298e-05 * SOLAR_MASS,
            5.15138902046611451e-05 * SOLAR_MASS,
        ],
    };
}

function offsetMomentum(b) {
    let px = 0.0, py = 0.0, pz = 0.0;
    for (let i = 0; i < N_BODIES; i++) {
        px += b.vx[i] * b.mass[i];
        py += b.vy[i] * b.mass[i];
        pz += b.vz[i] * b.mass[i];
    }
    b.vx[0] = -px / SOLAR_MASS;
    b.vy[0] = -py / SOLAR_MASS;
    b.vz[0] = -pz / SOLAR_MASS;
}

function energy(b) {
    let e = 0.0;
    for (let i = 0; i < N_BODIES; i++) {
        e += 0.5 * b.mass[i] * (b.vx[i] * b.vx[i] + b.vy[i] * b.vy[i] + b.vz[i] * b.vz[i]);
        for (let j = i + 1; j < N_BODIES; j++) {
            const dx = b.x[i] - b.x[j];
            const dy = b.y[i] - b.y[j];
            const dz = b.z[i] - b.z[j];
            const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);
            e -= (b.mass[i] * b.mass[j]) / dist;
        }
    }
    return e;
}

function advance(b, dt) {
    for (let i = 0; i < N_BODIES; i++) {
        for (let j = i + 1; j < N_BODIES; j++) {
            const dx = b.x[i] - b.x[j];
            const dy = b.y[i] - b.y[j];
            const dz = b.z[i] - b.z[j];
            const d2 = dx * dx + dy * dy + dz * dz;
            const mag = dt / (d2 * Math.sqrt(d2));

            b.vx[i] -= dx * b.mass[j] * mag;
            b.vy[i] -= dy * b.mass[j] * mag;
            b.vz[i] -= dz * b.mass[j] * mag;

            b.vx[j] += dx * b.mass[i] * mag;
            b.vy[j] += dy * b.mass[i] * mag;
            b.vz[j] += dz * b.mass[i] * mag;
        }
    }
    for (let i = 0; i < N_BODIES; i++) {
        b.x[i] += dt * b.vx[i];
        b.y[i] += dt * b.vy[i];
        b.z[i] += dt * b.vz[i];
    }
}

function fmt9(v) {
    return v.toFixed(9);
}

function main() {
    const args = process.argv.slice(2);
    if (args.length < 1) {
        console.error("usage: main.js <steps>");
        process.exit(1);
    }
    const steps = parseInt(args[0], 10);

    const bodies = initialBodies();
    offsetMomentum(bodies);
    console.log(fmt9(energy(bodies)));
    for (let i = 0; i < steps; i++) {
        advance(bodies, 0.01);
    }
    console.log(fmt9(energy(bodies)));
}

main();
