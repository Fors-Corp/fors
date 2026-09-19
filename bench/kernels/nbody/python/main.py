import sys
import math

N_BODIES = 5
SOLAR_MASS = 4.0 * math.pi * math.pi
DAYS_PER_YEAR = 365.24


def initial_bodies():
    x = [0.0, 4.84143144246472090e+00, 8.34336671824457987e+00,
         1.28943695621391310e+01, 1.53796971148509165e+01]
    y = [0.0, -1.16032004402742839e+00, 4.12479856412430479e+00,
         -1.51111514016986312e+01, -2.59193146099879641e+01]
    z = [0.0, -1.03622044471123109e-01, -4.03523417114321381e-01,
         -2.23307578892655734e-01, 1.79258772950371181e-01]
    vx = [0.0,
          1.66007664274403694e-03 * DAYS_PER_YEAR,
          -2.76742510726862411e-03 * DAYS_PER_YEAR,
          2.96460137564761618e-03 * DAYS_PER_YEAR,
          2.68067772490389322e-03 * DAYS_PER_YEAR]
    vy = [0.0,
          7.69901118419740425e-03 * DAYS_PER_YEAR,
          4.99852801234917238e-03 * DAYS_PER_YEAR,
          2.37847173959480950e-03 * DAYS_PER_YEAR,
          1.62824170038242295e-03 * DAYS_PER_YEAR]
    vz = [0.0,
          -6.90460016972063023e-05 * DAYS_PER_YEAR,
          2.30417297573763929e-05 * DAYS_PER_YEAR,
          -2.96589568540237556e-05 * DAYS_PER_YEAR,
          -9.51592254519715870e-05 * DAYS_PER_YEAR]
    mass = [SOLAR_MASS,
            9.54791938424326609e-04 * SOLAR_MASS,
            2.85885980666130812e-04 * SOLAR_MASS,
            4.36624404335156298e-05 * SOLAR_MASS,
            5.15138902046611451e-05 * SOLAR_MASS]
    return x, y, z, vx, vy, vz, mass


def offset_momentum(vx, vy, vz, mass):
    px = py = pz = 0.0
    for i in range(N_BODIES):
        px += vx[i] * mass[i]
        py += vy[i] * mass[i]
        pz += vz[i] * mass[i]
    vx[0] = -px / SOLAR_MASS
    vy[0] = -py / SOLAR_MASS
    vz[0] = -pz / SOLAR_MASS


def energy(x, y, z, vx, vy, vz, mass):
    e = 0.0
    for i in range(N_BODIES):
        e += 0.5 * mass[i] * (vx[i] * vx[i] + vy[i] * vy[i] + vz[i] * vz[i])
        for j in range(i + 1, N_BODIES):
            dx = x[i] - x[j]
            dy = y[i] - y[j]
            dz = z[i] - z[j]
            dist = math.sqrt(dx * dx + dy * dy + dz * dz)
            e -= (mass[i] * mass[j]) / dist
    return e


def advance(x, y, z, vx, vy, vz, mass, dt):
    for i in range(N_BODIES):
        for j in range(i + 1, N_BODIES):
            dx = x[i] - x[j]
            dy = y[i] - y[j]
            dz = z[i] - z[j]
            d2 = dx * dx + dy * dy + dz * dz
            mag = dt / (d2 * math.sqrt(d2))

            mj = mass[j]
            vx[i] -= dx * mj * mag
            vy[i] -= dy * mj * mag
            vz[i] -= dz * mj * mag

            mi = mass[i]
            vx[j] += dx * mi * mag
            vy[j] += dy * mi * mag
            vz[j] += dz * mi * mag

    for i in range(N_BODIES):
        x[i] += dt * vx[i]
        y[i] += dt * vy[i]
        z[i] += dt * vz[i]


def main():
    if len(sys.argv) < 2:
        print("usage: main.py <steps>", file=sys.stderr)
        sys.exit(1)
    steps = int(sys.argv[1])

    x, y, z, vx, vy, vz, mass = initial_bodies()
    offset_momentum(vx, vy, vz, mass)
    print(f"{energy(x, y, z, vx, vy, vz, mass):.9f}")
    for _ in range(steps):
        advance(x, y, z, vx, vy, vz, mass, 0.01)
    print(f"{energy(x, y, z, vx, vy, vz, mass):.9f}")


if __name__ == "__main__":
    main()
