import Foundation

let nBodies = 5
let solarMass = 4.0 * Double.pi * Double.pi
let daysPerYear = 365.24

struct Body {
    var x: Double
    var y: Double
    var z: Double
    var vx: Double
    var vy: Double
    var vz: Double
    var mass: Double
}

func initialBodies() -> [Body] {
    return [
        Body(x: 0.0, y: 0.0, z: 0.0, vx: 0.0, vy: 0.0, vz: 0.0, mass: solarMass),
        Body(x: 4.84143144246472090e+00,
             y: -1.16032004402742839e+00,
             z: -1.03622044471123109e-01,
             vx: 1.66007664274403694e-03 * daysPerYear,
             vy: 7.69901118419740425e-03 * daysPerYear,
             vz: -6.90460016972063023e-05 * daysPerYear,
             mass: 9.54791938424326609e-04 * solarMass),
        Body(x: 8.34336671824457987e+00,
             y: 4.12479856412430479e+00,
             z: -4.03523417114321381e-01,
             vx: -2.76742510726862411e-03 * daysPerYear,
             vy: 4.99852801234917238e-03 * daysPerYear,
             vz: 2.30417297573763929e-05 * daysPerYear,
             mass: 2.85885980666130812e-04 * solarMass),
        Body(x: 1.28943695621391310e+01,
             y: -1.51111514016986312e+01,
             z: -2.23307578892655734e-01,
             vx: 2.96460137564761618e-03 * daysPerYear,
             vy: 2.37847173959480950e-03 * daysPerYear,
             vz: -2.96589568540237556e-05 * daysPerYear,
             mass: 4.36624404335156298e-05 * solarMass),
        Body(x: 1.53796971148509165e+01,
             y: -2.59193146099879641e+01,
             z: 1.79258772950371181e-01,
             vx: 2.68067772490389322e-03 * daysPerYear,
             vy: 1.62824170038242295e-03 * daysPerYear,
             vz: -9.51592254519715870e-05 * daysPerYear,
             mass: 5.15138902046611451e-05 * solarMass),
    ]
}

func offsetMomentum(_ bodies: inout [Body]) {
    var px = 0.0, py = 0.0, pz = 0.0
    for b in bodies {
        px += b.vx * b.mass
        py += b.vy * b.mass
        pz += b.vz * b.mass
    }
    bodies[0].vx = -px / solarMass
    bodies[0].vy = -py / solarMass
    bodies[0].vz = -pz / solarMass
}

func energy(_ bodies: [Body]) -> Double {
    var e = 0.0
    for i in 0..<nBodies {
        let bi = bodies[i]
        e += 0.5 * bi.mass * (bi.vx * bi.vx + bi.vy * bi.vy + bi.vz * bi.vz)
        for j in (i + 1)..<nBodies {
            let bj = bodies[j]
            let dx = bi.x - bj.x
            let dy = bi.y - bj.y
            let dz = bi.z - bj.z
            let dist = (dx * dx + dy * dy + dz * dz).squareRoot()
            e -= (bi.mass * bj.mass) / dist
        }
    }
    return e
}

func advance(_ bodies: inout [Body], _ dt: Double) {
    for i in 0..<nBodies {
        for j in (i + 1)..<nBodies {
            let dx = bodies[i].x - bodies[j].x
            let dy = bodies[i].y - bodies[j].y
            let dz = bodies[i].z - bodies[j].z
            let d2 = dx * dx + dy * dy + dz * dz
            let mag = dt / (d2 * d2.squareRoot())

            let mj = bodies[j].mass
            bodies[i].vx -= dx * mj * mag
            bodies[i].vy -= dy * mj * mag
            bodies[i].vz -= dz * mj * mag

            let mi = bodies[i].mass
            bodies[j].vx += dx * mi * mag
            bodies[j].vy += dy * mi * mag
            bodies[j].vz += dz * mi * mag
        }
    }
    for i in 0..<nBodies {
        bodies[i].x += dt * bodies[i].vx
        bodies[i].y += dt * bodies[i].vy
        bodies[i].z += dt * bodies[i].vz
    }
}

let args = CommandLine.arguments
guard args.count >= 2, let steps = Int64(args[1]) else {
    FileHandle.standardError.write("usage: \(args[0]) <steps>\n".data(using: .utf8)!)
    exit(1)
}

var bodies = initialBodies()
offsetMomentum(&bodies)
print(String(format: "%.9f", energy(bodies)))
var i: Int64 = 0
while i < steps {
    advance(&bodies, 0.01)
    i += 1
}
print(String(format: "%.9f", energy(bodies)))
