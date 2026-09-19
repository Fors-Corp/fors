const std = @import("std");

const n_bodies = 5;
const pi = std.math.pi;
const solar_mass = 4.0 * pi * pi;
const days_per_year = 365.24;

const Body = struct {
    x: f64,
    y: f64,
    z: f64,
    vx: f64,
    vy: f64,
    vz: f64,
    mass: f64,
};

var bodies = [n_bodies]Body{
    .{ .x = 0.0, .y = 0.0, .z = 0.0, .vx = 0.0, .vy = 0.0, .vz = 0.0, .mass = solar_mass },
    .{
        .x = 4.84143144246472090e+00,
        .y = -1.16032004402742839e+00,
        .z = -1.03622044471123109e-01,
        .vx = 1.66007664274403694e-03 * days_per_year,
        .vy = 7.69901118419740425e-03 * days_per_year,
        .vz = -6.90460016972063023e-05 * days_per_year,
        .mass = 9.54791938424326609e-04 * solar_mass,
    },
    .{
        .x = 8.34336671824457987e+00,
        .y = 4.12479856412430479e+00,
        .z = -4.03523417114321381e-01,
        .vx = -2.76742510726862411e-03 * days_per_year,
        .vy = 4.99852801234917238e-03 * days_per_year,
        .vz = 2.30417297573763929e-05 * days_per_year,
        .mass = 2.85885980666130812e-04 * solar_mass,
    },
    .{
        .x = 1.28943695621391310e+01,
        .y = -1.51111514016986312e+01,
        .z = -2.23307578892655734e-01,
        .vx = 2.96460137564761618e-03 * days_per_year,
        .vy = 2.37847173959480950e-03 * days_per_year,
        .vz = -2.96589568540237556e-05 * days_per_year,
        .mass = 4.36624404335156298e-05 * solar_mass,
    },
    .{
        .x = 1.53796971148509165e+01,
        .y = -2.59193146099879641e+01,
        .z = 1.79258772950371181e-01,
        .vx = 2.68067772490389322e-03 * days_per_year,
        .vy = 1.62824170038242295e-03 * days_per_year,
        .vz = -9.51592254519715870e-05 * days_per_year,
        .mass = 5.15138902046611451e-05 * solar_mass,
    },
};

fn offsetMomentum() void {
    var px: f64 = 0.0;
    var py: f64 = 0.0;
    var pz: f64 = 0.0;
    for (bodies) |b| {
        px += b.vx * b.mass;
        py += b.vy * b.mass;
        pz += b.vz * b.mass;
    }
    bodies[0].vx = -px / solar_mass;
    bodies[0].vy = -py / solar_mass;
    bodies[0].vz = -pz / solar_mass;
}

fn energy() f64 {
    var e: f64 = 0.0;
    for (0..n_bodies) |i| {
        const bi = &bodies[i];
        e += 0.5 * bi.mass * (bi.vx * bi.vx + bi.vy * bi.vy + bi.vz * bi.vz);
        for (i + 1..n_bodies) |j| {
            const bj = &bodies[j];
            const dx = bi.x - bj.x;
            const dy = bi.y - bj.y;
            const dz = bi.z - bj.z;
            const dist = @sqrt(dx * dx + dy * dy + dz * dz);
            e -= (bi.mass * bj.mass) / dist;
        }
    }
    return e;
}

fn advance(dt: f64) void {
    for (0..n_bodies) |i| {
        const bi = &bodies[i];
        for (i + 1..n_bodies) |j| {
            const bj = &bodies[j];
            const dx = bi.x - bj.x;
            const dy = bi.y - bj.y;
            const dz = bi.z - bj.z;
            const d2 = dx * dx + dy * dy + dz * dz;
            const mag = dt / (d2 * @sqrt(d2));

            bi.vx -= dx * bj.mass * mag;
            bi.vy -= dy * bj.mass * mag;
            bi.vz -= dz * bj.mass * mag;

            bj.vx += dx * bi.mass * mag;
            bj.vy += dy * bi.mass * mag;
            bj.vz += dz * bi.mass * mag;
        }
    }
    for (0..n_bodies) |i| {
        const bi = &bodies[i];
        bi.x += dt * bi.vx;
        bi.y += dt * bi.vy;
        bi.z += dt * bi.vz;
    }
}

pub fn main(init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    const steps = try std.fmt.parseInt(i64, args[1], 10);

    offsetMomentum();

    var buf: [64]u8 = undefined;
    var out = try std.fmt.bufPrint(&buf, "{d:.9}\n", .{energy()});
    try std.Io.File.stdout().writeStreamingAll(init.io, out);

    var i: i64 = 0;
    while (i < steps) : (i += 1) {
        advance(0.01);
    }

    out = try std.fmt.bufPrint(&buf, "{d:.9}\n", .{energy()});
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
