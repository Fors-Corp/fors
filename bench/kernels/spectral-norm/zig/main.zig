const std = @import("std");

fn evalA(i: i64, j: i64) f64 {
    const ij = i + j;
    const denom = @divTrunc(ij * (ij + 1), 2) + i + 1;
    return 1.0 / @as(f64, @floatFromInt(denom));
}

fn evalATimesU(n: i64, u: []const f64, au: []f64) void {
    var i: i64 = 0;
    while (i < n) : (i += 1) {
        var sum: f64 = 0.0;
        var j: i64 = 0;
        while (j < n) : (j += 1) {
            sum += evalA(i, j) * u[@intCast(j)];
        }
        au[@intCast(i)] = sum;
    }
}

fn evalAtTimesU(n: i64, u: []const f64, au: []f64) void {
    var i: i64 = 0;
    while (i < n) : (i += 1) {
        var sum: f64 = 0.0;
        var j: i64 = 0;
        while (j < n) : (j += 1) {
            sum += evalA(j, i) * u[@intCast(j)];
        }
        au[@intCast(i)] = sum;
    }
}

fn evalAtATimesU(n: i64, u: []const f64, ataU: []f64, tmp: []f64) void {
    evalATimesU(n, u, tmp);
    evalAtTimesU(n, tmp, ataU);
}

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i64, args[1], 10);
    const nu: usize = @intCast(n);

    const u = try arena.alloc(f64, nu);
    const v = try arena.alloc(f64, nu);
    const tmp = try arena.alloc(f64, nu);

    for (u) |*x| x.* = 1.0;

    var iter: usize = 0;
    while (iter < 10) : (iter += 1) {
        evalAtATimesU(n, u, v, tmp);
        evalAtATimesU(n, v, u, tmp);
    }

    var vbv: f64 = 0.0;
    var vv: f64 = 0.0;
    for (0..nu) |i| {
        vbv += u[i] * v[i];
        vv += v[i] * v[i];
    }

    var buf: [64]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d:.9}\n", .{@sqrt(vbv / vv)});
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
