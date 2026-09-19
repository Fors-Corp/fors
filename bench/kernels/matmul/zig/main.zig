const std = @import("std");

fn worker(n: usize, a: []const f64, b: []const f64, c: []f64, row_start: usize, row_end: usize) void {
    var i = row_start;
    while (i < row_end) : (i += 1) {
        const a_row = a[i * n .. i * n + n];
        const c_row = c[i * n .. i * n + n];
        for (c_row) |*v| v.* = 0.0;

        var k: usize = 0;
        while (k < n) : (k += 1) {
            const aik = a_row[k];
            const b_row = b[k * n .. k * n + n];
            for (c_row, b_row) |*cv, bv| {
                cv.* += aik * bv;
            }
        }
    }
}

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i64, args[1], 10);
    var threads_n = try std.fmt.parseInt(i64, args[2], 10);
    if (threads_n < 1) threads_n = 1;
    if (threads_n > n) threads_n = n;
    const nu: usize = @intCast(n);
    const nt: usize = @intCast(threads_n);

    const a = try arena.alloc(f64, nu * nu);
    const b = try arena.alloc(f64, nu * nu);
    const c = try arena.alloc(f64, nu * nu);

    for (0..nu) |i| {
        for (0..nu) |j| {
            const ij: i64 = @as(i64, @intCast(i)) * @as(i64, @intCast(j));
            a[i * nu + j] = @floatFromInt(@mod(ij, 7) + 1);
            b[i * nu + j] = @floatFromInt(@mod(@as(i64, @intCast(i + j)), 5) + 1);
        }
    }

    const threads = try arena.alloc(std.Thread, nt);
    const base = @divTrunc(nu, nt);
    const rem = nu % nt;
    var row: usize = 0;
    for (0..nt) |t| {
        const cnt = base + (if (t < rem) @as(usize, 1) else 0);
        const row_start = row;
        const row_end = row + cnt;
        row += cnt;
        threads[t] = try std.Thread.spawn(.{}, worker, .{ nu, a, b, c, row_start, row_end });
    }
    for (0..nt) |t| {
        threads[t].join();
    }

    var sum: f64 = 0.0;
    var trace: f64 = 0.0;
    for (0..nu) |i| {
        const c_row = c[i * nu .. i * nu + nu];
        for (c_row) |v| sum += v;
        trace += c_row[i];
    }

    var buf: [64]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d:.0}\n{d:.0}\n", .{ sum, trace });
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
