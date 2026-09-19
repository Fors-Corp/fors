const std = @import("std");

fn worker(n: i64, row_start: i64, row_end: i64, out: *i64) void {
    var count: i64 = 0;
    const nf: f64 = @floatFromInt(n);

    var py = row_start;
    while (py < row_end) : (py += 1) {
        const ci0 = 2.0 * @as(f64, @floatFromInt(py)) / nf - 1.0;
        var px: i64 = 0;
        while (px < n) : (px += 1) {
            const cr = 2.0 * @as(f64, @floatFromInt(px)) / nf - 1.5;
            var zr: f64 = 0.0;
            var zi: f64 = 0.0;
            var iter: i32 = 0;
            while (iter < 50 and zr * zr + zi * zi <= 4.0) {
                const tr = zr * zr - zi * zi + cr;
                const ti = 2.0 * zr * zi + ci0;
                zr = tr;
                zi = ti;
                iter += 1;
            }
            if (iter == 50) {
                count += 1;
            }
        }
    }
    out.* = count;
}

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i64, args[1], 10);
    var num_threads = try std.fmt.parseInt(i64, args[2], 10);
    if (num_threads < 1) num_threads = 1;
    const nt: usize = @intCast(num_threads);

    const row_counts = try arena.alloc(i64, nt);
    const threads = try arena.alloc(std.Thread, nt);

    for (0..nt) |t| {
        const row_start = @divTrunc(n * @as(i64, @intCast(t)), num_threads);
        const row_end = @divTrunc(n * @as(i64, @intCast(t + 1)), num_threads);
        threads[t] = try std.Thread.spawn(.{}, worker, .{ n, row_start, row_end, &row_counts[t] });
    }

    var total: i64 = 0;
    for (0..nt) |t| {
        threads[t].join();
        total += row_counts[t];
    }

    var buf: [32]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d}\n", .{total});
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
