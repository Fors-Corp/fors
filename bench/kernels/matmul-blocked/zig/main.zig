const std = @import("std");

// Tuned axis vs naive matmul: cache blocking (kk/ii/jj tiles, i-k-j inside).
// Same BLOCK = 64 in every language.
const BLOCK: usize = 64;

fn worker(n: usize, a: []const f64, b: []const f64, c: []f64, row_start: usize, row_end: usize) void {
    for (row_start..row_end) |i| {
        const c_row = c[i * n .. i * n + n];
        for (c_row) |*v| v.* = 0.0;
    }

    var kk: usize = 0;
    while (kk < n) : (kk += BLOCK) {
        const k_end: usize = @min(kk + BLOCK, n);
        var ii: usize = row_start;
        while (ii < row_end) : (ii += BLOCK) {
            const i_end: usize = @min(ii + BLOCK, row_end);
            var jj: usize = 0;
            while (jj < n) : (jj += BLOCK) {
                const j_end: usize = @min(jj + BLOCK, n);
                var i: usize = ii;
                while (i < i_end) : (i += 1) {
                    const c_tile = c[i * n + jj .. i * n + j_end];
                    var k: usize = kk;
                    while (k < k_end) : (k += 1) {
                        const aik = a[i * n + k];
                        const b_tile = b[k * n + jj .. k * n + j_end];
                        for (c_tile, b_tile) |*cv, bv| {
                            cv.* += aik * bv;
                        }
                    }
                }
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
