const std = @import("std");

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i32, args[1], 10);
    const nu: usize = @intCast(n);

    const perm = try arena.alloc(i32, nu);
    const perm1 = try arena.alloc(i32, nu);
    const count = try arena.alloc(i32, nu);

    for (0..nu) |i| perm1[i] = @intCast(i);

    var r: i32 = n;
    var checksum: i32 = 0;
    var maxflips: i32 = 0;
    var sign: i32 = 1;

    outer: while (true) {
        while (r != 1) {
            count[@intCast(r - 1)] = r;
            r -= 1;
        }
        @memcpy(perm, perm1);

        var flips: i32 = 0;
        while (true) {
            const k = perm[0];
            if (k == 0) break;
            const k2: usize = @intCast(@divTrunc(k + 1, 2));
            var i: usize = 0;
            while (i < k2) : (i += 1) {
                const j: usize = @intCast(k - @as(i32, @intCast(i)));
                const t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            flips += 1;
        }

        checksum += sign * flips;
        if (flips > maxflips) maxflips = flips;

        while (true) {
            if (r == n) {
                break :outer;
            }
            const perm0 = perm1[0];
            var i: usize = 0;
            while (i < @as(usize, @intCast(r))) : (i += 1) {
                perm1[i] = perm1[i + 1];
            }
            perm1[@intCast(r)] = perm0;
            count[@intCast(r)] -= 1;
            if (count[@intCast(r)] > 0) break;
            r += 1;
        }
        sign = -sign;
    }

    var buf: [128]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d}\nPfannkuchen({d}) = {d}\n", .{ checksum, n, maxflips });
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
