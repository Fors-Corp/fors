const std = @import("std");

fn lowbias32(x_in: u32) u32 {
    var x = x_in;
    x ^= x >> 16;
    x *%= 0x7feb352d;
    x ^= x >> 15;
    x *%= 0x846ca68b;
    x ^= x >> 16;
    return x;
}

fn worker(start: i64, end: i64, out: *u64) void {
    var sum: u64 = 0;
    var i = start;
    while (i < end) : (i += 1) {
        var x: u32 = @truncate(@as(u64, @intCast(i)));
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        x = lowbias32(x);
        sum += x % 1000;
    }
    out.* = sum;
}

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i64, args[1], 10);
    var num_threads = try std.fmt.parseInt(i64, args[2], 10);
    if (num_threads < 1) num_threads = 1;
    const nt: usize = @intCast(num_threads);

    const partials = try arena.alloc(u64, nt);
    const threads = try arena.alloc(std.Thread, nt);

    for (0..nt) |t| {
        const start = @divTrunc(n * @as(i64, @intCast(t)), num_threads);
        const end = @divTrunc(n * @as(i64, @intCast(t + 1)), num_threads);
        threads[t] = try std.Thread.spawn(.{}, worker, .{ start, end, &partials[t] });
    }

    var total: u64 = 0;
    for (0..nt) |t| {
        threads[t].join();
        total += partials[t];
    }

    var buf: [32]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d}\n", .{total});
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
