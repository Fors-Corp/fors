const std = @import("std");

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const n = try std.fmt.parseInt(i64, args[1], 10);

    var im = std.AutoHashMap(i64, i64).init(arena);
    var sm = std.StringHashMap(i64).init(arena);

    var x: u64 = 42;
    const mod1: i64 = @divTrunc(n, 4) + 1;
    var i: i64 = 0;
    while (i < n) : (i += 1) {
        x = (x * 48271) % 2147483647;
        const key: i64 = @intCast(x % @as(u64, @intCast(mod1)));
        const entry = try im.getOrPut(key);
        if (entry.found_existing) {
            entry.value_ptr.* += 1;
        } else {
            entry.value_ptr.* = 1;
        }
    }

    const n2: i64 = @divTrunc(n, 4);
    const mod2: i64 = @divTrunc(n, 16) + 1;
    var strbuf: [32]u8 = undefined;
    i = 0;
    while (i < n2) : (i += 1) {
        x = (x * 48271) % 2147483647;
        const num: i64 = @intCast(x % @as(u64, @intCast(mod2)));
        const key = try std.fmt.bufPrint(&strbuf, "k{d}", .{num});
        const entry = try sm.getOrPut(key);
        if (entry.found_existing) {
            entry.value_ptr.* += 1;
        } else {
            entry.key_ptr.* = try arena.dupe(u8, key);
            entry.value_ptr.* = 1;
        }
    }

    const MOD: u64 = 1000000007;
    var checksum: u64 = 0;

    var im_it = im.iterator();
    while (im_it.next()) |entry| {
        const k: u64 = @as(u64, @intCast(entry.key_ptr.*)) % MOD;
        const c: u64 = @as(u64, @intCast(entry.value_ptr.*)) % MOD;
        checksum = (checksum + (k * c) % MOD) % MOD;
    }

    var sm_it = sm.iterator();
    while (sm_it.next()) |entry| {
        const num = try std.fmt.parseInt(i64, entry.key_ptr.*[1..], 10);
        const k: u64 = @as(u64, @intCast(num)) % MOD;
        const c: u64 = @as(u64, @intCast(entry.value_ptr.*)) % MOD;
        checksum = (checksum + (k * c) % MOD) % MOD;
    }

    var buf: [64]u8 = undefined;
    const out = try std.fmt.bufPrint(&buf, "{d}\n{d}\n{d}\n", .{ im.count(), sm.count(), checksum });
    try std.Io.File.stdout().writeStreamingAll(init.io, out);
}
