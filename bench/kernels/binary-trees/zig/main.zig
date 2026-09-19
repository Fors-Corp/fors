const std = @import("std");

const Node = struct {
    left: ?*Node,
    right: ?*Node,
};

fn makeTree(gpa: std.mem.Allocator, depth: i32) !*Node {
    const node = try gpa.create(Node);
    if (depth == 0) {
        node.left = null;
        node.right = null;
    } else {
        node.left = try makeTree(gpa, depth - 1);
        node.right = try makeTree(gpa, depth - 1);
    }
    return node;
}

fn checkTree(node: *Node) i64 {
    if (node.left == null) {
        return 1;
    }
    return 1 + checkTree(node.left.?) + checkTree(node.right.?);
}

fn freeTree(gpa: std.mem.Allocator, node: *Node) void {
    if (node.left) |left| {
        freeTree(gpa, left);
        freeTree(gpa, node.right.?);
    }
    gpa.destroy(node);
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    var max_depth = try std.fmt.parseInt(i32, args[1], 10);
    const min_depth: i32 = 4;
    if (max_depth < min_depth + 2) {
        max_depth = min_depth + 2;
    }

    var buf: [256]u8 = undefined;
    const stdout = std.Io.File.stdout();

    const stretch_depth = max_depth + 1;
    const stretch_tree = try makeTree(gpa, stretch_depth);
    var out = try std.fmt.bufPrint(&buf, "stretch tree of depth {d}\t check: {d}\n", .{ stretch_depth, checkTree(stretch_tree) });
    try stdout.writeStreamingAll(init.io, out);
    freeTree(gpa, stretch_tree);

    const long_lived_tree = try makeTree(gpa, max_depth);

    var depth: i32 = min_depth;
    while (depth <= max_depth) : (depth += 2) {
        const iterations: i64 = @as(i64, 1) << @intCast(max_depth - depth + min_depth);
        var check_sum: i64 = 0;
        var i: i64 = 0;
        while (i < iterations) : (i += 1) {
            const t = try makeTree(gpa, depth);
            check_sum += checkTree(t);
            freeTree(gpa, t);
        }
        out = try std.fmt.bufPrint(&buf, "{d}\t trees of depth {d}\t check: {d}\n", .{ iterations, depth, check_sum });
        try stdout.writeStreamingAll(init.io, out);
    }

    out = try std.fmt.bufPrint(&buf, "long lived tree of depth {d}\t check: {d}\n", .{ max_depth, checkTree(long_lived_tree) });
    try stdout.writeStreamingAll(init.io, out);
    freeTree(gpa, long_lived_tree);
}
