//! System.Random: a seeded one is .NET's own generator for seeds (Knuth's subtractive one, which (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const Array = rt.Array;
const Layout = rt.Layout;
const Raised = rt.Raised;
const Shower = rt.Shower;
const String = rt.String;
const TextBuilder = rt.TextBuilder;
const drop = rt.drop;
const dup = rt.dup;
const format = rt.format;
const raise = rt.raise;
const str = rt.str;
const strFrom = rt.strFrom;
const thread = rt.thread;
const track = rt.track;
const unitsOf = rt.unitsOf;
const writeNet = rt.writeNet;

// ---------------------------------------------------------------------------------------------
// System.Random: a seeded one is .NET's own generator for seeds (Knuth's subtractive one, which
// .NET keeps for `Random(seed)`), so it gives the numbers .NET gives; an unseeded one is seeded
// from what differs between runs
// ---------------------------------------------------------------------------------------------

pub const mbig: i32 = std.math.maxInt(i32);

pub const Random = *struct {
    pub const fable_identity = {};
    pub const fable_null_cell = {};
    @"$rc": u32 = 1,
    seed: [56]i32 = @splat(0),
    inext: usize = 0,
    inextp: usize = 21,

    pub fn sample(r: anytype) i32 {
        var i = r.inext + 1;
        if (i >= 56) i = 1;
        var p = r.inextp + 1;
        if (p >= 56) p = 1;
        var v = r.seed[i] -% r.seed[p];
        if (v == mbig) v -= 1;
        if (v < 0) v +%= mbig;
        r.seed[i] = v;
        r.inext = i;
        r.inextp = p;
        return v;
    }

    pub fn unit(r: anytype) f64 {
        return @as(f64, @floatFromInt(sample(r))) * (1.0 / @as(f64, @floatFromInt(mbig)));
    }

    pub fn largeRange(r: anytype) f64 {
        var result = sample(r);
        if (@rem(sample(r), 2) == 0) result = -result;
        var d: f64 = @floatFromInt(result);
        d += @as(f64, @floatFromInt(mbig - 1));
        d /= 2.0 * @as(f64, @floatFromInt(mbig)) - 1.0;
        return d;
    }
};

/// `Random(seed)`
pub fn randomNew(seed: i32) Random {
    const c = rt.alloc().create(@typeInfo(Random).pointer.child) catch rt.oom();
    c.* = .{};
    const subtraction: i32 = if (seed == std.math.minInt(i32)) mbig else @intCast(@abs(seed));
    var mj: i32 = 161803398 - subtraction;
    c.seed[55] = mj;
    var mk: i32 = 1;
    var ii: usize = 0;
    for (1..55) |_| {
        ii += 21;
        if (ii >= 55) ii -= 55;
        c.seed[ii] = mk;
        mk = mj -% mk;
        if (mk < 0) mk +%= mbig;
        mj = c.seed[ii];
    }
    for (1..5) |_| {
        for (1..56) |i| {
            var n = i + 30;
            if (n >= 55) n -= 55;
            c.seed[i] -%= c.seed[1 + n];
            if (c.seed[i] < 0) c.seed[i] +%= mbig;
        }
    }
    if (track) thread.stats.allocs += 1;
    return c;
}

pub var random_count: usize = 0;

/// `Random()`: seeded from what differs between runs and calls here: where the stack and the
/// heap are (the system places them anew each run) and a count of the generators made
pub fn randomUnseeded() Random {
    const count = @atomicRmw(usize, &random_count, .Add, 1, .monotonic) +% 1;
    const r = randomNew(0);
    var local: u8 = 0;
    const mix = [_]u64{ @intFromPtr(&local), @intFromPtr(r), count };
    const h = std.hash.Wyhash.hash(0x9E3779B97F4A7C15, std.mem.sliceAsBytes(&mix));
    const fresh = randomNew(@intCast(h & 0x7fffffff));
    drop(r);
    return fresh;
}

/// `Random.Shared`: one for each thread, as .NET's is (its generator is thread-local, so that it
/// can be used from any thread without a lock). It is kept as long as the thread and not counted
/// as alive (see `rt.uncount`).
const SharedRandom = if (rt.sgc.per_thread) struct {
    threadlocal var r: ?Random = null;
} else struct {
    var r: ?Random = null;
};

pub fn randomShared() Random {
    if (SharedRandom.r == null) {
        const saved_arena = if (comptime rt.uses_arena) thread.arena else null;
        if (comptime rt.uses_arena) thread.arena = null;
        defer if (comptime rt.uses_arena) {
            thread.arena = saved_arena;
        };
        SharedRandom.r = randomUnseeded();
        rt.uncount();
    }
    return dup(SharedRandom.r.?);
}

/// (given up when the thread ends, and before the program counts what it never freed)
pub fn randomSharedRelease() void {
    const r = SharedRandom.r orelse return;
    SharedRandom.r = null;
    rt.recount();
    drop(r);
}

/// `r.Next()`
pub fn randomNext(r: Random) i32 {
    return @TypeOf(r.*).sample(r);
}

/// `r.Next(maxValue)`
pub fn randomNextMax(r: Random, max: i32) Raised!i32 {
    if (max < 0) return raise(ArgumentOutOfRangeException, format(.{ "maxValue ('", max, "') must be a non-negative value. (Parameter 'maxValue')" }));
    return @intFromFloat(@TypeOf(r.*).unit(r) * @as(f64, @floatFromInt(max)));
}

/// `r.Next(minValue, maxValue)`
pub fn randomNextRange(r: Random, min: i32, max: i32) Raised!i32 {
    if (min > max) return raise(ArgumentOutOfRangeException, str("'minValue' cannot be greater than maxValue. (Parameter 'minValue')"));
    const range: i64 = @as(i64, max) - min;
    const R = @TypeOf(r.*);
    if (range <= std.math.maxInt(i32)) return @as(i32, @intFromFloat(R.unit(r) * @as(f64, @floatFromInt(range)))) + min;
    return @intCast(@as(i64, @intFromFloat(R.largeRange(r) * @as(f64, @floatFromInt(range)))) + min);
}

/// `r.NextDouble()`
pub fn randomNextDouble(r: Random) f64 {
    return @TypeOf(r.*).unit(r);
}

/// `r.NextBytes(buffer)`
pub fn randomNextBytes(r: Random, buffer: Array(u8)) void {
    for (buffer.items) |*b| b.* = @truncate(@as(u32, @bitCast(@TypeOf(r.*).sample(r))));
}

pub const StringBuilder = *struct {
    pub const fable_identity = {};
    pub const fable_null_cell = {};
    @"$rc": u32 = 1,
    units: std.ArrayList(u16) = .empty,

    pub fn fable_free(c: anytype) void {
        c.units.deinit(rt.alloc());
    }

    pub fn fable_show(b: *Shower, x: anytype, depth: i32) *Layout {
        _ = depth;
        return b.leaf(false, b.arena.dupe(u16, x.units.items) catch rt.oom(), false);
    }
};

pub fn sbNew(init: String) StringBuilder {
    const c = rt.alloc().create(@typeInfo(StringBuilder).pointer.child) catch rt.oom();
    c.* = .{};
    c.units.appendSlice(rt.alloc(), unitsOf(init)) catch rt.oom();
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `sb.Append x`: the builder again (a reference of its own).
pub fn sbAppend(sb: StringBuilder, x: anytype) StringBuilder {
    var out: TextBuilder = .{ .list = sb.units };
    writeNet(&out, x);
    sb.units = out.list;
    return dup(sb);
}

pub fn sbAppendLine(sb: StringBuilder, x: anytype) StringBuilder {
    var out: TextBuilder = .{ .list = sb.units };
    writeNet(&out, x);
    out.addOne('\n');
    sb.units = out.list;
    return dup(sb);
}

pub fn sbToString(sb: StringBuilder) String {
    return strFrom(sb.units.items);
}

pub fn sbLength(sb: StringBuilder) i32 {
    return @intCast(sb.units.items.len);
}

pub fn sbClear(sb: StringBuilder) StringBuilder {
    sb.units.clearRetainingCapacity();
    return dup(sb);
}
