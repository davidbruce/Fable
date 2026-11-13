//! The clock and the local time zone, for `DateTime` (the library's DateTime.fs): the time now,
//! and the offset of the local time zone at an instant, read from /etc/localtime (TZif), as .NET
//! reads it on Unix when `TZ` is not set. (The `TZ` variable is not read: the program's
//! environment reaches only its `main` in Zig.) Without a readable zone, local time is UTC.
const std = @import("std");

/// .NET's ticks (100 ns since 0001-01-01) of the Unix epoch
pub const unix_epoch_ticks: i64 = 621_355_968_000_000_000;

/// The time now, in UTC ticks
pub fn nowUtcTicks() i64 {
    var ts: std.posix.timespec = undefined;
    _ = std.posix.system.clock_gettime(.REALTIME, &ts);
    const ns: i128 = @as(i128, ts.sec) * 1_000_000_000 + ts.nsec;
    return unix_epoch_ticks + @as(i64, @intCast(@divFloor(ns, 100)));
}

const Zone = struct {
    /// transition times (Unix seconds), ascending, and the offset (seconds) from each
    times: []i64 = &.{},
    offsets: []i32 = &.{},
    /// the offset before the first transition (or of a zone without transitions)
    initial: i32 = 0,
};

var zone: ?Zone = null;

fn readFile(path: [*:0]const u8, buf: []u8) ?[]u8 {
    const rc = std.posix.system.open(path, .{ .ACCMODE = .RDONLY }, @as(std.posix.mode_t, 0));
    if (std.posix.errno(rc) != .SUCCESS) return null;
    const fd: std.posix.fd_t = @intCast(rc);
    defer _ = std.posix.system.close(fd);
    var n: usize = 0;
    while (n < buf.len) {
        const r = std.posix.system.read(fd, buf.ptr + n, buf.len - n);
        if (std.posix.errno(r) != .SUCCESS) return null;
        const got: usize = @intCast(r);
        if (got == 0) break;
        n += got;
    }
    return buf[0..n];
}

fn be32(b: []const u8) i32 {
    return std.mem.readInt(i32, b[0..4], .big);
}

fn be64(b: []const u8) i64 {
    return std.mem.readInt(i64, b[0..8], .big);
}

/// A TZif file: the version 2+ (64-bit) part when there is one
fn parse(data: []const u8, allocator: std.mem.Allocator) ?Zone {
    if (data.len < 44 or !std.mem.eql(u8, data[0..4], "TZif")) return null;
    var p = data;
    var wide = false;
    // (version 2 and later: skip the 32-bit block to the 64-bit one)
    if (data[4] >= '2') {
        const counts = header(data);
        const skip = 44 + counts.timecnt * 4 + counts.timecnt + counts.typecnt * 6 + counts.charcnt + counts.leapcnt * 8 + counts.isstdcnt + counts.isutcnt;
        if (data.len < skip + 44) return null;
        p = data[skip..];
        wide = true;
    }
    const c = header(p);
    const tsize: usize = if (wide) 8 else 4;
    var at: usize = 44;
    if (p.len < at + c.timecnt * tsize + c.timecnt + c.typecnt * 6) return null;
    const times = allocator.alloc(i64, c.timecnt) catch return null;
    for (0..c.timecnt) |i| {
        times[i] = if (wide) be64(p[at + i * 8 ..]) else be32(p[at + i * 4 ..]);
    }
    at += c.timecnt * tsize;
    const idx = p[at .. at + c.timecnt];
    at += c.timecnt;
    const types = p[at .. at + c.typecnt * 6];
    const offsets = allocator.alloc(i32, c.timecnt) catch return null;
    for (0..c.timecnt) |i| offsets[i] = be32(types[@as(usize, idx[i]) * 6 ..]);
    // (before the first transition: the first type that is not daylight time)
    var initial: i32 = if (c.typecnt > 0) be32(types[0..]) else 0;
    for (0..c.typecnt) |t| {
        if (types[t * 6 + 4] == 0) {
            initial = be32(types[t * 6 ..]);
            break;
        }
    }
    return .{ .times = times, .offsets = offsets, .initial = initial };
}

const Counts = struct { isutcnt: usize, isstdcnt: usize, leapcnt: usize, timecnt: usize, typecnt: usize, charcnt: usize };

fn header(p: []const u8) Counts {
    return .{
        .isutcnt = @intCast(be32(p[20..])),
        .isstdcnt = @intCast(be32(p[24..])),
        .leapcnt = @intCast(be32(p[28..])),
        .timecnt = @intCast(be32(p[32..])),
        .typecnt = @intCast(be32(p[36..])),
        .charcnt = @intCast(be32(p[40..])),
    };
}

fn loadZone() Zone {
    const allocator = std.heap.page_allocator;
    const buf = allocator.alloc(u8, 1 << 20) catch return .{};
    defer allocator.free(buf);
    if (readFile("/etc/localtime", buf)) |data| {
        if (parse(data, allocator)) |z| return z;
    }
    return .{};
}

/// The offset of the local time zone (in ticks) at a UTC instant (in ticks)
pub fn localOffsetTicks(utc_ticks: i64) i64 {
    if (zone == null) zone = loadZone();
    const z = zone.?;
    const seconds = @divFloor(utc_ticks - unix_epoch_ticks, 10_000_000);
    var offset: i32 = z.initial;
    // (the last transition at or before the instant)
    var lo: usize = 0;
    var hi: usize = z.times.len;
    while (lo < hi) {
        const mid = (lo + hi) / 2;
        if (z.times[mid] <= seconds) lo = mid + 1 else hi = mid;
    }
    if (lo > 0) offset = z.offsets[lo - 1];
    return @as(i64, offset) * 10_000_000;
}

test "the clock and the local zone" {
    const now = nowUtcTicks();
    try std.testing.expect(now > 638_000_000_000_000_000);
    const off = localOffsetTicks(now);
    try std.testing.expect(off > -15 * 36_000_000_000 and off < 15 * 36_000_000_000);
}
