//! Files, directories and the environment, as .NET's System.IO and Environment have them on
//! Unix: paths are UTF-8 for the system, texts are read as UTF-8 (or UTF-16 with its byte-order
//! mark) and written as UTF-8 without one, and what fails raises .NET's exception of it, with
//! .NET's message.
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");

const String = rt.String;
const Raised = rt.Raised;
const sys = std.posix.system;

// ---- the program's arguments ----

/// The arguments of `[<EntryPoint>] main argv`: the command line without the program's name, as
/// .NET gives them
pub fn programArgs(args: std.process.Args) rt.Array(String) {
    var it = std.process.Args.Iterator.initAllocator(args, rt.alloc()) catch rt.oom();
    defer it.deinit();
    _ = it.skip();
    var items: std.ArrayList(String) = .empty;
    while (it.next()) |a| items.append(rt.alloc(), fromUtf8(a)) catch rt.oom();
    return rt.arrayFrom(rt.Array(String), items.toOwnedSlice(rt.alloc()) catch rt.oom());
}

// ---- the console ----

/// `Console.Write`/`WriteLine` (and `Console.Error`'s): the text to standard output or error,
/// through the sinks `printf` uses
pub fn consoleWrite(s: String, to_err: bool, newline: bool) void {
    rt.writeText(if (to_err) rt.write_err else rt.write_out, s, newline);
}

// ---- strings and paths ----

/// The UTF-8 of `s`, ended by a zero (the caller frees it)
fn utf8z(s: String) [:0]u8 {
    const units = rt.unitsOf(s);
    const buf = rt.alloc().allocSentinel(u8, units.len * 3, 0) catch rt.oom();
    const n = std.unicode.wtf16LeToWtf8(buf, units);
    buf[n] = 0;
    return buf[0..n :0];
}

fn dupeZ(bytes: []const u8) error{OutOfMemory}![:0]u8 {
    const buf = try rt.alloc().allocSentinel(u8, bytes.len, 0);
    @memcpy(buf[0..bytes.len], bytes);
    return buf;
}

fn freeZ(z: [:0]u8) void {
    rt.alloc().free(z.ptr[0 .. std.mem.len(z.ptr) + 1]);
}

/// A string of UTF-8 bytes: what is not UTF-8 is U+FFFD, as .NET decodes it
pub fn fromUtf8(bytes: []const u8) String {
    var b: rt.TextBuilder = .{};
    var i: usize = 0;
    while (i < bytes.len) {
        const n = std.unicode.utf8ByteSequenceLength(bytes[i]) catch {
            b.addOne(0xFFFD);
            i += 1;
            continue;
        };
        if (i + n > bytes.len) {
            b.addOne(0xFFFD);
            i += 1;
            continue;
        }
        const cp = std.unicode.utf8Decode(bytes[i .. i + n]) catch {
            b.addOne(0xFFFD);
            i += 1;
            continue;
        };
        if (cp < 0x10000) {
            b.addOne(@intCast(cp));
        } else {
            const c = cp - 0x10000;
            b.addOne(@intCast(0xD800 + (c >> 10)));
            b.addOne(@intCast(0xDC00 + (c & 0x3FF)));
        }
        i += n;
    }
    return b.finish();
}

fn fromUtf16(bytes: []const u8, big: bool) String {
    var b: rt.TextBuilder = .{};
    var i: usize = 0;
    while (i + 1 < bytes.len) : (i += 2) {
        const u: u16 = if (big) (@as(u16, bytes[i]) << 8) | bytes[i + 1] else (@as(u16, bytes[i + 1]) << 8) | bytes[i];
        b.addOne(u);
    }
    if (i < bytes.len) b.addOne(0xFFFD);
    return b.finish();
}

/// `Environment.GetEnvironmentVariable(name)`: null when it is not set
pub fn getEnv(name: String) String {
    const z = utf8z(name);
    defer freeZ(z);
    if (envBytes(z)) |v| return fromUtf8(v);
    return null;
}

pub fn envBytes(name: [:0]const u8) ?[]const u8 {
    if (comptime builtin.link_libc) {
        const v = std.c.getenv(name.ptr) orelse return null;
        return std.mem.span(v);
    }
    if (comptime builtin.os.tag == .linux) {
        // (without libc: the process's environment as Linux shows it)
        const S = struct {
            var data: ?[]u8 = null;
        };
        if (S.data == null) S.data = readAll("/proc/self/environ") catch null;
        const data = S.data orelse return null;
        var it = std.mem.splitScalar(u8, data, 0);
        while (it.next()) |entry| {
            if (entry.len > name.len and entry[name.len] == '=' and std.mem.eql(u8, entry[0..name.len], name)) return entry[name.len + 1 ..];
        }
    }
    return null;
}

/// The current directory, as UTF-8 (the caller frees it)
fn cwd() []u8 {
    var buf: [4096]u8 = undefined;
    const rc = sys.getcwd(&buf, buf.len);
    if (comptime @TypeOf(rc) == ?[*]u8 or @TypeOf(rc) == [*c]u8) {
        if (rc == null) return rt.alloc().dupe(u8, "/") catch rt.oom();
    } else if (std.posix.errno(rc) != .SUCCESS) return rt.alloc().dupe(u8, "/") catch rt.oom();
    const n = std.mem.indexOfScalar(u8, &buf, 0) orelse buf.len;
    return rt.alloc().dupe(u8, buf[0..n]) catch rt.oom();
}

/// `Path.GetFullPath(path)`: absolute, without `.`, `..` and repeated separators
fn fullPathBytes(path: []const u8) []u8 {
    var joined: std.ArrayList(u8) = .empty;
    defer joined.deinit(rt.alloc());
    if (path.len == 0 or path[0] != '/') {
        const dir = cwd();
        defer rt.alloc().free(dir);
        joined.appendSlice(rt.alloc(), dir) catch rt.oom();
        joined.append(rt.alloc(), '/') catch rt.oom();
    }
    joined.appendSlice(rt.alloc(), path) catch rt.oom();

    var parts: std.ArrayList([]const u8) = .empty;
    defer parts.deinit(rt.alloc());
    var it = std.mem.splitScalar(u8, joined.items, '/');
    while (it.next()) |p| {
        if (p.len == 0 or std.mem.eql(u8, p, ".")) continue;
        if (std.mem.eql(u8, p, "..")) {
            if (parts.items.len > 0) _ = parts.pop();
            continue;
        }
        parts.append(rt.alloc(), p) catch rt.oom();
    }
    var out: std.ArrayList(u8) = .empty;
    for (parts.items) |p| {
        out.append(rt.alloc(), '/') catch rt.oom();
        out.appendSlice(rt.alloc(), p) catch rt.oom();
    }
    // (a path that ends with a separator keeps it, as .NET keeps it)
    if (out.items.len == 0 or (path.len > 0 and path[path.len - 1] == '/')) out.append(rt.alloc(), '/') catch rt.oom();
    return out.toOwnedSlice(rt.alloc()) catch rt.oom();
}

pub fn fullPath(path: String) Raised!String {
    if (path == null) return rt.raise(rt.ArgumentNullException, rt.str("Value cannot be null. (Parameter 'path')"));
    if (rt.unitsOf(path).len == 0) return rt.raise(rt.ArgumentException, rt.str("The value cannot be an empty string. (Parameter 'path')"));
    const z = utf8z(path);
    defer freeZ(z);
    const f = fullPathBytes(z);
    defer rt.alloc().free(f);
    return fromUtf8(f);
}

// ---- errors ----

const Errno = std.posix.E;

/// What a failure on `path` raises on .NET
fn fail(e: Errno, path: []const u8, comptime is_dir: bool) Raised {
    const full = fullPathBytes(path);
    defer rt.alloc().free(full);
    const name = fromUtf8(full);
    defer rt.drop(name);
    switch (e) {
        .NOENT, .NOTDIR => {
            // (the file is missing, or the directory it would be in)
            if (!is_dir and parentExists(full)) return rt.raise(rt.FileNotFoundException, rt.format(.{ "Could not find file '", name, "'." }));
            return rt.raise(rt.DirectoryNotFoundException, rt.format(.{ "Could not find a part of the path '", name, "'." }));
        },
        .ACCES, .PERM, .ISDIR, .ROFS => return rt.raise(rt.UnauthorizedAccessException, rt.format(.{ "Access to the path '", name, "' is denied." })),
        .EXIST => return rt.raise(rt.IOException, rt.format(.{ "The file '", name, "' already exists." })),
        .NOTEMPTY => return rt.raise(rt.IOException, rt.format(.{ "Directory not empty : '", name, "'" })),
        else => return rt.raise(rt.IOException, rt.format(.{ "I/O error on '", name, "' (", @as(i32, @backingInt(e)), ")." })),
    }
}

fn parentExists(full: []const u8) bool {
    const slash = std.mem.lastIndexOfScalar(u8, full, '/') orelse return true;
    const parent = dupeZ(if (slash == 0) "/" else full[0..slash]) catch rt.oom();
    defer rt.alloc().free(parent);
    return isDir(parent);
}

// ---- files ----

fn openFlags(comptime mode: enum { read, write, append, create_new }) std.posix.O {
    var o: std.posix.O = .{ .ACCMODE = if (mode == .read) .RDONLY else .WRONLY };
    switch (mode) {
        .read => {},
        .write => {
            o.CREAT = true;
            o.TRUNC = true;
        },
        .append => {
            o.CREAT = true;
            o.APPEND = true;
        },
        .create_new => {
            o.CREAT = true;
            o.EXCL = true;
        },
    }
    o.CLOEXEC = true;
    return o;
}

fn readAll(path: [*:0]const u8) ![]u8 {
    const rc = sys.open(path, openFlags(.read), @as(std.posix.mode_t, 0));
    switch (std.posix.errno(rc)) {
        .SUCCESS => {},
        else => |e| return errnoError(e),
    }
    const fd: std.posix.fd_t = @intCast(rc);
    defer _ = sys.close(fd);
    var out: std.ArrayList(u8) = .empty;
    var buf: [16384]u8 = undefined;
    while (true) {
        const r = sys.read(fd, &buf, buf.len);
        switch (std.posix.errno(r)) {
            .SUCCESS => {},
            .INTR => continue,
            else => |e| {
                out.deinit(rt.alloc());
                return errnoError(e);
            },
        }
        const n: usize = @intCast(r);
        if (n == 0) break;
        out.appendSlice(rt.alloc(), buf[0..n]) catch rt.oom();
    }
    return out.toOwnedSlice(rt.alloc()) catch rt.oom();
}

/// (an errno carried as a Zig error, to be turned into .NET's exception)
const io_thread = if (rt.sgc.per_thread) struct {
    threadlocal var last_errno: Errno = .SUCCESS;
    threadlocal var rng: ?std.Random.DefaultPrng = null;
} else struct {
    var last_errno: Errno = .SUCCESS;
    var rng: ?std.Random.DefaultPrng = null;
};

fn errnoError(e: Errno) error{Sys} {
    io_thread.last_errno = e;
    return error.Sys;
}

fn writeAll(path: [*:0]const u8, bytes: []const u8, append: bool) !void {
    const rc = sys.open(path, if (append) openFlags(.append) else openFlags(.write), @as(std.posix.mode_t, 0o666));
    switch (std.posix.errno(rc)) {
        .SUCCESS => {},
        else => |e| return errnoError(e),
    }
    const fd: std.posix.fd_t = @intCast(rc);
    defer _ = sys.close(fd);
    var done: usize = 0;
    while (done < bytes.len) {
        const r = sys.write(fd, bytes.ptr + done, bytes.len - done);
        switch (std.posix.errno(r)) {
            .SUCCESS => done += @intCast(r),
            .INTR => {},
            else => |e| return errnoError(e),
        }
    }
}

fn checkPath(path: String) Raised!void {
    if (path == null) return rt.raise(rt.ArgumentNullException, rt.str("Value cannot be null. (Parameter 'path')"));
    if (rt.unitsOf(path).len == 0) return rt.raise(rt.ArgumentException, rt.str("The value cannot be an empty string. (Parameter 'path')"));
}

/// `File.ReadAllText(path)`: UTF-8, or UTF-16 or UTF-8 by its byte-order mark
pub fn readAllText(path: String) Raised!String {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const bytes = readAll(z) catch return fail(io_thread.last_errno, z, false);
    defer rt.alloc().free(bytes);
    if (bytes.len >= 3 and bytes[0] == 0xEF and bytes[1] == 0xBB and bytes[2] == 0xBF) return fromUtf8(bytes[3..]);
    if (bytes.len >= 2 and bytes[0] == 0xFF and bytes[1] == 0xFE) return fromUtf16(bytes[2..], false);
    if (bytes.len >= 2 and bytes[0] == 0xFE and bytes[1] == 0xFF) return fromUtf16(bytes[2..], true);
    return fromUtf8(bytes);
}

/// `File.ReadAllBytes(path)`
pub fn readAllBytes(path: String) Raised!rt.Array(u8) {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const bytes = readAll(z) catch return fail(io_thread.last_errno, z, false);
    return rt.arrays.arrayFrom(rt.Array(u8), bytes);
}

/// `File.WriteAllText(path, text)` and `File.AppendAllText`: UTF-8, without a byte-order mark
pub fn writeAllText(path: String, text: String, append: bool) Raised!void {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const t = utf8z(text);
    defer freeZ(t);
    writeAll(z, t, append) catch return fail(io_thread.last_errno, z, false);
}

/// `File.WriteAllBytes(path, bytes)`
pub fn writeAllBytes(path: String, bytes: rt.Array(u8)) Raised!void {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    writeAll(z, bytes.items, false) catch return fail(io_thread.last_errno, z, false);
}

fn isDir(z: [*:0]const u8) bool {
    var o = openFlags(.read);
    o.DIRECTORY = true;
    const rc = sys.open(z, o, @as(std.posix.mode_t, 0));
    if (std.posix.errno(rc) != .SUCCESS) return false;
    _ = sys.close(@intCast(rc));
    return true;
}

/// `File.Exists(path)`: a file (not a directory) is there
pub fn fileExists(path: String) bool {
    if (path == null or rt.unitsOf(path).len == 0) return false;
    const z = utf8z(path);
    defer freeZ(z);
    const rc = sys.open(z, openFlags(.read), @as(std.posix.mode_t, 0));
    switch (std.posix.errno(rc)) {
        .SUCCESS => {
            _ = sys.close(@intCast(rc));
            return !isDir(z);
        },
        // (there, but not to be read: it exists)
        .ACCES, .PERM => return !isDir(z),
        else => return false,
    }
}

/// `File.Delete(path)`: nothing when it is not there (but its directory must be)
pub fn deleteFile(path: String) Raised!void {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const rc = sys.unlink(z);
    switch (std.posix.errno(rc)) {
        .SUCCESS => {},
        .NOENT => {
            const full = fullPathBytes(z);
            defer rt.alloc().free(full);
            if (!parentExists(full)) return fail(.NOENT, z, true);
        },
        else => |e| return fail(e, z, false),
    }
}

/// `File.Copy(source, dest, overwrite)`: the bytes of the file, into a new one (IOException when
/// `dest` exists and `overwrite` is false, as on .NET)
pub fn copyFile(source: String, dest: String, overwrite: bool) Raised!void {
    try checkPath(source);
    try checkPath(dest);
    if (!overwrite and fileExists(dest)) {
        const z = utf8z(dest);
        defer freeZ(z);
        return fail(.EXIST, z, false);
    }
    const bytes = try readAllBytes(source);
    defer rt.drop(bytes);
    try writeAllBytes(dest, bytes);
}

/// `File.Move(source, dest, overwrite)`
pub fn moveFile(source: String, dest: String, overwrite: bool) Raised!void {
    try checkPath(source);
    try checkPath(dest);
    const zs = utf8z(source);
    defer freeZ(zs);
    const zd = utf8z(dest);
    defer freeZ(zd);
    if (!fileExists(source)) return fail(.NOENT, zs, false);
    if (!overwrite and fileExists(dest)) return fail(.EXIST, zd, false);
    const rc = sys.rename(zs, zd);
    switch (std.posix.errno(rc)) {
        .SUCCESS => {},
        else => |e| return fail(e, zs, false),
    }
}

// ---- directories ----

/// `Directory.Exists(path)`
pub fn dirExists(path: String) bool {
    if (path == null or rt.unitsOf(path).len == 0) return false;
    const z = utf8z(path);
    defer freeZ(z);
    return isDir(z);
}

/// `Directory.CreateDirectory(path)`: it and the directories above it that are missing
pub fn createDirectory(path: String) Raised!void {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const full = fullPathBytes(z);
    defer rt.alloc().free(full);
    var i: usize = 1;
    while (i <= full.len) : (i += 1) {
        if (i == full.len or full[i] == '/') {
            const part = dupeZ(full[0..i]) catch rt.oom();
            defer rt.alloc().free(part);
            if (isDir(part)) continue;
            const rc = sys.mkdir(part, 0o777);
            switch (std.posix.errno(rc)) {
                .SUCCESS, .EXIST => if (!isDir(part)) return fail(.EXIST, part, true),
                else => |e| return fail(e, part, true),
            }
        }
    }
}

/// `Directory.Delete(path)`: an empty directory
pub fn deleteDirectory(path: String) Raised!void {
    try checkPath(path);
    const z = utf8z(path);
    defer freeZ(z);
    const rc = sys.rmdir(z);
    switch (std.posix.errno(rc)) {
        .SUCCESS => {},
        else => |e| return fail(e, z, true),
    }
}

/// `Directory.GetCurrentDirectory()` and `Environment.CurrentDirectory`
pub fn currentDirectory() String {
    const d = cwd();
    defer rt.alloc().free(d);
    return fromUtf8(d);
}

// ---- temporary files ----

/// `Path.GetTempPath()`: TMPDIR, or /tmp/, ending with a separator
pub fn tempPath() String {
    const dir = envBytes("TMPDIR") orelse "/tmp/";
    if (dir.len > 0 and dir[dir.len - 1] == '/') return fromUtf8(dir);
    var b: std.ArrayList(u8) = .empty;
    defer b.deinit(rt.alloc());
    b.appendSlice(rt.alloc(), dir) catch rt.oom();
    b.append(rt.alloc(), '/') catch rt.oom();
    return fromUtf8(b.items);
}

fn randomChar() u8 {
    if (io_thread.rng == null) {
        const seed: u64 = @bitCast(@import("fable_time.zig").monotonicNs() ^ @import("fable_time.zig").nowUtcTicks() ^ @as(i64, rt.threadId()));
        io_thread.rng = std.Random.DefaultPrng.init(seed);
    }
    const chars = "abcdefghijklmnopqrstuvwxyz012345";
    return chars[io_thread.rng.?.random().uintLessThan(usize, chars.len)];
}

/// `Path.GetRandomFileName()`: eight characters, a dot and three more
pub fn randomFileName() String {
    var name: [12]u8 = undefined;
    for (0..8) |i| name[i] = randomChar();
    name[8] = '.';
    for (9..12) |i| name[i] = randomChar();
    return fromUtf8(&name);
}

/// `Path.GetTempFileName()`: a new empty file in the temporary directory, `tmpXXXXXX.tmp`
pub fn tempFileName() Raised!String {
    const dir = envBytes("TMPDIR") orelse "/tmp";
    var tries: usize = 0;
    while (tries < 100) : (tries += 1) {
        var b: std.ArrayList(u8) = .empty;
        defer b.deinit(rt.alloc());
        b.appendSlice(rt.alloc(), dir) catch rt.oom();
        if (dir.len == 0 or dir[dir.len - 1] != '/') b.append(rt.alloc(), '/') catch rt.oom();
        b.appendSlice(rt.alloc(), "tmp") catch rt.oom();
        for (0..6) |_| b.append(rt.alloc(), randomChar()) catch rt.oom();
        b.appendSlice(rt.alloc(), ".tmp") catch rt.oom();
        const z = dupeZ(b.items) catch rt.oom();
        defer rt.alloc().free(z);
        const rc = sys.open(z, openFlags(.create_new), @as(std.posix.mode_t, 0o600));
        switch (std.posix.errno(rc)) {
            .SUCCESS => {
                _ = sys.close(@intCast(rc));
                return fromUtf8(b.items);
            },
            .EXIST => continue,
            else => |e| return fail(e, z, false),
        }
    }
    return rt.raise(rt.IOException, rt.str("The file could not be created: too many temporary files."));
}
