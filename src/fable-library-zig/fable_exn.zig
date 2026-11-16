//! Exceptions: .NET's classes, F#'s exception declarations, raise and catch (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const Collected = rt.Collected;
const GcHdr = rt.GcHdr;
const Layout = rt.Layout;
const Prec = rt.Prec;
const Random = rt.Random;
const Shower = rt.Shower;
const String = rt.String;
const TextBuilder = rt.TextBuilder;
const anyText = rt.anyText;
const asyncStateRelease = rt.asyncStateRelease;
const box = rt.box;
const captured = rt.captured;
const cell = rt.cell;
const collect = rt.collect;
const compare = rt.compare;
const counted = rt.counted;
const drop = rt.drop;
const dup = rt.dup;
const eql = rt.eql;
const exn_show = rt.exn_show;
const free = rt.free;
const functions_in_cycles = rt.functions_in_cycles;
const gcTick = rt.gcTick;
const hash = rt.hash;
const holdsCyclic = rt.holdsCyclic;
const live = rt.live;
const markShared = rt.markShared;
const new = rt.new;
const nullRef = rt.nullRef;
const oom = rt.oom;
const overflow = rt.overflow;
const run = rt.run;
const sgc = rt.sgc;
const stack_traces = rt.stack_traces;
const str = rt.str;
const thread = rt.thread;
const track = rt.track;
const unitsOf = rt.unitsOf;
const writeText = rt.writeText;

// Exceptions
//
// A function that can raise returns `Raised!T`. `raise` moves the exception into `current` and
// returns `error.Raised`; every caller on the way gives up what it still owns and returns the
// error too, until a `with` handler takes the exception out. The exception is always owned in
// exactly one place.
//
// An exception is a reference-counted cell that starts with a header naming its type, so that
// a file can declare exception types that no other file has to know about.
// ---------------------------------------------------------------------------------------------

pub const Raised = error{Raised};

pub const ExnType = struct {
    name: []const u8,
    destroy: *const fn (Exn) void,
    /// marks what the exception holds shared (see `markShared`)
    share: *const fn (Exn) Raised!void,
    /// the message, for an exception that was made with one
    message: ?*const fn (Exn) String = null,
    /// the .NET class this one derives from, if a program can name it
    parent: ?*const ExnType = null,
    /// the exception as `%A` writes it (null when the program never formats one: see `exn_show`)
    show: ?*const fn (*Shower, Exn, Prec, i32) *Layout,
    /// F#'s `exception` declarations are equal when their fields are (null: only to itself)
    eql: ?*const fn (Exn, Exn) bool = null,
    hash: ?*const fn (Exn) i32 = null,
    /// a .NET exception's `InnerException`
    set_inner: ?*const fn (Exn, Exn) void = null,
    inner: ?*const fn (Exn) ?Exn = null,
    /// an AggregateException's `InnerExceptions`, when it was made with them
    set_inners: ?*const fn (Exn, rt.Array(Exn)) void = null,
    inners: ?*const fn (Exn) ?rt.Array(Exn) = null,
    /// an ArgumentException's `ParamName`
    set_param: ?*const fn (Exn, String) void = null,
    param: ?*const fn (Exn) String = null,
};

pub const ExnHeader = struct {
    @"$rc": u32 = 1,
    /// the collector's header of this exception, if what it holds can be part of a cycle
    gc: ?*sgc.Hdr = null,
    type: *const ExnType,
    trace_len: u8 = 0,
    trace_thrown: bool = false,
    trace_skipped: bool = false,
    trace_addrs: if (stack_traces) [32]usize else void = undefined,
};

/// F#'s `exn`.
pub const Exn = *ExnHeader;

/// An F# `exception` declaration with the given fields.
pub fn ExnOf(comptime name: []const u8, comptime Payload: type) type {
    return ExnUnder(name, Payload, null, true);
}

/// F#'s `MatchFailureException`: the file, line and column of the match, and a fixed message.
pub const MatchFailureException = ExnUnder("Microsoft.FSharp.Core.MatchFailureException", struct { Data0: String, Data1: i32, Data2: i32 }, null, true);

/// A .NET exception class with a message, derived from `Parent` (or from `System.Exception`).
pub fn Class(comptime name: []const u8, comptime Parent: ?type) type {
    return ExnUnder(name, Described, if (Parent) |P| &P.info else null, false);
}

pub fn ExnUnder(comptime name: []const u8, comptime Payload: type, comptime parent: ?*const ExnType, comptime sealed: bool) type {
    return struct {
        const cyclic = functions_in_cycles and holdsCyclic(Payload);
        const Whole = struct { header: ExnHeader, hdr: GcHdr(cyclic) = undefined, payload: Payload };
        const K = Collected(
            Whole,
            "hdr",
            @as(isize, @offsetOf(Whole, "header")) + @as(isize, @offsetOf(ExnHeader, "$rc")) - @as(isize, @offsetOf(Whole, "hdr")),
            "payload",
        );

        const is_match_failure = std.mem.eql(u8, name, "Microsoft.FSharp.Core.MatchFailureException");
        const is_aggregate = std.mem.eql(u8, name, "System.AggregateException");

        pub const info: ExnType = .{
            .name = name,
            .destroy = destroy,
            .share = share,
            .message = if (Payload == Described) message else if (is_match_failure) matchMessage else if (@hasField(Payload, "fable_message")) classMessage else null,
            .parent = parent,
            .show = if (exn_show) show else null,
            // (an object of a class compares by reference, as on .NET)
            .eql = if (Payload == Described or @hasField(Payload, "fable_message")) null else payloadEql,
            .hash = if (Payload == Described or @hasField(Payload, "fable_message")) null else payloadHash,
            .set_inner = setInner,
            .inner = innerOf,
            .set_inners = setInners,
            .inners = innersOf,
            .set_param = setParam,
            .param = paramOf,
        };

        /// (a class deriving from System.Exception: the message its base constructor was given)
        pub fn classMessage(e: Exn) String {
            return dup(of(e).fable_message);
        }

        pub fn matchMessage(_: Exn) String {
            return str("The match cases were incomplete");
        }

        pub fn payloadEql(a: Exn, b: Exn) bool {
            return eql(of(a).*, of(b).*);
        }

        pub fn payloadHash(e: Exn) i32 {
            return hash(of(e).*);
        }

        pub fn show(b: *Shower, e: Exn, prec: Prec, depth: i32) *Layout {
            if (comptime is_match_failure) return b.case("MatchFailureException", of(e), prec, depth);
            if (Payload != Described) return b.case(name, of(e), prec, depth);
            // a .NET exception: its class and its message (and the exception inside, as
            // .NET's `ToString` writes it)
            var t: TextBuilder = .{};
            exnText(&t, e);
            const s = t.finish();
            defer drop(s);
            return b.leaf(false, b.arena.dupe(u16, unitsOf(s)) catch oom(), false);
        }

        pub fn setInner(e: Exn, within: Exn) void {
            if (Payload == Described) {
                const p: *Payload = @constCast(of(e));
                if (p.InnerException) |old| drop(old);
                p.InnerException = dup(within);
            }
        }

        pub fn setInners(e: Exn, all: rt.Array(Exn)) void {
            if (Payload == Described) {
                const p: *Payload = @constCast(of(e));
                if (p.Inners) |old| drop(old);
                p.Inners = dup(all);
                if (p.InnerException) |old| drop(old);
                p.InnerException = if (all.items.len > 0) dup(all.items[0]) else null;
            }
        }

        pub fn innersOf(e: Exn) ?rt.Array(Exn) {
            return if (Payload == Described) of(e).Inners else null;
        }

        pub fn setParam(e: Exn, param_name: String) void {
            if (Payload == Described) {
                const p: *Payload = @constCast(of(e));
                drop(p.ParamName);
                p.ParamName = dup(param_name);
            }
        }

        pub fn paramOf(e: Exn) String {
            return if (Payload == Described) dup(of(e).ParamName) else null;
        }

        pub fn innerOf(e: Exn) ?Exn {
            return if (Payload == Described) of(e).InnerException else null;
        }

        pub fn message(e: Exn) String {
            if (comptime is_aggregate) return aggregateMessage(e, of(e).Message);
            return dup(of(e).Message);
        }

        pub fn new(payload: Payload) Exn {
            if (comptime cyclic) gcTick();
            const c = rt.allocator.create(Whole) catch oom();
            c.* = .{ .header = .{ .type = &info }, .payload = payload };
            if (comptime cyclic) {
                c.hdr = thread.collector.hdr(&K.desc, K.isLeaf(c));
                c.header.gc = &c.hdr;
            }
            if (track) thread.stats.allocs += 1;
            return &c.header;
        }

        /// Is `e` an exception of this type, or of a class that derives from it?
        pub inline fn is(e: Exn) bool {
            if (sealed) return e.type == &info;
            var t: ?*const ExnType = e.type;
            while (t) |class| : (t = class.parent) {
                if (class == &info) return true;
            }
            return false;
        }

        /// The fields of an exception of this type.
        pub inline fn of(e: Exn) *const Payload {
            const c: *Whole = @alignCast(@fieldParentPtr("header", e));
            return &c.payload;
        }

        pub fn destroy(e: Exn) void {
            const c: *Whole = @alignCast(@fieldParentPtr("header", e));
            drop(c.payload);
            free(c);
        }

        pub fn share(e: Exn) Raised!void {
            const c: *Whole = @alignCast(@fieldParentPtr("header", e));
            try markShared(c.payload);
        }
    };
}

/// The exception in flight is `thread.current`.
pub noinline fn throw(e: Exn) void {
    std.debug.assert(thread.current == null);
    if (stack_traces and !e.trace_thrown) {
        e.trace_thrown = true;
        var st = std.debug.captureCurrentStackTrace(.{ .first_address = @returnAddress() }, &e.trace_addrs);
        if (st.return_addresses.len == 0) {
            st = std.debug.captureCurrentStackTrace(.{}, &e.trace_addrs);
        }
        e.trace_len = @intCast(st.return_addresses.len);
        e.trace_skipped = st.skipped != .none;
    }
    thread.current = e;
}

pub fn take() Exn {
    const e = thread.current.?;
    thread.current = null;
    return e;
}

/// Can a call with a result of this type have raised?
pub fn isRaised(comptime T: type) bool {
    return @typeInfo(T) == .error_union;
}

/// The result type of a function that raises only if one of the functions of other files it
/// calls does. (A file is compiled without knowing whether they do; Zig knows.)
pub fn MayRaise(comptime T: type, comptime callees: anytype) type {
    inline for (callees) |callee| {
        if (isRaised(@typeInfo(@TypeOf(callee)).@"fn".return_type.?)) return Raised!T;
    }
    return T;
}

/// What a .NET exception class holds: its message.
pub const Described = struct { Message: String, InnerException: ?Exn = null, ParamName: String = null, Inners: ?rt.Array(Exn) = null };

/// What `failwith` raises: .NET's `System.Exception` with a message. (Every exception is a
/// `System.Exception`, so a test for that class is not a test at all; this is the test for
/// exactly this class, which is what the `Failure` pattern is.)
pub const Failure = ExnUnder("System.Exception", Described, null, true);

/// The .NET exception classes that a program can raise and handle by name, each under the
/// class it derives from on .NET.
pub const SystemException = Class("System.SystemException", null);
pub const ArgumentException = Class("System.ArgumentException", SystemException);
pub const ArgumentNullException = Class("System.ArgumentNullException", ArgumentException);
pub const ArgumentOutOfRangeException = Class("System.ArgumentOutOfRangeException", ArgumentException);
pub const ArithmeticException = Class("System.ArithmeticException", SystemException);
pub const DivideByZeroException = Class("System.DivideByZeroException", ArithmeticException);
pub const OverflowException = Class("System.OverflowException", ArithmeticException);
pub const InvalidOperationException = Class("System.InvalidOperationException", SystemException);
pub const ThreadStateException = Class("System.Threading.ThreadStateException", SystemException);
pub const NotSupportedException = Class("System.NotSupportedException", SystemException);
pub const NotImplementedException = Class("System.NotImplementedException", SystemException);
pub const IndexOutOfRangeException = Class("System.IndexOutOfRangeException", SystemException);
pub const NullReferenceException = Class("System.NullReferenceException", SystemException);
pub const FormatException = Class("System.FormatException", SystemException);
pub const KeyNotFoundException = Class("System.Collections.Generic.KeyNotFoundException", SystemException);
pub const AggregateException = Class("System.AggregateException", null);
pub const InvalidCastException = Class("System.InvalidCastException", SystemException);
pub const TimeoutException = Class("System.TimeoutException", SystemException);
pub const UriFormatException = Class("System.UriFormatException", FormatException);
pub const IOException = Class("System.IO.IOException", SystemException);
pub const FileNotFoundException = Class("System.IO.FileNotFoundException", IOException);
pub const DirectoryNotFoundException = Class("System.IO.DirectoryNotFoundException", IOException);
pub const UnauthorizedAccessException = Class("System.UnauthorizedAccessException", SystemException);
pub const ObjectDisposedException = Class("System.ObjectDisposedException", InvalidOperationException);
pub const OperationCanceledException = Class("System.OperationCanceledException", SystemException);
pub const TaskCanceledException = Class("System.Threading.Tasks.TaskCanceledException", OperationCanceledException);
pub const ApplicationException = Class("System.ApplicationException", null);
pub const OutOfMemoryException = Class("System.OutOfMemoryException", SystemException);
pub const NotFiniteNumberException = Class("System.NotFiniteNumberException", ArithmeticException);
pub const RankException = Class("System.RankException", SystemException);
pub const ArrayTypeMismatchException = Class("System.ArrayTypeMismatchException", SystemException);
pub const MissingMethodException = Class("System.MissingMethodException", SystemException);

/// Raise an exception of a .NET class with a message.
pub fn raise(comptime C: type, message: String) Raised {
    throw(C.new(.{ .Message = message }));
    return error.Raised;
}

/// `a / b` for whole numbers: as .NET, a division by zero raises, and so does the smallest
/// number of 32 or 64 bits divided by -1 (its result does not fit).
pub fn div(comptime T: type, a: T, b: T) Raised!T {
    if (b == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    const info = @typeInfo(T).int;
    if (info.signedness == .signed and b == -1) {
        if (info.bits >= 32 and a == std.math.minInt(T)) {
            return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        }
        return 0 -% a;
    }
    return @divTrunc(a, b);
}

/// `a % b` for whole numbers, with the sign of `a`.
pub fn rem(comptime T: type, a: T, b: T) Raised!T {
    if (b == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    const info = @typeInfo(T).int;
    if (info.signedness == .signed and b == -1) {
        if (info.bits >= 32 and a == std.math.minInt(T)) {
            return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        }
        return 0;
    }
    return @rem(a, b);
}

/// `e.Message`: the message an exception was made with; for an F# exception, the exception
/// as `%A` writes it.
/// `Exception(message, inner)`: the new exception, with `inner` inside it.
pub fn exnWithInner(e: Exn, inner_exn: Exn) Exn {
    if (e.type.set_inner) |f| f(e, inner_exn);
    return dup(e);
}

/// `AggregateException(message, exceptions)`: the new exception, with them inside it (the first
/// is its `InnerException`)
pub fn exnWithInners(e: Exn, all: anytype) Exn {
    const A = rt.Array(Exn);
    const list: A = if (comptime @typeInfo(@TypeOf(all)) == .optional)
        (all orelse rt.arrayFrom(A, rt.arrayItems(A, 0)))
    else
        all;
    if (e.type.set_inners) |f| f(e, list);
    if (comptime @typeInfo(@TypeOf(all)) == .optional) {
        if (all == null) drop(list);
    }
    return dup(e);
}

/// `e.InnerExceptions`: those an AggregateException was made with, or the one inside it
pub fn exnInnerList(e: Exn) rt.Array(Exn) {
    const A = rt.Array(Exn);
    if (e.type.inners) |f| {
        if (f(e)) |all| return dup(all);
    }
    const inner: ?Exn = if (e.type.inner) |f| f(e) else null;
    const items = rt.arrayItems(A, if (inner == null) 0 else 1);
    if (inner) |i| items[0] = dup(i);
    return rt.arrayFrom(A, items);
}

/// `e.Flatten()`: an AggregateException of the exceptions inside `e` and inside the
/// AggregateExceptions among them, at every depth, with `e`'s own message
pub fn exnFlatten(e: Exn) Exn {
    var leaves: std.ArrayList(Exn) = .empty;
    collectLeaves(&leaves, e);
    const A = rt.Array(Exn);
    const list = rt.arrayFrom(A, leaves.toOwnedSlice(rt.allocator) catch rt.oom());
    defer drop(list);
    const own: String = if (e.type.inners != null) AggregateException.of(e).Message else null;
    const flat = AggregateException.new(.{ .Message = dup(own) });
    defer drop(flat);
    return exnWithInners(flat, list);
}

fn collectLeaves(leaves: *std.ArrayList(Exn), e: Exn) void {
    const all = exnInnerList(e);
    defer drop(all);
    for (all.items) |i| {
        if (AggregateException.is(i)) {
            collectLeaves(leaves, i);
        } else {
            leaves.append(rt.allocator, dup(i)) catch rt.oom();
        }
    }
}

/// An AggregateException's message: its own, then the message of each exception inside it in
/// parentheses, as .NET writes it
fn aggregateMessage(e: Exn, own: String) String {
    const all = exnInnerList(e);
    defer drop(all);
    if (all.items.len == 0) return dup(own);
    var b: TextBuilder = .{};
    b.add(unitsOf(own));
    for (all.items) |i| {
        b.addAscii(" (");
        const m = exnMessage(i);
        defer drop(m);
        b.add(unitsOf(m));
        b.addAscii(")");
    }
    return b.finish();
}

/// `e.InnerException`, which is null for most exceptions.
pub fn exnInner(e: Exn) Raised!Exn {
    if (e.type.inner) |f| {
        if (f(e)) |i| return dup(i);
    }
    return nullRef();
}

/// `box e.InnerException`: null when there is none, as on .NET
pub fn exnInnerBoxed(e: Exn) Any {
    if (e.type.inner) |f| {
        if (f(e)) |i| return box(i);
    }
    return null;
}

/// `isNull e.InnerException`
pub fn exnHasNoInner(e: Exn) bool {
    if (e.type.inner) |f| return f(e) == null;
    return true;
}

/// `e.ToString()` without the stack trace: its class, its message, and the exceptions inside.
pub fn exnText(t: *TextBuilder, e: Exn) void {
    t.addAscii(e.type.name);
    t.addAscii(": ");
    const m = exnMessage(e);
    defer drop(m);
    t.add(unitsOf(m));
    if (e.type.inner) |f| {
        if (f(e)) |i| {
            t.addAscii("\n ---> ");
            exnText(t, i);
            t.addAscii("\n   --- End of inner exception stack trace ---");
        }
    }
}

/// `e.ToString()`: .NET's class name and message (its stack trace's frames are left out)
pub fn exnToString(e: Exn) Raised!String {
    const m = exnMessage(e);
    defer drop(m);
    var b: TextBuilder = .{};
    b.addAscii(e.type.name);
    if (unitsOf(m).len > 0) {
        b.addAscii(": ");
        b.add(unitsOf(m));
    }
    return b.finish();
}

pub fn exnMessage(e: Exn) String {
    if (e.type.message) |message| return message(e);
    if (comptime exn_show) return anyText(e);
    return str(e.type.name);
}

/// `e.StackTrace`: null until the exception is thrown, then the captured frames.
pub fn exnStackTrace(e: Exn) String {
    // (with no capture there are no frames to write, and the field that holds them is void)
    return if (comptime stack_traces) traceText(e) else null;
}

pub fn traceText(e: Exn) String {
    if (!e.trace_thrown) return null;
    var aw: std.Io.Writer.Allocating = .init(rt.allocator);
    defer aw.deinit();
    const st: std.debug.StackTrace = .{
        .return_addresses = e.trace_addrs[0..e.trace_len],
        .skipped = if (e.trace_skipped) .unknown else .none,
    };
    std.debug.writeStackTrace(&st, .{ .writer = &aw.writer, .mode = .no_color }) catch {};
    const utf8 = aw.written();
    if (utf8.len == 0) return str("");
    var b: TextBuilder = .{};
    var i: usize = 0;
    while (i < utf8.len) {
        const n = std.unicode.utf8ByteSequenceLength(utf8[i]) catch {
            b.addOne(utf8[i]);
            i += 1;
            continue;
        };
        if (i + n > utf8.len) {
            b.addOne(utf8[i]);
            i += 1;
            continue;
        }
        const cp = std.unicode.utf8Decode(utf8[i .. i + n]) catch {
            b.addOne(utf8[i]);
            i += 1;
            continue;
        };
        if (cp <= 0xFFFF) {
            b.addOne(@intCast(cp));
        } else {
            const s = cp - 0x10000;
            b.addOne(@intCast(0xD800 + (s >> 10)));
            b.addOne(@intCast(0xDC00 + (s & 0x3FF)));
        }
        i += n;
    }
    return b.finish();
}

/// The module values of a file with tests, before the first test of it runs.
pub fn testInit(init: anytype) !void {
    const r = init();
    if (comptime isRaised(@TypeOf(r))) {
        r catch {
            uncaught();
            return error.TestFailed;
        };
    }
}

/// A test that `zig test` runs (an F# function marked `[<Fact>]`): it fails if it raises,
/// and the exception is written as an unhandled one would be.
/// A cell the runtime keeps for as long as the thread (a cache: the null array of a type, a
/// shared Random) is not counted as alive, so that what a program or a test leaves alive is
/// what it made; `recount` puts it back just before the runtime gives it up.
pub inline fn uncount() void {
    if (track) thread.stats.frees += 1;
}

pub inline fn recount() void {
    if (track) thread.stats.frees -= 1;
}

/// Before a test: what is alive (once cycles that died are freed), to compare after it.
pub fn testLiveBefore() i64 {
    _ = collect();
    return live();
}

/// After a test: every cell it made is freed (what it left waiting has run; cycles that died are
/// freed first). Only in builds that count cells.
pub fn testNoLeak(before: i64) !void {
    if (!track) return;
    asyncStateRelease();
    _ = collect();
    const now = live();
    if (now != before) {
        std.debug.print("fable: the test left {d} cell(s) alive\n", .{now - before});
        return error.TestLeaked;
    }
}

pub fn testCase(f: anytype) !void {
    const n = @typeInfo(@TypeOf(f)).@"fn".param_types.len;
    const r = if (n == 0) f() else f({});
    if (comptime isRaised(@TypeOf(r))) {
        if (r) |v| {
            drop(v);
        } else |_| {
            uncaught();
            return error.TestFailed;
        }
    } else drop(r);
}

/// The program's entry point let an exception escape: say which, and give it up.
pub fn uncaught() void {
    const e = take();
    const text = exnMessage(e);
    rt.write_err("Unhandled exception. ");
    rt.write_err(e.type.name);
    rt.write_err(": ");
    writeText(rt.write_err, text, true);
    drop(text);
    drop(e);
}
