//! The hand-written part of the Zig runtime library: reference-counted cells, reuse tokens,
//! the generic dup/drop/equality that generated code calls, and conversions between numbers.
//! The cycle collector will live here too.
const std = @import("std");
const builtin = @import("builtin");
pub const sgc = @import("fable_sgc.zig");

pub const interface_version: i32 = 8;

// ---------------------------------------------------------------------------------------------
// Cells
//
// A recursive union is a `union(enum)` whose cases with fields point to a cell:
//
//     pub const List = union(enum) {
//         Nil,
//         Cons: *struct { @"$rc": u32 = 1, head: i32, tail: List },
//     };
//
// The count is the first field and has a name no F# field can be given. Counts are not atomic:
// a value belongs to one thread.
// ---------------------------------------------------------------------------------------------

/// Where cells come from. A program may set this before it allocates anything.
pub var allocator: std.mem.Allocator = if (builtin.link_libc)
    std.heap.c_allocator
else if (builtin.single_threaded)
    std.heap.page_allocator
else
    std.heap.smp_allocator;

/// Counters are kept in Debug and ReleaseSafe builds only.
pub const track = std.debug.runtime_safety;

pub const Stats = struct {
    allocs: i64 = 0,
    frees: i64 = 0,
    reuses: i64 = 0,
    dups: i64 = 0,
    decs: i64 = 0,
};
pub var stats: Stats = .{};

/// The cell type of one case of a recursive union.
pub fn Cell(comptime T: type, comptime tag: std.meta.Tag(T)) type {
    return @typeInfo(@FieldType(T, @tagName(tag))).pointer.child;
}

/// A new cell with a count of one.
pub inline fn cell(comptime T: type, comptime tag: std.meta.Tag(T), init: Cell(T, tag)) *Cell(T, tag) {
    const C = Cell(T, tag);
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) stats.allocs += 1;
    return c;
}

/// Reuse: build in the dead cell that `tok` holds, if it holds one; allocate otherwise.
pub inline fn cellReuse(comptime T: type, comptime tag: std.meta.Tag(T), tok: anytype, init: Cell(T, tag)) *Cell(T, tag) {
    const C = Cell(T, tag);
    const Dead = @typeInfo(@typeInfo(@TypeOf(tok)).pointer.child).optional.child;
    // (In generic code the dead cell and the new one are the same case of one generic type,
    // with type arguments that may differ. Only when they turn out to have one layout is the
    // dead cell built in; otherwise the token is left alone and its owner frees the cell.)
    if (comptime (@sizeOf(@typeInfo(Dead).pointer.child) == @sizeOf(C) and @alignOf(@typeInfo(Dead).pointer.child) == @alignOf(C))) {
        if (tok.*) |p| {
            tok.* = null;
            const c: *C = @ptrCast(@alignCast(p));
            c.* = init;
            if (comptime hasGc(C)) {
                // (a cell that is built in again is a new cell: it gets an age of its own)
                collector.allocs += 1;
                c.@"$gc" = gcHeader(C, c);
            }
            if (track) stats.reuses += 1;
            return c;
        }
    }
    return cell(T, tag, init);
}

pub inline fn isUnique(c: anytype) bool {
    return c.@"$rc" == 1;
}

pub inline fn retain(c: anytype) void {
    c.@"$rc" += 1;
    if (track) stats.dups += 1;
    if (gcOf(c)) |h| collector.onRetain(h);
}

/// Take one reference off a cell that is known to be shared.
pub inline fn release(c: anytype) void {
    c.@"$rc" -= 1;
    if (track) stats.decs += 1;
    if (gcOf(c)) |h| collector.onRelease(h);
}

/// Take one reference off; true when it was the last one, and the caller gives up what the
/// cell holds and frees it. (False also when the cell's whole structure died with this
/// reference: the collector frees all of it, this cell included.)
pub inline fn releaseIsLast(c: anytype) bool {
    if (c.@"$rc" != 1) {
        c.@"$rc" -= 1;
        if (track) stats.decs += 1;
        if (gcOf(c)) |h| collector.onRelease(h);
        return false;
    }
    if (gcOf(c)) |h| return !collector.onZero(h);
    return true;
}

/// A cell that is not shared is taken apart without its count going to zero: its fields are
/// about to be moved out or given up.
pub inline fn forget(c: anytype) void {
    if (gcOf(c)) |h| collector.onFree(h);
}

/// A reference left a cell that is being taken apart and went to a variable as it is.
pub inline fn touch(x: anytype) void {
    eachHdr(x, {}, movedOut);
}

fn movedOut(_: void, h: *sgc.Hdr) void {
    collector.onMoveOut(h);
}

pub inline fn free(c: anytype) void {
    if (track) stats.frees += 1;
    allocator.destroy(c);
}

/// The count and the collector's header are not part of what a cell holds.
fn isCount(comptime field_name: []const u8) bool {
    return std.mem.eql(u8, field_name, "$rc") or std.mem.eql(u8, field_name, "$gc");
}

fn isCellPtr(comptime T: type) bool {
    const info = @typeInfo(T);
    if (info != .pointer or info.pointer.size != .one) return false;
    const C = info.pointer.child;
    return @typeInfo(C) == .@"struct" and @hasField(C, "$rc");
}

/// Does a value of this type hold references to cells? (Does not look through a cell.)
pub fn isManaged(comptime T: type) bool {
    if (isCellPtr(T)) return true;
    if (comptime isFunc(T)) return true;
    switch (@typeInfo(T)) {
        .optional => |o| return isManaged(o.child),
        .@"struct" => |s| {
            inline for (s.field_types) |F| {
                if (isManaged(F)) return true;
            }
            return false;
        },
        .@"union" => |u| {
            inline for (u.field_types) |F| {
                if (isManaged(F)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// A union whose cases are cells: the handle of a recursive union.
fn isHeapUnion(comptime T: type) bool {
    switch (@typeInfo(T)) {
        .@"union" => |u| {
            inline for (u.field_types) |F| {
                if (isCellPtr(F)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// Make a borrowed value an owned one: one more reference to every cell it points to directly.
pub inline fn dup(x: anytype) @TypeOf(x) {
    retainAll(x);
    return x;
}

fn retainAll(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        if (x.env) |e| retain(e);
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => retain(x),
        .optional => if (x) |v| retainAll(v),
        .@"struct" => |s| inline for (s.field_names) |name| retainAll(@field(x, name)),
        .@"union" => switch (x) {
            inline else => |p| retainAll(p),
        },
        else => comptime unreachable,
    }
}

/// Give up an owned value: take one reference off every cell it points to directly, and free
/// the cells that were not shared, giving up what they hold.
pub fn drop(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (releaseIsLast(e)) e.destroy(e);
        }
        return;
    }
    if (T == Exn) {
        if (releaseIsLast(x)) x.type.destroy(x);
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => dropRecord(T, x),
        .optional => if (x) |v| drop(v),
        .@"struct" => |s| inline for (s.field_names) |name| drop(@field(x, name)),
        .@"union" => if (comptime isHeapUnion(T)) dropHeap(T, x) else switch (x) {
            inline else => |p| drop(p),
        },
        else => comptime unreachable,
    }
}

/// The last field of a cell that has the union's own type is followed in a loop, so giving up
/// a long list (or the right spine of a tree) does not use stack in proportion to its length.
fn dropHeap(comptime T: type, x: T) void {
    var cur = x;
    while (true) {
        switch (cur) {
            inline else => |c| {
                if (@TypeOf(c) == void) {
                    return;
                } else {
                    if (!releaseIsLast(c)) return;
                    const info = @typeInfo(@TypeOf(c.*)).@"struct";
                    const self_field: ?usize = comptime blk: {
                        var found: ?usize = null;
                        for (info.field_types, 0..) |F, i| {
                            if (F == T) found = i;
                        }
                        break :blk found;
                    };
                    inline for (info.field_names, 0..) |name, i| {
                        if (comptime !isCount(name) and (self_field == null or self_field.? != i)) {
                            drop(@field(c, name));
                        }
                    }
                    if (self_field) |i| {
                        const next: T = @field(c, info.field_names[i]);
                        free(c);
                        cur = next;
                    } else {
                        free(c);
                        return;
                    }
                }
            },
        }
    }
}

/// A reference record. Its last field of the record's own type (or an option of it) is
/// followed in a loop, so giving up a long chain of records does not use stack in proportion
/// to its length.
fn dropRecord(comptime P: type, x: P) void {
    const info = @typeInfo(@typeInfo(P).pointer.child).@"struct";
    const self_field: ?usize = comptime blk: {
        var found: ?usize = null;
        for (info.field_types, 0..) |F, i| {
            if (F == P or F == ?P) found = i;
        }
        break :blk found;
    };
    var cur = x;
    while (true) {
        if (!releaseIsLast(cur)) return;
        inline for (info.field_names, 0..) |name, i| {
            if (comptime !isCount(name) and (self_field == null or self_field.? != i)) {
                drop(@field(cur, name));
            }
        }
        if (self_field) |i| {
            const next: ?P = @field(cur, info.field_names[i]);
            free(cur);
            cur = next orelse return;
        } else {
            free(cur);
            return;
        }
    }
}

/// Structural equality, as F#'s `=` on records, unions, tuples and options.
pub fn eql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (comptime !isManaged(T)) return std.meta.eql(a, b);
    if (comptime isFunc(T)) @compileError("function values cannot be compared");
    if (T == Exn) return a == b;
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (a == b) return true;
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name)) {
                    if (!eql(@field(a, name), @field(b, name))) return false;
                }
            }
            return true;
        },
        .optional => {
            if (a) |x| {
                if (b) |y| return eql(x, y);
                return false;
            }
            return b == null;
        },
        .@"struct" => |s| {
            inline for (s.field_names) |name| {
                if (!eql(@field(a, name), @field(b, name))) return false;
            }
            return true;
        },
        .@"union" => {
            if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
            switch (a) {
                inline else => |pa, tag| return eql(pa, @field(b, @tagName(tag))),
            }
        },
        else => comptime unreachable,
    }
}

/// A new reference record (a record with mutable fields, or one that contains itself): a
/// pointer to a counted cell that holds the fields.
pub inline fn new(comptime P: type, init: @typeInfo(P).pointer.child) P {
    const C = @typeInfo(P).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) stats.allocs += 1;
    return c;
}

/// Store into a variable or a field of a plain value that owns what it holds: the old value
/// is given up once the new one is in place.
pub inline fn store(place: anytype, value: @TypeOf(place.*)) void {
    const old = place.*;
    place.* = value;
    drop(old);
}

/// Store into a field of a reference record. The collector is told what the record no longer
/// points at and what it points at now: this is where a cycle can be closed.
pub inline fn storeIn(owner: anytype, comptime field: []const u8, value: @FieldType(@TypeOf(owner.*), field)) void {
    const old = @field(owner, field);
    @field(owner, field) = value;
    if (gcOf(owner)) |h| {
        eachHdr(old, h, unstored);
        eachHdr(value, h, stored);
    } else {
        touch(value);
    }
    drop(old);
}

fn unstored(owner: *sgc.Hdr, old: *sgc.Hdr) void {
    collector.onUnstore(owner, old);
}

fn stored(owner: *sgc.Hdr, child: *sgc.Hdr) void {
    collector.onStore(owner, child);
}

/// F#'s `ref` cell.
pub fn Ref(comptime T: type) type {
    return *struct {
        pub const fable_cyclic = holdsCyclic(T);
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        contents: T,
    };
}

/// F#'s list.
pub fn List(comptime T: type) type {
    return union(enum) {
        pub const fable_cyclic = holdsCyclic(T);
        Empty,
        Cons: *struct { @"$rc": u32 = 1, @"$gc": GcHdr(fable_cyclic) = undefined, Head: T, Tail: List(T) },
    };
}

// ---------------------------------------------------------------------------------------------
// Cycles
//
// Reference counting alone never frees a structure that reaches itself. A structure can only
// do that through a field that is assigned after the cell was made, so most types cannot be
// part of a cycle at all, and their cells are exactly as above. The cells of the types that
// can (the compiler works out which) carry a header of the collector, `$gc`, next to their
// count. The collector (fable_sgc.zig) keeps one count per connected group of such cells: the
// references to its cells that are not held in a field of one of them. When that count
// reaches zero the whole group is dead, cycles included, and is freed.
//
// What the collector has to be told is all in this file: a cell is made, retained, released,
// taken apart, and a field of it is assigned. Generated code does not call the collector.
// ---------------------------------------------------------------------------------------------

/// A test mode: before every allocation of a cell with a collector header, every structure's
/// count is checked against the cells and what they point at. A program turns it on with
/// `pub const fable_verify_cycles = true;` in its root file. Very slow.
const verify_cycles: bool = if (@hasDecl(@import("root"), "fable_verify_cycles")) @import("root").fable_verify_cycles else false;

var collector: sgc.Gc = undefined;
var collector_ready: bool = false;

/// The type of a cell's `$gc` field: the collector's header, or nothing.
pub fn GcHdr(comptime cyclic: bool) type {
    return if (cyclic) sgc.Hdr else void;
}

fn hasGc(comptime C: type) bool {
    return @hasField(C, "$gc") and @FieldType(C, "$gc") == sgc.Hdr;
}

/// The collector's header of a cell, if it has one. An environment and an exception say so
/// themselves (their type does not show what they hold); for any other cell it is in its type.
inline fn gcOf(c: anytype) ?*sgc.Hdr {
    const C = @TypeOf(c.*);
    if (C == Env or C == ExnHeader) return c.gc;
    if (comptime hasGc(C)) return &c.@"$gc";
    return null;
}

/// Does a value of this type hold, directly, a reference to a cell that can be part of a
/// cycle? A function value and an exception count: what they hold is not in their type.
/// (Only declarations are looked at, never fields of cells: this is evaluated while the types
/// that ask are still being put together.)
pub fn holdsCyclic(comptime T: type) bool {
    if (T == Exn) return true;
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (p.size != .one or @typeInfo(p.child) != .@"struct") return false;
            return @hasDecl(p.child, "fable_cyclic") and p.child.fable_cyclic;
        },
        .optional => |o| return holdsCyclic(o.child),
        .@"struct" => |s| {
            if (@hasDecl(T, "fable_func")) return true;
            inline for (s.field_types) |F| {
                if (holdsCyclic(F)) return true;
            }
            return false;
        },
        .@"union" => |u| {
            if (@hasDecl(T, "fable_cyclic")) return T.fable_cyclic;
            inline for (u.field_types) |F| {
                if (holdsCyclic(F)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// Call `f(ctx, header)` for every cell with a collector header that `x` refers to directly.
fn eachHdr(x: anytype, ctx: anytype, comptime f: anytype) void {
    const T = @TypeOf(x);
    if (comptime !holdsCyclic(T)) return;
    if (T == Exn) {
        if (x.gc) |h| f(ctx, h);
        return;
    }
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (e.gc) |h| f(ctx, h);
        }
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => f(ctx, &x.@"$gc"),
        .optional => if (x) |v| eachHdr(v, ctx, f),
        .@"struct" => |s| inline for (s.field_names) |name| eachHdr(@field(x, name), ctx, f),
        .@"union" => switch (x) {
            inline else => |p| {
                if (comptime isCellPtr(@TypeOf(p))) {
                    if (comptime hasGc(@TypeOf(p.*))) f(ctx, &p.@"$gc");
                } else {
                    eachHdr(p, ctx, f);
                }
            },
        },
        else => comptime unreachable,
    }
}

/// Give up what a dead cell holds, except its references to cells that are going away with it.
fn dropOutside(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime !holdsCyclic(T)) return drop(x);
    if (T == Exn) {
        if (x.gc) |h| {
            if (sgc.isGarbage(h)) return;
        }
        return drop(x);
    }
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (e.gc) |h| {
                if (sgc.isGarbage(h)) return;
            }
        }
        return drop(x);
    }
    switch (@typeInfo(T)) {
        .pointer => if (!sgc.isGarbage(&x.@"$gc")) drop(x),
        .optional => if (x) |v| dropOutside(v),
        .@"struct" => |s| inline for (s.field_names) |name| dropOutside(@field(x, name)),
        .@"union" => switch (x) {
            inline else => |p| {
                if (comptime isCellPtr(@TypeOf(p))) {
                    if (comptime hasGc(@TypeOf(p.*))) {
                        if (!sgc.isGarbage(&p.@"$gc")) drop(x);
                    } else {
                        drop(x);
                    }
                } else {
                    dropOutside(p);
                }
            },
        },
        else => comptime unreachable,
    }
}

fn visit(v: *sgc.Visitor, h: *sgc.Hdr) void {
    v.visit(h);
}

fn countOne(n: *usize, _: *sgc.Hdr) void {
    n.* += 1;
}

/// What the collector needs to know about one type of cell `C`: where its count is, which
/// cells it refers to, and how to give up what it holds and free it. `gc_field` is the
/// collector's header in `C`; `payload` is the field that holds everything else (all fields
/// but the count and the header when it is null).
fn Collected(comptime C: type, comptime gc_field: []const u8, comptime rc_offset: isize, comptime payload: ?[]const u8) type {
    return struct {
        inline fn cellOf(n: *sgc.Hdr) *C {
            return @alignCast(@fieldParentPtr(gc_field, n));
        }

        fn trace(n: *sgc.Hdr, v: *sgc.Visitor) void {
            const c = cellOf(n);
            if (payload) |p| {
                eachHdr(@field(c, p), v, visit);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), v, visit);
            }
        }

        fn releaseOutside(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                dropOutside(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) dropOutside(@field(c, name));
            }
        }

        fn freeCell(n: *sgc.Hdr, _: ?*anyopaque) void {
            free(cellOf(n));
        }

        fn finalize(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                drop(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) drop(@field(c, name));
            }
            free(c);
        }

        /// Is the cell being made without a reference to a cell that can be part of a cycle?
        fn isLeaf(c: *const C) bool {
            var n: usize = 0;
            if (payload) |p| {
                eachHdr(@field(c, p), &n, countOne);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), &n, countOne);
            }
            return n == 0;
        }

        const desc: sgc.Desc = .{
            .rc_offset = rc_offset,
            .trace = trace,
            .release_outside = releaseOutside,
            .free = freeCell,
            .finalize = finalize,
        };
    };
}

noinline fn collectorSetup() void {
    collector.init(.{}, null, allocator);
    collector_ready = true;
}

/// Before a cell with a collector header is allocated (its field values are computed by
/// then): the only place where the collector does work of its own accord.
inline fn gcTick() void {
    if (!collector_ready) collectorSetup();
    if (verify_cycles) collector.verify();
    if (collector.tickDue()) collector.tickSlow();
}

/// The header of a new cell of a recursive union or of a reference record.
inline fn gcHeader(comptime C: type, c: *const C) sgc.Hdr {
    const K = Collected(C, "$gc", @as(isize, @offsetOf(C, "$rc")) - @as(isize, @offsetOf(C, "$gc")), null);
    return collector.hdr(&K.desc, K.isLeaf(c));
}

/// Free every cycle that is dead now. Returns how many cells that freed.
pub fn collect() i64 {
    if (!collector_ready) return 0;
    return @intCast(collector.collectAll());
}

/// Give back the collector's own bookkeeping. Nothing it looks after may be alive.
pub fn collectorDeinit() void {
    if (collector_ready) collector.deinit();
}

/// The collector's counters (see fable_sgc.zig), or null if no cell ever needed it.
pub fn collectorCounters() ?sgc.Counters {
    return if (collector_ready) collector.counters else null;
}

/// How a call that ends a function is made when the caller and the callee have the same
/// parameter and result types: as a jump, where the compiler backend can guarantee one.
pub const tail_call: std.builtin.CallModifier = if (builtin.zig_backend == .stage2_llvm and switch (builtin.cpu.arch) {
    .wasm32, .wasm64 => false,
    else => true,
}) .always_tail else .auto;

// ---------------------------------------------------------------------------------------------
// Function values
//
// A function value is a pointer to code and a pointer to the values the code captured:
//
//     fable_rt.Func(*const fn (?*fable_rt.Env, i32) i32)
//
// The code takes the environment first. It owns its other arguments and its result; what it
// captured stays owned by the environment, which is reference counted and frees the captures
// with itself. A function that captures nothing has no environment.
// ---------------------------------------------------------------------------------------------

/// The start of every environment.
pub const Env = struct {
    @"$rc": u32 = 1,
    /// the collector's header of this environment, if what it captured can be part of a cycle
    gc: ?*sgc.Hdr = null,
    destroy: *const fn (*Env) void,
};

pub fn Func(comptime Code: type) type {
    return struct {
        pub const fable_func = {};
        env: ?*Env,
        code: Code,
    };
}

fn isFunc(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_func");
}

fn EnvOf(comptime Captures: type) type {
    return struct {
        const Self = @This();
        const cyclic = holdsCyclic(Captures);
        const K = Collected(
            Self,
            "hdr",
            @as(isize, @offsetOf(Self, "header")) + @as(isize, @offsetOf(Env, "$rc")) - @as(isize, @offsetOf(Self, "hdr")),
            "captures",
        );

        header: Env,
        hdr: GcHdr(cyclic) = undefined,
        captures: Captures,

        fn destroy(header: *Env) void {
            const self: *Self = @fieldParentPtr("header", header);
            drop(self.captures);
            free(self);
        }
    };
}

/// A function value that owns `captures`.
pub inline fn closure(comptime F: type, comptime Captures: type, captures: Captures, code: @FieldType(F, "code")) F {
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = allocator.create(E) catch @panic("fable: out of memory");
    e.* = .{ .header = .{ .destroy = E.destroy }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) stats.allocs += 1;
    return .{ .env = &e.header, .code = code };
}

/// What the function value captured, from inside its code.
pub inline fn captured(comptime Captures: type, env: ?*Env) *const Captures {
    const e: *EnvOf(Captures) = @fieldParentPtr("header", env.?);
    return &e.captures;
}

// ---------------------------------------------------------------------------------------------
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
};

pub const ExnHeader = struct {
    @"$rc": u32 = 1,
    /// the collector's header of this exception, if what it holds can be part of a cycle
    gc: ?*sgc.Hdr = null,
    type: *const ExnType,
};

/// F#'s `exn`.
pub const Exn = *ExnHeader;

/// An F# `exception` declaration with the given fields.
pub fn ExnOf(comptime name: []const u8, comptime Payload: type) type {
    return struct {
        const cyclic = holdsCyclic(Payload);
        const Whole = struct { header: ExnHeader, hdr: GcHdr(cyclic) = undefined, payload: Payload };
        const K = Collected(
            Whole,
            "hdr",
            @as(isize, @offsetOf(Whole, "header")) + @as(isize, @offsetOf(ExnHeader, "$rc")) - @as(isize, @offsetOf(Whole, "hdr")),
            "payload",
        );

        pub const info: ExnType = .{ .name = name, .destroy = destroy };

        pub fn new(payload: Payload) Exn {
            if (comptime cyclic) gcTick();
            const c = allocator.create(Whole) catch @panic("fable: out of memory");
            c.* = .{ .header = .{ .type = &info }, .payload = payload };
            if (comptime cyclic) {
                c.hdr = collector.hdr(&K.desc, K.isLeaf(c));
                c.header.gc = &c.hdr;
            }
            if (track) stats.allocs += 1;
            return &c.header;
        }

        /// Is `e` an exception of this type?
        pub inline fn is(e: Exn) bool {
            return e.type == &info;
        }

        /// The fields of an exception of this type.
        pub inline fn of(e: Exn) *const Payload {
            const c: *Whole = @fieldParentPtr("header", e);
            return &c.payload;
        }

        fn destroy(e: Exn) void {
            const c: *Whole = @fieldParentPtr("header", e);
            drop(c.payload);
            free(c);
        }
    };
}

/// The exception in flight.
var current: ?Exn = null;

pub fn throw(e: Exn) void {
    std.debug.assert(current == null);
    current = e;
}

pub fn take() Exn {
    const e = current.?;
    current = null;
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

/// The program's entry point let an exception escape: say which, and give it up.
pub fn uncaught() void {
    const e = take();
    std.debug.print("Unhandled exception: {s}\n", .{e.type.name});
    drop(e);
}

// ---------------------------------------------------------------------------------------------
// Calls between files
//
// A file is compiled without knowing what the functions of other files were inferred to
// borrow. So the callee's file states it, as a constant next to the function:
//
//     pub const @"sumList$sig" = .{ .borrows = .{true}, .result_borrowed = false };
//
// and the caller's file says what it does with each argument: `.keep` (it uses the value
// again), `.give` (this was its last use) or `.plain` (not a managed value). `across` puts
// the two together when the program is compiled, so the call costs what it would cost if
// both functions were in one file.
// ---------------------------------------------------------------------------------------------

pub const Use = enum { plain, keep, give };

pub inline fn across(
    comptime f: anytype,
    comptime sig: anytype,
    comptime uses: anytype,
    args: anytype,
) @typeInfo(@TypeOf(f)).@"fn".return_type.? {
    var a: std.meta.ArgsTuple(@TypeOf(f)) = undefined;
    inline for (uses, 0..) |use, i| {
        const u: Use = use;
        // the callee takes ownership, the caller keeps using the value: one more reference
        a[i] = if (u == .keep and !sig.borrows[i]) dup(args[i]) else args[i];
    }
    const raw = @call(.auto, f, a);
    // (If the callee raised, it has given up what it owned; what it only borrowed and the caller
    // was done with is given up here, and the caller goes on unwinding.)
    const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
        inline for (uses, 0..) |use, i| {
            const u: Use = use;
            if (u == .give and sig.borrows[i]) drop(args[i]);
        }
        return err;
    } else raw;
    // (a borrowed result may be part of an argument: it is made owned before they are given up)
    const result = if (sig.result_borrowed) dup(r) else r;
    inline for (uses, 0..) |use, i| {
        const u: Use = use;
        // the callee only borrowed what the caller was done with: the caller gives it up
        if (u == .give and sig.borrows[i]) drop(args[i]);
    }
    return result;
}

/// Cells that were allocated and not freed (0 when counters are not kept).
pub fn live() i64 {
    return stats.allocs - stats.frees;
}

/// Called when the program's entry point has returned: true, with a message, if cells are
/// still allocated. Only checks in builds that keep counters.
pub fn leaked() bool {
    // (cycles that died without anything noticing yet are not leaks)
    _ = collect();
    if (!track or live() == 0) return false;
    std.debug.print("fable: {d} cell(s) were never freed (allocated {d}, freed {d})\n", .{ live(), stats.allocs, stats.frees });
    return true;
}

// ---------------------------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------------------------

/// A conversion between number types with the result .NET gives:
/// - integer to integer keeps the low bits (sign- or zero-extending the source first);
/// - float to integer truncates toward zero, saturates at the target's limits, NaN is 0;
/// - integer to float and float to float round to nearest.
pub fn conv(comptime To: type, x: anytype) To {
    const From = @TypeOf(x);
    switch (@typeInfo(To)) {
        .int => |to| switch (@typeInfo(From)) {
            .int => |from| {
                const bits = @max(to.bits, from.bits);
                const WideFrom = @Int(from.signedness, bits);
                const WideTo = @Int(to.signedness, bits);
                return @truncate(@as(WideTo, @bitCast(@as(WideFrom, x))));
            },
            .float => {
                if (std.math.isNan(x)) return 0;
                const t = @trunc(x);
                if (t >= @as(From, @floatFromInt(std.math.maxInt(To)))) return std.math.maxInt(To);
                if (t <= @as(From, @floatFromInt(std.math.minInt(To)))) return std.math.minInt(To);
                return @intFromFloat(t);
            },
            .comptime_int, .comptime_float => return x,
            else => @compileError("conv: unsupported source type " ++ @typeName(From)),
        },
        .float => switch (@typeInfo(From)) {
            .int => return @floatFromInt(x),
            .float => return @floatCast(x),
            .comptime_int, .comptime_float => return x,
            else => @compileError("conv: unsupported source type " ++ @typeName(From)),
        },
        else => @compileError("conv: unsupported target type " ++ @typeName(To)),
    }
}

// ---------------------------------------------------------------------------------------------
// Tests (`zig test fable_rt.zig`)
// ---------------------------------------------------------------------------------------------

const TestList = union(enum) {
    Nil,
    Cons: *struct { @"$rc": u32 = 1, head: i32, tail: TestList },
};

const TestTree = union(enum) {
    Leaf,
    Node: *struct { @"$rc": u32 = 1, left: TestTree, value: i32, right: TestTree },
};

const TestPair = struct { first: TestList, second: ?TestList, n: i32 };

fn testCons(head: i32, tail: TestList) TestList {
    return .{ .Cons = cell(TestList, .Cons, .{ .head = head, .tail = tail }) };
}

fn testRange(n: i32) TestList {
    var l: TestList = .Nil;
    var i: i32 = n;
    while (i > 0) : (i -= 1) l = testCons(i, l);
    return l;
}

fn testTree(depth: i32) TestTree {
    if (depth == 0) return .Leaf;
    return .{ .Node = cell(TestTree, .Node, .{ .left = testTree(depth - 1), .value = depth, .right = testTree(depth - 1) }) };
}

test "a dropped list frees every cell, without recursion" {
    const before = stats;
    drop(testRange(1_000_000));
    try std.testing.expectEqual(@as(i64, 1_000_000), stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 1_000_000), stats.frees - before.frees);
}

test "a shared cell is freed by its last owner" {
    const before = stats;
    const tail = testRange(3);
    const a = testCons(10, dup(tail));
    const b = testCons(20, tail);
    drop(a);
    try std.testing.expectEqual(@as(i64, 1), stats.frees - before.frees);
    try std.testing.expectEqual(@as(i32, 1), b.Cons.tail.Cons.head);
    drop(b);
    try std.testing.expectEqual(@as(i64, 5), stats.frees - before.frees);
}

test "trees, and values that hold cells" {
    const before = stats;
    drop(testTree(10));
    try std.testing.expectEqual(@as(i64, 1023), stats.frees - before.frees);
    const p = TestPair{ .first = testRange(2), .second = testRange(3), .n = 1 };
    const q = dup(p);
    drop(p);
    try std.testing.expectEqual(@as(i64, 1023), stats.frees - before.frees);
    drop(q);
    try std.testing.expectEqual(@as(i64, 1028), stats.frees - before.frees);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
}

test "a dead cell is built in again" {
    const before = stats;
    const l = testRange(1);
    var tok: ?*Cell(TestList, .Cons) = null;
    if (isUnique(l.Cons)) tok = l.Cons;
    const m = TestList{ .Cons = cellReuse(TestList, .Cons, &tok, .{ .head = 7, .tail = .Nil }) };
    try std.testing.expectEqual(l.Cons, m.Cons);
    try std.testing.expectEqual(@as(i64, 1), stats.reuses - before.reuses);
    try std.testing.expectEqual(@as(i64, 1), stats.allocs - before.allocs);
    drop(m);
}

test "structural equality looks through cells" {
    const a = testRange(4);
    const b = testRange(4);
    const c = testRange(5);
    try std.testing.expect(eql(a, b));
    try std.testing.expect(!eql(a, c));
    try std.testing.expect(eql(TestPair{ .first = a, .second = null, .n = 1 }, TestPair{ .first = b, .second = null, .n = 1 }));
    try std.testing.expect(!eql(TestPair{ .first = a, .second = c, .n = 1 }, TestPair{ .first = b, .second = null, .n = 1 }));
    try std.testing.expect(eql(@as(?TestList, a), @as(?TestList, b)));
    drop(a);
    drop(b);
    drop(c);
}

fn testSum(xs: TestList) i32 {
    var total: i32 = 0;
    var cur = xs;
    while (cur == .Cons) : (cur = cur.Cons.tail) total += cur.Cons.head;
    return total;
}
const testSum_sig = .{ .borrows = .{true}, .result_borrowed = false };

fn testTail(xs: TestList) TestList {
    return if (xs == .Cons) xs.Cons.tail else .Nil;
}
const testTail_sig = .{ .borrows = .{true}, .result_borrowed = true };

fn testPush(n: i32, xs: TestList) TestList {
    return testCons(n, xs);
}
const testPush_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

test "a call between files costs what the callee needs" {
    const before = stats;
    const xs = testRange(3);
    // borrowed by the callee, kept by the caller: nothing is counted
    try std.testing.expectEqual(@as(i32, 6), across(testSum, testSum_sig, .{.keep}, .{xs}));
    try std.testing.expectEqual(@as(i64, 0), stats.dups - before.dups);
    // a borrowed result is made owned
    const t = across(testTail, testTail_sig, .{.keep}, .{xs});
    try std.testing.expectEqual(@as(i64, 1), stats.dups - before.dups);
    // owned by the callee, kept by the caller: one more reference
    const ys = across(testPush, testPush_sig, .{ .plain, .keep }, .{ 0, xs });
    try std.testing.expectEqual(@as(i64, 2), stats.dups - before.dups);
    // owned by the callee, given by the caller: a move
    const zs = across(testPush, testPush_sig, .{ .plain, .give }, .{ 9, ys });
    try std.testing.expectEqual(@as(i64, 2), stats.dups - before.dups);
    // borrowed by the callee, given by the caller: the caller gives it up after the call
    try std.testing.expectEqual(@as(i32, 15), across(testSum, testSum_sig, .{.give}, .{zs}));
    try std.testing.expectEqual(@as(i32, 5), across(testSum, testSum_sig, .{.give}, .{t}));
    drop(xs);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
}

const TestFn = Func(*const fn (?*Env, i32) i32);
const TestCaptures = struct { xs: TestList, n: i32 };

fn testAddSum(env: ?*Env, x: i32) i32 {
    const c = captured(TestCaptures, env);
    return x + c.n + testSum(c.xs);
}

fn testDouble(_: ?*Env, x: i32) i32 {
    return x * 2;
}

test "a function value owns what it captured" {
    const before = stats;
    const f = closure(TestFn, TestCaptures, .{ .xs = testRange(3), .n = 10 }, testAddSum);
    try std.testing.expectEqual(@as(i32, 17), f.code(f.env, 1));
    const g = dup(f);
    drop(f);
    try std.testing.expectEqual(@as(i32, 18), g.code(g.env, 2));
    const plain = TestFn{ .env = null, .code = testDouble };
    try std.testing.expectEqual(@as(i32, 8), plain.code(plain.env, 4));
    drop(dup(plain));
    // in a value that is dropped as a whole
    const pair: struct { f: TestFn, o: ?TestFn } = .{ .f = g, .o = plain };
    drop(pair);
    try std.testing.expectEqual(@as(i64, 4), stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 4), stats.frees - before.frees);
}

const TestParseError = ExnOf("ParseError", struct { pos: i32, items: TestList });
const TestOverflow = ExnOf("Overflow", struct { limit: i32 });

fn testCheck(x: i32, owned: TestList) Raised!i32 {
    if (x < 0) {
        throw(TestParseError.new(.{ .pos = x, .items = owned }));
        return error.Raised;
    }
    drop(owned);
    return x;
}
const testCheck_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

fn testOuter(x: i32) MayRaise(i32, .{testCheck}) {
    const xs = testRange(2);
    const raw = across(testCheck, testCheck_sig, .{ .plain, .give }, .{ x, xs });
    const r = if (comptime isRaised(@TypeOf(raw))) (raw catch return error.Raised) else raw;
    return r + 1;
}

fn testPlain(x: i32) MayRaise(i32, .{testSum}) {
    return x;
}

test "an exception owns its fields and is taken by one handler" {
    const before = stats;
    try std.testing.expectEqual(@as(i32, 6), try testOuter(5));
    try std.testing.expectError(error.Raised, testOuter(-3));
    const e = take();
    try std.testing.expect(TestParseError.is(e));
    try std.testing.expect(!TestOverflow.is(e));
    try std.testing.expectEqual(@as(i32, -3), TestParseError.of(e).pos);
    try std.testing.expectEqual(@as(i32, 3), testSum(TestParseError.of(e).items));
    const again = dup(e);
    drop(e);
    drop(again);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
    // a function that calls nothing that raises has a plain result
    try std.testing.expect(@TypeOf(testPlain(1)) == i32);
    try std.testing.expect(@TypeOf(testOuter(1)) == Raised!i32);
}

const TestNode = *struct { @"$rc": u32 = 1, id: i32, next: ?TestNode };

test "reference records: identity, stores and long chains" {
    const before = stats;
    var head: TestNode = new(TestNode, .{ .id = 0, .next = null });
    var i: i32 = 1;
    while (i < 200_000) : (i += 1) head = new(TestNode, .{ .id = i, .next = head });
    const second = dup(head.next.?);
    // the field gets a new value: the old one stays alive through `second`
    store(&head.next, null);
    try std.testing.expectEqual(@as(i32, 199_998), second.id);
    const box = new(Ref(TestList), .{ .contents = testRange(3) });
    const alias = dup(box);
    store(&alias.contents, testRange(5));
    try std.testing.expectEqual(@as(i32, 15), testSum(box.contents));
    try std.testing.expect(eql(box, alias));
    drop(head);
    drop(second);
    drop(box);
    drop(alias);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
}

const TestPerson = *struct {
    pub const fable_cyclic = true;
    @"$rc": u32 = 1,
    @"$gc": GcHdr(fable_cyclic) = undefined,
    id: i32,
    friend: ?TestPerson,
    friends: List(TestPerson),
    callback: ?Func(*const fn (?*Env, i32) Raised!i32),
};

fn testPerson(id: i32) TestPerson {
    return new(TestPerson, .{ .id = id, .friend = null, .friends = .Empty, .callback = null });
}

const TestSelf = struct { self: TestPerson };

fn testAddId(env: ?*Env, x: i32) Raised!i32 {
    return x + captured(TestSelf, env).self.id;
}

test "cycles are freed when their last outside reference goes" {
    const before = stats;
    // two records that point at each other
    const a = testPerson(1);
    const b = testPerson(2);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(a));
    drop(a);
    try std.testing.expectEqual(@as(i64, 0), stats.frees - before.frees);
    drop(b);
    try std.testing.expectEqual(@as(i64, 2), stats.frees - before.frees);
    // a record that reaches itself through a list
    const c = testPerson(3);
    const cons = List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = dup(c), .Tail = .Empty }) };
    storeIn(c, "friends", cons);
    drop(c);
    try std.testing.expectEqual(@as(i64, 4), stats.frees - before.frees);
    // a record that holds a function which captured the record
    const d = testPerson(40);
    const f = closure(Func(*const fn (?*Env, i32) Raised!i32), TestSelf, .{ .self = dup(d) }, testAddId);
    storeIn(d, "callback", f);
    try std.testing.expectEqual(@as(i32, 42), try d.callback.?.code(d.callback.?.env, 2));
    drop(d);
    try std.testing.expectEqual(@as(i64, 6), stats.frees - before.frees);
    // a ring with a tail hanging off it, cut loose in the middle of a structure that lives on
    const keep = testPerson(5);
    const x = testPerson(6);
    const y = testPerson(7);
    storeIn(x, "friend", dup(y));
    storeIn(y, "friend", dup(x));
    storeIn(keep, "friend", x);
    drop(y);
    storeIn(keep, "friend", null);
    _ = collect();
    try std.testing.expectEqual(@as(i64, 8), stats.frees - before.frees);
    drop(keep);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
    // cells of the same types that never form a cycle are plain reference counting
    const lone = testPerson(8);
    storeIn(lone, "friends", List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = testPerson(9), .Tail = .Empty }) });
    drop(lone);
    try std.testing.expectEqual(stats.allocs - before.allocs, stats.frees - before.frees);
    try std.testing.expect(@sizeOf(@typeInfo(@FieldType(List(i32), "Cons")).pointer.child) == 24);
}

test "conv follows .NET" {
    try std.testing.expectEqual(@as(i32, -1), conv(i32, @as(u32, 0xFFFF_FFFF)));
    try std.testing.expectEqual(@as(u8, 0x34), conv(u8, @as(i32, 0x1234)));
    try std.testing.expectEqual(@as(i64, -5), conv(i64, @as(i32, -5)));
    try std.testing.expectEqual(@as(u64, 0xFFFF_FFFF_FFFF_FFFB), conv(u64, @as(i32, -5)));
    try std.testing.expectEqual(@as(i32, 3), conv(i32, @as(f64, 3.99)));
    try std.testing.expectEqual(@as(i32, -3), conv(i32, @as(f64, -3.99)));
    try std.testing.expectEqual(@as(i32, 2147483647), conv(i32, @as(f64, 1e30)));
    try std.testing.expectEqual(@as(i32, 0), conv(i32, std.math.nan(f64)));
    try std.testing.expectEqual(@as(f64, 7.0), conv(f64, @as(i32, 7)));
}
