//! The hand-written part of the Zig runtime library: reference-counted cells, reuse tokens,
//! the generic dup/drop/equality that generated code calls, and conversions between numbers.
//! The cycle collector will live here too.
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
pub const sgc = @import("fable_sgc.zig");

pub const interface_version: i32 = 10;

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

/// What belongs to one thread: its counters, its cycle collector and the exception it is
/// passing up. A value is owned by the thread that made it (counts are not atomic), so each
/// thread has all of this for itself. (Plain globals where there is one thread or no
/// thread-local storage: see `sgc.per_thread`.)
const thread = if (sgc.per_thread) struct {
    threadlocal var stats: Stats = .{};
    threadlocal var collector: sgc.Gc = undefined;
    threadlocal var collector_ready: bool = false;
    threadlocal var current: ?Exn = null;
} else struct {
    var stats: Stats = .{};
    var collector: sgc.Gc = undefined;
    var collector_ready: bool = false;
    var current: ?Exn = null;
};

/// This thread's counters (all zero in builds that do not count).
pub inline fn counters() *Stats {
    return &thread.stats;
}

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
    if (track) thread.stats.allocs += 1;
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
                thread.collector.allocs += 1;
                c.@"$gc" = gcHeader(C, c);
            }
            if (track) thread.stats.reuses += 1;
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
    if (track) thread.stats.dups += 1;
    if (gcOf(c)) |h| thread.collector.onRetain(h);
}

/// Take one reference off a cell that is known to be shared.
pub inline fn release(c: anytype) void {
    c.@"$rc" -= 1;
    if (track) thread.stats.decs += 1;
    if (gcOf(c)) |h| thread.collector.onRelease(h);
}

/// Take one reference off; true when it was the last one, and the caller gives up what the
/// cell holds and frees it. (False also when the cell's whole structure died with this
/// reference: the collector frees all of it, this cell included.)
pub inline fn releaseIsLast(c: anytype) bool {
    if (c.@"$rc" != 1) {
        c.@"$rc" -= 1;
        if (track) thread.stats.decs += 1;
        if (gcOf(c)) |h| thread.collector.onRelease(h);
        return false;
    }
    if (gcOf(c)) |h| return !thread.collector.onZero(h);
    return true;
}

/// A cell that is not shared is taken apart without its count going to zero: its fields are
/// about to be moved out or given up.
pub inline fn forget(c: anytype) void {
    if (gcOf(c)) |h| thread.collector.onFree(h);
}

/// A reference left a cell that is being taken apart and went to a variable as it is.
pub inline fn touch(x: anytype) void {
    eachHdr(x, {}, movedOut);
}

fn movedOut(_: void, h: *sgc.Hdr) void {
    thread.collector.onMoveOut(h);
}

pub inline fn free(c: anytype) void {
    if (track) thread.stats.frees += 1;
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
    if (T == String) return true;
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
    if (T == String) return strRetain(x);
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
    if (T == String) return strRelease(x);
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
    if (T == String) return strEql(a, b);
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
    if (track) thread.stats.allocs += 1;
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
    thread.collector.onUnstore(owner, old);
}

fn stored(owner: *sgc.Hdr, child: *sgc.Hdr) void {
    thread.collector.onStore(owner, child);
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
// taken apart, and a field of it is assigned. Generated code does not call the thread.collector.
// ---------------------------------------------------------------------------------------------

/// A test mode: before every allocation of a cell with a collector header, every structure's
/// count is checked against the cells and what they point at. A program turns it on with
/// `pub const fable_verify_cycles = true;` in its root file. Very slow.
const verify_cycles: bool = if (@hasDecl(@import("root"), "fable_verify_cycles")) @import("root").fable_verify_cycles else false;

/// What a file says about the records with assignable fields that its code makes:
/// - `holds`: one of them has an assignable field that can hold a function value or an
///   exception (directly or through other data);
/// - `generic`: one of them is made in generic code, with an assignable field whose type
///   depends on a type parameter;
/// - `instantiated`: a generic function is used with a type argument that can hold a function
///   value or an exception.
pub const Cycles = struct { holds: bool = false, generic: bool = false, instantiated: bool = false };

/// A file's own answer joined with those of the files it uses.
pub fn joinCycles(comptime own: Cycles, comptime used: anytype) Cycles {
    var r = own;
    inline for (used) |u| {
        r.holds = r.holds or u.holds;
        r.generic = r.generic or u.generic;
        r.instantiated = r.instantiated or u.instantiated;
    }
    return r;
}

/// Can a function value or an exception be part of a cycle in this program? What they hold
/// is not in their type, so a cell that holds one would have to be taken for cycle-capable
/// always. But a cycle needs an assignable field to close it, and one through a function
/// value needs an assignable field that can hold a function value. The program's root file
/// (the one with the entry point) says in `$cycles` whether the program makes a record with
/// such a field anywhere, joined over all the files it uses. If it does not, function values
/// and exceptions are never part of a cycle, and neither they nor the cells that hold them
/// need the collector. (Yes when the root file does not say.)
pub const functions_in_cycles: bool = blk: {
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    break :blk c.holds or (c.generic and c.instantiated);
};

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
    if (T == Exn) return functions_in_cycles;
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (p.size != .one or @typeInfo(p.child) != .@"struct") return false;
            return @hasDecl(p.child, "fable_cyclic") and p.child.fable_cyclic;
        },
        .optional => |o| return holdsCyclic(o.child),
        .@"struct" => |s| {
            if (@hasDecl(T, "fable_func")) return functions_in_cycles;
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
    thread.collector.init(.{}, null, allocator);
    thread.collector_ready = true;
}

/// Before a cell with a collector header is allocated (its field values are computed by
/// then): the only place where the collector does work of its own accord.
inline fn gcTick() void {
    if (!thread.collector_ready) collectorSetup();
    if (verify_cycles) thread.collector.verify();
    if (thread.collector.tickDue()) thread.collector.tickSlow();
}

/// The header of a new cell of a recursive union or of a reference record.
inline fn gcHeader(comptime C: type, c: *const C) sgc.Hdr {
    const K = Collected(C, "$gc", @as(isize, @offsetOf(C, "$rc")) - @as(isize, @offsetOf(C, "$gc")), null);
    return thread.collector.hdr(&K.desc, K.isLeaf(c));
}

/// Free every cycle that is dead now. Returns how many cells that freed.
pub fn collect() i32 {
    if (!thread.collector_ready) return 0;
    return @intCast(thread.collector.collectAll());
}

/// At most `budget` cells of collector work. True while more is waiting. The collector only
/// works of its own accord when a cell that can be part of a cycle is allocated; a program
/// that has idle time, and may not allocate for a while, calls this there. With nothing to do
/// it costs two compares.
pub fn collectStep(budget: i32) bool {
    if (!thread.collector_ready or budget <= 0) return false;
    return thread.collector.step(@intCast(budget));
}

/// No collector work until `collectorResume`, for code that must not be delayed. (Counts are
/// kept all the same, and a structure whose last outside reference goes is still freed.)
pub fn collectorPause() void {
    if (!thread.collector_ready) collectorSetup();
    thread.collector.noCollectEnter();
}

pub fn collectorResume() void {
    thread.collector.noCollectLeave();
}

pub const Knob = enum {
    /// 0: checks of live structures are only started by `collect` and `collectStep`
    automatic,
    /// cells of a check per allocation (0 or less: a check runs to its end at once)
    pace,
    /// cells of a dead structure freed per allocation (0 or less: all at once, inside the
    /// release that killed it)
    free_budget,
    /// with a free budget: cells that one drop frees at once before the rest is queued
    free_now,
    /// a structure that lost a reference is checked when it has grown by 1/`check_growth`
    /// (at least `check_min` cells) since, or after max(`check_wait`, `check_factor` times
    /// its cells) allocations
    check_growth,
    check_min,
    check_wait,
    check_factor,
};

/// Tune this thread's collector.
pub fn collectorSet(comptime knob: Knob, value: i32) void {
    if (!thread.collector_ready) collectorSetup();
    var cfg = thread.collector.cfg;
    const limit: usize = if (value <= 0) sgc.unlimited else @intCast(value);
    const count: usize = if (value <= 0) 0 else @intCast(value);
    switch (knob) {
        .automatic => cfg.auto = value != 0,
        .pace => cfg.pace = limit,
        .free_budget => cfg.free_budget = limit,
        .free_now => cfg.free_now = count,
        .check_growth => cfg.check_growth = @max(count, 1),
        .check_min => cfg.check_min = count,
        .check_wait => cfg.check_wait = count,
        .check_factor => cfg.check_factor = count,
    }
    thread.collector.configure(cfg);
}

/// For programs and tests that want to see what the runtime did (0 in builds that do not
/// count): cells allocated, built in again, freed; references added to and taken off cells
/// that stayed shared.
pub fn counted(comptime what: enum { allocs, reuses, frees, shared }) i32 {
    return @intCast(switch (what) {
        .allocs => thread.stats.allocs,
        .reuses => thread.stats.reuses,
        .frees => thread.stats.frees,
        .shared => thread.stats.dups + thread.stats.decs,
    });
}

/// Cells of this thread that are allocated now (0 in builds that do not count).
pub fn liveCells() i32 {
    return @intCast(live());
}

/// Give back the collector's own bookkeeping. Nothing it looks after may be alive.
pub fn collectorDeinit() void {
    if (thread.collector_ready) thread.collector.deinit();
}

/// The collector's counters (see fable_sgc.zig), or null if no cell ever needed it.
pub fn collectorCounters() ?sgc.Counters {
    return if (thread.collector_ready) thread.collector.counters else null;
}

/// How a call that ends a function is made when the caller and the callee have the same
/// parameter and result types: as a jump, where the compiler backend can guarantee one.
pub const tail_call: std.builtin.CallModifier = if (builtin.zig_backend == .stage2_llvm and switch (builtin.cpu.arch) {
    .wasm32, .wasm64 => false,
    else => true,
}) .always_tail else .auto;

// ---------------------------------------------------------------------------------------------
// Strings
//
// A string is what it is on .NET: an immutable sequence of UTF-16 code units, so that its
// length, its characters and their order are the same here and there. It is a pointer to a
// header that the units follow. A literal is static data: it is never counted and never
// freed, and making one costs nothing.
// ---------------------------------------------------------------------------------------------

pub const Str = extern struct {
    /// the number of references, or `literal` for a string that is static data
    rc: u32,
    len: u32,

    pub const literal: u32 = std.math.maxInt(u32);

    /// The UTF-16 code units.
    pub inline fn units(s: *const Str) []const u16 {
        const first: [*]const u16 = @ptrCast(@as([*]const Str, @ptrCast(s)) + 1);
        return first[0..s.len];
    }
};

/// F#'s `string`.
pub const String = *const Str;

fn LiteralCell(comptime n: usize) type {
    return extern struct { header: Str, units: [n]u16 };
}

/// A string literal, from UTF-8 text.
pub inline fn str(comptime utf8: []const u8) String {
    const static = comptime blk: {
        // (the conversion is a loop at compile time, and a function with many literals runs it
        // many times: the compiler's guard against endless loops is not for this)
        @setEvalBranchQuota(std.math.maxInt(u32));
        const u = std.unicode.utf8ToUtf16LeStringLiteral(utf8);
        break :blk LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len }, .units = u.* };
    };
    return &static.header;
}

/// A string literal that is not well-formed text (F# allows a surrogate on its own).
pub inline fn strOf(comptime u: []const u16) String {
    const static = comptime LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len }, .units = u[0..u.len].* };
    return &static.header;
}

fn strWords(len: usize) usize {
    return @sizeOf(Str) / 4 + (len + 1) / 2;
}

/// A new string of `len` units, to be filled in by the caller. Its count is one.
fn strNew(len: usize) struct { String, []u16 } {
    const words = allocator.alloc(u32, strWords(len)) catch @panic("fable: out of memory");
    const s: *Str = @ptrCast(words.ptr);
    s.* = .{ .rc = 1, .len = @intCast(len) };
    if (track) thread.stats.allocs += 1;
    const first: [*]u16 = @ptrCast(@as([*]Str, @ptrCast(s)) + 1);
    return .{ s, first[0..len] };
}

inline fn strRetain(s: String) void {
    if (s.rc == Str.literal) return;
    @constCast(s).rc += 1;
    if (track) thread.stats.dups += 1;
}

inline fn strRelease(s: String) void {
    if (s.rc == Str.literal) return;
    const m = @constCast(s);
    if (m.rc != 1) {
        m.rc -= 1;
        if (track) thread.stats.decs += 1;
        return;
    }
    if (track) thread.stats.frees += 1;
    const words: [*]u32 = @ptrCast(@alignCast(m));
    allocator.free(words[0..strWords(m.len)]);
}

pub fn strEql(a: String, b: String) bool {
    return a == b or std.mem.eql(u16, a.units(), b.units());
}

/// The order of two strings by their code units: negative, zero or positive, and the same
/// number as .NET's `String.CompareOrdinal`, which is what F#'s `compare` gives for strings.
pub fn strCompare(a: String, b: String) i32 {
    const x = a.units();
    const y = b.units();
    const x0: i32 = if (x.len != 0) x[0] else 0;
    const y0: i32 = if (y.len != 0) y[0] else 0;
    if (x0 != y0) return x0 - y0;
    for (x[0..@min(x.len, y.len)], y[0..@min(x.len, y.len)]) |c, d| {
        if (c != d) return @as(i32, c) - @as(i32, d);
    }
    return @as(i32, @intCast(x.len)) - @as(i32, @intCast(y.len));
}

/// F#'s `compare` for numbers, chars, booleans and strings: negative, zero or positive.
pub fn compare(a: anytype, b: @TypeOf(a)) i32 {
    const T = @TypeOf(a);
    if (T == String) return strCompare(a, b);
    if (T == bool) return @as(i32, @intFromBool(a)) - @as(i32, @intFromBool(b));
    if (a < b) return -1;
    if (a > b) return 1;
    if (a == b) return 0;
    // (not a number: it comes before every number, and equals itself)
    if (a == a) return 1;
    return if (b == b) -1 else 0;
}

pub inline fn strLen(s: String) i32 {
    return @intCast(s.len);
}

/// `s.[i]`
pub inline fn strAt(s: String, i: i32) u16 {
    return s.units()[@intCast(i)];
}

/// `a + b`: a new string, unless one of them is empty.
pub fn strConcat(a: String, b: String) String {
    if (a.len == 0) return dup(b);
    if (b.len == 0) return dup(a);
    const s, const u = strNew(a.len + b.len);
    @memcpy(u[0..a.len], a.units());
    @memcpy(u[a.len..], b.units());
    return s;
}

/// How a value is turned into text: an F# format specifier (`%5d`, `%.2f`, `%s`, ...), or
/// what `string x` and `$"{x}"` do (kind 'P').
pub const Spec = struct {
    kind: u8 = 'P',
    width: u16 = 0,
    precision: ?u8 = null,
    zero: bool = false,
    left: bool = false,
    plus: bool = false,
    space: bool = false,
};

fn Arg(comptime T: type, comptime spec: Spec) type {
    return struct {
        pub const fable_spec = spec;
        value: T,
    };
}

/// A value with its format specifier, as a part of `format`.
pub inline fn arg(comptime spec: Spec, value: anytype) Arg(@TypeOf(value), spec) {
    return .{ .value = value };
}

/// The text of one part: ASCII in `scratch`, or the units of a string.
const Piece = union(enum) {
    ascii: []const u8,
    units: []const u16,

    fn len(p: Piece) usize {
        return switch (p) {
            .ascii => |a| a.len,
            .units => |u| u.len,
        };
    }
};

const scratch_len = 400;

/// The decimal digits of a number: 0.d0 d1 d2 ... x 10^point.
const Decimal = struct {
    /// (a double has at most 309 digits before the point, or 1074 after it)
    digits: [1100]u8 = undefined,
    len: usize = 0,
    point: i32 = 1,

    /// The exact digits of a finite number that is not negative.
    fn exact(x: f64) Decimal {
        var d: Decimal = .{};
        if (x == 0) return d;
        const bits: u64 = @bitCast(x);
        const biased: i32 = @intCast((bits >> 52) & 0x7FF);
        var m: u64 = bits & ((1 << 52) - 1);
        var e: i32 = undefined;
        if (biased == 0) {
            e = -1074;
        } else {
            m |= 1 << 52;
            e = biased - 1075;
        }
        const zeros: u6 = @intCast(@ctz(m));
        m >>= zeros;
        e += zeros;

        var limbs: [36]u32 = @splat(0);
        if (e >= 0) {
            // a whole number, m * 2^e: its digits, nine at a time from the last
            const at: usize = @intCast(@divTrunc(e, 32));
            const wide: u128 = @as(u128, m) << @intCast(@mod(e, 32));
            limbs[at] = @truncate(wide);
            limbs[at + 1] = @truncate(wide >> 32);
            limbs[at + 2] = @truncate(wide >> 64);
            var n: usize = at + 3;
            var end: usize = d.digits.len;
            while (n > 0) {
                var rem: u64 = 0;
                var i = n;
                while (i > 0) {
                    i -= 1;
                    const cur = (rem << 32) | limbs[i];
                    limbs[i] = @intCast(cur / 1_000_000_000);
                    rem = cur % 1_000_000_000;
                }
                while (n > 0 and limbs[n - 1] == 0) n -= 1;
                for (0..9) |_| {
                    end -= 1;
                    d.digits[end] = @intCast(rem % 10);
                    rem /= 10;
                }
            }
            while (d.digits[end] == 0) end += 1;
            d.len = d.digits.len - end;
            std.mem.copyForwards(u8, d.digits[0..d.len], d.digits[end..]);
            d.point = @intCast(d.len);
            return d;
        }

        // m / 2^shift: the whole part, then one digit of the rest at a time
        const shift: usize = @intCast(-e);
        const whole: u64 = if (shift >= 64) 0 else m >> @intCast(shift);
        const rest: u64 = if (shift >= 64) m else m & ((@as(u64, 1) << @intCast(shift)) - 1);
        if (whole != 0) {
            const text = std.fmt.bufPrint(&d.digits, "{d}", .{whole}) catch unreachable;
            for (d.digits[0..text.len]) |*c| c.* -= '0';
            d.len = text.len;
        }
        d.point = @intCast(d.len);
        limbs[0] = @truncate(rest);
        limbs[1] = @truncate(rest >> 32);
        const top = shift / 32;
        const bit: u5 = @intCast(shift % 32);
        for (0..shift) |_| {
            var carry: u64 = 0;
            for (limbs[0 .. top + 2]) |*l| {
                const cur = @as(u64, l.*) * 10 + carry;
                l.* = @truncate(cur);
                carry = cur >> 32;
            }
            var next: u32 = limbs[top] >> bit;
            if (bit != 0) {
                next |= limbs[top + 1] << @intCast(32 - @as(u6, bit));
                limbs[top] &= (@as(u32, 1) << bit) - 1;
            } else {
                limbs[top] = 0;
            }
            limbs[top + 1] = 0;
            if (d.len == 0 and next == 0) {
                d.point -= 1;
            } else {
                d.digits[d.len] = @intCast(next);
                d.len += 1;
            }
        }
        return d;
    }

    /// The shortest digits that read back as the same number, of its own type.
    fn shortest(x: anytype) Decimal {
        var d: Decimal = .{};
        if (x == 0) return d;
        var buf: [64]u8 = undefined;
        const text = std.fmt.bufPrint(&buf, "{e}", .{x}) catch unreachable;
        const e = std.mem.indexOfScalar(u8, text, 'e').?;
        for (text[0..e]) |c| {
            if (c == '.') continue;
            d.digits[d.len] = c - '0';
            d.len += 1;
        }
        d.point = (std.fmt.parseInt(i32, text[e + 1 ..], 10) catch unreachable) + 1;
        return d;
    }

    /// Keep `n` digits, rounding to the nearest and a tie to the even digit, as .NET does.
    fn round(d: *Decimal, n: i32) void {
        if (n >= d.len) return;
        if (n < 0) {
            d.len = 0;
            return;
        }
        const keep: usize = @intCast(n);
        const next = d.digits[keep];
        var up = next > 5;
        if (next == 5) {
            up = keep > 0 and d.digits[keep - 1] % 2 == 1;
            for (d.digits[keep + 1 .. d.len]) |c| {
                if (c != 0) up = true;
            }
        }
        d.len = keep;
        if (!up) return;
        var i = keep;
        while (i > 0) {
            i -= 1;
            if (d.digits[i] != 9) {
                d.digits[i] += 1;
                return;
            }
            d.digits[i] = 0;
        }
        // (all nines, or no digit at all: one, a place higher)
        d.digits[0] = 1;
        d.len = @max(keep, 1);
        d.point += 1;
    }

    inline fn digit(d: *const Decimal, i: i32) u8 {
        return if (i >= 0 and i < d.len) '0' + d.digits[@intCast(i)] else '0';
    }
};

const Text = struct {
    buf: []u8,
    len: usize = 0,

    inline fn put(t: *Text, c: u8) void {
        t.buf[t.len] = c;
        t.len += 1;
    }

    /// e+005: the exponent with its sign and at least `width` digits
    fn exponent(t: *Text, letter: u8, exp: i32, width: usize) void {
        t.put(letter);
        t.put(if (exp < 0) '-' else '+');
        var digits: [8]u8 = undefined;
        const text = std.fmt.bufPrint(&digits, "{d}", .{@abs(exp)}) catch unreachable;
        for (@min(text.len, width)..width) |_| t.put('0');
        for (text) |c| t.put(c);
    }

    /// The digits without the zeros at their end: plainly while the exponent is above -5 and
    /// below `limit`, as d.ddde+xx otherwise.
    fn general(t: *Text, d: *const Decimal, limit: i32, letter: u8) void {
        var n: i32 = @intCast(d.len);
        while (n > 0 and d.digits[@intCast(n - 1)] == 0) n -= 1;
        const exp = d.point - 1;
        if (exp > -5 and exp < limit) {
            if (d.point <= 0) {
                t.put('0');
            } else {
                var i: i32 = 0;
                while (i < d.point) : (i += 1) t.put(d.digit(i));
            }
            if (n > d.point) {
                t.put('.');
                var i: i32 = @min(d.point, 0);
                while (i < 0) : (i += 1) t.put('0');
                i = @max(d.point, 0);
                while (i < n) : (i += 1) t.put(d.digit(i));
            }
        } else {
            t.put(d.digit(0));
            if (n > 1) {
                t.put('.');
                var i: i32 = 1;
                while (i < n) : (i += 1) t.put(d.digit(i));
            }
            t.exponent(letter, exp, 2);
        }
    }
};

/// A float as F# and .NET write it. `%f` and `%e` round the exact value of the number; `%g`
/// keeps six digits; everything else (`string x`, `$"{x}"`, `%O`) is the shortest text that
/// reads back as the same number.
fn floatText(comptime spec: Spec, value: anytype, out: []u8) []const u8 {
    const x: f64 = value;
    if (std.math.isNan(x)) return "NaN";
    if (std.math.isInf(x)) return if (x > 0) "Infinity" else "-Infinity";
    var t: Text = .{ .buf = out };
    if (std.math.signbit(x)) t.put('-') else if (spec.plus) t.put('+') else if (spec.space) t.put(' ');
    const precision: i32 = @min(spec.precision orelse 6, 80);
    switch (spec.kind) {
        'f', 'F' => {
            var d = Decimal.exact(@abs(x));
            d.round(d.point + precision);
            var i: i32 = @min(d.point, 1) - 1;
            while (i < d.point) : (i += 1) t.put(d.digit(i));
            if (precision > 0) {
                t.put('.');
                var k: i32 = 0;
                while (k < precision) : (k += 1) t.put(d.digit(d.point + k));
            }
        },
        'e', 'E' => {
            var d = Decimal.exact(@abs(x));
            d.round(precision + 1);
            t.put(d.digit(0));
            if (precision > 0) {
                t.put('.');
                var k: i32 = 1;
                while (k <= precision) : (k += 1) t.put(d.digit(k));
            }
            t.exponent(spec.kind, d.point - 1, 3);
        },
        'g', 'G' => {
            const letter: u8 = if (spec.kind == 'g') 'e' else 'E';
            if (precision == 0) {
                const d = Decimal.shortest(@abs(value));
                t.general(&d, if (@TypeOf(value) == f32) 9 else 17, letter);
            } else {
                var d = Decimal.exact(@abs(x));
                d.round(precision);
                t.general(&d, precision, letter);
            }
        },
        else => {
            const d = Decimal.shortest(@abs(value));
            t.general(&d, if (@TypeOf(value) == f32) 9 else 17, 'E');
        },
    }
    return out[0..t.len];
}

fn pieceOf(comptime spec: Spec, value: anytype, scratch: *[scratch_len]u8) Piece {
    const T = @TypeOf(value);
    if (T == String) return .{ .units = value.units() };
    switch (@typeInfo(T)) {
        .bool => return .{ .ascii = if (spec.kind == 'b')
            (if (value) "true" else "false")
        else
            (if (value) "True" else "False") },
        .int => |info| {
            if (spec.kind == 'c') {
                // (a char: one UTF-16 unit, kept in the scratch space as such)
                const u: *[1]u16 = @ptrCast(@alignCast(scratch));
                u[0] = @intCast(value);
                return .{ .units = u };
            }
            const Bits = @Int(.unsigned, info.bits);
            const sign: []const u8 = if (value >= 0 and spec.plus) "+" else if (value >= 0 and spec.space) " " else "";
            const text = switch (spec.kind) {
                'x' => std.fmt.bufPrint(scratch, "{x}", .{@as(Bits, @bitCast(value))}),
                'X' => std.fmt.bufPrint(scratch, "{X}", .{@as(Bits, @bitCast(value))}),
                'o' => std.fmt.bufPrint(scratch, "{o}", .{@as(Bits, @bitCast(value))}),
                'u' => std.fmt.bufPrint(scratch, "{d}", .{@as(Bits, @bitCast(value))}),
                else => std.fmt.bufPrint(scratch, "{s}{d}", .{ sign, value }),
            };
            return .{ .ascii = text catch unreachable };
        },
        .comptime_int => return pieceOf(spec, @as(i64, value), scratch),
        .float => return .{ .ascii = floatText(spec, value, scratch) },
        .comptime_float => return .{ .ascii = floatText(spec, @as(f64, value), scratch) },
        else => @compileError("fable: a value of type " ++ @typeName(T) ++ " cannot be formatted yet"),
    }
}

fn isLiteralText(comptime T: type) bool {
    const info = @typeInfo(T);
    if (info != .pointer) return false;
    if (info.pointer.size == .slice) return info.pointer.child == u8;
    if (info.pointer.size != .one) return false;
    const child = @typeInfo(info.pointer.child);
    return child == .array and child.array.child == u8;
}

/// Text from parts: literal text (a Zig string literal), strings, and values, bare or with a
/// format specifier (`fable_rt.arg`). This is `sprintf`, string interpolation and `string x`.
pub fn format(parts: anytype) String {
    @setEvalBranchQuota(std.math.maxInt(u32));
    const names = @typeInfo(@TypeOf(parts)).@"struct".field_names;
    var pieces: [names.len]Piece = undefined;
    var pad: [names.len]usize = @splat(0);
    var scratch: [names.len][scratch_len]u8 align(2) = undefined;
    var total: usize = 0;
    inline for (names, 0..) |name, i| {
        const part = @field(parts, name);
        const T = @TypeOf(part);
        if (comptime isLiteralText(T)) {
            pieces[i] = .{ .units = comptime std.unicode.utf8ToUtf16LeStringLiteral(part) };
        } else if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec"))) {
            pieces[i] = pieceOf(T.fable_spec, part.value, &scratch[i]);
            if (T.fable_spec.width > pieces[i].len()) pad[i] = T.fable_spec.width - pieces[i].len();
        } else {
            pieces[i] = pieceOf(.{}, part, &scratch[i]);
        }
        total += pieces[i].len() + pad[i];
    }
    const s, const out = strNew(total);
    var at: usize = 0;
    inline for (names, 0..) |name, i| {
        const T = @TypeOf(@field(parts, name));
        const spec: Spec = if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec"))) T.fable_spec else .{};
        at = writePiece(out, at, pieces[i], pad[i], spec);
    }
    return s;
}

/// Write one part at `at`, padded to its width; returns where the next part starts.
fn writePiece(out: []u16, start: usize, piece: Piece, pad: usize, spec: Spec) usize {
    var at = start;
    if (pad != 0 and !spec.left) {
        if (spec.zero and piece == .ascii) {
            // (zeros go between the sign and the digits)
            const a = piece.ascii;
            const signed = a.len > 0 and (a[0] == '-' or a[0] == '+' or a[0] == ' ');
            if (signed) {
                out[at] = a[0];
                at += 1;
            }
            @memset(out[at..][0..pad], '0');
            at += pad;
            for (a[@intFromBool(signed)..]) |c| {
                out[at] = c;
                at += 1;
            }
            return at;
        }
        @memset(out[at..][0..pad], ' ');
        at += pad;
    }
    switch (piece) {
        .ascii => |a| for (a) |c| {
            out[at] = c;
            at += 1;
        },
        .units => |u| {
            @memcpy(out[at..][0..u.len], u);
            at += u.len;
        },
    }
    if (pad != 0 and spec.left) {
        @memset(out[at..][0..pad], ' ');
        at += pad;
    }
    return at;
}

fn posixWrite(fd: i32, bytes: []const u8) void {
    if (builtin.os.tag == .freestanding) return;
    var done: usize = 0;
    while (done < bytes.len) {
        const n = std.posix.system.write(fd, bytes.ptr + done, bytes.len - done);
        if (n <= 0) return;
        done += @intCast(n);
    }
}

fn defaultOut(bytes: []const u8) void {
    posixWrite(1, bytes);
}

fn defaultErr(bytes: []const u8) void {
    posixWrite(2, bytes);
}

/// Where `printf` and `eprintf` send their text, as UTF-8. A program may replace them (a
/// freestanding one has to: there they do nothing).
pub var write_out: *const fn (bytes: []const u8) void = defaultOut;
pub var write_err: *const fn (bytes: []const u8) void = defaultErr;

fn writeText(write: *const fn ([]const u8) void, s: String, newline: bool) void {
    var buf: [512]u8 = undefined;
    var rest = s.units();
    while (rest.len != 0) {
        // (a pair of surrogates is not split between two chunks)
        var n = @min(rest.len, buf.len / 3);
        if (n < rest.len and rest[n - 1] >= 0xD800 and rest[n - 1] < 0xDC00) n -= 1;
        if (n == 0) n = 1;
        const len = std.unicode.wtf16LeToWtf8(&buf, rest[0..n]);
        write(buf[0..len]);
        rest = rest[n..];
    }
    if (newline) write("\n");
}

/// `printf` / `printfn`: the text of `parts` (see `format`) to standard output.
pub fn print(parts: anytype, comptime newline: bool) void {
    const s = format(parts);
    writeText(write_out, s, newline);
    drop(s);
}

/// `eprintf` / `eprintfn`
pub fn printErr(parts: anytype, comptime newline: bool) void {
    const s = format(parts);
    writeText(write_err, s, newline);
    drop(s);
}

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
        const cyclic = functions_in_cycles and holdsCyclic(Captures);
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
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
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
    /// the message, for an exception that was made with one
    message: ?*const fn (Exn) String = null,
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
        const cyclic = functions_in_cycles and holdsCyclic(Payload);
        const Whole = struct { header: ExnHeader, hdr: GcHdr(cyclic) = undefined, payload: Payload };
        const K = Collected(
            Whole,
            "hdr",
            @as(isize, @offsetOf(Whole, "header")) + @as(isize, @offsetOf(ExnHeader, "$rc")) - @as(isize, @offsetOf(Whole, "hdr")),
            "payload",
        );

        pub const info: ExnType = .{
            .name = name,
            .destroy = destroy,
            .message = if (Payload == Described) message else null,
        };

        fn message(e: Exn) String {
            return dup(of(e).Message);
        }

        pub fn new(payload: Payload) Exn {
            if (comptime cyclic) gcTick();
            const c = allocator.create(Whole) catch @panic("fable: out of memory");
            c.* = .{ .header = .{ .type = &info }, .payload = payload };
            if (comptime cyclic) {
                c.hdr = thread.collector.hdr(&K.desc, K.isLeaf(c));
                c.header.gc = &c.hdr;
            }
            if (track) thread.stats.allocs += 1;
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

/// The exception in flight is `thread.current`.
pub fn throw(e: Exn) void {
    std.debug.assert(thread.current == null);
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
pub const Described = struct { Message: String };

/// What `failwith` raises: .NET's `System.Exception` with a message.
pub const Failure = ExnOf("System.Exception", Described);

/// The .NET exception classes that a program can raise and handle by name. (Each is a type of
/// its own here: a handler for one does not catch the classes that derive from it on .NET.)
pub const ArgumentException = ExnOf("System.ArgumentException", Described);
pub const ArgumentNullException = ExnOf("System.ArgumentNullException", Described);
pub const ArgumentOutOfRangeException = ExnOf("System.ArgumentOutOfRangeException", Described);
pub const InvalidOperationException = ExnOf("System.InvalidOperationException", Described);
pub const NotSupportedException = ExnOf("System.NotSupportedException", Described);
pub const NotImplementedException = ExnOf("System.NotImplementedException", Described);
pub const IndexOutOfRangeException = ExnOf("System.IndexOutOfRangeException", Described);
pub const DivideByZeroException = ExnOf("System.DivideByZeroException", Described);
pub const OverflowException = ExnOf("System.OverflowException", Described);
pub const FormatException = ExnOf("System.FormatException", Described);
pub const KeyNotFoundException = ExnOf("System.Collections.Generic.KeyNotFoundException", Described);

/// `e.Message`: the message an exception was made with; for an F# exception, its name.
pub fn exnMessage(e: Exn) String {
    if (e.type.message) |message| return message(e);
    const s, const u = strNew(e.type.name.len);
    for (e.type.name, u) |c, *o| o.* = c;
    return s;
}

/// The program's entry point let an exception escape: say which, and give it up.
pub fn uncaught() void {
    const e = take();
    write_err("Unhandled exception. ");
    write_err(e.type.name);
    if (e.type.message) |message| {
        const text = message(e);
        write_err(": ");
        writeText(write_err, text, false);
        drop(text);
    }
    write_err("\n");
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
    return thread.stats.allocs - thread.stats.frees;
}

/// Called when the program's entry point has returned: true, with a message, if cells are
/// still allocated. Only checks in builds that keep counters.
pub fn leaked() bool {
    // (cycles that died without anything noticing yet are not leaks)
    _ = collect();
    if (!track or live() == 0) return false;
    std.debug.print("fable: {d} cell(s) were never freed (allocated {d}, freed {d})\n", .{ live(), thread.stats.allocs, thread.stats.frees });
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
    const before = thread.stats;
    drop(testRange(1_000_000));
    try std.testing.expectEqual(@as(i64, 1_000_000), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 1_000_000), thread.stats.frees - before.frees);
}

test "a shared cell is freed by its last owner" {
    const before = thread.stats;
    const tail = testRange(3);
    const a = testCons(10, dup(tail));
    const b = testCons(20, tail);
    drop(a);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.frees - before.frees);
    try std.testing.expectEqual(@as(i32, 1), b.Cons.tail.Cons.head);
    drop(b);
    try std.testing.expectEqual(@as(i64, 5), thread.stats.frees - before.frees);
}

test "trees, and values that hold cells" {
    const before = thread.stats;
    drop(testTree(10));
    try std.testing.expectEqual(@as(i64, 1023), thread.stats.frees - before.frees);
    const p = TestPair{ .first = testRange(2), .second = testRange(3), .n = 1 };
    const q = dup(p);
    drop(p);
    try std.testing.expectEqual(@as(i64, 1023), thread.stats.frees - before.frees);
    drop(q);
    try std.testing.expectEqual(@as(i64, 1028), thread.stats.frees - before.frees);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "a dead cell is built in again" {
    const before = thread.stats;
    const l = testRange(1);
    var tok: ?*Cell(TestList, .Cons) = null;
    if (isUnique(l.Cons)) tok = l.Cons;
    const m = TestList{ .Cons = cellReuse(TestList, .Cons, &tok, .{ .head = 7, .tail = .Nil }) };
    try std.testing.expectEqual(l.Cons, m.Cons);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - before.reuses);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.allocs - before.allocs);
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
    const before = thread.stats;
    const xs = testRange(3);
    // borrowed by the callee, kept by the caller: nothing is counted
    try std.testing.expectEqual(@as(i32, 6), across(testSum, testSum_sig, .{.keep}, .{xs}));
    try std.testing.expectEqual(@as(i64, 0), thread.stats.dups - before.dups);
    // a borrowed result is made owned
    const t = across(testTail, testTail_sig, .{.keep}, .{xs});
    try std.testing.expectEqual(@as(i64, 1), thread.stats.dups - before.dups);
    // owned by the callee, kept by the caller: one more reference
    const ys = across(testPush, testPush_sig, .{ .plain, .keep }, .{ 0, xs });
    try std.testing.expectEqual(@as(i64, 2), thread.stats.dups - before.dups);
    // owned by the callee, given by the caller: a move
    const zs = across(testPush, testPush_sig, .{ .plain, .give }, .{ 9, ys });
    try std.testing.expectEqual(@as(i64, 2), thread.stats.dups - before.dups);
    // borrowed by the callee, given by the caller: the caller gives it up after the call
    try std.testing.expectEqual(@as(i32, 15), across(testSum, testSum_sig, .{.give}, .{zs}));
    try std.testing.expectEqual(@as(i32, 5), across(testSum, testSum_sig, .{.give}, .{t}));
    drop(xs);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
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
    const before = thread.stats;
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
    try std.testing.expectEqual(@as(i64, 4), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 4), thread.stats.frees - before.frees);
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
    const before = thread.stats;
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
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    // a function that calls nothing that raises has a plain result
    try std.testing.expect(@TypeOf(testPlain(1)) == i32);
    try std.testing.expect(@TypeOf(testOuter(1)) == Raised!i32);
}

const TestNode = *struct { @"$rc": u32 = 1, id: i32, next: ?TestNode };

test "reference records: identity, stores and long chains" {
    const before = thread.stats;
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
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
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
    const before = thread.stats;
    // two records that point at each other
    const a = testPerson(1);
    const b = testPerson(2);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(a));
    drop(a);
    try std.testing.expectEqual(@as(i64, 0), thread.stats.frees - before.frees);
    drop(b);
    try std.testing.expectEqual(@as(i64, 2), thread.stats.frees - before.frees);
    // a record that reaches itself through a list
    const c = testPerson(3);
    const cons = List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = dup(c), .Tail = .Empty }) };
    storeIn(c, "friends", cons);
    drop(c);
    try std.testing.expectEqual(@as(i64, 4), thread.stats.frees - before.frees);
    // a record that holds a function which captured the record
    const d = testPerson(40);
    const f = closure(Func(*const fn (?*Env, i32) Raised!i32), TestSelf, .{ .self = dup(d) }, testAddId);
    storeIn(d, "callback", f);
    try std.testing.expectEqual(@as(i32, 42), try d.callback.?.code(d.callback.?.env, 2));
    drop(d);
    try std.testing.expectEqual(@as(i64, 6), thread.stats.frees - before.frees);
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
    try std.testing.expectEqual(@as(i64, 8), thread.stats.frees - before.frees);
    drop(keep);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    // cells of the same types that never form a cycle are plain reference counting
    const lone = testPerson(8);
    storeIn(lone, "friends", List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = testPerson(9), .Tail = .Empty }) });
    drop(lone);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    try std.testing.expect(@sizeOf(@typeInfo(@FieldType(List(i32), "Cons")).pointer.child) == 24);
}

fn testThreadWork(result: *i64) void {
    const before = thread.stats;
    var round: i32 = 0;
    while (round < 2000) : (round += 1) {
        const a = testPerson(round);
        const b = testPerson(round + 1);
        storeIn(a, "friend", dup(b));
        storeIn(b, "friend", dup(a));
        drop(a);
        drop(b);
    }
    throw(TestOverflow.new(.{ .limit = 1 }));
    drop(take());
    result.* = (thread.stats.allocs - before.allocs) - (thread.stats.frees - before.frees);
}

test "every thread has its own collector" {
    if (!sgc.per_thread) return;
    var left: [4]i64 = @splat(-1);
    var threads: [4]std.Thread = undefined;
    for (&threads, &left) |*t, *l| t.* = try std.Thread.spawn(.{}, testThreadWork, .{l});
    for (threads) |t| t.join();
    for (left) |l| try std.testing.expectEqual(@as(i64, 0), l);
}

test "the collector can be stepped and tuned" {
    const before = thread.stats;
    collectorSet(.free_budget, 2);
    const a = testPerson(1);
    const b = testPerson(2);
    const c = testPerson(3);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(c));
    storeIn(c, "friend", dup(a));
    drop(a);
    drop(b);
    drop(c);
    // dead, and queued: freed a few cells at a time
    try std.testing.expect(thread.stats.frees - before.frees < 3);
    var steps: i32 = 0;
    while (collectStep(1)) steps += 1;
    try std.testing.expect(steps > 0);
    try std.testing.expectEqual(@as(i64, 3), thread.stats.frees - before.frees);
    collectorSet(.free_budget, 0);
    collectorPause();
    collectorResume();
    try std.testing.expectEqual(@as(i32, 0), collect());
}

fn expectText(expected: []const u8, s: String) !void {
    var buf: [512]u8 = undefined;
    const n = std.unicode.wtf16LeToWtf8(&buf, s.units());
    try std.testing.expectEqualStrings(expected, buf[0..n]);
    drop(s);
}

test "strings: literals, concatenation, comparison" {
    const before = thread.stats;
    const hello = str("héllo");
    try std.testing.expectEqual(@as(i32, 5), strLen(hello));
    try std.testing.expectEqual(@as(u16, 0xE9), strAt(hello, 1));
    const both = strConcat(hello, str(" wörld"));
    try std.testing.expectEqual(@as(i32, 11), strLen(both));
    const again = dup(both);
    try std.testing.expect(eql(both, again));
    try std.testing.expect(eql(str("ab"), str("ab")) and !eql(str("ab"), str("ac")));
    try std.testing.expect(strConcat(str(""), hello) == hello);
    drop(both);
    drop(again);
    drop(hello);
    // (a literal is never counted: only `both` was allocated)
    try std.testing.expectEqual(@as(i64, 1), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.frees - before.frees);
    // an emoji is two units
    try std.testing.expectEqual(@as(i32, 2), strLen(str("\u{1F600}")));
}

test "format follows F# and .NET" {
    const name = str("list");
    try expectText("list has 3 items", format(.{ name, " has ", @as(i32, 3), " items" }));
    try expectText("n=   42|42   |00042|-0042|+7| 7|  +42|+42  ", format(.{
        "n=", arg(.{ .kind = 'd', .width = 5 }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .left = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .zero = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .zero = true }, @as(i32, -42)),
        "|",  arg(.{ .kind = 'd', .plus = true }, @as(i32, 7)),
        "|",  arg(.{ .kind = 'd', .space = true }, @as(i32, 7)),
        "|",  arg(.{ .kind = 'd', .width = 5, .plus = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .plus = true, .left = true }, @as(i32, 42)),
    }));
    try expectText("ff FF 377 ffffffff 4294967295 -9223372036854775808", format(.{
        arg(.{ .kind = 'x' }, @as(i32, 255)), " ", arg(.{ .kind = 'X' }, @as(i32, 255)),                  " ",
        arg(.{ .kind = 'o' }, @as(i32, 255)), " ", arg(.{ .kind = 'x' }, @as(i32, -1)),                   " ",
        arg(.{ .kind = 'u' }, @as(i32, -1)),  " ", arg(.{ .kind = 'd' }, @as(i64, std.math.minInt(i64))),
    }));
    try expectText("true True A é", format(.{
        arg(.{ .kind = 'b' }, true), " ", true, " ", arg(.{ .kind = 'c' }, @as(u16, 'A')), " ", arg(.{ .kind = 'c' }, @as(u16, 0xE9)),
    }));
    try expectText("[  ab]", format(.{ "[", arg(.{ .kind = 's', .width = 4 }, str("ab")), "]" }));
}

fn expectFloat(expected: []const u8, comptime spec: Spec, value: anytype) !void {
    var buf: [scratch_len]u8 = undefined;
    try std.testing.expectEqualStrings(expected, floatText(spec, value, &buf));
}

test "floats are written as .NET writes them" {
    const f: Spec = .{ .kind = 'f' };
    const e: Spec = .{ .kind = 'e' };
    const g: Spec = .{ .kind = 'g' };
    // (every expected text here is what .NET 10 prints)
    // %f: the exact value, a tie to the even digit
    try expectFloat("3.141590", f, @as(f64, 3.14159));
    try expectFloat("2.67", .{ .kind = 'f', .precision = 2 }, @as(f64, 2.675));
    try expectFloat("0.12", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.125));
    try expectFloat("0.38", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.375));
    try expectFloat("0.62", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.625));
    try expectFloat("1.00", .{ .kind = 'f', .precision = 2 }, @as(f64, 1.005));
    try expectFloat("0", .{ .kind = 'f', .precision = 0 }, @as(f64, 0.5));
    try expectFloat("2", .{ .kind = 'f', .precision = 0 }, @as(f64, 1.5));
    try expectFloat("2", .{ .kind = 'f', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.000", .{ .kind = 'f', .precision = 3 }, @as(f64, 1.0005));
    try expectFloat("10000000000000000000000.000000", f, @as(f64, 1e22));
    try expectFloat("-0.000000", f, @as(f64, -0.0));
    try expectFloat("0.000000", f, @as(f64, 1e-7));
    try expectFloat("0.000", .{ .kind = 'f', .precision = 3 }, std.math.floatTrueMin(f64));
    try expectFloat("0.100000", f, @as(f32, 0.1));
    try expectFloat("0.1000000015", .{ .kind = 'f', .precision = 10 }, @as(f32, 0.1));
    try expectFloat("+1.500000", .{ .kind = 'f', .plus = true }, @as(f64, 1.5));
    try expectFloat(" 1.500000", .{ .kind = 'f', .space = true }, @as(f64, 1.5));
    try expectFloat("999.999000", f, @as(f64, 999.999));
    try expectFloat("1000.00", .{ .kind = 'f', .precision = 2 }, @as(f64, 999.999));
    // %e
    try expectFloat("1.500000e+020", e, @as(f64, 1.5e20));
    try expectFloat("1.500000E-020", .{ .kind = 'E' }, @as(f64, 1.5e-20));
    try expectFloat("1.23e+004", .{ .kind = 'e', .precision = 2 }, @as(f64, 12345.678));
    try expectFloat("0.000000e+000", e, @as(f64, 0.0));
    try expectFloat("2e+000", .{ .kind = 'e', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.2e+000", .{ .kind = 'e', .precision = 1 }, @as(f64, 1.25));
    try expectFloat("1.4e+000", .{ .kind = 'e', .precision = 1 }, @as(f64, 1.35));
    try expectFloat("1.000000e+023", e, @as(f64, 1e23));
    try expectFloat("1.000000e+011", e, @as(f64, 9.9999999e10));
    try expectFloat("-1.234e-004", .{ .kind = 'e', .precision = 3 }, @as(f64, -0.00012345));
    try expectFloat("4.940656e-324", e, std.math.floatTrueMin(f64));
    try expectFloat("1.000000e-001", e, @as(f32, 0.1));
    // %g
    try expectFloat("3", g, @as(f64, 3.0));
    try expectFloat("1e+20", g, @as(f64, 1e20));
    try expectFloat("0.0001", g, @as(f64, 0.0001));
    try expectFloat("1e-05", g, @as(f64, 0.00001));
    try expectFloat("3.14159", g, @as(f64, 3.14159265));
    try expectFloat("123456", g, @as(f64, 123456.0));
    try expectFloat("1.23457e+06", g, @as(f64, 1234567.0));
    try expectFloat("100000", g, @as(f64, 100000.0));
    try expectFloat("1e+06", g, @as(f64, 1000000.0));
    try expectFloat("1E-20", .{ .kind = 'G' }, @as(f64, 1e-20));
    try expectFloat("3.14", .{ .kind = 'g', .precision = 3 }, @as(f64, 3.14159));
    try expectFloat("1.23e+03", .{ .kind = 'g', .precision = 3 }, @as(f64, 1234.0));
    try expectFloat("10", g, @as(f64, 9.9999995));
    try expectFloat("-0", g, @as(f64, -0.0));
    try expectFloat("0.1", g, @as(f32, 0.1));
    try expectFloat("1.79769e+308", g, std.math.floatMax(f64));
    try expectFloat("2.5", .{ .kind = 'g', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.2345678901234568e+17", .{ .kind = 'g', .precision = 0 }, @as(f64, 123456789012345678.0));
    try expectFloat("2", .{ .kind = 'g', .precision = 1 }, @as(f64, 2.5));
    try expectFloat("0.3", .{ .kind = 'g', .precision = 1 }, @as(f64, 0.35));
    try expectFloat("0.10000000000000000555", .{ .kind = 'g', .precision = 20 }, @as(f64, 0.1));
    // `string x`
    const p: Spec = .{};
    try expectFloat("1", p, @as(f64, 1.0));
    try expectFloat("1.5", p, @as(f64, 1.5));
    try expectFloat("-0", p, @as(f64, -0.0));
    try expectFloat("0.0001", p, @as(f64, 0.0001));
    try expectFloat("1E-05", p, @as(f64, 0.00001));
    try expectFloat("1.5E-05", p, @as(f64, 1.5e-5));
    try expectFloat("100000000000000", p, @as(f64, 1e14));
    try expectFloat("10000000000000000", p, @as(f64, 1e16));
    try expectFloat("15000000000000000", p, @as(f64, 1.5e16));
    try expectFloat("1E+17", p, @as(f64, 1e17));
    try expectFloat("1.2345678901234568E+17", p, @as(f64, 123456789012345678.0));
    try expectFloat("1E+20", p, @as(f64, 1e20));
    try expectFloat("1.7976931348623157E+308", p, std.math.floatMax(f64));
    try expectFloat("5E-324", p, std.math.floatTrueMin(f64));
    try expectFloat("NaN", p, std.math.nan(f64));
    try expectFloat("-Infinity", p, -std.math.inf(f64));
    try expectFloat("0.1", p, @as(f32, 0.1));
    try expectFloat("16777216", p, @as(f32, 16777216.0));
    try expectFloat("100000000", p, @as(f32, 1e8));
    try expectFloat("1E+09", p, @as(f32, 1e9));
    try expectFloat("123456790", p, @as(f32, 123456789.0));
    try expectFloat("3E-05", p, @as(f32, 3.0e-5));
    try expectFloat("3.4028235E+38", p, std.math.floatMax(f32));
}

test "compare gives what .NET gives" {
    try std.testing.expectEqual(@as(i32, -1), compare(str("abc"), str("abd")));
    try std.testing.expectEqual(@as(i32, 1), compare(str("b"), str("abc")));
    try std.testing.expectEqual(@as(i32, 32), compare(str("a"), str("A")));
    try std.testing.expectEqual(@as(i32, 131), compare(str("é"), str("f")));
    try std.testing.expectEqual(@as(i32, -97), compare(str(""), str("a")));
    try std.testing.expectEqual(@as(i32, -2), compare(str("ab"), str("abcd")));
    try std.testing.expectEqual(@as(i32, 0), compare(str("ab"), str("ab")));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(i32, 1), @as(i32, 2)));
    try std.testing.expectEqual(@as(i32, 1), compare(true, false));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(u16, 'a'), @as(u16, 'c')));
    const nan = std.math.nan(f64);
    try std.testing.expectEqual(@as(i32, -1), compare(nan, @as(f64, 1.0)));
    try std.testing.expectEqual(@as(i32, 1), compare(@as(f64, 1.0), nan));
    try std.testing.expectEqual(@as(i32, 0), compare(nan, nan));
}

test "a failure carries its message" {
    const before = thread.stats;
    throw(Failure.new(.{ .Message = format(.{ "bad ", @as(i32, 7) }) }));
    const e = take();
    try std.testing.expect(Failure.is(e) and !ArgumentException.is(e));
    try expectText("bad 7", exnMessage(e));
    drop(e);
    const other = ArgumentException.new(.{ .Message = str("no") });
    try std.testing.expect(!Failure.is(other) and ArgumentException.is(other));
    try expectText("no", exnMessage(other));
    drop(other);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
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
