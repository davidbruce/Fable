//! Fat-pointer interfaces (`{ data, vt }`), `IfaceMeta`, adapters, and casts (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const BoxChain = rt.BoxChain;
const Env = rt.Env;
const EnvOf = rt.EnvOf;
const Func = rt.Func;
const InvalidCastException = rt.InvalidCastException;
const Obj = rt.Obj;
const ObjCell = rt.ObjCell;
const ObjType = rt.ObjType;
const Raised = rt.Raised;
const TailFn = rt.TailFn;
const TextBuilder = rt.TextBuilder;
const arrayNull = rt.arrayNull;
const box = rt.box;
const boxType = rt.boxType;
const boxed = rt.boxed;
const captured = rt.captured;
const closure = rt.closure;
const convert = rt.convert;
const drop = rt.drop;
const dropEnv = rt.dropEnv;
const dup = rt.dup;
const eql = rt.eql;
const gcTick = rt.gcTick;
const isArrayPtr = rt.isArrayPtr;
const markCell = rt.markCell;
const markShared = rt.markShared;
const netTypeName = rt.netTypeName;
const new = rt.new;
const nullRef = rt.nullRef;
const objCast = rt.objCast;
const objIs = rt.objIs;
const oom = rt.oom;
const raise = rt.raise;
const retain = rt.retain;
const sgc = rt.sgc;
const take = rt.take;
const thread = rt.thread;
const time = rt.time;
const track = rt.track;
const tryUnbox = rt.tryUnbox;
const unbox = rt.unbox;

// ---------------------------------------------------------------------------------------------
fn ifaceVtStruct(comptime N: usize, comptime names: [N][]const u8, comptime types: [N]type) type {
    const FieldAttr = std.builtin.Type.Struct.FieldAttributes;
    const meta_name: [1][]const u8 = .{"$meta"};
    const meta_type: [1]type = .{*const IfaceMeta};
    const meta_attr: [1]FieldAttr = .{.{}};
    var tc_names: [N][]const u8 = undefined;
    var tc_types: [N]type = undefined;
    var tc_attrs: [N]FieldAttr = undefined;
    const default_null: ?TailFn = null;
    for (0..N) |i| {
        tc_names[i] = names[i] ++ "$tc";
        tc_types[i] = ?TailFn;
        tc_attrs[i] = .{ .default_value_ptr = @ptrCast(&default_null) };
    }
    const base_attrs: [N]FieldAttr = @splat(.{});
    const all_names = meta_name ++ names ++ tc_names;
    const all_types = meta_type ++ types ++ tc_types;
    const all_attrs = meta_attr ++ base_attrs ++ tc_attrs;
    return @Struct(.auto, null, &all_names, &all_types, &all_attrs);
}

pub fn IfaceAnon0() type {
    return struct {
        pub fn of() type {
            return ifaceVtStruct(0, .{}, .{});
        }
    };
}

pub fn IfaceAnon1(comptime names: [1][]const u8) type {
    return struct {
        pub fn of(comptime T1: type) type {
            return ifaceVtStruct(1, names, .{T1});
        }
    };
}

pub fn IfaceAnon2(comptime names: [2][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type) type {
            return ifaceVtStruct(2, names, .{ T1, T2 });
        }
    };
}

pub fn IfaceAnon3(comptime names: [3][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type) type {
            return ifaceVtStruct(3, names, .{ T1, T2, T3 });
        }
    };
}

pub fn IfaceAnon4(comptime names: [4][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type) type {
            return ifaceVtStruct(4, names, .{ T1, T2, T3, T4 });
        }
    };
}

pub fn IfaceAnon5(comptime names: [5][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type) type {
            return ifaceVtStruct(5, names, .{ T1, T2, T3, T4, T5 });
        }
    };
}

pub fn IfaceAnon6(comptime names: [6][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type) type {
            return ifaceVtStruct(6, names, .{ T1, T2, T3, T4, T5, T6 });
        }
    };
}

pub fn IfaceAnon7(comptime names: [7][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type) type {
            return ifaceVtStruct(7, names, .{ T1, T2, T3, T4, T5, T6, T7 });
        }
    };
}

pub fn IfaceAnon8(comptime names: [8][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type) type {
            return ifaceVtStruct(8, names, .{ T1, T2, T3, T4, T5, T6, T7, T8 });
        }
    };
}

pub fn IfaceAnon9(comptime names: [9][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type) type {
            return ifaceVtStruct(9, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9 });
        }
    };
}

pub fn IfaceAnon10(comptime names: [10][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type) type {
            return ifaceVtStruct(10, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10 });
        }
    };
}

pub fn IfaceAnon11(comptime names: [11][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type) type {
            return ifaceVtStruct(11, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11 });
        }
    };
}

pub fn IfaceAnon12(comptime names: [12][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type) type {
            return ifaceVtStruct(12, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 });
        }
    };
}

pub fn IfaceAnon13(comptime names: [13][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type) type {
            return ifaceVtStruct(13, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13 });
        }
    };
}

pub fn IfaceAnon14(comptime names: [14][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type) type {
            return ifaceVtStruct(14, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14 });
        }
    };
}

pub fn IfaceAnon15(comptime names: [15][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type) type {
            return ifaceVtStruct(15, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 });
        }
    };
}

pub fn IfaceAnon16(comptime names: [16][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type) type {
            return ifaceVtStruct(16, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16 });
        }
    };
}

pub fn IfaceAnon17(comptime names: [17][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type) type {
            return ifaceVtStruct(17, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 });
        }
    };
}

pub fn IfaceAnon18(comptime names: [18][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type) type {
            return ifaceVtStruct(18, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18 });
        }
    };
}

pub fn IfaceAnon19(comptime names: [19][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type) type {
            return ifaceVtStruct(19, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19 });
        }
    };
}

pub fn IfaceAnon20(comptime names: [20][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type) type {
            return ifaceVtStruct(20, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20 });
        }
    };
}

pub fn IfaceAnon21(comptime names: [21][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type) type {
            return ifaceVtStruct(21, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21 });
        }
    };
}

pub fn IfaceAnon22(comptime names: [22][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type) type {
            return ifaceVtStruct(22, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22 });
        }
    };
}

pub fn IfaceAnon23(comptime names: [23][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type) type {
            return ifaceVtStruct(23, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23 });
        }
    };
}

pub fn IfaceAnon24(comptime names: [24][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type, comptime T24: type) type {
            return ifaceVtStruct(24, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24 });
        }
    };
}

/// An interface a class implements: the interface (`ifaceId`) and the class's table for it
pub const IfaceImpl = struct { id: *const anyopaque, vt: *const anyopaque };

/// What tells an interface type from the others at run time (a variable of its own: constants
/// of equal values could share an address)
pub fn ifaceId(comptime I: type) *const anyopaque {
    return @ptrCast(&IfaceIdOf(I).tag);
}

fn IfaceIdOf(comptime I: type) type {
    return struct {
        var tag: u8 = @truncate(@sizeOf(I));
    };
}

/// A class's object type with the interfaces it implements
pub fn withIfaces(comptime t: ObjType, comptime ifaces: []const IfaceImpl) ObjType {
    var r = t;
    r.ifaces = ifaces;
    return r;
}

/// The table of interface `C` of the class of `p` (or of a parent class), if it implements it
pub fn objIfaceVt(comptime C: type, p: Obj) ?*const anyopaque {
    var t: ?*const ObjType = p.type;
    while (t) |ty| : (t = ty.parent) {
        for (ty.ifaces) |e| {
            if (e.id == ifaceId(C)) return e.vt;
        }
    }
    return null;
}

/// `o :?> C` of an object of a class that implements interface `C` (a reference of its own)
pub fn objAsIface(comptime C: type, p: Obj) ?C {
    const vt = objIfaceVt(C, p) orelse return null;
    retain(p);
    return C{ .data = @ptrCast(p), .vt = @ptrCast(@alignCast(vt)) };
}

// ---------------------------------------------------------------------------------------------
// Interfaces: fat pointer `{ data, vt }` with a static vtable and metadata hooks
// ---------------------------------------------------------------------------------------------

pub const IfaceMeta = struct {
    retain: *const fn (?*anyopaque) void,
    drop: *const fn (?*anyopaque) void,
    share: *const fn (?*anyopaque) Raised!void,
    iso_reach: *const fn (?*anyopaque, *rt.IsoRegion) void,
    hdr_of: *const fn (?*anyopaque) ?*sgc.Hdr,
    as_obj: *const fn (?*anyopaque) ?Obj,
    find_box: *const fn (?*anyopaque, *const ObjType) ?Obj,
};

fn emptyRetain(_: ?*anyopaque) void {}
fn emptyDrop(_: ?*anyopaque) void {}
fn emptyShare(_: ?*anyopaque) Raised!void {}
fn emptyIsoReach(_: ?*anyopaque, _: *rt.IsoRegion) void {}
fn emptyHdr(_: ?*anyopaque) ?*sgc.Hdr {
    return null;
}
fn emptyAsObj(_: ?*anyopaque) ?Obj {
    return null;
}
fn emptyFindBox(_: ?*anyopaque, _: *const ObjType) ?Obj {
    return null;
}

pub const empty_iface_meta: IfaceMeta = .{
    .retain = emptyRetain,
    .drop = emptyDrop,
    .share = emptyShare,
    .iso_reach = emptyIsoReach,
    .hdr_of = emptyHdr,
    .as_obj = emptyAsObj,
    .find_box = emptyFindBox,
};

fn objIfaceRetain(d: ?*anyopaque) void {
    if (d) |p| retain(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceDrop(d: ?*anyopaque) void {
    if (d) |p| drop(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceShare(d: ?*anyopaque) Raised!void {
    if (d) |p| try markShared(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceIsoReach(d: ?*anyopaque, r: *rt.IsoRegion) void {
    if (d) |p| r.reachOpaque(Obj, @ptrCast(@alignCast(p)));
}
fn objIfaceHdr(d: ?*anyopaque) ?*sgc.Hdr {
    const p = d orelse return null;
    const o: Obj = @ptrCast(@alignCast(p));
    return o.gc;
}
fn objIfaceAsObj(d: ?*anyopaque) ?Obj {
    const p = d orelse return null;
    return @ptrCast(@alignCast(p));
}
fn objIfaceFindBox(d: ?*anyopaque, target_ty: *const ObjType) ?Obj {
    const p = d orelse return null;
    const o: Obj = @ptrCast(@alignCast(p));
    if (o.type == target_ty) return o;
    if (o.type.unwrap_box) |f| return f(o, target_ty);
    return null;
}

pub const obj_iface_meta: IfaceMeta = .{
    .retain = objIfaceRetain,
    .drop = objIfaceDrop,
    .share = objIfaceShare,
    .iso_reach = objIfaceIsoReach,
    .hdr_of = objIfaceHdr,
    .as_obj = objIfaceAsObj,
    .find_box = objIfaceFindBox,
};

pub const box_iface_meta = obj_iface_meta;

fn envIfaceRetain(d: ?*anyopaque) void {
    if (d) |p| retain(@as(*Env, @ptrCast(@alignCast(p))));
}
fn envIfaceDrop(d: ?*anyopaque) void {
    if (d) |p| dropEnv(@ptrCast(@alignCast(p)));
}
fn envIfaceShare(d: ?*anyopaque) Raised!void {
    if (d) |p| {
        const e: *Env = @ptrCast(@alignCast(p));
        if (!try markCell(e)) return;
        return e.share(e);
    }
}
fn envIfaceIsoReach(d: ?*anyopaque, r: *rt.IsoRegion) void {
    if (d) |p| r.reachOpaque(*Env, @ptrCast(@alignCast(p)));
}
fn envIfaceHdr(d: ?*anyopaque) ?*sgc.Hdr {
    const p = d orelse return null;
    const e: *Env = @ptrCast(@alignCast(p));
    return e.gc;
}

pub const env_iface_meta: IfaceMeta = .{
    .retain = envIfaceRetain,
    .drop = envIfaceDrop,
    .share = envIfaceShare,
    .iso_reach = envIfaceIsoReach,
    .hdr_of = envIfaceHdr,
    .as_obj = emptyAsObj,
    .find_box = emptyFindBox,
};

pub fn upcastIfaceMeta(comptime SubIface: type) *const IfaceMeta {
    return &struct {
        fn asObj(d: ?*anyopaque) ?Obj {
            const p = d orelse return null;
            const o: Obj = @ptrCast(@alignCast(p));
            const sub = boxed(SubIface, o).value;
            return sub.vt.@"$meta".as_obj(sub.data);
        }
        fn findBox(d: ?*anyopaque, target_ty: *const ObjType) ?Obj {
            const p = d orelse return null;
            const o: Obj = @ptrCast(@alignCast(p));
            if (o.type == target_ty) return o;
            const sub = boxed(SubIface, o).value;
            return sub.vt.@"$meta".find_box(sub.data, target_ty);
        }
        const meta: IfaceMeta = .{
            .retain = objIfaceRetain,
            .drop = objIfaceDrop,
            .share = objIfaceShare,
            .iso_reach = objIfaceIsoReach,
            .hdr_of = objIfaceHdr,
            .as_obj = asObj,
            .find_box = findBox,
        };
    }.meta;
}

pub fn Iface(comptime Vt: type) type {
    return struct {
        pub const fable_iface = {};
        data: ?*anyopaque,
        vt: *const Vt,
    };
}

pub fn isIface(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_iface");
}

/// Box `val` directly into a fat-pointer interface (consumes `val`).
pub inline fn ifaceBox(comptime I: type, comptime T: type, val: T, vt: @FieldType(I, "vt")) I {
    const o = ObjCell(BoxChain(T)).new(boxType(T), .{ .own = .{ .value = val } });
    return .{ .data = @ptrCast(o), .vt = vt };
}

/// Allocate an environment holding `captures` for an object-expression fat-pointer interface (consumes `captures`).
pub inline fn ifaceClosure(comptime I: type, comptime Captures: type, captures: Captures, vt: @FieldType(I, "vt")) I {
    if (@sizeOf(Captures) == 0) return .{ .data = null, .vt = vt };
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = rt.alloc().create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .data = @ptrCast(&e.header), .vt = vt };
}

// ---- generic methods of interfaces: one slot, its type parameters erased to `obj` (as Koka
// compiles polymorphism), and values converted where the slot is called ----

fn ifaceOf(comptime T: type) ?type {
    if (isIface(T)) return T;
    if (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) return @typeInfo(T).optional.child;
    return null;
}

/// `x` (borrowed) as a value of type `To` (owned): the same, boxed into an object, unboxed from
/// one, or an interface adapted to its erased instantiation (or back)
pub fn erasedConv(comptime To: type, x: anytype) To {
    const From = @TypeOf(x);
    if (From == To) return dup(x);
    if (To == Any) return box(x);
    if (From == Any) {
        if (tryUnbox(?To, x)) |v| return v;
        @panic("fable: an erased value of a generic method is not of the type it is used as");
    }
    if (comptime ifaceOf(To) != null and ifaceOf(From) != null) return ifaceAdapt(To, x);
    @compileError("fable: a generic method of an interface cannot convert " ++ @typeName(From) ++ " to " ++ @typeName(To) ++ " yet");
}

/// The interface `src` (borrowed) seen as the interface type `Target`, whose members take and give
/// the same values erased to `obj` (or the other way): each member converts what it is given
/// (a member takes its arguments over, as every slot does), calls the member of `src` with them,
/// and converts what it gives back
pub fn ifaceAdapt(comptime Target: type, src: anytype) Target {
    const S = @TypeOf(src);
    const I = ifaceOf(Target).?;
    const SI = ifaceOf(S).?;
    const s: SI = if (comptime @typeInfo(S) == .optional) (src orelse return if (comptime @typeInfo(Target) == .optional) null else nullRefPanic()) else src;
    const A = IfaceAdapter(I, SI);
    return ifaceClosure(I, A.Held, .{ .c0 = dup(s) }, &A.vt);
}

fn nullRefPanic() noreturn {
    @panic("fable: a null interface given to a generic method");
}

fn erasedBack(comptime R: type, raw: anytype) R {
    const Raw = @TypeOf(raw);
    if (comptime @typeInfo(Raw) == .error_union) {
        const v = raw catch {
            if (comptime @typeInfo(R) == .error_union) return error.Raised;
            @panic("fable: an erased member raised where its slot cannot");
        };
        return erasedBack(R, v);
    }
    const Out = if (@typeInfo(R) == .error_union) @typeInfo(R).error_union.payload else R;
    const out = erasedConv(Out, raw);
    drop(raw);
    return out;
}

fn IfaceAdapter(comptime I: type, comptime SI: type) type {
    const Vt = @typeInfo(@FieldType(I, "vt")).pointer.child;
    const SVt = @typeInfo(@FieldType(SI, "vt")).pointer.child;
    return struct {
        const Held = struct { c0: SI };

        fn Thunk(comptime name: []const u8) type {
            const F = @typeInfo(@typeInfo(@FieldType(Vt, name)).pointer.child).@"fn";
            const SF = @typeInfo(@typeInfo(@FieldType(SVt, name)).pointer.child).@"fn";
            const R = F.return_type.?;
            const P = F.param_types;
            const SP = SF.param_types;
            return switch (P.len) {
                2 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0));
                    }
                },
                3 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?, a1: P[2].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        const x1 = erasedConv(SP[2].?, a1);
                        drop(a1);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0, x1));
                    }
                },
                4 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?, a1: P[2].?, a2: P[3].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        const x1 = erasedConv(SP[2].?, a1);
                        drop(a1);
                        const x2 = erasedConv(SP[3].?, a2);
                        drop(a2);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0, x1, x2));
                    }
                },
                else => @compileError("fable: an interface member of this many parameters cannot be adapted yet"),
            };
        }

        const vt: Vt = blk: {
            var v: Vt = undefined;
            for (@typeInfo(Vt).@"struct".field_names) |name| {
                if (std.mem.eql(u8, name, "$meta")) {
                    v.@"$meta" = &env_iface_meta;
                } else if (std.mem.endsWith(u8, name, "$tc")) {
                    @field(v, name) = null;
                } else {
                    @field(v, name) = Thunk(name).f;
                }
            }
            break :blk v;
        };
    };
}

/// Extract a first-class `Func` closure from a fat-pointer interface method slot (borrows `iface`).
pub fn ifaceMethod(comptime F: type, iface: anytype, comptime field: []const u8) F {
    const I = @TypeOf(iface);
    const Caps = struct { iface: I };
    const Fn = @typeInfo(@typeInfo(@FieldType(F, "code")).pointer.child).@"fn";
    const R = Fn.return_type.?;
    const P = Fn.param_types;
    const M = switch (P.len) {
        1 => struct {
            fn code(env: ?*Env) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data);
            }
        },
        2 => struct {
            fn code(env: ?*Env, a0: P[1].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0);
            }
        },
        3 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1);
            }
        },
        4 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2);
            }
        },
        5 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3);
            }
        },
        6 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4);
            }
        },
        7 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5);
            }
        },
        8 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?, a6: P[7].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5, a6);
            }
        },
        9 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?, a6: P[7].?, a7: P[8].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5, a6, a7);
            }
        },
        else => @compileError("fable: interface method of this many arguments"),
    };
    return closure(F, Caps, .{ .iface = dup(iface) }, M.code);
}

/// Borrow the underlying `Obj` from an interface value or optional interface, if any.
pub inline fn ifaceToObjBorrow(x: anytype) ?Obj {
    const T = @TypeOf(x);
    if (comptime @typeInfo(T) == .optional) {
        const v = x orelse return null;
        return v.vt.@"$meta".as_obj(v.data);
    }
    return x.vt.@"$meta".as_obj(x.data);
}

pub fn ifaceToAnyBorrow(x: anytype) Any {
    return ifaceToObjBorrow(x);
}

pub fn ifaceIsClass(x: anytype, ty: *const ObjType) bool {
    const o = ifaceToObjBorrow(x) orelse return false;
    return objIs(o, ty);
}

pub fn ifaceCastClass(x: anytype, ty: *const ObjType) Raised!Any {
    if (comptime @typeInfo(@TypeOf(x)) == .optional) {
        if (x == null) return null;
    }
    if (ifaceToObjBorrow(x)) |o| return objCast(o, ty);
    const Short = struct {
        pub fn of(name: []const u8) []const u8 {
            return if (std.mem.lastIndexOfScalar(u8, name, '+')) |i| name[i + 1 ..] else name;
        }
    };
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '<iface>' to type '");
    b.addAscii(Short.of(ty.name));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}

pub fn ifaceTryUnbox(comptime OT: type, x: anytype) OT {
    const T = @typeInfo(OT).optional.child;
    const v = if (comptime @typeInfo(@TypeOf(x)) == .optional)
        (x orelse return if (T == void) {} else null)
    else
        x;
    if (T == void) return null;
    const V = @TypeOf(v);
    if (comptime V == T) return dup(v);
    if (comptime (@typeInfo(T) == .optional and @typeInfo(T).optional.child == V)) return @as(T, dup(v));
    if (T == Any or T == Obj) {
        if (ifaceToObjBorrow(v)) |o| return dup(o);
        return box(v);
    }
    if (comptime (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child))) {
        const C = @typeInfo(T).optional.child;
        if (v.vt.@"$meta".find_box(v.data, boxType(C))) |bp| return @as(T, dup(boxed(C, bp).value));
    }
    if (v.vt.@"$meta".find_box(v.data, boxType(T))) |bp| return dup(boxed(T, bp).value);
    if (ifaceToObjBorrow(v)) |o| return tryUnbox(OT, @as(Any, o));
    return null;
}

pub fn ifaceUnbox(comptime T: type, x: anytype) Raised!T {
    const v = if (comptime @typeInfo(@TypeOf(x)) == .optional)
        (x orelse {
            if (T == void) return {};
            if (comptime @typeInfo(T) == .optional) return null;
            if (comptime isArrayPtr(T)) return arrayNull(T);
            return nullRef();
        })
    else
        x;
    const V = @TypeOf(v);
    if (comptime V == T) return dup(v);
    if (comptime (@typeInfo(T) == .optional and @typeInfo(T).optional.child == V)) return @as(T, dup(v));
    if (T == Any) return box(v);
    if (T == Obj) {
        if (ifaceToObjBorrow(v)) |o| return dup(o);
        return box(v).?;
    }
    if (comptime (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child))) {
        const C = @typeInfo(T).optional.child;
        if (v.vt.@"$meta".find_box(v.data, boxType(C))) |bp| return @as(T, dup(boxed(C, bp).value));
    }
    if (v.vt.@"$meta".find_box(v.data, boxType(T))) |bp| return dup(boxed(T, bp).value);
    if (ifaceToObjBorrow(v)) |o| return unbox(T, @as(Any, o));
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '<iface>' to type '");
    b.addAscii(netTypeName(T));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}
