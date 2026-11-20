//! C interop (`DllImport`, `c:`, `NativePtr`, `Marshal`, `NativeMemory`, `MemoryMarshal`, `Unsafe`,
//! `NativeLibrary`, `StackAlloc`) shared by F# programs compiled to Zig (part of fable_rt.zig, which re-exports it).
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");

const Any = rt.Any;
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const FileNotFoundException = rt.FileNotFoundException;
const NotSupportedException = rt.NotSupportedException;
const OutOfMemoryException = rt.OutOfMemoryException;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const String = rt.String;
const Unraised = rt.Unraised;
const alloc = rt.alloc;
const arrayIsNull = rt.arrayIsNull;
const io = rt.io;
const isArrayPtr = rt.isArrayPtr;
const isCellPtr = rt.isCellPtr;
const isFunc = rt.isFunc;
const isManaged = rt.isManaged;
const isNullOf = rt.isNullOf;
const isRaised = rt.isRaised;
const isRawPtr = rt.isRawPtr;
const isSlice = rt.isSlice;
const oom = rt.oom;
const raise = rt.raise;
const str = rt.str;
const strFrom = rt.strFrom;
const uncaught = rt.uncaught;
const unitsOf = rt.unitsOf;

// ---------------------------------------------------------------------------------------------
// C strings & CKind marshalling
// ---------------------------------------------------------------------------------------------

/// A string given to C for one call (UTF-8 zero-terminated on stack when small)
const CString = struct {
    small: [256]u8 = undefined,
    big: ?[]u8 = null,

    fn init(c: *CString, s: String) [*:0]const u8 {
        const units = unitsOf(s);
        const need = units.len * 3 + 1;
        const buf: []u8 = if (need <= c.small.len) &c.small else blk: {
            const b = alloc().alloc(u8, need) catch oom();
            c.big = b;
            break :blk b;
        };
        const n = std.unicode.wtf16LeToWtf8(buf, units);
        buf[n] = 0;
        return @ptrCast(buf.ptr);
    }

    fn deinit(c: *CString) void {
        if (c.big) |b| alloc().free(b);
    }
};

/// A string given to C as UTF-16 for one call
const CWString = struct {
    small: [128]u16 = undefined,
    big: ?[]u16 = null,

    fn init(c: *CWString, s: String) [*:0]const u16 {
        const units = unitsOf(s);
        const buf: []u16 = if (units.len + 1 <= c.small.len) &c.small else blk: {
            const b = alloc().alloc(u16, units.len + 1) catch oom();
            c.big = b;
            break :blk b;
        };
        @memcpy(buf[0..units.len], units);
        buf[units.len] = 0;
        return @ptrCast(buf.ptr);
    }

    fn deinit(c: *CWString) void {
        if (c.big) |b| alloc().free(b);
    }
};

/// How a value crosses to C (`[<MarshalAs>]`, DllImport's `CharSet`, LibraryImport's `StringMarshalling`):
/// `.plain` as it is; a bool as .NET's 4-byte `BOOL` (`.bool4`) or C99 1-byte `_Bool` (`.bool1`);
/// a string as UTF-8 (`.utf8`) or UTF-16 (`.utf16`); `.cb_bool1` for C99 `_Bool` delegate returns.
pub const CKind = enum { plain, bool4, bool1, utf8, utf16, cb_bool1 };

pub fn isExternC(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .@"struct" and info.@"struct".layout == .@"extern" and !isManaged(T);
}

pub fn isExternUnion(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .@"union" and info.@"union".tag_type == null and !isManaged(T);
}

fn isAllowedFieldType(comptime T: type) bool {
    if (isRawPtr(T)) return true;
    return switch (@typeInfo(T)) {
        .int, .float, .bool => true,
        .array => |a| isAllowedFieldType(a.child),
        .@"struct" => isExternC(T) or isPlainStruct(T),
        .@"union" => isExternUnion(T),
        else => false,
    };
}

/// Is T a non-extern Zig struct of numbers, bools, raw pointers, fixed arrays, extern unions, or nested such structs?
fn isPlainStruct(comptime T: type) bool {
    return comptime blk: {
        const info = @typeInfo(T);
        if (info != .@"struct") break :blk false;
        if (info.@"struct".is_tuple or isManaged(T)) break :blk false;
        if (info.@"struct".layout == .@"packed" or info.@"struct".layout == .@"extern") break :blk false;
        for (info.@"struct".field_types) |F| {
            if (!isAllowedFieldType(F)) break :blk false;
        }
        break :blk info.@"struct".field_names.len != 0;
    };
}

/// The C layout of a non-extern plain struct
fn CStruct(comptime T: type) type {
    const st = @typeInfo(T).@"struct";
    if (st.layout == .@"extern") return T;
    var types: [st.field_names.len]type = undefined;
    for (st.field_types, 0..) |F, i| types[i] = if (isPlainStruct(F)) CStruct(F) else F;
    return @Struct(.@"extern", null, st.field_names, &types, &@splat(.{}));
}

fn convertArray(comptime Dest: type, x: anytype, comptime to_c: bool) Dest {
    const info = @typeInfo(Dest).array;
    var out: Dest = undefined;
    inline for (0..info.len) |i| {
        const Elem = info.child;
        out[i] = if (@typeInfo(Elem) == .@"struct")
            (if (to_c) toCStruct(Elem, x[i]) else fromCStruct(Elem, x[i]))
        else
            x[i];
    }
    return out;
}

/// `x` as the struct `C` (a C struct of the same field names: `CStruct(T)`, or one from a C header)
fn toCStruct(comptime C: type, x: anytype) C {
    var c: C = undefined;
    inline for (@typeInfo(C).@"struct".field_names) |name| {
        if (!@hasField(@TypeOf(x), name)) @compileError("fable: the C struct " ++ @typeName(C) ++ " has a field `" ++ name ++ "` that " ++ @typeName(@TypeOf(x)) ++ " has not");
        const F = @FieldType(C, name);
        const v = @field(x, name);
        @field(c, name) = if (@typeInfo(F) == .@"struct" and F != @TypeOf(v))
            toCStruct(F, v)
        else if (@typeInfo(F) == .array and @typeInfo(@TypeOf(v)) == .array and F != @TypeOf(v))
            convertArray(F, v, true)
        else if (@typeInfo(F) == .float and @TypeOf(v) != F)
            @floatCast(v)
        else if (@typeInfo(F) == .int and @TypeOf(v) != F)
            @intCast(v)
        else
            v;
    }
    return c;
}

/// A C struct `c` as the F# struct T
fn fromCStruct(comptime T: type, c: anytype) T {
    var x: T = undefined;
    inline for (@typeInfo(T).@"struct".field_names) |name| {
        const F = @FieldType(T, name);
        const v = @field(c, name);
        @field(x, name) = if (@typeInfo(F) == .@"struct" and F != @TypeOf(v))
            fromCStruct(F, v)
        else if (@typeInfo(F) == .array and @typeInfo(@TypeOf(v)) == .array and F != @TypeOf(v))
            convertArray(F, v, false)
        else if (@typeInfo(F) == .float and @TypeOf(v) != F)
            @floatCast(v)
        else if (@typeInfo(F) == .int and @TypeOf(v) != F)
            @intCast(v)
        else
            v;
    }
    return x;
}

/// (a byref / inref / outref: `*T` or `*const T` of a value, not a counted cell or `anyopaque`)
fn isByref(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .pointer and info.pointer.size == .one and !isCellPtr(T) and @typeInfo(info.pointer.child) != .@"fn" and @typeInfo(info.pointer.child) != .@"opaque" and info.pointer.child != anyopaque;
}

/// What C is given for a value of type T, crossing as `kind`
fn CArg(comptime T: type, comptime kind: CKind) type {
    if (T == String) return if (kind == .utf16) ?[*:0]const u16 else ?[*:0]const u8;
    if (T == bool) return if (kind == .bool1 or kind == .cb_bool1) bool else i32;
    if (comptime isRawPtr(T)) return T;
    if (comptime isArrayPtr(T)) return ?[*]@typeInfo(@FieldType(@typeInfo(T).pointer.child, "items")).pointer.child;
    if (comptime isSlice(T)) {
        const p = @typeInfo(T).pointer;
        return if (p.attrs.@"const") ?[*]const p.child else ?[*]p.child;
    }
    if (comptime isExternC(T) or isExternUnion(T)) return T;
    if (comptime isPlainStruct(T)) return CStruct(T);
    if (comptime isFunc(T)) return CallbackFn(kind, T);
    if (comptime isByref(T)) {
        const p = @typeInfo(T).pointer;
        const V = p.child;
        if (V == bool) {
            if (kind == .bool1) return T;
            return if (p.attrs.@"const") *const i32 else *i32;
        }
        if (comptime isExternC(V) or isExternUnion(V) or isRawPtr(V) or @typeInfo(V) == .int or @typeInfo(V) == .float) return T;
        if (comptime isPlainStruct(V)) {
            const C = CStruct(V);
            return if (p.attrs.@"const") *const C else *C;
        }
        @compileError("fable: a [<DllImport>] function's byref (out, ref, inref) parameter is of a number, a bool, a raw pointer, or a C ABI struct/union; not " ++ @typeName(V));
    }
    if (comptime isManaged(T)) @compileError("fable: a [<DllImport>] function takes and gives numbers, bools, strings, arrays, spans, delegates, raw pointers, byrefs and C ABI structs/unions; not " ++ @typeName(T));
    return T;
}

/// What a byref's value is copied into for the call (and back after when non-const): a C struct, a `BOOL`
fn CTemp(comptime T: type, comptime kind: CKind) type {
    if (!isByref(T)) return void;
    const V = @typeInfo(T).pointer.child;
    if (V == bool) return if (kind == .bool1) void else i32;
    if (isPlainStruct(V)) return CStruct(V);
    return void;
}

/// A result of C as F#'s `R`
fn fromC(comptime R: type, comptime kind: CKind, r: anytype) R {
    if (R == String) {
        if (kind == .utf16) {
            const p: ?[*:0]const u16 = r;
            return if (p) |q| strFrom(std.mem.span(q)) else null;
        }
        const p: ?[*:0]const u8 = r;
        return if (p) |q| io.fromUtf8(std.mem.span(q)) else null;
    }
    if (R == bool) return if (kind == .bool1 or kind == .cb_bool1) r else r != 0;
    if (comptime isPlainStruct(R)) return fromCStruct(R, r);
    return r;
}

/// An F# value as C's (a callback's result)
fn toC(comptime T: type, comptime kind: CKind, x: T) CArg(T, kind) {
    if (T == bool) return if (kind == .bool1 or kind == .cb_bool1) x else @intFromBool(x);
    if (comptime isPlainStruct(T)) return toCStruct(CStruct(T), x);
    return x;
}

fn CFn(comptime P: []const type, comptime R: type) type {
    return switch (P.len) {
        0 => *const fn () callconv(.c) R,
        1 => *const fn (P[0]) callconv(.c) R,
        2 => *const fn (P[0], P[1]) callconv(.c) R,
        3 => *const fn (P[0], P[1], P[2]) callconv(.c) R,
        4 => *const fn (P[0], P[1], P[2], P[3]) callconv(.c) R,
        5 => *const fn (P[0], P[1], P[2], P[3], P[4]) callconv(.c) R,
        6 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5]) callconv(.c) R,
        7 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6]) callconv(.c) R,
        8 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7]) callconv(.c) R,
        9 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8]) callconv(.c) R,
        10 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9]) callconv(.c) R,
        11 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10]) callconv(.c) R,
        12 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10], P[11]) callconv(.c) R,
        13 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10], P[11], P[12]) callconv(.c) R,
        14 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10], P[11], P[12], P[13]) callconv(.c) R,
        15 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10], P[11], P[12], P[13], P[14]) callconv(.c) R,
        16 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[8], P[9], P[10], P[11], P[12], P[13], P[14], P[15]) callconv(.c) R,
        else => @compileError("fable: a C function of more than sixteen arguments"),
    };
}

// ---------------------------------------------------------------------------------------------
// Callbacks & CallbackPool
// ---------------------------------------------------------------------------------------------

fn Callback(comptime name: []const u8, comptime index: usize, comptime kind: CKind, comptime F: type) type {
    _ = name;
    _ = index;
    const cb_ret_kind: CKind = if (kind == .cb_bool1) .bool1 else .plain;
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (comptime isRaised(RR)) Unraised(RR) else RR;
    const CR = CArg(R, cb_ret_kind);
    return struct {
        threadlocal var current: ?F = null;
        var latest: ?F = null;
        var guard = std.atomic.Value(u32).init(0);

        fn setLatest(f: F) void {
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            latest = f;
            guard.store(0, .release);
        }

        fn delegate() F {
            if (current) |f| return f;
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            const f = latest;
            guard.store(0, .release);
            return f orelse @panic("fable: a C callback was called with no delegate given for it");
        }

        fn invoke(c_args: anytype) CR {
            const f = delegate();
            var f_args: std.meta.ArgsTuple(Code) = undefined;
            f_args[0] = f.env;
            inline for (P, 0..) |A, i| {
                const a = c_args[i];
                f_args[i + 1] = if (A.? == String) strFromCStr(a) else fromC(A.?, .plain, a);
            }
            const result = @call(.auto, f.code, f_args);
            const value = if (comptime isRaised(RR)) result catch {
                uncaught();
                std.process.abort();
            } else result;
            return toC(R, cb_ret_kind, value);
        }

        const C = blk: {
            var ps: [P.len]type = undefined;
            for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
            break :blk ps;
        };

        const code = switch (P.len) {
            0 => struct {
                fn f() callconv(.c) CR {
                    return invoke(.{});
                }
            }.f,
            1 => struct {
                fn f(a: C[0]) callconv(.c) CR {
                    return invoke(.{a});
                }
            }.f,
            2 => struct {
                fn f(a: C[0], b: C[1]) callconv(.c) CR {
                    return invoke(.{ a, b });
                }
            }.f,
            3 => struct {
                fn f(a: C[0], b: C[1], c: C[2]) callconv(.c) CR {
                    return invoke(.{ a, b, c });
                }
            }.f,
            4 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d });
                }
            }.f,
            5 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d, e });
                }
            }.f,
            6 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d, e, g });
                }
            }.f,
            7 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5], h: C[6]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d, e, g, h });
                }
            }.f,
            8 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5], h: C[6], k: C[7]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d, e, g, h, k });
                }
            }.f,
            else => @compileError("fable: a callback of more than eight arguments"),
        };
    };
}

/// The nullable C function pointer type of a callback for a delegate of type F
fn CallbackFn(comptime kind: CKind, comptime F: type) type {
    const cb_ret_kind: CKind = if (kind == .cb_bool1) .bool1 else .plain;
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (comptime isRaised(RR)) Unraised(RR) else RR;
    var ps: [P.len]type = undefined;
    for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
    return ?CFn(&ps, CArg(R, cb_ret_kind));
}

/// Comptime-generated slot pool of C thunks for `Marshal.GetFunctionPointerForDelegate`.
pub fn CallbackPool(comptime F: type, comptime capacity: usize) type {
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (comptime isRaised(RR)) Unraised(RR) else RR;
    const CR = CArg(R, .plain);
    const C = blk: {
        var ps: [P.len]type = undefined;
        for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
        break :blk ps;
    };
    const FnPtr = CFn(&C, CR);

    return struct {
        var slots: [capacity]?F = @splat(null);
        var guard = std.atomic.Value(u32).init(0);

        fn invokeSlot(comptime slot: usize, c_args: anytype) CR {
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            const f = slots[slot];
            guard.store(0, .release);
            const target = f orelse @panic("fable: callback pool slot is empty");
            var f_args: std.meta.ArgsTuple(Code) = undefined;
            f_args[0] = target.env;
            inline for (P, 0..) |A, i| {
                const a = c_args[i];
                f_args[i + 1] = if (A.? == String) strFromCStr(a) else fromC(A.?, .plain, a);
            }
            const result = @call(.auto, target.code, f_args);
            const value = if (comptime isRaised(RR)) result catch {
                uncaught();
                std.process.abort();
            } else result;
            return toC(R, .plain, value);
        }

        fn thunk(comptime slot: usize) FnPtr {
            return switch (P.len) {
                0 => struct {
                    fn f() callconv(.c) CR {
                        return invokeSlot(slot, .{});
                    }
                }.f,
                1 => struct {
                    fn f(a: C[0]) callconv(.c) CR {
                        return invokeSlot(slot, .{a});
                    }
                }.f,
                2 => struct {
                    fn f(a: C[0], b: C[1]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b });
                    }
                }.f,
                3 => struct {
                    fn f(a: C[0], b: C[1], c: C[2]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c });
                    }
                }.f,
                4 => struct {
                    fn f(a: C[0], b: C[1], c: C[2], d: C[3]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c, d });
                    }
                }.f,
                5 => struct {
                    fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c, d, e });
                    }
                }.f,
                6 => struct {
                    fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c, d, e, g });
                    }
                }.f,
                7 => struct {
                    fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5], h: C[6]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c, d, e, g, h });
                    }
                }.f,
                8 => struct {
                    fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4], g: C[5], h: C[6], k: C[7]) callconv(.c) CR {
                        return invokeSlot(slot, .{ a, b, c, d, e, g, h, k });
                    }
                }.f,
                else => @compileError("fable: a callback of more than eight arguments"),
            };
        }

        const table: [capacity]FnPtr = blk: {
            var arr: [capacity]FnPtr = undefined;
            for (0..capacity) |i| arr[i] = thunk(i);
            break :blk arr;
        };

        pub fn allocPtr(f: F) Raised!isize {
            if (isNullOf(f)) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'd')"));
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            defer guard.store(0, .release);
            for (slots, 0..) |maybe, i| {
                if (maybe) |existing| {
                    if (existing.code == f.code and existing.env == f.env) {
                        return @bitCast(@intFromPtr(table[i]));
                    }
                }
            }
            for (&slots, 0..) |*slot, i| {
                if (slot.* == null) {
                    slot.* = f;
                    return @bitCast(@intFromPtr(table[i]));
                }
            }
            return raise(NotSupportedException, str("CallbackPool exhausted (max 32 distinct delegates per signature)"));
        }

        pub fn findByPtr(ptr: isize) ?F {
            const addr: usize = @bitCast(ptr);
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            defer guard.store(0, .release);
            for (slots, 0..) |maybe, i| {
                if (@intFromPtr(table[i]) == addr) return maybe;
            }
            return null;
        }
    };
}

// ---------------------------------------------------------------------------------------------
// P/Invoke & C calls (`callC` / `cCall`)
// ---------------------------------------------------------------------------------------------

/// `f args` of `[<DllImport>] extern R f(...)`: the C function `name`, each argument crossing as
/// its kind in `kinds`, the result as `ret`
pub fn callC(comptime R: type, comptime name: []const u8, comptime kinds: anytype, comptime ret: CKind, args: anytype) R {
    const fields = @typeInfo(@TypeOf(args)).@"struct".field_types;
    const n = fields.len;
    const params = comptime blk: {
        var ps: [n]type = undefined;
        for (fields, 0..) |F, i| ps[i] = CArg(F, kinds[i]);
        break :blk ps;
    };
    const temp_types = comptime blk: {
        var ts: [n]type = undefined;
        for (fields, 0..) |F, i| ts[i] = CTemp(F, kinds[i]);
        break :blk ts;
    };
    var c_args: @Tuple(&params) = undefined;
    var temps: @Tuple(&temp_types) = undefined;
    var strings: [n]CString = undefined;
    var wide: [n]CWString = undefined;
    inline for (0..n) |i| {
        const F = fields[i];
        const kind: CKind = kinds[i];
        if (F == String) {
            if (kind == .utf16) {
                wide[i] = .{};
                c_args[i] = if (args[i] == null) null else wide[i].init(args[i]);
            } else {
                strings[i] = .{};
                c_args[i] = if (args[i] == null) null else strings[i].init(args[i]);
            }
        } else if (comptime isArrayPtr(F)) {
            c_args[i] = if (arrayIsNull(args[i])) null else args[i].items.ptr;
        } else if (comptime isSlice(F)) {
            c_args[i] = if (args[i].len == 0) null else args[i].ptr;
        } else if (comptime isPlainStruct(F)) {
            c_args[i] = toCStruct(CStruct(F), args[i]);
        } else if (comptime isFunc(F)) {
            if (isNullOf(args[i])) {
                c_args[i] = null;
            } else {
                const Cb = Callback(name, i, kinds[i], F);
                Cb.setLatest(args[i]);
                c_args[i] = &Cb.code;
            }
        } else if (comptime temp_types[i] != void) {
            const V = @typeInfo(F).pointer.child;
            temps[i] = if (V == bool) @intFromBool(args[i].*) else toCStruct(temp_types[i], args[i].*);
            c_args[i] = &temps[i];
        } else if (F == bool) {
            c_args[i] = if (kind == .bool1 or kind == .cb_bool1) args[i] else @intFromBool(args[i]);
        } else {
            c_args[i] = args[i];
        }
    }
    // (the delegates of this call, for callbacks that come while it runs on this thread)
    const saved_types = comptime blk: {
        var ts: [n]type = undefined;
        for (fields, 0..) |F, i| ts[i] = if (isFunc(F)) ?F else void;
        break :blk ts;
    };
    var saved: @Tuple(&saved_types) = undefined;
    inline for (0..n) |i| {
        if (comptime isFunc(fields[i])) {
            const Cb = Callback(name, i, kinds[i], fields[i]);
            saved[i] = Cb.current;
            Cb.current = if (isNullOf(args[i])) null else args[i];
        }
    }
    defer inline for (0..n) |i| {
        if (fields[i] == String) {
            if (kinds[i] == .utf16) wide[i].deinit() else strings[i].deinit();
        }
        if (comptime isFunc(fields[i])) Callback(name, i, kinds[i], fields[i]).current = saved[i];
    };
    const CR = comptime if (R == String) (if (ret == .utf16) ?[*:0]const u16 else ?[*:0]const u8) else CArg(R, ret);
    const f = @extern(CFn(&params, CR), .{ .name = name });
    const r = @call(.auto, f, c_args);
    // (what C wrote into mutable byrefs' copies, back into them; inrefs stay immutable)
    inline for (0..n) |i| {
        if (comptime temp_types[i] != void and !@typeInfo(fields[i]).pointer.attrs.@"const") {
            const V = @typeInfo(fields[i]).pointer.child;
            args[i].* = if (V == bool) temps[i] != 0 else fromCStruct(V, temps[i]);
        }
    }
    return fromC(R, ret, r);
}

/// `f args` of a C function imported with `[<Import("f", "c:module")>]`
pub fn cCall(comptime R: type, f: anytype, args: anytype) R {
    const P = @typeInfo(@TypeOf(f)).@"fn".param_types;
    const fields = @typeInfo(@TypeOf(args)).@"struct".field_types;
    if (P.len != fields.len) @compileError("fable: the C function takes " ++ std.fmt.comptimePrint("{d}", .{P.len}) ++ " arguments");
    const params = comptime blk: {
        var ps: [P.len]type = undefined;
        for (P, 0..) |p, i| ps[i] = p.?;
        break :blk ps;
    };
    var c_args: @Tuple(&params) = undefined;
    var strings: [fields.len]CString = undefined;
    inline for (0..fields.len) |i| {
        const F = fields[i];
        if (F == String) {
            strings[i] = .{};
            c_args[i] = if (args[i] == null) @ptrFromInt(0) else @ptrCast(strings[i].init(args[i]));
        } else if (comptime isArrayPtr(F)) {
            if (arrayIsNull(args[i])) {
                const pi = @typeInfo(params[i]);
                c_args[i] = if (pi == .optional or (pi == .pointer and pi.pointer.size == .c)) null else @ptrCast(args[i].items.ptr);
            } else {
                c_args[i] = @ptrCast(args[i].items.ptr);
            }
        } else if (comptime isSlice(F)) {
            if (args[i].len == 0) {
                const pi = @typeInfo(params[i]);
                c_args[i] = if (pi == .optional or (pi == .pointer and pi.pointer.size == .c)) null else @ptrCast(args[i].ptr);
            } else {
                c_args[i] = @ptrCast(args[i].ptr);
            }
        } else if (comptime @typeInfo(F) == .int and @typeInfo(params[i]) == .int) {
            c_args[i] = @intCast(args[i]);
        } else if (comptime @typeInfo(F) == .float and @typeInfo(params[i]) == .float) {
            c_args[i] = @floatCast(args[i]);
        } else if (comptime (isPlainStruct(F) or isExternC(F)) and @typeInfo(params[i]) == .@"struct" and params[i] != F) {
            c_args[i] = toCStruct(params[i], args[i]);
        } else {
            c_args[i] = args[i];
        }
    }
    defer inline for (0..fields.len) |i| {
        if (fields[i] == String) strings[i].deinit();
    };
    const r = @call(.auto, f, c_args);
    const T = @TypeOf(r);
    if (R == String) {
        const p: ?[*:0]const u8 = @ptrCast(r);
        return if (p) |q| io.fromUtf8(std.mem.span(q)) else null;
    }
    if (comptime T == R) return r;
    if (comptime (isPlainStruct(R) or isExternC(R)) and @typeInfo(T) == .@"struct") return fromCStruct(R, r);
    if (comptime @typeInfo(T) == .int and @typeInfo(R) == .int) return @intCast(r);
    if (comptime @typeInfo(T) == .float and @typeInfo(R) == .float) return @floatCast(r);
    if (comptime @typeInfo(T) == .bool and @typeInfo(R) == .bool) return r;
    return r;
}

/// For Zig code of the program's: UTF-8 Z-string, which the caller frees (`fable_rt.allocator`),
/// and conversions from UTF-8 bytes or C string (copied).
pub fn strToUtf8Z(s: String) [:0]u8 {
    const units = unitsOf(s);
    const buf = rt.allocator.allocSentinel(u8, std.unicode.calcWtf8Len(units), 0) catch oom();
    _ = std.unicode.wtf16LeToWtf8(buf, units);
    return buf;
}

pub fn strFromUtf8(bytes: []const u8) String {
    return io.fromUtf8(bytes);
}

pub fn strFromCStr(p: ?[*:0]const u8) String {
    const q = p orelse return null;
    return io.fromUtf8(std.mem.span(q));
}

// ---------------------------------------------------------------------------------------------
// `NativePtr.stackalloc` and `Span(ptr, n)`
// ---------------------------------------------------------------------------------------------

pub const StackAlloc = struct {
    buf: [1024]u8 align(16) = undefined,
    used: usize = 0,
    blocks: ?*Block = null,

    const Block = struct { next: ?*Block, bytes: []align(16) u8 };

    pub fn alloc(self: *StackAlloc, comptime T: type, n: i32) Raised!?[*]T {
        if (n < 0) return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        const size = @as(usize, @intCast(n)) * @sizeOf(T);
        const start = std.mem.alignForward(usize, self.used, @max(@alignOf(T), 1));
        if (start + size <= self.buf.len) {
            self.used = start + size;
            const bytes = self.buf[start .. start + size];
            @memset(bytes, 0);
            return @as(?[*]T, @ptrCast(@alignCast(bytes.ptr)));
        }
        const bytes = rt.alloc().alignedAlloc(u8, .@"16", @max(size, 1)) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        @memset(bytes, 0);
        const b = rt.alloc().create(Block) catch {
            rt.alloc().free(bytes);
            return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        };
        b.* = .{ .next = self.blocks, .bytes = bytes };
        self.blocks = b;
        return @as(?[*]T, @ptrCast(@alignCast(bytes.ptr)));
    }

    pub fn deinit(self: *StackAlloc) void {
        var b = self.blocks;
        while (b) |x| {
            b = x.next;
            rt.alloc().free(x.bytes);
            rt.alloc().destroy(x);
        }
        self.blocks = null;
    }
};

/// `Span<T>(ptr, n)` / `ReadOnlySpan<T>(ptr, n)` over a raw nullable pointer
pub fn spanOfPtr(comptime S: type, p: anytype, n: i32) Raised!S {
    if (n < 0) return raise(ArgumentOutOfRangeException, str("Specified argument was out of the range of valid values. (Parameter 'length')"));
    const T = @typeInfo(S).pointer.child;
    const q = if (@typeInfo(@TypeOf(p)) == .optional)
        (p orelse {
            if (n == 0) return rt.spanEmpty(S);
            return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'pointer')"));
        })
    else
        p;
    const items: [*]T = @ptrCast(@alignCast(@constCast(q)));
    return items[0..@intCast(n)];
}

// ---------------------------------------------------------------------------------------------
// NativePtr helpers (nullable `?[*]T` with positive/negative offset support)
// ---------------------------------------------------------------------------------------------

fn PtrElem(comptime P: type) type {
    const inner = if (@typeInfo(P) == .optional) @typeInfo(P).optional.child else P;
    return @typeInfo(inner).pointer.child;
}

pub inline fn ptrAdd(p: anytype, offset: i32) @TypeOf(p) {
    const P = @TypeOf(p);
    const Elem = PtrElem(P);
    const base: usize = if (@typeInfo(P) == .optional) (if (p) |q| @intFromPtr(q) else 0) else @intFromPtr(p);
    const byte_off: isize = @as(isize, offset) *% @as(isize, @intCast(@sizeOf(Elem)));
    const next: usize = base +% @as(usize, @bitCast(byte_off));
    return @ptrFromInt(next);
}

pub inline fn ptrGet(p: anytype, i: i32) PtrElem(@TypeOf(p)) {
    return ptrAdd(p, i).?[0];
}

pub inline fn ptrSet(p: anytype, i: i32, val: PtrElem(@TypeOf(p))) void {
    ptrAdd(p, i).?[0] = val;
}

pub inline fn ptrRead(p: anytype) PtrElem(@TypeOf(p)) {
    return p.?[0];
}

pub inline fn ptrWrite(p: anytype, val: PtrElem(@TypeOf(p))) void {
    p.?[0] = val;
}

pub fn ptrCopy(dst: anytype, src: @TypeOf(dst), count: i32) void {
    if (count <= 0) return;
    const d_addr: usize = if (dst) |q| @intFromPtr(q) else 0;
    const s_addr: usize = if (src) |q| @intFromPtr(q) else 0;
    const n: usize = @intCast(count);
    const d_slice = dst.?[0..n];
    const s_slice = src.?[0..n];
    if (d_addr < s_addr) {
        std.mem.copyForwards(PtrElem(@TypeOf(dst)), d_slice, s_slice);
    } else if (d_addr > s_addr) {
        std.mem.copyBackwards(PtrElem(@TypeOf(dst)), d_slice, s_slice);
    }
}

pub fn ptrCopyBlock(dst: anytype, src: anytype, byte_count: i32) void {
    if (byte_count <= 0) return;
    nativeCopy(@as(?*anyopaque, @ptrCast(@constCast(src))), @as(?*anyopaque, @ptrCast(dst)), @intCast(byte_count));
}

pub fn ptrInitBlock(dst: anytype, value: u8, byte_count: u32) void {
    nativeFill(@as(?*anyopaque, @ptrCast(dst)), byte_count, value);
}

pub fn ptrClear(dst: anytype, count: i32) void {
    if (count <= 0) return;
    const n: usize = @intCast(count);
    @memset(dst.?[0..n], std.mem.zeroes(PtrElem(@TypeOf(dst))));
}

// ---------------------------------------------------------------------------------------------
// Allocator backend for `Marshal.AllocHGlobal` and `NativeMemory`
//
// When linking libc (`builtin.link_libc`), `Alloc`/`Free`/`Realloc`/`AllocHGlobal` delegate
// straight to `std.c` so pointers are interchangeable with C `malloc`/`free`. When libc is not
// linked (e.g., pure Zig unit tests), a 16-byte header holds the allocation length.
// Aligned allocations always store `AlignedHdr` behind the returned aligned pointer so
// `AlignedRealloc`/`AlignedFree` work portably on all platforms (`std.c.aligned_alloc` is not
// exposed consistently across OSes and lacks `realloc`/sized free).
// ---------------------------------------------------------------------------------------------

const NonLibcHdr = extern struct {
    len: usize,
    _pad: usize = 0,
};

const AlignedHdr = extern struct {
    base: [*]u8,
    total_len: usize,
    req_len: usize,
    _pad: usize = 0,
};

fn rawAlloc(byte_count: usize, zeroed: bool) ?[*]u8 {
    const n = @max(byte_count, 1);
    if (comptime builtin.link_libc) {
        const p = if (zeroed) std.c.calloc(1, n) else std.c.malloc(n);
        return @ptrCast(p);
    }
    const total = n + @sizeOf(NonLibcHdr);
    const slice = rt.allocator.alignedAlloc(u8, .@"16", total) catch return null;
    if (zeroed) @memset(slice[@sizeOf(NonLibcHdr)..], 0);
    const hdr: *NonLibcHdr = @ptrCast(slice.ptr);
    hdr.* = .{ .len = total };
    return @ptrCast(slice.ptr + @sizeOf(NonLibcHdr));
}

fn rawFree(ptr: ?*anyopaque) void {
    const p = ptr orelse return;
    if (comptime builtin.link_libc) {
        std.c.free(p);
        return;
    }
    const user: [*]u8 = @ptrCast(p);
    const base: [*]align(16) u8 = @alignCast(user - @sizeOf(NonLibcHdr));
    const hdr: *const NonLibcHdr = @ptrCast(base);
    rt.allocator.free(base[0..hdr.len]);
}

fn rawRealloc(ptr: ?*anyopaque, byte_count: usize) ?[*]u8 {
    if (ptr == null) return rawAlloc(byte_count, false);
    const n = @max(byte_count, 1);
    if (comptime builtin.link_libc) {
        return @ptrCast(std.c.realloc(ptr, n));
    }
    const old_user: [*]u8 = @ptrCast(ptr.?);
    const old_base: [*]align(16) u8 = @alignCast(old_user - @sizeOf(NonLibcHdr));
    const old_hdr: *const NonLibcHdr = @ptrCast(old_base);
    const old_len = old_hdr.len - @sizeOf(NonLibcHdr);
    const new_user = rawAlloc(n, false) orelse return null;
    @memcpy(new_user[0..@min(old_len, n)], old_user[0..@min(old_len, n)]);
    rawFree(ptr);
    return new_user;
}

pub fn nativeAlloc(byte_count: usize) Raised!?*anyopaque {
    return rawAlloc(byte_count, false) orelse raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
}

pub fn nativeAllocElem(elem_count: usize, elem_size: usize) Raised!?*anyopaque {
    const total = std.math.mul(usize, elem_count, elem_size) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
    return nativeAlloc(total);
}

pub fn nativeAllocZeroed(byte_count: usize) Raised!?*anyopaque {
    return rawAlloc(byte_count, true) orelse raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
}

pub fn nativeAllocZeroedElem(elem_count: usize, elem_size: usize) Raised!?*anyopaque {
    const total = std.math.mul(usize, elem_count, elem_size) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
    return nativeAllocZeroed(total);
}

pub fn nativeRealloc(ptr: ?*anyopaque, byte_count: usize) Raised!?*anyopaque {
    return rawRealloc(ptr, byte_count) orelse raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
}

pub fn nativeFree(ptr: ?*anyopaque) void {
    rawFree(ptr);
}

pub fn nativeAlignedAlloc(byte_count: usize, alignment: usize) Raised!?*anyopaque {
    if (alignment == 0 or !std.math.isPowerOfTwo(alignment)) {
        return raise(ArgumentException, str("Alignment must be a power of two."));
    }
    const eff_align = @max(alignment, @alignOf(AlignedHdr));
    const n = @max(byte_count, 1);
    const total = n + eff_align + @sizeOf(AlignedHdr);
    const base = rawAlloc(total, false) orelse return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
    const raw_addr = @intFromPtr(base) + @sizeOf(AlignedHdr);
    const aligned_addr = std.mem.alignForward(usize, raw_addr, eff_align);
    const hdr: *AlignedHdr = @ptrFromInt(aligned_addr - @sizeOf(AlignedHdr));
    hdr.* = .{ .base = base, .total_len = total, .req_len = byte_count };
    return @ptrFromInt(aligned_addr);
}

pub fn nativeAlignedRealloc(ptr: ?*anyopaque, byte_count: usize, alignment: usize) Raised!?*anyopaque {
    if (ptr == null) return nativeAlignedAlloc(byte_count, alignment);
    const old_addr = @intFromPtr(ptr.?);
    const old_hdr: *const AlignedHdr = @ptrFromInt(old_addr - @sizeOf(AlignedHdr));
    const new_ptr = try nativeAlignedAlloc(byte_count, alignment);
    const copy_len = @min(old_hdr.req_len, byte_count);
    if (copy_len > 0) {
        const dst: [*]u8 = @ptrCast(new_ptr.?);
        const src: [*]const u8 = @ptrCast(ptr.?);
        @memcpy(dst[0..copy_len], src[0..copy_len]);
    }
    nativeAlignedFree(ptr);
    return new_ptr;
}

pub fn nativeAlignedFree(ptr: ?*anyopaque) void {
    const p = ptr orelse return;
    const hdr: *const AlignedHdr = @ptrFromInt(@intFromPtr(p) - @sizeOf(AlignedHdr));
    rawFree(hdr.base);
}

pub fn nativeCopy(source: ?*anyopaque, destination: ?*anyopaque, byte_count: usize) void {
    if (byte_count == 0) return;
    const s: [*]const u8 = @ptrCast(source.?);
    const d: [*]u8 = @ptrCast(destination.?);
    const sa = @intFromPtr(s);
    const da = @intFromPtr(d);
    if (da < sa) {
        std.mem.copyForwards(u8, d[0..byte_count], s[0..byte_count]);
    } else if (da > sa) {
        std.mem.copyBackwards(u8, d[0..byte_count], s[0..byte_count]);
    }
}

pub fn nativeFill(ptr: ?*anyopaque, byte_count: usize, value: u8) void {
    if (byte_count == 0) return;
    const d: [*]u8 = @ptrCast(ptr.?);
    @memset(d[0..byte_count], value);
}

pub fn nativeClear(ptr: ?*anyopaque, byte_count: usize) void {
    nativeFill(ptr, byte_count, 0);
}

// ---------------------------------------------------------------------------------------------
// `System.Runtime.InteropServices.Marshal`
// ---------------------------------------------------------------------------------------------

pub fn marshalSizeOf(comptime T: type) i32 {
    if (T == bool) return 4;
    if (comptime isPlainStruct(T)) return @intCast(@sizeOf(CStruct(T)));
    return @intCast(@sizeOf(T));
}

pub fn marshalOffsetOf(comptime T: type, field_name: String) Raised!isize {
    const info = @typeInfo(T);
    if (info != .@"struct") return raise(ArgumentException, str("Type must be a struct."));
    const units = unitsOf(field_name);
    var small: [256]u8 = undefined;
    var heap: ?[]u8 = null;
    defer if (heap) |h| alloc().free(h);
    const need = units.len * 3;
    const buf: []u8 = if (need <= small.len) small[0..need] else blk: {
        heap = alloc().alloc(u8, need) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        break :blk heap.?;
    };
    const n = std.unicode.wtf16LeToWtf8(buf, units);
    const utf8 = buf[0..n];
    const ST = if (comptime isPlainStruct(T)) CStruct(T) else T;
    inline for (@typeInfo(ST).@"struct".field_names) |fname| {
        if (std.mem.eql(u8, fname, utf8)) {
            return @intCast(@offsetOf(ST, fname));
        }
    }
    return raise(ArgumentException, str("Field not found on struct."));
}

pub fn marshalAllocHGlobal(cb: isize) Raised!isize {
    if (cb < 0) return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
    const p = try nativeAlloc(@intCast(cb));
    return @bitCast(@intFromPtr(p.?));
}

pub fn marshalReAllocHGlobal(pv: isize, cb: isize) Raised!isize {
    if (cb < 0) return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
    const old: ?*anyopaque = if (pv == 0) null else @ptrFromInt(@as(usize, @bitCast(pv)));
    const p = try nativeRealloc(old, @intCast(cb));
    return @bitCast(@intFromPtr(p.?));
}

pub fn marshalFreeHGlobal(ptr: isize) void {
    if (ptr == 0) return;
    nativeFree(@ptrFromInt(@as(usize, @bitCast(ptr))));
}

pub fn marshalPtrToStringUTF8(ptr: isize) String {
    if (ptr == 0) return null;
    const p: [*:0]const u8 = @ptrFromInt(@as(usize, @bitCast(ptr)));
    return io.fromUtf8(std.mem.span(p));
}

pub fn marshalPtrToStringUTF8Len(ptr: isize, len: i32) Raised!String {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    if (len < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'byteLen')"));
    const p: [*]const u8 = @ptrFromInt(@as(usize, @bitCast(ptr)));
    return io.fromUtf8(p[0..@intCast(len)]);
}

pub fn marshalPtrToStringUni(ptr: isize) String {
    if (ptr == 0) return null;
    const p: [*:0]const u16 = @ptrFromInt(@as(usize, @bitCast(ptr)));
    return strFrom(std.mem.span(p));
}

pub fn marshalPtrToStringUniLen(ptr: isize, len: i32) Raised!String {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    if (len < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'len')"));
    const p: [*]const u16 = @ptrFromInt(@as(usize, @bitCast(ptr)));
    return strFrom(p[0..@intCast(len)]);
}

pub fn marshalStringToHGlobalUTF8(s: String) Raised!isize {
    if (s == null) return 0;
    const units = unitsOf(s);
    const max_bytes = units.len * 3 + 1;
    const p = try nativeAlloc(max_bytes);
    const buf: [*]u8 = @ptrCast(p.?);
    const n = std.unicode.wtf16LeToWtf8(buf[0..max_bytes], units);
    buf[n] = 0;
    return @bitCast(@intFromPtr(buf));
}

pub fn marshalStringToHGlobalUni(s: String) Raised!isize {
    if (s == null) return 0;
    const units = unitsOf(s);
    const p = try nativeAlloc((units.len + 1) * @sizeOf(u16));
    const buf: [*]u16 = @ptrCast(@alignCast(p.?));
    @memcpy(buf[0..units.len], units);
    buf[units.len] = 0;
    return @bitCast(@intFromPtr(buf));
}

pub fn marshalPtrToStructure(comptime T: type, ptr: isize) Raised!T {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    if (comptime isPlainStruct(T)) {
        const C = CStruct(T);
        const raw: *align(1) const C = @ptrFromInt(@as(usize, @bitCast(ptr)));
        return fromCStruct(T, raw.*);
    }
    const raw: *align(1) const T = @ptrFromInt(@as(usize, @bitCast(ptr)));
    return raw.*;
}

pub fn marshalStructureToPtr(val: anytype, ptr: isize) Raised!void {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    const T = @TypeOf(val);
    if (comptime isPlainStruct(T)) {
        const C = CStruct(T);
        const raw: *align(1) C = @ptrFromInt(@as(usize, @bitCast(ptr)));
        raw.* = toCStruct(C, val);
        return;
    }
    const raw: *align(1) T = @ptrFromInt(@as(usize, @bitCast(ptr)));
    raw.* = val;
}

pub fn marshalCopyToArray(src_ptr: isize, arr: anytype, start_idx: i32, length: i32) Raised!void {
    if (src_ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'source')"));
    if (arrayIsNull(arr)) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'destination')"));
    if (start_idx < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'startIndex')"));
    if (length < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'length')"));
    const start: usize = @intCast(start_idx);
    const len: usize = @intCast(length);
    if (start + len > arr.items.len) return raise(ArgumentException, str("Destination array was not long enough."));
    if (len == 0) return;
    const dst_bytes = std.mem.sliceAsBytes(arr.items[start .. start + len]);
    const src_bytes: [*]const u8 = @ptrFromInt(@as(usize, @bitCast(src_ptr)));
    @memcpy(dst_bytes, src_bytes[0..dst_bytes.len]);
}

pub fn marshalCopyFromArray(arr: anytype, start_idx: i32, dst_ptr: isize, length: i32) Raised!void {
    if (arrayIsNull(arr)) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'source')"));
    if (dst_ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'destination')"));
    if (start_idx < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'startIndex')"));
    if (length < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'length')"));
    const start: usize = @intCast(start_idx);
    const len: usize = @intCast(length);
    if (start + len > arr.items.len) return raise(ArgumentException, str("Source array was not long enough."));
    if (len == 0) return;
    const src_bytes = std.mem.sliceAsBytes(arr.items[start .. start + len]);
    const dst_bytes: [*]u8 = @ptrFromInt(@as(usize, @bitCast(dst_ptr)));
    @memcpy(dst_bytes[0..src_bytes.len], src_bytes);
}

pub fn marshalRead(comptime T: type, ptr: isize, ofs: i32) Raised!T {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    const addr: usize = @as(usize, @bitCast(ptr)) +% @as(usize, @bitCast(@as(isize, ofs)));
    const p: *align(1) const T = @ptrFromInt(addr);
    return p.*;
}

pub fn marshalWrite(comptime T: type, ptr: isize, ofs: i32, val: T) Raised!void {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    const addr: usize = @as(usize, @bitCast(ptr)) +% @as(usize, @bitCast(@as(isize, ofs)));
    const p: *align(1) T = @ptrFromInt(addr);
    p.* = val;
}

pub fn marshalGetFunctionPointerForDelegate(f: anytype) Raised!isize {
    return CallbackPool(@TypeOf(f), 32).allocPtr(f);
}

pub fn marshalGetDelegateForFunctionPointer(comptime F: type, ptr: isize) Raised!F {
    if (ptr == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'ptr')"));
    if (CallbackPool(F, 32).findByPtr(ptr)) |existing| return rt.dup(existing);
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (comptime isRaised(RR)) Unraised(RR) else RR;
    const C = comptime blk: {
        var ps: [P.len]type = undefined;
        for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
        break :blk ps;
    };
    const CR = CArg(R, .plain);
    const CFnType = CFn(&C, CR);
    const Captures = struct { fptr: CFnType };
    const code = switch (P.len) {
        0 => struct {
            fn f(env: ?*rt.Env) RR {
                const cap = rt.captured(Captures, env);
                const r = cap.fptr();
                return fromC(R, .plain, r);
            }
        }.f,
        1 => struct {
            fn f(env: ?*rt.Env, a0: P[0].?) RR {
                return callSlot(Captures, RR, R, P, C, env, .{a0});
            }
        }.f,
        2 => struct {
            fn f(env: ?*rt.Env, a0: P[0].?, a1: P[1].?) RR {
                return callSlot(Captures, RR, R, P, C, env, .{ a0, a1 });
            }
        }.f,
        3 => struct {
            fn f(env: ?*rt.Env, a0: P[0].?, a1: P[1].?, a2: P[2].?) RR {
                return callSlot(Captures, RR, R, P, C, env, .{ a0, a1, a2 });
            }
        }.f,
        4 => struct {
            fn f(env: ?*rt.Env, a0: P[0].?, a1: P[1].?, a2: P[2].?, a3: P[3].?) RR {
                return callSlot(Captures, RR, R, P, C, env, .{ a0, a1, a2, a3 });
            }
        }.f,
        5 => struct {
            fn f(env: ?*rt.Env, a0: P[0].?, a1: P[1].?, a2: P[2].?, a3: P[3].?, a4: P[4].?) RR {
                return callSlot(Captures, RR, R, P, C, env, .{ a0, a1, a2, a3, a4 });
            }
        }.f,
        else => @compileError("fable: GetDelegateForFunctionPointer supports up to 5 parameters"),
    };
    return rt.closure(F, Captures, .{ .fptr = @ptrFromInt(@as(usize, @bitCast(ptr))) }, code);
}

fn callSlot(comptime Captures: type, comptime RR: type, comptime R: type, comptime P: anytype, comptime C: anytype, env: ?*rt.Env, args: anytype) RR {
    _ = P;
    const cap = rt.captured(Captures, env);
    var c_args: @Tuple(&C) = undefined;
    var strings: [C.len]CString = undefined;
    inline for (0..C.len) |i| {
        const A = @TypeOf(args[i]);
        if (A == String) {
            strings[i] = .{};
            c_args[i] = if (args[i] == null) null else strings[i].init(args[i]);
        } else if (A == bool) {
            c_args[i] = @intFromBool(args[i]);
        } else if (comptime isPlainStruct(A)) {
            c_args[i] = toCStruct(CStruct(A), args[i]);
        } else {
            c_args[i] = args[i];
        }
    }
    defer inline for (0..C.len) |i| {
        if (@TypeOf(args[i]) == String) strings[i].deinit();
    };
    const r = @call(.auto, cap.fptr, c_args);
    return fromC(R, .plain, r);
}

// ---------------------------------------------------------------------------------------------
// `MemoryMarshal` and `Unsafe`
// ---------------------------------------------------------------------------------------------

pub fn spanCast(comptime ToSlice: type, span: anytype) ToSlice {
    const To = @typeInfo(ToSlice).pointer.child;
    const FromSlice = @TypeOf(span);
    const From = @typeInfo(FromSlice).pointer.child;
    const is_const = @typeInfo(ToSlice).pointer.attrs.@"const";
    if (span.len == 0) return rt.spanEmpty(ToSlice);
    const byte_len = span.len * @sizeOf(From);
    const out_len = byte_len / @sizeOf(To);
    if (out_len == 0) return rt.spanEmpty(ToSlice);
    const ptr: if (is_const) [*]const To else [*]To = @ptrCast(@alignCast(span.ptr));
    return ptr[0..out_len];
}

pub fn spanAsBytes(comptime BytesSlice: type, span: anytype) BytesSlice {
    if (span.len == 0) return rt.spanEmpty(BytesSlice);
    return std.mem.sliceAsBytes(span);
}

pub inline fn spanGetRef(span: anytype) if (@typeInfo(@TypeOf(span)).pointer.attrs.@"const") *const @typeInfo(@TypeOf(span)).pointer.child else *@typeInfo(@TypeOf(span)).pointer.child {
    return &span.ptr[0];
}

pub inline fn arrayGetDataRef(arr: anytype) *@typeInfo(@FieldType(@TypeOf(arr.*), "items")).pointer.child {
    return &arr.items.ptr[0];
}

pub inline fn spanCreateFromRef(comptime S: type, ref: anytype, length: i32) S {
    const T = @typeInfo(S).pointer.child;
    const is_const = @typeInfo(S).pointer.attrs.@"const";
    if (length <= 0) return rt.spanEmpty(S);
    const p: if (is_const) [*]const T else [*]T = @ptrCast(ref);
    return p[0..@intCast(length)];
}

pub inline fn unsafeReadUnaligned(comptime T: type, ptr: ?*anyopaque) T {
    const p: *align(1) const T = @ptrCast(ptr.?);
    return p.*;
}

pub inline fn unsafeWriteUnaligned(comptime T: type, ptr: ?*anyopaque, val: T) void {
    const p: *align(1) T = @ptrCast(ptr.?);
    p.* = val;
}

pub inline fn unsafeAdd(ref: anytype, ofs: anytype) @TypeOf(ref) {
    const Elem = @typeInfo(@TypeOf(ref)).pointer.child;
    const base = @intFromPtr(ref);
    const byte_off: isize = @as(isize, @intCast(ofs)) *% @as(isize, @intCast(@sizeOf(Elem)));
    return @ptrFromInt(base +% @as(usize, @bitCast(byte_off)));
}

pub inline fn unsafeAs(comptime To: type, from: anytype) To {
    const F = @TypeOf(from);
    if (@typeInfo(F) == .pointer and @typeInfo(To) == .pointer) {
        return @ptrCast(@alignCast(@constCast(from)));
    }
    return @bitCast(from);
}

// ---------------------------------------------------------------------------------------------
// `System.Runtime.InteropServices.NativeLibrary`
// ---------------------------------------------------------------------------------------------

fn dynLibFromHandle(handle: isize) Raised!std.DynLib {
    if (handle == 0) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'handle')"));
    const Inner = @FieldType(std.DynLib, "inner");
    if (comptime @hasField(Inner, "handle")) {
        return .{ .inner = .{ .handle = @ptrFromInt(@as(usize, @bitCast(handle))) } };
    } else if (comptime @hasField(Inner, "dll")) {
        return .{ .inner = .{ .dll = @ptrFromInt(@as(usize, @bitCast(handle))) } };
    }
    return raise(NotSupportedException, str("NativeLibrary handle conversion is not supported on this platform."));
}

fn dynLibHandle(lib: std.DynLib) isize {
    const Inner = @FieldType(std.DynLib, "inner");
    if (comptime @hasField(Inner, "handle")) {
        return @bitCast(@intFromPtr(lib.inner.handle));
    } else if (comptime @hasField(Inner, "dll")) {
        return @bitCast(@intFromPtr(lib.inner.dll));
    }
    return 0;
}

pub fn nativeLibLoad(path: String) Raised!isize {
    if (path == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'libraryPath')"));
    var c_path: CString = .{};
    defer c_path.deinit();
    const z = c_path.init(path);
    const lib = std.DynLib.open(std.mem.span(z)) catch return raise(FileNotFoundException, str("Unable to load shared library."));
    return dynLibHandle(lib);
}

pub fn nativeLibTryLoad(path: String, handle_out: *isize) bool {
    if (path == null) {
        handle_out.* = 0;
        return false;
    }
    var c_path: CString = .{};
    defer c_path.deinit();
    const z = c_path.init(path);
    const lib = std.DynLib.open(std.mem.span(z)) catch {
        handle_out.* = 0;
        return false;
    };
    handle_out.* = dynLibHandle(lib);
    return true;
}

pub fn nativeLibFree(handle: isize) void {
    if (handle == 0) return;
    var lib = dynLibFromHandle(handle) catch return;
    lib.close();
}

pub fn nativeLibGetExport(handle: isize, name: String) Raised!isize {
    var lib = try dynLibFromHandle(handle);
    if (name == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'name')"));
    var c_name: CString = .{};
    defer c_name.deinit();
    const z = c_name.init(name);
    const sym = lib.lookup(*anyopaque, std.mem.span(z)) orelse return raise(ArgumentException, str("Unable to find an entry point in the shared library."));
    return @bitCast(@intFromPtr(sym));
}

pub fn nativeLibTryGetExport(handle: isize, name: String, addr_out: *isize) bool {
    addr_out.* = 0;
    if (handle == 0 or name == null) return false;
    var lib = dynLibFromHandle(handle) catch return false;
    var c_name: CString = .{};
    defer c_name.deinit();
    const z = c_name.init(name);
    const sym = lib.lookup(*anyopaque, std.mem.span(z)) orelse return false;
    addr_out.* = @bitCast(@intFromPtr(sym));
    return true;
}

// ---------------------------------------------------------------------------------------------
// Array element & string pinning helpers (`fixed`, `&arr.[i]`)
// ---------------------------------------------------------------------------------------------

pub fn arrayElemPtr(arr: anytype, idx: i32) Raised!*@typeInfo(@FieldType(@TypeOf(arr.*), "items")).pointer.child {
    if (arrayIsNull(arr)) return rt.nullRef();
    if (idx < 0 or @as(usize, @intCast(idx)) >= arr.items.len) {
        return raise(rt.IndexOutOfRangeException, str("Index was outside the bounds of the array."));
    }
    return &arr.items[@intCast(idx)];
}

const empty_utf16_nul: [1]u16 = .{0};

pub fn stringPinnableRef(s: String) *const u16 {
    const units = unitsOf(s);
    if (units.len == 0) return &empty_utf16_nul[0];
    return &units[0];
}

pub inline fn keepAlive(_: anytype) void {}
