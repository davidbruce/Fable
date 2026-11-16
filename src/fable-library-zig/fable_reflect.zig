//! .NET's `System.Type` and F#'s reflection (`FSharpType`, `FSharpValue`), made at comptime
//! from the Zig types: a type's information exists only if the program asks for it. The
//! program's records and unions say who they are in .NET (`pub const fable_type = .{ ... }`,
//! written by the compiler); the runtime's own types (lists, options, Result, Choice, tuples,
//! arrays, functions, primitives) are known here. Values cross as boxed objects, as in .NET.
const std = @import("std");
const rt = @import("fable_rt.zig");

const Any = rt.Any;
const Raised = rt.Raised;
const String = rt.String;

pub const Kind = enum { other, primitive, object, array, record, anon_record, @"union", tuple, function, class, @"enum", interface };

/// A record's field, a union case's field or a tuple's element: its name, its type, and what
/// it is in a boxed value of the type (boxed)
pub const Field = struct {
    name: []const u8,
    ty: Type,
    get: ?*const fn (Any) Raised!Any = null,
};

pub const Case = struct {
    name: []const u8,
    tag: i32,
    fields: []const Field,
    /// the boxed value of this case made of the boxed fields
    make: ?*const fn ([]const Any) Raised!Any = null,
};

pub const TypeInfo = struct {
    /// .NET's `FullName` (of a generic type: with its arguments, `G`1[System.Int32]`)
    full_name: []const u8,
    name: []const u8,
    namespace: []const u8,
    kind: Kind,
    /// a generic type's arguments (none for its definition)
    args: []const Type = &.{},
    /// a generic type's definition (itself for a definition)
    definition: ?Type = null,
    is_definition: bool = false,
    /// an array's element
    element: ?Type = null,
    /// a record's fields, a tuple's elements
    fields: []const Field = &.{},
    cases: []const Case = &.{},
    /// a record or a tuple made of its boxed fields
    make: ?*const fn ([]const Any) Raised!Any = null,
    /// the case of a boxed value of a union
    tag_of: ?*const fn (Any) Raised!i32 = null,
    /// a class's base class (none for Object) and the interfaces it implements
    parent: ?Type = null,
    interfaces: []const Type = &.{},
    /// an enum's underlying number type, and its cases (names and values)
    underlying: ?Type = null,
    enum_names: []const []const u8 = &.{},
    enum_values: []const i64 = &.{},
};

pub const Type = *const TypeInfo;

var reflect_lock: u32 = 0;
var class_types: std.AutoHashMapUnmanaged(*const rt.ObjType, Type) = .empty;
var exn_types: std.AutoHashMapUnmanaged(*const rt.ExnType, Type) = .empty;
var named_types: std.StringHashMapUnmanaged(Type) = .empty;
var tuple_types: std.StringHashMapUnmanaged(Type) = .empty;

/// `UnionCaseInfo`: the union and the case
pub const UnionCase = struct {
    union_type: Type,
    index: usize,
};

/// `PropertyInfo`: the type and its field (of a record, or of a union case)
pub const Property = struct {
    owner: Type,
    case: i32 = -1,
    index: usize,
};

// ---- names ----

fn join(comptime parts: []const []const u8, comptime sep: []const u8) []const u8 {
    comptime var s: []const u8 = "";
    inline for (parts, 0..) |p, i| {
        s = s ++ (if (i == 0) "" else sep) ++ p;
    }
    return s;
}

/// `G`1[System.Int32,System.String]`
fn withArgs(comptime base: []const u8, comptime args: []const Type) []const u8 {
    if (args.len == 0) return base;
    comptime var names: []const []const u8 = &.{};
    inline for (args) |a| names = names ++ .{a.full_name};
    return base ++ "[" ++ join(names, ",") ++ "]";
}

// (plain loops: these run at comptime)
fn lastOf(comptime s: []const u8, comptime c: u8) ?usize {
    comptime var i = s.len;
    inline while (i > 0) {
        i -= 1;
        if (s[i] == c) return i;
    }
    return null;
}

fn firstOf(comptime s: []const u8, comptime c: u8) ?usize {
    inline for (s, 0..) |x, i| {
        if (x == c) return i;
    }
    return null;
}

fn nameOfFull(comptime full: []const u8) []const u8 {
    @setEvalBranchQuota(100_000);
    // (a generic type's name ends before its arguments)
    const base = if (firstOf(full, '[')) |b| full[0..b] else full;
    const plus = lastOf(base, '+');
    const dot = lastOf(base, '.');
    const at: usize = if (plus) |p| (if (dot) |d| @max(p, d) else p) else (dot orelse return base);
    return base[at + 1 ..];
}

fn namespaceOfFull(comptime full: []const u8) []const u8 {
    @setEvalBranchQuota(100_000);
    // (before the outermost type: what is before the first '+', up to its last '.')
    const outer = if (firstOf(full, '+')) |p| full[0..p] else full;
    const dot = lastOf(outer, '.') orelse return "";
    return outer[0..dot];
}

// ---- the information of a type ----

pub fn typeOf(comptime T: type) Type {
    return &Info(T).info;
}

fn Info(comptime T: type) type {
    return struct {
        pub const info: TypeInfo = build(T);
    };
}

fn prim(comptime full: []const u8) TypeInfo {
    return .{ .full_name = full, .name = nameOfFull(full), .namespace = namespaceOfFull(full), .kind = .primitive };
}

fn typesOf(comptime Ts: []const type) []const Type {
    comptime var out: []const Type = &.{};
    inline for (Ts) |X| out = out ++ .{typeOf(X)};
    return out;
}

fn interfaceInfo(comptime T: type) TypeInfo {
    const tname = @typeName(T);
    return .{ .full_name = tname, .name = tname, .namespace = "", .kind = .interface };
}

fn build(comptime T: type) TypeInfo {
    @setEvalBranchQuota(100_000);
    if (T == String) return prim("System.String");
    if (T == Any or T == rt.Obj) return .{ .full_name = "System.Object", .name = "Object", .namespace = "System", .kind = .object };
    if (T == void) return prim("Microsoft.FSharp.Core.Unit");
    if (T == rt.BigInt) return prim("System.Numerics.BigInteger");
    if (T == rt.NetDecimal) return prim("System.Decimal");
    if (T == Type) return .{ .full_name = "System.Type", .name = "Type", .namespace = "System", .kind = .class };
    switch (T) {
        i8 => return prim("System.SByte"),
        u8 => return prim("System.Byte"),
        i16 => return prim("System.Int16"),
        c_ushort => return prim("System.UInt16"),
        u16 => return prim("System.Char"),
        i32 => return prim("System.Int32"),
        u32 => return prim("System.UInt32"),
        i64 => return prim("System.Int64"),
        u64 => return prim("System.UInt64"),
        i128 => return prim("System.Int128"),
        u128 => return prim("System.UInt128"),
        isize => return prim("System.IntPtr"),
        usize => return prim("System.UIntPtr"),
        f16 => return prim("System.Half"),
        f32 => return prim("System.Single"),
        f64 => return prim("System.Double"),
        bool => return prim("System.Boolean"),
        else => {},
    }
    const info = @typeInfo(T);
    // an array
    if (info == .pointer and info.pointer.size == .one and @hasDecl(info.pointer.child, "fable_array")) {
        const E = info.pointer.child.fable_array;
        const e = typeOf(E);
        return .{ .full_name = e.full_name ++ "[]", .name = e.name ++ "[]", .namespace = e.namespace, .kind = .array, .element = e };
    }
    // a function value: F#'s curried `FSharpFunc<A, B>`
    if (comptime rt.isFunc(T)) {
        const F = @typeInfo(@typeInfo(@FieldType(T, "code")).pointer.child).@"fn";
        comptime var params: []const type = &.{};
        inline for (F.param_types[1..]) |P| params = params ++ .{P.?};
        const R = rt.Unraised(F.return_type.?);
        return funcInfo(params, R);
    }
    if (comptime rt.isIface(T)) return interfaceInfo(T);
    if (info == .optional and comptime rt.isIface(info.optional.child)) return interfaceInfo(info.optional.child);
    // an option (a string and an object are not: their null is their own)
    if (info == .optional) return optionInfo(info.optional.child);
    // a tuple
    if (info == .@"struct" and info.@"struct".is_tuple) return tupleInfo(T);
    // a type that says what it is (the program's records and unions, Result, Choice, list)
    const C = if (info == .pointer and info.pointer.size == .one) info.pointer.child else T;
    if ((@typeInfo(C) == .@"struct" or @typeInfo(C) == .@"union") and @hasDecl(C, "fable_type")) return declared(T, C, C.fable_type);
    // an anonymous record: a struct of fields and nothing else (one type per shape)
    if (info == .@"struct" and info.@"struct".decl_names.len == 0) return anonInfo(T);
    return .{ .full_name = @typeName(T), .name = @typeName(T), .namespace = "", .kind = .other };
}

fn anonInfo(comptime T: type) TypeInfo {
    const st = @typeInfo(T).@"struct";
    const args = typesOf(st.field_types);
    const full = std.fmt.comptimePrint("<>f__AnonymousType{s}`{d}", .{ join(st.field_names, "_"), st.field_names.len });
    return .{
        .full_name = withArgs(full, args),
        .name = full,
        .namespace = "",
        .kind = .anon_record,
        .args = args,
        .fields = fieldsOf(T, T, null),
        .make = &struct {
            fn f(vals: []const Any) Raised!Any {
                const v = try fill(T, vals);
                defer rt.drop(v);
                return rt.box(v);
            }
        }.f,
    };
}

fn funcInfo(comptime params: []const type, comptime R: type) TypeInfo {
    const domain = typeOf(params[0]);
    const range = if (params.len == 1) typeOf(R) else &FuncRest(params[1..], R).info;
    const def: Type = &FuncDef.info;
    return .{
        .full_name = withArgs("Microsoft.FSharp.Core.FSharpFunc`2", &.{ domain, range }),
        .name = "FSharpFunc`2",
        .namespace = "Microsoft.FSharp.Core",
        .kind = .function,
        .args = &.{ domain, range },
        .definition = def,
    };
}

fn FuncRest(comptime params: []const type, comptime R: type) type {
    return struct {
        pub const info: TypeInfo = funcInfo(params, R);
    };
}

const FuncDef = struct {
    pub const info: TypeInfo = .{ .full_name = "Microsoft.FSharp.Core.FSharpFunc`2", .name = "FSharpFunc`2", .namespace = "Microsoft.FSharp.Core", .kind = .function, .is_definition = true };
};

fn Def(comptime full: []const u8, comptime kind: Kind) type {
    return struct {
        pub const info: TypeInfo = .{ .full_name = full, .name = nameOfFull(full), .namespace = namespaceOfFull(full), .kind = kind, .is_definition = true };
    };
}

fn optionInfo(comptime X: type) TypeInfo {
    const O = ?X;
    const full = "Microsoft.FSharp.Core.FSharpOption`1";
    const x = typeOf(X);
    return .{
        .full_name = withArgs(full, &.{x}),
        .name = "FSharpOption`1",
        .namespace = "Microsoft.FSharp.Core",
        .kind = .@"union",
        .args = &.{x},
        .definition = &Def(full, .@"union").info,
        .cases = &.{
            .{ .name = "None", .tag = 0, .fields = &.{}, .make = &struct {
                fn f(_: []const Any) Raised!Any {
                    const v: O = null;
                    return rt.box(v);
                }
            }.f },
            .{ .name = "Some", .tag = 1, .fields = &.{.{ .name = "Value", .ty = x, .get = &struct {
                fn f(o: Any) Raised!Any {
                    const v = try rt.unbox(O, o);
                    defer rt.drop(v);
                    return rt.box(v.?);
                }
            }.f }}, .make = &struct {
                fn f(vals: []const Any) Raised!Any {
                    try count(vals, 1);
                    const v: O = try rt.unbox(X, vals[0]);
                    defer rt.drop(v);
                    return rt.box(v);
                }
            }.f },
        },
        .tag_of = &struct {
            fn f(o: Any) Raised!i32 {
                const v = try rt.unbox(O, o);
                defer rt.drop(v);
                return if (v == null) 0 else 1;
            }
        }.f,
    };
}

fn count(vals: []const Any, n: usize) Raised!void {
    if (vals.len != n) return rt.raise(rt.ArgumentException, rt.str("The number of values given does not match the number of fields."));
}

/// The fields of a struct (`T` itself, or what `T` points to) as reflection fields
fn fieldsOf(comptime T: type, comptime S: type, comptime names: ?[]const []const u8) []const Field {
    const s = @typeInfo(S).@"struct";
    comptime var out: []const Field = &.{};
    comptime var i = 0;
    inline for (s.field_names, s.field_types) |fname, F| {
        if (fname[0] == '$') continue;
        const shown = if (names) |n| n[i] else fname;
        out = out ++ .{Field{ .name = shown, .ty = typeOf(F), .get = &FieldGet(T, fname).get }};
        i += 1;
    }
    return out;
}

fn FieldGet(comptime T: type, comptime fname: []const u8) type {
    return struct {
        fn get(o: Any) Raised!Any {
            const v = try rt.unbox(T, o);
            defer rt.drop(v);
            return rt.box(@field(v, fname));
        }
    };
}

/// A value of the struct `S` made of boxed fields (the `$` fields keep their defaults)
fn fill(comptime S: type, vals: []const Any) Raised!S {
    const s = @typeInfo(S).@"struct";
    var r: S = undefined;
    comptime var n = 0;
    inline for (s.field_names) |fname| {
        if (fname[0] != '$') n += 1;
    }
    try count(vals, n);
    comptime var i = 0;
    inline for (s.field_names, s.field_types, s.field_attrs) |fname, F, attrs| {
        if (fname[0] == '$') {
            if (attrs.default_value_ptr) |p| @field(r, fname) = @as(*const F, @ptrCast(@alignCast(p))).* else @field(r, fname) = undefined;
        } else {
            @field(r, fname) = try rt.unbox(F, vals[i]);
            i += 1;
        }
    }
    return r;
}

fn tupleInfo(comptime T: type) TypeInfo {
    const s = @typeInfo(T).@"struct";
    const elems = typesOf(s.field_types);
    comptime var names: []const []const u8 = &.{};
    inline for (0..s.field_types.len) |i| names = names ++ .{std.fmt.comptimePrint("Item{d}", .{i + 1})};
    const full = std.fmt.comptimePrint("System.Tuple`{d}", .{s.field_types.len});
    return .{
        .full_name = withArgs(full, elems),
        .name = nameOfFull(full),
        .namespace = "System",
        .kind = .tuple,
        .args = elems,
        .definition = &Def(full, .tuple).info,
        .fields = fieldsOf(T, T, names),
        .make = &struct {
            fn f(vals: []const Any) Raised!Any {
                const v = try fill(T, vals);
                defer rt.drop(v);
                return rt.box(v);
            }
        }.f,
    };
}

/// A record or a union of the program (or of the runtime): `d` is its `fable_type`
fn declared(comptime T: type, comptime C: type, comptime d: anytype) TypeInfo {
    const args: []const Type = if (@hasField(@TypeOf(d), "args")) typesOf(&d.args) else &.{};
    const kind: Kind = d.kind;
    var info: TypeInfo = .{
        .full_name = withArgs(d.full_name, args),
        .name = nameOfFull(d.full_name),
        .namespace = if (@hasField(@TypeOf(d), "namespace")) d.namespace else namespaceOfFull(d.full_name),
        .kind = kind,
        .args = args,
        .definition = if (args.len > 0) &Def(d.full_name, kind).info else null,
    };
    switch (kind) {
        .record, .anon_record => {
            info.fields = fieldsOf(T, C, null);
            info.make = &struct {
                fn f(vals: []const Any) Raised!Any {
                    const v: T = if (C == T) try fill(T, vals) else blk: {
                        const cell = rt.allocator.create(C) catch rt.oom();
                        cell.* = try fill(C, vals);
                        break :blk cell;
                    };
                    defer rt.drop(v);
                    return rt.box(v);
                }
            }.f;
        },
        .@"union" => {
            info.cases = casesOf(T);
            info.tag_of = &struct {
                fn f(o: Any) Raised!i32 {
                    const v = try rt.unbox(T, o);
                    defer rt.drop(v);
                    return @backingInt(std.meta.activeTag(v));
                }
            }.f;
        },
        else => {},
    }
    return info;
}

fn casesOf(comptime T: type) []const Case {
    const u = @typeInfo(T).@"union";
    comptime var out: []const Case = &.{};
    inline for (u.field_names, u.field_types, 0..) |cname, P, i| {
        const fields: []const Field = if (P == void) &.{} else caseFields(T, cname, P);
        out = out ++ .{Case{ .name = cname, .tag = i, .fields = fields, .make = &CaseMake(T, cname, P).make }};
    }
    return out;
}

/// The fields of a case: its payload struct (or the cell it points to)
fn caseFields(comptime T: type, comptime cname: []const u8, comptime P: type) []const Field {
    const S = if (@typeInfo(P) == .pointer) @typeInfo(P).pointer.child else P;
    const s = @typeInfo(S).@"struct";
    comptime var out: []const Field = &.{};
    inline for (s.field_names, s.field_types) |fname, F| {
        if (fname[0] == '$') continue;
        out = out ++ .{Field{ .name = fname, .ty = typeOf(F), .get = &CaseGet(T, cname, fname).get }};
    }
    return out;
}

fn CaseGet(comptime T: type, comptime cname: []const u8, comptime fname: []const u8) type {
    return struct {
        fn get(o: Any) Raised!Any {
            const v = try rt.unbox(T, o);
            defer rt.drop(v);
            const p = @field(v, cname);
            return rt.box(@field(p, fname));
        }
    };
}

fn CaseMake(comptime T: type, comptime cname: []const u8, comptime P: type) type {
    return struct {
        fn make(vals: []const Any) Raised!Any {
            const v: T = if (P == void) blk: {
                try count(vals, 0);
                break :blk @unionInit(T, cname, {});
            } else if (@typeInfo(P) == .pointer) blk: {
                const S = @typeInfo(P).pointer.child;
                const cell = rt.allocator.create(S) catch rt.oom();
                cell.* = try fill(S, vals);
                break :blk @unionInit(T, cname, cell);
            } else @unionInit(T, cname, try fill(P, vals));
            defer rt.drop(v);
            return rt.box(v);
        }
    };
}

// ---- types the compiler names (classes, interfaces, enums) ----

/// The type the compiler describes: `.{ .full_name, .kind, .args = .{...} }`
pub fn named(comptime d: anytype) Type {
    return &struct {
        // (the enum's cases, as constants of their own: the info points at them)
        const enum_names_c: [enumCount(d)][]const u8 = if (@hasField(@TypeOf(d), "enum_names")) d.enum_names else .{};
        const enum_values_c: [enumCount(d)]i64 = if (@hasField(@TypeOf(d), "enum_values")) d.enum_values else .{};
        pub const info: TypeInfo = blk: {
            const args: []const Type = if (@hasField(@TypeOf(d), "args")) typesOf(&d.args) else &.{};
            const interfaces: []const Type = if (@hasField(@TypeOf(d), "interfaces")) &d.interfaces else &.{};
            break :blk .{
                .full_name = withArgs(d.full_name, args),
                .name = nameOfFull(d.full_name),
                .namespace = namespaceOfFull(d.full_name),
                .kind = d.kind,
                .args = args,
                .definition = if (args.len > 0) &Def(d.full_name, d.kind).info else null,
                .parent = if (@hasField(@TypeOf(d), "parent")) d.parent else null,
                .interfaces = interfaces,
                .underlying = if (@hasField(@TypeOf(d), "underlying")) typeOf(d.underlying) else null,
                .enum_names = &enum_names_c,
                .enum_values = &enum_values_c,
            };
        };
    }.info;
}

fn enumCount(comptime d: anytype) usize {
    return if (@hasField(@TypeOf(d), "enum_names")) d.enum_names.len else 0;
}

/// `typedefof<G<_>>`: the definition of a generic type
pub fn definitionOf(t: Type) Type {
    return t.definition orelse t;
}

/// `null` of `System.Type` (what `GetElementType()` of a type that is no array gives)
pub const null_info: TypeInfo = .{ .full_name = "", .name = "", .namespace = "", .kind = .other };

pub fn nullType() Type {
    return &null_info;
}

pub fn elementOrNull(t: Type) Type {
    return t.element orelse &null_info;
}

// ---- System.Type ----

pub fn equals(a: Type, b: Type) bool {
    if (a == b) return true;
    if (a.is_definition != b.is_definition) return false;
    if (!std.mem.eql(u8, a.full_name, b.full_name)) return false;
    if (a.args.len != b.args.len) return false;
    for (a.args, b.args) |x, y| {
        if (!equals(x, y)) return false;
    }
    return true;
}

fn text(s: []const u8) String {
    return rt.io.fromUtf8(s);
}

pub fn fullName(t: Type) String {
    return text(t.full_name);
}

pub fn name(t: Type) String {
    return text(t.name);
}

pub fn namespace(t: Type) String {
    return text(t.namespace);
}

pub fn toString(t: Type) String {
    return text(t.full_name);
}

pub fn isGenericType(t: Type) bool {
    return t.args.len > 0 or t.is_definition;
}

pub fn isGenericTypeDefinition(t: Type) bool {
    return t.is_definition;
}

pub fn isArray(t: Type) bool {
    return t.kind == .array;
}

pub fn isEnum(t: Type) bool {
    return t.kind == .@"enum";
}

pub fn isClass(t: Type) bool {
    return t.kind == .class or t.kind == .record or t.kind == .anon_record or t.kind == .@"union" or t.kind == .tuple or t.kind == .array or t.kind == .function or t.kind == .object or t == typeOf(String);
}

pub fn isInterface(t: Type) bool {
    return t.kind == .interface;
}

pub fn elementType(t: Type) ?Type {
    return t.element;
}

pub fn genericDefinition(t: Type) Raised!Type {
    if (t.is_definition) return t;
    return t.definition orelse rt.raise(rt.InvalidOperationException, rt.str("This operation is only valid on generic types."));
}

pub fn genericArguments(t: Type) rt.Array(Type) {
    const items = rt.arrays.arrayItems(rt.Array(Type), t.args.len);
    @memcpy(items, t.args);
    return rt.arrays.arrayFrom(rt.Array(Type), items);
}

/// A Type known only by its name (a quotation's types)
pub fn typeNamed(name_: String) Type {
    var buf: std.ArrayList(u8) = .empty;
    defer buf.deinit(rt.allocator);
    var tmp: [4]u8 = undefined;
    for (rt.unitsOf(name_)) |u| {
        const n = std.unicode.utf8Encode(u, &tmp) catch 1;
        buf.appendSlice(rt.allocator, tmp[0..n]) catch rt.oom();
    }
    rt.lockField(&reflect_lock);
    defer rt.unlockField(&reflect_lock);
    if (named_types.get(buf.items)) |existing| return existing;
    const bk = rt.bookkeeping();
    const full = bk.dupe(u8, buf.items) catch rt.oom();
    const info = bk.create(TypeInfo) catch rt.oom();
    const at = if (std.mem.lastIndexOfAny(u8, full, ".+")) |i| i + 1 else 0;
    info.* = .{ .full_name = full, .name = full[at..], .namespace = if (at > 0) full[0 .. at - 1] else "", .kind = .other };
    named_types.put(bk, full, info) catch rt.oom();
    return info;
}

/// `def.MakeGenericType(args)` of types known only when the program runs: the constructed type
/// (interned by its full name, which `equals` compares as it does a type made by `typeof`)
pub fn makeGenericType(def: Type, args: rt.Array(Type)) Raised!Type {
    const d = def.definition orelse def;
    const items = args.items;
    const arity: usize = blk: {
        const tick = std.mem.lastIndexOfScalar(u8, d.full_name, '`') orelse break :blk 0;
        const end = std.mem.indexOfScalarPos(u8, d.full_name, tick, '[') orelse d.full_name.len;
        break :blk std.fmt.parseInt(usize, d.full_name[tick + 1 .. end], 10) catch 0;
    };
    if (!(def.is_definition or def.args.len > 0) or arity == 0)
        return rt.raise(rt.InvalidOperationException, rt.str("Method may only be called on a Type for which Type.IsGenericParameter is true."));
    if (items.len != arity)
        return rt.raise(rt.ArgumentException, rt.str("The number of generic arguments provided doesn't equal the arity of the generic type definition. (Parameter 'instantiation')"));
    const base = if (std.mem.indexOfScalar(u8, d.full_name, '[')) |i| d.full_name[0..i] else d.full_name;
    var buf: std.ArrayList(u8) = .empty;
    defer buf.deinit(rt.allocator);
    buf.appendSlice(rt.allocator, base) catch rt.oom();
    buf.append(rt.allocator, '[') catch rt.oom();
    for (items, 0..) |a, i| {
        if (i > 0) buf.append(rt.allocator, ',') catch rt.oom();
        buf.appendSlice(rt.allocator, a.full_name) catch rt.oom();
    }
    buf.append(rt.allocator, ']') catch rt.oom();
    rt.lockField(&reflect_lock);
    defer rt.unlockField(&reflect_lock);
    if (named_types.get(buf.items)) |existing| return existing;
    const bk = rt.bookkeeping();
    const full = bk.dupe(u8, buf.items) catch rt.oom();
    const own_args = bk.dupe(Type, items) catch rt.oom();
    const info = bk.create(TypeInfo) catch rt.oom();
    info.* = .{
        .full_name = full,
        .name = d.name,
        .namespace = d.namespace,
        .kind = d.kind,
        .args = own_args,
        .definition = d,
        .parent = d.parent,
        .interfaces = d.interfaces,
    };
    named_types.put(bk, full, info) catch rt.oom();
    return info;
}

/// A PropertyInfo of nothing (a quotation keeps a property's name only)
pub fn nullProperty() Property {
    return .{ .owner = &null_info, .index = 0 };
}

/// A tuple of boxed items (a quotation's evaluation): `unbox` to a tuple type makes it
pub fn looseTuple(items: rt.Array(Any)) Raised!Any {
    const loose: LooseTuple = .{ .items = rt.dup(items) };
    defer rt.drop(loose);
    return rt.box(loose);
}

pub fn isNullType(t: Type) bool {
    return t == &null_info or t.full_name.len == 0;
}

/// `t.IsSubclassOf(c)`: `c` is one of the classes above `t`
pub fn isSubclassOf(t: Type, c: Type) bool {
    // (every type but `obj` itself and the interfaces derives from `obj`)
    if (std.mem.eql(u8, c.full_name, "System.Object")) return t.kind != .interface and !std.mem.eql(u8, t.full_name, "System.Object");
    var p = t.parent;
    while (p) |x| : (p = x.parent) {
        if (equals(x, c)) return true;
    }
    return false;
}

/// `t.GetInterface(name[, ignoreCase])`: the interface of that name it implements, or null
pub fn getInterface(t: Type, name_: String, ignore_case: bool) Type {
    const wanted = rt.unitsOf(name_);
    var c: ?Type = t;
    while (c) |x| : (c = x.parent) {
        for (x.interfaces) |i| {
            if (i.name.len != wanted.len) continue;
            var same = true;
            for (i.name, wanted) |a, b| {
                const ua: u16 = a;
                if (ua != b and !(ignore_case and std.ascii.toLower(a) == std.ascii.toLower(@truncate(b)) and b < 128)) {
                    same = false;
                    break;
                }
            }
            if (same) return i;
        }
    }
    return &null_info;
}

fn notEnum() Raised {
    return rt.raise(rt.ArgumentException, rt.str("Type provided must be an Enum. (Parameter 'enumType')"));
}

/// `Enum.GetNames(t)` and `t.GetEnumNames()`
pub fn enumNames(t: Type) Raised!rt.Array(String) {
    if (t.kind != .@"enum") return notEnum();
    const items = rt.arrays.arrayItems(rt.Array(String), t.enum_names.len);
    for (t.enum_names, 0..) |n, i| items[i] = text(n);
    return rt.arrays.arrayFrom(rt.Array(String), items);
}

/// `Enum.GetValues(t)`: the values, each boxed as the enum's underlying integer (as an enum's
/// value is boxed here)
pub fn enumValues(t: Type) Raised!rt.Array(Any) {
    if (t.kind != .@"enum") return notEnum();
    const under: []const u8 = if (t.underlying) |u| u.full_name else "System.Int32";
    const items = rt.arrays.arrayItems(rt.Array(Any), t.enum_values.len);
    for (t.enum_values, 0..) |v, i| items[i] = boxInteger(under, v);
    return rt.arrays.arrayFrom(rt.Array(Any), items);
}

fn boxInteger(type_name: []const u8, v: i64) Any {
    inline for (.{ i8, u8, i16, c_ushort, i32, u32, i64, u64 }) |N| {
        if (std.mem.eql(u8, rt.boxType(N).name, type_name)) return rt.box(@as(N, @intCast(v)));
    }
    return rt.box(@as(i32, @intCast(v)));
}

/// The number a boxed integer holds (an enum's value is boxed as its number)
fn boxedInteger(o: Any) ?i64 {
    const p = o orelse return null;
    inline for (.{ i8, u8, i16, c_ushort, i32, u32, i64, u64 }) |N| {
        if (p.type == rt.boxType(N)) return @intCast(rt.boxed(N, p).value);
    }
    return null;
}

/// `Enum.GetName(t, value)`: the name of the case of that value (null when none)
pub fn enumName(t: Type, value: Any) Raised!String {
    if (t.kind != .@"enum") return notEnum();
    const v = boxedInteger(value) orelse return rt.raise(rt.ArgumentException, rt.str("The value passed in must be an enum base or an underlying type for an enum, such as an Int32. (Parameter 'value')"));
    for (t.enum_values, 0..) |x, i| {
        if (x == v) return text(t.enum_names[i]);
    }
    return null;
}

/// `Enum.IsDefined(t, value)`: a case of that value, or of that name
pub fn enumIsDefined(t: Type, value: Any) Raised!bool {
    if (t.kind != .@"enum") return notEnum();
    if (value) |p| {
        if (p.type == rt.boxType(String)) {
            const name_ = rt.boxed(String, p).value;
            for (t.enum_names) |n| {
                if (sameText(n, name_)) return true;
            }
            return false;
        }
    }
    const v = boxedInteger(value) orelse return rt.raise(rt.ArgumentException, rt.str("The value passed in must be an enum base or an underlying type for an enum, such as an Int32. (Parameter 'value')"));
    for (t.enum_values) |x| {
        if (x == v) return true;
    }
    return false;
}

fn sameText(a: []const u8, b: String) bool {
    const u = rt.unitsOf(b);
    if (u.len != a.len) return false;
    for (a, u) |x, y| {
        if (@as(u16, x) != y) return false;
    }
    return true;
}

/// The value `v` boxed as the enum's underlying number
fn boxUnderlying(t: Type, v: i64) Any {
    const u = t.underlying orelse typeOf(i32);
    inline for (.{ i8, u8, i16, c_ushort, i32, u32, i64, u64 }) |N| {
        if (u == typeOf(N)) return rt.box(@as(N, @intCast(v)));
    }
    return rt.box(@as(i32, @intCast(v)));
}

/// `Enum.Parse(t, s[, ignoreCase])`: a case's name, names joined by commas (their values or'd),
/// or a number
pub fn enumParse(t: Type, s: String, ignore_case: bool) Raised!Any {
    if (t.kind != .@"enum") return notEnum();
    const units = rt.unitsOf(s);
    var total: i64 = 0;
    var start: usize = 0;
    var i: usize = 0;
    while (i <= units.len) : (i += 1) {
        if (i == units.len or units[i] == ',') {
            var a = start;
            var b = i;
            while (a < b and (units[a] == ' ' or units[a] == '\t')) a += 1;
            while (b > a and (units[b - 1] == ' ' or units[b - 1] == '\t')) b -= 1;
            const part = units[a..b];
            if (part.len == 0) return rt.raise(rt.ArgumentException, rt.format(.{ "Requested value '", s, "' was not found." }));
            var found: ?i64 = null;
            for (t.enum_names, 0..) |n, k| {
                if (n.len != part.len) continue;
                var same = true;
                for (n, part) |x, y| {
                    const ux: u16 = x;
                    if (ux != y and !(ignore_case and y < 128 and std.ascii.toLower(x) == std.ascii.toLower(@truncate(y)))) {
                        same = false;
                        break;
                    }
                }
                if (same) {
                    found = t.enum_values[k];
                    break;
                }
            }
            if (found == null) {
                // (a number)
                var neg = false;
                var j: usize = 0;
                if (j < part.len and (part[j] == '-' or part[j] == '+')) {
                    neg = part[j] == '-';
                    j += 1;
                }
                if (j == part.len) return rt.raise(rt.ArgumentException, rt.format(.{ "Requested value '", s, "' was not found." }));
                var n: i64 = 0;
                while (j < part.len) : (j += 1) {
                    if (part[j] < '0' or part[j] > '9') return rt.raise(rt.ArgumentException, rt.format(.{ "Requested value '", s, "' was not found." }));
                    n = n * 10 + (part[j] - '0');
                }
                found = if (neg) -n else n;
            }
            total |= found.?;
            start = i + 1;
        }
    }
    return boxUnderlying(t, total);
}

/// `t.IsAssignableFrom(s)` (and `IsInstanceOfType` of a value of the type `s`)
pub fn isAssignableFrom(t: Type, s: Type) bool {
    if (std.mem.eql(u8, t.full_name, "System.Object")) return true;
    if (equals(t, s)) return true;
    var c: ?Type = s;
    while (c) |x| : (c = x.parent) {
        if (equals(x, t)) return true;
        for (x.interfaces) |i| {
            if (equals(i, t)) return true;
        }
    }
    return false;
}

/// The type of a boxed value or an object (`o.GetType()` of an `obj`)
pub fn typeOfObject(o: Any) Raised!Type {
    const p = o orelse return rt.raise(rt.NullReferenceException, rt.str("Object reference not set to an instance of an object."));
    if (p.type.reflect) |f| return f();
    // (an object of a class: by its name, interned per ObjType)
    rt.lockField(&reflect_lock);
    defer rt.unlockField(&reflect_lock);
    if (class_types.get(p.type)) |existing| return existing;
    const bk = rt.bookkeeping();
    const info = bk.create(TypeInfo) catch rt.oom();
    info.* = .{ .full_name = p.type.name, .name = p.type.name[if (std.mem.lastIndexOfAny(u8, p.type.name, ".+")) |i| i + 1 else 0..], .namespace = "", .kind = .class };
    class_types.put(bk, p.type, info) catch rt.oom();
    return info;
}

/// `e.GetType()` of an exception: by its class's name, interned per exception type
pub fn typeOfExn(e: rt.Exn) Type {
    rt.lockField(&reflect_lock);
    defer rt.unlockField(&reflect_lock);
    if (exn_types.get(e.type)) |existing| return existing;
    const bk = rt.bookkeeping();
    const full = e.type.name;
    const info = bk.create(TypeInfo) catch rt.oom();
    const dot = std.mem.lastIndexOfScalar(u8, full, '.');
    info.* = .{
        .full_name = full,
        .name = full[if (std.mem.lastIndexOfAny(u8, full, ".+")) |i| i + 1 else 0..],
        .namespace = if (dot) |i| full[0..i] else "",
        .kind = .class,
    };
    exn_types.put(bk, e.type, info) catch rt.oom();
    return info;
}

pub fn objectIsRecord(o: Any) Raised!bool {
    return isRecord(try typeOfObject(o));
}

pub fn objectIsUnion(o: Any) Raised!bool {
    return isUnion(try typeOfObject(o));
}

pub fn objectCaseTag(o: Any) Raised!i32 {
    return unionTag(try typeOfObject(o), o);
}

pub fn objectCaseName(o: Any) Raised!String {
    const t = try typeOfObject(o);
    const tag = try unionTag(t, o);
    return text(t.cases[@intCast(tag)].name);
}

pub fn objectCaseFields(o: Any) Raised!rt.Array(Any) {
    const t = try typeOfObject(o);
    const tag = try unionTag(t, o);
    return readAll(t.cases[@intCast(tag)].fields, o);
}

pub fn objectRecordFields(o: Any) Raised!rt.Array(Any) {
    return getRecordFields(try typeOfObject(o), o);
}

/// `t.IsInstanceOfType(o)` of an object: by its class (and those above it), or what it holds
pub fn isInstanceOf(t: Type, o: Any) bool {
    const p = o orelse return false;
    if (std.mem.eql(u8, t.full_name, "System.Object")) return true;
    if (p.type.reflect) |f| return isAssignableFrom(t, f());
    var ty: ?*const rt.ObjType = p.type;
    while (ty) |x| : (ty = x.parent) {
        if (std.mem.eql(u8, x.name, t.full_name)) return true;
    }
    return false;
}

pub fn enumUnderlyingType(t: Type) Raised!Type {
    return t.underlying orelse rt.raise(rt.ArgumentException, rt.str("Type provided must be an Enum. (Parameter 'enumType')"));
}

// ---- FSharpType ----

pub fn isRecord(t: Type) bool {
    return t.kind == .record or t.kind == .anon_record;
}

pub fn isUnion(t: Type) bool {
    return t.kind == .@"union";
}

pub fn isTuple(t: Type) bool {
    return t.kind == .tuple;
}

pub fn isFunction(t: Type) bool {
    return t.kind == .function;
}

pub fn recordFields(t: Type) Raised!rt.Array(Property) {
    if (!isRecord(t)) return rt.raise(rt.ArgumentException, rt.format(.{ "The type '", text(t.full_name), "' is not an F# record type. (Parameter 'recordType')" }));
    const items = rt.arrays.arrayItems(rt.Array(Property), t.fields.len);
    for (items, 0..) |*p, i| p.* = .{ .owner = t, .index = i };
    return rt.arrays.arrayFrom(rt.Array(Property), items);
}

pub fn unionCases(t: Type) Raised!rt.Array(UnionCase) {
    if (!isUnion(t)) return rt.raise(rt.ArgumentException, rt.format(.{ "The type '", text(t.full_name), "' is not an F# union type. (Parameter 'unionType')" }));
    const items = rt.arrays.arrayItems(rt.Array(UnionCase), t.cases.len);
    for (items, 0..) |*c, i| c.* = .{ .union_type = t, .index = i };
    return rt.arrays.arrayFrom(rt.Array(UnionCase), items);
}

pub fn tupleElements(t: Type) Raised!rt.Array(Type) {
    if (!isTuple(t)) return rt.raise(rt.ArgumentException, rt.format(.{ "The type '", text(t.full_name), "' is not a tuple type. (Parameter 'tupleType')" }));
    return genericArguments(t);
}

pub fn functionElements(t: Type) Raised!struct { Type, Type } {
    if (!isFunction(t) or t.args.len != 2) return rt.raise(rt.ArgumentException, rt.format(.{ "The type '", text(t.full_name), "' is not an F# function type. (Parameter 'functionType')" }));
    return .{ t.args[0], t.args[1] };
}

/// `FSharpType.MakeTupleType(types)`: a tuple type of these (equal to `typeof` of it)
pub fn makeTupleType(types: rt.Array(Type)) Type {
    var names: std.ArrayList(u8) = .empty;
    defer names.deinit(rt.allocator);
    names.print(rt.allocator, "System.Tuple`{d}[", .{types.items.len}) catch rt.oom();
    for (types.items, 0..) |e, i| {
        if (i > 0) names.append(rt.allocator, ',') catch rt.oom();
        names.appendSlice(rt.allocator, e.full_name) catch rt.oom();
    }
    names.append(rt.allocator, ']') catch rt.oom();
    rt.lockField(&reflect_lock);
    defer rt.unlockField(&reflect_lock);
    if (tuple_types.get(names.items)) |existing| return existing;
    const bk = rt.bookkeeping();
    const elems = bk.dupe(Type, types.items) catch rt.oom();
    const base_len = std.fmt.count("System.Tuple`{d}", .{elems.len});
    const full = bk.dupe(u8, names.items) catch rt.oom();
    const info = bk.create(TypeInfo) catch rt.oom();
    info.* = .{ .full_name = full, .name = full["System.".len..base_len], .namespace = "System", .kind = .tuple, .args = elems };
    // (what a tuple of these is made of: the one `typeof` gives, when the program has it)
    info.make = null;
    tuple_types.put(bk, full, info) catch rt.oom();
    return info;
}

// ---- PropertyInfo and UnionCaseInfo ----

fn propertyField(p: Property) Field {
    if (p.case >= 0) return p.owner.cases[@intCast(p.case)].fields[p.index];
    return p.owner.fields[p.index];
}

pub fn propertyName(p: Property) String {
    return text(propertyField(p).name);
}

pub fn propertyType(p: Property) Type {
    return propertyField(p).ty;
}

/// `field.GetValue(o)`: the field of a boxed value, boxed
pub fn propertyValue(p: Property, o: Any) Raised!Any {
    const g = propertyField(p).get orelse return rt.raise(rt.InvalidOperationException, rt.str("The field cannot be read."));
    return g(o);
}

pub fn caseName(c: UnionCase) String {
    return text(c.union_type.cases[c.index].name);
}

pub fn caseTag(c: UnionCase) i32 {
    return c.union_type.cases[c.index].tag;
}

pub fn caseDeclaringType(c: UnionCase) Type {
    return c.union_type;
}

pub fn caseFieldsOf(c: UnionCase) rt.Array(Property) {
    const fields = c.union_type.cases[c.index].fields;
    const items = rt.arrays.arrayItems(rt.Array(Property), fields.len);
    for (items, 0..) |*p, i| p.* = .{ .owner = c.union_type, .case = @intCast(c.index), .index = i };
    return rt.arrays.arrayFrom(rt.Array(Property), items);
}

// ---- FSharpValue ----

fn values(xs: []const Any) rt.Array(Any) {
    const items = rt.arrays.arrayItems(rt.Array(Any), xs.len);
    @memcpy(items, xs);
    return rt.arrays.arrayFrom(rt.Array(Any), items);
}

fn readAll(fields: []const Field, o: Any) Raised!rt.Array(Any) {
    const items = rt.arrays.arrayItems(rt.Array(Any), fields.len);
    for (fields, 0..) |f, i| items[i] = try f.get.?(o);
    return rt.arrays.arrayFrom(rt.Array(Any), items);
}

/// `FSharpValue.GetRecordFields(r)` of a boxed record of the type `t`
pub fn getRecordFields(t: Type, o: Any) Raised!rt.Array(Any) {
    if (!isRecord(t)) return rt.raise(rt.ArgumentException, rt.str("The input type is not an F# record type."));
    return readAll(t.fields, o);
}

pub fn getTupleFields(t: Type, o: Any) Raised!rt.Array(Any) {
    if (!isTuple(t)) return rt.raise(rt.ArgumentException, rt.str("The input type is not a tuple type."));
    return readAll(t.fields, o);
}

pub fn getTupleField(t: Type, o: Any, i: i32) Raised!Any {
    if (i < 0 or i >= t.fields.len) return rt.raise(rt.ArgumentOutOfRangeException, rt.str("Index was out of range. (Parameter 'index')"));
    return t.fields[@intCast(i)].get.?(o);
}

pub fn makeRecord(t: Type, vals: rt.Array(Any)) Raised!Any {
    const m = t.make orelse return rt.raise(rt.ArgumentException, rt.str("The input type is not an F# record type."));
    return m(vals.items);
}

/// A tuple of a type made by `MakeTupleType`: its elements, boxed (`unbox` to the tuple type
/// makes the tuple of them)
pub const LooseTuple = struct {
    items: rt.Array(Any),
};

pub fn makeTuple(vals: rt.Array(Any), t: Type) Raised!Any {
    if (t.make) |m| return m(vals.items);
    if (vals.items.len != t.args.len) return rt.raise(rt.ArgumentException, rt.str("The number of values given does not match the number of fields."));
    const loose: LooseTuple = .{ .items = rt.dup(vals) };
    defer rt.drop(loose);
    return rt.box(loose);
}

/// The tuple `T` of a loose one
pub fn tupleOfLoose(comptime T: type, loose: LooseTuple) Raised!T {
    const st = @typeInfo(T).@"struct";
    if (loose.items.items.len != st.field_types.len) return rt.raise(rt.InvalidCastException, rt.str("Specified cast is not valid."));
    var r: T = undefined;
    inline for (st.field_types, 0..) |F, i| r[i] = try rt.unbox(F, loose.items.items[i]);
    return r;
}

pub fn makeUnion(c: UnionCase, vals: rt.Array(Any)) Raised!Any {
    return c.union_type.cases[c.index].make.?(vals.items);
}

/// `FSharpValue.GetUnionFields(v, t)`: the case and the fields of a boxed union value
pub fn getUnionFields(t: Type, o: Any) Raised!struct { UnionCase, rt.Array(Any) } {
    if (!isUnion(t)) return rt.raise(rt.ArgumentException, rt.str("The input type is not an F# union type."));
    const tag = try t.tag_of.?(o);
    const index: usize = @intCast(tag);
    return .{ .{ .union_type = t, .index = index }, try readAll(t.cases[index].fields, o) };
}

pub fn unionTag(t: Type, o: Any) Raised!i32 {
    if (!isUnion(t)) return rt.raise(rt.ArgumentException, rt.str("The input type is not an F# union type."));
    return t.tag_of.?(o);
}

pub fn getRecordField(o: Any, p: Property) Raised!Any {
    return propertyValue(p, o);
}
