//! %A: a value as F# would write it (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const Exn = rt.Exn;
const Obj = rt.Obj;
const ShowNode = rt.ShowNode;
const String = rt.String;
const TextBuilder = rt.TextBuilder;
const TreeWalk = rt.TreeWalk;
const TypeShape = rt.TypeShape;
const bigDigits = rt.bigDigits;
const decAscii = rt.decAscii;
const drop = rt.drop;
const floatText = rt.floatText;
const ifaceToObjBorrow = rt.ifaceToObjBorrow;
const isBigInt = rt.isBigInt;
const isCellNull = rt.isCellNull;
const isCellPtr = rt.isCellPtr;
const isCollection = rt.isCollection;
const isCount = rt.isCount;
const isDecimal = rt.isDecimal;
const isFunc = rt.isFunc;
const isIface = rt.isIface;
const oom = rt.oom;
const reflect = rt.reflect;
const scratch_len = rt.scratch_len;
const showSeq = rt.showSeq;
const str = rt.str;
const take = rt.take;
const unitsOf = rt.unitsOf;

// %A: a value as F# would write it
//
// This is the printer of FSharp.Core, rule for rule, so that the text is the same: the value
// becomes a layout (text, and joints that may or must break), the layout is fitted into lines
// of 80 characters by breaking the outermost joints first, and the result is written with the
// indentation the breaks ask for. A list shows its first 100 items; a record that contains
// itself is cut where it comes round again.
// ---------------------------------------------------------------------------------------------

pub const Joint = union(enum) { unbreakable, breakable: i32, broken: i32 };

pub const Layout = struct {
    /// no space is wanted before this text (`tight_left`) or after it (`tight_right`)
    tight_left: bool,
    tight_right: bool,
    what: union(enum) {
        leaf: []const u16,
        node: struct { l: *Layout, r: *Layout, joint: Joint },
    },
};

/// Where a value stands decides whether it needs brackets.
pub const Prec = enum(u8) { bracket_if_tuple_or_not_atomic = 2, bracket_if_tuple = 3, never_bracket = 4 };

pub const print_width = 80;
pub const print_length = 100;
pub const print_depth = 100;

pub const Shower = struct {
    arena: std.mem.Allocator,
    /// the reference records that are being written, to find one that contains itself
    path: [print_depth]*const anyopaque = undefined,
    on_path: usize = 0,
    /// the breaks that could still be made to gain room: the columns each would save (negative
    /// once it was made), the innermost last
    savings: std.ArrayList(i32) = .empty,
    outer: usize = 0,

    pub fn leaf(b: *Shower, tight_left: bool, text: []const u16, tight_right: bool) *Layout {
        const l = b.arena.create(Layout) catch oom();
        l.* = .{ .tight_left = tight_left, .tight_right = tight_right, .what = .{ .leaf = text } };
        return l;
    }

    pub fn ascii(b: *Shower, tight_left: bool, text: []const u8, tight_right: bool) *Layout {
        const u = b.arena.alloc(u16, text.len) catch oom();
        for (text, u) |c, *to| to.* = c;
        return b.leaf(tight_left, u, tight_right);
    }

    pub fn word(b: *Shower, text: []const u8) *Layout {
        return b.ascii(false, text, false);
    }

    pub fn join(b: *Shower, l: *Layout, r: *Layout, joint: Joint) *Layout {
        const n = b.arena.create(Layout) catch oom();
        n.* = .{ .tight_left = l.tight_left, .tight_right = r.tight_right, .what = .{ .node = .{ .l = l, .r = r, .joint = joint } } };
        return n;
    }

    pub fn tight(b: *Shower, l: *Layout, r: *Layout) *Layout {
        return b.join(l, r, .unbreakable);
    }

    pub fn bracket(b: *Shower, l: *Layout) *Layout {
        return b.tight(b.tight(b.ascii(false, "(", true), l), b.ascii(true, ")", false));
    }

    /// The items with `sep` after each but the last, and a possible break after each `sep`.
    pub fn separated(b: *Shower, items: []const *Layout, sep: []const u8) *Layout {
        var all = items[0];
        for (items[1..]) |item| all = b.join(b.tight(all, b.ascii(true, sep, false)), item, .{ .breakable = 0 });
        return all;
    }

    /// `Case`, `Case x` or `Case (x, y)`: a union case, `Some`, `ValueSome`, or an F# exception.
    pub fn case(b: *Shower, name: []const u8, payload: anytype, prec: Prec, depth: i32) *Layout {
        return b.caseShape(name, payload, .{}, &.{}, prec, depth);
    }

    pub fn caseShape(b: *Shower, name: []const u8, payload: anytype, comptime shape: TypeShape, field_refs: []const u16, prec: Prec, depth: i32) *Layout {
        const P = @TypeOf(payload);
        if (P == void) return b.word(name);
        const fields = if (@typeInfo(P) == .pointer) payload else &payload;
        const names = @typeInfo(@TypeOf(fields.*)).@"struct".field_names;
        comptime var n = 0;
        inline for (names) |field| {
            if (comptime !isCount(field)) n += 1;
        }
        if (n == 0) return b.word(name);
        var items: [n]*Layout = undefined;
        comptime var i = 0;
        inline for (names) |field| {
            if (comptime !isCount(field)) {
                const child_idx = if (i < field_refs.len) field_refs[i] else ShowNode.auto;
                items[i] = b.showShape(@field(fields, field), shape, child_idx, if (n == 1) .bracket_if_tuple_or_not_atomic else .bracket_if_tuple, depth - 1);
                i += 1;
            }
        }
        const args = if (n == 1) items[0] else b.bracket(b.separated(&items, ","));
        const whole = b.join(b.word(name), args, .{ .breakable = 2 });
        return if (@backingInt(prec) <= @backingInt(Prec.bracket_if_tuple_or_not_atomic)) b.bracket(whole) else whole;
    }

    /// A two-dimensional array: `[[a; b]` and every further row on a line of its own, `]`.
    pub fn array2D(b: *Shower, items: anytype, arr_shape: [2]usize, depth: i32) *Layout {
        return b.array2DShape(items, arr_shape, .{}, ShowNode.auto, depth);
    }

    pub fn array2DShape(b: *Shower, items: anytype, arr_shape: [2]usize, comptime shape: TypeShape, child_idx: u16, depth: i32) *Layout {
        var all: ?*Layout = null;
        for (0..arr_shape[0]) |i| {
            var row: std.ArrayList(*Layout) = .empty;
            for (items[i * arr_shape[1] ..][0..arr_shape[1]]) |item| {
                if (row.items.len == print_length) {
                    row.append(b.arena, b.word("...")) catch oom();
                    break;
                }
                row.append(b.arena, b.showShape(item, shape, child_idx, .bracket_if_tuple, depth - 1)) catch oom();
            }
            const inner = if (row.items.len == 0) b.word("[]") else b.tight(b.tight(b.ascii(false, "[", true), b.separated(row.items, ";")), b.ascii(true, "]", false));
            all = if (all) |above| b.join(above, inner, .{ .broken = 0 }) else inner;
        }
        const body = all orelse return b.word("[]");
        return b.tight(b.tight(b.ascii(false, "[", true), body), b.ascii(true, "]", false));
    }

    /// `{ A = 1` and every further field on a line of its own.
    pub fn record(b: *Shower, fields: anytype, depth: i32) *Layout {
        return b.recordShape(fields, .{}, &.{}, depth);
    }

    pub fn recordShape(b: *Shower, fields: anytype, comptime shape: TypeShape, field_refs: []const u16, depth: i32) *Layout {
        var all: ?*Layout = null;
        comptime var fi: usize = 0;
        inline for (@typeInfo(@TypeOf(fields.*)).@"struct".field_names) |field| {
            if (comptime !isCount(field)) {
                const child_idx = if (fi < field_refs.len) field_refs[fi] else ShowNode.auto;
                fi += 1;
                const value = b.showShape(@field(fields, field), shape, child_idx, .bracket_if_tuple, depth - 1);
                const item = b.join(b.tight(b.word(field), b.word("=")), value, .{ .breakable = 1 });
                all = if (all) |above| b.join(above, item, .{ .broken = 0 }) else item;
            }
        }
        return b.tight(b.tight(b.word("{"), all.?), b.word("}"));
    }

    pub fn number(b: *Shower, x: anytype) *Layout {
        const T = @TypeOf(x);
        var buf: [scratch_len + 4]u8 = undefined;
        switch (@typeInfo(T)) {
            .int => |info| {
                const suffix = switch (T) {
                    i8 => "y",
                    u8 => "uy",
                    c_ushort => "us",
                    i16 => "s",
                    i32 => "",
                    u32 => "u",
                    i64 => "L",
                    u64 => "UL",
                    isize => "n",
                    usize => "un",
                    else => if (info.signedness == .signed) "" else "u",
                };
                return b.word(std.fmt.bufPrint(&buf, "{d}{s}", .{ x, suffix }) catch unreachable);
            },
            .float => {
                const suffix = if (T == f32) "f" else "";
                if (std.math.isNan(x)) return b.word("nan" ++ suffix);
                if (std.math.isInf(x)) return if (x > 0) b.word("infinity" ++ suffix) else b.word("-infinity" ++ suffix);
                if (T == f32 and x > -2147483648.0 and x < 2147483648.0 and @trunc(x) == x) {
                    return b.word(std.fmt.bufPrint(&buf, "{d}.0f", .{@as(i32, @intFromFloat(x))}) catch unreachable);
                }
                const text = floatText(.{ .kind = 'g', .precision = 10 }, x, buf[0..scratch_len]);
                var plain = T == f64;
                for (text) |c| {
                    if (!(std.ascii.isDigit(c) or c == '-')) plain = false;
                }
                const tail = if (plain) ".0" else suffix;
                var all: [scratch_len + 4]u8 = undefined;
                return b.word(std.fmt.bufPrint(&all, "{s}{s}", .{ text, tail }) catch unreachable);
            },
            else => comptime unreachable,
        }
    }

    pub fn char(b: *Shower, c: u16) *Layout {
        var text: [8]u16 = undefined;
        var n: usize = 0;
        text[n] = '\'';
        n += 1;
        if (c == '\'' or c == '\\') {
            text[n] = '\\';
            text[n + 1] = c;
            n += 2;
        } else if (c == 8) {
            text[n] = '\\';
            text[n + 1] = 'b';
            n += 2;
        } else if (c < 0x20 or (c >= 0x7F and c <= 0x9F)) {
            text[n] = '\\';
            text[n + 1] = '0' + c / 100;
            text[n + 2] = '0' + (c / 10) % 10;
            text[n + 3] = '0' + c % 10;
            n += 4;
        } else {
            text[n] = c;
            n += 1;
        }
        text[n] = '\'';
        n += 1;
        return b.leaf(false, b.arena.dupe(u16, text[0..n]) catch oom(), false);
    }

    pub fn quoted(b: *Shower, u: []const u16) *Layout {
        const text = b.arena.alloc(u16, u.len + 2) catch oom();
        text[0] = '"';
        @memcpy(text[1..][0..u.len], u);
        text[u.len + 1] = '"';
        return b.leaf(false, text, false);
    }

    /// The layout of a value. A `u16` is taken to be a char unless `node` marks it `.u16_num`.
    pub fn show(b: *Shower, x: anytype, prec: Prec, depth: i32) *Layout {
        return b.showShape(x, .{}, ShowNode.auto, prec, depth);
    }

    pub fn showShape(b: *Shower, x: anytype, comptime shape: TypeShape, node_idx: u16, prec: Prec, depth: i32) *Layout {
        const T = @TypeOf(x);
        if (depth <= 0) return b.word("...");
        if (T == String) return if (x) |p| b.quoted(p.units()) else b.word("null");
        if (T == reflect.Type) return b.word(x.full_name);
        if (T == Any) return if (x) |o| b.showShape(o, shape, node_idx, prec, depth) else b.word("null");
        if (comptime isBigInt(T)) {
            const d = bigDigits(x);
            defer rt.alloc().free(d);
            return b.word(d);
        }
        if (comptime isDecimal(T)) {
            var buf: [41]u8 = undefined;
            const t = decAscii(x, &buf);
            buf[t.len] = 'M';
            const copy = b.arena.dupe(u8, buf[0 .. t.len + 1]) catch oom();
            return b.word(copy);
        }
        if (comptime isCellPtr(T)) {
            if (isCellNull(x)) return b.word("null");
        }
        if (T == Exn) {
            if (x.type.show) |exn_show_fn| return exn_show_fn(b, x, prec, depth);
            return b.word(x.type.name);
        }
        if (T == Obj) return b.word(x.type.name);
        if (comptime isIface(T)) {
            if (ifaceToObjBorrow(x)) |o| return b.word(o.type.name);
            return b.word("<iface>");
        }
        if (comptime isFunc(T)) return b.word("<fun>");
        const node: ShowNode = if (node_idx < shape.nodes.len) shape.nodes[node_idx] else .{};
        switch (@typeInfo(T)) {
            .void => return b.word("()"),
            .bool => return b.word(if (x) "true" else "false"),
            .int => return if (T == u16 and node.kind != .u16_num) b.char(x) else b.number(x),
            .float => return b.number(x),
            .optional => {
                const is_vopt = node.kind == .vopt;
                const child: u16 = if (is_vopt or node.kind == .opt) node.a else ShowNode.auto;
                if (x) |v| return b.caseShape(if (is_vopt) "ValueSome" else "Some", .{v}, shape, &.{child}, prec, depth);
                return b.word(if (is_vopt) "ValueNone" else "None");
            },
            .pointer => |ptr| {
                if (comptime @hasDecl(ptr.child, "fable_show_shape")) return ptr.child.fable_show_shape(b, x, shape, node, depth);
                if (comptime @hasDecl(ptr.child, "fable_identity")) return ptr.child.fable_show(b, x, depth);
                if (comptime @hasDecl(ptr.child, "fable_array")) {
                    const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
                    if (x.shape) |arr_shape| return b.array2DShape(x.items, arr_shape, shape, child, depth);
                    if (x.items.len == 0) return b.word("[||]");
                    var items: std.ArrayList(*Layout) = .empty;
                    for (x.items) |item| {
                        if (items.items.len == print_length) {
                            items.append(b.arena, b.word("...")) catch oom();
                            break;
                        }
                        items.append(b.arena, b.showShape(item, shape, child, .bracket_if_tuple, depth - 1)) catch oom();
                    }
                    return b.tight(b.tight(b.ascii(false, "[|", true), b.separated(items.items, ";")), b.ascii(true, "|]", false));
                }
                // a reference record
                const addr: *const anyopaque = @ptrCast(x);
                for (b.path[0..b.on_path]) |seen| {
                    if (seen == addr) return b.word("...");
                }
                if (b.on_path == b.path.len) return b.word("...");
                b.path[b.on_path] = addr;
                b.on_path += 1;
                defer b.on_path -= 1;
                const field_refs: []const u16 = if (node.kind == .record) shape.refs[node.a..][0..node.b] else &.{};
                return b.recordShape(x, shape, field_refs, depth);
            },
            .@"struct" => |s| {
                // a sequence (Seq.fs): `seq [a; b; c; d; ...]`, which walks it, as .NET does
                if (comptime @hasField(T, "fable_seq")) {
                    const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
                    var items: [4]*Layout = undefined;
                    var n: usize = 0;
                    var more = false;
                    const walk = x.fable_seq.code(x.fable_seq.env, {}) catch {
                        drop(take());
                        return b.word("seq [...]");
                    };
                    defer drop(walk);
                    defer walk.close.code(walk.close.env, {}) catch drop(take());
                    while (true) {
                        const next = walk.next.code(walk.next.env, {}) catch {
                            drop(take());
                            break;
                        };
                        const item = next orelse break;
                        defer drop(item);
                        if (n == 4) {
                            more = true;
                            break;
                        }
                        items[n] = b.showShape(item, shape, child, .bracket_if_tuple, depth - 1);
                        n += 1;
                    }
                    return showSeq(b, items[0..n], more);
                }
                if (!s.is_tuple) {
                    const field_refs: []const u16 = if (node.kind == .record) shape.refs[node.a..][0..node.b] else &.{};
                    return b.recordShape(&x, shape, field_refs, depth);
                }
                const is_struct = node.kind == .struct_tuple;
                const field_refs: []const u16 = if (is_struct or node.kind == .tuple) shape.refs[node.a..][0..node.b] else &.{};
                var items: [s.field_names.len]*Layout = undefined;
                inline for (s.field_names, 0..) |field, i| {
                    const child_idx = if (i < field_refs.len) field_refs[i] else ShowNode.auto;
                    items[i] = b.showShape(@field(x, field), shape, child_idx, .bracket_if_tuple, depth - 1);
                }
                const tup = b.bracket(b.separated(&items, ","));
                return if (is_struct) b.tight(b.word("struct"), tup) else tup;
            },
            .@"union" => {
                if (comptime isCollection(T)) {
                    // `map [(1, "a"); ...]`, `set [1; 2]`: nine entries, then `...`
                    const name = if (T.fable_collection == .map) "map" else "set";
                    const k_idx: u16 = if (node.kind == .map or node.kind == .seq) node.a else ShowNode.auto;
                    const v_idx: u16 = if (node.kind == .map) node.b else ShowNode.auto;
                    var items: std.ArrayList(*Layout) = .empty;
                    var w = TreeWalk(T).init(x);
                    while (w.next()) |n| {
                        if (items.items.len == 9) {
                            items.append(b.arena, b.word("...")) catch oom();
                            break;
                        }
                        const item = if (comptime T.fable_collection == .map) blk: {
                            const pair_items: [2]*Layout = .{
                                b.showShape(n.key, shape, k_idx, .bracket_if_tuple, depth - 1),
                                b.showShape(n.value, shape, v_idx, .bracket_if_tuple, depth - 1),
                            };
                            break :blk b.bracket(b.separated(&pair_items, ","));
                        } else b.showShape(n.key, shape, k_idx, .bracket_if_tuple, depth - 1);
                        items.append(b.arena, item) catch oom();
                    }
                    const list = if (items.items.len == 0)
                        b.word("[]")
                    else
                        b.tight(b.tight(b.ascii(false, "[", true), b.separated(items.items, ";")), b.ascii(true, "]", false));
                    const whole = b.join(b.word(name), list, .{ .breakable = 2 });
                    return if (@backingInt(prec) <= @backingInt(Prec.bracket_if_tuple_or_not_atomic)) b.bracket(whole) else whole;
                }
                if (comptime @hasDecl(T, "fable_list")) {
                    const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
                    if (x == .Empty) return b.word("[]");
                    var items: std.ArrayList(*Layout) = .empty;
                    var rest = x;
                    while (rest == .Cons) : (rest = rest.Cons.Tail) {
                        if (items.items.len == print_length) {
                            items.append(b.arena, b.word("...")) catch oom();
                            break;
                        }
                        items.append(b.arena, b.showShape(rest.Cons.Head, shape, child, .bracket_if_tuple, depth - 1)) catch oom();
                    }
                    return b.tight(b.tight(b.ascii(false, "[", true), b.separated(items.items, ";")), b.ascii(true, "]", false));
                }
                switch (x) {
                    inline else => |payload, tag| {
                        const tag_idx = comptime blk: {
                            for (@typeInfo(T).@"union".field_names, 0..) |name, idx| {
                                if (std.mem.eql(u8, name, @tagName(tag))) break :blk idx;
                            }
                            unreachable;
                        };
                        const field_refs: []const u16 = if (node.kind == .@"union" and tag_idx < node.b) blk: {
                            const case_idx = shape.refs[node.a + tag_idx];
                            const cn = if (case_idx < shape.nodes.len) shape.nodes[case_idx] else ShowNode{};
                            break :blk if (cn.kind == .record) shape.refs[cn.a..][0..cn.b] else &.{};
                        } else &.{};
                        return b.caseShape(@tagName(tag), payload, shape, field_refs, prec, depth);
                    },
                }
            },
            else => @compileError("fable: a value of type " ++ @typeName(T) ++ " cannot be written with %A"),
        }
    }

    /// Make the next break that is still open, the outermost first; the columns it saves.
    pub fn forceBreak(b: *Shower) ?i32 {
        if (b.outer == b.savings.items.len) return null;
        const saving = b.savings.items[b.outer];
        b.savings.items[b.outer] = -saving;
        b.outer += 1;
        return saving;
    }

    /// Fit `layout`, which starts at column `start`, into the width by turning joints that may
    /// break into breaks. Returns the column after it, and the width of its last line.
    pub fn fit(b: *Shower, start: i32, layout: *Layout) struct { i32, i32 } {
        switch (layout.what) {
            .leaf => |text| {
                const width: i32 = @intCast(text.len);
                var pos = start;
                while (pos + width > print_width) {
                    pos -= b.forceBreak() orelse break;
                }
                return .{ pos + width, width };
            },
            .node => |*n| {
                const mid: i32 = if (n.l.tight_right or n.r.tight_left) 0 else 1;
                var pos, const left = b.fit(start, n.l);
                switch (n.joint) {
                    .unbreakable => {
                        pos, const right = b.fit(pos + mid, n.r);
                        return .{ pos, left + mid + right };
                    },
                    .broken => |indent| {
                        pos, const right = b.fit(pos - left + indent, n.r);
                        return .{ pos, indent + right };
                    },
                    .breakable => |indent| {
                        const saving = left + mid - indent;
                        if (saving <= 0) {
                            pos, const right = b.fit(pos + mid, n.r);
                            return .{ pos, left + mid + right };
                        }
                        b.savings.append(b.arena, saving) catch oom();
                        pos, const right = b.fit(pos + mid, n.r);
                        const made = b.savings.pop().? < 0;
                        if (b.outer > b.savings.items.len) b.outer = b.savings.items.len;
                        if (!made) return .{ pos, left + mid + right };
                        n.joint = .{ .broken = indent };
                        return .{ pos, indent + right };
                    },
                }
            },
        }
    }

    pub fn write(out: *TextBuilder, column: *i32, layout: *const Layout, tab: i32) void {
        switch (layout.what) {
            .leaf => |text| {
                out.add(text);
                column.* += @intCast(text.len);
            },
            .node => |n| {
                write(out, column, n.l, tab);
                switch (n.joint) {
                    .broken => |indent| {
                        out.addOne('\n');
                        var i: i32 = 0;
                        while (i < tab + indent) : (i += 1) out.addOne(' ');
                        column.* = tab + indent;
                        write(out, column, n.r, tab + indent);
                    },
                    else => {
                        if (!(n.l.tight_right or n.r.tight_left)) {
                            out.addOne(' ');
                            column.* += 1;
                        }
                        write(out, column, n.r, column.*);
                    },
                }
            },
        }
    }
};

pub fn writeObj(out: *TextBuilder, o: Obj) void {
    if (o.type.to_string) |f| {
        const t = f(null, o, {}) catch return out.addAscii(o.type.name);
        defer drop(t);
        return out.add(unitsOf(t));
    }
    out.addAscii(o.type.name);
}

/// `%A`: the value as F# would write it.
pub fn anyText(x: anytype) String {
    return anyTextAt(.{}, ShowNode.auto, x);
}

pub fn anyTextShape(comptime shape: TypeShape, x: anytype) String {
    const start: u16 = if (shape.nodes.len != 0) 0 else ShowNode.auto;
    return anyTextAt(shape, start, x);
}

pub fn anyTextAt(comptime shape: TypeShape, node_idx: u16, x: anytype) String {
    if (@TypeOf(x) == String and x == null) return str("<null>");
    var arena = std.heap.ArenaAllocator.init(rt.alloc());
    defer arena.deinit();
    var b: Shower = .{ .arena = arena.allocator() };
    const layout = b.showShape(x, shape, node_idx, .bracket_if_tuple, print_depth);
    _ = b.fit(0, layout);
    var out: TextBuilder = .{};
    var column: i32 = 0;
    Shower.write(&out, &column, layout, 0);
    return out.finish();
}
