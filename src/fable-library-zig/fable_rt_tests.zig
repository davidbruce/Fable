//! Unit tests for `fable_rt` (wired into `fable_rt.zig` via `test { _ = @import("fable_rt_tests.zig"); }`)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const ArithmeticException = rt.ArithmeticException;
const Array = rt.Array;
const Cell = rt.Cell;
const Decimal = rt.Decimal;
const Dictionary = rt.Dictionary;
const DivideByZeroException = rt.DivideByZeroException;
const Env = rt.Env;
const ExnOf = rt.ExnOf;
const Failure = rt.Failure;
const FormatException = rt.FormatException;
const Func = rt.Func;
const GcHdr = rt.GcHdr;
const HashSet = rt.HashSet;
const Iface = rt.Iface;
const IfaceAnon1 = rt.IfaceAnon1;
const IfaceMeta = rt.IfaceMeta;
const IndexOutOfRangeException = rt.IndexOutOfRangeException;
const KeyNotFoundException = rt.KeyNotFoundException;
const List = rt.List;
const MayRaise = rt.MayRaise;
const NetDecimal = rt.NetDecimal;
const NullReferenceException = rt.NullReferenceException;
const Obj = rt.Obj;
const ObjType = rt.ObjType;
const OutOfMemoryException = rt.OutOfMemoryException;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const Random = rt.Random;
const Ref = rt.Ref;
const ResizeArray = rt.ResizeArray;
const ShowNode = rt.ShowNode;
const Spec = rt.Spec;
const String = rt.String;
const StringBuilder = rt.StringBuilder;
const SystemException = rt.SystemException;
const TailCtx = rt.TailCtx;
const TailFn = rt.TailFn;
const TailStatus = rt.TailStatus;
const TypeShape = rt.TypeShape;
const Weak = rt.Weak;
const absOf = rt.absOf;
const across = rt.across;
const acrossAssumed = rt.acrossAssumed;
const anyIsClass = rt.anyIsClass;
const anyText = rt.anyText;
const anyTextShape = rt.anyTextShape;
const anyToClass = rt.anyToClass;
const anyToString = rt.anyToString;
const apply2 = rt.apply2;
const arg = rt.arg;
const arrayCopy = rt.arrayCopy;
const arrayCreate = rt.arrayCreate;
const arrayFrom = rt.arrayFrom;
const arrayGet = rt.arrayGet;
const arrayItemAt = rt.arrayItemAt;
const arrayLen = rt.arrayLen;
const arrayOf = rt.arrayOf;
const arrayOfList = rt.arrayOfList;
const arraySet = rt.arraySet;
const arraySetAt = rt.arraySetAt;
const arraySlice = rt.arraySlice;
const arraySub = rt.arraySub;
const arrayToList = rt.arrayToList;
const arrayZero = rt.arrayZero;
const arrays = rt.arrays;
const assertNoRaise = rt.assertNoRaise;
const assertNoStore = rt.assertNoStore;
const bigDivRem = rt.bigDivRem;
const bigLit = rt.bigLit;
const bigMul = rt.bigMul;
const bigNeg = rt.bigNeg;
const bigOf = rt.bigOf;
const bigParse = rt.bigParse;
const bigPow = rt.bigPow;
const bigText = rt.bigText;
const bigToFloat = rt.bigToFloat;
const bigToInt = rt.bigToInt;
const bigint = rt.bigint;
const box = rt.box;
const boxed = rt.boxed;
const callAssumedG = rt.callAssumedG;
const callAssumedM = rt.callAssumedM;
const callHofAssumedG = rt.callHofAssumedG;
const callHofAssumedM = rt.callHofAssumedM;
const callHofG = rt.callHofG;
const callHofM = rt.callHofM;
const callM = rt.callM;
const canPlugRet = rt.canPlugRet;
const captured = rt.captured;
const cell = rt.cell;
const cellReuse = rt.cellReuse;
const charNumericValue = rt.charNumericValue;
const closure = rt.closure;
const closure2 = rt.closure2;
const closureTc = rt.closureTc;
const collect = rt.collect;
const collectStep = rt.collectStep;
const collectorPause = rt.collectorPause;
const collectorResume = rt.collectorResume;
const collectorSet = rt.collectorSet;
const compare = rt.compare;
const conv = rt.conv;
const counted = rt.counted;
const decAdd = rt.decAdd;
const decAscii = rt.decAscii;
const decDiv = rt.decDiv;
const decMul = rt.decMul;
const decOf = rt.decOf;
const decParse = rt.decParse;
const decRem = rt.decRem;
const decRound = rt.decRound;
const decSub = rt.decSub;
const decToFloat = rt.decToFloat;
const decToInt = rt.decToInt;
const decWhole = rt.decWhole;
const decimal = rt.decimal;
const dictAdd = rt.dictAdd;
const dictGet = rt.dictGet;
const dictSet = rt.dictSet;
const div = rt.div;
const drop = rt.drop;
const dropAll = rt.dropAll;
const dropEnv = rt.dropEnv;
const dup = rt.dup;
const empty_iface_meta = rt.empty_iface_meta;
const env_iface_meta = rt.env_iface_meta;
const eql = rt.eql;
const exnMessage = rt.exnMessage;
const exnStackTrace = rt.exnStackTrace;
const exn_show = rt.exn_show;
const fitsTailArgs = rt.fitsTailArgs;
const floatText = rt.floatText;
const format = rt.format;
const free = rt.free;
const hash = rt.hash;
const htCount = rt.htCount;
const htNew = rt.htNew;
const htRemove = rt.htRemove;
const ifaceAdapt = rt.ifaceAdapt;
const ifaceBox = rt.ifaceBox;
const ifaceCastClass = rt.ifaceCastClass;
const ifaceClosure = rt.ifaceClosure;
const ifaceIsClass = rt.ifaceIsClass;
const ifaceUnbox = rt.ifaceUnbox;
const index_range = rt.index_range;
const invokeK = rt.invokeK;
const isRaised = rt.isRaised;
const isType = rt.isType;
const isUnique = rt.isUnique;
const listOf = rt.listOf;
const markShared = rt.markShared;
const netText = rt.netText;
const new = rt.new;
const objCast = rt.objCast;
const objIs = rt.objIs;
const objNew = rt.objNew;
const objPart = rt.objPart;
const objStore = rt.objStore;
const objType = rt.objType;
const objVt = rt.objVt;
const obj_iface_meta = rt.obj_iface_meta;
const oom_catchable = rt.oom_catchable;
const oom_policy = rt.oom_policy;
const overflow = rt.overflow;
const parseBool = rt.parseBool;
const parseFloat = rt.parseFloat;
const parseInt = rt.parseInt;
const parseIntFs = rt.parseIntFs;
const plugRet = rt.plugRet;
const pown = rt.pown;
const raAdd = rt.raAdd;
const raContains = rt.raContains;
const raGet = rt.raGet;
const raIndexOf = rt.raIndexOf;
const raInsert = rt.raInsert;
const raOfList = rt.raOfList;
const raRemove = rt.raRemove;
const raRemoveAt = rt.raRemoveAt;
const raSort = rt.raSort;
const raise = rt.raise;
const random = rt.random;
const randomNew = rt.randomNew;
const randomNext = rt.randomNext;
const randomNextBytes = rt.randomNextBytes;
const randomNextDouble = rt.randomNextDouble;
const randomNextMax = rt.randomNextMax;
const randomNextRange = rt.randomNextRange;
const refEql = rt.refEql;
const rem = rt.rem;
const roundEven = rt.roundEven;
const roundTo = rt.roundTo;
const sbAppend = rt.sbAppend;
const sbNew = rt.sbNew;
const sbToString = rt.sbToString;
const scratch_len = rt.scratch_len;
const setAdd = rt.setAdd;
const setOfList = rt.setOfList;
const sgc = rt.sgc;
const signOf = rt.signOf;
const spanClear = rt.spanClear;
const spanCopyTo = rt.spanCopyTo;
const spanFill = rt.spanFill;
const spanSet = rt.spanSet;
const spanToArray = rt.spanToArray;
const store = rt.store;
const storeIn = rt.storeIn;
const str = rt.str;
const strAt = rt.strAt;
const strCase = rt.strCase;
const strCompareCulture = rt.strCompareCulture;
const strCompareCultureRange = rt.strCompareCultureRange;
const strCompareIgnoreCase = rt.strCompareIgnoreCase;
const strCompareRangeWith = rt.strCompareRangeWith;
const strCompareTo = rt.strCompareTo;
const strConcat = rt.strConcat;
const strContains = rt.strContains;
const strContainsChar = rt.strContainsChar;
const strEndsWith = rt.strEndsWith;
const strEndsWithChar = rt.strEndsWithChar;
const strEndsWithOpt = rt.strEndsWithOpt;
const strEql = rt.strEql;
const strEqualsIgnoreCase = rt.strEqualsIgnoreCase;
const strIndexOf = rt.strIndexOf;
const strIndexOfChar = rt.strIndexOfChar;
const strIndexOfCharIgnoreCase = rt.strIndexOfCharIgnoreCase;
const strInsert = rt.strInsert;
const strIsNullOrEmpty = rt.strIsNullOrEmpty;
const strIsNullOrWhiteSpace = rt.strIsNullOrWhiteSpace;
const strLastIndexOf = rt.strLastIndexOf;
const strLastIndexOfChar = rt.strLastIndexOfChar;
const strLen = rt.strLen;
const strLength = rt.strLength;
const strOfChar = rt.strOfChar;
const strPad = rt.strPad;
const strRemove = rt.strRemove;
const strReplace = rt.strReplace;
const strReplaceChar = rt.strReplaceChar;
const strReplicate = rt.strReplicate;
const strSplitChars = rt.strSplitChars;
const strSplitString = rt.strSplitString;
const strStartsWith = rt.strStartsWith;
const strStartsWithChar = rt.strStartsWithChar;
const strStartsWithOpt = rt.strStartsWithOpt;
const strSubstring = rt.strSubstring;
const strTrim = rt.strTrim;
const tailLoad = rt.tailLoad;
const tailStore = rt.tailStore;
const tail_call = rt.tail_call;
const take = rt.take;
const takeSelf = rt.takeSelf;
const takeSelfBorrowed = rt.takeSelfBorrowed;
const thread = rt.thread;
const throw = rt.throw;
const time = rt.time;
const toText = rt.toText;
const toTextShape = rt.toTextShape;
const tryParseInt = rt.tryParseInt;
const tryUnbox = rt.tryUnbox;
const unbox = rt.unbox;
const unicode = rt.unicode;
const unitsOf = rt.unitsOf;
const upcastIfaceMeta = rt.upcastIfaceMeta;
const weakNew = rt.weakNew;
const weakSet = rt.weakSet;
const weakTryGet = rt.weakTryGet;
const xcallAssumedM = rt.xcallAssumedM;
const xcallHofAssumedG = rt.xcallHofAssumedG;
const xcallHofAssumedM = rt.xcallHofAssumedM;
const xcallHofM = rt.xcallHofM;
const xcallM = rt.xcallM;
const xcallPlain = rt.xcallPlain;

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

pub fn testCons(head: i32, tail: TestList) TestList {
    return .{ .Cons = cell(TestList, .Cons, .{ .head = head, .tail = tail }) };
}

pub fn testRange(n: i32) TestList {
    var l: TestList = .Nil;
    var i: i32 = n;
    while (i > 0) : (i -= 1) l = testCons(i, l);
    return l;
}

pub fn testTree(depth: i32) TestTree {
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

pub fn testSum(xs: TestList) i32 {
    var total: i32 = 0;
    var cur = xs;
    while (cur == .Cons) : (cur = cur.Cons.tail) total += cur.Cons.head;
    return total;
}
const testSum_sig = .{ .borrows = .{true}, .result_borrowed = false };

pub fn testTail(xs: TestList) TestList {
    return if (xs == .Cons) xs.Cons.tail else .Nil;
}
const testTail_sig = .{ .borrows = .{true}, .result_borrowed = true };

pub fn testPush(n: i32, xs: TestList) TestList {
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

pub fn testAddSum(env: ?*Env, x: i32) i32 {
    const c = captured(TestCaptures, env);
    return x + c.n + testSum(c.xs);
}

pub fn testDouble(_: ?*Env, x: i32) i32 {
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

pub fn testCheck(x: i32, owned: TestList) Raised!i32 {
    if (x < 0) {
        throw(TestParseError.new(.{ .pos = x, .items = owned }));
        return error.Raised;
    }
    drop(owned);
    return x;
}
const testCheck_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

pub fn testOuter(x: i32) MayRaise(i32, .{testCheck}) {
    const xs = testRange(2);
    const raw = across(testCheck, testCheck_sig, .{ .plain, .give }, .{ x, xs });
    const r = if (comptime isRaised(@TypeOf(raw))) (raw catch return error.Raised) else raw;
    return r + 1;
}

pub fn testPlain(x: i32) MayRaise(i32, .{testSum}) {
    return x;
}

/// (an allocator that refuses what is larger than a megabyte: the program's allocation fails,
/// the exception's own does not)
const RefusingLarge = struct {
    inner: std.mem.Allocator,

    fn allocFn(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret: usize) ?[*]u8 {
        const self: *RefusingLarge = @ptrCast(@alignCast(ctx));
        if (len > 1 << 20) return null;
        return self.inner.rawAlloc(len, alignment, ret);
    }

    fn resizeFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret: usize) bool {
        const self: *RefusingLarge = @ptrCast(@alignCast(ctx));
        return self.inner.rawResize(memory, alignment, new_len, ret);
    }

    fn remapFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret: usize) ?[*]u8 {
        const self: *RefusingLarge = @ptrCast(@alignCast(ctx));
        return self.inner.rawRemap(memory, alignment, new_len, ret);
    }

    fn freeFn(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret: usize) void {
        const self: *RefusingLarge = @ptrCast(@alignCast(ctx));
        self.inner.rawFree(memory, alignment, ret);
    }

    fn get(self: *RefusingLarge) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{ .alloc = allocFn, .resize = resizeFn, .remap = remapFn, .free = freeFn } };
    }
};

test "out of memory: an array that cannot be allocated raises OutOfMemoryException (the .dotnet policy)" {
    try std.testing.expect(oom_policy == .dotnet); // (tests are built in Debug)
    try std.testing.expect(oom_catchable);
    var refusing: RefusingLarge = .{ .inner = rt.allocator };
    const saved = rt.allocator;
    rt.allocator = refusing.get();
    defer rt.allocator = saved;
    try std.testing.expectError(error.Raised, arrayCreate(Array(i64), 10_000_000, 0));
    const e = take();
    defer drop(e);
    try std.testing.expect(OutOfMemoryException.is(e));
    // (a small one still is)
    const small = try arrayCreate(Array(i64), 8, 1);
    defer drop(small);
    try std.testing.expectEqual(@as(usize, 8), small.items.len);
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
    const r = new(Ref(TestList), .{ .contents = testRange(3) });
    const alias = dup(r);
    store(&alias.contents, testRange(5));
    try std.testing.expectEqual(@as(i32, 15), testSum(r.contents));
    try std.testing.expect(eql(r, alias));
    drop(head);
    drop(second);
    drop(r);
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

pub fn testPerson(id: i32) TestPerson {
    return new(TestPerson, .{ .id = id, .friend = null, .friends = .Empty, .callback = null });
}

const TestSelf = struct { self: TestPerson };

pub fn testAddId(env: ?*Env, x: i32) Raised!i32 {
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

pub fn testThreadWork(result: *i64) void {
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

test "storing a composite value with two cyclic cells does not double-count" {
    const before = thread.stats;
    const Fn = Func(*const fn (?*Env, i32) Raised!i32);
    const Pair = struct { first: Fn, second: Fn };
    const Cap = struct { box: Ref(?Pair) };
    const r = new(Ref(?Pair), .{ .contents = null });
    const f1 = closure(Fn, Cap, .{ .box = dup(r) }, struct {
        fn call(_: ?*Env, x: i32) Raised!i32 {
            return x;
        }
    }.call);
    const f2 = closure(Fn, Cap, .{ .box = dup(r) }, struct {
        fn call(_: ?*Env, x: i32) Raised!i32 {
            return x;
        }
    }.call);
    storeIn(r, "contents", .{ .first = f1, .second = f2 });
    const f2_keep = dup(r.contents.?.second);
    storeIn(r, "contents", null);
    drop(f2_keep);
    drop(r);
    _ = collect();
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
pub fn expectText(expected: []const u8, s: String) !void {
    var buf: [512]u8 = undefined;
    const n = std.unicode.wtf16LeToWtf8(&buf, unitsOf(s));
    try std.testing.expectEqualStrings(expected, buf[0..n]);
    drop(s);
}

test "strings: literals, concatenation, comparison" {
    const before = thread.stats;
    const hello = str("héllo");
    try std.testing.expectEqual(@as(i32, 5), try strLen(hello));
    try std.testing.expectEqual(@as(u16, 0xE9), try strAt(hello, 1));
    const both = strConcat(hello, str(" wörld"));
    try std.testing.expectEqual(@as(i32, 11), try strLen(both));
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
    try std.testing.expectEqual(@as(i32, 2), try strLen(str("\u{1F600}")));
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

pub fn expectFloat(expected: []const u8, comptime spec: Spec, value: anytype) !void {
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
    const P = struct { Name: String, Age: i32 };
    try std.testing.expectEqual(@as(i32, -1), compare(P{ .Name = str("a"), .Age = 2 }, P{ .Name = str("a"), .Age = 3 }));
    try std.testing.expectEqual(@as(i32, 1), compare(@as(?i32, 1), @as(?i32, null)));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(struct { i32, i32 }, .{ 1, 2 }), @as(struct { i32, i32 }, .{ 1, 3 })));
    try std.testing.expect(hash(P{ .Name = str("a"), .Age = 2 }) == hash(P{ .Name = str("a"), .Age = 2 }) and hash(@as(i32, -7)) == -7);
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
pub fn expectRaised(comptime C: type, expected: []const u8, result: anytype) !void {
    if (result) |value| {
        drop(value);
        return error.TestExpectedError;
    } else |_| {}
    const e = take();
    defer drop(e);
    try std.testing.expect(C.is(e));
    try expectText(expected, exnMessage(e));
}

test "string methods do what .NET does" {
    const before = thread.stats;
    const abc = str("abc");
    const none: String = null;
    try expectText("bc", try strSubstring(abc, 1, null));
    try expectText("b", try strSubstring(abc, 1, 1));
    try expectText("", try strSubstring(abc, 3, null));
    try expectRaised(ArgumentOutOfRangeException, "startIndex cannot be larger than length of string. (Parameter 'startIndex')", strSubstring(abc, 5, null));
    try expectRaised(ArgumentOutOfRangeException, "Index and length must refer to a location within the string. (Parameter 'length')", strSubstring(abc, 1, 5));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('-1') must be a non-negative value. (Parameter 'startIndex')\nActual value was -1.", strSubstring(abc, -1, null));
    try expectRaised(ArgumentOutOfRangeException, "length ('-1') must be a non-negative value. (Parameter 'length')\nActual value was -1.", strSubstring(abc, 2, -1));
    try expectRaised(NullReferenceException, "Object reference not set to an instance of an object.", strSubstring(none, 1, null));
    try expectRaised(NullReferenceException, "Object reference not set to an instance of an object.", strLen(none));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", strAt(abc, 5));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", strAt(abc, -1));
    try std.testing.expectEqual(@as(i32, 0), strLength(none));
    try std.testing.expectEqual(@as(i32, 2), try strIndexOfChar(abc, 'c', 0));
    try std.testing.expectEqual(@as(i32, -1), try strIndexOf(abc, str("c"), 3));
    try std.testing.expectEqual(@as(i32, 0), try strIndexOf(abc, str(""), 0));
    try std.testing.expectEqual(@as(i32, 3), try strLastIndexOf(abc, str("")));
    try std.testing.expectEqual(@as(i32, 0), try strLastIndexOfChar(abc, 'a'));
    try expectRaised(ArgumentOutOfRangeException, index_range ++ " (Parameter 'startIndex')", strIndexOf(abc, str("c"), 4));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'value')", strIndexOf(abc, none, 0));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'value')", strContains(abc, none));
    try std.testing.expect(try strContains(abc, str("bc")) and try strStartsWith(abc, str("")) and try strEndsWith(abc, str("bc")));
    try std.testing.expect(try strContainsChar(abc, 'b') and try strStartsWithChar(abc, 'a') and !try strEndsWithChar(abc, 'a'));
    try expectText("Ǆ STRAßE ΐ İI", try strCase(str("ǅ straße ΐ İi"), true));
    try expectText("ǆ strasse İi σ", try strCase(str("ǅ STRASSE İI Σ"), false));
    try expectText("x y", try strTrim(str(" \t\n\u{a0}\u{2003}x y\u{3000}\u{85} "), true, true, null));
    try expectText("a ", try strTrim(str(" a "), true, false, null));
    try expectText(" a", try strTrim(str(" a "), false, true, null));
    try expectText("a", try strTrim(str("xxaxx"), true, true, 'x'));
    try expectText("azcazc", try strReplaceChar(str("abcabc"), 'b', 'z'));
    try expectText("aa", try strReplace(str("abcabc"), str("bc"), str("")));
    try expectText("ac", try strReplace(abc, str("b"), none));
    try expectRaised(ArgumentException, "The value cannot be an empty string. (Parameter 'oldValue')", strReplace(abc, str(""), str("x")));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'oldValue')", strReplace(abc, none, str("x")));
    try expectText("aXYbc", try strInsert(abc, 1, str("XY")));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('5') must be less than or equal to '3'. (Parameter 'startIndex')\nActual value was 5.", strInsert(abc, 5, str("x")));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('4294967295') must be less than or equal to '3'. (Parameter 'startIndex')\nActual value was 4294967295.", strInsert(abc, -1, str("x")));
    try expectText("a", try strRemove(abc, 1, null));
    try expectText("ac", try strRemove(abc, 1, 1));
    try expectRaised(ArgumentOutOfRangeException, "startIndex cannot be larger than length of string. (Parameter 'startIndex')", strRemove(abc, 5, null));
    try expectRaised(ArgumentOutOfRangeException, "StartIndex cannot be less than zero. (Parameter 'startIndex')", strRemove(abc, -1, null));
    try expectRaised(ArgumentOutOfRangeException, "count ('5') must be less than or equal to '2'. (Parameter 'count')\nActual value was 5.", strRemove(abc, 1, 5));
    try expectText("  abc", try strPad(abc, true, 5, ' '));
    try expectText("abc..", try strPad(abc, false, 5, '.'));
    try expectRaised(ArgumentOutOfRangeException, "totalWidth ('-1') must be a non-negative value. (Parameter 'totalWidth')\nActual value was -1.", strPad(abc, true, -1, ' '));
    try expectText("xxx", try strOfChar('x', 3));
    try expectText("ababab", try strReplicate(3, str("ab")));
    try expectRaised(ArgumentException, "The input must be non-negative.\ncount = -1 (Parameter 'count')", strReplicate(-1, str("a")));
    try expectText("", strConcat(none, none));
    try std.testing.expect(strConcat(none, none) != null and strIsNullOrEmpty(none) and strIsNullOrWhiteSpace(str(" \t")));
    try std.testing.expect(!eql(none, str("")) and eql(none, none));
    try std.testing.expectEqual(@as(i32, -1), compare(none, str("")));
    try std.testing.expectEqual(@as(i32, 1), compare(str(""), none));
    try expectText("|     |<null>|", format(.{ arg(.{ .kind = 's' }, none), "|", arg(.{ .kind = 's', .width = 5 }, none), "|", arg(.{ .kind = 'O' }, none), "|", none }));
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "case mapping is .NET's for every code unit" {
    var upper: u32 = 0;
    var lower: u32 = 0;
    for (0..0x10000) |c| {
        upper = upper *% 31 +% unicode.toUpper(@intCast(c));
        lower = lower *% 31 +% unicode.toLower(@intCast(c));
    }
    // (the same sums over Char.ToUpperInvariant and Char.ToLowerInvariant on .NET 10)
    try std.testing.expectEqual(@as(u32, 4105874476), upper);
    try std.testing.expectEqual(@as(u32, 3480348820), lower);
}

pub fn expectNet(expected: []const u8, comptime fmt: []const u8, value: anytype) !void {
    var buf: [scratch_len]u8 = undefined;
    try std.testing.expectEqualStrings(expected, netText(fmt, value, &buf));
}

test ".NET's standard numeric formats" {
    const x: f64 = 1234.5678;
    try expectNet("1,234.57", "N2", x);
    try expectNet("1,235", "N0", x);
    try expectNet("1,234.57", "N", x);
    try expectNet("1234.6", "F1", x);
    try expectNet("1235", "F0", x);
    try expectNet("1.23E+003", "E2", x);
    try expectNet("1.234568e+003", "e", x);
    try expectNet("1234.5678", "G", x);
    try expectNet("1.23E+03", "G3", x);
    try expectNet("1.2e+03", "g2", x);
    try expectNet("1234.5678", "R", x);
    try expectNet("123,456.8 %", "P1", x);
    try expectNet("123,456.78 %", "P", x);
    try expectNet("\xA41,234.57", "C", x);
    try expectNet("(\xA41,234.57)", "C", -x);
    try expectNet("-123,456.78 %", "P", -x);
    try expectNet("1E+03", "G1", x);
    try expectNet("1234.5678", "G10", x);
    try expectNet("42", "D", @as(i32, 42));
    try expectNet("00042", "D5", @as(i32, 42));
    try expectNet("2A", "X", @as(i32, 42));
    try expectNet("002a", "x4", @as(i32, 42));
    try expectNet("42.00", "N2", @as(i32, 42));
    try expectNet("4.20E+001", "E2", @as(i32, 42));
    try expectNet("4,200 %", "P0", @as(i32, 42));
    try expectNet("\xA442.00", "C", @as(i32, 42));
    try expectNet("00101010", "B8", @as(i32, 42));
    try expectNet("-0001234567", "D10", @as(i32, -1234567));
    try expectNet("FFED2979", "X", @as(i32, -1234567));
    try expectNet("-1,234,567.0", "N1", @as(i32, -1234567));
    try expectNet("(\xA41,234,567.00)", "C", @as(i32, -1234567));
    try expectNet("-123,456,700 %", "P0", @as(i32, -1234567));
    try expectNet("-1.235E+006", "E3", @as(i32, -1234567));
    try expectNet("-1.235E+06", "G4", @as(i32, -1234567));
    try expectNet("1,234,567,890,123", "N0", @as(i64, 1234567890123));
    try expectNet("FF", "X", @as(i8, -1));
    try expectNet("ffffffffffffffff", "x", @as(i64, -1));
    try expectNet("00065535", "D8", @as(u16, 65535));
    try expectNet("0", "N0", @as(i32, 0));
    try expectNet("0.00E+000", "E2", @as(i32, 0));
    try expectNet("1.23E+04", "G3", @as(i32, 12345));
    try expectNet("12345", "G", @as(i32, 12345));
    try expectNet("1.2E+04", "G2", @as(i64, 12345));
    try expectNet("0.00", "N2", @as(f64, 0.0));
    try expectNet("-0", "N0", @as(f64, -0.5));
    try expectNet("-0.0", "F1", @as(f64, -0.0));
    try expectNet("0.12", "F2", @as(f64, 0.125));
    try expectNet("2.67", "F2", @as(f64, 2.675));
    try expectNet("2", "F0", @as(f64, 2.5));
    try expectNet("2", "N0", @as(f64, 1.5));
    try expectNet("100,000,000,000,000,000,000", "N0", @as(f64, 1e20));
    try expectNet("1E+008", "E0", @as(f64, 123456789.0));
    try expectNet("0.00012", "G2", @as(f64, 0.000123));
    try expectNet("1000000000000000", "G", @as(f64, 1e15));
    try expectNet("1E-05", "G", @as(f64, 1e-5));
    try expectNet("1.2345678901234568E+17", "G", @as(f64, 123456789012345678.0));
    try expectNet("1E+02", "G2", @as(f64, 100.0));
    try expectNet("0.10000000000000001", "G17", @as(f64, 0.1));
    try expectNet("NaN", "N2", std.math.nan(f64));
    try expectNet("-Infinity", "E2", -std.math.inf(f64));
    try expectNet("0.100", "F3", @as(f32, 0.1));
    try expectNet("0.1", "G", @as(f32, 0.1));
    try expectNet("0.1000000015", "N10", @as(f32, 0.1));
    try expectText("   42|42   |     1,234.6", format(.{
        arg(.{ .width = 5 }, @as(i32, 42)), "|", arg(.{ .width = 5, .left = true }, @as(i32, 42)), "|", arg(.{ .width = 12, .net = "N1" }, x),
    }));
}

pub fn run(comptime c: u8, comptime n: usize) *const [n]u8 {
    return &@as([n]u8, @splat(c));
}

const ShowPerson = struct { Name: String, Age: i32 };
const ShowShape = union(enum) {
    A,
    B: struct { Item: i32 },
    C: struct { Item1: String, Item2: i32 },
    D: struct { Item: ShowPerson },
    F: struct { Item: struct { i32, i32 } },
};
const ShowTree = union(enum) {
    Leaf,
    Node: *struct { @"$rc": u32 = 1, Item1: ShowTree, Item2: i32, Item3: ShowTree },
};
const ShowRing = *struct { @"$rc": u32 = 1, Count: i32, Next: ?ShowRing };
const ShowErr = ExnOf("MyErr", struct { Data0: i32, Data1: String });

pub fn testList(comptime T: type, items: []const T) List(T) {
    var all: List(T) = .Empty;
    var i = items.len;
    while (i > 0) {
        i -= 1;
        const tail = all;
        all = .{ .Cons = cell(List(T), .Cons, .{ .Head = dup(items[i]), .Tail = tail }) };
    }
    return all;
}

pub fn expectAny(expected: []const u8, x: anytype) !void {
    try expectText(expected, anyText(x));
}

test "%A writes what F# writes" {
    const before = thread.stats;
    try expectAny("1", @as(i32, 1));
    try expectAny("1uy", @as(u8, 1));
    try expectAny("-1y", @as(i8, -1));
    try expectAny("1L", @as(i64, 1));
    try expectAny("1UL", @as(u64, 1));
    try expectAny("1.0", @as(f64, 1.0));
    try expectAny("-0.0", @as(f64, -0.0));
    try expectAny("1e+20", @as(f64, 1e20));
    try expectAny("1e-05", @as(f64, 1e-5));
    try expectAny("123456789.1", @as(f64, 123456789.123456789));
    try expectAny("1.23456789e+12", @as(f64, 1234567890123.0));
    try expectAny("1.0f", @as(f32, 1.0));
    try expectAny("1.5f", @as(f32, 1.5));
    try expectAny("1e+10f", @as(f32, 1e10));
    try expectAny("nan", std.math.nan(f64));
    try expectAny("nanf", std.math.nan(f32));
    try expectAny("-infinity", -std.math.inf(f64));
    try expectAny("'a'", @as(u16, 'a'));
    try expectAny("'\\010'", @as(u16, '\n'));
    try expectAny("'\\''", @as(u16, '\''));
    try expectAny("'\"'", @as(u16, '"'));
    try expectAny("'\\\\'", @as(u16, '\\'));
    try expectAny("'\\000'", @as(u16, 0));
    try expectAny("\"q\"uote\"", str("q\"uote"));
    try expectAny("<null>", @as(String, null));
    try expectAny("()", {});
    try expectAny("(1, \"a\")", @as(struct { i32, String }, .{ 1, str("a") }));
    try expectAny("Some 1", @as(?i32, 1));
    try expectAny("None", @as(?i32, null));
    try expectAny("Some (Some 1)", @as(??i32, @as(?i32, 1)));
    try expectAny("Some None", @as(??i32, @as(?i32, null)));
    try expectAny("Some (1, 2)", @as(?struct { i32, i32 }, .{ 1, 2 }));
    try expectAny("Some -1", @as(?i32, -1));
    try expectAny("A", @as(ShowShape, .A));
    try expectAny("B 1", @as(ShowShape, .{ .B = .{ .Item = 1 } }));
    try expectAny("C (\"x\", 2)", @as(ShowShape, .{ .C = .{ .Item1 = str("x"), .Item2 = 2 } }));
    try expectAny("F (1, 2)", @as(ShowShape, .{ .F = .{ .Item = .{ 1, 2 } } }));
    try expectAny("Some A", @as(?ShowShape, .A));
    try expectAny("Some (B 1)", @as(?ShowShape, .{ .B = .{ .Item = 1 } }));
    const ann: ShowPerson = .{ .Name = str("Ann"), .Age = 3 };
    try expectAny("{ Name = \"Ann\"\n  Age = 3 }", ann);
    try expectAny("D { Name = \"Ann\"\n    Age = 3 }", @as(ShowShape, .{ .D = .{ .Item = ann } }));
    try expectAny("{ Name = null\n  Age = 3 }", @as(ShowPerson, .{ .Name = null, .Age = 3 }));
    try expectAny(
        "{ Inner = { Name = \"Ann\"\n            Age = 3 }\n  Opt = Some 1 }",
        @as(struct { Inner: ShowPerson, Opt: ?i32 }, .{ .Inner = ann, .Opt = 1 }),
    );

    const three = testList(i32, &.{ 1, 2, 3 });
    try expectAny("[1; 2; 3]", three);
    try expectAny("Some [1; 2; 3]", @as(?List(i32), three));
    drop(three);
    try expectAny("[]", @as(List(i32), .Empty));
    var numbers: [120]i32 = undefined;
    for (&numbers, 1..) |*n, i| n.* = @intCast(i);
    const forty = testList(i32, numbers[0..40]);
    try expectAny(
        "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22;\n" ++
            " 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40]",
        forty,
    );
    drop(forty);
    const many = testList(i32, &numbers);
    try expectAny(
        "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22;\n" ++
            " 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42;\n" ++
            " 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62;\n" ++
            " 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82;\n" ++
            " 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; ...]",
        many,
    );
    drop(many);
    const people = testList(ShowPerson, &.{ ann, .{ .Name = str("Bob"), .Age = 4 } });
    try expectAny("[{ Name = \"Ann\"\n   Age = 3 }; { Name = \"Bob\"\n                Age = 4 }]", people);
    drop(people);

    const z80 = str(run('z', 80));
    try expectAny("C (\"" ++ run('z', 80) ++ "\",\n   1)", @as(ShowShape, .{ .C = .{ .Item1 = z80, .Item2 = 1 } }));
    try expectAny("Some\n  \"" ++ run('z', 80) ++ "\"", @as(?String, z80));
    try expectAny(
        "(\"" ++ run('z', 70) ++ "\",\n \"" ++ run('w', 70) ++ "\")",
        @as(struct { String, String }, .{ str(run('z', 70)), str(run('w', 70)) }),
    );

    const leafT: ShowTree = .Leaf;
    const node = struct {
        pub fn of(l: ShowTree, v: i32, r: ShowTree) ShowTree {
            return .{ .Node = cell(ShowTree, .Node, .{ .Item1 = l, .Item2 = v, .Item3 = r }) };
        }
    }.of;
    const small = node(node(leafT, 1, leafT), 2, node(leafT, 3, leafT));
    try expectAny("Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))", small);
    drop(small);
    const big = node(
        node(node(node(leafT, 1111111111, leafT), 222222222, leafT), 333333333, node(leafT, 444444444, leafT)),
        555555555,
        node(leafT, 666666666, node(leafT, 777777777, leafT)),
    );
    try expectAny(
        "Node\n  (Node\n     (Node (Node (Leaf, 1111111111, Leaf), 222222222, Leaf), 333333333,\n" ++
            "      Node (Leaf, 444444444, Leaf)), 555555555,\n   Node (Leaf, 666666666, Node (Leaf, 777777777, Leaf)))",
        big,
    );
    drop(big);

    // a record that contains itself
    const first = new(ShowRing, .{ .Count = 1, .Next = null });
    const second = new(ShowRing, .{ .Count = 2, .Next = first });
    first.Next = second;
    try expectAny("{ Count = 1\n  Next = Some { Count = 2\n                Next = Some ... } }", first);
    first.Next = null;
    drop(second);

    // an F# exception: `%A`, and its message
    const e = ShowErr.new(.{ .Data0 = 1, .Data1 = str("a") });
    try expectAny("MyErr (1, \"a\")", e);
    try expectText("MyErr (1, \"a\")", exnMessage(e));
    try expectText("x=MyErr (1, \"a\")!", format(.{ "x=", arg(.{ .kind = 'A' }, e), "!" }));
    drop(e);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "exception classes derive as on .NET, division raises" {
    const e = ArgumentNullException.new(.{ .Message = str("no") });
    try std.testing.expect(ArgumentNullException.is(e) and ArgumentException.is(e) and SystemException.is(e));
    try std.testing.expect(!ArgumentOutOfRangeException.is(e) and !Failure.is(e) and !ArithmeticException.is(e));
    drop(e);
    try std.testing.expectEqual(@as(i32, -3), try div(i32, 7, -2));
    try std.testing.expectEqual(@as(i32, 1), try rem(i32, 7, -2));
    try std.testing.expectEqual(@as(i8, -128), try div(i8, -128, -1));
    try std.testing.expectEqual(@as(i8, 0), try rem(i8, -128, -1));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", div(i32, 5, 0));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", rem(u8, 5, 0));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", div(i32, std.math.minInt(i32), -1));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", rem(i64, std.math.minInt(i64), -1));
}

test "arrays: identity, items, what they raise" {
    const before = thread.stats;
    const A = Array(String);
    const bc = strConcat(str("b"), str("c"));
    const a = arrayOf(A, .{ str("a"), bc, str("d") });
    drop(bc);
    try std.testing.expectEqual(@as(i32, 3), arrayLen(a));
    try expectText("bc", try arrayGet(a, 1));
    const made = strConcat(str("x"), str("y"));
    try arraySet(a, 0, made);
    drop(made);
    try expectText("xy", try arrayGet(a, 0));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", arrayGet(a, 3));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", arraySet(a, -1, str("z")));
    const copy = arrayCopy(a);
    try std.testing.expect(eql(a, copy) and a != copy);
    try expectAny("[|\"xy\"; \"bc\"; \"d\"|]", a);
    const part = arraySlice(a, 1, 5);
    try expectAny("[|\"bc\"; \"d\"|]", part);
    const none = arraySlice(a, 2, 1);
    try expectAny("[||]", none);
    try expectRaised(ArgumentOutOfRangeException, "The index is outside the legal range.\ncount = 5, array.Length = 3 (Parameter 'count')", arraySub(a, 1, 5));
    const zeros = try arrayZero(Array(?i32), 2);
    try expectAny("[|None; None|]", zeros);
    try expectRaised(ArgumentException, "The input must be non-negative.\ncount = -1 (Parameter 'count')", arrayZero(Array(i32), -1));
    const list = arrayToList(a);
    const back = arrayOfList(A, list);
    try std.testing.expect(eql(a, back));
    for ([_]A{ a, copy, part, none, back }) |x| drop(x);
    drop(zeros);
    drop(list);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "numbers: what .NET raises and returns" {
    try std.testing.expectEqual(@as(i32, 5), try absOf(@as(i32, -5)));
    try expectRaised(OverflowException, "Negating the minimum value of a twos complement number is invalid.", absOf(@as(i32, std.math.minInt(i32))));
    try expectRaised(ArithmeticException, "Function does not accept floating point Not-a-Number values.", signOf(std.math.nan(f64)));
    try std.testing.expectEqual(@as(i32, 1024), pown(@as(i32, 2), 10));
    try std.testing.expectEqual(@as(f64, 0.25), pown(@as(f64, 2), -2));
    try std.testing.expectEqual(@as(f64, 2), roundEven(@as(f64, 2.5)));
    try std.testing.expectEqual(@as(f64, 4), roundEven(@as(f64, 3.5)));
    try std.testing.expectEqual(@as(f64, -2), roundEven(@as(f64, -2.5)));
    try std.testing.expectEqual(@as(f64, 2.57), try roundTo(@as(f64, 2.567), 2));
    try std.testing.expectEqual(@as(i32, -7), try parseIntFs(i32, str(" -7 ")));
    try std.testing.expectEqual(@as(i32, 31), try parseIntFs(i32, str("0x1F")));
    try std.testing.expectEqual(@as(i32, 5), try parseIntFs(i32, str("0b101")));
    try std.testing.expectEqual(@as(i32, 10), try parseIntFs(i32, str("1_0")));
    try std.testing.expectEqual(@as(i64, 9223372036854775807), try parseIntFs(i64, str("9223372036854775807")));
    try expectRaised(FormatException, "The input string '4x' was not in a correct format.", parseIntFs(i32, str("4x")));
    try expectRaised(FormatException, "Input string was not in a correct format.", parseIntFs(i32, str("")));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", parseIntFs(i32, str("99999999999")));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", parseIntFs(u8, str("256")));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", parseIntFs(i16, str("40000")));
    try expectRaised(OverflowException, "Value was either too large or too small for a UInt32.", parseIntFs(u16, str("-1")));
    try expectRaised(FormatException, "The input string '0x1F' was not in a correct format.", parseInt(i32, str("0x1F")));
    try expectRaised(OverflowException, "Value was either too large or too small for an unsigned byte.", parseInt(u8, str("300")));
    try std.testing.expectEqual(@as(?i32, 12), tryParseInt(i32, str("12")));
    try std.testing.expectEqual(@as(?i32, null), tryParseInt(i32, str("x")));
    try std.testing.expectEqual(@as(f64, 1000), try parseFloat(f64, str(" 1e3 ")));
    try std.testing.expectEqual(@as(f64, 0.5), try parseFloat(f64, str(".5")));
    try std.testing.expect(std.math.isNan(try parseFloat(f64, str("NaN"))));
    try std.testing.expectEqual(-std.math.inf(f64), try parseFloat(f64, str("-Infinity")));
    try expectRaised(FormatException, "The input string 'abc' was not in a correct format.", parseFloat(f64, str("abc")));
    try expectRaised(FormatException, "The input string 'inf' was not in a correct format.", parseFloat(f64, str("inf")));
    try std.testing.expect(try parseBool(str("True")) and !try parseBool(str("false")));
}

test ".NET's collections: ResizeArray, Dictionary, HashSet" {
    const before = thread.stats;
    const R = ResizeArray(i32);
    const r = raOfList(R, listOf(i32, &.{ 3, 1, 2 }));
    defer drop(r);
    raAdd(r, 5);
    try expectAny("seq [3; 1; 2; 5]", r);
    try expectRaised(ArgumentOutOfRangeException, "Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')", raGet(r, 9));
    try expectRaised(ArgumentOutOfRangeException, "Index must be within the bounds of the List. (Parameter 'index')", raInsert(r, 9, 1));
    try raInsert(r, 0, 9);
    try raRemoveAt(r, 1);
    raSort(r);
    try expectAny("seq [1; 2; 5; 9]", r);
    try std.testing.expect(!raContains(r, 3) and raIndexOf(r, 5) == 2 and !raRemove(r, 3));
    const D = Dictionary(i32, String);
    const d = htNew(D);
    defer drop(d);
    try dictAdd(d, 2, str("b"));
    try dictAdd(d, 1, str("a"));
    try dictSet(d, 3, str("c"));
    try dictSet(d, 2, str("B"));
    try expectAny("seq [[2, B]; [1, a]; [3, c]]", d);
    try expectRaised(ArgumentException, "An item with the same key has already been added. Key: 1", dictAdd(d, 1, str("x")));
    try expectRaised(KeyNotFoundException, "The given key '9' was not present in the dictionary.", dictGet(d, 9));
    try std.testing.expect(try htRemove(d, 2));
    try dictSet(d, 7, str("g"));
    try expectAny("seq [[7, g]; [1, a]; [3, c]]", d);
    try std.testing.expectEqual(@as(i32, 3), htCount(d));
    const h = setOfList(HashSet(i32), listOf(i32, &.{ 3, 1, 3 }));
    defer drop(h);
    try std.testing.expect(setAdd(h, 4) and !setAdd(h, 1));
    try expectAny("seq [3; 1; 4]", h);
    for (0..1000) |i| try dictSet(d, @intCast(i), str("n"));
    try std.testing.expectEqual(@as(i32, 1000), htCount(d));
    _ = before;
}

test ".NET's ToString, Split, StringBuilder, categories" {
    try expectText("Some(1)|(1, a)|[1; 2; 3; ... ]|[a]", format(.{
        toText(@as(?i32, 1)), "|", toText(@as(struct { i32, String }, .{ 1, str("a") })), "|", toText(listOf(i32, &.{ 1, 2, 3, 4 })), "|", toText(listOf(String, &.{str("a")})),
    }));
    try expectAny("[|\"a\"; \"b\"; \"\"; \"c\"|]", try strSplitChars(str("a,b,,c"), &.{','}, std.math.maxInt(i32), 0));
    try expectAny("[|\"a\"; \"b\"|]", try strSplitChars(str("a,,b"), &.{','}, std.math.maxInt(i32), 1));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitString(str("a--b--c"), str("--"), std.math.maxInt(i32), 0));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitChars(str("a b\tc"), &.{}, std.math.maxInt(i32), 0));
    const sb = sbNew(str(""));
    drop(sbAppend(sb, str("a")));
    drop(sbAppend(sb, @as(i32, 1)));
    drop(sbAppend(sb, @as(u16, 'c')));
    drop(sbAppend(sb, @as(f64, 2.5)));
    drop(sbAppend(sb, true));
    try expectText("a1c2.5True", sbToString(sb));
    drop(sb);
    var sum: u32 = 0;
    for (0..0x10000) |c| sum = sum *% 31 +% @backingInt(unicode.category(@intCast(c)));
    // (the same sum over Char.GetUnicodeCategory on .NET 10)
    try std.testing.expectEqual(@as(u32, 3966132137), sum);
    try std.testing.expect(strEqualsIgnoreCase(str("abc"), str("ABC")) and strCompareIgnoreCase(str("a"), str("A")) == 0);
    try std.testing.expectEqual(@as(f64, 7), charNumericValue('7'));
}

test "weak references see their target go" {
    const before = thread.stats;
    const R = *struct { @"$rc": u32 = 1, value: i32 };
    const a = new(R, .{ .value = 7 });
    const w = try weakNew(Weak(R), a);
    const w2 = try weakNew(Weak(R), a);
    const got = weakTryGet(w).?;
    try std.testing.expectEqual(@as(i32, 7), got.value);
    drop(got);
    drop(a);
    try std.testing.expect(weakTryGet(w) == null and weakTryGet(w2) == null);
    const b = new(R, .{ .value = 8 });
    try weakSet(w, b);
    try std.testing.expectEqual(@as(i32, 8), weakTryGet(w).?.value);
    drop(b);
    drop(b);
    drop(w);
    drop(w2);
    try std.testing.expectEqual(@as(usize, 0), thread.weak.count());
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "objects: parts, virtual members, type tests, cycles" {
    const before = thread.stats;
    const Shape = struct {
        const Part = struct { name: String };
        const Chain = struct { own: Part };
        const VT = struct { area: *const fn (Obj) f64 };
        const ty: ObjType = objType(Chain, "Probe+Shape", null, &.{null}, null);
        pub fn name(o: Obj) String {
            return objPart(*Part, &.{Part}, o).name;
        }
    };
    const Circle = struct {
        const Part = struct { r: f64, next: ?Obj };
        const Chain = struct { base: Shape.Chain, own: Part };
        pub fn area(o: Obj) f64 {
            const r = objPart(*Part, &.{ Shape.Part, Part }, o).r;
            return 3 * r * r;
        }
        const vt: Shape.VT = .{ .area = area };
        const ty: ObjType = objType(Chain, "Probe+Circle", &Shape.ty, &.{ @ptrCast(&vt), null }, null);
    };
    const chain: Circle.Chain = .{ .base = .{ .own = .{ .name = str("circle") } }, .own = .{ .r = 2, .next = null } };
    const c = objNew(&Circle.ty, chain);
    drop(chain);
    try expectText("circle", dup(Shape.name(c)));
    try std.testing.expectEqual(@as(f64, 12), objVt(*const Shape.VT, c, 0).area(c));
    try std.testing.expect(objIs(c, &Shape.ty) and objIs(c, &Circle.ty));
    const s = try objCast(c, &Shape.ty);
    drop(s);
    try expectText("Probe+Circle", anyText(c));
    // (a cycle through an object field: freed by the collector when functions can be in cycles)
    objStore(c, &objPart(*Circle.Part, &.{ Shape.Part, Circle.Part }, c).next, dup(c));
    drop(c);
    _ = collect();
    _ = before;
}

test "equality of a long list does not use the stack" {
    var a: List(i32) = .Empty;
    var b: List(i32) = .Empty;
    for (0..1_000_000) |i| {
        const na = cell(List(i32), .Cons, .{ .Head = @as(i32, @intCast(i)), .Tail = a });
        a = .{ .Cons = na };
        const nb = cell(List(i32), .Cons, .{ .Head = @as(i32, @intCast(i)), .Tail = b });
        b = .{ .Cons = nb };
    }
    try std.testing.expect(eql(a, b));
    const c: List(i32) = .{ .Cons = cell(List(i32), .Cons, .{ .Head = 7, .Tail = b }) };
    try std.testing.expect(!eql(a, c));
    drop(a);
    drop(c);
}

test "decimal does what .NET does" {
    const D = struct {
        pub fn p(comptime text: []const u8) NetDecimal {
            return decParse(str(text), true) catch unreachable;
        }
        pub fn is(expected: []const u8, d: NetDecimal) !void {
            var buf: [40]u8 = undefined;
            try std.testing.expectEqualStrings(expected, decAscii(d, &buf));
        }
    };
    const p = D.p;
    try D.is("1.10", p("1.10"));
    try D.is("0.3333333333333333333333333333", try decDiv(p("1"), p("3")));
    try D.is("0.6666666666666666666666666667", try decDiv(p("2"), p("3")));
    try D.is("0.25", try decDiv(p("1"), p("4")));
    try D.is("5", try decDiv(p("10"), p("2")));
    try D.is("1.00", try decDiv(p("1.00"), p("1")));
    try D.is("1.0000", try decMul(p("1.000"), p("1.0")));
    try D.is("0.30", try decAdd(p("0.1"), p("0.20")));
    try D.is("0.0000000000000000000000000000", try decMul(p("1e-28"), p("0.5")));
    try D.is("0.0000000000000000000000000002", try decMul(p("3e-28"), p("0.5")));
    try D.is("33.333333333333333333333333333", try decDiv(p("100"), p("3")));
    try D.is("0.1428571428571428571428571429", try decDiv(p("1"), p("7")));
    try D.is("10.000", try decSub(p("12.345"), p("2.345")));
    try D.is("1", try decRem(p("7"), p("3")));
    try D.is("-1.5", try decRem(p("-7.5"), p("2")));
    try D.is("1.358024679135802467913580237", try decMul(p("1.23456789012345678901234567"), p("1.1")));
    try D.is("20", try decDiv(p("10"), p("0.5")));
    try D.is("0.125", try decDiv(p("1"), p("8")));
    try D.is("2.00", try decDiv(p("4.00"), p("2")));
    try D.is("2.5", try decDiv(p("5"), p("2.0")));
    try D.is("0", try decDiv(p("0"), p("5.00")));
    try D.is("1.0000000000000000000000000001", try decAdd(p("1e-28"), p("1")));
    try D.is("79228162514264337593543950334", try decSub(p("79228162514264337593543950335"), p("0.5")));
    try D.is("79228162514264337593543950334", try decAdd(p("79228162514264337593543950334"), p("0.5")));
    try D.is("79.22816251426433759354395030", try decMul(p("7.92281625142643375935439503"), p("10")));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decAdd(p("79228162514264337593543950335"), p("1")));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", decDiv(p("1"), p("0")));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", decToInt(i32, p("1e20")));
    try expectRaised(OverflowException, "Value was either too large or too small for an unsigned byte.", decToInt(u8, p("300")));
    try D.is("0.1", try decOf(@as(f64, 0.1)));
    try D.is("0.333333333333333", try decOf(@as(f64, 1.0 / 3.0)));
    try D.is("123456789.123457", try decOf(@as(f64, 123456789.123456789)));
    try D.is("0", try decOf(@as(f64, 1e-30)));
    try D.is("2.5", try decOf(@as(f32, 2.5)));
    try D.is("10000000000000000000000000000", try decOf(@as(f64, 1e28)));
    try D.is("0.0000000000000000000123456789", try decOf(@as(f64, 1.23456789e-20)));
    try D.is("-1234567890123460000", try decOf(@as(f64, -1234567890123456789.0)));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decOf(@as(f64, 1e29)));
    try std.testing.expectEqual(@as(i32, -2), try decToInt(i32, p("-2.7")));
    try std.testing.expectEqual(@as(f64, 1.1), decToFloat(f64, p("1.1")));
    try std.testing.expectEqual(@as(f64, 7.922816251426434e28), decToFloat(f64, p("79228162514264337593543950335")));
    try D.is("2", decRound(p("2.5"), 0, true));
    try D.is("-2", decRound(p("-2.5"), 0, true));
    try D.is("3", decRound(p("2.5"), 0, false));
    try D.is("2.34", decRound(p("2.345"), 2, true));
    try D.is("1.00", decRound(p("1.005"), 2, true));
    try D.is("-2", decWhole(p("-1.5"), .down));
    try D.is("2", decWhole(p("1.2"), .up));
    try D.is("-1", decWhole(p("-1.7"), .toward_zero));
    try std.testing.expect(eql(p("1.0"), p("1.00")) and compare(p("2"), p("10")) == -1 and hash(p("1.0")) == hash(p("1.00")));
    try D.is("1000.5", try decParse(str("1,000.5"), false));
    try expectRaised(FormatException, "The input string '1e3' was not in a correct format.", decParse(str("1e3"), false));
    try D.is("1000", p("1e3"));
    try D.is("0.1234567890123456789012345679", p("0.123456789012345678901234567890123"));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decParse(str("99999999999999999999999999999"), false));
    try expectRaised(FormatException, "The input string '1.5x' was not in a correct format.", decParse(str("1.5x"), false));
    try D.is("0.000", p("-0.000"));
    try expectText("2.35|1,234.50|1.500000|1.57|1.5|1.10|  2.25|1.10M", format(.{ arg(.{ .net = "F2" }, p("2.345")), "|", arg(.{ .net = "N2" }, p("1234.5")), "|", arg(.{ .kind = 'f' }, p("1.5")), "|", arg(.{ .kind = 'f', .precision = 2 }, p("1.567")), "|", arg(.{ .kind = 'g' }, p("1.5")), "|", p("1.10"), "|", arg(.{ .kind = 'M', .width = 6 }, p("2.25")), "|", anyText(p("1.10")) }));
}

test "bigint does what .NET does" {
    const before = thread.stats;
    const a = bigLit("123456789012345678901234567890");
    defer drop(a);
    const sq = bigMul(a, a);
    defer drop(sq);
    try expectText("15241578753238836750495351562536198787501905199875019052100", bigText(sq));
    const seven = bigOf(@as(i32, 7));
    defer drop(seven);
    const q = try bigDivRem(a, seven, true);
    defer drop(q);
    try expectText("17636684144620811271604938270", bigText(q));
    const na = bigNeg(a);
    defer drop(na);
    const nq = try bigDivRem(na, seven, true);
    defer drop(nq);
    try expectText("-17636684144620811271604938270", bigText(nq));
    const two = bigOf(@as(i32, 2));
    defer drop(two);
    const p = try bigPow(two, 100);
    defer drop(p);
    try expectText("1267650600228229401496703205376", bigText(p));
    const zero = bigOf(@as(i32, 0));
    defer drop(zero);
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", bigDivRem(a, zero, true));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", bigToInt(i32, a));
    try expectRaised(FormatException, "The value could not be parsed.", bigParse(str("12x")));
    const parsed = try bigParse(str(" -123 "));
    defer drop(parsed);
    try expectText("-123", bigText(parsed));
    try std.testing.expect(compare(a, seven) == 1 and eql(a, a) and !eql(a, seven));
    try std.testing.expectEqual(@as(i32, 42), try bigToInt(i32, bigOf(@as(i32, 42))));
    try std.testing.expectEqual(@as(f64, 1.2345678901234568e29), bigToFloat(f64, a));
    try expectText("a=123456789012345678901234567890", format(.{ "a=", a }));
    _ = before;
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

test "box" {
    const a = box(@as(i32, 5));
    const b = box(@as(i32, 5));
    const c = box(str("x"));
    defer drop(a);
    defer drop(b);
    defer drop(c);
    try std.testing.expect(eql(a, b));
    try std.testing.expect(!eql(a, c));
    try std.testing.expect(!refEql(a, b));
    try std.testing.expect(isType(i32, a));
    try std.testing.expect(!isType(i64, a));
    try std.testing.expectEqual(@as(i32, 5), try unbox(i32, a));
    try std.testing.expectEqual(hash(@as(i32, 5)), hash(a));
    try std.testing.expectEqual(@as(i32, 0), compare(a, b));
    try std.testing.expectError(error.Raised, unbox(i64, a));
    drop(take());
    const t = try anyToString(c, false);
    defer drop(t);
    try std.testing.expect(strEql(t, str("x")));
    try std.testing.expect(box(@as(String, null)) == null);
    try std.testing.expect(box({}) == null);
    try std.testing.expect(isType(void, null));
    try std.testing.expect(!isType(void, a));
    try std.testing.expect(tryUnbox(?void, null) != null);
    try std.testing.expect(tryUnbox(?void, a) == null);
    try std.testing.expectEqual({}, try unbox(void, box({})));
    try std.testing.expectError(error.Raised, unbox(void, a));
    drop(take());
}

test "Random(seed) gives .NET's numbers" {
    const r = randomNew(1234);
    defer drop(r);
    // (what `Random(1234)` gives on .NET: Next(), Next(100), Next(1000, 10000), NextDouble())
    try std.testing.expectEqual(@as(i32, 857019877), randomNext(r));
    try std.testing.expectEqual(@as(i32, 89), try randomNextMax(r, 100));
    try std.testing.expectEqual(@as(i32, 3872), try randomNextRange(r, 1000, 10000));
    try std.testing.expectEqual(@as(f64, 0.9467375338760845), randomNextDouble(r));
    const b = arrayFrom(Array(u8), rt.allocator.alloc(u8, 6) catch unreachable);
    defer drop(b);
    const r2 = randomNew(5432);
    defer drop(r2);
    randomNextBytes(r2, b);
    try std.testing.expectEqualSlices(u8, &.{ 152, 238, 227, 30, 153, 56 }, b.items);
    const r3 = randomNew(-7);
    defer drop(r3);
    try std.testing.expectEqual(@as(i32, 766440938), try randomNextRange(r3, -2000000000, 2000000000));
    try std.testing.expectEqual(@as(i32, 1419354884), randomNext(r3));
}

test "TypeShape formats voption, struct tuple, u16_num, and recursive unions" {
    const vopt_int: TypeShape = .{ .nodes = &.{.{ .kind = .vopt, .a = ShowNode.auto }} };
    try expectText("ValueSome 42", anyTextShape(vopt_int, @as(?i32, 42)));
    try expectText("ValueNone", anyTextShape(vopt_int, @as(?i32, null)));
    try expectText("42", toTextShape(vopt_int, @as(?i32, 42)));
    try expectText("ValueNone", toTextShape(vopt_int, @as(?i32, null)));

    const vopt_st_num: TypeShape = .{
        .nodes = &.{
            .{ .kind = .vopt, .a = 1 },
            .{ .kind = .struct_tuple, .a = 0, .b = 2 },
            .{ .kind = .u16_num },
        },
        .refs = &.{ ShowNode.auto, 2 },
    };
    const p1: ?struct { i32, c_ushort } = .{ 7, 16 };
    try expectText("ValueSome struct (7, 16us)", anyTextShape(vopt_st_num, p1));
    try expectText("(7, 16)", toTextShape(vopt_st_num, p1));

    const Tree = union(enum) {
        Leaf: struct { Value: ?c_ushort },
        Pair: struct { Left: struct { ?i32, bool }, Right: void },
    };
    const tree_shape: TypeShape = .{
        .nodes = &.{
            .{ .kind = .@"union", .a = 0, .b = 2 },
            .{ .kind = .record, .a = 2, .b = 1 },
            .{ .kind = .vopt, .a = 3 },
            .{ .kind = .u16_num },
            .{ .kind = .record, .a = 3, .b = 2 },
            .{ .kind = .struct_tuple, .a = 5, .b = 2 },
        },
        .refs = &.{ 1, 4, 2, 5, ShowNode.auto, ShowNode.auto, ShowNode.auto },
    };
    const t1: Tree = .{ .Leaf = .{ .Value = 65 } };
    const t2: Tree = .{ .Pair = .{ .Left = .{ 9, true }, .Right = {} } };
    const t3: Tree = .{ .Leaf = .{ .Value = null } };
    try expectText("Leaf (ValueSome 65us)", anyTextShape(tree_shape, t1));
    try expectText("Leaf ValueNone", anyTextShape(tree_shape, t3));
    try expectText("Pair (struct (Some 9, true), ())", anyTextShape(tree_shape, t2));
}

test "managed span operations maintain reference counts" {
    const start_stats = thread.stats;
    {
        const arr = arrays.arrayOf(Array(String), .{ str("a"), str("b"), str("c") });
        defer drop(arr);
        const sp = arr.items;

        const dyn1 = strConcat(str("d"), str("1"));
        defer drop(dyn1);
        try spanSet(sp, 1, dyn1);
        try std.testing.expect(strEql(sp[1], str("d1")));

        const dyn2 = strConcat(str("f"), str("2"));
        defer drop(dyn2);
        spanFill(sp[0..2], dyn2);
        try std.testing.expect(strEql(sp[0], str("f2")));
        try std.testing.expect(strEql(sp[1], str("f2")));
        try std.testing.expect(strEql(sp[2], str("c")));

        const copied = spanToArray(Array(String), sp[1..]);
        defer drop(copied);
        try std.testing.expectEqual(@as(usize, 2), copied.items.len);
        try std.testing.expect(strEql(copied.items[0], str("f2")));
        try std.testing.expect(strEql(copied.items[1], str("c")));

        // Overlapping forward & backward CopyTo
        const s_hi = strConcat(str("h"), str("i"));
        defer drop(s_hi);
        try spanSet(sp, 0, s_hi);
        try spanCopyTo(sp[0..2], sp[1..3]);
        try std.testing.expect(strEql(sp[0], str("hi")));
        try std.testing.expect(strEql(sp[1], str("hi")));
        try std.testing.expect(strEql(sp[2], str("f2")));

        try spanClear(sp);
        try std.testing.expect(sp[0] == null and sp[1] == null and sp[2] == null);
    }
    try std.testing.expectEqual(start_stats.allocs - start_stats.frees, thread.stats.allocs - thread.stats.frees);
}

test "culture string comparison matches .NET InvariantCulture weights" {
    try std.testing.expectEqual(@as(i32, 1), try strCompareTo(str("ABC"), str("abc")));
    try std.testing.expectEqual(@as(i32, -1), try strCompareTo(str("aBc"), str("Abc")));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("ab"), str("ABC"), false));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("_"), str("0"), false));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("0"), str("a"), false));
    try std.testing.expectEqual(@as(i32, 0), strCompareCulture(str("ABC"), str("abc"), true));
    try std.testing.expect(try strCompareCultureRange(str("ABC"), 1, str("bcd"), 0, 2, false) > 0);
    try std.testing.expectEqual(@as(i32, 0), try strCompareRangeWith(str("ABC"), 1, str("bcd"), 0, 2, 5));
    try std.testing.expect(try strStartsWithOpt(str("ABCD"), str("ab"), true));
    try std.testing.expect(try strEndsWithOpt(str("ABCD"), str("cd"), true));
    try std.testing.expectEqual(@as(i32, 1), try strIndexOfCharIgnoreCase(str("aBc"), 'B'));
    // (pairs checked with .NET: accents after the base letter, expansions, ignorable control
    // chars, letters without a base after their neighbour; the table was also checked against
    // 3,000 random pairs over U+0000..U+024F, see fable_collation.zig)
    const pairs = .{
        .{ "e", "é", -1 },
        .{ "é", "f", -1 },
        .{ "z", "é", 1 },
        .{ "co-op", "coop", -1 },
        .{ "a-b", "ab", -1 },
        .{ "Æ", "AE", 1 },
        .{ "ss", "ß", -1 },
        .{ "résumé", "resume", 1 },
        .{ "ı", "z", -1 },
        .{ "o", "ı", 1 },
        .{ "\u{1}", "", 0 },
        .{ "\u{a0}", " ", 1 },
        .{ "file10", "file9", -1 },
        .{ "a", "A", -1 },
    };
    inline for (pairs) |t| {
        try std.testing.expectEqual(@as(i32, t[2]), strCompareCulture(str(t[0]), str(t[1]), false));
    }
}

test "exception stack trace is null before throw and captured on throw" {
    const start_stats = thread.stats;
    {
        const e0 = Failure.new(.{ .Message = str("unthrown") });
        defer drop(e0);
        try std.testing.expect(exnStackTrace(e0) == null);

        throw(dup(e0));
        const caught = take();
        defer drop(caught);
        const trace = exnStackTrace(caught);
        defer drop(trace);
        try std.testing.expect(trace != null);
        try std.testing.expect(unitsOf(trace).len > 0);
    }
    try std.testing.expectEqual(start_stats.allocs - start_stats.frees, thread.stats.allocs - thread.stats.frees);
}

// ---- values shared between threads ----

const ShareTestList = List(String);
const ShareTestRec = *struct { @"$rc": u32 = 1, name: String, items: ShareTestList };

fn shareTestList(n: usize) ShareTestList {
    var l: ShareTestList = .Empty;
    var i: usize = 0;
    while (i < n) : (i += 1) l = ShareTestList{ .Cons = cell(ShareTestList, .Cons, .{ .Head = strConcat(str("x"), str("y")), .Tail = l }) };
    return l;
}

fn shareTestReader(r: ShareTestRec, out: *usize) void {
    var k: usize = 0;
    var round: usize = 0;
    while (round < 2000) : (round += 1) {
        const mine = dup(r);
        var cur = dup(mine.items);
        while (true) {
            switch (cur) {
                .Empty => break,
                .Cons => |c| {
                    k += 1;
                    const next = dup(c.Tail);
                    drop(cur);
                    cur = next;
                },
            }
        }
        drop(mine);
    }
    out.* = k;
    drop(r);
}

test "a value shared between threads is counted atomically and freed once" {
    const before = thread.stats;
    const r = new(ShareTestRec, .{ .name = strConcat(str("a"), str("b")), .items = shareTestList(100_000) });
    try markShared(r);
    var outs: [4]usize = @splat(0);
    var ts: [4]std.Thread = undefined;
    for (&ts, &outs) |*t, *o| t.* = try std.Thread.spawn(.{}, shareTestReader, .{ dup(r), o });
    for (ts) |t| t.join();
    for (outs) |o| try std.testing.expectEqual(@as(usize, 2000 * 100_000), o);
    drop(r);
    // (allocations on this thread; frees happened on whichever thread let go last: this one)
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "native integers and SGC header compile cleanly across pointer widths" {
    try std.testing.expectEqual(@sizeOf(sgc.Hdr), 3 * @sizeOf(*sgc.Hdr) + 12);
    const n: isize = -7;
    const u: usize = 42;
    try std.testing.expectEqual(@as(i32, -7), conv(i32, n));
    try std.testing.expectEqual(@as(u32, 42), conv(u32, u));
    try std.testing.expectEqual(@as(usize, 42), conv(usize, @as(u64, 42)));
    try std.testing.expectEqual(@as(isize, -7), conv(isize, @as(i64, -7)));
    try std.testing.expectEqual(@as(i32, 42), hash(u));
    try std.testing.expectEqual(if (@bitSizeOf(isize) == 64) @as(i32, 6) else @as(i32, -7), hash(n));
    const big_u: u64 = std.math.maxInt(u64);
    _ = hash(big_u);
}

test "fat-pointer interface: zero-alloc class cast, upcast, and round-trip downcast" {
    const Part = struct { x: i32 };
    const Chain = struct { own: Part };
    const cls_ty: ObjType = objType(Chain, "RtTestClass", null, &.{}, null);

    const ISubVt = struct {
        @"$meta": *const IfaceMeta,
        Get: *const fn (?*anyopaque, void) Raised!i32,
    };
    const ISub = Iface(ISubVt);
    const IBaseVt = struct {
        @"$meta": *const IfaceMeta,
        Get: *const fn (?*anyopaque, void) Raised!i32,
    };
    const IBase = Iface(IBaseVt);

    const SubClsImpl = struct {
        fn get(d: ?*anyopaque, _: void) Raised!i32 {
            const o: Obj = @ptrCast(@alignCast(d.?));
            return objPart(*Part, &.{Part}, o).x;
        }
        const vt: ISubVt = .{
            .@"$meta" = &obj_iface_meta,
            .Get = &get,
        };
    };
    const BaseUpcastImpl = struct {
        fn get(d: ?*anyopaque, u: void) Raised!i32 {
            const sub = boxed(ISub, @ptrCast(@alignCast(d.?))).value;
            return sub.vt.Get(sub.data, u);
        }
        const vt: IBaseVt = .{
            .@"$meta" = upcastIfaceMeta(ISub),
            .Get = &get,
        };
    };

    const before = thread.stats;
    {
        const obj = objNew(&cls_ty, Chain{ .own = .{ .x = 42 } });
        const after_obj = thread.stats.allocs;

        // Zero-alloc class -> interface view
        const sub: ?ISub = ISub{ .data = @ptrCast(obj), .vt = &SubClsImpl.vt };
        try std.testing.expectEqual(after_obj, thread.stats.allocs);
        try std.testing.expectEqual(@as(i32, 42), try sub.?.vt.Get(sub.?.data, {}));
        try std.testing.expect(ifaceIsClass(sub, &cls_ty));

        // Round-trip class downcast
        const back_any = try ifaceCastClass(sub, &cls_ty);
        defer drop(back_any);
        try std.testing.expectEqual(obj, back_any.?);

        // Upcast ISub -> IBase & round-trip downcasts to both ISub and class
        const base: ?IBase = ifaceBox(IBase, ISub, sub.?, &BaseUpcastImpl.vt);
        defer drop(base);
        try std.testing.expectEqual(@as(i32, 42), try base.?.vt.Get(base.?.data, {}));
        try std.testing.expect(ifaceIsClass(base, &cls_ty));

        const back_sub = try ifaceUnbox(?ISub, base);
        defer drop(back_sub);
        try std.testing.expectEqual(@as(i32, 42), try back_sub.?.vt.Get(back_sub.?.data, {}));

        const back_cls = try ifaceCastClass(base, &cls_ty);
        defer drop(back_cls);
        try std.testing.expectEqual(obj, back_cls.?);

        // Boxed interface preserves wrapper for unbox(?ISub) while delegating class identity & refEql
        const boxed_sub = box(sub);
        defer drop(boxed_sub);
        try std.testing.expect(isType(?ISub, boxed_sub));
        const unboxed_sub = try unbox(?ISub, boxed_sub);
        defer drop(unboxed_sub);
        try std.testing.expectEqual(@as(i32, 42), try unboxed_sub.?.vt.Get(unboxed_sub.?.data, {}));
        try std.testing.expect(anyIsClass(boxed_sub, &cls_ty));
        const cast_cls = try anyToClass(boxed_sub, &cls_ty);
        defer drop(cast_cls);
        try std.testing.expectEqual(obj, cast_cls.?);
        try std.testing.expect(refEql(sub, sub));
        try std.testing.expect(refEql(sub, back_sub));
        try std.testing.expect(refEql(@as(Any, obj), boxed_sub));
        try std.testing.expect(refEql(@as(?ISub, null), @as(?ISub, null)));
        try std.testing.expect(!refEql(sub, @as(?ISub, null)));
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "closure2 and apply2: zero intermediate closure alloc and exception-edge drops" {
    const Inner = Func(*const fn (?*Env, String) Raised!i32);
    const Outer = Func(*const fn (?*Env, i32) Raised!Inner);
    const Caps = struct { base: i32 };
    const Impl = struct {
        fn innerCode(env: ?*Env, b: String) Raised!i32 {
            defer drop(b);
            const c = captured(Caps, env);
            return c.base + @as(i32, @intCast(unitsOf(b).len));
        }
        fn code(env: ?*Env, a: i32) Raised!Inner {
            const c = captured(Caps, env);
            return closure(Inner, Caps, .{ .base = c.base + a }, innerCode);
        }
        fn code2(env: ?*Env, a: i32, b: String) Raised!i32 {
            defer drop(b);
            const c = captured(Caps, env);
            return c.base + a + @as(i32, @intCast(unitsOf(b).len));
        }
        fn raisingFirst(_: ?*Env, _: i32) Raised!Inner {
            return raise(ArgumentException, str("boom"));
        }
    };

    const before = thread.stats;
    {
        const f = closure2(Outer, Caps, .{ .base = 10 }, Impl.code, Impl.code2);
        defer drop(f);

        const s1 = strConcat(str("he"), str("llo"));
        const after_s1 = thread.stats.allocs;
        const r1 = try apply2(i32, f, 5, s1);
        try std.testing.expectEqual(@as(i32, 20), r1);
        // apply2 invoked code2 directly without allocating an Inner closure Env.
        try std.testing.expectEqual(after_s1, thread.stats.allocs);

        // Partial application still works through 1-arg code.
        const g = try f.code(f.env, 5);
        defer drop(g);
        const s2 = strConcat(str("wo"), str("rld"));
        try std.testing.expectEqual(@as(i32, 20), try g.code(g.env, s2));

        // When 1-arg code raises inside apply2, owned second argument b must be dropped.
        const failing: Outer = .{ .env = null, .code = Impl.raisingFirst };
        const s3 = strConcat(str("le"), str("ak?"));
        const res = apply2(i32, failing, 1, s3);
        try std.testing.expectError(error.Raised, res);
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "arraySetAt, dropAll, callM/xcallM, and exn_show" {
    const before = thread.stats;
    {
        const A = Array(String);
        const arr = arrayOf(A, .{ str("a"), str("b") });
        const s = strConcat(str("c"), str("d"));
        arraySetAt(arr, 1, s);
        drop(s);
        try expectText("cd", try arrayGet(arr, 1));

        const p1 = strConcat(str("p"), str("1"));
        const p2 = strConcat(str("p"), str("2"));
        dropAll(.{ arr, p1, p2 });

        const Nums = Array(i32);
        const nums = arrayOf(Nums, .{ 1, 2, 3 });
        arraySetAt(nums, 0, 42);
        try std.testing.expectEqual(@as(i32, 42), arrayItemAt(nums, 0));
        drop(nums);

        const Mod = struct {
            pub fn echo(x: String) Raised!String {
                if (unitsOf(x).len == 0) return raise(ArgumentException, str("empty"));
                return dup(x);
            }
            pub const @"echo$sig" = .{ .borrows = .{true}, .result_borrowed = false };

            pub fn plainOk(n: i32) i32 {
                return n + 1;
            }
        };

        const src = strConcat(str("hi"), str("!"));
        const echoed = try xcallM(Mod, "echo", "k", .{src}, .{});
        try expectText("hi!", echoed);
        try expectText("hi!", dup(src));

        const held = strConcat(str("he"), str("ld"));
        const fail_arg = str("");
        try std.testing.expectError(error.Raised, xcallM(Mod, "echo", "g", .{fail_arg}, .{ src, held }));
        drop(take());

        try std.testing.expectEqual(@as(i32, 8), try xcallPlain(Mod.plainOk(7), .{}));
        try std.testing.expect(exn_show);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "an array that does not fit raises OutOfMemoryException" {
    const saved = rt.allocator;
    defer rt.allocator = saved;
    // (an allocator that refuses what is larger than a page, as a heap does what it cannot fit)
    const Big = struct {
        var base: std.mem.Allocator = undefined;
        fn bigAlloc(_: *anyopaque, len: usize, a: std.mem.Alignment, ra: usize) ?[*]u8 {
            if (len > 4096) return null;
            return base.rawAlloc(len, a, ra);
        }
        fn bigResize(_: *anyopaque, m: []u8, a: std.mem.Alignment, n: usize, ra: usize) bool {
            return base.rawResize(m, a, n, ra);
        }
        fn bigRemap(_: *anyopaque, m: []u8, a: std.mem.Alignment, n: usize, ra: usize) ?[*]u8 {
            return base.rawRemap(m, a, n, ra);
        }
        fn bigFree(_: *anyopaque, m: []u8, a: std.mem.Alignment, ra: usize) void {
            base.rawFree(m, a, ra);
        }
        const vt: std.mem.Allocator.VTable = .{ .alloc = bigAlloc, .resize = bigResize, .remap = bigRemap, .free = bigFree };
    };
    Big.base = saved;
    rt.allocator = .{ .ptr = undefined, .vtable = &Big.vt };
    const A = Array(i64);
    try std.testing.expectError(error.Raised, arrayZero(A, 1000));
    rt.allocator = saved;
    const e = take();
    try std.testing.expectEqualStrings("System.OutOfMemoryException", e.type.name);
    drop(e);
}

test "invokeK: Known 1-arg, curried 2-arg with/without call2, borrowing, error drops, and Func fallback" {
    const before = thread.stats;
    {
        const s_prefix = strConcat(str("pre:"), str(""));
        defer drop(s_prefix);

        const KLen = struct {
            pub const fable_known = {};
            caps: struct { c0: String },
            pub const borrows = .{true};
            pub const result_borrowed = false;
            pub inline fn call(self: *const @This(), x: String) i32 {
                return @as(i32, @intCast(unitsOf(self.caps.c0).len + unitsOf(x).len));
            }
        };

        const item1 = strConcat(str("ab"), str("c"));
        defer drop(item1);
        const r_keep = try invokeK(i32, KLen{ .caps = .{ .c0 = s_prefix } }, "k", .{item1}, .{});
        try std.testing.expectEqual(@as(i32, 7), r_keep);

        const item2 = strConcat(str("de"), str("fg"));
        const r_give = try invokeK(i32, KLen{ .caps = .{ .c0 = s_prefix } }, "g", .{item2}, .{});
        try std.testing.expectEqual(@as(i32, 8), r_give);

        const Inner = Func(*const fn (?*Env, String) Raised!i32);
        const Caps = struct { base: i32 };
        const CurriedImpl = struct {
            fn inner(env: ?*Env, b: String) Raised!i32 {
                defer drop(b);
                const c = captured(Caps, env);
                return c.base + @as(i32, @intCast(unitsOf(b).len));
            }
            fn stage1(a: i32) Inner {
                return closure(Inner, Caps, .{ .base = a }, inner);
            }
        };
        const KCurried2 = struct {
            pub const fable_known = {};
            caps: struct { c0: i32 },
            pub const borrows = .{false};
            pub const result_borrowed = false;
            pub const borrows2 = .{ false, true };
            pub const result_borrowed2 = false;
            pub inline fn call(self: *const @This(), a: i32) Inner {
                return CurriedImpl.stage1(self.caps.c0 + a);
            }
            pub inline fn call2(self: *const @This(), a: i32, b: String) i32 {
                return self.caps.c0 + a + @as(i32, @intCast(unitsOf(b).len));
            }
        };
        const KCurried1 = struct {
            pub const fable_known = {};
            caps: struct { c0: i32 },
            pub const borrows = .{false};
            pub const result_borrowed = false;
            pub inline fn call(self: *const @This(), a: i32) Inner {
                return CurriedImpl.stage1(self.caps.c0 + a);
            }
        };
        const KRaise1 = struct {
            pub const fable_known = {};
            pub const borrows = .{true};
            pub const result_borrowed = false;
            pub inline fn call(_: *const @This(), x: String) Raised!Inner {
                _ = x;
                return raise(ArgumentException, str("boom1"));
            }
        };

        const item3 = strConcat(str("x"), str("yz"));
        const allocs_before = thread.stats.allocs;
        try std.testing.expectEqual(@as(i32, 18), try invokeK(i32, KCurried2{ .caps = .{ .c0 = 10 } }, "pg", .{ @as(i32, 5), item3 }, .{}));
        try std.testing.expectEqual(allocs_before, thread.stats.allocs);

        const item4 = strConcat(str("w"), str("xyz"));
        try std.testing.expectEqual(@as(i32, 19), try invokeK(i32, KCurried1{ .caps = .{ .c0 = 10 } }, "pg", .{ @as(i32, 5), item4 }, .{}));

        const held = strConcat(str("he"), str("ld"));
        const arg_a = strConcat(str("aa"), str("a"));
        const arg_b = strConcat(str("bb"), str("b"));
        try std.testing.expectError(error.Raised, invokeK(i32, KRaise1{}, "gg", .{ arg_a, arg_b }, .{held}));
        drop(take());

        // Ordinary Func fallback
        const Fn1 = Func(*const fn (?*Env, String) Raised!i32);
        const f_fallback: Fn1 = .{ .env = null, .code = struct {
            fn f(_: ?*Env, s: String) Raised!i32 {
                defer drop(s);
                return @as(i32, @intCast(unitsOf(s).len));
            }
        }.f };
        defer drop(f_fallback);
        try std.testing.expectEqual(@as(i32, 3), try invokeK(i32, f_fallback, "k", .{item1}, .{}));
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "callHofM and callHofG: callK dispatch, noescape mixed args, toFunc fallback with borrow/own" {
    const before = thread.stats;
    {
        const s_cap = strConcat(str("pre:"), str(""));
        defer drop(s_cap);

        const Fn1 = Func(*const fn (?*Env, String) Raised!i32);
        const Caps = struct { c0: String };
        const Kn1 = struct {
            pub const fable_known = {};
            pub const FuncType = Fn1;
            caps: struct { c0: String },
            pub const borrows = .{true};
            pub const result_borrowed = false;
            pub inline fn call(self: *const @This(), x: String) i32 {
                return @as(i32, @intCast(unitsOf(self.caps.c0).len + unitsOf(x).len));
            }
            pub fn toFunc(self: @This()) FuncType {
                const Adapter = struct {
                    fn code(env: ?*Env, a0: String) Raised!i32 {
                        defer drop(a0);
                        const c = captured(Caps, env);
                        return @as(i32, @intCast(unitsOf(c.c0).len + unitsOf(a0).len));
                    }
                };
                return closure(FuncType, Caps, .{ .c0 = dup(self.caps.c0) }, Adapter.code);
            }
        };

        const Mod = struct {
            pub fn withK(f: Fn1, s: String) Raised!i32 {
                defer drop(f);
                return f.code(f.env, s);
            }
            pub fn @"withK$k"(f: anytype, s: String) Raised!i32 {
                return invokeK(i32, f, "g", .{s}, .{});
            }
            pub const @"withK$sig" = .{ .borrows = .{ false, false }, .result_borrowed = false };
            pub const @"withK$noescape" = .{ true, false };

            pub fn escBorrow(f: Fn1, s: String) Raised!i32 {
                return f.code(f.env, s);
            }
            pub const @"escBorrow$sig" = .{ .borrows = .{ true, false }, .result_borrowed = false };

            pub fn escOwn(f: Fn1, s: String) Raised!i32 {
                defer drop(f);
                return f.code(f.env, s);
            }
            pub const @"escOwn$sig" = .{ .borrows = .{ false, false }, .result_borrowed = false };

            pub fn escRaise(f: Fn1, s: String) Raised!i32 {
                _ = f;
                drop(s);
                return raise(ArgumentException, str("boom-hof"));
            }
            pub const @"escRaise$sig" = .{ .borrows = .{ true, false }, .result_borrowed = false };

            pub fn gen(comptime T: type) type {
                _ = T;
                return struct {
                    pub const sig = .{ .borrows = .{ true, false }, .result_borrowed = false };
                    pub const noescape = .{ true, false };
                    pub fn call(f: Fn1, s: String) Raised!i32 {
                        return f.code(f.env, s);
                    }
                    pub fn callK(f: anytype, s: String) Raised!i32 {
                        return invokeK(i32, f, "g", .{s}, .{});
                    }
                };
            }
        };

        const k_val = Kn1{ .caps = .{ .c0 = s_cap } };

        // No-escape module call: 0 heap env allocs beyond string arg
        const s1 = strConcat(str("ab"), str("c"));
        const a0 = thread.stats.allocs;
        try std.testing.expectEqual(@as(i32, 7), try xcallHofM(Mod, "withK", "gg", .{ k_val, s1 }, .{}));
        try std.testing.expectEqual(a0, thread.stats.allocs);

        // No-escape generic call: 0 heap env allocs
        const s2 = strConcat(str("de"), str("fg"));
        const a1 = thread.stats.allocs;
        try std.testing.expectEqual(@as(i32, 8), try callHofG(Mod.gen(String), "gg", .{ k_val, s2 }, .{}));
        try std.testing.expectEqual(a1, thread.stats.allocs);

        // Escaping callK-less module HOFs: toFunc() fallback (borrows=true and borrows=false), plus error unwind drop
        const s3 = strConcat(str("hi"), str(""));
        try std.testing.expectEqual(@as(i32, 6), try callHofM(Mod, "escBorrow", "gg", .{ k_val, s3 }, .{}));

        const s4 = strConcat(str("jk"), str("l"));
        try std.testing.expectEqual(@as(i32, 7), try callHofM(Mod, "escOwn", "gg", .{ k_val, s4 }, .{}));

        const s5 = strConcat(str("mn"), str("o"));
        const held = strConcat(str("he"), str("ld"));
        try std.testing.expectError(error.Raised, xcallHofM(Mod, "escRaise", "gg", .{ k_val, s5 }, .{held}));
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "acrossAssumed: borrowed return without dup, generic form, empty result_from, and raise cleanup" {
    const before = thread.stats;
    {
        const s_owned = strConcat(str("hello "), str("world"));
        defer drop(s_owned);

        const s_extra = strConcat(str("ex"), str("tra"));

        const Mod = struct {
            pub fn idStr(s: String, n: i32) String {
                _ = n;
                return s;
            }
            pub const @"idStr$sig" = .{ .borrows = .{ true, false }, .result_borrowed = true, .result_from = .{0} };

            pub fn constStr(s: String) String {
                _ = s;
                return str("lit");
            }
            pub const @"constStr$sig" = .{ .borrows = .{true}, .result_borrowed = true, .result_from = .{} };

            pub fn borrowAndRaise(s: String) Raised!String {
                _ = s;
                return raise(ArgumentException, str("boom-assumed"));
            }
            pub const @"borrowAndRaise$sig" = .{ .borrows = .{true}, .result_borrowed = true, .result_from = .{0} };

            pub fn gen(comptime T: type) type {
                _ = T;
                return struct {
                    pub fn call(x: String, drop_me: String) String {
                        _ = drop_me;
                        return x;
                    }
                    pub const sig = .{ .borrows = .{ true, true }, .result_borrowed = true, .result_from = .{0} };
                };
            }
        };

        // Module callAssumedM: 0 RC dups and 0 allocs on borrowed result
        const b0 = thread.stats;
        const r1 = callAssumedM(Mod, "idStr", .{0}, "kp", .{ s_owned, @as(i32, 42) }, .{});
        try std.testing.expect(strEql(s_owned, r1));
        try std.testing.expectEqual(b0.allocs, thread.stats.allocs);
        try std.testing.expectEqual(b0.dups, thread.stats.dups);

        // Empty result_from = .{}
        const r2 = callAssumedM(Mod, "constStr", .{}, "k", .{s_owned}, .{});
        try std.testing.expect(strEql(str("lit"), r2));

        // Generic callAssumedG with one 'k' borrowed source and one 'g' borrowed dead arg
        const r3 = callAssumedG(Mod.gen(String), .{0}, "kg", .{ s_owned, s_extra }, .{});
        try std.testing.expect(strEql(s_owned, r3));

        // Raise edge drops err_drops even though source arg is 'k'
        const s_err_drop = strConcat(str("drop"), str("me"));
        try std.testing.expectError(error.Raised, xcallAssumedM(Mod, "borrowAndRaise", .{0}, "k", .{s_owned}, .{s_err_drop}));
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "assertNoRaise and assertNoStore: valid non-raising and field-disjoint store assertions" {
    const Mod = struct {
        pub fn pureAdd(a: i32, b: i32) i32 {
            return a +% b;
        }
        pub const @"pureAdd$stores" = .{ .fields = .{}, .calls_callback = false, .calls_ext_store = false };

        pub fn setB() void {}
        pub const @"setB$stores" = .{ .fields = .{"Mod.Box|B"}, .calls_callback = false, .calls_ext_store = false };

        pub fn genPure(comptime T: type) type {
            return struct {
                pub fn call(x: T) T {
                    return x;
                }
            };
        }
    };
    comptime {
        assertNoRaise(Mod.pureAdd);
        assertNoRaise(Mod.genPure(i32).call);
        assertNoStore(Mod, "pureAdd", .{"Mod.Box|A"}, true);
        assertNoStore(Mod, "setB", .{"Mod.Box|A"}, true);
        assertNoStore(Mod, "setB", .{}, true);
    }
    try std.testing.expectEqual(@as(i32, 5), Mod.pureAdd(2, 3));
}

test "TailCtx, fitsTailArgs, tailStore/tailLoad, takeSelf, dropEnv, plugRet and chained TailFn" {
    const before = thread.stats;
    {
        const Big = struct { data: [136]u8 };
        comptime {
            try std.testing.expect(fitsTailArgs(&.{ i32, String, void, ?i64 }));
            try std.testing.expect(!fitsTailArgs(&.{Big}));
            try std.testing.expect(canPlugRet(List(String)));
            try std.testing.expect(!canPlugRet(void));
            try std.testing.expect(!canPlugRet(Obj));
        }

        const s_arg = strConcat(str("he"), str("llo"));
        const Caps = struct { prefix: String };
        const Chain = struct {
            fn step1(ctx: *TailCtx, ret: *anyopaque) TailStatus {
                const a = tailLoad(&.{ i32, String }, ctx);
                const ts = takeSelfBorrowed(ctx);
                const env: ?*Env = @ptrCast(@alignCast(ts.ptr));
                const c = captured(Caps, env);
                const joined = strConcat(c.prefix, a[1]);
                drop(a[1]);
                if (ts.owned) dropEnv(env);
                if (a[0] <= 0) {
                    @as(*String, @ptrCast(@alignCast(ret))).* = joined;
                    return .ok;
                }
                tailStore(&.{ i32, String }, ctx, .{ a[0] - 1, joined });
                ctx.self = null;
                ctx.self_owned = true;
                return @call(tail_call, step2, .{ ctx, ret });
            }
            fn step2(ctx: *TailCtx, ret: *anyopaque) TailStatus {
                const a = tailLoad(&.{ i32, String }, ctx);
                if (a[0] == 1) {
                    drop(a[1]);
                    _ = raise(ArgumentException, str("tc-boom")) catch {};
                    plugRet(String, ret);
                    return .raised;
                }
                tailStore(&.{String}, ctx, .{a[1]});
                ctx.self = null;
                return @call(tail_call, step3, .{ ctx, ret });
            }
            fn step3(ctx: *TailCtx, ret: *anyopaque) TailStatus {
                const a = tailLoad(&.{String}, ctx);
                @as(*String, @ptrCast(@alignCast(ret))).* = a[0];
                return .ok;
            }
        };

        const Fn1 = Func(*const fn (?*Env, i32, String) Raised!String);
        const f = closureTc(Fn1, Caps, .{ .prefix = dup(s_arg) }, struct {
            fn c(_: ?*Env, n: i32, s: String) Raised!String {
                _ = n;
                return s;
            }
        }.c, &Chain.step1);
        drop(s_arg);

        var ctx: TailCtx = .{};
        var res: String = undefined;
        const arg2 = strConcat(str("!"), str("?"));
        tailStore(&.{ i32, String }, &ctx, .{ @as(i32, 1), arg2 });
        ctx.self = @ptrCast(f.env);
        ctx.self_owned = false; // lent from caller: f remains alive with rc=1
        try std.testing.expectEqual(TailStatus.ok, f.tcode.?(&ctx, @ptrCast(&res)));
        try std.testing.expect(strEql(str("hello!?"), res));
        drop(res);

        // Error path with plugRet leaves res droppable
        var ctx_err: TailCtx = .{};
        var res_err: String = undefined;
        const arg_err = strConcat(str("x"), str("y"));
        tailStore(&.{ i32, String }, &ctx_err, .{ @as(i32, 2), arg_err });
        ctx_err.self = @ptrCast(f.env); // moves f's remaining env ownership
        ctx_err.self_owned = true;
        try std.testing.expectEqual(TailStatus.raised, f.tcode.?(&ctx_err, @ptrCast(&res_err)));
        drop(take());
        drop(res_err);

        // plugRet on List(String) writes .Empty without allocating or leaking
        var list_plug: List(String) = undefined;
        plugRet(List(String), @ptrCast(&list_plug));
        drop(list_plug);

        // Zero-sized non-void parameters (e.g. 1-case fieldless union) round-trip through tailStore/tailLoad
        const Single = union(enum) { Only };
        var ctx_z: TailCtx = .{};
        tailStore(&.{ Single, i32, void }, &ctx_z, .{ Single.Only, @as(i32, 7), {} });
        const loaded_z = tailLoad(&.{ Single, i32, void }, &ctx_z);
        try std.testing.expect(loaded_z[0] == .Only);
        try std.testing.expectEqual(@as(i32, 7), loaded_z[1]);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "Iface $tc slots, IfaceAdapter nulls $tc, and cross-iface tail chain" {
    const before = thread.stats;
    {
        const IA = Iface(IfaceAnon1(.{"Step"}).of(*const fn (?*anyopaque, i32, *const anyopaque) Raised!i32));
        const IBoxed = Iface(struct {
            @"$meta": *const IfaceMeta,
            Boxed: *const fn (?*anyopaque, Any) Raised!Any,
            @"Boxed$tc": ?TailFn = null,
        });
        const IConc = Iface(struct {
            @"$meta": *const IfaceMeta,
            Boxed: *const fn (?*anyopaque, i32) Raised!i32,
            @"Boxed$tc": ?TailFn = null,
        });

        const VtA = @typeInfo(@FieldType(IA, "vt")).pointer.child;
        // Defaulted $tc field on IfaceAnon starts null
        const default_vt: VtA = .{
            .@"$meta" = &empty_iface_meta,
            .Step = struct {
                fn f(_: ?*anyopaque, x: i32, _: *const anyopaque) Raised!i32 {
                    return x;
                }
            }.f,
        };
        try std.testing.expect(default_vt.@"Step$tc" == null);

        // Chaining through interface Step$tc slots with self_owned=false and self_owned=true
        const Caps = struct { tag: String };
        const Node = struct {
            fn callNorm(d: ?*anyopaque, n: i32, other: *const anyopaque) Raised!i32 {
                _ = d;
                _ = n;
                _ = other;
                return 0;
            }
            fn stepTc(ctx: *TailCtx, ret: *anyopaque) TailStatus {
                const a = tailLoad(&.{ i32, *const anyopaque }, ctx);
                const ts = takeSelfBorrowed(ctx);
                const env: ?*Env = @ptrCast(@alignCast(ts.ptr));
                if (ts.owned) dropEnv(env);
                if (a[0] <= 0) {
                    @as(*i32, @ptrCast(@alignCast(ret))).* = 99;
                    return .ok;
                }
                const nxt: *const IA = @ptrCast(@alignCast(a[1]));
                const nxt_own = dup(nxt.*);
                tailStore(&.{ i32, *const anyopaque }, ctx, .{ a[0] - 1, a[1] });
                ctx.self = nxt_own.data;
                ctx.self_owned = true;
                return @call(tail_call, nxt.vt.@"Step$tc".?, .{ ctx, ret });
            }
            const vt: VtA = .{
                .@"$meta" = &env_iface_meta,
                .Step = &callNorm,
                .@"Step$tc" = &stepTc,
            };
        };

        const s = strConcat(str("if"), str("ace"));
        const ia = ifaceClosure(IA, Caps, .{ .tag = s }, &Node.vt);
        defer drop(ia);

        var tctx: TailCtx = .{};
        var res: i32 = undefined;
        tailStore(&.{ i32, *const anyopaque }, &tctx, .{ @as(i32, 3), @as(*const anyopaque, @ptrCast(&ia)) });
        tctx.self = ia.data;
        tctx.self_owned = false;
        try std.testing.expectEqual(TailStatus.ok, ia.vt.@"Step$tc".?(&tctx, @ptrCast(&res)));
        try std.testing.expectEqual(@as(i32, 99), res);

        // IfaceAdapter zeroes $tc fields cleanly
        const BoxedVt = @typeInfo(@FieldType(IBoxed, "vt")).pointer.child;
        const boxed_vt: BoxedVt = .{
            .@"$meta" = &empty_iface_meta,
            .Boxed = struct {
                fn f(_: ?*anyopaque, x: Any) Raised!Any {
                    return x;
                }
            }.f,
        };
        const ib: IBoxed = .{ .data = null, .vt = &boxed_vt };
        const ic = ifaceAdapt(IConc, ib);
        defer drop(ic);
        try std.testing.expect(ic.vt.@"Boxed$tc" == null);
        try std.testing.expectEqual(@as(i32, 42), try ic.vt.Boxed(ic.data, 42));
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "callHofAssumedM and callHofAssumedG: Known lambda + borrowed RetFrom without dup" {
    const before = thread.stats;
    {
        const s_owned = strConcat(str("hello "), str("assumed"));
        defer drop(s_owned);

        const F = Func(*const fn (?*Env, String) Raised!bool);
        const K = struct {
            pub const fable_known = {};
            pub const FuncType = F;
            pub const sig = .{ .borrows = .{ true, true }, .result_borrowed = false };
            cap: i32,
            pub inline fn call(self: *const @This(), x: String) Raised!bool {
                return strLength(x) > self.cap;
            }
            fn adapter(env: ?*Env, x: String) Raised!bool {
                const c = captured(struct { cap: i32 }, env);
                defer drop(x);
                return strLength(x) > c.cap;
            }
            pub fn toFunc(self: @This()) F {
                return closure(F, struct { cap: i32 }, .{ .cap = self.cap }, adapter);
            }
        };

        const Mod = struct {
            pub fn checkOrFallback(k: F, s: String) Raised!String {
                defer drop(k);
                _ = try k.code(k.env, dup(s));
                return s;
            }
            pub fn @"checkOrFallback$k"(k: anytype, s: String) Raised!String {
                if (try k.call(s)) return s;
                return s;
            }
            pub const @"checkOrFallback$sig" = .{ .borrows = .{ false, true }, .result_borrowed = true, .result_from = .{1} };
            pub const @"checkOrFallback$noescape" = .{ true, false };

            pub fn pickEsc(k: F, s: String) Raised!String {
                _ = try k.code(k.env, dup(s));
                return s;
            }
            pub const @"pickEsc$sig" = .{ .borrows = .{ true, true }, .result_borrowed = true, .result_from = .{1} };

            pub fn raiseAfter(k: F, s: String) Raised!String {
                defer drop(k);
                _ = s;
                return raise(ArgumentException, str("boom-hof-assumed"));
            }
            pub const @"raiseAfter$sig" = .{ .borrows = .{ false, true }, .result_borrowed = true, .result_from = .{1} };

            pub fn gen(comptime T: type) type {
                _ = T;
                return struct {
                    pub fn call(k: F, s: String) Raised!String {
                        defer drop(k);
                        _ = try k.code(k.env, dup(s));
                        return s;
                    }
                    pub fn callK(k: anytype, s: String) Raised!String {
                        _ = try k.call(s);
                        return s;
                    }
                    pub const sig = .{ .borrows = .{ false, true }, .result_borrowed = true, .result_from = .{1} };
                    pub const noescape = .{ true, false };
                };
            }
        };

        const b0 = thread.stats;
        const r1 = try xcallHofAssumedM(Mod, "checkOrFallback", .{1}, "gk", .{ K{ .cap = 3 }, s_owned }, .{});
        try std.testing.expect(strEql(s_owned, r1));
        try std.testing.expectEqual(b0.allocs, thread.stats.allocs);
        try std.testing.expectEqual(b0.dups, thread.stats.dups);

        const r2 = try xcallHofAssumedM(Mod, "pickEsc", .{1}, "gk", .{ K{ .cap = 3 }, s_owned }, .{});
        try std.testing.expect(strEql(s_owned, r2));

        const r3 = try xcallHofAssumedG(Mod.gen(String), .{1}, "gk", .{ K{ .cap = 3 }, s_owned }, .{});
        try std.testing.expect(strEql(s_owned, r3));

        const s_err = strConcat(str("err"), str("drop"));
        try std.testing.expectError(error.Raised, xcallHofAssumedM(Mod, "raiseAfter", .{1}, "gk", .{ K{ .cap = 3 }, s_owned }, .{s_err}));
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "dropEnv: deep 150k multi-capture closure chain frees in O(1) stack" {
    const before = thread.stats;
    {
        const F = Func(*const fn (?*Env, i32) Raised!i32);
        const Caps = struct { c0: F, c1: F };
        const H = struct {
            fn base(_: ?*Env, x: i32) Raised!i32 {
                return x + 10;
            }
            fn step(env: ?*Env, x: i32) Raised!i32 {
                const c = captured(Caps, env);
                if (x >= 0) return c.c0.code(c.c0.env, x + 1);
                return c.c1.code(c.c1.env, x);
            }
        };
        const leaf: F = .{ .env = null, .code = H.base };
        var cur: F = leaf;
        for (0..150_000) |_| {
            cur = closure(F, Caps, .{ .c0 = cur, .c1 = dup(leaf) }, H.step);
        }
        defer drop(cur);
        try std.testing.expectEqual(@as(i32, 9), try cur.code(cur.env, -1));
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "3-flag $rc: immortal null cells never mutate or pass isUnique" {
    const before = thread.stats;
    const R = *struct { @"$rc": u32 = 1, value: i32 };
    const nr = rt.nullOf(R);
    try std.testing.expect(rt.isCellNull(nr));
    try std.testing.expect(!isUnique(nr));
    const rc0 = nr.@"$rc";
    try std.testing.expect((rc0 & rt.immortal_bit) != 0);
    rt.retain(nr);
    try std.testing.expectEqual(rc0, nr.@"$rc");
    rt.release(nr);
    try std.testing.expectEqual(rc0, nr.@"$rc");
    try std.testing.expect(!rt.releaseIsLast(nr));
    try std.testing.expectEqual(rc0, nr.@"$rc");
    try std.testing.expect(!try rt.markCell(nr));

    const na = rt.arrayNull(Array(i32));
    try std.testing.expect(rt.isCellNull(na));
    try std.testing.expect(!isUnique(na));
    try std.testing.expect(!rt.releaseIsLast(na));
    drop(na);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "3-flag $rc: local weak_bit blocks isUnique and clears handle on free and SGC collection" {
    const before = thread.stats;
    const R = *struct { @"$rc": u32 = 1, value: i32 };
    {
        const a = new(R, .{ .value = 11 });
        try std.testing.expect(isUnique(a));
        const w = try weakNew(Weak(R), a);
        defer drop(w);
        try std.testing.expect((a.@"$rc" & rt.weak_bit) != 0);
        try std.testing.expect(!isUnique(a));
        // Duplicate + release keeps weak_bit intact
        const b = dup(a);
        try std.testing.expectEqual(@as(u32, rt.weak_bit | 2), a.@"$rc");
        drop(b);
        try std.testing.expectEqual(@as(u32, rt.weak_bit | 1), a.@"$rc");
        try std.testing.expect(!isUnique(a));
        drop(a);
        try std.testing.expect(weakTryGet(w) == null);
    }

    // Cyclic SGC cells with a local WeakReference still collect cleanly and clear handle
    {
        const keep = testPerson(0);
        const p1 = testPerson(10);
        const p2 = testPerson(20);
        storeIn(p1, "friend", dup(p2));
        storeIn(p2, "friend", dup(p1));
        storeIn(keep, "friend", p1);
        const wp = try weakNew(Weak(TestPerson), p2);
        defer drop(wp);
        try std.testing.expect((p2.@"$rc" & rt.weak_bit) != 0);
        try std.testing.expect(!isUnique(p2));
        drop(p2);
        // Cut loose the p1<->p2 ring from `keep` so only SGC check finds it
        storeIn(keep, "friend", null);
        _ = rt.collect();
        try std.testing.expect(weakTryGet(wp) == null);
        drop(keep);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "3-flag $rc: adoptShared adopts unique cells despite active shared weak references elsewhere" {
    const before = thread.stats;
    const R = *struct { @"$rc": u32 = 1, value: i32 };
    const Pair = *struct { @"$rc": u32 = 1, a: R, b: R };
    {
        // An unrelated shared WeakReference keeps rt.weak_refs.shared_count > 0 across the process
        const unrelated = new(R, .{ .value = 99 });
        defer drop(unrelated);
        try markShared(unrelated);
        const w_unrel = try weakNew(Weak(R), unrelated);
        defer drop(w_unrel);
        try std.testing.expect(rt.weak_refs.shared_count.load(.monotonic) > 0);

        // Build Pair where `inner_free` has no weak ref and `inner_weak` DOES have a shared weak ref
        const inner_free = new(R, .{ .value = 1 });
        const inner_weak = new(R, .{ .value = 2 });
        const w_msg = try weakNew(Weak(R), inner_weak);
        defer drop(w_msg);
        const p = new(Pair, .{ .a = inner_free, .b = inner_weak });
        try markShared(p);
        try std.testing.expect(rt.isShared(p));
        try std.testing.expect(rt.isShared(inner_free));
        try std.testing.expect(rt.isShared(inner_weak));

        // Adopt: `p` and `inner_free` lose shared_bit even with active shared weak refs elsewhere,
        // while `inner_weak` (has weak_bit) stays shared!
        rt.adoptShared(p);
        try std.testing.expect(!rt.isShared(p));
        try std.testing.expect(!rt.isShared(inner_free));
        try std.testing.expect(rt.isShared(inner_weak));
        const got = weakTryGet(w_msg).?;
        try std.testing.expectEqual(@as(i32, 2), got.value);
        drop(got);
        drop(p);
        try std.testing.expect(weakTryGet(w_msg) == null);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "cellReuse from non-cyclic to cyclic cell initializes thread collector on fresh thread" {
    if (!rt.sgc.per_thread) return;

    const PlainU = union(enum) {
        Empty,
        Box: *struct { @"$rc": u32 = 1, a: i64, b: i64, c: i64, d: i64, e: i64, f: i32 },
    };
    const CyclicU = union(enum) {
        pub const fable_cyclic = true;
        Nil,
        Node: *struct { @"$rc": u32 = 1, @"$gc": GcHdr(true) = undefined, v: i64 },
    };
    comptime {
        std.debug.assert(@sizeOf(Cell(PlainU, .Box)) == @sizeOf(Cell(CyclicU, .Node)));
        std.debug.assert(@alignOf(Cell(PlainU, .Box)) == @alignOf(Cell(CyclicU, .Node)));
    }

    const Worker = struct {
        fn run(ok: *bool) void {
            defer rt.collectorDeinit();
            std.debug.assert(!thread.collector_ready);
            const before = thread.stats;
            const old_u = PlainU{ .Box = cell(PlainU, .Box, .{ .a = 1, .b = 2, .c = 3, .d = 4, .e = 5, .f = 6 }) };
            const old_addr = @intFromPtr(old_u.Box);
            var tok: ?*Cell(PlainU, .Box) = old_u.Box;
            defer if (tok) |d| rt.free(d);
            const new_u = CyclicU{ .Node = cellReuse(CyclicU, .Node, &tok, .{ .v = 99 }) };
            const reused_same = tok == null and @intFromPtr(new_u.Node) == old_addr and thread.collector_ready;
            const tracked_ok = !rt.track or (thread.stats.reuses - before.reuses == 1);
            drop(new_u);
            ok.* = reused_same and tracked_ok and (thread.stats.allocs - before.allocs == thread.stats.frees - before.frees);
        }
    };

    var ok = false;
    const t = try std.Thread.spawn(.{}, Worker.run, .{&ok});
    t.join();
    try std.testing.expect(ok);
}

test "newReuse hits matching KRefRecord layouts, falls back on mismatch, and respects weak references" {
    const RecA = *struct { @"$rc": u32 = 1, x: i64, y: i64 };
    const RecB = *struct { @"$rc": u32 = 1, tag: String, n: i64 };
    const RecBig = *struct { @"$rc": u32 = 1, a: i64, b: i64, c: i64 };
    comptime {
        std.debug.assert(@sizeOf(@typeInfo(RecA).pointer.child) == @sizeOf(@typeInfo(RecB).pointer.child));
        std.debug.assert(@alignOf(@typeInfo(RecA).pointer.child) == @alignOf(@typeInfo(RecB).pointer.child));
        std.debug.assert(@sizeOf(@typeInfo(RecBig).pointer.child) != @sizeOf(@typeInfo(RecA).pointer.child));
    }

    const before = thread.stats;
    // Hit: matching layout reuses address in place
    {
        const a = rt.new(RecA, .{ .x = 10, .y = 20 });
        const addr = @intFromPtr(a);
        try std.testing.expect(isUnique(a));
        var tok: ?RecA = a;
        defer if (tok) |d| rt.free(d);
        const s = strConcat(str("he"), str("llo"));
        const b = rt.newReuse(RecB, &tok, .{ .tag = s, .n = 42 });
        try std.testing.expect(tok == null);
        try std.testing.expectEqual(addr, @intFromPtr(b));
        try std.testing.expect(strEql(b.tag, str("hello")));
        try std.testing.expectEqual(@as(i64, 42), b.n);
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - before.reuses);
        drop(b);
    }

    // Size mismatch: token left intact, new allocation returned, defer frees dead cell
    {
        const a = rt.new(RecA, .{ .x = 1, .y = 2 });
        const addr = @intFromPtr(a);
        var tok: ?RecA = a;
        defer if (tok) |d| rt.free(d);
        const big = rt.newReuse(RecBig, &tok, .{ .a = 1, .b = 2, .c = 3 });
        try std.testing.expect(tok != null);
        try std.testing.expect(@intFromPtr(big) != addr);
        drop(big);
    }

    // WeakReference sets weak_bit, preventing isUnique reuse
    {
        const a = rt.new(RecA, .{ .x = 7, .y = 8 });
        const w = try weakNew(Weak(RecA), a);
        try std.testing.expect(!isUnique(a));
        drop(a);
        try std.testing.expect(weakTryGet(w) == null);
        drop(w);
    }

    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "weak_bit blocks cross-constructor cellReuse without resurrecting wrong type" {
    const PolyU = union(enum) {
        Zero,
        Num: *struct { @"$rc": u32 = 1, n: i64, pad: i64 },
        Str: *struct { @"$rc": u32 = 1, s: String, len: i64 },
    };
    const before = thread.stats;
    const old_cell = cell(PolyU, .Num, .{ .n = 77, .pad = 0 });
    const w = try weakNew(Weak(@TypeOf(old_cell)), old_cell);
    try std.testing.expect(!isUnique(old_cell));

    var tok: ?@TypeOf(old_cell) = null;
    defer if (tok) |d| rt.free(d);
    if (isUnique(old_cell)) {
        tok = old_cell;
    } else {
        drop(old_cell);
    }
    try std.testing.expect(tok == null);

    const next_u = PolyU{ .Str = cellReuse(PolyU, .Str, &tok, .{ .s = strConcat(str("a"), str("b")), .len = 2 }) };
    try std.testing.expect(weakTryGet(w) == null);
    drop(next_u);
    drop(w);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "closureReuse and closureTcReuse reuse EnvOf on match, clean up on mismatch, and handle cyclic envs" {
    const Fn1 = Func(*const fn (?*Env, i32) Raised!i32);
    const CapsSame = struct { c0: i64, c1: String };
    const CapsDiff = struct { c0: i64, c1: i64, c2: i64 };
    const before = thread.stats;

    // Exact match hit via closureTcReuse
    {
        const s0 = strConcat(str("k"), str("0"));
        const e_orig = closureTc(Fn1, CapsSame, .{ .c0 = 10, .c1 = dup(s0) }, struct {
            fn code(_: ?*Env, x: i32) Raised!i32 {
                return x;
            }
        }.code, null);
        drop(s0);
        const orig_addr = @intFromPtr(e_orig.env.?);
        var ctx: TailCtx = .{};
        try std.testing.expect(isUnique(e_orig.env.?));
        rt.forgetEnv(e_orig.env.?);
        const c = captured(CapsSame, e_orig.env);
        const c0_v = c.c0;
        const c1_v = c.c1;
        const re: *rt.EnvOf(CapsSame) = @alignCast(@fieldParentPtr("header", e_orig.env.?));
        ctx.reuse_env = @ptrCast(re);
        ctx.reuse_env_size = @sizeOf(rt.EnvOf(CapsSame));
        ctx.reuse_env_align = @alignOf(rt.EnvOf(CapsSame));

        const reused = rt.closureTcReuse(&ctx, Fn1, CapsSame, .{ .c0 = c0_v + 5, .c1 = c1_v }, struct {
            fn code(env: ?*Env, x: i32) Raised!i32 {
                const cap = captured(CapsSame, env);
                return x + @as(i32, @intCast(cap.c0));
            }
        }.code, null);
        try std.testing.expect(ctx.reuse_env == null);
        try std.testing.expectEqual(orig_addr, @intFromPtr(reused.env.?));
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - before.reuses);
        try std.testing.expectEqual(@as(i32, 18), try reused.code(reused.env, 3));
        drop(reused);
    }

    // Mismatch leaves ctx.reuse_env non-null for caller free
    {
        const e1 = closure(Fn1, CapsSame, .{ .c0 = 1, .c1 = str("x") }, struct {
            fn code(_: ?*Env, x: i32) Raised!i32 {
                return x;
            }
        }.code);
        var ctx: TailCtx = .{};
        rt.forgetEnv(e1.env.?);
        const re: *rt.EnvOf(CapsSame) = @alignCast(@fieldParentPtr("header", e1.env.?));
        const reuse_guard: ?*rt.EnvOf(CapsSame) = re;
        ctx.reuse_env = @ptrCast(re);
        ctx.reuse_env_size = @sizeOf(rt.EnvOf(CapsSame));
        ctx.reuse_env_align = @alignOf(rt.EnvOf(CapsSame));
        defer if (reuse_guard) |p| {
            if (ctx.reuse_env != null) {
                ctx.reuse_env = null;
                rt.free(p);
            }
        };

        const f2 = rt.closureReuse(&ctx, Fn1, CapsDiff, .{ .c0 = 1, .c1 = 2, .c2 = 3 }, struct {
            fn code(_: ?*Env, x: i32) Raised!i32 {
                return x + 1;
            }
        }.code);
        try std.testing.expect(ctx.reuse_env != null);
        try std.testing.expect(@intFromPtr(f2.env.?) != @intFromPtr(e1.env.?));
        drop(f2);
    }

    // Cyclic EnvOf (when functions_in_cycles / Ref): forgetEnv + touch + closureReuse
    {
        const CycNode = struct {
            pub const fable_cyclic = true;
            @"$rc": u32 = 1,
            @"$gc": GcHdr(true) = undefined,
            val: i32,
        };
        const CycPtr = *CycNode;
        const CapsCyc = struct { c0: CycPtr, c1: i64 };
        const n1 = rt.new(CycPtr, .{ .val = 55 });
        const f1 = closure(Fn1, CapsCyc, .{ .c0 = n1, .c1 = 1 }, struct {
            fn code(_: ?*Env, x: i32) Raised!i32 {
                return x;
            }
        }.code);
        const addr1 = @intFromPtr(f1.env.?);
        var ctx: TailCtx = .{};
        rt.forgetEnv(f1.env.?);
        const cap0 = captured(CapsCyc, f1.env).c0;
        if (comptime rt.EnvOf(CapsCyc).cyclic) rt.touch(cap0);
        const re: *rt.EnvOf(CapsCyc) = @alignCast(@fieldParentPtr("header", f1.env.?));
        ctx.reuse_env = @ptrCast(re);
        ctx.reuse_env_size = @sizeOf(rt.EnvOf(CapsCyc));
        ctx.reuse_env_align = @alignOf(rt.EnvOf(CapsCyc));

        const f2 = rt.closureReuse(&ctx, Fn1, CapsCyc, .{ .c0 = cap0, .c1 = 2 }, struct {
            fn code(env: ?*Env, x: i32) Raised!i32 {
                return x + captured(CapsCyc, env).c0.val;
            }
        }.code);
        try std.testing.expect(ctx.reuse_env == null);
        try std.testing.expectEqual(addr1, @intFromPtr(f2.env.?));
        try std.testing.expectEqual(@as(i32, 60), try f2.code(f2.env, 5));
        drop(f2);
    }

    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}
test "Weak(?Obj) sees target gone when ObjCell Raw is freed" {
    const Part = struct {
        val: i64,
        next: ?Obj,
    };
    const Chain = struct { own: Part };
    const T = struct {
        const ty: ObjType = rt.objType(Chain, "WeakObjNode", null, &.{}, null);
    };
    const before = thread.stats;

    const w_single = blk: {
        const o = objNew(&T.ty, Chain{ .own = .{ .val = 1, .next = null } });
        defer drop(o);
        break :blk try weakNew(Weak(?Obj), @as(?Obj, o));
    };
    try std.testing.expect(weakTryGet(w_single) == null);
    drop(w_single);

    const w_cycle = blk: {
        const a = rt.objAlloc(Chain, &T.ty);
        rt.objInitField(Part, &.{Part}, 0, a, 2);
        rt.objInitField(Part, &.{Part}, 1, a, @as(?Obj, dup(a)));
        defer drop(a);
        break :blk try weakNew(Weak(?Obj), @as(?Obj, a));
    };
    _ = collect();
    try std.testing.expect(weakTryGet(w_cycle) == null);
    drop(w_cycle);

    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "arrayFilterInPlace and FilterReuseBuf: unique shrink, capacity free, eql/compare/hash parity, and exception safety" {
    const before = thread.stats;
    const PredI32 = Func(*const fn (?*Env, i32) Raised!bool);
    const PredStr = Func(*const fn (?*Env, String) Raised!bool);
    const H = struct {
        fn lt3(_: ?*Env, x: i32) Raised!bool {
            return x < 3;
        }
        fn none(_: ?*Env, _: i32) Raised!bool {
            return false;
        }
        fn strFilterOrBoom(_: ?*Env, s: String) Raised!bool {
            defer drop(s);
            const u = unitsOf(s);
            if (u.len > 0 and u[0] == '3') return raise(ArgumentException, str("filter-boom"));
            return u.len > 0 and (u[0] == '0' or u[0] == '2');
        }
    };
    const pred_lt3: PredI32 = .{ .env = null, .code = H.lt3 };
    const pred_none: PredI32 = .{ .env = null, .code = H.none };
    const pred_boom: PredStr = .{ .env = null, .code = H.strFilterOrBoom };

    // Unique shrink 10 -> 3 -> 0, preserving capacity and matching fresh arrays for eql/compare/hash
    {
        const arr = arrayOf(Array(i32), .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 });
        const addr = @intFromPtr(arr);
        const reuses0 = thread.stats.reuses;

        const shrunk = try rt.arrayFilterInPlace(arr, pred_lt3);
        try std.testing.expectEqual(addr, @intFromPtr(shrunk));
        try std.testing.expectEqual(@as(usize, 3), shrunk.items.len);
        try std.testing.expectEqual(@as(usize, 10), shrunk.capacity);
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - reuses0);

        const fresh = arrayOf(Array(i32), .{ 0, 1, 2 });
        try std.testing.expect(eql(shrunk, fresh));
        try std.testing.expectEqual(@as(i32, 0), compare(shrunk, fresh));
        try std.testing.expectEqual(hash(fresh), hash(shrunk));

        const empty = try rt.arrayFilterInPlace(shrunk, pred_none);
        try std.testing.expectEqual(addr, @intFromPtr(empty));
        try std.testing.expectEqual(@as(usize, 0), empty.items.len);
        try std.testing.expectEqual(@as(usize, 10), empty.capacity);

        const fresh_empty = arrayOf(Array(i32), .{});
        try std.testing.expect(eql(empty, fresh_empty));
        try std.testing.expectEqual(@as(i32, 0), compare(empty, fresh_empty));
        try std.testing.expectEqual(hash(fresh_empty), hash(empty));

        dropAll(.{ empty, fresh, fresh_empty });
    }

    // Aliased array must not be reused or mutated in place
    {
        const a1 = arrayOf(Array(i32), .{ 1, 2, 3, 4 });
        const alias = dup(a1);
        const res = try rt.arrayFilterInPlace(a1, pred_lt3);
        try std.testing.expect(@intFromPtr(res) != @intFromPtr(alias));
        try std.testing.expectEqual(@as(usize, 4), alias.items.len);
        try std.testing.expectEqual(@as(usize, 2), res.items.len);
        dropAll(.{ alias, res });
    }

    // Weak-referenced array must clear weak_bit (not be reused in place) and notify weak handle
    {
        const a2 = arrayOf(Array(i32), .{ 1, 2, 3, 4 });
        const addr2 = @intFromPtr(a2);
        const w = try weakNew(Weak(Array(i32)), a2);
        const res2 = try rt.arrayFilterInPlace(a2, pred_lt3);
        try std.testing.expect(@intFromPtr(res2) != addr2);
        try std.testing.expect(weakTryGet(w) == null);
        dropAll(.{ res2, w });
    }

    // Mid-loop exception unwind on unique Array(String) frees remaining & filtered elements cleanly
    {
        const items = rt.arrayItems(Array(String), 5);
        items[0] = strConcat(str("0"), str("-heap"));
        items[1] = strConcat(str("1"), str("-heap"));
        items[2] = strConcat(str("2"), str("-heap"));
        items[3] = strConcat(str("3"), str("-heap"));
        items[4] = strConcat(str("4"), str("-heap"));
        const strs = arrayFrom(Array(String), items);
        try std.testing.expectError(error.Raised, rt.arrayFilterInPlace(strs, pred_boom));
        drop(take());
    }

    // Direct FilterReuseBuf mid-loop abandon on unique Array(String)
    {
        const items = rt.arrayItems(Array(String), 4);
        items[0] = strConcat(str("a"), str("-0"));
        items[1] = strConcat(str("b"), str("-1"));
        items[2] = strConcat(str("c"), str("-2"));
        items[3] = strConcat(str("d"), str("-3"));
        const strs = arrayFrom(Array(String), items);
        var fb = rt.arrayFilterBufNew(strs);
        try std.testing.expect(fb.in_place);
        try std.testing.expectEqual(@as(i32, 4), rt.arrayFilterBufLen(&fb));

        const x0 = rt.arrayFilterBufItem(&fb, 0);
        drop(x0);
        rt.arrayFilterBufStep(&fb, 0, true);

        const x1 = rt.arrayFilterBufItem(&fb, 1);
        drop(x1);
        rt.arrayFilterBufStep(&fb, 1, false);

        const x2 = rt.arrayFilterBufItem(&fb, 2);
        drop(x2);
        rt.arrayFilterBufAbandon(&fb);
    }

    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "arrayMapInPlace, arrayMapiInPlace, and MapBuf: same-type, cross-type layout, cyclic, mismatch, non-unique, and exception unwind" {
    const before = thread.stats;
    const FnI32 = Func(*const fn (?*Env, i32) Raised!i32);
    const FnI32F32 = Func(*const fn (?*Env, i32) Raised!f32);
    const FnI32I64 = Func(*const fn (?*Env, i32) Raised!i64);
    const FnObj = Func(*const fn (?*Env, ?Obj) Raised!?Obj);
    const FnStr = Func(*const fn (?*Env, String) Raised!String);
    const FnStrInner = Func(*const fn (?*Env, String) Raised!String);
    const FnMapiStr = Func(*const fn (?*Env, i32) Raised!FnStrInner);
    const BoxRecPtr = *struct { @"$rc": u32 = 1, v: i32 };
    const BoxRec = ?BoxRecPtr;
    const FnStrBox = Func(*const fn (?*Env, String) Raised!BoxRec);

    comptime {
        std.debug.assert(rt.arrays.canReuseArrayMap(Array(i32), Array(f32)));
        std.debug.assert(rt.arrays.canReuseArrayMap(Array(String), Array(BoxRec)));
        std.debug.assert(!rt.arrays.canReuseArrayMap(Array(i32), Array(i64)));
    }

    const H = struct {
        fn dbl(_: ?*Env, x: i32) Raised!i32 {
            return x * 2;
        }
        fn toF32(_: ?*Env, x: i32) Raised!f32 {
            return @as(f32, @floatFromInt(x)) + 0.5;
        }
        fn toI64(_: ?*Env, x: i32) Raised!i64 {
            return @as(i64, x) * 1000;
        }
        fn idObj(_: ?*Env, o: ?Obj) Raised!?Obj {
            return o;
        }
        fn mapiStrCode(_: ?*Env, _: i32) Raised!FnStrInner {
            return .{ .env = null, .code = struct {
                fn g(_: ?*Env, s: String) Raised!String {
                    return s;
                }
            }.g };
        }
        fn mapiStrCode2(_: ?*Env, i: i32, s: String) Raised!String {
            defer drop(s);
            return switch (i) {
                0 => strConcat(str("0:"), s),
                1 => strConcat(str("1:"), s),
                else => strConcat(str("2:"), s),
            };
        }
        fn strMapOrBoom(_: ?*Env, s: String) Raised!String {
            defer drop(s);
            if (unitsOf(s)[0] == '2') return raise(ArgumentException, str("map-str-boom"));
            return strConcat(str("ok-"), s);
        }
        fn strToBoxOrBoom(_: ?*Env, s: String) Raised!BoxRec {
            defer drop(s);
            if (unitsOf(s)[0] == '2') return raise(ArgumentException, str("map-box-boom"));
            return new(BoxRecPtr, .{ .v = @intCast(unitsOf(s).len) });
        }
    };

    const fn_dbl: FnI32 = .{ .env = null, .code = H.dbl };
    const fn_to_f32: FnI32F32 = .{ .env = null, .code = H.toF32 };
    const fn_to_i64: FnI32I64 = .{ .env = null, .code = H.toI64 };
    const fn_id_obj: FnObj = .{ .env = null, .code = H.idObj };
    const fn_mapi_str: FnMapiStr = .{ .env = null, .code = H.mapiStrCode, .code2 = H.mapiStrCode2 };
    const fn_str_boom: FnStr = .{ .env = null, .code = H.strMapOrBoom };
    const fn_box_boom: FnStrBox = .{ .env = null, .code = H.strToBoxOrBoom };

    // 1. Same-type i32 -> i32 in place
    {
        const a = arrayOf(Array(i32), .{ 1, 2, 3, 4 });
        const addr = @intFromPtr(a);
        const reuses0 = thread.stats.reuses;
        const b = try rt.arrayMapInPlace(Array(i32), a, fn_dbl);
        try std.testing.expectEqual(addr, @intFromPtr(b));
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - reuses0);
        try std.testing.expectEqualSlices(i32, &.{ 2, 4, 6, 8 }, b.items);
        drop(b);
    }

    // 2. Same-type String -> String via arrayMapiInPlace
    {
        const items = rt.arrayItems(Array(String), 3);
        items[0] = strConcat(str("a"), str("a"));
        items[1] = strConcat(str("b"), str("b"));
        items[2] = strConcat(str("c"), str("c"));
        const a = arrayFrom(Array(String), items);
        const addr = @intFromPtr(a);
        const reuses0 = thread.stats.reuses;
        const b = try rt.arrayMapiInPlace(Array(String), a, fn_mapi_str);
        try std.testing.expectEqual(addr, @intFromPtr(b));
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - reuses0);
        try expectText("0:aa", dup(b.items[0]));
        try expectText("1:bb", dup(b.items[1]));
        try expectText("2:cc", dup(b.items[2]));
        drop(b);
    }

    // 3. Cross-type same-layout i32 -> f32 in place
    {
        const a = arrayOf(Array(i32), .{ 1, 2, 3 });
        const addr = @intFromPtr(a);
        const reuses0 = thread.stats.reuses;
        const b = try rt.arrayMapInPlace(Array(f32), a, fn_to_f32);
        try std.testing.expectEqual(addr, @intFromPtr(b));
        if (rt.track) try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - reuses0);
        try std.testing.expectEqualSlices(f32, &.{ 1.5, 2.5, 3.5 }, b.items);
        drop(b);
    }

    // 4. Layout mismatch i32 -> i64 falls back to fresh allocation
    {
        const a = arrayOf(Array(i32), .{ 1, 2, 3 });
        const addr = @intFromPtr(a);
        const b = try rt.arrayMapInPlace(Array(i64), a, fn_to_i64);
        try std.testing.expect(@intFromPtr(b) != addr);
        try std.testing.expectEqualSlices(i64, &.{ 1000, 2000, 3000 }, b.items);
        drop(b);
    }

    // 5. Cyclic Array(?Obj) -> Array(?Obj) in place (forget + reinit GcHdr)
    {
        const items = rt.arrayItems(Array(?Obj), 3);
        items[0] = rt.objectNew();
        items[1] = rt.objectNew();
        items[2] = rt.objectNew();
        const a = arrayFrom(Array(?Obj), items);
        const addr = @intFromPtr(a);
        const b = try rt.arrayMapInPlace(Array(?Obj), a, fn_id_obj);
        try std.testing.expectEqual(addr, @intFromPtr(b));
        try std.testing.expectEqual(@as(usize, 3), b.items.len);
        drop(b);
    }

    // 6. Non-unique fallbacks: aliased, shared, weak-referenced, and null
    {
        const a_alias = arrayOf(Array(i32), .{ 2, 4 });
        const kept = dup(a_alias);
        const m_alias = try rt.arrayMapInPlace(Array(i32), a_alias, fn_dbl);
        try std.testing.expect(@intFromPtr(m_alias) != @intFromPtr(kept));
        try std.testing.expectEqualSlices(i32, &.{ 2, 4 }, kept.items);
        try std.testing.expectEqualSlices(i32, &.{ 4, 8 }, m_alias.items);
        dropAll(.{ kept, m_alias });

        const a_shared = arrayOf(Array(i32), .{ 3, 5 });
        const shared_addr = @intFromPtr(a_shared);
        try markShared(a_shared);
        const m_shared = try rt.arrayMapInPlace(Array(i32), a_shared, fn_dbl);
        try std.testing.expect(@intFromPtr(m_shared) != shared_addr);
        try std.testing.expectEqualSlices(i32, &.{ 6, 10 }, m_shared.items);
        drop(m_shared);

        const a_weak = arrayOf(Array(i32), .{ 7, 9 });
        const weak_addr = @intFromPtr(a_weak);
        const w = try weakNew(Weak(Array(i32)), a_weak);
        const m_weak = try rt.arrayMapInPlace(Array(i32), a_weak, fn_dbl);
        try std.testing.expect(@intFromPtr(m_weak) != weak_addr);
        try std.testing.expect(weakTryGet(w) == null);
        dropAll(.{ m_weak, w });

        const a_null = rt.arrayNull(Array(i32));
        try std.testing.expect(!isUnique(a_null));
        const m_null = try rt.arrayMapInPlace(Array(i32), a_null, fn_dbl);
        try std.testing.expect(@intFromPtr(m_null) != @intFromPtr(a_null));
        try std.testing.expectEqual(@as(usize, 0), m_null.items.len);
        drop(m_null);
    }

    // 7. Mid-loop exception unwind on same-type String -> String and cross-type String -> BoxRec
    {
        const items1 = rt.arrayItems(Array(String), 5);
        items1[0] = strConcat(str("0"), str("-s"));
        items1[1] = strConcat(str("1"), str("-s"));
        items1[2] = strConcat(str("2"), str("-s"));
        items1[3] = strConcat(str("3"), str("-s"));
        items1[4] = strConcat(str("4"), str("-s"));
        const a1 = arrayFrom(Array(String), items1);
        try std.testing.expectError(error.Raised, rt.arrayMapInPlace(Array(String), a1, fn_str_boom));
        drop(take());

        const items2 = rt.arrayItems(Array(String), 4);
        items2[0] = strConcat(str("0"), str("-box"));
        items2[1] = strConcat(str("1"), str("-box"));
        items2[2] = strConcat(str("2"), str("-box"));
        items2[3] = strConcat(str("3"), str("-box"));
        const a2 = arrayFrom(Array(String), items2);
        try std.testing.expectError(error.Raised, rt.arrayMapInPlace(Array(BoxRec), a2, fn_box_boom));
        drop(take());
    }

    // 8. Direct MapBuf mid-loop abandon on unique Array(String)
    {
        const items = rt.arrayItems(Array(String), 4);
        items[0] = strConcat(str("m"), str("0"));
        items[1] = strConcat(str("m"), str("1"));
        items[2] = strConcat(str("m"), str("2"));
        items[3] = strConcat(str("m"), str("3"));
        const a = arrayFrom(Array(String), items);
        var buf = rt.arrayMapBufNew(a, Array(String));
        try std.testing.expect(buf.in_place);
        try std.testing.expectEqual(@as(i32, 4), rt.arrayMapBufLen(&buf));

        const x0 = rt.arrayMapBufTake(&buf, 0);
        rt.arrayMapBufPush(strConcat(x0, str("!")), &buf);
        drop(x0);

        const x1 = rt.arrayMapBufTake(&buf, 1);
        drop(x1);
        rt.arrayMapBufAbandon(&buf);
    }

    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "arraySortByKeys and arraySortInPlaceByKeys: stability, desc, managed keys/values, zero RC moves, shared array" {
    const before = thread.stats;
    {
        const A = Array(String);
        const arr_items = rt.arrayItems(A, 5);
        arr_items[0] = strConcat(str("b-"), str("0"));
        arr_items[1] = strConcat(str("a-"), str("0"));
        arr_items[2] = strConcat(str("b-"), str("1"));
        arr_items[3] = strConcat(str("a-"), str("1"));
        arr_items[4] = strConcat(str("c-"), str("0"));
        const arr = arrayFrom(A, arr_items);
        defer drop(arr);

        const key_items = rt.arrayItems(A, 5);
        key_items[0] = strConcat(str("k"), str("b"));
        key_items[1] = strConcat(str("k"), str("a"));
        key_items[2] = strConcat(str("k"), str("b"));
        key_items[3] = strConcat(str("k"), str("a"));
        key_items[4] = strConcat(str("k"), str("c"));
        const keys = arrayFrom(A, key_items);
        defer drop(keys);

        const keys_asc = arrayCopy(keys);
        const asc = rt.arraySortByKeys(keys_asc, arr, false);
        drop(keys_asc);
        try expectText("a-0", dup(asc.items[0]));
        try expectText("a-1", dup(asc.items[1]));
        try expectText("b-0", dup(asc.items[2]));
        try expectText("b-1", dup(asc.items[3]));
        try expectText("c-0", dup(asc.items[4]));
        drop(asc);

        const keys_desc = arrayCopy(keys);
        const desc = rt.arraySortByKeys(keys_desc, arr, true);
        drop(keys_desc);
        try expectText("c-0", dup(desc.items[0]));
        try expectText("b-0", dup(desc.items[1]));
        try expectText("b-1", dup(desc.items[2]));
        try expectText("a-0", dup(desc.items[3]));
        try expectText("a-1", dup(desc.items[4]));
        drop(desc);

        // In-place sortByKeys swaps elements without RC retain/drop traffic beyond temp work slices
        const arr_inplace = arrayCopy(arr);
        const keys_inplace = arrayCopy(keys);
        const s0 = thread.stats;
        rt.arraySortInPlaceByKeys(keys_inplace, arr_inplace, false);
        try std.testing.expectEqual(@as(i64, 0), thread.stats.dups - s0.dups);
        try std.testing.expectEqual(@as(i64, 0), thread.stats.allocs - s0.allocs);
        try std.testing.expectEqual(@as(i64, 0), thread.stats.frees - s0.frees);
        try expectText("a-0", dup(arr_inplace.items[0]));
        try expectText("a-1", dup(arr_inplace.items[1]));
        try expectText("b-0", dup(arr_inplace.items[2]));
        try expectText("b-1", dup(arr_inplace.items[3]));
        try expectText("c-0", dup(arr_inplace.items[4]));
        dropAll(.{ arr_inplace, keys_inplace });

        // Shared array in-place sortByKeys descends stably
        const arr_shared = arrayCopy(arr);
        const keys_shared = arrayCopy(keys);
        try markShared(arr_shared);
        rt.arraySortInPlaceByKeys(keys_shared, arr_shared, true);
        try expectText("c-0", arrayItemAt(arr_shared, 0));
        try expectText("b-0", arrayItemAt(arr_shared, 1));
        try expectText("b-1", arrayItemAt(arr_shared, 2));
        try expectText("a-0", arrayItemAt(arr_shared, 3));
        try expectText("a-1", arrayItemAt(arr_shared, 4));
        dropAll(.{ arr_shared, keys_shared });
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "invokeIfaceK, unwrapIfaceK, and checkNonNull: KnownIface fast path, Iface fallback, and error unwind" {
    const before = thread.stats;
    {
        const ICmp = Iface(IfaceAnon1(.{"Compare"}).of(*const fn (?*anyopaque, String, String) Raised!i32));
        const Caps = struct { bias: i32 };
        const KCmp = struct {
            pub const fable_known = {};
            pub const fable_known_iface = {};
            pub const FuncType = ?ICmp;
            caps: Caps,
            pub const @"slot_Compare$borrows" = .{ true, true };
            pub const @"slot_Compare$result_borrowed" = false;
            pub inline fn slot_Compare(self: *const @This(), a: String, b: String) Raised!i32 {
                if (unitsOf(a).len == 0) return raise(ArgumentException, str("empty-compare"));
                return compare(a, b) + self.caps.bias;
            }
            pub fn toFunc(self: @This()) FuncType {
                const Adapter = struct {
                    fn cmp(env: ?*anyopaque, a: String, b: String) Raised!i32 {
                        defer dropAll(.{ a, b });
                        const c = captured(Caps, @ptrCast(@alignCast(env.?)));
                        if (unitsOf(a).len == 0) return raise(ArgumentException, str("empty-compare"));
                        return compare(a, b) + c.bias;
                    }
                    const vt: @typeInfo(@FieldType(ICmp, "vt")).pointer.child = .{
                        .@"$meta" = &env_iface_meta,
                        .Compare = cmp,
                    };
                };
                return ifaceClosure(ICmp, Caps, self.caps, &Adapter.vt);
            }
        };

        const s1 = strConcat(str("aa"), str("b"));
        const s2 = strConcat(str("aa"), str("a"));
        const s3 = strConcat(str("cc"), str("c"));
        const held = strConcat(str("he"), str("ld"));
        defer dropAll(.{ s1, s2, s3 });

        const k = KCmp{ .caps = .{ .bias = 10 } };
        try rt.checkNonNull(k);
        const u_k = rt.unwrapIfaceK(k);
        const allocs0 = thread.stats.allocs;
        const r_k = try rt.invokeIfaceK(i32, u_k, "Compare", "kk", .{ s1, s2 }, .{});
        try std.testing.expectEqual(@as(i32, 11), r_k);
        try std.testing.expectEqual(allocs0, thread.stats.allocs);

        // KnownIface error unwind drops consumed ('g') borrowed args and err_drops
        const empty_s1 = strConcat(str(""), str(""));
        try std.testing.expectError(error.Raised, rt.invokeIfaceK(i32, u_k, "Compare", "gk", .{ empty_s1, s2 }, .{dup(held)}));
        drop(take());

        // Ordinary ?ICmp fallback
        const iface: ?ICmp = k.toFunc();
        defer drop(iface);
        try rt.checkNonNull(iface);
        const u_i = rt.unwrapIfaceK(iface);
        const r_i = try rt.invokeIfaceK(i32, u_i, "Compare", "gk", .{ dup(s3), s2 }, .{});
        try std.testing.expectEqual(@as(i32, 12), r_i);

        const empty_s2 = strConcat(str(""), str(""));
        try std.testing.expectError(error.Raised, rt.invokeIfaceK(i32, u_i, "Compare", "gk", .{ empty_s2, s2 }, .{held}));
        drop(take());

        // Null optional interface triggers NullReferenceException
        try std.testing.expectError(error.Raised, rt.checkNonNull(@as(?ICmp, null)));
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "Iso.tryPack atomic non-mutation preserves shared_bit on failure" {
    const before = thread.stats;
    const Pair = struct { clean: Obj, extra: Obj };
    {
        const clean = rt.objectNew();
        const a = testPerson(10);
        const b = testPerson(11);
        storeIn(a, "friend", dup(b));
        storeIn(b, "friend", dup(a));
        drop(b);
        const boxed_cyc = ifaceBox(
            Iface(struct { @"$meta": *const IfaceMeta }),
            TestPerson,
            a,
            &.{ .@"$meta" = &rt.box_iface_meta },
        );
        const cyc_obj: Obj = @ptrCast(@alignCast(boxed_cyc.data.?));
        const res = rt.isoTryPack(Pair).call(.{ .clean = clean, .extra = cyc_obj });
        try std.testing.expect(res[0] == null);
        const kept = res[1].?;
        // Atomic 2-phase ShareProbe must leave clean unshared when the second element fails.
        try std.testing.expect(!rt.isShared(kept.clean));
        try std.testing.expect(!rt.isShared(kept.extra));
        drop(kept.extra);
        _ = collect();
        const res_ok = rt.isoTryPack(Obj).call(kept.clean);
        try std.testing.expect(res_ok[0] != null);
        const unpacked = try rt.isoUnpack(res_ok[0].?);
        drop(res_ok[0].?);
        drop(unpacked);
    }
    {
        const PairStr = struct { clean: Obj, text: String };
        const clean = rt.objectNew();
        var buf: [2048]u8 = undefined;
        var fba = std.heap.FixedBufferAllocator.init(&buf);
        var frame: rt.Arena = undefined;
        rt.arenaEnter(&frame, &fba);
        const arena_s = strConcat(str("ar_"), str("s"));
        const res = rt.isoTryPack(PairStr).call(.{ .clean = clean, .text = arena_s });
        try std.testing.expect(res[0] == null);
        const kept = res[1].?;
        try std.testing.expect(!rt.isShared(kept.clean));
        drop(kept.text);
        rt.arenaLeave(&frame);
        const res_ok = rt.isoTryPack(Obj).call(kept.clean);
        try std.testing.expect(res_ok[0] != null);
        const unpacked = try rt.isoUnpack(res_ok[0].?);
        drop(res_ok[0].?);
        drop(unpacked);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "Iso.pack supports all 5 IfaceMeta kinds across OS thread" {
    if (!sgc.per_thread) return;
    const before = thread.stats;
    const IVt = struct {
        @"$meta": *const IfaceMeta,
        get: *const fn (?*anyopaque) i32,
    };
    const IVal = Iface(IVt);
    const ISubVt = struct {
        @"$meta": *const IfaceMeta,
        val: *const fn (?*anyopaque) i32,
    };
    const ISub = Iface(ISubVt);
    const All5 = struct {
        empty: IVal,
        obj: IVal,
        box: IVal,
        env: IVal,
        upcast: IVal,
    };
    const ObjCls = struct {
        const Part = struct { n: i32 };
        const Chain = struct { own: Part };
        const ty: ObjType = objType(Chain, "IsoAll5+ObjCls", null, &.{}, null);
    };
    const EnvCap = struct { s: String, n: i32 };
    const SubCap = struct { s: String, v: i32 };

    const empty_vt: IVt = .{
        .@"$meta" = &empty_iface_meta,
        .get = struct {
            fn f(_: ?*anyopaque) i32 {
                return 1;
            }
        }.f,
    };
    const obj_vt: IVt = .{
        .@"$meta" = &obj_iface_meta,
        .get = struct {
            fn f(d: ?*anyopaque) i32 {
                const o: Obj = @ptrCast(@alignCast(d.?));
                return rt.objPart(*ObjCls.Part, &.{ObjCls.Part}, o).n;
            }
        }.f,
    };
    const box_vt: IVt = .{
        .@"$meta" = &rt.box_iface_meta,
        .get = struct {
            fn f(d: ?*anyopaque) i32 {
                const o: Obj = @ptrCast(@alignCast(d.?));
                return rt.boxed(i32, o).value;
            }
        }.f,
    };
    const env_vt: IVt = .{
        .@"$meta" = &env_iface_meta,
        .get = struct {
            fn f(d: ?*anyopaque) i32 {
                const e: *Env = @ptrCast(@alignCast(d.?));
                return captured(EnvCap, e).n;
            }
        }.f,
    };
    const sub_vt: ISubVt = .{
        .@"$meta" = &env_iface_meta,
        .val = struct {
            fn f(d: ?*anyopaque) i32 {
                const e: *Env = @ptrCast(@alignCast(d.?));
                return captured(SubCap, e).v;
            }
        }.f,
    };
    const upcast_vt: IVt = .{
        .@"$meta" = upcastIfaceMeta(ISub),
        .get = struct {
            fn f(d: ?*anyopaque) i32 {
                const o: Obj = @ptrCast(@alignCast(d.?));
                const s = rt.boxed(ISub, o).value;
                return s.vt.val(s.data);
            }
        }.f,
    };

    const i_empty: IVal = .{ .data = null, .vt = &empty_vt };
    const i_obj: IVal = .{
        .data = @ptrCast(objNew(&ObjCls.ty, ObjCls.Chain{ .own = .{ .n = 2 } })),
        .vt = &obj_vt,
    };
    const i_box = ifaceBox(IVal, i32, 3, &box_vt);
    const i_env = ifaceClosure(IVal, EnvCap, .{ .s = strConcat(str("env_"), str("cap")), .n = 4 }, &env_vt);
    const sub = ifaceClosure(ISub, SubCap, .{ .s = strConcat(str("sub_"), str("cap")), .v = 5 }, &sub_vt);
    const i_upcast = ifaceBox(IVal, ISub, sub, &upcast_vt);

    const packed_iso = try rt.isoPack(All5).call(.{
        .empty = i_empty,
        .obj = i_obj,
        .box = i_box,
        .env = i_env,
        .upcast = i_upcast,
    });
    const Shared = struct { iso: rt.Iso(All5), sum: i32 = 0, worker_bal: i64 = 0 };
    var sh: Shared = .{ .iso = packed_iso };
    const t = try std.Thread.spawn(.{}, struct {
        fn work(s: *Shared) void {
            const w_before = thread.stats;
            const v = rt.isoUnpack(s.iso) catch unreachable;
            drop(s.iso);
            s.sum = v.empty.vt.get(v.empty.data) +
                v.obj.vt.get(v.obj.data) +
                v.box.vt.get(v.box.data) +
                v.env.vt.get(v.env.data) +
                v.upcast.vt.get(v.upcast.data);
            drop(v);
            s.worker_bal = (thread.stats.allocs - w_before.allocs) - (thread.stats.frees - w_before.frees);
            rt.collectorDeinit();
        }
    }.work, .{&sh});
    t.join();
    const main_bal = (thread.stats.allocs - before.allocs) - (thread.stats.frees - before.frees);
    try std.testing.expectEqual(@as(i32, 15), sh.sum);
    try std.testing.expectEqual(@as(i64, -8), sh.worker_bal);
    try std.testing.expectEqual(@as(i64, 0), main_bal + sh.worker_bal);
}

test "Iso.pack calls finishCheck on active collector check and respects collectorPause" {
    _ = collect();
    const before = thread.stats;
    const a = testPerson(1);
    const b = testPerson(2);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(a));
    // Start an incremental check on this thread's live cycle structure while holding a and b.
    try std.testing.expect(thread.collector.startRun(true));
    try std.testing.expect(thread.collector.phase != .idle);
    drop(b);

    // packOrNull finishes the in-progress check before walking and succeeds.
    const r0 = rt.isoTryPack(TestPerson).call(a);
    try std.testing.expect(r0[0] != null);
    try std.testing.expectEqual(sgc.Phase.idle, thread.collector.phase);
    const a_back = try rt.isoUnpack(r0[0].?);
    drop(r0[0].?);

    // With noCollectEnter active, finishCheck respects collectorPause and refuses the move.
    try std.testing.expect(thread.collector.startRun(true));
    try std.testing.expect(thread.collector.phase != .idle);
    collectorPause();
    const r1 = rt.isoTryPack(TestPerson).call(a_back);
    try std.testing.expect(r1[0] == null);
    try std.testing.expect(thread.collector.phase != .idle);
    collectorResume();

    // Once resumed, finishCheck drives the paused check to idle and packs cleanly.
    const r2 = rt.isoTryPack(TestPerson).call(r1[1].?);
    try std.testing.expect(r2[0] != null);
    try std.testing.expectEqual(sgc.Phase.idle, thread.collector.phase);
    const a_final = try rt.isoUnpack(r2[0].?);
    drop(r2[0].?);
    drop(a_final);
    _ = collect();
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "StackArena concurrent entry across OS threads is race-free" {
    if (!sgc.per_thread) return;
    const ArenaWorker = struct {
        fn nestedInner(n: i32) !i32 {
            var ibuf: [2048]u8 = undefined;
            var ifba = std.heap.FixedBufferAllocator.init(&ibuf);
            var iframe: rt.Arena = undefined;
            rt.arenaEnter(&iframe, &ifba);
            const s = strConcat(str("inner_"), str("ok"));
            const arr = rt.arrayCreate(Array(i32), 4, n) catch unreachable;
            const total = @as(i32, @intCast(unitsOf(s).len)) + arr.items[0];
            drop(arr);
            drop(s);
            rt.arenaLeave(&iframe);
            return total;
        }
        fn runArena(out: *i64) void {
            const b = thread.stats;
            var obuf: [4096]u8 = undefined;
            var ofba = std.heap.FixedBufferAllocator.init(&obuf);
            var oframe: rt.Arena = undefined;
            rt.arenaEnter(&oframe, &ofba);
            var round: i32 = 0;
            var acc: i32 = 0;
            while (round < 25) : (round += 1) {
                const s = strConcat(str("outer_"), str("x"));
                acc += nestedInner(round) catch unreachable;
                drop(s);
            }
            rt.arenaLeave(&oframe);
            const arr = rt.arrayCreate(Array(i32), 3, acc) catch unreachable;
            drop(arr);
            rt.collectorDeinit();
            out.* = (thread.stats.allocs - b.allocs) - (thread.stats.frees - b.frees);
        }
        fn runHeap(out: *i64) void {
            const b = thread.stats;
            var round: i32 = 0;
            while (round < 50) : (round += 1) {
                const s = strConcat(str("heap_"), str("y"));
                const arr = rt.arrayCreate(Array(i32), 5, round) catch unreachable;
                drop(arr);
                drop(s);
            }
            rt.collectorDeinit();
            out.* = (thread.stats.allocs - b.allocs) - (thread.stats.frees - b.frees);
        }
    };
    var balances: [8]i64 = @splat(-1);
    var threads: [8]std.Thread = undefined;
    for (0..6) |i| threads[i] = try std.Thread.spawn(.{}, ArenaWorker.runArena, .{&balances[i]});
    for (6..8) |i| threads[i] = try std.Thread.spawn(.{}, ArenaWorker.runHeap, .{&balances[i]});
    for (threads) |t| t.join();
    for (balances) |bal| try std.testing.expectEqual(@as(i64, 0), bal);
}

test "collectorDeinit drains local cycles and records ThreadExitSgcStats" {
    if (!sgc.per_thread) return;
    const before_stats = rt.threadExitSgcStats();
    const t = try std.Thread.spawn(.{}, struct {
        fn work() void {
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
            std.debug.assert(thread.collector.dying_cells > 0 or thread.collector.n_live > 0);
            rt.collectorDeinit();
        }
    }.work, .{});
    t.join();
    const after_stats = rt.threadExitSgcStats();
    try std.testing.expect(after_stats.threads_drained >= before_stats.threads_drained + 1);
    try std.testing.expect(after_stats.collected_on_exit >= before_stats.collected_on_exit + 2);
    try std.testing.expectEqual(before_stats.remaining_structures_on_exit, after_stats.remaining_structures_on_exit);
}

test "markShared and Iso.pack produce actionable diagnostic messages" {
    const before = thread.stats;
    const textContains = struct {
        fn call(s: String, needle: []const u8) bool {
            var buf: [1024]u8 = undefined;
            const n = std.unicode.wtf16LeToWtf8(&buf, unitsOf(s));
            return std.mem.indexOf(u8, buf[0..n], needle) != null;
        }
    }.call;
    // 1. Cyclic structure shared with markShared
    {
        const a = testPerson(1);
        const b = testPerson(2);
        storeIn(a, "friend", dup(b));
        storeIn(b, "friend", dup(a));
        drop(b);
        try std.testing.expectError(error.Raised, rt.markShared(a));
        const e = take();
        defer drop(e);
        try std.testing.expect(rt.NotSupportedException.is(e));
        const msg = exnMessage(e);
        defer drop(msg);
        try std.testing.expect(textContains(msg, "fable_sgc"));
        try std.testing.expect(textContains(msg, "Iso.pack"));
        try std.testing.expect(textContains(msg, "WeakReference"));
        drop(a);
        _ = collect();
    }
    // 2. Aliased value passed to isoPack
    {
        const L = List(i32);
        const xs = L{ .Cons = cell(L, .Cons, .{ .Head = 1, .Tail = .Empty }) };
        const alias = dup(xs);
        defer drop(alias);
        try std.testing.expectError(error.Raised, rt.isoPack(L).call(xs));
        const e = take();
        defer drop(e);
        try std.testing.expect(rt.InvalidOperationException.is(e));
        const msg = exnMessage(e);
        defer drop(msg);
        try std.testing.expect(textContains(msg, "another live reference"));
    }
    // 3. StackArena string passed to isoPack
    {
        var buf: [2048]u8 = undefined;
        var fba = std.heap.FixedBufferAllocator.init(&buf);
        var frame: rt.Arena = undefined;
        rt.arenaEnter(&frame, &fba);
        const ar_s = strConcat(str("stack_"), str("s"));
        try std.testing.expectError(error.Raised, rt.isoPack(String).call(ar_s));
        const e = take();
        try std.testing.expect(rt.InvalidOperationException.is(e));
        const msg = exnMessage(e);
        try std.testing.expect(textContains(msg, "[<StackArena>]"));
        drop(msg);
        drop(e);
        rt.arenaLeave(&frame);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "poolStart / poolJoin / poolShutdown stress & zero-leak" {
    if (!rt.sgc.per_thread) return;
    const before_live = rt.live();
    const Ctx = struct {
        sum: *std.atomic.Value(i64),
        val: i32,
        text: String,
    };
    const L = List(i32);
    var total = std.atomic.Value(i64).init(0);
    var threads: [200]rt.ThreadOf = undefined;
    for (0..200) |i| {
        const s = strConcat(str("p_"), str("item"));
        const f = closure(
            rt.ThreadStart,
            Ctx,
            .{ .sum = &total, .val = @intCast(i + 1), .text = s },
            struct {
                fn call(env: ?*Env, _: void) Raised!void {
                    const c = captured(Ctx, env);
                    const xs = L{ .Cons = cell(L, .Cons, .{ .Head = c.val, .Tail = L{ .Cons = cell(L, .Cons, .{ .Head = @intCast(unitsOf(c.text).len), .Tail = .Empty }) } }) };
                    defer drop(xs);
                    _ = c.sum.fetchAdd(@as(i64, xs.Cons.Head) + @as(i64, xs.Cons.Tail.Cons.Head), .acq_rel);
                }
            }.call,
        );
        threads[i] = try rt.poolStart(f);
        drop(f);
    }
    for (threads) |t| {
        rt.threadJoin(t);
        drop(t);
    }
    rt.poolShutdown();
    _ = collect();
    // sum(1..200) + 200 * 6 = 20100 + 1200 = 21300
    try std.testing.expectEqual(@as(i64, 21300), total.load(.acquire));
    try std.testing.expectEqual(before_live, rt.live());
}

test "pool nested tasks (> max_pool_workers) never deadlock" {
    if (!rt.sgc.per_thread) return;
    const before_live = rt.live();
    const InnerCtx = struct { done: *std.atomic.Value(i32) };
    const OuterCtx = struct { done: *std.atomic.Value(i32) };
    var count = std.atomic.Value(i32).init(0);
    var outers: [12]rt.ThreadOf = undefined;
    for (0..12) |i| {
        const f = closure(
            rt.ThreadStart,
            OuterCtx,
            .{ .done = &count },
            struct {
                fn outer(env: ?*Env, _: void) Raised!void {
                    const c = captured(OuterCtx, env);
                    const inf = closure(
                        rt.ThreadStart,
                        InnerCtx,
                        .{ .done = c.done },
                        struct {
                            fn inner(ienv: ?*Env, _: void) Raised!void {
                                _ = captured(InnerCtx, ienv).done.fetchAdd(1, .acq_rel);
                            }
                        }.inner,
                    );
                    const it = try rt.poolStart(inf);
                    drop(inf);
                    rt.threadJoin(it);
                    drop(it);
                    _ = c.done.fetchAdd(1, .acq_rel);
                }
            }.outer,
        );
        outers[i] = try rt.poolStart(f);
        drop(f);
    }
    for (outers) |t| {
        rt.threadJoin(t);
        drop(t);
    }
    rt.poolShutdown();
    _ = collect();
    try std.testing.expectEqual(@as(i32, 24), count.load(.acquire));
    try std.testing.expectEqual(before_live, rt.live());
}

test "poolRunWorkers concurrent execution & error propagation" {
    if (!rt.sgc.per_thread) return;
    const before_live = rt.live();
    const Ctx = struct { n: *std.atomic.Value(i32) };
    var n = std.atomic.Value(i32).init(0);
    {
        const f = closure(rt.ThreadStart, Ctx, .{ .n = &n }, struct {
            fn work(env: ?*Env, _: void) Raised!void {
                _ = captured(Ctx, env).n.fetchAdd(1, .acq_rel);
            }
        }.work);
        defer drop(f);
        try rt.poolRunWorkers(4, f);
    }
    try std.testing.expectEqual(@as(i32, 4), n.load(.acquire));

    const FailCtx = struct { seq: *std.atomic.Value(i32) };
    var seq = std.atomic.Value(i32).init(0);
    {
        const f = closure(rt.ThreadStart, FailCtx, .{ .seq = &seq }, struct {
            fn work(env: ?*Env, _: void) Raised!void {
                const idx = captured(FailCtx, env).seq.fetchAdd(1, .acq_rel);
                if (idx == 0) return raise(rt.Failure, str("pool worker boom"));
            }
        }.work);
        defer drop(f);
        try std.testing.expectError(error.Raised, rt.poolRunWorkers(4, f));
        drop(take());
    }
    rt.poolShutdown();
    _ = collect();
    try std.testing.expectEqual(before_live, rt.live());
}

test "threadStart moves t.start out and transfers unique captures unshared" {
    if (!rt.sgc.per_thread) return;
    const before_live = rt.live();
    const L = List(i32);
    const Cap = struct { xs: L, was_shared: *bool };

    // Case A: unique capture arrives unshared
    var out_a: bool = true;
    {
        const xs = L{ .Cons = cell(L, .Cons, .{ .Head = 42, .Tail = .Empty }) };
        const f = closure(rt.ThreadStart, Cap, .{ .xs = xs, .was_shared = &out_a }, struct {
            fn run(env: ?*Env, _: void) Raised!void {
                const c = captured(Cap, env);
                c.was_shared.* = rt.isShared(c.xs.Cons);
            }
        }.run);
        const t = rt.threadNew(f);
        drop(f);
        try rt.threadStart(t);
        rt.threadJoin(t);
        drop(t);
    }
    try std.testing.expectEqual(false, out_a);

    // Case B: aliased capture (rc == 2) is marked shared
    var out_b: bool = false;
    {
        const ys = L{ .Cons = cell(L, .Cons, .{ .Head = 99, .Tail = .Empty }) };
        const ys_alias = dup(ys);
        defer drop(ys_alias);
        const f = closure(rt.ThreadStart, Cap, .{ .xs = ys, .was_shared = &out_b }, struct {
            fn run(env: ?*Env, _: void) Raised!void {
                const c = captured(Cap, env);
                c.was_shared.* = rt.isShared(c.xs.Cons);
            }
        }.run);
        const t = rt.threadNew(f);
        drop(f);
        try rt.threadStart(t);
        rt.threadJoin(t);
        drop(t);
    }
    try std.testing.expectEqual(true, out_b);

    // Case C: StackArena capture rejected cleanly without leaking
    {
        const StrCap = struct { s: String };
        var buf: [2048]u8 = undefined;
        var fba = std.heap.FixedBufferAllocator.init(&buf);
        var frame: rt.Arena = undefined;
        rt.arenaEnter(&frame, &fba);
        const ar_s = strConcat(str("th_"), str("arena"));
        const f = closure(rt.ThreadStart, StrCap, .{ .s = ar_s }, struct {
            fn run(_: ?*Env, _: void) Raised!void {}
        }.run);
        const t = rt.threadNew(f);
        drop(f);
        try std.testing.expectError(error.Raised, rt.threadStart(t));
        const e = take();
        try std.testing.expect(rt.NotSupportedException.is(e));
        drop(e);
        drop(t);
        rt.arenaLeave(&frame);
    }
    _ = collect();
    try std.testing.expectEqual(before_live, rt.live());
}

test "poolShutdown drains local fable_sgc cycles on workers" {
    if (!rt.sgc.per_thread) return;
    const before_live = rt.live();
    const before_stats = rt.threadExitSgcStats();
    const f = closure(
        rt.ThreadStart,
        struct {},
        .{},
        struct {
            fn run(_: ?*Env, _: void) Raised!void {
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
                std.debug.assert(thread.collector.dying_cells > 0 or thread.collector.n_live > 0);
            }
        }.run,
    );
    const t = try rt.poolStart(f);
    drop(f);
    rt.threadJoin(t);
    drop(t);
    rt.poolShutdown();
    _ = collect();
    const after_stats = rt.threadExitSgcStats();
    try std.testing.expect(after_stats.threads_drained >= before_stats.threads_drained + 1);
    try std.testing.expect(after_stats.collected_on_exit >= before_stats.collected_on_exit + 3);
    try std.testing.expectEqual(before_stats.remaining_structures_on_exit, after_stats.remaining_structures_on_exit);
    try std.testing.expectEqual(before_live, rt.live());
}

test "ffi NativePtr, StackAlloc, and spanOfPtr" {
    var stack: rt.StackAlloc = .{};
    defer stack.deinit();
    const p: ?[*]i32 = try stack.alloc(i32, 4);
    try std.testing.expect(p != null);
    rt.ptrWrite(p, 10);
    rt.ptrSet(p, 1, 20);
    const p2 = rt.ptrAdd(p, 2);
    rt.ptrWrite(p2, 30);
    try std.testing.expectEqual(@as(i32, 20), rt.ptrGet(p2, -1));
    try std.testing.expectEqual(@as(i32, 10), rt.ptrRead(p));
    rt.ptrSet(p, 3, 40);
    // Overlapping forward & backward copies
    rt.ptrCopy(rt.ptrAdd(p, 1), p, 2);
    try std.testing.expectEqual(@as(i32, 10), rt.ptrGet(p, 1));
    try std.testing.expectEqual(@as(i32, 20), rt.ptrGet(p, 2));
    rt.ptrInitBlock(@as(?[*]u8, @ptrCast(p.?)), 0xAB, 4);
    try std.testing.expectEqual(@as(u8, 0xAB), @as([*]const u8, @ptrCast(p.?))[3]);
    rt.ptrClear(p, 2);
    try std.testing.expectEqual(@as(i32, 0), rt.ptrGet(p, 0));
    rt.ptrCopyBlock(@as(?[*]u8, @ptrCast(p.?)), @as(?[*]const u8, @ptrCast(rt.ptrAdd(p, 3))), 4);
    try std.testing.expectEqual(@as(i32, 40), rt.ptrGet(p, 0));

    const empty_span = try rt.spanOfPtr([]u8, @as(?[*]u8, null), 0);
    try std.testing.expectEqual(@as(usize, 0), empty_span.len);
    try std.testing.expectError(error.Raised, rt.spanOfPtr([]u8, @as(?[*]u8, null), 3));
    drop(rt.take());
}

test "ffi NativeMemory and AlignedAlloc" {
    const p = try rt.nativeAllocZeroed(32);
    defer rt.nativeFree(p);
    rt.nativeFill(p, 8, 7);
    const slice: [*]const u8 = @ptrCast(p.?);
    try std.testing.expectEqual(@as(u8, 7), slice[0]);
    try std.testing.expectEqual(@as(u8, 0), slice[8]);
    rt.nativeCopy(p, @ptrFromInt(@intFromPtr(p.?) + 4), 8);
    try std.testing.expectEqual(@as(u8, 7), slice[11]);
    rt.nativeClear(p, 16);
    try std.testing.expectEqual(@as(u8, 0), slice[11]);

    const q = try rt.nativeAllocElem(4, @sizeOf(i32));
    const q2 = try rt.nativeRealloc(q, 32);
    rt.nativeFree(q2);

    const z = try rt.nativeAllocZeroedElem(4, @sizeOf(i32));
    rt.nativeFree(z);

    const al = try rt.nativeAlignedAlloc(24, 64);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(al.?) % 64);
    @as([*]u8, @ptrCast(al.?))[0] = 0x5A;
    @as([*]u8, @ptrCast(al.?))[23] = 0xC3;
    const al2 = try rt.nativeAlignedRealloc(al, 128, 128);
    try std.testing.expectEqual(@as(usize, 0), @intFromPtr(al2.?) % 128);
    try std.testing.expectEqual(@as(u8, 0x5A), @as([*]const u8, @ptrCast(al2.?))[0]);
    try std.testing.expectEqual(@as(u8, 0xC3), @as([*]const u8, @ptrCast(al2.?))[23]);
    rt.nativeAlignedFree(al2);

    try std.testing.expectError(error.Raised, rt.nativeAlignedAlloc(16, 3));
    drop(rt.take());
}

test "ffi Marshal strings, structs, arrays, read/write, and CallbackPool" {
    const Vec = extern struct { x: f32, y: f32, z: i32 };
    try std.testing.expectEqual(@as(i32, 12), rt.marshalSizeOf(Vec));
    try std.testing.expectEqual(@as(i32, 4), rt.marshalSizeOf(bool));
    const field_y = str("y");
    try std.testing.expectEqual(@as(isize, 4), try rt.marshalOffsetOf(Vec, field_y));

    const mem = try rt.marshalAllocHGlobal(24);
    const mem2 = try rt.marshalReAllocHGlobal(mem, 48);
    defer rt.marshalFreeHGlobal(mem2);

    const orig = Vec{ .x = 1.5, .y = -2.25, .z = 99 };
    try rt.marshalStructureToPtr(orig, mem2);
    const round = try rt.marshalPtrToStructure(Vec, mem2);
    try std.testing.expectEqual(orig, round);

    try rt.marshalWrite(i32, mem2, 16, 0x12345678);
    try std.testing.expectEqual(@as(i32, 0x12345678), try rt.marshalRead(i32, mem2, 16));

    const s_in = str("Raylib \u{03BB}");
    const u8p = try rt.marshalStringToHGlobalUTF8(s_in);
    defer rt.marshalFreeHGlobal(u8p);
    const u8s = rt.marshalPtrToStringUTF8(u8p);
    defer drop(u8s);
    try std.testing.expect(rt.strEql(s_in, u8s));

    const u16p = try rt.marshalStringToHGlobalUni(s_in);
    defer rt.marshalFreeHGlobal(u16p);
    const u16s = rt.marshalPtrToStringUni(u16p);
    defer drop(u16s);
    try std.testing.expect(rt.strEql(s_in, u16s));

    const arr = rt.arrays.arrayOf(Array(i32), .{ @as(i32, 3), @as(i32, 6), @as(i32, 9) });
    defer drop(arr);
    try rt.marshalCopyFromArray(arr, 0, mem2, 3);
    const out_arr = try rt.arrays.arrayZero(Array(i32), 3);
    defer drop(out_arr);
    try rt.marshalCopyToArray(mem2, out_arr, 0, 3);
    try std.testing.expectEqual(@as(i32, 9), out_arr.items[2]);

    const Del = Func(*const fn (?*Env, i32) Raised!i32);
    const before_live = rt.live();
    const f = closure(
        Del,
        struct { bias: i32 },
        .{ .bias = 7 },
        struct {
            fn call(env: ?*Env, x: i32) Raised!i32 {
                const cap = rt.captured(struct { bias: i32 }, env);
                return x + cap.bias;
            }
        }.call,
    );
    const c_ptr = try rt.marshalGetFunctionPointerForDelegate(f);
    const raw_fn: *const fn (i32) callconv(.c) i32 = @ptrFromInt(@as(usize, @bitCast(c_ptr)));
    try std.testing.expectEqual(@as(i32, 42), raw_fn(35));

    const back = try rt.marshalGetDelegateForFunctionPointer(Del, c_ptr);
    try std.testing.expectEqual(@as(i32, 50), try back.code(back.env, 43));
    drop(back);

    const ext_c = struct {
        fn mul3(x: i32) callconv(.c) i32 {
            return x * 3;
        }
    }.mul3;
    const ext_del = try rt.marshalGetDelegateForFunctionPointer(Del, @bitCast(@intFromPtr(&ext_c)));
    try std.testing.expectEqual(@as(i32, 21), try ext_del.code(ext_del.env, 7));
    drop(ext_del);
    drop(f);
    try std.testing.expectEqual(before_live, rt.live());
}

test "ffi MemoryMarshal, Unsafe, and NativeLibrary" {
    const arr = rt.arrays.arrayOf(Array(i32), .{ @as(i32, 0x04030201), @as(i32, 0x08070605) });
    defer drop(arr);
    const sp: []i32 = arr.items;
    const bytes = rt.spanCast([]u8, sp);
    try std.testing.expectEqual(@as(usize, 8), bytes.len);
    const b2 = rt.spanAsBytes([]const u8, sp);
    try std.testing.expectEqual(@as(usize, 8), b2.len);
    const ref_head = rt.spanGetRef(sp);
    try std.testing.expectEqual(@as(i32, 0x04030201), ref_head.*);
    const ref_arr = rt.arrayGetDataRef(arr);
    const ref_next = rt.unsafeAdd(ref_arr, 1);
    try std.testing.expectEqual(@as(i32, 0x08070605), ref_next.*);
    const sp2 = rt.spanCreateFromRef([]const i32, ref_arr, 2);
    try std.testing.expectEqual(@as(usize, 2), sp2.len);
    rt.unsafeWriteUnaligned(u16, @ptrCast(bytes.ptr + 1), 0xBEEF);
    try std.testing.expectEqual(@as(u16, 0xBEEF), rt.unsafeReadUnaligned(u16, @ptrCast(bytes.ptr + 1)));
    try std.testing.expectEqual(@as(u32, 0x3F800000), rt.unsafeAs(u32, @as(f32, 1.0)));

    if (comptime builtin.link_libc and builtin.os.tag == .macos) {
        const lib = try rt.nativeLibLoad(str("libSystem.B.dylib"));
        defer rt.nativeLibFree(lib);
        const sym = try rt.nativeLibGetExport(lib, str("abs"));
        const abs_fn: *const fn (i32) callconv(.c) i32 = @ptrFromInt(@as(usize, @bitCast(sym)));
        try std.testing.expectEqual(@as(i32, 99), abs_fn(-99));
        var h_out: isize = 0;
        var a_out: isize = 0;
        try std.testing.expect(rt.nativeLibTryLoad(str("libSystem.B.dylib"), &h_out));
        defer rt.nativeLibFree(h_out);
        try std.testing.expect(rt.nativeLibTryGetExport(h_out, str("abs"), &a_out));
        try std.testing.expect(a_out != 0);
    }
}

test "ffi eql, hash, show, hasZero, hasNull on raw ptrs and extern unions" {
    const U = extern union { i: i32, f: f32 };
    const un1: U = .{ .i = 0x3F800000 };
    const un2: U = .{ .f = 1.0 };
    try std.testing.expect(rt.eql(un1, un2));
    try std.testing.expectEqual(rt.hash(un1), rt.hash(un2));
    try std.testing.expectEqual(@as(i32, 0), rt.compare(un1, un2));
    try std.testing.expect(rt.hasNull(U));
    try std.testing.expect(rt.arrays.hasZero(U));
    const u_null = rt.nullOf(U);
    try std.testing.expectEqual(@as(i32, 0), u_null.i);

    const S = extern struct { ptr: ?*anyopaque, data: [4]f32, u: U };
    try std.testing.expect(rt.hasNull(S));
    try std.testing.expect(rt.arrays.hasZero(S));
    const s1 = rt.nullOf(S);
    const s2 = S{ .ptr = null, .data = .{ 0, 0, 0, 0 }, .u = u_null };
    try std.testing.expect(rt.eql(s1, s2));
    const txt = rt.anyText(s1);
    defer drop(txt);
    try std.testing.expect(rt.unitsOf(txt).len > 0);
}
