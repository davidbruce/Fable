//! Threads, reentrant per-object futex locks, and `Parallel.For` (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const AggregateException = rt.AggregateException;
const ArgumentNullException = rt.ArgumentNullException;
const Env = rt.Env;
const Exn = rt.Exn;
const Func = rt.Func;
const OutOfMemoryException = rt.OutOfMemoryException;
const Raised = rt.Raised;
const ThreadStateException = rt.ThreadStateException;
const bookkeeping = rt.bookkeeping;
const captured = rt.captured;
const cell = rt.cell;
const collectorDeinit = rt.collectorDeinit;
const collectorSetup = rt.collectorSetup;
const drop = rt.drop;
const dup = rt.dup;
const exnWithInner = rt.exnWithInner;
const lockField = rt.lockField;
const markShared = rt.markShared;
const new = rt.new;
const oom = rt.oom;
const raise = rt.raise;
const release = rt.release;
const sgc = rt.sgc;
const stored = rt.stored;
const str = rt.str;
const take = rt.take;
const thread = rt.thread;
const throw = rt.throw;
const track = rt.track;
const uncaught = rt.uncaught;
const unlockField = rt.unlockField;

const max_pool_workers: usize = 8;

const worker_tls = if (sgc.per_thread) struct {
    pub threadlocal var active: bool = false;
} else struct {
    pub var active: bool = false;
};

const PoolJob = struct {
    run: *const fn (*PoolJob) void,
    next: ?*PoolJob = null,
    remaining: ?*u32 = null,
    done_flag: ?*u32 = null,
    release_after: ?*const fn (*PoolJob) void = null,
    fn_code: *const fn (?*Env, void) Raised!void = threadRan,
    fn_env: ?*Env = null,
};

var pool: struct {
    active: u32 = 0,
    init_lock: u32 = 0,
    queue_lock: u32 = 0,
    seq: u32 = 0,
    wait_seq: u32 = 0,
    stopping: bool = false,
    in_flight: usize = 0,
    head: ?*PoolJob = null,
    tail: ?*PoolJob = null,
    workers: [max_pool_workers]std.Thread = undefined,
    n_workers: usize = 0,
} = .{};

/// .NET's `Thread`: a function run on a thread of its own (or on the shared worker pool when
/// `pooled = true`). Captures are transferred whole when unaliased or marked shared otherwise.
pub const ThreadStart = Func(*const fn (?*Env, void) Raised!void);

pub const ThreadOf = *struct {
    pub const fable_identity = {};
    @"$rc": u32 = 1,
    start: ThreadStart,
    /// the thread, once started and until joined
    handle: ?*std.Thread = null,
    started: bool = false,
    pooled: bool = false,
    has_gc: bool = false,
    /// set (atomically) when the thread's function has ended
    finished: u32 = 0,
    job: PoolJob = .{ .run = poolThreadRun },
};

fn poolFlushStats() void {
    if (track) {
        const delta = thread.stats.allocs - thread.stats.frees;
        if (delta != 0) {
            _ = @atomicRmw(isize, &rt.ended_threads_live, .Add, @intCast(delta), .monotonic);
            thread.stats.allocs = 0;
            thread.stats.frees = 0;
        }
    }
}

fn poolEnsureStarted() void {
    if (comptime builtin.single_threaded) return;
    if (@atomicLoad(u32, &pool.active, .acquire) != 0) return;
    lockField(&pool.init_lock);
    defer unlockField(&pool.init_lock);
    if (@atomicLoad(u32, &pool.active, .acquire) != 0) return;
    const cpus = std.Thread.getCpuCount() catch 4;
    const target = @min(@max(cpus, 4), max_pool_workers);
    var count: usize = 0;
    while (count < target) : (count += 1) {
        pool.workers[count] = std.Thread.spawn(.{}, poolWorkerMain, .{}) catch break;
    }
    pool.n_workers = count;
    if (count > 0) @atomicStore(u32, &pool.active, 1, .release);
}

fn poolEnqueue(job: *PoolJob) void {
    job.next = null;
    lockField(&pool.queue_lock);
    if (pool.tail) |tail| tail.next = job else pool.head = job;
    pool.tail = job;
    pool.seq +%= 1;
    unlockField(&pool.queue_lock);
    futexWake(&pool.seq, false);
}

fn poolEnqueueBatch(jobs: []const *PoolJob) void {
    if (jobs.len == 0) return;
    lockField(&pool.queue_lock);
    for (jobs) |job| {
        job.next = null;
        if (pool.tail) |tail| tail.next = job else pool.head = job;
        pool.tail = job;
    }
    pool.seq +%= 1;
    unlockField(&pool.queue_lock);
    futexWake(&pool.seq, true);
}

fn poolPopOrWait() ?*PoolJob {
    while (true) {
        lockField(&pool.queue_lock);
        if (pool.head) |j| {
            pool.head = j.next;
            if (pool.head == null) pool.tail = null;
            j.next = null;
            pool.in_flight += 1;
            unlockField(&pool.queue_lock);
            return j;
        }
        if (pool.stopping and pool.in_flight == 0) {
            unlockField(&pool.queue_lock);
            return null;
        }
        const observed = @atomicLoad(u32, &pool.seq, .acquire);
        unlockField(&pool.queue_lock);
        futexWait(&pool.seq, observed);
    }
}

fn poolFinishInFlight() void {
    lockField(&pool.queue_lock);
    pool.in_flight -= 1;
    const wake_stop = pool.stopping and pool.head == null and pool.in_flight == 0;
    if (wake_stop) pool.seq +%= 1;
    unlockField(&pool.queue_lock);
    if (wake_stop) futexWake(&pool.seq, true);
}

fn poolExecJob(job: *PoolJob, comptime on_worker: bool) void {
    const rem_opt = job.remaining;
    const flag_opt = job.done_flag;
    const rel_opt = job.release_after;
    if (comptime !on_worker) {
        const saved_async = thread.async_state;
        const saved_arena = thread.arena;
        thread.async_state = null;
        thread.arena = null;
        job.run(job);
        rt.asyncStateRelease();
        thread.async_state = saved_async;
        thread.arena = saved_arena;
    } else {
        job.run(job);
        rt.asyncStateRelease();
        poolFlushStats();
    }
    if (rem_opt) |rem| {
        if (@atomicRmw(u32, rem, .Sub, 1, .acq_rel) == 1) {
            _ = @atomicRmw(u32, &pool.wait_seq, .Add, 1, .acq_rel);
            futexWake(&pool.wait_seq, true);
        }
    }
    if (flag_opt) |flag| setAndWakeAll(flag);
    if (rel_opt) |rel| {
        rel(job);
        if (comptime on_worker) poolFlushStats();
    }
    poolFinishInFlight();
}

fn poolTryRunOne() bool {
    lockField(&pool.queue_lock);
    const job = pool.head orelse {
        unlockField(&pool.queue_lock);
        return false;
    };
    pool.head = job.next;
    if (pool.head == null) pool.tail = null;
    job.next = null;
    pool.in_flight += 1;
    unlockField(&pool.queue_lock);
    poolExecJob(job, false);
    return true;
}

fn poolWorkerMain() void {
    worker_tls.active = true;
    defer worker_tls.active = false;
    while (poolPopOrWait()) |job| poolExecJob(job, true);
    collectorDeinit();
    poolFlushStats();
}

/// Gracefully drain in-flight jobs and join all worker pool threads so thread-local
/// `collectorDeinit()` and `ended_threads_live` settle before exit or leak checks.
pub fn poolShutdown() void {
    if (comptime builtin.single_threaded) return;
    if (@atomicLoad(u32, &pool.active, .acquire) == 0) return;
    lockField(&pool.init_lock);
    defer unlockField(&pool.init_lock);
    if (@atomicLoad(u32, &pool.active, .acquire) == 0) return;
    lockField(&pool.queue_lock);
    pool.stopping = true;
    pool.seq +%= 1;
    unlockField(&pool.queue_lock);
    futexWake(&pool.seq, true);
    for (pool.workers[0..pool.n_workers]) |w| w.join();
    pool.n_workers = 0;
    pool.stopping = false;
    pool.head = null;
    pool.tail = null;
    pool.in_flight = 0;
    @atomicStore(u32, &pool.active, 0, .release);
}

fn poolThreadRun(job: *PoolJob) void {
    const t: ThreadOf = @fieldParentPtr("job", job);
    const f: ThreadStart = .{ .env = job.fn_env, .code = job.fn_code };
    job.fn_env = null;
    job.fn_code = threadRan;
    if (t.has_gc and !thread.collector_ready) collectorSetup();
    f.code(f.env, {}) catch {
        uncaught();
        std.process.exit(134);
    };
    drop(f);
}

fn poolThreadRelease(job: *PoolJob) void {
    const t: ThreadOf = @fieldParentPtr("job", job);
    drop(t);
}

/// `Thread(fun () -> ...)`
pub fn threadNew(start: ThreadStart) ThreadOf {
    return new(ThreadOf, .{ .start = dup(start) });
}

/// Internal thread handle backed by the runtime worker pool (used by `Task.Run`).
pub fn poolNew(start: ThreadStart) ThreadOf {
    return new(ThreadOf, .{ .start = dup(start), .pooled = true });
}

/// Create and immediately submit a pooled `ThreadOf`.
pub fn poolStart(start: ThreadStart) Raised!ThreadOf {
    const t = poolNew(start);
    threadStart(t) catch |e| {
        drop(t);
        return e;
    };
    return t;
}

/// `t.Start()`
pub fn threadStart(t: ThreadOf) Raised!void {
    if (t.started) return raise(ThreadStateException, str("Thread is running or terminated; it cannot restart."));
    // Move `t.start` out of `ThreadOf` before transfer so unique capture trees retain RC=1.
    const start_fn = t.start;
    t.start = .{ .env = null, .code = threadRan };
    thread.transfer_saw_gc = false;
    rt.transferOrShareOrRaise(start_fn) catch |err| {
        t.start = start_fn;
        return err;
    };
    const has_gc = thread.transfer_saw_gc;
    // (the thread object too: the worker holds it, and the flag in it, until it ends)
    markShared(t) catch |err| {
        t.start = start_fn;
        return err;
    };
    if (t.pooled) {
        t.has_gc = has_gc;
        t.started = true;
        if (comptime !builtin.single_threaded) {
            poolEnsureStarted();
            if (pool.n_workers > 0) {
                t.job = .{
                    .run = poolThreadRun,
                    .done_flag = &t.finished,
                    .release_after = poolThreadRelease,
                    .fn_code = start_fn.code,
                    .fn_env = start_fn.env,
                };
                _ = dup(t);
                poolEnqueue(&t.job);
                return;
            }
        }
        const saved_async = thread.async_state;
        const saved_arena = thread.arena;
        thread.async_state = null;
        thread.arena = null;
        start_fn.code(start_fn.env, {}) catch {
            uncaught();
            std.process.exit(134);
        };
        drop(start_fn);
        rt.asyncStateRelease();
        thread.async_state = saved_async;
        thread.arena = saved_arena;
        setAndWakeAll(&t.finished);
        return;
    }
    const h = rt.allocator.create(std.Thread) catch oom();
    const t_ref = dup(t);
    h.* = std.Thread.spawn(.{}, threadMain, .{ start_fn, has_gc, &t.finished, t_ref }) catch {
        rt.allocator.destroy(h);
        t.start = start_fn;
        drop(t_ref);
        return raise(OutOfMemoryException, str("Thread failed to start."));
    };
    t.handle = h;
    t.started = true;
}

/// (what a thread runs: its function, then what it kept for itself is given up; an exception
/// that leaves it ends the program, as on .NET)
fn threadMain(f: ThreadStart, has_gc: bool, finished: *u32, t: ThreadOf) void {
    if (has_gc and !thread.collector_ready) collectorSetup();
    f.code(f.env, {}) catch {
        uncaught();
        std.process.exit(134);
    };
    drop(f);
    // (what the function wrote is seen by whoever sees this; the thread object is kept alive
    // until then, as it holds the flag)
    setAndWakeAll(finished);
    drop(t);
    collectorDeinit();
    if (track) _ = @atomicRmw(isize, &rt.ended_threads_live, .Add, @intCast(thread.stats.allocs - thread.stats.frees), .monotonic);
}

fn threadRan(_: ?*Env, _: void) Raised!void {}

/// `t.Join()`: waits for the thread to end
pub fn threadJoin(t: ThreadOf) void {
    if (t.pooled) {
        while (@atomicLoad(u32, &t.finished, .acquire) == 0) {
            if (worker_tls.active and poolTryRunOne()) continue;
            futexWait(&t.finished, 0);
        }
        return;
    }
    const h = t.handle orelse return;
    h.join();
    rt.allocator.destroy(h);
    t.handle = null;
}

/// `t.IsAlive`: started and not ended
pub fn threadIsAlive(t: ThreadOf) bool {
    return t.started and @atomicLoad(u32, &t.finished, .acquire) == 0;
}

/// `Thread.CurrentThread.ManagedThreadId`
pub fn threadId() i32 {
    return @truncate(@as(i64, @intCast(std.Thread.getCurrentId())));
}

// ---- `lock`: .NET's Monitor, re-entrant, per object address with OS futex parking ----
//
// Each locked object address gets its own MonitorNode stored in a small table guarded by a
// spinlock only while acquiring/releasing a reference count on the node. Contended callers
// sleep in the OS kernel via futex (__ulock_wait on Darwin, futex on Linux), so unrelated
// objects never collide and waiting threads do not busy-spin.

pub fn futexWait(ptr: *const u32, expect: u32) void {
    if (comptime builtin.single_threaded) return;
    switch (builtin.os.tag) {
        .macos, .ios, .tvos, .watchos, .visionos => {
            const flags: std.c.UL = .{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true };
            _ = std.c.__ulock_wait(flags, @constCast(ptr), expect, 0);
        },
        .linux => {
            _ = std.os.linux.futex_4arg(@ptrCast(ptr), .{ .cmd = .WAIT, .private = true }, expect, null);
        },
        else => std.Thread.yield() catch {},
    }
}

pub fn futexWake(ptr: *const u32, wake_all: bool) void {
    if (comptime builtin.single_threaded) return;
    switch (builtin.os.tag) {
        .macos, .ios, .tvos, .watchos, .visionos => {
            const flags: std.c.UL = .{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true, .WAKE_ALL = wake_all };
            _ = std.c.__ulock_wake(flags, @constCast(ptr), 0);
        },
        .linux => {
            _ = std.os.linux.futex_3arg(@ptrCast(ptr), .{ .cmd = .WAKE, .private = true }, if (wake_all) std.math.maxInt(i32) else 1);
        },
        else => {},
    }
}

pub fn waitUntilSet(flag: *const u32) void {
    while (@atomicLoad(u32, flag, .acquire) == 0) {
        futexWait(flag, 0);
    }
}

pub fn setAndWakeAll(flag: *u32) void {
    @atomicStore(u32, flag, 1, .release);
    futexWake(flag, true);
}

const MonitorNode = struct {
    // state: 0 = unlocked, 1 = locked (uncontended), 2 = locked (maybe waiters)
    state: u32 = 0,
    owner_valid: u32 = 0,
    owner: usize = 0,
    depth: u32 = 0,
    refs: usize = 0,
    next_free: ?*MonitorNode = null,
};

var monitor_table_lock: u32 = 0;
var monitors: std.AutoHashMapUnmanaged(usize, *MonitorNode) = .empty;
var free_monitors: ?*MonitorNode = null;

fn acquireMonitor(key: usize) *MonitorNode {
    lockField(&monitor_table_lock);
    defer unlockField(&monitor_table_lock);
    if (monitors.get(key)) |node| {
        node.refs += 1;
        return node;
    }
    const node = if (free_monitors) |head| blk: {
        free_monitors = head.next_free;
        head.* = .{ .refs = 1 };
        break :blk head;
    } else blk: {
        const fresh = bookkeeping().create(MonitorNode) catch oom();
        fresh.* = .{ .refs = 1 };
        break :blk fresh;
    };
    monitors.put(bookkeeping(), key, node) catch oom();
    return node;
}

fn releaseMonitor(key: usize, node: *MonitorNode) void {
    lockField(&monitor_table_lock);
    defer unlockField(&monitor_table_lock);
    node.refs -= 1;
    if (node.refs == 0) {
        _ = monitors.remove(key);
        node.next_free = free_monitors;
        free_monitors = node;
    }
}

pub fn lockEnter(key: usize) void {
    const node = acquireMonitor(key);
    const me: usize = if (comptime builtin.single_threaded) 1 else @intCast(std.Thread.getCurrentId());
    if (@atomicLoad(u32, &node.state, .acquire) != 0 and
        @atomicLoad(u32, &node.owner_valid, .acquire) != 0 and
        @atomicLoad(usize, &node.owner, .monotonic) == me)
    {
        node.depth += 1;
        return;
    }
    var c = @cmpxchgStrong(u32, &node.state, 0, 1, .acquire, .monotonic);
    if (c != null) {
        if (c.? == 1) c = @atomicRmw(u32, &node.state, .Xchg, 2, .acquire);
        while (c.? != 0) : (c = @atomicRmw(u32, &node.state, .Xchg, 2, .acquire)) {
            futexWait(&node.state, 2);
        }
    }
    @atomicStore(usize, &node.owner, me, .monotonic);
    @atomicStore(u32, &node.owner_valid, 1, .release);
    node.depth = 1;
}

pub fn lockExit(key: usize) void {
    const node = blk: {
        lockField(&monitor_table_lock);
        defer unlockField(&monitor_table_lock);
        break :blk monitors.get(key) orelse unreachable;
    };
    node.depth -= 1;
    if (node.depth == 0) {
        @atomicStore(u32, &node.owner_valid, 0, .monotonic);
        if (@atomicRmw(u32, &node.state, .Xchg, 0, .release) == 2) {
            futexWake(&node.state, false);
        }
    }
    releaseMonitor(key, node);
}

/// (the address a lock is taken on: of the cell; null cannot be locked)
fn lockKey(o: anytype) ?usize {
    const T = @TypeOf(o);
    if (comptime @typeInfo(T) == .optional) {
        const p = o orelse return null;
        return lockKey(p);
    }
    if (comptime @typeInfo(T) != .pointer) @compileError("fable: `lock` needs an object of a reference type, not " ++ @typeName(T));
    return @intFromPtr(o);
}

fn LockResult(comptime F: type) type {
    return @typeInfo(@typeInfo(@FieldType(F, "code")).pointer.child).@"fn".return_type.?;
}

/// `lock o (fun () -> ...)`: the function, run while this thread holds the lock of `o`
pub fn lockRun(o: anytype, f: anytype) LockResult(@TypeOf(f)) {
    const key = lockKey(o) orelse return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'obj')"));
    lockEnter(key);
    defer lockExit(key);
    return f.code(f.env, {});
}

/// `step(ctx, i)` for each `i` below `n`, in chunks on up to eight threads (the calling one
/// among them); what `ctx` holds must be shared already, and so must what a step leaves behind.
/// The first exception stops the others and is raised here. (Few items: here, in order.)
pub fn parallelFor(n: usize, ctx: anytype, comptime step: fn (@TypeOf(ctx), usize) Raised!void) Raised!void {
    const cpus = if (comptime builtin.single_threaded) 1 else std.Thread.getCpuCount() catch 1;
    const workers = @min(@min(cpus, max_pool_workers), n / 256);
    if (workers < 2) {
        var i: usize = 0;
        while (i < n) : (i += 1) step(ctx, i) catch return aggregated(take());
        return;
    }
    const State = struct {
        failed: ?Exn = null,
        stop: u32 = 0,

        fn chunk(st: *@This(), c: @TypeOf(ctx), lo: usize, hi: usize) void {
            var i = lo;
            while (i < hi) : (i += 1) {
                if (@atomicLoad(u32, &st.stop, .acquire) != 0) return;
                step(c, i) catch {
                    const e = take();
                    if (@cmpxchgStrong(u32, &st.stop, 0, 1, .acq_rel, .acquire) == null) {
                        // (the exception goes to the calling thread)
                        markShared(e) catch drop(take());
                        st.failed = e;
                    } else drop(e);
                    return;
                };
            }
        }
    };
    const size = (n + workers - 1) / workers;
    poolEnsureStarted();
    var state: State = .{};
    if (pool.n_workers == 0) {
        state.chunk(ctx, 0, n);
        if (state.failed) |e| return aggregated(e);
        return;
    }
    const ChunkJob = struct {
        job: PoolJob,
        state: *State,
        ctx: @TypeOf(ctx),
        lo: usize,
        hi: usize,

        fn run(jp: *PoolJob) void {
            const self: *@This() = @fieldParentPtr("job", jp);
            self.state.chunk(self.ctx, self.lo, self.hi);
        }
    };
    var remaining: u32 = @intCast(workers - 1);
    var jobs: [max_pool_workers]ChunkJob = undefined;
    var ptrs: [max_pool_workers]*PoolJob = undefined;
    var w: usize = 1;
    while (w < workers) : (w += 1) {
        const lo = @min(n, w * size);
        const hi = @min(n, lo + size);
        const idx = w - 1;
        jobs[idx] = .{
            .job = .{ .run = ChunkJob.run, .remaining = &remaining },
            .state = &state,
            .ctx = ctx,
            .lo = lo,
            .hi = hi,
        };
        ptrs[idx] = &jobs[idx].job;
    }
    poolEnqueueBatch(ptrs[0 .. workers - 1]);
    state.chunk(ctx, 0, @min(n, size));
    while (true) {
        const observed = @atomicLoad(u32, &pool.wait_seq, .acquire);
        if (@atomicLoad(u32, &remaining, .acquire) == 0) break;
        if (poolTryRunOne()) continue;
        if (@atomicLoad(u32, &remaining, .acquire) == 0) break;
        futexWait(&pool.wait_seq, observed);
    }
    if (state.failed) |e| return aggregated(e);
}

/// Run `count` worker invocations concurrently on the shared worker pool (for `Async.Parallel`).
pub fn poolRunWorkers(count: i32, f: ThreadStart) Raised!void {
    if (count <= 0) return;
    try markShared(f);
    const n: usize = @min(@as(usize, @intCast(count)), max_pool_workers);
    if (comptime builtin.single_threaded) {
        const saved_async = thread.async_state;
        const saved_arena = thread.arena;
        thread.async_state = null;
        thread.arena = null;
        defer {
            rt.asyncStateRelease();
            thread.async_state = saved_async;
            thread.arena = saved_arena;
        }
        return f.code(f.env, {});
    }
    poolEnsureStarted();
    const State = struct {
        f: ThreadStart,
        failed: ?Exn = null,
        has_fail: u32 = 0,

        fn exec(st: *@This()) void {
            st.f.code(st.f.env, {}) catch {
                const e = take();
                if (@cmpxchgStrong(u32, &st.has_fail, 0, 1, .acq_rel, .acquire) == null) {
                    markShared(e) catch drop(take());
                    st.failed = e;
                } else drop(e);
            };
        }
    };
    var state: State = .{ .f = f };
    if (n == 1 or pool.n_workers == 0) {
        const saved_async = thread.async_state;
        const saved_arena = thread.arena;
        thread.async_state = null;
        thread.arena = null;
        var k: usize = 0;
        while (k < n) : (k += 1) {
            state.exec();
            rt.asyncStateRelease();
        }
        thread.async_state = saved_async;
        thread.arena = saved_arena;
        if (state.failed) |e| {
            throw(e);
            return error.Raised;
        }
        return;
    }
    const WorkerJob = struct {
        job: PoolJob,
        state: *State,

        fn run(jp: *PoolJob) void {
            const self: *@This() = @fieldParentPtr("job", jp);
            self.state.exec();
        }
    };
    var remaining: u32 = @intCast(n);
    var jobs: [max_pool_workers]WorkerJob = undefined;
    var ptrs: [max_pool_workers]*PoolJob = undefined;
    for (0..n) |i| {
        jobs[i] = .{
            .job = .{ .run = WorkerJob.run, .remaining = &remaining },
            .state = &state,
        };
        ptrs[i] = &jobs[i].job;
    }
    poolEnqueueBatch(ptrs[0..n]);
    while (true) {
        const observed = @atomicLoad(u32, &pool.wait_seq, .acquire);
        if (@atomicLoad(u32, &remaining, .acquire) == 0) break;
        if (worker_tls.active and poolTryRunOne()) continue;
        if (@atomicLoad(u32, &remaining, .acquire) == 0) break;
        futexWait(&pool.wait_seq, observed);
    }
    if (state.failed) |e| {
        throw(e);
        return error.Raised;
    }
}

/// `Parallel.For(from, to, fun i -> ...)`: the body for each `i` from `from` below `to`, on
/// threads; what it captured is shared first
pub fn parallelForRange(from: i32, to: i32, f: anytype) Raised!void {
    if (to <= from) return;
    try markShared(f);
    const Ctx = struct { f: @TypeOf(f), from: i32 };
    const S = struct {
        fn step(c: Ctx, i: usize) Raised!void {
            return c.f.code(c.f.env, c.from + @as(i32, @intCast(i)));
        }
    };
    return parallelFor(@intCast(@as(i64, to) - from), Ctx{ .f = f, .from = from }, S.step);
}

/// (as .NET's Parallel raises an exception of its work: an AggregateException with it inside)
fn aggregated(e: Exn) Raised {
    defer drop(e);
    const agg = AggregateException.new(.{ .Message = str("One or more errors occurred.") });
    defer drop(agg);
    throw(exnWithInner(agg, e));
    return error.Raised;
}
