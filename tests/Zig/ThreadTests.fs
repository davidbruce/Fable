module Fable.Tests.Zig.ThreadTests

open System.Threading
open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<Fact>]
let ``test Threads read a shared list and write their own slots`` () =
    let data = [ for i in 1..10_000 -> string i ]
    let results: int[] = Array.zeroCreate 4

    let threads =
        [
            for k in 0..3 ->
                Thread(fun () ->
                    let mutable total = 0

                    for s in data do
                        total <- total + s.Length

                    results.[k] <- total + k
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    results |> equal [| 38894; 38895; 38896; 38897 |]

[<Fact>]
let ``test A string made on a thread is seen after Join`` () =
    let slot: string[] = Array.zeroCreate 1
    let t = Thread(fun () -> slot.[0] <- String.replicate 3 "ab")
    t.Start()
    t.Join()
    slot.[0] |> equal "ababab"

[<Fact>]
let ``test A thread cannot be started twice`` () =
    let t = Thread(fun () -> ())
    t.Start()
    t.Join()

    let raised =
        try
            t.Start()
            false
        with :? ThreadStateException ->
            true

    raised |> equal true

[<Fact>]
let ``test lock keeps a shared counter and list right`` () =
    let gate = obj ()
    let total = ref 0
    let log = ResizeArray<string>()

    let threads =
        [
            for k in 0..3 ->
                Thread(fun () ->
                    for _ in 1..2_000 do
                        lock gate (fun () -> total.Value <- total.Value + 1)

                    lock gate (fun () -> log.Add(sprintf "thread %d" k))
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    total.Value |> equal 8_000
    log.Count |> equal 4

[<Fact>]
let ``test lock can be taken again by the thread that holds it`` () =
    let gate = obj ()
    lock gate (fun () -> lock gate (fun () -> 7)) |> equal 7

[<Fact>]
let ``test Interlocked counts from several threads and swaps values`` () =
    let counter = ref 0

    let threads =
        [
            for _ in 0..3 ->
                Thread(fun () ->
                    for _ in 1..5_000 do
                        Interlocked.Increment(&counter.contents) |> ignore
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    counter.Value |> equal 20_000
    let mutable local = 5
    Interlocked.Add(&local, 10) |> equal 15
    Interlocked.Exchange(&local, 3) |> equal 15
    Interlocked.CompareExchange(&local, 9, 3) |> equal 3
    Interlocked.CompareExchange(&local, 1, 3) |> equal 9
    Interlocked.Decrement(&local) |> equal 8

[<Fact>]
let ``test Array.Parallel works on threads and gives what Array gives`` () =
    let xs = [| 1..100_000 |]
    xs |> Array.Parallel.map (fun x -> int64 x * 2L) |> Array.sum |> equal 10_000_100_000L
    let names = Array.Parallel.init 5_000 (fun i -> string i)
    names.[4999] |> equal "4999"
    names |> Array.Parallel.mapi (fun i s -> s.Length + i) |> Array.sum |> equal 12_516_390
    let hits = ref 0
    let gate = obj ()
    xs |> Array.Parallel.iter (fun _ -> lock gate (fun () -> hits.Value <- hits.Value + 1))
    hits.Value |> equal 100_000

[<Fact>]
let ``test An exception in Array.Parallel is raised inside an AggregateException`` () =
    let message =
        try
            Array.Parallel.init 5_000 (fun i -> if i = 4321 then failwith "boom" else i) |> ignore
            "no"
        with e ->
            e.Message

    message |> equal "One or more errors occurred. (boom)"

[<Fact>]
let ``test Parallel.For runs the body for each index on threads`` () =
    let total = ref 0L
    let squares: int64[] = Array.zeroCreate 10_000

    System.Threading.Tasks.Parallel.For(
        0,
        10_000,
        fun i ->
            squares.[i] <- int64 i * int64 i
            Interlocked.Add(&total.contents, int64 i) |> ignore
    )
    |> ignore

    total.Value |> equal 49_995_000L
    Array.sum squares |> equal 333_283_335_000L

    let message =
        try
            System.Threading.Tasks.Parallel.For(0, 1000, fun i -> if i = 500 then failwith "bad") |> ignore
            "no"
        with e ->
            e.Message

    message |> equal "One or more errors occurred. (bad)"

[<Fact>]
let ``test Task.Run runs on a thread and gives its result`` () =
    let tasks =
        [| for k in 1..4 -> System.Threading.Tasks.Task.Run(fun () -> [ for i in 1 .. k * 1000 -> string i ] |> List.length) |]

    tasks |> Array.map (fun t -> t.Result) |> equal [| 1000; 2000; 3000; 4000 |]
    let unitTask = System.Threading.Tasks.Task.Run(fun () -> ())
    unitTask.Wait()
    unitTask.IsCompleted |> equal true
    let t = task {
        let! x = System.Threading.Tasks.Task.Run(fun () -> 40)
        return x + 2
    }
    t.Result |> equal 42

[<Fact>]
let ``test An exception in Task.Run is raised by Result inside an AggregateException`` () =
    let t = System.Threading.Tasks.Task.Run(fun () -> failwith "oops": int)

    let message =
        try
            string t.Result
        with e ->
            e.Message

    message |> equal "One or more errors occurred. (oops)"

[<Fact>]
let ``test Threads run async computations with their own timers`` () =
    // (each thread waits on its own timers: two at once do not take each other's)
    let results: int[] = Array.zeroCreate 4

    let work (k: int) =
        async {
            let mutable total = 0

            for i in 1..5 do
                do! Async.Sleep 2
                total <- total + i * (k + 1)

            return total
        }

    let threads =
        [
            for k in 0..3 ->
                Thread(fun () -> results.[k] <- Async.RunSynchronously(work k))
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    results |> equal [| 15; 30; 45; 60 |]

type private Box = { mutable Items: int list }

[<Fact>]
let ``test A shared field read while another thread stores into it stays alive`` () =
    // (no lock: a reader may see the old list or the new one, never one that was freed)
    let box = { Items = [ 1; 2; 3 ] }
    let mutable seen = 0

    let writer =
        Thread(fun () ->
            for i in 1..20_000 do
                box.Items <- [ i; i; i ]
        )

    let reader =
        Thread(fun () ->
            for _ in 1..20_000 do
                let xs = box.Items
                seen <- seen + (if List.length xs = 3 then 1 else 0)
        )

    writer.Start()
    reader.Start()
    writer.Join()
    reader.Join()
    seen |> equal 20_000
    box.Items |> equal [ 20_000; 20_000; 20_000 ]

[<Fact>]
let ``test Async.Parallel runs its computations at once`` () =
    // (each blocks its thread for 200 ms: one after another that would be 800 ms)
    let sw = System.Diagnostics.Stopwatch.StartNew()

    let results =
        [ for i in 1..4 -> async {
              Thread.Sleep 200
              return i * i
          } ]
        |> Async.Parallel
        |> Async.RunSynchronously

    results |> equal [| 1; 4; 9; 16 |]
    (sw.ElapsedMilliseconds < 600L) |> equal true

[<Fact>]
let ``test A shared array item read while another thread stores into it stays alive`` () =
    // (no lock: a reader may see the old list or the new one, never one that was freed)
    let slots: int list[] = [| [ 1; 2; 3 ] |]
    let mutable seen = 0

    let writer =
        Thread(fun () ->
            for i in 1..20_000 do
                slots.[0] <- [ i; i; i ]
        )

    let reader =
        Thread(fun () ->
            for _ in 1..20_000 do
                let xs = slots.[0]
                seen <- seen + (if List.length xs = 3 then 1 else 0)
        )

    writer.Start()
    reader.Start()
    writer.Join()
    reader.Join()
    seen |> equal 20_000
    slots.[0] |> equal [ 20_000; 20_000; 20_000 ]

[<Fact>]
let ``test Async.Parallel of many computations gives every result in order`` () =
    let results =
        [ for i in 1..100 -> async { return i * i } ]
        |> Async.Parallel
        |> Async.RunSynchronously

    results |> equal [| for i in 1..100 -> i * i |]

[<Fact>]
let ``test A lazy value forced on several threads is made once`` () =
    let runs = ref 0
    let gate = obj ()

    let value =
        lazy
            (lock gate (fun () -> runs.Value <- runs.Value + 1)
             Thread.Sleep 20
             42)

    let results: int[] = Array.zeroCreate 4

    let threads =
        [ for k in 0..3 -> Thread(fun () -> results.[k] <- value.Value) ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    results |> equal [| 42; 42; 42; 42 |]
    runs.Value |> equal 1

[<Fact>]
let ``test Per-object lock does not collide across unrelated objects`` () =
    let objs = [| for _ in 1..130 -> obj () |]
    let t1Ready = ref 0
    let t2Ready = ref 0

    let rec holdRange (i: int) (last: int) (onAllHeld: unit -> unit) =
        lock objs.[i] (fun () ->
            if i < last then
                holdRange (i + 1) last onAllHeld
            else
                onAllHeld ()
        )

    let t1 =
        Thread(fun () ->
            holdRange 0 64 (fun () ->
                Interlocked.Exchange(&t1Ready.contents, 1) |> ignore

                while Interlocked.CompareExchange(&t2Ready.contents, 0, 0) = 0 do
                    Thread.Sleep 1
            )
        )

    let t2 =
        Thread(fun () ->
            while Interlocked.CompareExchange(&t1Ready.contents, 0, 0) = 0 do
                Thread.Sleep 1

            holdRange 65 129 (fun () -> Interlocked.Exchange(&t2Ready.contents, 1) |> ignore)
        )

    t1.Start()
    t2.Start()
    t1.Join()
    t2.Join()
    t1Ready.Value |> equal 1
    t2Ready.Value |> equal 1

#if FABLE_COMPILER_ZIG // (.NET's ResizeArray, Dictionary, and HashSet are unsynchronized; Zig locks shared cells so buffer growth cannot free under a reader)
[<Fact>]
let ``test Shared ResizeArray, Dictionary, and HashSet serialize concurrent reads and writes`` () =
    let ra = ResizeArray<string>()
    let dict = System.Collections.Generic.Dictionary<int, string>()
    let set = System.Collections.Generic.HashSet<int>()

    let threads =
        [
            for k in 0..3 ->
                Thread(fun () ->
                    let baseIdx = k * 250

                    for i in 0..249 do
                        let key = baseIdx + i
                        let label = string key
                        ra.Add label
                        dict.[key] <- label
                        set.Add key |> ignore

                    for i in 0..49 do
                        let key = baseIdx + i
                        dict.[key] <- "u" + string key
                        set.Contains key |> ignore
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    ra.Count |> equal 1000
    dict.Count |> equal 1000
    set.Count |> equal 1000
    dict.[255] |> equal "u255"
    dict.Remove 255 |> equal true
    set.Remove 255 |> equal true
    ra.Remove "255" |> equal true
    ra.Clear()
    dict.Clear()
    set.Clear()
#endif

[<Fact>]
let ``test Concurrent Path.GetRandomFileName and reflection lookups are thread-safe`` () =
    let ok = ref 0
    let expectedTuple = typeof<int * string>

    let threads =
        [
            for _ in 0..3 ->
                Thread(fun () ->
                    let mutable allGood = true

                    for _ in 1..50 do
                        let name = System.IO.Path.GetRandomFileName()
                        let o = obj ()
                        let ot = o.GetType()
                        let tt =
                            Microsoft.FSharp.Reflection.FSharpType.MakeTupleType [| typeof<int>; typeof<string> |]

                        if System.String.IsNullOrEmpty name || System.String.IsNullOrEmpty ot.FullName || tt.FullName <> expectedTuple.FullName then
                            allGood <- false

                    if allGood then
                        Interlocked.Increment(&ok.contents) |> ignore
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    ok.Value |> equal 4

type private ThreadMailboxMsg =
    | Add of int
    | Get of AsyncReplyChannel<int>
    | GetAndStop of AsyncReplyChannel<int>

[<Fact>]
let ``test MailboxProcessor Post and PostAndReply work across multiple OS threads`` () =
    let mb =
        MailboxProcessor.Start(fun inbox ->
            let rec loop total =
                async {
                    let! msg = inbox.Receive()

                    match msg with
                    | Add n -> return! loop (total + n)
                    | Get ch ->
                        ch.Reply total
                        return! loop total
                    | GetAndStop ch ->
                        ch.Reply total
                        return ()
                }

            loop 0
        )

    let workerReads: int[] = Array.zeroCreate 4

    let threads =
        [
            for k in 0..3 ->
                Thread(fun () ->
                    for _ in 1..75 do
                        mb.Post(Add 1)

                    workerReads.[k] <- mb.PostAndReply(fun ch -> Get ch)
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    for r in workerReads do
        r >= 75 |> equal true

    let finalTotal = mb.PostAndReply(fun ch -> GetAndStop ch)
    finalTotal |> equal 300

type WeakNode = { mutable Next: WeakNode option; Name: string }

[<Fact>]
let ``test Weak references work with values shared between threads`` () =
    // (shared first, then a weak reference)
    let gate = obj ()
    let t = Thread(fun () -> lock gate (fun () -> ()))
    t.Start()
    t.Join()
    let w1 = System.WeakReference<obj>(gate)
    let mutable x = null
    (w1.TryGetTarget(&x) && obj.ReferenceEquals(x, gate)) |> equal true
    // (a weak reference, then shared)
    let o = obj ()
    let w2 = System.WeakReference<obj>(o)
    let t2 = Thread(fun () -> lock o (fun () -> ()))
    t2.Start()
    t2.Join()
    (w2.TryGetTarget(&x) && obj.ReferenceEquals(x, o)) |> equal true
    // (a weak reference used by another thread)
    let n = { Next = None; Name = "a" }
    let w3 = System.WeakReference<WeakNode>(n)
    let mutable seen = ""
    let t3 =
        Thread(fun () ->
            let mutable m = Unchecked.defaultof<WeakNode>
            if w3.TryGetTarget(&m) then
                seen <- m.Name
        )
    t3.Start()
    t3.Join()
    seen |> equal n.Name

[<Fact>]
let ``test A null shared with a thread outlives the thread that made it`` () =
    let gate = obj ()
    let go = ref false
    let result = ref false
    let second = ref (None: Thread option)

    let first =
        Thread(fun () ->
            let d: System.Collections.Generic.Dictionary<string, obj> = Unchecked.defaultof<_>

            let t =
                Thread(fun () ->
                    while not (lock gate (fun () -> go.Value)) do
                        Thread.Sleep 1

                    result.Value <- isNull d
                )

            t.Start()
            lock gate (fun () -> second.Value <- Some t)
        )

    first.Start()
    first.Join()
    lock gate (fun () -> go.Value <- true)
    second.Value.Value.Join()
    result.Value |> equal true

[<Fable.Core.Zig.StackArena(65536)>]
let private shareFromArena () : bool =
    let r = ref 1

    try
        let t = Thread(fun () -> r.Value <- 2)
        t.Start()
        t.Join()
        false
    with :? System.NotSupportedException ->
        true

[<Fact>]
let ``test A value made in a stack arena is not shared with a thread`` () =
#if FABLE_COMPILER_ZIG
    shareFromArena () |> equal true
#else
    shareFromArena () |> equal false
#endif

type IsoMsg =
    | Work of Fable.Core.Zig.Iso<int list>
    | Buffer of Fable.Core.Zig.Iso<ResizeArray<int>>
    | Sum of AsyncReplyChannel<int>

[<Fact>]
let ``test Iso moves a value between threads whole`` () =
    let mb =
        MailboxProcessor.Start(fun inbox ->
            let rec loop total =
                async {
                    match! inbox.Receive() with
                    | Work iso ->
                        let xs = Fable.Core.Zig.Iso.unpack iso
                        return! loop (total + List.sum (List.map (fun x -> x * 2) xs))
                    | Buffer iso ->
                        let b = Fable.Core.Zig.Iso.unpack iso
                        b.Add 100
                        return! loop (total + Seq.sum b)
                    | Sum ch -> ch.Reply total
                }

            loop 0
        )

    let t =
        Thread(fun () ->
            for i in 1..100 do
                mb.Post(Work(Fable.Core.Zig.Iso.pack [ i; i + 1 ]))
                mb.Post(Buffer(Fable.Core.Zig.Iso.pack (ResizeArray [ i ])))
        )

    t.Start()
    t.Join()
    mb.PostAndReply Sum |> equal 35450

[<Fact>]
let ``test An Iso gives its value once`` () =
    let iso = Fable.Core.Zig.Iso.pack [ 3 ]
    Fable.Core.Zig.Iso.unpack iso |> equal [ 3 ]

    (try
        Fable.Core.Zig.Iso.unpack iso |> ignore
        "twice"
     with :? System.InvalidOperationException ->
         "taken")
    |> equal "taken"

#if FABLE_COMPILER_ZIG
[<Fact>]
let ``test Iso.pack refuses a value that is not isolated`` () =
    let kept = [ 1; 2 ]

    (try
        Fable.Core.Zig.Iso.pack kept |> ignore
        "packed"
     with :? System.InvalidOperationException ->
         "not isolated")
    |> equal "not isolated"

    kept.Length |> equal 2
#endif

type RingNode = { mutable Next: RingNode option; V: int }

let private ringOf n =
    let first = { Next = None; V = 0 }
    let mutable last = first

    for i in 1 .. n - 1 do
        let x = { Next = None; V = i }
        last.Next <- Some x
        last <- x

    last.Next <- Some first
    first

let private sumRing (start: RingNode) =
    let mutable total = start.V
    let mutable cur = start.Next.Value

    while not (obj.ReferenceEquals(cur, start)) do
        total <- total + cur.V
        cur <- cur.Next.Value

    total

type RingMsg =
    | Ring of Fable.Core.Zig.Iso<RingNode>
    | Pair of Fable.Core.Zig.Iso<int list * int list>
    | RingTotal of AsyncReplyChannel<int>

[<Fact>]
let ``test Iso moves cycles and shared parts between threads`` () =
    let mb =
        MailboxProcessor.Start(fun inbox ->
            let rec loop total =
                async {
                    match! inbox.Receive() with
                    | Ring iso -> return! loop (total + sumRing (Fable.Core.Zig.Iso.unpack iso))
                    | Pair iso ->
                        let (a, b) = Fable.Core.Zig.Iso.unpack iso
                        return! loop (total + List.sum a + List.sum b)
                    | RingTotal ch -> ch.Reply total
                }

            loop 0
        )

    let t =
        Thread(fun () ->
            for k in 1..50 do
                mb.Post(Ring(Fable.Core.Zig.Iso.pack (ringOf 10)))
                let leaf = [ k ]
                mb.Post(Pair(Fable.Core.Zig.Iso.pack (leaf, leaf)))
        )

    t.Start()
    t.Join()
    mb.PostAndReply RingTotal |> equal 4800

[<Fact>]
let ``test An Iso of a value the collector follows can be dropped on a fresh thread`` () =
    // (a cell that can be part of a cycle, in none: its new thread's collector is made for it)
    let iso = Fable.Core.Zig.Iso.pack { Next = None; V = 1 }
    let seen = ref 0

    let t =
        Thread(fun () ->
            let node = Fable.Core.Zig.Iso.unpack iso
            seen.Value <- node.V
        )

    t.Start()
    t.Join()
    seen.Value |> equal 1

[<Fact>]
let ``test An Iso may hold what is shared already, as a reply function`` () =
    let total = ref 0
    let reply = fun (x: int) -> lock total (fun () -> total.Value <- total.Value + x)
    let t0 = Thread(fun () -> reply 0)
    t0.Start()
    t0.Join()
    let iso = Fable.Core.Zig.Iso.pack ([ 1; 2; 3 ], reply)

    let t =
        Thread(fun () ->
            let (xs, answer) = Fable.Core.Zig.Iso.unpack iso
            answer (List.sum xs)
        )

    t.Start()
    t.Join()
    total.Value |> equal 6

#if FABLE_COMPILER_ZIG
[<Fable.Core.Zig.StackArena(65536)>]
let private packFromArena () : bool =
    try
        Fable.Core.Zig.Iso.pack [ 1; 2; 3 ] |> ignore
        false
    with :? System.InvalidOperationException ->
        true

[<Fact>]
let ``test Iso.pack refuses what was made in a stack arena`` () = packFromArena () |> equal true

[<Fact>]
let ``test A shared cell in an Iso keeps its weak references`` () =
    let gate = obj ()
    let t0 = Thread(fun () -> lock gate (fun () -> ()))
    t0.Start()
    t0.Join()
    let w = System.WeakReference<obj>(gate)
    let iso = Fable.Core.Zig.Iso.pack ([ 1 ], gate)
    let (xs, g) = Fable.Core.Zig.Iso.unpack iso
    let mutable target = null
    (w.TryGetTarget(&target) && obj.ReferenceEquals(target, g)) |> equal true
    List.sum xs |> equal 1
#endif

type OuterNode = { mutable Count: int; Node: RingNode }

[<Fact>]
let ``test An Iso of a value reaching collector cells deep down can be dropped on a fresh thread`` () =
    // (the outer record cannot be part of a cycle; the node inside can)
    let iso = Fable.Core.Zig.Iso.pack { Count = 1; Node = { Next = None; V = 2 } }
    let seen = ref 0

    let t =
        Thread(fun () ->
            let o = Fable.Core.Zig.Iso.unpack iso
            seen.Value <- o.Count + o.Node.V
        )

    t.Start()
    t.Join()
    seen.Value |> equal 3

[<Fact>]
let ``test Iso.tryPack gives an Iso, or the value back`` () =
    match Fable.Core.Zig.Iso.tryPack [ 1; 2 ] with
    | Ok iso -> Fable.Core.Zig.Iso.unpack iso |> equal [ 1; 2 ]
    | Error _ -> failwith "a fresh value is isolated"

#if FABLE_COMPILER_ZIG
    let kept = [ 3; 4 ]

    match Fable.Core.Zig.Iso.tryPack kept with
    | Ok _ -> failwith "a value still used is not isolated"
    | Error back -> back |> equal [ 3; 4 ]

    kept.Length |> equal 2
#endif

#if FABLE_COMPILER_ZIG
type Counter() =
    member val N = 0 with get, set

[<Fact>]
let ``test Iso.pack refuses functions and objects that are not shared already`` () =
    let refused (f: unit -> unit) =
        try
            f ()
            false
        with :? System.InvalidOperationException ->
            true

    let xs = [ 1; 2 ]
    let f = fun () -> List.sum xs
    refused (fun () -> Fable.Core.Zig.Iso.pack (f, xs) |> ignore) |> equal true
    let ys = [ 3 ]
    let g = fun () -> List.sum ys
    refused (fun () -> Fable.Core.Zig.Iso.pack (ys, g) |> ignore) |> equal true
    let c = Counter()
    refused (fun () -> Fable.Core.Zig.Iso.pack c |> ignore) |> equal true
    c.N <- 1
    c.N |> equal 1

[<Fable.Core.Zig.StackArena(65536)>]
let private packTextFromArena (n: int) : bool =
    try
        Fable.Core.Zig.Iso.pack (sprintf "x=%d" n) |> ignore
        false
    with :? System.InvalidOperationException ->
        true

[<Fact>]
let ``test Iso.pack refuses a string made in a stack arena`` () = packTextFromArena 1 |> equal true

type private IIsoBase =
    abstract BaseVal: unit -> int

type private IIsoSub =
    inherit IIsoBase
    abstract SubVal: unit -> int

type private IsoCls(x: int) =
    interface IIsoBase with
        member _.BaseVal() = x * 2

    interface IIsoSub with
        member _.SubVal() = x + 10

[<Fact>]
let ``test Iso.pack moves interfaces across threads for all IfaceMeta kinds`` () =
    let stateless =
        { new IIsoBase with
            member _.BaseVal() = 11 }
    let capturedStr = sprintf "ok:%d" 22
    let capturing =
        { new IIsoBase with
            member _.BaseVal() = capturedStr.Length + 19 }
    let cls = IsoCls 7 :> IIsoBase
    let sub =
        { new IIsoSub with
            member _.BaseVal() = 30
            member _.SubVal() = 4 }
    let upcastIface = sub :> IIsoBase
    let iso = Fable.Core.Zig.Iso.pack (stateless, capturing, cls, upcastIface)
    let out = ref 0
    let t =
        Thread(fun () ->
            let (a, b, c, d) = Fable.Core.Zig.Iso.unpack iso
            out.Value <- a.BaseVal() + b.BaseVal() + c.BaseVal() + d.BaseVal()
        )
    t.Start()
    t.Join()
    out.Value |> equal (11 + (5 + 19) + 14 + 30)

type private CycleHolder(node: RingNode) =
    member _.Node = node

[<Fact>]
let ``test Iso.tryPack does not partially share an unisolated pair`` () =
    let clean = Counter()
    clean.N <- 42
    let a = { Next = None; V = 1 }
    let b = { Next = Some a; V = 2 }
    a.Next <- Some b
    let bad = CycleHolder(a)
    match Fable.Core.Zig.Iso.tryPack (clean, bad) with
    | Ok _ -> failwith "unshareable cyclic holder must reject Iso.tryPack"
    | Error(cleanBack, _badBack) ->
        match Fable.Core.Zig.Iso.tryPack cleanBack with
        | Ok iso ->
            let unpacked = Fable.Core.Zig.Iso.unpack iso
            unpacked.N |> equal 42
        | Error _ -> failwith "clean half must remain packable after failed Iso.tryPack"

[<Fable.Core.Emit("if ($0 == .Cons) fable_rt.isShared($0.Cons) else false")>]
let private isListShared (_x: 'a list) : bool = Fable.Core.Util.nativeOnly

[<Fact>]
let ``test Task.Run transfers unique input and isolated output unshared`` () =
    let xs = [ 1..100 ]
    let t =
        System.Threading.Tasks.Task.Run(fun () ->
            let wasShared = isListShared xs
            (wasShared, List.map (fun x -> x * 2) xs)
        )
    let (inShared, ys) = t.Result
    let (inShared2, ys2) = t.Result
    inShared |> equal false
    inShared2 |> equal false
    isListShared ys |> equal false
    isListShared ys2 |> equal false
    List.sum ys |> equal 10100
    List.sum ys2 |> equal 10100

[<Fact>]
let ``test Thread transfers unique input capture unshared`` () =
    let xs = [ 1..50 ]
    let inShared = ref true
    let sumOut = ref 0
    let t =
        Thread(fun () ->
            inShared.Value <- isListShared xs
            sumOut.Value <- List.sum xs
        )
    t.Start()
    t.Join()
    inShared.Value |> equal false
    sumOut.Value |> equal 1275

[<Fact>]
let ``test Async.Parallel returns isolated results unshared`` () =
    let arr =
        [ for i in 1..4 -> async { return [ i; i * 10 ] } ]
        |> Async.Parallel
        |> Async.RunSynchronously
    arr.Length |> equal 4
    for k in 0..3 do
        isListShared arr.[k] |> equal false
        arr.[k] |> equal [ k + 1; (k + 1) * 10 ]
#endif

[<Fable.Core.Zig.StackArena(2048)>]
let private nestedArenaInner (n: int) : int =
    [ 1..n ] |> List.map (fun x -> x * 2) |> List.sum

[<Fable.Core.Zig.StackArena(8192)>]
let private nestedArenaOuter (seed: int) : int =
    let xs = [ 1..8 ] |> List.map (fun x -> x + seed)
    let inner = nestedArenaInner 10
    List.sum xs + inner

[<Fact>]
let ``test StackArena executes safely concurrently across multiple threads`` () =
    let expected = 4 * nestedArenaOuter 3
    let results = Array.zeroCreate 4
    let threads =
        Array.init 4 (fun i ->
            Thread(fun () ->
                let mutable acc = 0
                for _ in 1..20 do
                    acc <- acc + nestedArenaOuter 3
                results[i] <- acc
            )
        )
    for t in threads do t.Start()
    for t in threads do t.Join()
    Array.sum results |> equal (20 * expected)

[<Fact>]
let ``test Task.Run burst, nested Task.Run, concurrent Result reads, and IsFaulted`` () =
    let burst =
        [| for i in 1..50 -> System.Threading.Tasks.Task.Run(fun () -> [ for j in 1..20 -> i + j ] |> List.sum) |]
    let burstSum = burst |> Array.sumBy (fun t -> t.Result)
    burstSum |> equal 36000

    let nested =
        [| for i in 1..12 ->
               System.Threading.Tasks.Task.Run(fun () ->
                   let inner = System.Threading.Tasks.Task.Run(fun () -> i * 3)
                   inner.Result + 1
               ) |]
    nested |> Array.sumBy (fun t -> t.Result) |> equal 246

    let sharedTask = System.Threading.Tasks.Task.Run(fun () -> [ 1..10 ])
    let readers = Array.init 2 (fun _ -> [])
    let rThreads =
        Array.init 2 (fun idx ->
            Thread(fun () -> readers.[idx] <- sharedTask.Result)
        )
    for rt in rThreads do rt.Start()
    for rt in rThreads do rt.Join()
    readers.[0] |> equal [ 1..10 ]
    readers.[1] |> equal [ 1..10 ]

    let faulted = System.Threading.Tasks.Task.Run(fun () -> failwith "boom": int)
    while not faulted.IsCompleted do
        Thread.Sleep 1
    faulted.IsFaulted |> equal true
    let raisedAgg =
        try
            faulted.Result |> ignore
            false
        with :? System.AggregateException ->
            true
    raisedAgg |> equal true

[<Fact>]
let ``test Nested Async.Parallel and Task.Run inside Parallel.For do not deadlock`` () =
    let nestedAsync =
        [ for i in 1..4 ->
              Async.Parallel [ for j in 1..4 -> async { return i * 10 + j } ] ]
        |> Async.Parallel
        |> Async.RunSynchronously
    let flatSum = nestedAsync |> Array.sumBy Array.sum
    flatSum |> equal 440

    let out = Array.zeroCreate<int> 600
    System.Threading.Tasks.Parallel.For(
        0,
        600,
        fun i -> out.[i] <- System.Threading.Tasks.Task.Run(fun () -> i * 2).Result
    )
    |> ignore
    Array.sum out |> equal 359400
