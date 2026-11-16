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
