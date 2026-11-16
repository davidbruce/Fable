module Fable.Tests.Zig.AsyncTests

open System
open System.Threading
open Fable.Tests.Util
open Fable.Tests.Util
open Fable.Tests.Util.Testing

let private runOffThreadPool action =
#if FABLE_COMPILER
    action ()
#else
    // .NET reschedules deferred FromContinuations callbacks invoked on a pool thread.
    // Use a dedicated thread so the probe can observe completion and thrown callbacks.
    let mutable failure = None
    let thread = Thread(ThreadStart(fun () ->
        try action ()
        with error -> failure <- Some error))
    thread.Start()
    thread.Join()
    failure |> Option.iter raise
#endif

let private observeTryCancelled token (work: Async<int>) =
    let calls = ResizeArray<string>()
    Async.StartWithContinuations(
        work,
        (fun value -> calls.Add(string value)),
        (fun error -> calls.Add("error: " + error.Message)),
        (fun error -> calls.Add("cancel: " + error.Message)),
        token)
    calls

module private FinalizerRegressions =
    open System
    open System.Threading

    let private check expected actual =
        if expected <> actual then failwithf "Expected %A, got %A" expected actual

    let private observe (token: CancellationToken) work =
        let terminal = ResizeArray<string>()
        Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun e -> terminal.Add e.Message), (fun _ -> terminal.Add "cancel"), token)
        terminal

    let preCancelled () =
        for throws in [false; true] do
            use source = new CancellationTokenSource()
            source.Cancel()
            let mutable cleanups = 0
            let mutable entered = false
            let work = async.TryFinally(async { entered <- true }, fun () ->
                cleanups <- cleanups + 1
                if throws then failwith "cleanup")
            let terminal = observe source.Token work
            check false entered
            check 1 cleanups
            check [|"cancel"|] (terminal.ToArray())

    let nestedPreCancelled () =
        use source = new CancellationTokenSource()
        source.Cancel()
        let cleanups = ResizeArray<string>()
        let inner = async.TryFinally(async.Return 42, fun () -> cleanups.Add "inner")
        let outer = async.TryFinally(inner, fun () -> cleanups.Add "outer")
        let terminal = observe source.Token outer
        check [|"outer"|] (cleanups.ToArray())
        check [|"cancel"|] (terminal.ToArray())

    let cancelledAcquisition () =
        for acquisition in [0; 1; 2] do
            use source = new CancellationTokenSource()
            let mutable disposals = 0
            let mutable entered = false
            let resource = { new IDisposable with member _.Dispose() = disposals <- disposals + 1 }
            let acquire = Async.FromContinuations(fun (ok, _, _) ->
                source.Cancel()
                ok resource)
            let work =
                if acquisition = 1 then async {
                    use! owned = acquire
                    entered <- true
                }
                elif acquisition = 0 then async {
                    let! acquired = acquire
                    use owned = acquired
                    entered <- true
                }
                else async {
                    use owned =
                        source.Cancel()
                        resource
                    entered <- true
                }
            let terminal = observe source.Token work
            check false entered
            check 1 disposals
            check [|"cancel"|] (terminal.ToArray())

    let normalAndFailure () =
        for fails in [false; true] do
            let mutable disposals = 0
            let resource = { new IDisposable with member _.Dispose() = disposals <- disposals + 1 }
            let work = async {
                use owned = resource
                if fails then failwith "body"
                return 42
            }
            let terminal = observe CancellationToken.None work
            check 1 disposals
            check [|if fails then "body" else "success"|] (terminal.ToArray())

    let trampoline () = async {
        let mutable cleanups = 0
        for _ in 1 .. 10000 do
            do! async.TryFinally(async { return () }, fun () -> cleanups <- cleanups + 1)
        check 10000 cleanups
    }

    let downstreamExceptions () =
        for channel in ["success"; "error"; "cancel"] do
            let mutable cleanups = 0
            let calls = ResizeArray<string>()
            let body: Async<unit> = Async.FromContinuations(fun (ok, error, cancelled) ->
                match channel with
                | "success" -> ok ()
                | "error" -> error (Exception "body")
                | _ -> cancelled (OperationCanceledException()))
            let terminal name = calls.Add name; failwith "downstream"
            let caught =
                try
                    Async.StartWithContinuations(
                        async.TryFinally(body, fun () -> cleanups <- cleanups + 1),
                        (fun () -> terminal "success"), (fun _ -> terminal "error"), (fun _ -> terminal "cancel"))
                    "no exception"
                with e -> e.Message
            check "downstream" caught
            check 1 cleanups
            check [|channel|] (calls.ToArray())

#if FABLE_COMPILER && !FABLE_COMPILER_ZIG // (the Python runtime)
module private Runtime =
    open Fable.Core.PyInterop

    type Observation =
        abstract terminal: string array
        abstract errors: string array
        abstract before: string array
        abstract outcome: string array
        abstract listeners: int
        abstract scheduled: int
        abstract cancel_count: int
        abstract retired: bool
        abstract owner_loop: bool
        abstract threads_finished: bool
        abstract pending_before: bool
        abstract pending_after: bool

    type ObserveSleep = delegate of Async<unit> * System.Threading.CancellationToken * string -> Observation
    type ObserveMailbox = delegate of Async<int> * MailboxProcessor<int> * System.Threading.CancellationToken -> Observation
    type ObserveOwnerLoop = delegate of Async<unit> * System.Threading.CancellationToken -> Observation
    type ObserveSettlement = delegate of ((unit -> unit) -> Async<unit>) * System.Threading.CancellationToken * string -> Observation

    let observeSleep: ObserveSleep = import "observe_sleep" "./py/async_runtime.py"
    let observeMailbox: ObserveMailbox = import "observe_mailbox" "./py/async_runtime.py"
    let observeOwnerLoop: ObserveOwnerLoop = import "observe_owner_loop" "./py/async_runtime.py"
    let observeSettlement: ObserveSettlement = import "observe_settlement" "./py/async_runtime.py"
#endif

type DisposableAction(f) =
    interface IDisposable with
        member _.Dispose() = f()

type MyException(value) =
    inherit Exception()
    member _.Value: int = value

let asyncMap f a = async {
    let! a = a
    return f a
}

let sleepAndAssign token (res : Ref<bool>) =
    Async.StartImmediate(async {
        do! Async.Sleep 200
        res.Value <- true
    }, token)

let successWork: Async<string> = Async.FromContinuations(fun (onSuccess,_,_) -> onSuccess "success")
let errorWork: Async<string> = Async.FromContinuations(fun (_,onError,_) -> onError (exn "error"))
let cancelWork: Async<string> = Async.FromContinuations(fun (_,_,onCancel) ->
        System.OperationCanceledException("cancelled") |> onCancel)

[<Fact>]
let ``test TryCancelled preserves success and ordinary errors`` () =
    let mutable compensations = 0
    let wrap work = Async.TryCancelled(work, fun _ -> compensations <- compensations + 1)
    equal [|"42"|] ((observeTryCancelled CancellationToken.None (wrap (async.Return 42))).ToArray())
    for error in [Exception "body"; OperationCanceledException "thrown"] do
        let work: Async<int> = async { return raise error }
        equal [|"error: " + error.Message|] ((observeTryCancelled CancellationToken.None (wrap work)).ToArray())
    let mutable completed = false
    Async.StartWithContinuations(
        Async.TryCancelled(async.Return (), fun _ -> compensations <- compensations + 1),
        (fun () -> completed <- true), raise, raise)
    equal true completed
    equal 0 compensations

[<Fact>]
let ``test TryCancelled preserves cancellation identity and supports reuse`` () =
    for throws in [false; true] do
        let original = OperationCanceledException "original"
        let calls = ResizeArray<string>()
        let mutable handlerSawOriginal = true
        let body: Async<int> = Async.FromContinuations(fun (_, _, cancel) -> cancel original)
        let work = Async.TryCancelled(body, fun error ->
            handlerSawOriginal <- handlerSawOriginal && obj.ReferenceEquals(original, error)
            calls.Add "compensation"
            if throws then failwith "compensation defect")
        for _ in 1 .. 2 do
            Async.StartWithContinuations(work,
                (fun _ -> failwith "unexpected success"),
                (fun _ -> failwith "unexpected error"),
                (fun error ->
                    equal true (obj.ReferenceEquals(original, error))
                    calls.Add "cancel"))
        equal [|"compensation"; "cancel"; "compensation"; "cancel"|] (calls.ToArray())
        equal true handlerSawOriginal

[<Fact>]
let ``test TryCancelled installs nested handlers before cancellation`` () =
    use source = new CancellationTokenSource()
    source.Cancel()
    let mutable entered = false
    let calls = ResizeArray<string>()
    let body = async { entered <- true; return 42 }
    let inner = Async.TryCancelled(body, fun _ -> calls.Add "inner")
    let outer = Async.TryCancelled(inner, fun _ -> calls.Add "outer")
    Async.StartWithContinuations(outer,
        (fun _ -> failwith "unexpected success"), raise,
        (fun _ -> calls.Add "cancel"), source.Token)
    equal false entered
    equal [|"inner"; "outer"; "cancel"|] (calls.ToArray())

[<Fact>]
let ``test TryCancelled handles deferred cancellation`` () =
    runOffThreadPool (fun () ->
        let original = OperationCanceledException "deferred"
        let mutable cancel = fun (_: OperationCanceledException) -> failwith "not started"
        let calls = ResizeArray<string>()
        let body: Async<int> = Async.FromContinuations(fun (_, _, continuation) -> cancel <- continuation)
        let work = Async.TryCancelled(body, fun _ -> calls.Add "compensation")
        Async.StartWithContinuations(work,
            (fun _ -> failwith "unexpected success"), raise,
            (fun error -> equal true (obj.ReferenceEquals(original, error)); calls.Add "cancel"))
        equal 0 calls.Count
        cancel original
        equal [|"compensation"; "cancel"|] (calls.ToArray()))

[<Fact>]
let ``test TryCancelled preserves finalizer order when handlers throw`` () =
    let calls = ResizeArray<string>()
    let body: Async<int> = Async.FromContinuations(fun (_, _, cancel) -> cancel (OperationCanceledException "original"))
    let finalized = async.TryFinally(body, fun () -> calls.Add "finally")
    let inner = Async.TryCancelled(finalized, fun _ -> calls.Add "inner"; failwith "inner defect")
    let outer = Async.TryCancelled(inner, fun _ -> calls.Add "outer"; failwith "outer defect")
    equal [|"cancel: original"|] ((observeTryCancelled CancellationToken.None outer).ToArray())
    equal [|"finally"; "inner"; "outer"|] (calls.ToArray())

[<Fact>]
let ``test TryCancelled propagates downstream errors once`` () =
    runOffThreadPool (fun () ->
        for channel in ["success"; "error"; "cancel"] do
            let mutable compensations = 0
            let calls = ResizeArray<string>()
            let mutable complete = fun () -> failwith "not started"
            let body: Async<int> = Async.FromContinuations(fun (ok, error, cancel) ->
                complete <- fun () ->
                    match channel with
                    | "success" -> ok 42
                    | "error" -> error (Exception "body")
                    | _ -> cancel (OperationCanceledException "original"))
            let work = Async.TryCancelled(body, fun _ -> compensations <- compensations + 1)
            let terminal name = calls.Add name; failwith "downstream"
            Async.StartWithContinuations(work,
                (fun _ -> terminal "success"),
                (fun _ -> terminal "error"),
                (fun _ -> terminal "cancel"))
            let caught =
                try
                    complete ()
                    "no exception"
                with error -> error.Message
            equal "downstream" caught
            equal [|channel|] (calls.ToArray())
            equal (if channel = "cancel" then 1 else 0) compensations)

[<Fact>]
let ``test TryCancelled preserves bounded trampoline execution`` () =
    async {
        let original = OperationCanceledException "deep cancellation"
        let mutable compensations = 0
        let rec loop remaining =
            if remaining = 0 then
                Async.FromContinuations(fun (_, _, cancel) -> cancel original)
            else
                Async.TryCancelled(async {
                    do! async.Return ()
                    return! loop (remaining - 1)
                }, fun _ -> compensations <- compensations + 1)
        do! Async.FromContinuations(fun (ok, error, _) ->
            Async.StartWithContinuations(loop 10000,
                (fun () -> error (Exception "unexpected success")), error,
                (fun cancelled ->
                    if obj.ReferenceEquals(original, cancelled) then ok ()
                    else error (Exception "cancellation identity changed"))))
        equal 10000 compensations
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Simple async translates without exception`` () =
    async { return () }
    |> Async.StartImmediate

[<Fact>]
let ``test Cancellation callback errors expose the first InnerException`` () =
    for count in [1; 2] do
        use cts = new System.Threading.CancellationTokenSource()
        let errors = Array.init count (fun i -> exn (string i))
        let mutable calls = 0
        errors |> Array.iter (fun error ->
            cts.Token.Register(fun () ->
                calls <- calls + 1
                raise error) |> ignore)
        let caught =
            try
                cts.Cancel()
                None
            with ex -> Some ex
        match caught with
        | Some ex ->
            equal errors[count - 1].Message ex.InnerException.Message
            equal true (obj.ReferenceEquals(errors[count - 1], ex.InnerException))
        | None -> failwith "Expected cancellation callback errors"
        equal count calls
        equal true cts.IsCancellationRequested
        cts.Cancel()
        equal count calls


[<Fact>]
let ``test Async while binding works correctly`` () =
    let mutable result = 0
    async {
        while result < 10 do
            result <- result + 1
    } |> Async.StartImmediate
    equal result 10

[<Fact>]
let ``test Async for binding works correctly`` () =
    let inputs = [|1; 2; 3|]
    let mutable result = 0
    async {
        for inp in inputs do
            result <- result + inp
    } |> Async.StartImmediate
    equal result 6

[<Fact>]
let ``test Async exceptions are handled correctly`` () =
    let mutable result = 0
    let f shouldThrow =
        async {
            try
                if shouldThrow then failwith "boom!"
                else result <- 12
            with _ -> result <- 10
        } |> Async.StartImmediate
        result
    f true + f false |> equal 22

[<Fact>]
let ``test Simple async is executed correctly`` () =
    let mutable result = false
    let x = async { return 99 }
    async {
        let! x = x
        let y = 99
        result <- x = y
    }
    |> Async.StartImmediate
    equal result true

[<Fact>]
let ``test async use statements should dispose of resources when they go out of scope`` () =
    let mutable isDisposed = false
    let mutable step1ok = false
    let mutable step2ok = false
    let resource = async {
        return new DisposableAction(fun () -> isDisposed <- true)
    }
    async {
        use! r = resource
        step1ok <- not isDisposed
    }
    //TODO: RunSynchronously would make more sense here but in JS I think this will be ok.
    |> Async.StartImmediate
    step2ok <- isDisposed
    (step1ok && step2ok) |> equal true

[<Fact>]
let ``test Try ... with ... expressions inside async expressions work the same`` () =
    let result = ref ""
    let throw() : unit =
        raise(exn "Boo!")
    let append(x) =
        result.Value <- result.Value + x
    let innerAsync() =
        async {
            append "b"
            try append "c"
                throw()
                append "1"
            with _ -> append "d"
            append "e"
        }
    async {
        append "a"
        try do! innerAsync()
        with _ -> append "2"
        append "f"
    } |> Async.StartImmediate
    equal "abcdef" result.Value

// Disable this test for dotnet as it's failing too many times in Appveyor
#if FABLE_COMPILER

[<Fact>]
let ``test async cancellation works`` () =
    async {
        let res1, res2, res3 = ref false, ref false, ref false
        let tcs1 = new System.Threading.CancellationTokenSource(50)
        let tcs2 = new System.Threading.CancellationTokenSource()
        let tcs3 = new System.Threading.CancellationTokenSource()
        sleepAndAssign tcs1.Token res1
        sleepAndAssign tcs2.Token res2
        sleepAndAssign tcs3.Token res3
        tcs2.Cancel()
        tcs3.CancelAfter(1000)
        do! Async.Sleep 500
        equal false res1.Value
        equal false res2.Value
        equal true res3.Value
    } |> Async.StartImmediate

[<Fact>]
let ``test CancellationTokenSourceRegister works`` () =
    async {
        let mutable x = 0
        let res1 = ref false
        let tcs1 = new System.Threading.CancellationTokenSource(50)
        let foo = tcs1.Token.Register(fun () ->
            x <- x + 1)
        sleepAndAssign tcs1.Token res1
        do! Async.Sleep 500
        equal false res1.Value
        equal 1 x
    } |> Async.StartImmediate
#endif

[<Fact>]
let ``test Async StartWithContinuations works`` () =
    let res1, res2, res3 = ref "", ref "", ref ""
    Async.StartWithContinuations(successWork, (fun x -> res1.Value <- x), ignore, ignore)
    Async.StartWithContinuations(errorWork, ignore, (fun x -> res2.Value <- x.Message), ignore)
    Async.StartWithContinuations(cancelWork, ignore, ignore, (fun x -> res3.Value <- x.Message))
    equal "success" res1.Value
    equal "error" res2.Value
    equal "cancelled" res3.Value

[<Fact>]
let ``test Async.Catch works`` () =
    let assign (res: Ref<string>) = function
        | Choice1Of2 msg -> res.Value <- msg
        | Choice2Of2 (ex: Exception) -> res.Value <- "ERROR: " + ex.Message
    let res1 = ref ""
    let res2 = ref ""
    async {
        let! x1 = successWork |> Async.Catch
        assign res1 x1
        let! x2 = errorWork |> Async.Catch
        assign res2 x2
    } |> Async.StartImmediate
    equal "success" res1.Value
    equal "ERROR: error" res2.Value

[<Fact>]
let ``test Async.Ignore works`` () =
    let res = ref false
    async {
        do! successWork |> Async.Ignore
        res.Value <- true
    } |> Async.StartImmediate
    equal true res.Value

[<Fact>]
let ``test Async.Parallel works`` () =
    async {
        let makeWork i =
            async {
                do! Async.Sleep 200
                return i
            }
        let res: int[] ref = ref [||]
        let works = [makeWork 1; makeWork 2; makeWork 3]
        async {
            let! x = Async.Parallel works
            res.Value <- x
        } |> Async.StartImmediate
        do! Async.Sleep 500
        res.Value |> Array.sum |> equal 6
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.Parallel is lazy`` () =
    async {
        let mutable x = 0

        let add i =
#if FABLE_COMPILER
            x <- x + i
#else
            System.Threading.Interlocked.Add(&x, i) |> ignore<int>
#endif

        let a = Async.Parallel [
            async { add 1 }
            async { add 2 }
        ]

        do! Async.Sleep 100

        equal 0 x

        let! _ = a

        equal 3 x
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.Sequential works`` () =
    async {
        let mutable _aggregate = 0

        let makeWork i =
            async {
                // check that the individual work items run sequentially and not interleaved
                _aggregate <- _aggregate + i
                let copyOfI = _aggregate
                do! Async.Sleep 100
                equal copyOfI _aggregate
                do! Async.Sleep 100
                equal copyOfI _aggregate
                return i
            }
        let works = [ for i in 1 .. 5 -> makeWork i ]
        let now = DateTimeOffset.Now
        let! result = Async.Sequential works
        let ``then`` = DateTimeOffset.Now
        let d = ``then`` - now
        if d.TotalSeconds < 0.99 then
            failwithf "expected sequential operations to take 1 second or more, but took %.3f" d.TotalSeconds
        result |> equal [| 1 .. 5 |]
        result |> Seq.sum |> equal _aggregate
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.Sequential is lazy`` () =
    async {
        let mutable x = 0

        let a = Async.Sequential [
            async { x <- x + 1 }
            async { x <- x + 2 }
        ]

        do! Async.Sleep 100

        equal 0 x

        let! _ = a

        equal 3 x
    } |> Async.RunSynchronously

[<Fact>]
let ``test Interaction between Async and Task works`` () =
    async {
        let mutable res = false
        do!
            async { res <- true }
            |> Async.StartAsTask
            |> Async.AwaitTask

        equal true res
    } |> Async.RunSynchronously

[<Fact>]
let ``test Tasks can be cancelled`` () =
    async {
        use source = new System.Threading.CancellationTokenSource()
        let entered = System.Threading.Tasks.TaskCompletionSource<int>()
        let work = async {
            entered.SetResult 1
            do! Async.Sleep Int32.MaxValue
            failwith "Cancelled task resumed"
        }
        let task = Async.StartAsTask(work, cancellationToken=source.Token)
        let! _ = Async.AwaitTask entered.Task
        source.Cancel()
        let! result = Async.Catch(Async.AwaitTask task)
        match result with
        | Choice2Of2 (:? System.Threading.Tasks.TaskCanceledException) -> ()
        | _ -> failwith "Expected TaskCanceledException through the error continuation"
    } |> Async.RunSynchronously

[<Fact>]
let ``test TaskCanceledException preserves message and inner exception`` () =
    let inner = Exception("inner")
    let error: exn = System.Threading.Tasks.TaskCanceledException("task failure", inner)
    match error with
    | :? System.Threading.Tasks.TaskCanceledException ->
        equal "task failure" error.Message
        equal true (obj.ReferenceEquals(inner, error.InnerException))
    | _ -> failwith "Expected TaskCanceledException"

[<Fact>]
let ``test Deep recursion with async doesn't cause stack overflow`` () =
    async {
        let result = ref false
        let rec trampolineTest (res: bool ref) i = async {
            if i > 100000
            then res.Value <- true
            else return! trampolineTest res (i+1)
        }
        do! trampolineTest result 0
        equal result.Value true
    } |> Async.StartImmediate

[<Fact>]
let ``test Nested failure propagates in async expressions`` () =
    async {
        let data = ref ""
        let f1 x =
            async {
                try
                    failwith "1"
                    return x
                with
                | e -> return! failwith ("2 " + e.Message)
            }
        let f2 x =
            async {
                try
                    return! f1 x
                with
                | e -> return! failwith ("3 " + e.Message)
            }
        let f() =
            async {
                try
                    let! y = f2 4
                    return ()
                with
                | e -> data.Value <- e.Message
            }
            |> Async.StartImmediate
        f()
        do! Async.Sleep 100
        equal "3 2 1" data.Value
    } |> Async.StartImmediate

[<Fact>]
let ``test Try .. finally expressions inside async expressions work`` () =
    async {
        let data = ref ""
        async {
            try data.Value <- data.Value + "1 "
            finally data.Value <- data.Value + "2 "
        } |> Async.StartImmediate
        async {
            try
                try failwith "boom!"
                finally data.Value <- data.Value + "3"
            with _ -> ()
        } |> Async.StartImmediate
        do! Async.Sleep 100
        equal "1 2 3" data.Value
    } |> Async.StartImmediate

[<Fact>]
let ``test Final statement inside async expressions can throw`` () =
    async {
        let data = ref ""
        let f() = async {
            try data.Value <- data.Value + "1 "
            finally failwith "boom!"
        }
        async {
            try
                do! f()
                return ()
            with
            | e -> data.Value <- data.Value + e.Message
        }
        |> Async.StartImmediate
        do! Async.Sleep 100
        equal "1 boom!" data.Value
    } |> Async.StartImmediate

[<Fact>]
let ``test Async.Bind propagates exceptions`` () = // See #724
    async {
        let task1 name = async {
            // printfn "testing with %s" name
            if name = "fail" then
                failwith "Invalid access credentials"
            return "Ok"
        }

        let task2 name = async {
            // printfn "testing with %s" name
            do! Async.Sleep 100 //difference between task1 and task2
            if name = "fail" then
                failwith "Invalid access credentials"
            return "Ok"
        }

        let doWork name task =
            let catch comp = async {
                let! res = Async.Catch comp
                return
                    match res with
                    | Choice1Of2 str -> str
                    | Choice2Of2 ex -> ex.Message
            }
            // printfn "doing work - %s" name
            async {
                let! a = task "work" |> catch
                // printfn "work - %A" a
                let! b = task "fail" |> catch
                // printfn "fail - %A" b
                return a, b
            }

        let! res1 = doWork "task1" task1
        let! res2 = doWork "task2" task2
        equal ("Ok", "Invalid access credentials") res1
        equal ("Ok", "Invalid access credentials") res2
    } |> Async.StartImmediate


[<Fact>]
let ``test Async.StartChild works`` () =
    async {
        let mutable x = ""
        let taskA = async {
            do! Async.Sleep 500
            x <- x + "D"
            return "E"
        }
        let taskB = async {
            do! Async.Sleep 100
            x <- x + "C"
            return "F"
        }
        let! result1Async = taskA |> Async.StartChild // start first request but do not wait
        let! result2Async = taskB |> Async.StartChild // start second request in parallel
        x <- x + "AB"
        let! result1 = result1Async
        let! result2 = result2Async
        x <- x + result1 + result2
        equal x "ABCDEF"
    } |> Async.StartImmediate

[<Fact>]
let ``test Async.StartChild applies timeout`` () =
    async {
        let mutable x = ""

        let task = async {
            // A busy .NET runner can time out before this child is scheduled.
            do! Async.Sleep 1_000
            x <- x + "X" // Never hit
        }

        try
            let! childTask = Async.StartChild (task, 200)

            do! childTask
        with
            | :? TimeoutException ->
                x <- x + "B"

        x <- x + "C"

        equal "BC" x
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with timeout completes when computation finishes before timeout`` () = // See #4481
    async {
        let fast = async { do! Async.Sleep 10 }
        try
            let! child = Async.StartChild(fast, 1_000)
            do! child
            equal true true // should reach here
        with
            | :? TimeoutException ->
                failwith "should not time out"
    } |> Async.RunSynchronously

let private assertChildFailure startChild (error: exn) =
    async {
        let failing: Async<int> = async {
            do! Async.Sleep 10
            return raise error
        }
        let! child = startChild(failing, 60_000)
        let! result = Async.Catch child
        match result with
        | Choice2Of2 caught -> obj.ReferenceEquals(error, caught) |> equal true
        | _ -> failwith "Expected child failure"
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild preserves child TimeoutException`` () =
    assertChildFailure
        (fun (computation, timeout) -> Async.StartChild(computation, timeout))
        (TimeoutException("child timeout"))

let private assertChildTimeout startChild assertError =
    async {
        let pending: Async<int> = Async.FromContinuations(ignore)
        let! child = startChild(pending, 0)
        let! result = Async.Catch child
        match result with
        | Choice2Of2 ex -> assertError ex
        | _ -> failwith "Expected child timeout"
    } |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild zero timeout raises TimeoutException`` () =
    assertChildTimeout
        (fun (computation, timeout) -> Async.StartChild(computation, timeout))
        (fun ex -> ex :? TimeoutException |> equal true)

#if FABLE_COMPILER && !FABLE_COMPILER_ZIG // (the Python runtime)
module private NativeTimeout =
    open Fable.Core
    open Fable.Core.PyInterop

    let startChild: Func<Async<int>, int, Async<Async<int>>> = import "start_child" "fable_library.async_"
    let timeoutError: obj = import "TimeoutError" "builtins"

    [<Emit("TimeoutError($0)")>]
    let createTimeoutError (message: string) : exn = nativeOnly

[<Fact>]
let ``test Python start_child deadline matches both timeout types`` () =
    assertChildTimeout
        (fun (computation, timeout) -> NativeTimeout.startChild.Invoke(computation, timeout))
        (fun ex ->
            ex :? TimeoutException |> equal true
            Fable.Core.PyInterop.pyInstanceof ex NativeTimeout.timeoutError |> equal true)

[<Fact>]
let ``test Async.StartChild preserves child Python TimeoutError`` () =
    assertChildFailure
        (fun (computation, timeout) -> Async.StartChild(computation, timeout))
        (NativeTimeout.createTimeoutError "child timeout")

[<Fact>]
let ``test Python start_child preserves child TimeoutError`` () =
    assertChildFailure
        (fun (computation, timeout) -> NativeTimeout.startChild.Invoke(computation, timeout))
        (NativeTimeout.createTimeoutError "child timeout")
#endif

[<Fact>]
let ``test Unit arguments are erased`` () = // See #1832
    let mutable token = 0
    async {
        let! res =
            async.Return 5
            |> asyncMap (fun x -> token <- x)
        equal 5 token
        res
    } |> Async.StartImmediate

[<Fact>]
let ``test Can use custom exceptions in async workflows #2396`` () =
    let workflow(): Async<unit> = async {
        return MyException(7) |> raise
    }
    let parentWorkflow() =
        async {
            try
                do! workflow()
                return 100
            with
            | :? MyException as ex -> return ex.Value
        }
    async {
        let! res = parentWorkflow()
        equal 7 res
    } |> Async.StartImmediate

[<Fact>]
let ``test Async.Sleep works correctly with TimeSpan argument`` () =
    async {
        let mutable executionOrder = ""

        // Test that TimeSpan(0, 1, 0) means 1 minute = 60,000 milliseconds, not 600,000,000 milliseconds
        let shortTask = async {
            do! Async.Sleep(System.TimeSpan(0, 0, 0, 0, 100)) // 100 milliseconds
            executionOrder <- executionOrder + "A"
        }

        let mediumTask = async {
            do! Async.Sleep(System.TimeSpan(0, 0, 0, 0, 300)) // 300 milliseconds
            executionOrder <- executionOrder + "B"
        }

        // Start both tasks in parallel
        let! shortTaskAsync = shortTask |> Async.StartChild
        let! mediumTaskAsync = mediumTask |> Async.StartChild

        // Wait for both to complete
        do! shortTaskAsync
        do! mediumTaskAsync

        // Verify execution order - shorter TimeSpan should complete first
        equal "AB" executionOrder

        // Test direct comparison with integer milliseconds
        let startTime = System.DateTime.Now
        do! Async.Sleep(System.TimeSpan(0, 0, 0, 0, 200)) // 200ms TimeSpan
        let endTime = System.DateTime.Now
        let elapsedMs = (endTime - startTime).TotalMilliseconds

        // Should be approximately 200ms, not 2,000,000ms (which would be 2000 seconds)
        // Allow some tolerance for timing variations
        let isReasonableTime = elapsedMs >= 150.0 && elapsedMs <= 500.0
        equal true isReasonableTime
    } |> Async.StartImmediate

[<Fact>]
let ``test Async.AwaitEvent fires continuation when event is triggered`` () =
    let ev = Event<int>()
    Async.StartImmediate(async {
        let! v = Async.AwaitEvent ev.Publish
        equal 42 v
    })
    ev.Trigger(42)

[<Fact>]
let ``test Async.AwaitEvent with cancelAction invokes it on cancellation`` () =
    let ev = Event<int>()
    let cts = new System.Threading.CancellationTokenSource()
    let mutable cancelCalled = false
    Async.StartImmediate(async {
        let! _ = Async.AwaitEvent(ev.Publish, fun () -> cancelCalled <- true)
        ()
    }, cts.Token)
    cts.Cancel()
    equal true cancelCalled

[<Fact>]
let ``test FromContinuations unit and generic values`` () =
    let fromValue value = Async.FromContinuations(fun (ok, _, _) -> ok value)
    let mutable completed = 0
    let unitWork: Async<unit> = Async.FromContinuations(fun (ok, _, _) -> ok ())
    Async.StartWithContinuations(unitWork, (fun () -> completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(fromValue (), (fun () -> completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(fromValue 42, (fun value -> equal 42 value; completed <- completed + 1), raise, raise)
    equal 3 completed

[<Fact>]
let ``test unit continuations preserve captured callbacks`` () =
    let mutable calls = 0
    let rec genericDeadline callback value remaining =
        if remaining > 0 then genericDeadline callback value (remaining - 1)
        else Async.StartWithContinuations(async { return value }, (fun result -> callback result), raise, raise)
    let rec unitDeadline (callback: unit -> unit) remaining =
        if remaining > 0 then unitDeadline callback (remaining - 1)
        else Async.StartWithContinuations(async { return () }, (fun () -> callback ()), raise, raise)
    genericDeadline (fun () -> calls <- calls + 1) () 2
    unitDeadline (fun () -> calls <- calls + 1) 2
    let rec namedUnitCapture (__unit: int) remaining =
        if remaining > 0 then namedUnitCapture __unit (remaining - 1)
        else Async.StartWithContinuations(async { return () }, (fun () -> calls <- calls + __unit), raise, raise)
    namedUnitCapture 3 2
    equal 5 calls

[<Fact>]
let ``test cooperative cancellation stops at the next async boundary`` () =
    use source = new System.Threading.CancellationTokenSource()
    let mutable finalizers = 0
    let mutable terminal = ""
    let mutable reached = false
    let work = async {
        try
            source.Cancel()
            do! async { return () }
            reached <- true
        finally
            finalizers <- finalizers + 1
    }
    Async.StartWithContinuations(work, (fun () -> terminal <- "success"), (fun _ -> terminal <- "error"), (fun _ -> terminal <- "cancel"), source.Token)
    equal false reached
    equal 1 finalizers
    equal "cancel" terminal


[<Fact>]
let ``test finalizer failure overrides success once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! successWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun error -> terminal.Add error.Message), (fun _ -> terminal.Add "cancel"))
    equal [| "finalizer" |] (terminal.ToArray())
    equal 1 finalizers

[<Fact>]
let ``test finalizer failure overrides body failure once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! errorWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun error -> terminal.Add error.Message), (fun _ -> terminal.Add "cancel"))
    equal [| "finalizer" |] (terminal.ToArray())
    equal 1 finalizers

[<Fact>]
let ``test finalizer failure preserves cancellation once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! cancelWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun _ -> terminal.Add "error"), (fun _ -> terminal.Add "cancel"))
    equal [| "cancel" |] (terminal.ToArray())
    equal 1 finalizers

#if FABLE_COMPILER && !FABLE_COMPILER_ZIG // (the Python runtime and timers)
let private checkSleep cancelFirst throws =
    use source = new System.Threading.CancellationTokenSource()
    let mutable finalizers = 0
    let work = async {
        try do! Async.Sleep 100
        finally
            finalizers <- finalizers + 1
            if throws then failwith "finalizer"
    }
    let result = Runtime.observeSleep.Invoke(work, source.Token, if cancelFirst then "cancel" else "timeout")
    let expected = if cancelFirst then "cancel" elif throws then "error" else "success"
    equal [| expected |] result.terminal
    equal 1 finalizers
    equal 0 result.listeners
    equal 1 result.scheduled
    equal true result.retired
    equal 1 result.cancel_count
    if throws && not cancelFirst then equal [| "finalizer" |] result.errors
    else equal [||] result.errors

[<Fact>]
let ``test cancelled Sleep ignores stale timers and cleans up`` () =
    checkSleep true false

[<Fact>]
let ``test completed Sleep ignores cancellation and stale timers`` () =
    checkSleep false false

[<Fact>]
let ``test cancelled Sleep ignores a throwing finalizer and stale timers`` () =
    checkSleep true true

[<Fact>]
let ``test precancelled Sleep does not execute or schedule`` () =
    use source = new System.Threading.CancellationTokenSource()
    let mutable reached = false
    let work = async {
        reached <- true
        do! Async.Sleep 100
    }
    let result = Runtime.observeSleep.Invoke(work, source.Token, "precancel")
    equal [| "cancel" |] result.terminal
    equal false reached
    equal 0 result.scheduled
    equal 0 result.listeners

[<Fact>]
let ``test idle Receive is cancelled by its token and keeps later posts queued`` () =
    use source = new System.Threading.CancellationTokenSource()
    let mailbox = new MailboxProcessor<int>((fun _ -> async { return () }), source.Token)
    let result = Runtime.observeMailbox.Invoke(mailbox.Receive(), mailbox, source.Token)
    equal [| "cancel" |] result.before
    equal false result.pending_before
    equal [| "cancel" |] result.terminal
    equal false result.pending_after
    equal 0 result.listeners
    equal [| "42" |] result.outcome

[<Fact>]
let ``test Sleep cancellation from another thread runs on the owner loop`` () =
    use source = new System.Threading.CancellationTokenSource()
    let result = Runtime.observeOwnerLoop.Invoke(Async.Sleep 100000, source.Token)
    equal [| "cancel" |] result.terminal
    equal true result.owner_loop
    equal true result.threads_finished
    equal 0 result.listeners

let private checkSettlement winner =
    use source = new System.Threading.CancellationTokenSource()
    let mutable finalizers = 0
    let makeWork timeout = async {
        try do! Async.Sleep 100
        finally
            finalizers <- finalizers + 1
            timeout ()
    }
    let result = Runtime.observeSettlement.Invoke(makeWork, source.Token, winner)
    equal [| winner |] result.outcome
    equal [| if winner = "timeout" then "success" else "cancel" |] result.terminal
    equal 1 finalizers
    equal true result.threads_finished
    equal 0 result.listeners
    equal true result.retired
    equal 1 result.cancel_count

[<Fact>]
let ``test reply wins concurrent reply cancellation and timeout settlement`` () =
    checkSettlement "reply"

[<Fact>]
let ``test cancellation wins concurrent reply cancellation and timeout settlement`` () =
    checkSettlement "cancel"

[<Fact>]
let ``test timeout wins concurrent reply cancellation and timeout settlement`` () =
    checkSettlement "timeout"

[<Fact>]
let ``test cancellation during Sleep installation releases resources`` () =
    use source = new System.Threading.CancellationTokenSource()
    let result = Runtime.observeSleep.Invoke(Async.Sleep 100, source.Token, "install_cancel")
    equal [| "cancel" |] result.terminal
    equal 0 result.listeners
    equal 1 result.scheduled
    equal true result.retired
    equal 1 result.cancel_count

[<Fact>]
let ``test failed Sleep installation releases its registration`` () =
    use source = new System.Threading.CancellationTokenSource()
    let result = Runtime.observeSleep.Invoke(Async.Sleep 100, source.Token, "install_error")
    equal [| "error" |] result.terminal
    equal [| "scheduler" |] result.errors
    equal 0 result.listeners
    equal 0 result.scheduled
#endif

[<Fact>]
let ``test cancelling a waiting Receive reports cancel and keeps later posts queued`` () =
    async {
        use source = new System.Threading.CancellationTokenSource()
        let mailbox = new MailboxProcessor<int>((fun _ -> async { return () }), source.Token)
        let! outcome =
            Async.FromContinuations(fun (ok, _, _) ->
                Async.StartWithContinuations(mailbox.Receive(), (fun value -> ok $"value {value}"), (fun _ -> ok "error"), (fun _ -> ok "cancel"), source.Token)
                source.Cancel())
        equal "cancel" outcome
        mailbox.Post 42
        let! next = mailbox.Receive()
        equal 42 next
    } |> Async.RunSynchronously

[<Fact>]
let ``test cancelling the mailbox token cancels a body waiting in Receive`` () =
    async {
        use source = new System.Threading.CancellationTokenSource()
        let! outcome =
            Async.FromContinuations(fun (ok, _, _) ->
                MailboxProcessor<int>.Start((fun inbox -> async {
                    let received = ref None
                    try
                        source.CancelAfter 50
                        let! message = inbox.Receive()
                        received.Value <- Some message
                    finally
                        match received.Value with
                        | Some message -> ok $"received {message}"
                        | None -> ok "cancelled" }), source.Token)
                |> ignore)
        equal "cancelled" outcome
    } |> Async.RunSynchronously

[<Fact>]
let ``test TryFinally installs cleanup before pre-cancellation`` () =
    FinalizerRegressions.preCancelled ()

[<Fact>]
let ``test pre-cancelled nested TryFinally only runs outer cleanup`` () =
    FinalizerRegressions.nestedPreCancelled ()

[<Fact>]
let ``test cancelled acquisition disposes use and use bang resources`` () =
    FinalizerRegressions.cancelledAcquisition ()

[<Fact>]
let ``test resource cleanup runs once on success and failure`` () =
    FinalizerRegressions.normalAndFailure ()

[<Fact>]
let ``test TryFinally preserves bounded trampoline execution`` () =
    FinalizerRegressions.trampoline () |> Async.RunSynchronously

[<Fact>]
let ``test TryFinally propagates downstream continuation errors once`` () =
    FinalizerRegressions.downstreamExceptions ()

let private fromGenericCallback (callback: ('T -> unit) -> (exn -> unit) -> (OperationCanceledException -> unit) -> unit) : Async<'T> =
    Async.FromContinuations(fun (ok, error, cancelled) -> callback ok error cancelled)

let private forwardGenericValue (continuation: 'T -> unit) (value: 'T) =
    continuation value

[<Fact>]
let ``test unit FromContinuations accepts a forwarded generic value`` () =
    let work: Async<unit> = Async.FromContinuations(fun (ok, _, _) -> forwardGenericValue ok ())
    let mutable completed = false
    Async.StartWithContinuations(work, (fun () -> completed <- true), raise, raise)
    equal true completed

[<Fact>]
let ``test generic FromContinuations accepts erased unit callbacks`` () =
    let calls = ResizeArray<string>()
    let start work = Async.StartWithContinuations(work, (fun _ -> calls.Add "success"), (fun e -> calls.Add e.Message), (fun e -> calls.Add e.Message))
    let unitWork: Async<unit> = fromGenericCallback (fun ok _ _ -> ok ())
    start unitWork
    let valueWork = fromGenericCallback (fun ok _ _ -> ok 42)
    Async.StartWithContinuations(valueWork, (fun value -> equal 42 value; calls.Add "value"), raise, raise)
    let errorWork: Async<unit> = fromGenericCallback (fun _ error _ -> error (exn "error"))
    start errorWork
    let cancelWork: Async<unit> = fromGenericCallback (fun _ _ cancelled -> cancelled (OperationCanceledException("cancel")))
    start cancelWork
    equal [|"success"; "value"; "error"; "cancel"|] (calls.ToArray())

let private invokeGenericCallback (callback: ('T -> unit) -> 'Result) (value: 'T) : 'Result =
    callback (fun received -> equal value received)

[<Fact>]
let ``test generic unit callback adaptation preserves return types`` () =
    equal 42 (invokeGenericCallback (fun ok -> ok (); 42) ())
    equal "unit" (invokeGenericCallback (fun ok -> ok (); "unit") ())
    equal "value" (invokeGenericCallback (fun ok -> ok 7; "value") 7)

type private CallbackRunner =
    static member Run(callback: ('T -> unit) -> 'Result, value: 'T, [<ParamArray>] extra: int[]) : 'Result =
        callback (fun received -> equal value received)

[<Fact>]
let ``test generic unit callback adaptation covers local functions and param arrays`` () =
    let run (callback: ('T -> unit) -> 'Result) (value: 'T) : 'Result =
        callback (fun received -> equal value received)
    equal 42 (run (fun ok -> ok (); 42) ())
    equal "value" (run (fun ok -> ok 7; "value") 7)
    equal 42 (CallbackRunner.Run((fun ok -> ok (); 42), (), 1, 2))
    equal "value" (CallbackRunner.Run((fun ok -> ok 7; "value"), 7))

[<Fact>]
let ``test Async try with does not run with branch when body succeeds`` () =
    let work = async {
        try
            return 1
        with _ ->
            return 99 }
    let mutable result = 0
    Async.StartWithContinuations(work, (fun r -> result <- r), ignore, ignore)
    equal 1 result

[<Fact>]
let ``test Exception thrown by the continuation is not redirected to the with branch`` () =
    let work = async {
        try
            return 1
        with _ ->
            return 99 }
    let mutable calls = 0
    throwsAnyError (fun () ->
        Async.StartWithContinuations(
            work,
            (fun _ -> calls <- calls + 1; failwith "boom from continuation"),
            ignore,
            ignore))
    equal 1 calls

[<Fact>]
let ``test Exception thrown by the continuation is not redirected through a bind`` () =
    let work = async {
        let! x = async { return 1 }
        return x + 1 }
    let calls = ResizeArray<string>()
    throwsAnyError (fun () ->
        Async.StartWithContinuations(
            work,
            (fun value -> calls.Add (string value); failwith "boom from continuation"),
            (fun _ -> calls.Add "error"),
            (fun _ -> calls.Add "cancel")))
    equal [|"2"|] (calls.ToArray())

[<Fact>]
let ``test FromContinuations rejects a second completion`` () =
    let unitCalls = ResizeArray<string>()
    let unitWork: Async<unit> = Async.FromContinuations(fun (ok, _, _) -> ok (); ok ())
    throwsAnyError (fun () ->
        Async.StartWithContinuations(unitWork, (fun () -> unitCalls.Add "success"), (fun _ -> unitCalls.Add "error"), (fun _ -> unitCalls.Add "cancel")))
    equal true (unitCalls.Count <= 1)
    equal false (unitCalls.Contains "error")
    equal false (unitCalls.Contains "cancel")

    let valueCalls = ResizeArray<string>()
    let valueWork = Async.FromContinuations(fun (ok, _, _) -> ok 42; ok 43)
    throwsAnyError (fun () ->
        Async.StartWithContinuations(valueWork, (fun v -> valueCalls.Add (string v)), (fun _ -> valueCalls.Add "error"), (fun _ -> valueCalls.Add "cancel")))
    equal true (valueCalls.Count <= 1)
    equal false (valueCalls.Contains "43")
    equal false (valueCalls.Contains "error")
    equal false (valueCalls.Contains "cancel")

// ---- ported from tests/Js/Main (2026-11-16) ----




type Message = string * AsyncReplyChannel<string>


















[<Fact>]
let ``test Generic FromContinuations accepts erased unit callbacks`` () =
    let calls = ResizeArray<string>()
    let start work = Async.StartWithContinuations(work, (fun _ -> calls.Add "success"), (fun e -> calls.Add e.Message), (fun e -> calls.Add e.Message))
    let unitWork: Async<unit> = fromGenericCallback (fun ok _ _ -> ok ())
    start unitWork
    let valueWork = fromGenericCallback (fun ok _ _ -> ok 42)
    Async.StartWithContinuations(valueWork, (fun value -> equal 42 value; calls.Add "value"), raise, raise)
    let errorWork: Async<unit> = fromGenericCallback (fun _ error _ -> error (exn "error"))
    start errorWork
    let cancelWork: Async<unit> = fromGenericCallback (fun _ _ cancelled -> cancelled (OperationCanceledException("cancel")))
    start cancelWork
    equal [|"success"; "value"; "error"; "cancel"|] (calls.ToArray())

[<Fact>]
let ``test Generic unit continuations work through recursive bindings and aliases`` () =
    let mutable recurse = true
    let rec fromValue value =
        if recurse then
            recurse <- false
            fromValue value
        else Async.FromContinuations(fun (ok, _, _) -> ok value)
    let alias = fromValue
    let mutable completed = 0
    Async.StartWithContinuations(fromValue (), (fun () -> completed <- completed + 1), raise, raise)
    recurse <- true
    Async.StartWithContinuations(alias (), (fun () -> completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(alias 42, (fun value -> equal 42 value; completed <- completed + 1), raise, raise)
    equal 3 completed

[<Fact>]
let ``test Generic unit continuations work through tuple pattern bindings`` () =
    let fromValue, fromOther =
        (fun (value: 'T) -> Async.FromContinuations(fun (ok, _, _) -> ok value)),
        (fun (value: 'U) -> Async.FromContinuations(fun (ok, _, _) -> ok value))
    let mutable completed = 0
    Async.StartWithContinuations(fromValue (), (fun () -> completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(fromValue 42, (fun value -> equal 42 value; completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(fromOther (), (fun () -> completed <- completed + 1), raise, raise)
    Async.StartWithContinuations(fromOther "a", (fun value -> equal "a" value; completed <- completed + 1), raise, raise)
    equal 4 completed

[<Fact>]
let ``test Generic unit continuations work inside nested lambdas and object expressions`` () =
    let fromValue value = Async.FromContinuations(fun (ok, _, _) -> ok value)
    let mutable completed = 0
    let startUnit () = Async.StartWithContinuations(fromValue (), (fun () -> completed <- completed + 1), raise, raise)
    let disposable =
        { new IDisposable with
            member _.Dispose() =
                Async.StartWithContinuations(fromValue (), (fun () -> completed <- completed + 1), raise, raise) }
    startUnit ()
    startUnit ()
    disposable.Dispose()
    Async.StartWithContinuations(fromValue 42, (fun value -> equal 42 value; completed <- completed + 1), raise, raise)
    equal 4 completed

[<Fact>]
let ``test Unit continuations preserve captured callbacks`` () =
    let mutable calls = 0
    let rec genericDeadline callback value remaining =
        if remaining > 0 then genericDeadline callback value (remaining - 1)
        else Async.StartWithContinuations(async { return value }, (fun result -> callback result), raise, raise)
    let rec unitDeadline (callback: unit -> unit) remaining =
        if remaining > 0 then unitDeadline callback (remaining - 1)
        else Async.StartWithContinuations(async { return () }, (fun () -> callback ()), raise, raise)
    genericDeadline (fun () -> calls <- calls + 1) () 2
    unitDeadline (fun () -> calls <- calls + 1) 2
    equal 2 calls

[<Fact>]
let ``test Finalizer failure overrides success once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! successWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun error -> terminal.Add error.Message), (fun _ -> terminal.Add "cancel"))
    equal [| "finalizer" |] (terminal.ToArray())
    equal 1 finalizers

[<Fact>]
let ``test Finalizer failure overrides body failure once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! errorWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun error -> terminal.Add error.Message), (fun _ -> terminal.Add "cancel"))
    equal [| "finalizer" |] (terminal.ToArray())
    equal 1 finalizers

[<Fact>]
let ``test Finalizer failure preserves cancellation once`` () =
    let mutable finalizers = 0
    let terminal = ResizeArray<string>()
    let work = async {
        try return! cancelWork
        finally
            finalizers <- finalizers + 1
            failwith "finalizer"
    }
    Async.StartWithContinuations(work, (fun _ -> terminal.Add "success"), (fun _ -> terminal.Add "error"), (fun _ -> terminal.Add "cancel"))
    equal [| "cancel" |] (terminal.ToArray())
    equal 1 finalizers

[<Fact>]
let ``test Non captured exception in async is propagated when using Async.StartImmediate`` () =
    throwsAnyError (fun _ ->
        async {
            failwith "boom!"
        } |> Async.StartImmediate
    )

[<Fact>]
let ``test Async.StartWithContinuations works`` () =
    let res1, res2, res3 = ref "", ref "", ref ""
    Async.StartWithContinuations(successWork, (fun x -> res1 := x), ignore, ignore)
    Async.StartWithContinuations(errorWork, ignore, (fun x -> res2 := x.Message), ignore)
    Async.StartWithContinuations(cancelWork, ignore, ignore, (fun x -> res3 := x.Message))
    equal "success" !res1
    equal "error" !res2
    equal "cancelled" !res3

[<Fact>]
let ``test Async try .. with returns correctly from 'with' branch`` () =
    let work = async {
        try
          failwith "testing"
          return -1
        with e ->
          return 42 }
    let mutable result = 0
    Async.StartWithContinuations(work, (fun r -> result <- r), ignore, ignore)
    equal result 42

[<Fact>]
let ``test Async try .. with does not run 'with' branch when body succeeds`` () =
    let work = async {
        try
          return 1
        with _ ->
          return 99 }
    let mutable result = 0
    Async.StartWithContinuations(work, (fun r -> result <- r), ignore, ignore)
    equal result 1

[<Fact>]
let ``test Exception thrown by the continuation is not redirected to the 'with' branch`` () =
    let work = async {
        try
          return 1
        with _ ->
          return 99 }
    let mutable calls = 0
    throwsAnyError (fun () ->
        Async.StartWithContinuations(
            work,
            (fun _ -> calls <- calls + 1; failwith "boom from continuation"),
            ignore,
            ignore))
    equal 1 calls

[<Fact>]
let ``test Async.Parallel rejects a maxDegreeOfParallelism below 1`` () =
    let mutable raised = false
    try
        Async.Parallel([ async { return 1 } ], maxDegreeOfParallelism = 0) |> ignore
    with :? ArgumentException -> raised <- true
    equal true raised

[<Fact>]
let ``test Cancellation registrations dispose pending callbacks and invoke late callbacks`` () =
    use source = new System.Threading.CancellationTokenSource()
    let calls = ResizeArray<int>()
    let first: IDisposable = source.Token.Register(fun () -> calls.Add 1)
    let mutable second: IDisposable = null
    second <- source.Token.Register(fun () ->
        second.Dispose()
        first.Dispose()
        calls.Add 2)
    source.Cancel()
    let late: IDisposable = source.Token.Register((fun state -> calls.Add (unbox<int> state)), box 0)
    late.Dispose()
    second.Dispose()
    equal [| 2; 0 |] (calls.ToArray())

[<Fact>]
let ``test Cancellation callback failure preserves remaining listeners`` () =
    use source = new System.Threading.CancellationTokenSource()
    let mutable remaining = 0
    let mutable errors = -1
    source.Token.Register(fun () -> remaining <- remaining + 1) |> ignore
    source.Token.Register(fun () -> failwith "callback") |> ignore
    try source.Cancel()
    with error ->
        errors <- (error :?> AggregateException).InnerExceptions.Count
    equal 1 errors
    equal 1 remaining

[<Fact>]
let ``test AggregateException holds its inner exceptions`` () =
    let a = exn "a"
    let b = InvalidOperationException "b"
    let describe (e: AggregateException) =
        e.Message, e.InnerExceptions.Count, (if isNull e.InnerException then "" else e.InnerException.Message)
    describe (AggregateException()) |> equal ("One or more errors occurred.", 0, "")
    describe (AggregateException("m")) |> equal ("m", 0, "")
    describe (AggregateException("m", a)) |> equal ("m (a)", 1, "a")
    describe (AggregateException(a, b)) |> equal ("One or more errors occurred. (a) (b)", 2, "a")
    describe (AggregateException("m", [| a; b |])) |> equal ("m (a) (b)", 2, "a")
    describe (AggregateException([ a; b ] :> seq<exn>)) |> equal ("One or more errors occurred. (a) (b)", 2, "a")
    let e = AggregateException(a, b)
    [ for x in e.InnerExceptions -> x.Message ] |> equal [ "a"; "b" ]
    e.InnerExceptions.[1].Message |> equal "b"
    AggregateException(e, exn "c").Flatten().InnerExceptions.Count |> equal 3



// ---- ported from tests/Js/Main (2026-11-16, last) ----

[<Fact>]
let ``test Cancelling a waiting Receive reports cancel and keeps later posts queued`` () =
    async {
        use source = new System.Threading.CancellationTokenSource()
        let mailbox = new MailboxProcessor<int>((fun _ -> async { return () }), source.Token)
        let! outcome =
            Async.FromContinuations(fun (ok, _, _) ->
                Async.StartWithContinuations(mailbox.Receive(), (fun value -> ok $"value {value}"), (fun _ -> ok "error"), (fun _ -> ok "cancel"), source.Token)
                source.Cancel())
        equal "cancel" outcome
        mailbox.Post 42
        let! next = mailbox.Receive()
        equal 42 next
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Cancelling the mailbox token cancels a body waiting in Receive`` () =
    async {
        use source = new System.Threading.CancellationTokenSource()
        let! outcome =
            Async.FromContinuations(fun (ok, _, _) ->
                MailboxProcessor<int>.Start((fun inbox -> async {
                    let received = ref None
                    try
                        source.CancelAfter 50
                        let! message = inbox.Receive()
                        received.Value <- Some message
                    finally
                        match received.Value with
                        | Some message -> ok $"received {message}"
                        | None -> ok "cancelled" }), source.Token)
                |> ignore)
        equal "cancelled" outcome
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async cancellation works`` () =
    async {
        let res1, res2, res3 = ref false, ref false, ref false
        let tcs1 = new System.Threading.CancellationTokenSource(50)
        let tcs2 = new System.Threading.CancellationTokenSource()
        let tcs3 = new System.Threading.CancellationTokenSource()
        sleepAndAssign tcs1.Token res1
        sleepAndAssign tcs2.Token res2
        sleepAndAssign tcs3.Token res3
        tcs2.Cancel()
        tcs3.CancelAfter(1000)
        do! Async.Sleep 500
        equal false !res1
        equal false !res2
        equal true !res3
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test CancellationTokenSource.Register works`` () =
    async {
        let mutable x = 0
        let res1 = ref false
        let tcs1 = new System.Threading.CancellationTokenSource(50)
        let foo = tcs1.Token.Register(fun () ->
            x <- x + 1)
        sleepAndAssign tcs1.Token res1
        do! Async.Sleep 500
        equal false !res1
        equal 1 x
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test CancellationToken can be disposed`` () =
    // See #2879
    async {
        let res1 = ref false
        do
            use tcs1 = new System.Threading.CancellationTokenSource()
            sleepAndAssign tcs1.Token res1
        do! Async.Sleep 300
        // Disposing the CancellationToken doesn't cancel the operation
        equal true !res1
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor.post works`` () =
    async {
        let mutable res = None
        let agent = new MailboxProcessor<int>(fun inbox ->
            let rec messageLoop() = async {
                let! msg = inbox.Receive()
                match msg with
                | 3 -> () // Finish loop
                | _ ->
                    res <- Some msg
                    return! messageLoop()
            }
            messageLoop()
        )
        agent.Post(1)
        equal None res // Mailbox hasn't started yet
        agent.Start()
        agent.Post(2)
        // Not necessary in the JS implementation, but in .NET
        // MailboxProcessor works in the background so we must wait a bit
        do! Async.Sleep 200
        equal (Some 2) res
        agent.Post(3)
        equal (Some 2) res  // Mailbox has finished
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor.postAndAsyncReply works`` () =
    async {
        let formatString = "Msg: {0} - {1}"
        let agent = MailboxProcessor<Message>.Start(fun inbox ->
            let rec loop n = async {
                let! (message, replyChannel) = inbox.Receive()
                do! Async.Sleep(100) // Delay a bit
                replyChannel.Reply(String.Format(formatString, n, message))
                if message <> "Bye" then do! loop (n + 1)
            }
            loop 0)
        let! resp = agent.PostAndAsyncReply(fun replyChannel -> "Hi", replyChannel)
        equal "Msg: 0 - Hi" resp
        let! resp = agent.PostAndAsyncReply(fun replyChannel -> "Bye", replyChannel)
        equal "Msg: 1 - Bye" resp
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor delivers falsy messages in order`` () =
    // See #1588
    async {
        let mutable collected = []
        let agent = MailboxProcessor<int>.Start(fun inbox ->
            let rec loop () = async {
                let! msg = inbox.Receive()
                if msg = -1 then ()
                else
                    collected <- msg :: collected
                    return! loop ()
            }
            loop ())
        for msg in [1; 0; 2; 0; 3] do
            agent.Post(msg)
        agent.Post(-1)
        do! Async.Sleep 200
        equal [1; 0; 2; 0; 3] (List.rev collected)
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor.postAndAsyncReply completes with unit reply`` () =
    async {
        let mutable ran = false
        let agent = MailboxProcessor<AsyncReplyChannel<unit>>.Start(fun inbox ->
            let rec loop () = async {
                let! chan = inbox.Receive()
                chan.Reply()
                return! loop ()
            }
            loop ())
        do! agent.PostAndAsyncReply(fun ch -> ch)
        ran <- true
        equal true ran
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor second Reply is ignored`` () =
    async {
        let log = ResizeArray<string>()
        let completed = new MailboxProcessor<unit>(fun _ -> async { return () })
        let agent = MailboxProcessor<AsyncReplyChannel<int>>.Start(fun inbox -> async {
            let! channel = inbox.Receive()
            channel.Reply 1
            channel.Reply 2
            log.Add "body done"
            completed.Post() })
        let! reply = agent.PostAndAsyncReply(id)
        equal 1 reply
        do! completed.Receive()
        equal [|"body done"|] (log.ToArray())
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test MailboxProcessor reply computation can be awaited twice`` () =
    async {
        let agent = MailboxProcessor<AsyncReplyChannel<int>>.Start(fun inbox -> async {
            let! channel = inbox.Receive()
            channel.Reply 42 })
        let work = agent.PostAndAsyncReply(id)
        let! first = work
        let! second = work
        equal 42 first
        equal 42 second
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild cancels the child when the parent's token is cancelled`` () =
    async {
        let mutable finallyRan = false
        let mutable completed = false
        let cts = new System.Threading.CancellationTokenSource()
        let child = async {
            try
                do! Async.Sleep 500
                completed <- true
            finally
                finallyRan <- true
        }
        let parent = async {
            let! childResult = Async.StartChild child
            do! childResult
        }
        Async.StartImmediate(parent, cts.Token)
        do! Async.Sleep 200
        cts.Cancel()
        do! Async.Sleep 600
        equal true finallyRan
        equal false completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Parallel children are cancelled when the parent's token is cancelled`` () =
    async {
        let mutable completed = 0
        let cts = new System.Threading.CancellationTokenSource()
        let mkChild () = async {
            do! Async.Sleep 500
            completed <- completed + 1
        }
        let work = async {
            let! _ = Async.Parallel [ mkChild(); mkChild(); mkChild() ]
            return ()
        }
        Async.StartImmediate(work, cts.Token)
        do! Async.Sleep 200
        cts.Cancel()
        do! Async.Sleep 600
        equal 0 completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Sequential children are cancelled when the parent's token is cancelled`` () =
    async {
        let mutable completed = 0
        let cts = new System.Threading.CancellationTokenSource()
        let mkChild () = async {
            do! Async.Sleep 500
            completed <- completed + 1
        }
        let work = async {
            let! _ = Async.Sequential [ mkChild(); mkChild(); mkChild() ]
            return ()
        }
        Async.StartImmediate(work, cts.Token)
        do! Async.Sleep 200
        cts.Cancel()
        do! Async.Sleep 600
        equal 0 completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with timeout cancels the child when the timeout expires`` () =
    async {
        let mutable completed = false
        let child = async {
            do! Async.Sleep 300
            completed <- true
        }
        let mutable timedOut = false
        try
            let! childResult = Async.StartChild(child, 100)
            do! childResult
        with
        | :? TimeoutException -> timedOut <- true
        do! Async.Sleep 400
        equal true timedOut
        equal false completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with timeout leaves the parent running when the timeout expires`` () =
    async {
        let child = async { do! Async.Sleep 300 }
        try
            let! childResult = Async.StartChild(child, 100)
            do! childResult
        with
        | :? TimeoutException -> ()
        let! token = Async.CancellationToken
        equal false token.IsCancellationRequested
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild timeout only runs while the result is awaited`` () =
    async {
        let child = async {
            do! Async.Sleep 150
            return 42
        }
        let! childResult = Async.StartChild(child, 100)
        do! Async.Sleep 250
        let! result = childResult
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with a timeout of -1 never times out`` () =
    async {
        let child = async {
            do! Async.Sleep 50
            return 42
        }
        let! childResult = Async.StartChild(child, -1)
        let! result = childResult
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with a timeout of 0 returns an available result`` () =
    async {
        let child = async {
            do! Async.Sleep 50
            return 42
        }
        let! childResult = Async.StartChild(child, 0)
        do! Async.Sleep 200
        let! result = childResult
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with a timeout of 0 raises when the result isn't available and leaves the child running`` () =
    async {
        let mutable completed = false
        let child = async {
            do! Async.Sleep 300
            completed <- true
        }
        let mutable timedOut = false
        try
            let! childResult = Async.StartChild(child, 0)
            do! childResult
        with
        | :? TimeoutException -> timedOut <- true
        do! Async.Sleep 400
        equal true timedOut
        equal true completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartChild with timeout raises the child's cancellation callback failure`` () =
    async {
        let child = async {
            let! token = Async.CancellationToken
            token.Register(fun () -> failwith "cleanup") |> ignore
            do! Async.Sleep 300
        }
        let mutable errors = -1
        try
            let! childResult = Async.StartChild(child, 100)
            do! childResult
        with error ->
            errors <- (error :?> AggregateException).InnerExceptions.Count
        equal 1 errors
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.OnCancel ignores a failing interruption`` () =
    async {
        let mutable interrupted = false
        let mutable cancelled = false
        let cts = new CancellationTokenSource()
        Async.StartWithContinuations(
            async {
                use! _ = Async.OnCancel(fun () ->
                    interrupted <- true
                    failwith "interruption")
                do! Async.Sleep 300
            },
            ignore,
            ignore,
            (fun _ -> cancelled <- true),
            cts.Token)
        do! Async.Sleep 50
        cts.Cancel()
        do! Async.Sleep 50
        equal true interrupted
        equal true cancelled
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Parallel respects maxDegreeOfParallelism`` () =
    async {
        let lockObj = obj ()
        let mutable running = 0
        let mutable peak = 0
        let work i = async {
            lock lockObj (fun () ->
                running <- running + 1
                peak <- max peak running)
            do! Async.Sleep 50
            lock lockObj (fun () -> running <- running - 1)
            return i
        }
        let! results = Async.Parallel([ for i in 1..10 -> work i ], maxDegreeOfParallelism = 3)
        equal [| 1..10 |] results
        equal 3 peak
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Parallel cancels the other computations when one fails`` () =
    async {
        let mutable completed = 0
        let work i = async {
            if i = 2 then
                do! Async.Sleep 20
                failwith "boom"
            do! Async.Sleep 300
            System.Threading.Interlocked.Increment(&completed) |> ignore<int>
        }
        let mutable error = ""
        try
            let! _ = Async.Parallel [ for i in 0..4 -> work i ]
            ()
        with ex -> error <- ex.Message
        do! Async.Sleep 400
        equal "boom" error
        equal 0 completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Parallel with an empty sequence returns an empty array`` () =
    async {
        let! results = Async.Parallel(([]: Async<int> list), maxDegreeOfParallelism = 2)
        equal 0 results.Length
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Choice returns the first Some and cancels the others`` () =
    async {
        let mutable completed = false
        let fast = async {
            do! Async.Sleep 20
            return Some 1
        }
        let slow = async {
            do! Async.Sleep 300
            completed <- true
            return Some 2
        }
        let none = async { return None }
        let! result = Async.Choice [ slow; none; fast ]
        do! Async.Sleep 400
        equal (Some 1) result
        equal false completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Choice returns None when every computation does`` () =
    async {
        let none = async {
            do! Async.Sleep 10
            return (None: int option)
        }
        let! result = Async.Choice [ none; none ]
        equal None result
        let! empty = Async.Choice ([]: Async<int option> list)
        equal None empty
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.Choice raises when a computation fails`` () =
    async {
        let fails = async {
            do! Async.Sleep 10
            return failwith "boom"
        }
        let slow = async {
            do! Async.Sleep 300
            return Some 1
        }
        let mutable error = ""
        try
            let! _ = Async.Choice [ slow; fails ]
            ()
        with ex -> error <- ex.Message
        equal "boom" error
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.OnCancel runs the interruption when cancelled`` () =
    async {
        let mutable interrupted = false
        let cts = new CancellationTokenSource()
        Async.StartImmediate(async {
            use! _ = Async.OnCancel(fun () -> interrupted <- true)
            do! Async.Sleep 300
        }, cts.Token)
        do! Async.Sleep 50
        cts.Cancel()
        do! Async.Sleep 50
        equal true interrupted
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.OnCancel doesn't run the interruption once disposed`` () =
    async {
        let mutable interrupted = false
        let cts = new CancellationTokenSource()
        Async.StartImmediate(async {
            let! registration = Async.OnCancel(fun () -> interrupted <- true)
            registration.Dispose()
            do! Async.Sleep 300
        }, cts.Token)
        do! Async.Sleep 50
        cts.Cancel()
        do! Async.Sleep 50
        equal false interrupted
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.OnCancel doesn't run the interruption when disposed before the cancellation and again by use!`` () =
    async {
        let mutable interrupted = false
        let cts = new CancellationTokenSource()
        Async.StartImmediate(async {
            use! registration = Async.OnCancel(fun () -> interrupted <- true)
            registration.Dispose()
            do! Async.Sleep 300
        }, cts.Token)
        do! Async.Sleep 50
        cts.Cancel()
        do! Async.Sleep 50
        equal false interrupted
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartAsTask works`` () =
    async {
        let t = Async.StartAsTask(async {
            do! Async.Sleep 10
            return 42
        })
        let! result = Async.AwaitTask t
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartAsTask passes the cancellation token`` () =
    async {
        let mutable completed = false
        let cts = new CancellationTokenSource()
        let t = Async.StartAsTask(async {
            do! Async.Sleep 200
            completed <- true
        }, cancellationToken = cts.Token)
        cts.Cancel()
        let mutable outcome = "pending"
        // AwaitTask reports a cancelled task as an exception on .NET and as a cancellation in JS
        Async.StartWithContinuations(
            Async.AwaitTask t,
            (fun () -> outcome <- "completed"),
            (fun _ -> outcome <- "cancelled"),
            (fun _ -> outcome <- "cancelled"))
        do! Async.Sleep 300
        equal "cancelled" outcome
        equal false completed
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Async.StartImmediateAsTask works`` () =
    async {
        let t = Async.StartImmediateAsTask(async { return 42 })
        let! result = Async.AwaitTask t
        equal 42 result
    }
    |> Async.RunSynchronously

let private loopLog = ResizeArray<string>()

let private loggedSource =
    seq {
        try
            for i in 1..5 do
                yield i
        finally
            loopLog.Add "finally"
    }

[<Fact>]
let ``test Loops in async work as on .NET, with or without awaits in their body`` () =
    let message (r: Choice<unit, exn>) =
        match r with
        | Choice2Of2 e -> e.Message
        | Choice1Of2() -> "ok"

    async {
        for i in 1..3 do
            if i = 2 then
                failwith "boom"
    }
    |> Async.Catch
    |> Async.RunSynchronously
    |> message
    |> equal "boom"

    // (an endless sequence, walked as the loop goes)
    async {
        for x in Seq.initInfinite id do
            if x = 5 then
                failwith "stop"
    }
    |> Async.Catch
    |> Async.RunSynchronously
    |> message
    |> equal "stop"

    // (a sequence's finally runs when the loop is left early, with or without do!)
    loopLog.Clear()

    async {
        for x in loggedSource do
            do! Async.Sleep 0

            if x = 3 then
                failwith "early"
    }
    |> Async.Catch
    |> Async.RunSynchronously
    |> message
    |> equal "early"

    List.ofSeq loopLog |> equal [ "finally" ]
    loopLog.Clear()

    async {
        for x in loggedSource do
            if x = 2 then
                failwith "sync early"
    }
    |> Async.Catch
    |> Async.RunSynchronously
    |> message
    |> equal "sync early"

    List.ofSeq loopLog |> equal [ "finally" ]

    let cts = new System.Threading.CancellationTokenSource()
    cts.Cancel()
    let mutable n = 0

    (try
        Async.RunSynchronously(
            async {
                for i in 1..10 do
                    n <- n + i
            },
            cancellationToken = cts.Token
        )

        "ran"
     with :? System.OperationCanceledException ->
         "cancelled")
    |> equal "cancelled"

    n |> equal 0
    let mutable k = 0

    async {
        while k < 10 do
            k <- k + 1
    }
    |> Async.RunSynchronously

    k |> equal 10
