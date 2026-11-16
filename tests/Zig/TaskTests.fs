module Fable.Tests.Zig.TaskTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing
open System.Threading.Tasks

// Bridge pattern: works on .NET (Async.AwaitTask wraps Task)
let awaitTask (t: Task<'T>) = Async.AwaitTask t

type DisposableAction(f) =
    interface IDisposable with
        member _.Dispose() = f ()

[<Fact>]
let ``test Simple task translates without exception`` () =
    let tsk = task { return () }
    tsk.GetAwaiter().GetResult()

[<Fact>]
let ``test Simple task result translates without exception`` () =
    let tsk = task { return () }
    tsk.Result

[<Fact>]
let ``test Simple Task.FromResult translates without exception`` () =
    let tsk = Task.FromResult 42
    let result = tsk.Result
    equal result 42

[<Fact>]
let ``test task while binding works correctly`` () =
    let mutable result = 0

    let tsk =
        task {
            while result < 10 do
                result <- result + 1
        }

    tsk.GetAwaiter().GetResult()
    equal result 10

[<Fact>]
let ``test task while loop handles large number of iterations without stack overflow`` () =
    let mutable result = 0

    let tsk =
        task {
            while result < 10000 do
                result <- result + 1
        }

    tsk.GetAwaiter().GetResult()
    equal result 10000

[<Fact>]
let ``test Task for binding works correctly`` () =
    let inputs = [| 1; 2; 3 |]
    let mutable result = 0

    let tsk =
        task {
            for inp in inputs do
                result <- result + inp
        }

    tsk.GetAwaiter().GetResult()
    equal result 6

[<Fact>]
let ``test Task exceptions are handled correctly`` () =
    let mutable result = 0

    let f shouldThrow =
        let tsk =
            task {
                try
                    if shouldThrow then
                        failwith "boom!"
                    else
                        result <- 12
                with
                | _ -> result <- 10
            }

        tsk.GetAwaiter().GetResult()
        result

    f true + f false |> equal 22

[<Fact>]
let ``test Simple task is executed correctly`` () =
    let mutable result = false
    let x = task { return 99 }

    task {
        let! x = x
        let y = 99
        result <- x = y
    }
    |> fun tsk -> tsk.GetAwaiter().GetResult()

    equal result true


[<Fact>]
let ``test task use statements should dispose of resources when they go out of scope`` () =
    let mutable isDisposed = false
    let mutable step1ok = false
    let mutable step2ok = false

    let resource =
        task { return new DisposableAction(fun () -> isDisposed <- true) }

    task {
        use! r = resource
        step1ok <- not isDisposed
    }
    |> fun tsk -> tsk.GetAwaiter().GetResult()

    step2ok <- isDisposed
    (step1ok && step2ok) |> equal true


[<Fact>]
let ``test Try ... with ... expressions inside async expressions work the same`` () =
    let mutable result = ""
    let throw () : unit = raise (exn "Boo!")
    let append (x) = result <- result + x

    let innerAsync () =
        task {
            append "b"

            try
                append "c"
                throw ()
                append "1"
            with
            | _ -> append "d"

            append "e"
        }

    task {
        append "a"

        try
            do! innerAsync ()
        with
        | _ -> append "2"

        append "f"
    }
    |> fun tsk -> tsk.GetAwaiter().GetResult()

    equal result "abcdef"


[<Fact>]
let ``test TaskCompletionSource is executed correctly`` () =
    let x =
        task {
            let tcs = TaskCompletionSource<int>()
            tcs.SetResult 42
            return! tcs.Task
        }

    let result =
        x |> fun tsk -> tsk.GetAwaiter().GetResult()

    equal 42 result

// Regression: async functions returning Task from if/else branches must await both branches
let skipPipeline () : Task<int option> = Task.FromResult None

let httpVerb (validate: string -> bool) =
    fun (value: string) ->
        if validate value then
            Task.FromResult(Some 42)
        else
            skipPipeline ()

[<Fact>]
let ``test async pass-through returns are awaited in if branches`` () =
    let result =
        httpVerb (fun s -> s = "GET") "GET"
        |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal (Some 42) result

    let result2 =
        httpVerb (fun s -> s = "GET") "POST"
        |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal None result2

// Regression: await in nested try/with inside async
[<Fact>]
let ``test async returns in try-with are awaited`` () =
    let getResult (fail: bool) : Task<int> =
        if fail then
            failwith "error"
        else
            Task.FromResult 99

    let wrapper (fail: bool) =
        task {
            try
                return! getResult fail
            with
            | _ -> return -1
        }

    let result = wrapper false |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal 99 result

    let result2 = wrapper true |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal -1 result2

// Regression: closure with let binding before if/else returning Task emits ternary;
// both branches of the ternary must be awaited.
let asyncNone () : Task<int option> = Task.FromResult None

let makeClosure (flag: bool) =
    let captured = flag
    fun (value: int) ->
        let x = value + 1
        if captured then Task.FromResult(Some x) else asyncNone ()

[<Fact>]
let ``test async ternary in closure awaits both branches`` () =
    let fn = makeClosure true
    let result = fn 41 |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal (Some 42) result

    let fn2 = makeClosure false
    let result2 = fn2 41 |> fun tsk -> tsk.GetAwaiter().GetResult()
    equal None result2

// ---- ported from tests/Js/Main (2026-11-16, last) ----

[<Fact>]
let ``test Simple task result works`` () =
    async {
        let! result = awaitTask (task { return 42 })
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Task.FromResult works`` () =
    async {
        let! result = awaitTask (Task.FromResult 42)
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task let bang works`` () =
    async {
        let! result = awaitTask (task {
            let! x = task { return 10 }
            let! y = task { return 20 }
            return x + y
        })
        equal 30 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task do bang works`` () =
    async {
        let mutable x = 0
        let! result = awaitTask (task {
            do! task { x <- 42 }
            return x
        })
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task return from works`` () =
    async {
        let inner = task { return "hello" }
        let! result = awaitTask (task { return! inner })
        equal "hello" result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task try-with works`` () =
    async {
        let mutable result = 0
        let! _ = awaitTask (task {
            try failwith "boom"
            with _e -> result <- 42
        })
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task sequential composition works`` () =
    async {
        let mutable count = 0
        let! result = awaitTask (task {
            let! a = task { count <- count + 1; return count }
            let! b = task { count <- count + 1; return count }
            return a + b
        })
        equal 3 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Task exceptions propagate through bind`` () =
    async {
        let mutable result = ""
        let! _ = awaitTask (task {
            try
                let! _ = task { failwith "inner"; return 0 }
                result <- "no exception"
            with ex ->
                result <- ex.Message
        })
        equal "inner" result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test TaskCompletionSource works`` () =
    async {
        let tcs = TaskCompletionSource<int>()
        tcs.SetResult(42)
        let! result = awaitTask tcs.Task
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Task.Delay works`` () =
    async {
        let mutable steps = []
        let! _ = awaitTask (task {
            steps <- "before" :: steps
            do! Task.Delay 20
            do! Task.Delay(TimeSpan.FromMilliseconds 10.)
            steps <- "after" :: steps
        })
        equal [ "after"; "before" ] steps
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test Task.Delay can be cancelled`` () =
    async {
        let cts = new System.Threading.CancellationTokenSource()
        let delay = Task.Delay(1000, cts.Token)
        cts.Cancel()
        let! cancelled = awaitTask (task {
            try
                do! delay
                return false
            with _ -> return true
        })
        equal true cancelled
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task can bind an Async`` () =
    async {
        let work = async {
            do! Async.Sleep 10
            return 41
        }
        let! result = awaitTask (task {
            let! x = work
            return x + 1
        })
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task can return! an Async`` () =
    async {
        let work = async {
            do! Async.Sleep 10
            return 42
        }
        let! result = awaitTask (task { return! work })
        equal 42 result
    }
    |> Async.RunSynchronously

[<Fact>]
let ``test task can do! an Async`` () =
    async {
        let mutable ran = false
        let work = async {
            do! Async.Sleep 10
            ran <- true
        }
        let! _ = awaitTask (task { do! work })
        equal true ran
    }
    |> Async.RunSynchronously

