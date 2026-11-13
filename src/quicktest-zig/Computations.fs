module Computations

// Computation expressions: builders of the program's own, and `async`. There is one thread:
// an async computation runs when it is started, its effects in .NET's order.
// `run` returns the number of failed checks.

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

let same (expected: string) (actual: string) : int =
    if actual = expected then
        0
    else
        1

type MaybeBuilder() =
    member _.Bind(m: 'a option, f: 'a -> 'b option) : 'b option = Option.bind f m
    member _.Return(x: 'a) : 'a option = Some x
    member _.ReturnFrom(m: 'a option) = m
    member _.Zero() : unit option = Some()

let maybe = MaybeBuilder()

let add (a: int option) (b: int option) : int option =
    maybe {
        let! x = a
        let! y = b
        return x + y
    }

type LogBuilder() =
    member _.Bind((value: 'a, log: string list), f: 'a -> 'b * string list) : 'b * string list =
        let result, more = f value
        result, log @ more

    member _.Return(x: 'a) : 'a * string list = x, []

let logged = LogBuilder()

let step (name: string) (x: int) : int * string list = x, [ name ]

let compute () : int * string list =
    logged {
        let! a = step "first" 1
        let! b = step "second" (a + 1)
        return a + b
    }

let double (n: int) : Async<int> = async { return n * 2 }

let work (n: int) (log: ResizeArray<string>) : Async<int> =
    async {
        log.Add "start"
        let! a = double n
        do! Async.Sleep 1
        let mutable total = a

        for i in [ 1; 2; 3 ] do
            let! d = double i
            total <- total + d

        let mutable count = 0

        while count < 2 do
            count <- count + 1

        try
            if total > 1000 then
                failwith "too big"

            log.Add "checked"
        finally
            log.Add "finally"

        let! safe =
            async {
                try
                    return failwith "inner"
                with e ->
                    return e.Message.Length
            }

        return total + count + safe
    }

let run () : int =
    let before = liveCells ()
    let log = ResizeArray<string>()
    let result = Async.RunSynchronously(work 5 log)

    let all =
        [ double 1; double 2; double 3 ] |> Async.Parallel |> Async.RunSynchronously

    let caught =
        async { return failwith "boom": int } |> Async.Catch |> Async.RunSynchronously

    let raised =
        try
            async { return failwith "out": int } |> Async.RunSynchronously |> string
        with e ->
            e.Message

    let mutable started = 0
    async { started <- started + 1 } |> Async.StartImmediate

    let failed =
        same
            "Some 3|None|(3, [\"first\"; \"second\"])"
            (sprintf "%A|%A|%A" (add (Some 1) (Some 2)) (add None (Some 2)) (compute ()))
        + check (result = 10 + 12 + 2 + 5)
        + same "seq [\"start\"; \"checked\"; \"finally\"]" (sprintf "%A" log)
        + same "[|2; 4; 6|]" (sprintf "%A" all)
        + same
            "boom|out|1"
            ((match caught with
              | Choice2Of2 e -> e.Message
              | Choice1Of2 _ -> "no")
             + "|"
             + raised
             + "|"
             + string started)

    printfn "computations: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
