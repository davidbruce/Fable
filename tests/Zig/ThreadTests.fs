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
