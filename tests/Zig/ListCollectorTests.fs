module Fable.Tests.Zig.ListCollectorTests

open Fable.Tests.Util
open Fable.Tests.Util.Testing
open Microsoft.FSharp.Core.CompilerServices

let cutOffLast list =
    let mutable headList = ListCollector<'a>()

    let rec visit list =
        match list with
        | []
        | [ _ ] -> ()
        | head :: tail ->
            headList.Add(head)
            visit tail

    visit list
    headList.Close()

[<Fact>]
let ``test ListCollector.Add and .Close`` () =
    let result = cutOffLast [ 1; 2; 3 ]
    result |> equal [ 1; 2 ]


[<Fact>]
let ``test ListCollector.Close works for empty list`` () =
    let mutable l = ListCollector<_>()
    let result = l.Close()

    result |> equal []


[<Fact>]
let ``test ListCollector.AddMany works`` () =
    let mutable l = ListCollector<_>()
    l.AddMany([ 1; 2; 3 ])

    let result = l.Close()

    result |> equal [ 1; 2; 3 ]


[<Fact>]
let ``test ListCollector.AddMany works for empty list`` () =
    let mutable l = ListCollector<_>()
    l.AddMany([])

    let result = l.Close()

    result |> equal []


[<Fact>]
let ``test ListCollector.AddManyAndClose works`` () =
    let mutable l = ListCollector<_>()
    let result = l.AddManyAndClose([ 1; 2; 3 ])

    result |> equal [ 1; 2; 3 ]
