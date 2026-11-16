module Fable.Tests.Zig.LoopsTests

open Fable.Tests.Util
open Fable.Tests.Util.Testing


[<Fact>]
let ``test For-loop upto works`` () =
    let mutable result = 0

    for i = 0 to 10 do
        result <- result + i
    done

    result
    |> equal 55

[<Fact>]
let ``test For-loop upto minus one works`` () =
    let mutable result = 0

    for i = 0 to 10 - 1 do
        result <- result + i
    done

    result
    |> equal 45

[<Fact>]
let ``test For-loop downto works`` () =
    let mutable result = 0
    for i = 10 downto 0 do
        result <- result + i

    result
    |> equal 55

[<Fact>]
let ``test for-in descending range with -1 step works`` () =
    let mutable result = ""
    for i in 5 .. -1 .. 1 do
        result <- result + string i
    result |> equal "54321"

[<Fact>]
let ``test for-in ascending range with 1 step works`` () =
    let mutable result = 0
    for i in 1 .. 1 .. 5 do
        result <- result + i
    result |> equal 15

[<Fact>]
let ``test for-in const-step range with zero iterations works`` () =
    let mutable count = 0
    for _i in 0 .. -1 .. 5 do
        count <- count + 1
    count |> equal 0

[<Fact>]
let ``test for-in step range other than one still works`` () =
    let mutable result = ""
    for i in 9 .. -2 .. 0 do
        result <- result + string i
    result |> equal "97531"

[<Fact>]
let ``test nested array length-alias for-loops read and write in bounds`` () =
    let arr = [| 10; 20; 30; 40; 50 |]
    let n = arr.Length
    let mutable acc = 0

    for i in 0 .. n - 1 do
        for j in i + 1 .. n - 1 do
            acc <- acc + arr[i] + arr[j]
            arr[j] <- arr[j] + 1

    acc |> equal 620
    arr |> equal [| 10; 21; 32; 43; 54 |]

    let fixedArr = [| "x" + string 1; "y" + string 2; "z" + string 3 |]
    let mutable joined = ""

    for k in 0 .. 2 do
        joined <- joined + fixedArr[k]

    joined |> equal "x1y2z3"

[<Fact>]
let ``test while loop monotonic index bounds elimination and mutation-before-index safety`` () =
    let s = "hello" + string 42
    let mutable i = 0
    let mutable count = 0

    while i < s.Length do
        if s[i] >= '0' && s[i] <= '9' then
            count <- count + 1
        i <- i + 1

    count |> equal 2

    // Mutation BEFORE indexing must still raise IndexOutOfRangeException on the last iteration.
    let mutable badIdx = 0
    raisedExceptionType (fun () ->
        while badIdx < s.Length do
            badIdx <- badIdx + 1
            let _c = s[badIdx]
            ()
    )
    |> equal "IndexOutOfRangeException"

[<Fact>]
let ``test shadowed bindings keep lexical flow facts isolated`` () =
    let x = "outer-" + string 1
    let n = x.Length

    let innerNull =
        let (x: string) = null
        isNull x

    innerNull |> equal true
    n |> equal 7
    x.Length |> equal 7

    let arr = [| "p" + string 1; "q" + string 2 |]
    let mutable collected = ""

    for item in (arr :> seq<string>) do
        collected <- collected + item + ";"

    collected |> equal "p1;q2;"
