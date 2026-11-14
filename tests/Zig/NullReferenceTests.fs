module Fable.Tests.Zig.NullReferenceTests

open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<AllowNullLiteral>]
type Node(v: int) =
    member _.Value = v
    member val Next: Node = null with get, set

type Plain(v: int) =
    member _.Value = v

[<Fact>]
let ``test A class's null is tested with isNull and =`` () =
    let a = Node(1)
    a.Next <- Node(2)
    isNull a.Next |> equal false
    isNull a.Next.Next |> equal true
    let n: Node = null
    (n = null) |> equal true

[<Fact>]
let ``test Unchecked.defaultof of a class is null`` () =
    let d = Unchecked.defaultof<Plain>
    isNull (box d) |> equal true

[<Fact>]
let ``test A member of null raises NullReferenceException`` () =
    let n: Node = null

    let message =
        try
            string n.Value
        with :? System.NullReferenceException as e ->
            e.Message

    message |> equal "Object reference not set to an instance of an object."

[<Fact>]
let ``test A chain of objects ends at null`` () =
    let a = Node(1)
    a.Next <- Node(2)
    a.Next.Next <- Node(3)
    let mutable sum = 0
    let mutable cur = a

    while not (isNull cur) do
        sum <- sum + cur.Value
        cur <- cur.Next

    sum |> equal 6

[<Fact>]
let ``test A downcast of null is null`` () =
    let o: obj = null
    let n = o :?> Node
    isNull n |> equal true
