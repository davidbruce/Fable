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

[<Fact>]
let ``test An array's null is tested with isNull and =`` () =
    let a: int[] = null
    isNull a |> equal true
    isNull Unchecked.defaultof<string[]> |> equal true
    let e: int[] = [||]
    isNull e |> equal false
    (e = null) |> equal false
    isNull (box a) |> equal true

[<Fact>]
let ``test Array.Resize grows, shrinks and starts from null`` () =
    let mutable r: int[] = null
    System.Array.Resize(&r, 3)
    r |> equal [| 0; 0; 0 |]
    r.[1] <- 5
    System.Array.Resize(&r, 2)
    r |> equal [| 0; 5 |]
    let mutable s = [| "a" |]
    System.Array.Resize(&s, 2)
    s.[0] |> equal "a"
    isNull s.[1] |> equal true

[<Fact>]
let ``test Array.zeroCreate of arrays holds null arrays`` () =
    let jagged: int[][] = Array.zeroCreate 2
    isNull jagged.[0] |> equal true
    jagged.[1] <- [| 1; 2 |]
    jagged.[1].[1] |> equal 2

[<Fact>]
let ``test An index of a null array raises NullReferenceException`` () =
    let a: int[] = null

    let raised =
        try
            a.[0] |> ignore
            false
        with :? System.NullReferenceException ->
            true

    raised |> equal true

type private INullableIface =
    abstract Ping: unit -> int

[<Fact>]
let ``test Null interface value works and raises NullReferenceException on call`` () =
    let iface: INullableIface = Unchecked.defaultof<INullableIface>
    obj.ReferenceEquals(iface, null) |> equal true

    let raised =
        try
            iface.Ping() |> ignore
            false
        with :? System.NullReferenceException ->
            true

    raised |> equal true

type WithCollectionFields() =
    [<DefaultValue>]
    val mutable Dict: System.Collections.Generic.Dictionary<string, int>

    [<DefaultValue>]
    val mutable Items: ResizeArray<int>

[<Fact>]
let ``test .NET collections can be null`` () =
    let nre f =
        try
            f ()
            false
        with :? System.NullReferenceException ->
            true

    let x = WithCollectionFields()
    isNull x.Dict |> equal true
    isNull x.Items |> equal true
    nre (fun () -> x.Items.Add 1) |> equal true
    nre (fun () -> x.Dict.Count |> ignore) |> equal true
    nre (fun () -> for _ in x.Items do ()) |> equal true
    x.Items <- ResizeArray [ 1 ]
    x.Items.Add 2
    x.Items.Count |> equal 2
    let items = Array.zeroCreate<ResizeArray<int>> 1
    isNull items.[0] |> equal true
    nre (fun () -> items.[0].Add 1) |> equal true
    let sb: System.Text.StringBuilder = Unchecked.defaultof<_>
    nre (fun () -> sb.Append "x" |> ignore) |> equal true
