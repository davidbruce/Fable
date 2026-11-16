module Fable.Tests.Zig.ComparisonTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing
open Fable.Tests.Util
open Fable.Core.PyInterop
open System.Collections.Generic
open FSharp.Data.UnitSystems.SI.UnitSymbols


type UTest = A of int | B of int
type RTest = { a: int; b: int }
type STest = struct val A: int; new(a: int) = { A = a }; end
type OTest(a) = member val A = a with get, set

[<CustomEquality; CustomComparison>]
type UTest2 =
    | String of string
    override x.GetHashCode() = x.GetHashCode()
    override x.Equals(other) =
       match other with
         | :? UTest2 as y ->
            match x, y with
            | String s1, String s2 -> (s1 + s1) = s2
         | _ -> false
    interface System.IEquatable<UTest2> with
        member x.Equals(y) =
            match x, y with
            | String s1, String s2 -> (s1 + s1) = s2
    interface System.IComparable with
        member x.CompareTo(other) =
            match other with
            | :? UTest2 as y ->
                match x, y with
                | String s1, String s2 -> compare (s1 + s1) s2
            | _ -> invalidArg "other" "cannot compare values of different types"


exception Ex of int

[<ReferenceEquality>]
type RefEqRecord = { a2: int; b2: int }

[<ReferenceEquality>]
type RefEqUnion = RefC of int | RefD of int

[<NoEquality; NoComparison>]
type NoEqRecord = { a3: int }

[<NoEquality; NoComparison>]
type NoEqUnion = NoEqCase of int

#nowarn "386"
[<NoEquality; NoComparison>]
type NoEqRecordWithOverride =
    { a4: int }
    override _.Equals(other) = true
    override _.GetHashCode() = 4

[<Struct; NoEquality; NoComparison>]
type NoEqStruct = { s2: int }

let genericEquals (a: 'T) (b: 'T) : bool =
    EqualityComparer<'T>.Default.Equals(a, b)

let genericHash (x: 'T) : int =
    EqualityComparer<'T>.Default.GetHashCode(x)

type MyTest(i: int) =
    member x.Value = i
    override x.GetHashCode() = i
    override x.Equals(yobj) =
       match yobj with
         | :? MyTest as y -> y.Value + 1 = x.Value
         | _ -> false
    interface System.IComparable with
        member x.CompareTo(yobj) =
            match yobj with
            | :? MyTest as y -> compare (y.Value + 1) x.Value
            | _ -> invalidArg "yobj" "cannot compare values of different types"
            // | _ -> -1

    interface System.IEquatable<MyTest> with
        member x.Equals(y) =
            y.Value + 1 = x.Value

type Status =
| CreateScenePicture
| ReadingOldDevice
| CreateOldMeterReadingPicture
| SelectingNewDevice
| ReadingNewDevice
| CreateNewMeterReadingPicture
| GetSignature
| Done

type MyClass(v) =
    member val Value: int = v with get, set

// See https://github.com/fable-compiler/Fable/issues/4834
type CustomValue(value: int, label: string) =
    member _.Value = value
    member _.Label = label

    override _.Equals(other) =
        match other with
        | :? CustomValue as other -> value = other.Value
        | _ -> false

    override _.GetHashCode() = value

type WrappedUnion = WrappedUnion of CustomValue

type WrappedRecord = { Value: CustomValue }

[<Fact>]
let ``test PhysicalEquality works`` () = // See #3998
    let r1 = ResizeArray([1; 2])
    let r2 = ResizeArray([1; 2])
    let r3 = r1

    LanguagePrimitives.PhysicalEquality r1 r2 |> equal false
    LanguagePrimitives.PhysicalEquality r2 r2 |> equal true
    LanguagePrimitives.PhysicalEquality r3 r1 |> equal true

[<Fact>]
let ``test ReferenceEquality record equality works`` () =
    let x = { a2 = 1; b2 = 2 }
    let y = { a2 = 1; b2 = 2 }
    equal true (x = x)
    equal false (x = y)
    equal true (x <> y)
    equal false (x.Equals y)
    equal true (genericEquals x x)
    equal false (genericEquals x y)
    equal false ([ x ] = [ y ])
    equal false ((x, 1) = (y, 1))
    equal false (Some x = Some y)
    equal true ([ x ] |> List.contains x)
    equal false ([ x ] |> List.contains y)

[<Fact>]
let ``test ReferenceEquality record hash works`` () =
    let x = { a2 = 1; b2 = 2 }
    let y = { a2 = 1; b2 = 2 }
    equal (hash x) (hash x)
    equal (genericHash x) (genericHash x)
    let d = Dictionary<RefEqRecord, int>()
    d[x] <- 1
    equal true (d.ContainsKey x)
    equal false (d.ContainsKey y)
    equal 2 (HashSet<RefEqRecord>([ x; y ]).Count)

[<Fact>]
let ``test ReferenceEquality union equality works`` () =
    let x = RefC 1
    let y = RefC 1
    equal true (x = x)
    equal false (x = y)
    equal false (x.Equals y)
    equal true (genericEquals x x)
    equal false (genericEquals x y)
    equal false ([ x ] |> List.contains y)
    equal 2 (HashSet<RefEqUnion>([ x; y ]).Count)

[<Fact>]
let ``test NoEquality record and union compare by reference`` () =
    let x = { a3 = 1 }
    equal true ((box x).Equals(box x))
    equal false ((box x).Equals(box { a3 = 1 }))
    equal true (genericEquals x x)
    equal false (genericEquals x { a3 = 1 })
    let u = NoEqCase 1
    equal true ((box u).Equals(box u))
    equal false ((box u).Equals(box (NoEqCase 1)))
    equal true (genericEquals u u)
    equal false (genericEquals u (NoEqCase 1))

[<Fact>]
let ``test NoEquality record keeps an explicit Equals override`` () =
    equal true ((box { a4 = 1 }).Equals(box { a4 = 2 }))
    equal 4 ((box { a4 = 1 }).GetHashCode())

[<Fact>]
let ``test NoEquality struct record compares structurally when boxed`` () =
    equal true ((box { s2 = 1 }).Equals(box { s2 = 1 }))
    equal false ((box { s2 = 1 }).Equals(box { s2 = 2 }))

[<Fact>]
let ``test Typed array equality works`` () =
    let xs1 = [| 1; 2; 3 |]
    let xs2 = [| 1; 2; 3 |]
    let xs3 = [| 1; 2; 4 |]
    let xs4 = [| 1; 2 |]
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 <> xs4)

[<Fact>]
let ``test Typed array option equality works`` () =
    let xs1 = Some [| 1; 2; 3 |]
    let xs2 = Some [| 1; 2; 3 |]
    let xs3 = Some [| 1; 2; 4 |]
    let xs4 = Some [| 1; 2 |]
    let xs5 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal false (xs1 = xs4)
    equal true (xs1 <> xs4)
    equal false (xs1 = xs5)
    equal true (xs1 <> xs5)
    equal true (xs5 = None)
    equal false (xs5 <> None)

[<Fact>]
let ``test Array equality works`` () =
    let xs1 = [| "1"; "2"; "3" |]
    let xs2 = [| "1"; "2"; "3" |]
    let xs3 = [| "1"; "2"; "4" |]
    let xs4 = [| "1"; "2" |]
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 <> xs4)

[<Fact>]
let ``test Array option equality works`` () =
    let xs1 = Some [| "1"; "2"; "3" |]
    let xs2 = Some [| "1"; "2"; "3" |]
    let xs3 = Some [| "1"; "2"; "4" |]
    let xs4 = Some [| "1"; "2" |]
    let xs5 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal false (xs1 = xs4)
    equal true (xs1 <> xs4)
    equal false (xs1 = xs5)
    equal true (xs1 <> xs5)
    equal true (xs5 = None)
    equal false (xs5 <> None)

[<Fact>]
let ``test Tuple equality works`` () =
    let xs1 = ( 1, 2, 3 )
    let xs2 = ( 1, 2, 3 )
    let xs3 = ( 1, 2, 4 )
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)

[<Fact>]
let ``test Tuple option equality works``() =
    let xs1 = Some ( 1, 2, 3 )
    let xs2 = Some ( 1, 2, 3 )
    let xs3 = Some ( 1, 2, 4 )
    let xs5 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal false (xs1 = xs5)
    equal true (xs1 <> xs5)
    equal true (xs5 = None)
    equal false (xs5 <> None)

[<Fact>]
let ``test List equality works`` () =
    let xs1 = [ 1; 2; 3 ]
    let xs2 = [ 1; 2; 3 ]
    let xs3 = [ 1; 2; 4 ]
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)

[<Fact>]
let ``test List option equality works``() =
    let xs1 = Some [ 1; 2; 3 ]
    let xs2 = Some [ 1; 2; 3 ]
    let xs3 = Some [ 1; 2; 4 ]
    let xs4 = Some [ 1; 2; 3; 1 ]
    let xs5 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal false (xs1 = xs4)
    equal true (xs1 <> xs4)
    equal false (xs1 = xs5)
    equal true (xs1 <> xs5)
    equal true (xs5 = None)
    equal false (xs5 <> None)

[<Fact>]
let ``test Set equality works`` () =
    let xs1 = Set [ 1; 2; 3 ]
    let xs2 = Set [ 1; 2; 3 ]
    let xs3 = Set [ 1; 2; 4 ]
    let xs4 = Set [ 3; 2; 1 ]
    let xs5 = Set [ 1; 2; 3; 1 ]
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 = xs4)
    equal false (xs1 <> xs5)

[<Fact>]
let ``test Set option equality works`` () =
    let xs1 = Some (Set [ 1; 2; 3 ])
    let xs2 = Some (Set [ 1; 2; 3 ])
    let xs3 = Some (Set [ 1; 2; 4 ])
    let xs4 = Some (Set [ 3; 2; 1 ])
    let xs5 = Some (Set [ 1; 2; 3; 1 ])
    let xs6 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 = xs4)
    equal false (xs1 <> xs5)
    equal false (xs1 = xs6)
    equal true (xs1 <> xs6)
    equal true (xs6 = None)
    equal false (xs6 <> None)

[<Fact>]
let ``test Map equality works`` () =
    let xs1 = Map [ ("a", 1); ("b", 2); ("c", 3) ]
    let xs2 = Map [ ("a", 1); ("b", 2); ("c", 3) ]
    let xs3 = Map [ ("a", 1); ("b", 2); ("c", 4) ]
    let xs4 = Map [ ("c", 3); ("b", 2); ("a", 1) ]
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 = xs4)

[<Fact>]
let ``test Map option equality works`` () =
    let xs1 = Some (Map [ ("a", 1); ("b", 2); ("c", 3) ])
    let xs2 = Some (Map [ ("a", 1); ("b", 2); ("c", 3) ])
    let xs3 = Some (Map [ ("a", 1); ("b", 2); ("c", 4) ])
    let xs4 = Some (Map [ ("c", 3); ("b", 2); ("a", 1) ])
    let xs5 = Some (Map [ ("a", 1); ("b", 2); ("c", 3); ("d", 1) ])
    let xs6 = None
    equal true (xs1 = xs2)
    equal false (xs1 = xs3)
    equal true (xs1 <> xs3)
    equal false (xs1 <> xs2)
    equal true (xs1 = xs4)
    equal true (xs1 <> xs5)
    equal false (xs1 = xs6)
    equal true (xs1 <> xs6)
    equal true (xs6 = None)
    equal false (xs6 <> None)

#if !FABLE_COMPILER_ZIG // (immutable records and unions are values in the Zig target: ReferenceEquals of them is refused)
[<Fact>]
let ``test Union equality works`` () =
    let u1 = A 2
    let u2 = A 2
    let u3 = A 4
    let u4 = B 2
    equal true (u1 = u2)
    equal false (u1 = u3)
    equal true (u1 <> u3)
    equal false (u1 <> u2)
    equal false (u1 = u4)
    Object.ReferenceEquals(u1, u1) |> equal true
    Object.ReferenceEquals(u1, u2) |> equal false
#endif

[<Fact>]
let ``test Union custom equality works`` () =
    let u1 = String "A"
    let u2 = String "A"
    let u3 = String "AA"
    equal false (u1 = u2)
    equal true (u1 = u3)

#if !FABLE_COMPILER_ZIG // (immutable records and unions are values in the Zig target: ReferenceEquals of them is refused)
[<Fact>]
let ``test Record equality works`` () =
    let r1 = { a = 1; b = 2 }
    let r2 = { a = 1; b = 2 }
    let r3 = { a = 1; b = 4 }
    equal true (r1 = r2)
    equal false (r1 = r3)
    equal true (r1 <> r3)
    equal false (r1 <> r2)
    Object.ReferenceEquals(r1, r1) |> equal true
    Object.ReferenceEquals(r1, r2) |> equal false
#endif

[<Fact>]
let ``test Exception equality works`` () =
    equal true ((Ex 1) = (Ex 1))
    equal false ((Ex 1) = (Ex 2))

[<Fact>]
let ``test Equality with objects implementing IEquatable works`` () =
    let c1 = MyTest(5)
    let c2 = MyTest(4)
    let c3 = MyTest(5)
    equal true (c1 = c2)
    equal false (c1 = c3)
    equal true (c1 <> c3)
    equal false (c1 <> c2)
    Object.ReferenceEquals(c1, c1) |> equal true
    Object.ReferenceEquals(c1, c2) |> equal false

[<Fact>]
let ``test Typed array comparison works`` () =
    let xs1 = [| 1; 2; 3 |]
    let xs2 = [| 1; 2; 3 |]
    let xs3 = [| 1; 2; 4 |]
    let xs4 = [| 1; 2; 2 |]
    let xs5 = [| 1; 2 |]
    let xs6 = [| 1; 2; 3; 1 |]
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)
    equal 1 (compare xs1 xs5)
    equal true (xs1 > xs5)
    equal -1 (compare xs1 xs6)
    equal false (xs1 > xs6)

[<Fact>]
let ``test Array comparison works`` () =
    let xs1 = [| "1"; "2"; "3" |]
    let xs2 = [| "1"; "2"; "3" |]
    let xs3 = [| "1"; "2"; "4" |]
    let xs4 = [| "1"; "2"; "2" |]
    let xs5 = [| "1"; "2" |]
    let xs6 = [| "1"; "2"; "3"; "1" |]
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)
    equal 1 (compare xs1 xs5)
    equal true (xs1 > xs5)
    equal -1 (compare xs1 xs6)
    equal false (xs1 > xs6)

[<Fact>]
let ``test Tuple comparison works`` () =
    let xs1 = ( 1, 2, 3 )
    let xs2 = ( 1, 2, 3 )
    let xs3 = ( 1, 2, 4 )
    let xs4 = ( 1, 2, 2 )
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)

[<Fact>]
let ``test List comparison works`` () =
    let xs1 = [ 1; 2; 3 ]
    let xs2 = [ 1; 2; 3 ]
    let xs3 = [ 1; 2; 4 ]
    let xs4 = [ 1; 2; 2 ]
    let xs5 = [ 1; 2 ]
    let xs6 = [ 1; 2; 3; 1 ]
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)
    equal 1 (compare xs1 xs5)
    equal true (xs1 > xs5)
    equal -1 (compare xs1 xs6)
    equal false (xs1 > xs6)

[<Fact>]
let ``test Set comparison works`` () =
    let xs1 = Set [ 1; 2; 3 ]
    let xs2 = Set [ 1; 2; 3 ]
    let xs3 = Set [ 1; 2; 4 ]
    let xs4 = Set [ 1; 2; 2 ]
    let xs5 = Set [ 1; 2 ]
    let xs6 = Set [ 1; 2; 3; 1 ]
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)
    equal 1 (compare xs1 xs5)
    equal true (xs1 > xs5)
    equal 0 (compare xs1 xs6)

[<Fact>]
let ``test Map comparison works`` () =
    let xs1 = Map [ ("a", 1); ("b", 2); ("c", 3) ]
    let xs2 = Map [ ("a", 1); ("b", 2); ("c", 3) ]
    let xs3 = Map [ ("a", 1); ("b", 2); ("c", 4) ]
    let xs4 = Map [ ("a", 1); ("b", 2); ("c", 2) ]
    let xs5 = Map [ ("a", 1); ("b", 2) ]
    let xs6 = Map [ ("a", 1); ("b", 2); ("c", 3); ("d", 1) ]
    equal 0 (compare xs1 xs2)
    equal -1 (compare xs1 xs3)
    equal true (xs1 < xs3)
    equal 1 (compare xs1 xs4)
    equal false (xs1 < xs4)
    equal 1 (compare xs1 xs5)
    equal true (xs1 > xs5)
    equal -1 (compare xs1 xs6)
    equal false (xs1 > xs6)

[<Fact>]
let ``test Union comparison works`` () =
    let u1 = A 2
    let u2 = A 2
    let u3 = A 4
    let u4 = A 1
    let u5 = B 2
    equal 0 (compare u1 u2)
    equal -1 (compare u1 u3)
    equal true (u1 < u3)
    equal 1 (compare u1 u4)
    equal false (u1 < u4)
    (compare u1 u5) = 0 |> equal false

[<Fact>]
let ``test Union custom comparison works`` () =
    let u1 = String "A"
    let u2 = String "A"
    let u3 = String "AA"
    equal 0 (compare u1 u3)
    equal true (compare u1 u2 > 0)

[<Fact>]
let ``test Record comparison works`` () =
    let r1 = { a = 1; b = 2 }
    let r2 = { a = 1; b = 2 }
    let r3 = { a = 1; b = 4 }
    equal 0 (compare r1 r2)
    (compare r1 r3) = 0 |> equal false

[<Fact>]
let ``test Comparison with objects implementing IComparable works`` () =
    let c1 = MyTest(5)
    let c2 = MyTest(4)
    let c3 = MyTest(5)
    equal 0 (compare c1 c2)
    equal 1 (compare c1 c3)
    equal true (c1 > c3)

[<Fact>]
let ``test compare with NaN follows .NET total ordering`` () =
    equal 0 (compare nan nan)
    equal -1 (compare nan 1.0)
    equal 1 (compare 1.0 nan)
    equal -1 (compare nan infinity)
    equal 1 (compare infinity nan)
    equal -1 (compare nan (-infinity))
    equal (compare nan 1.0) (-(compare 1.0 nan))

[<Fact>]
let ``test List.sort with NaN puts NaN first`` () =
    let sorted = List.sort [ 3.; nan; 1.; 2. ]
    Double.IsNaN(List.head sorted) |> equal true
    equal [ 1.; 2.; 3. ] (List.tail sorted)

[<Fact>]
let ``test min and max propagate NaN like .NET`` () =
    Double.IsNaN(min nan 1.0) |> equal true
    Double.IsNaN(min 1.0 nan) |> equal true
    Double.IsNaN(max nan 1.0) |> equal true
    Double.IsNaN(max 1.0 nan) |> equal true

[<Fact>]
let ``test max works with primitives`` () =
    max 1 2 |> equal 2
    max 10m 2m |> equal 10m
    Math.Max(1, 2) |> equal 2
    max "a" "b" |> equal "b"

[<Fact>]
let ``test max works with records`` () =
    let r1 = {a=1; b=1}
    let r2 = {a=1; b=2}
    max r1 r2 |> equal r2

[<Fact>]
let ``test max with objects implementing IComparable works`` () =
    let c1 = MyTest(5)
    let c2 = MyTest(5)
    System.Object.ReferenceEquals(max c1 c2, c1) |> equal true

[<Fact>]
let ``test min works with primitives`` () =
    min 1 2 |> equal 1
    min 10m 2m |> equal 2m
    System.Math.Min(1, 2) |> equal 1
    min "a" "b" |> equal "a"

[<Fact>]
let ``test min works with records`` () =
    let r1 = {a=1; b=1}
    let r2 = {a=1; b=2}
    min r1 r2 |> equal r1

[<Fact>]
let ``test min with objects implementing IComparable works`` () =
    let c1 = MyTest(5)
    let c2 = MyTest(5)
    Object.ReferenceEquals(min c1 c2, c2) |> equal true

[<Fact>]
let ``test nullArg works`` () =
    try
        nullArg null
        true
    with _ex ->
        false
    |> equal false


[<Fact>]
let ``test using function disposes the resource when action finishes`` () =
    let mutable disposed = false
    let resource = { new IDisposable with member _.Dispose() = disposed <- true }
    using resource (fun _resource -> ())
    equal true disposed

[<Fact>]
let ``test using function disposes the resource when action fails`` () =
    let mutable disposed = false
    let resource = { new IDisposable with member _.Dispose() = disposed <- true }
    try
        using resource (fun _resource -> failwith "action failed")
    with
    | _ -> () // ignore
    equal true disposed

[<Fact>]
let ``test isNull with primitives works`` () =
    isNull null |> equal true
    isNull (box 5) |> equal false
    isNull "" |> equal false
    isNull "0" |> equal false
    isNull "hello" |> equal false

[<Fact>]
let ``test isNull with objects works`` () =
    let s1: String = null
    isNull s1 |> equal true
    let s2: String = "hello"
    isNull s2 |> equal false

[<Fact>]
let ``test Classes must use identity hashing by default`` () =
    let x = MyClass(5)
    let y = MyClass(5)
    let h1 = hash(box x)
    let h2 = hash(box y)
    x.Value <- 8
    let h3 = hash(box x)
    h1 = h2 |> equal false
    h1 = h3 |> equal true

// #if FABLE_COMPILER
// [<Fact>]
// let ``test GetHashCode with arrays works`` () =
//     ([|1; 2|].GetHashCode(), [|1; 2|].GetHashCode()) ||> equal // Equal in Python (not in .NET)
//     ([|2; 1|].GetHashCode(), [|1; 2|].GetHashCode()) ||> notEqual
// #endif

// [<Fact>]
// let ``test GetHashCode with arrays works II`` () =
//     // Assigning the arrays makes them different
//     let a = [|1; 2|]
//     let b = [|1; 2|]
//     (a.GetHashCode(), b.GetHashCode()) ||> notEqual
//     ([|2; 1|].GetHashCode(), [|1; 2|].GetHashCode()) ||> notEqual

// [<Fact>]
// let ``test GetHashCode with lists works`` () =
//     ([1; 2].GetHashCode(), [1; 2].GetHashCode()) ||> equal
//     ([2; 1].GetHashCode(), [1; 2].GetHashCode()) ||> notEqual

[<Fact>]
let ``test Custom Equals and GetHashCode are used by structural values`` () = // See #4834
    let left = CustomValue(1, "left")
    let right = CustomValue(1, "right")

    left = right |> equal true
    hash left = hash right |> equal true

    WrappedUnion left = WrappedUnion right |> equal true
    hash (WrappedUnion left) = hash (WrappedUnion right) |> equal true

    { Value = left } = { Value = right } |> equal true
    hash { Value = left } = hash { Value = right } |> equal true

    [| left |] = [| right |] |> equal true
    hash [| left |] = hash [| right |] |> equal true

[<Fact>]
let ``GetHashCode with primitives works`` () =
    ((1).GetHashCode(), (1).GetHashCode()) ||> equal
    ((2).GetHashCode(), (1).GetHashCode()) ||> notEqual
    ("1".GetHashCode(), "1".GetHashCode()) ||> equal
    ("2".GetHashCode(), "1".GetHashCode()) ||> notEqual

[<Fact>]
let ``Equals with primitives works`` () =
    (true).Equals(true) |> equal true
    ('1').Equals('1') |> equal true
    (1y).Equals(1y) |> equal true
    (1uy).Equals(1uy) |> equal true
    (1s).Equals(1s) |> equal true
    (1).Equals(1) |> equal true
    (1L).Equals(1L) |> equal true
    (1u).Equals(1u) |> equal true
    (1us).Equals(1us) |> equal true
    (1ul).Equals(1ul) |> equal true
    (1uL).Equals(1uL) |> equal true
    (1.f).Equals(1.f) |> equal true
    (1.).Equals(1.) |> equal true
    (1.m).Equals(1.m) |> equal true
    ("1").Equals("1") |> equal true

[<Fact>]
let ``CompareTo with primitives works`` () =
    (true).CompareTo(true) |> equal 0
    ('1').CompareTo('1') |> equal 0
    (1y).CompareTo(1y) |> equal 0
    (1uy).CompareTo(1uy) |> equal 0
    (1s).CompareTo(1s) |> equal 0
    (1).CompareTo(1) |> equal 0
    (1L).CompareTo(1L) |> equal 0
    (1u).CompareTo(1u) |> equal 0
    (1us).CompareTo(1us) |> equal 0
    (1ul).CompareTo(1ul) |> equal 0
    (1uL).CompareTo(1uL) |> equal 0
    (1.f).CompareTo(1.f) |> equal 0
    (1.).CompareTo(1.) |> equal 0
    (1.m).CompareTo(1.m) |> equal 0
    ("1").CompareTo("1") |> equal 0

[<Fact>]
let ``test GetHashCode with wide numeric types works`` () =
    // These route through identity hashing, which used to take a different path
    // than structural hashing for the widths below.
    (5L).GetHashCode() |> equal ((5L).GetHashCode())
    (5UL).GetHashCode() |> equal ((5UL).GetHashCode())
    (5M).GetHashCode() |> equal ((5M).GetHashCode())
    (5I).GetHashCode() |> equal ((5I).GetHashCode())
    (5L).GetHashCode() = (6L).GetHashCode() |> equal false
    (5UL).GetHashCode() = (6UL).GetHashCode() |> equal false
    (5M).GetHashCode() = (6M).GetHashCode() |> equal false
    (5I).GetHashCode() = (6I).GetHashCode() |> equal false

[<Fact>]
let ``test hashing wide numeric types agrees with GetHashCode`` () =
    hash 5L |> equal ((5L).GetHashCode())
    hash 5UL |> equal ((5UL).GetHashCode())
    hash 5M |> equal ((5M).GetHashCode())
    hash 5I |> equal ((5I).GetHashCode())

[<Fact>]
let ``test wide numeric types work as hash keys`` () =
    // Added one at a time rather than from a sequence: constructing a HashSet from
    // an IEnumerable trips a known Pyright gap, the one that keeps test_hash_set.py
    // in the CI exclude list.
    let longs = System.Collections.Generic.HashSet<int64>()
    longs.Add 1L |> ignore
    longs.Add 2L |> ignore
    longs.Add 2L |> equal false
    longs.Contains 2L |> equal true
    longs.Contains 9L |> equal false
    let ulongs = System.Collections.Generic.HashSet<uint64>()
    ulongs.Add 2UL |> ignore
    ulongs.Contains 2UL |> equal true
    let decimals = System.Collections.Generic.HashSet<decimal>()
    decimals.Add 2M |> ignore
    decimals.Contains 2M |> equal true
    let bigs = System.Collections.Generic.HashSet<bigint>()
    bigs.Add 2I |> ignore
    bigs.Contains 2I |> equal true

// ---- ported from tests/Js/Main (2026-11-16) ----

[<CustomEquality; NoComparison>]
type FuzzyInt =
    | FuzzyInt of int
    override x.GetHashCode() =
        let (FuzzyInt x) = x
        x.GetHashCode()

    override x.Equals(y: obj) =
        match y with
        | :? FuzzyInt as y ->
            let (FuzzyInt x) = x
            let (FuzzyInt y) = y
            x - 2 <= y && y <= x + 2
        | _ -> false

type Test(i: int) =
    member x.Value = i
    override x.GetHashCode() = i
    override x.Equals(yobj) =
       match yobj with
         | :? Test as y -> y.Value + 1 = x.Value
         | _ -> false
    interface System.IComparable with
        member x.CompareTo(yobj) =
            match yobj with
            | :? Test as y -> compare (y.Value + 1) x.Value
            | _ -> invalidArg "yobj" "cannot compare values of different types"
            // | _ -> -1

    interface System.IEquatable<Test> with
        member x.Equals(y) =
            y.Value + 1 = x.Value

let genericCompare (a: 'T) (b: 'T) : int =
    let cmp = Comparer<'T>.Default
    cmp.Compare(a, b)


[<Fact>]
let ``test Array custom equality works`` () =
    let xs = [| FuzzyInt 3; FuzzyInt 5 |]
    let ys = [| FuzzyInt 2; FuzzyInt 4 |]
    let zs = [| FuzzyInt 2; FuzzyInt 8 |]
    xs = ys |> equal true
    xs = zs |> equal false

[<Fact>]
let ``test GetHashCode with tuples works`` () =
    ((1, 2).GetHashCode(), (1, 2).GetHashCode()) ||> equal
    ((2, 1).GetHashCode(), (1, 2).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with options works`` () =
    ((Some 1).GetHashCode(), (Some 1).GetHashCode()) ||> equal
    ((Some 2).GetHashCode(), (Some 1).GetHashCode()) ||> notEqual
    ((Some None).GetHashCode(), (Some 1).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with unions works`` () =
    ((UTest.A 1).GetHashCode(), (UTest.A 1).GetHashCode()) ||> equal
    ((UTest.A 2).GetHashCode(), (UTest.A 1).GetHashCode()) ||> notEqual
    ((UTest.B 1).GetHashCode(), (UTest.A 1).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with records works`` () =
    ({a=1; b=2}.GetHashCode(), {a=1; b=2}.GetHashCode()) ||> equal
    ({a=2; b=1}.GetHashCode(), {a=1; b=2}.GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with structs works`` () =
    (STest(1).GetHashCode(), STest(1).GetHashCode()) ||> equal
    (STest(2).GetHashCode(), STest(1).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with objects works`` () =
    (OTest(1).GetHashCode(), OTest(1).GetHashCode()) ||> notEqual
    (OTest(2).GetHashCode(), OTest(1).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with objects that overwrite it works`` () =
    (Test(1).GetHashCode(), Test(1).GetHashCode()) ||> equal
    (Test(2).GetHashCode(), Test(1).GetHashCode()) ||> notEqual

[<Fact>]
let ``test GetHashCode with same object works`` () =
    let o = OTest(1)
    let h1 = o.GetHashCode()
    o.A <- 2
    let h2 = o.GetHashCode()
    (h1, h2) ||> equal

[<Fact>]
let ``test GetHashCode with primitives works`` () =
    ((1).GetHashCode(), (1).GetHashCode()) ||> equal
    ((2).GetHashCode(), (1).GetHashCode()) ||> notEqual
    ("1".GetHashCode(), "1".GetHashCode()) ||> equal
    ("2".GetHashCode(), "1".GetHashCode()) ||> notEqual

[<Fact>]
let ``test Equals with primitives works`` () =
    (true).Equals(true) |> equal true
    ('1').Equals('1') |> equal true
    (1y).Equals(1y) |> equal true
    (1uy).Equals(1uy) |> equal true
    (1s).Equals(1s) |> equal true
    (1).Equals(1) |> equal true
    (1L).Equals(1L) |> equal true
    (1u).Equals(1u) |> equal true
    (1us).Equals(1us) |> equal true
    (1ul).Equals(1ul) |> equal true
    (1uL).Equals(1uL) |> equal true
    (1.f).Equals(1.f) |> equal true
    (1.).Equals(1.) |> equal true
    (1.m).Equals(1.m) |> equal true
    ("1").Equals("1") |> equal true

[<Fact>]
let ``test CompareTo with primitives works`` () =
    (true).CompareTo(true) |> equal 0
    ('1').CompareTo('1') |> equal 0
    (1y).CompareTo(1y) |> equal 0
    (1uy).CompareTo(1uy) |> equal 0
    (1s).CompareTo(1s) |> equal 0
    (1).CompareTo(1) |> equal 0
    (1L).CompareTo(1L) |> equal 0
    (1u).CompareTo(1u) |> equal 0
    (1us).CompareTo(1us) |> equal 0
    (1ul).CompareTo(1ul) |> equal 0
    (1uL).CompareTo(1uL) |> equal 0
    (1.f).CompareTo(1.f) |> equal 0
    (1.).CompareTo(1.) |> equal 0
    (1.m).CompareTo(1.m) |> equal 0
    ("1").CompareTo("1") |> equal 0

[<Fact>]
let ``test hash works with JS objects`` () =
    // See #2281
    let _ = obj () |> hash
    ()

[<Fact>]
let ``test hash with arrays works`` () =
    (hash [|1; 2|], hash [|1; 2|]) ||> equal
    (hash [|2; 1|], hash [|1; 2|]) ||> notEqual

[<Fact>]
let ``test hash with lists works`` () =
    (hash [1; 2], hash [1; 2]) ||> equal
    (hash [2; 1], hash [1; 2]) ||> notEqual

[<Fact>]
let ``test hash with tuples works`` () =
    (hash (1, 2), hash (1, 2)) ||> equal
    (hash (2, 1), hash (1, 2)) ||> notEqual

[<Fact>]
let ``test hash with options works`` () =
    (hash (Some 1), hash (Some 1)) ||> equal
    (hash (Some 2), hash (Some 1)) ||> notEqual
    (hash (Some None), hash (Some 1)) ||> notEqual

[<Fact>]
let ``test hash with unions works`` () =
    (hash (UTest.A 1), hash (UTest.A 1)) ||> equal
    (hash (UTest.A 2), hash (UTest.A 1)) ||> notEqual
    (hash (UTest.B 1), hash (UTest.A 1)) ||> notEqual

[<Fact>]
let ``test hash with records works`` () =
    (hash {a=1; b=2}, hash {a=1; b=2}) ||> equal
    (hash {a=2; b=1}, hash {a=1; b=2}) ||> notEqual

[<Fact>]
let ``test hash with structs works`` () =
    (hash (STest(1)), hash (STest(1))) ||> equal
    (hash (STest(2)), hash (STest(1))) ||> notEqual

[<Fact>]
let ``test hash with objects works`` () =
    (hash (OTest(1)), hash (OTest(1))) ||> notEqual
    (hash (OTest(2)), hash (OTest(1))) ||> notEqual

[<Fact>]
let ``test hash with same object works`` () =
    let o = OTest(1)
    let h1 = hash o
    o.A <- 2
    let h2 = hash o
    (h1, h2) ||> equal

[<Fact>]
let ``test hash with longs works`` () =
    (hash (1L<<<33), hash (1L<<<33)) ||> equal
    (hash (1L<<<34), hash (1L<<<33)) ||> notEqual
    (hash 3L, hash (3L + (1L<<<33))) ||> notEqual
    (hash (-3L), hash (3L))          ||> notEqual

[<Fact>]
let ``test hash with primitives works`` () =
    (hash 111, hash 111) ||> equal
    (hash 222, hash 111) ||> notEqual
    (hash "1", hash "1") ||> equal
    (hash "2", hash "1") ||> notEqual

[<Fact>]
let ``test Unchecked.hash with primitives works`` () =
    (Unchecked.hash 111, Unchecked.hash 111) ||> equal
    (Unchecked.hash 222, Unchecked.hash 333) ||> notEqual
    (Unchecked.hash "1", Unchecked.hash "1") ||> equal
    (Unchecked.hash "2", Unchecked.hash "3") ||> notEqual

[<Fact>]
let ``test Unchecked.hash with lists works`` () =
    (Unchecked.hash [1;2], Unchecked.hash [1;2]) ||> equal
    (Unchecked.hash [2;1], Unchecked.hash [1;2]) ||> notEqual

[<Fact>]
let ``test Unchecked.hash with arrays works`` () =
    (Unchecked.hash [|1;2|], Unchecked.hash [|1;2|]) ||> equal
    (Unchecked.hash [|2;1|], Unchecked.hash [|1;2|]) ||> notEqual

[<Fact>]
let ``test Unchecked.hash with tuples works`` () =
    (Unchecked.hash (1,2), Unchecked.hash (1,2)) ||> equal
    (Unchecked.hash (2,1), Unchecked.hash (1,2)) ||> notEqual

[<Fact>]
let ``test Unchecked.equals works`` () =
    Unchecked.equals 111 111 |> equal true
    Unchecked.equals 222 333 |> equal false
    Unchecked.equals "1" "1" |> equal true
    Unchecked.equals "2" "3" |> equal false
    Unchecked.equals [1] [1] |> equal true
    Unchecked.equals [2] [3] |> equal false
    // Use mutable values to prevent inlining
    let mutable ones = 111
    let mutable twos = 222
    let mutable threes = 333
    let mutable oneStr = "1"
    let mutable twoStr = "2"
    let mutable threeStr = "3"
    Unchecked.equals ones ones |> equal true
    Unchecked.equals twos threes |> equal false
    Unchecked.equals oneStr oneStr |> equal true
    Unchecked.equals twoStr threeStr |> equal false

[<Fact>]
let ``test Unchecked.compare works`` () =
    Unchecked.compare 111 111 |> equal 0
    Unchecked.compare 222 333 |> equal -1
    Unchecked.compare 333 222 |> equal 1
    Unchecked.compare "1" "1" |> equal 0
    Unchecked.compare "2" "3" |> equal -1
    Unchecked.compare "3" "2" |> equal 1
    Unchecked.compare [1] [1] |> equal 0
    Unchecked.compare [2] [3] |> equal -1
    Unchecked.compare [3] [2] |> equal 1

[<Fact>]
let ``test DU comparison works`` () =
    let hasStatusReached expectedStatus status =
        status >= expectedStatus
    let mutable run = fun x y ->
        x >= y |> equal true
        hasStatusReached y x |> equal true
    run Status.CreateNewMeterReadingPicture Status.SelectingNewDevice

[<Fact>]
let ``test LanguagePrimitives.GenericHash with primitives works`` () =
    (LanguagePrimitives.GenericHash 111, LanguagePrimitives.GenericHash 111) ||> equal
    (LanguagePrimitives.GenericHash 222, LanguagePrimitives.GenericHash 111) ||> notEqual
    (LanguagePrimitives.GenericHash "1", LanguagePrimitives.GenericHash "1") ||> equal
    (LanguagePrimitives.GenericHash "2", LanguagePrimitives.GenericHash "1") ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.GenericHash with lists works`` () =
    (LanguagePrimitives.GenericHash [1;2], LanguagePrimitives.GenericHash [1;2]) ||> equal
    (LanguagePrimitives.GenericHash [2;1], LanguagePrimitives.GenericHash [1;2]) ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.GenericHash with arrays works`` () =
    (LanguagePrimitives.GenericHash [|1;2|], LanguagePrimitives.GenericHash [|1;2|]) ||> equal
    (LanguagePrimitives.GenericHash [|2;1|], LanguagePrimitives.GenericHash [|1;2|]) ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.GenericHash with tuples works`` () =
    (LanguagePrimitives.GenericHash (1,2), LanguagePrimitives.GenericHash (1,2)) ||> equal
    (LanguagePrimitives.GenericHash (2,1), LanguagePrimitives.GenericHash (1,2)) ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.PhysicalHash with primitives works`` () =
    (LanguagePrimitives.PhysicalHash "1", LanguagePrimitives.PhysicalHash "1") ||> equal
    (LanguagePrimitives.PhysicalHash "2", LanguagePrimitives.PhysicalHash "1") ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.PhysicalHash with tuples works`` () =
    (LanguagePrimitives.PhysicalHash (1,2), LanguagePrimitives.PhysicalHash (1,2)) ||> notEqual
    (LanguagePrimitives.PhysicalHash (2,1), LanguagePrimitives.PhysicalHash (1,2)) ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.GenericComparison works`` () =
    LanguagePrimitives.GenericComparison 111 111 |> equal 0
    LanguagePrimitives.GenericComparison 222 333 |> equal -1
    LanguagePrimitives.GenericComparison 333 222 |> equal 1
    LanguagePrimitives.GenericComparison "1" "1" |> equal 0
    LanguagePrimitives.GenericComparison "2" "3" |> equal -1
    LanguagePrimitives.GenericComparison "3" "2" |> equal 1
    LanguagePrimitives.GenericComparison [1] [1] |> equal 0
    LanguagePrimitives.GenericComparison [2] [3] |> equal -1
    LanguagePrimitives.GenericComparison [3] [2] |> equal 1

[<Fact>]
let ``test LanguagePrimitives.GenericEquality works`` () =
    LanguagePrimitives.GenericEquality 111 111 |> equal true
    LanguagePrimitives.GenericEquality 222 333 |> equal false
    LanguagePrimitives.GenericEquality "1" "1" |> equal true
    LanguagePrimitives.GenericEquality "2" "3" |> equal false
    LanguagePrimitives.GenericEquality [1] [1] |> equal true
    LanguagePrimitives.GenericEquality [2] [3] |> equal false
    // Use mutable values to prevent inlining
    let mutable ones = 111
    let mutable twos = 222
    let mutable threes = 333
    let mutable oneStr = "1"
    let mutable twoStr = "2"
    let mutable threeStr = "3"
    LanguagePrimitives.GenericEquality ones ones |> equal true
    LanguagePrimitives.GenericEquality twos threes |> equal false
    LanguagePrimitives.GenericEquality oneStr oneStr |> equal true
    LanguagePrimitives.GenericEquality twoStr threeStr |> equal false

[<Fact>]
let ``test LanguagePrimitives.PhysicalEquality works`` () =
    LanguagePrimitives.PhysicalEquality "1" "1" |> equal true
    LanguagePrimitives.PhysicalEquality "2" "3" |> equal false
    LanguagePrimitives.PhysicalEquality [1] [1] |> equal false
    LanguagePrimitives.PhysicalEquality [2] [3] |> equal false
    // Use mutable values to prevent inlining
    let mutable oneStr = "1"
    let mutable twoStr = "2"
    let mutable threeStr = "3"
    LanguagePrimitives.PhysicalEquality oneStr oneStr |> equal true
    LanguagePrimitives.PhysicalEquality twoStr threeStr |> equal false

[<Fact>]
let ``test LanguagePrimitives.SByteWithMeasure works`` () =
    let distance: sbyte<m> = LanguagePrimitives.SByteWithMeasure 1y
    distance |> equal 1y<m>

[<Fact>]
let ``test LanguagePrimitives.Int16WithMeasure works`` () =
    let distance: int16<m> = LanguagePrimitives.Int16WithMeasure 1s
    distance |> equal 1s<m>

[<Fact>]
let ``test LanguagePrimitives.Int32WithMeasure works`` () =
    let distance: int<m> = LanguagePrimitives.Int32WithMeasure 1
    distance |> equal 1<m>

[<Fact>]
let ``test LanguagePrimitives.Int64WithMeasure works`` () =
    let distance: int64<m> = LanguagePrimitives.Int64WithMeasure 1L
    distance |> equal 1L<m>

[<Fact>]
let ``test LanguagePrimitives.Float32WithMeasure works`` () =
    let distance: float32<m> = LanguagePrimitives.Float32WithMeasure 1.0f
    distance |> equal 1.0f<m>

[<Fact>]
let ``test LanguagePrimitives.FloatWithMeasure works`` () =
    let distance: float<m> = LanguagePrimitives.FloatWithMeasure 1.0
    distance |> equal 1.0<m>

[<Fact>]
let ``test LanguagePrimitives.DecimalWithMeasure works`` () =
    let distance: decimal<m> = LanguagePrimitives.DecimalWithMeasure 1.0m
    distance |> equal 1.0m<m>

[<Fact>]
let ``test EqualityComparer.Equals works`` () =
    genericEquals 1 1 |> equal true
    genericEquals 1 2 |> equal false
    genericEquals "1" "1" |> equal true
    genericEquals "1" "2" |> equal false

[<Fact>]
let ``test EqualityComparer.GetHashCode works`` () =
    genericHash 1 |> equal ((1).GetHashCode())
    genericHash "1" |> equal ("1".GetHashCode())
[<Fact>]
let ``test Comparer.Compare works`` () =
    genericCompare 1 1 |> equal 0
    genericCompare 1 2 |> equal -1
    genericCompare 2 1 |> equal 1

[<Fact>]
let ``test Comparer.Create works`` () =
    let cmp = Comparer<'T>.Create(fun x y -> -(compare x y))
    cmp.Compare(1, 1) |> equal 0
    cmp.Compare(1, 2) |> equal 1
    cmp.Compare(2, 1) |> equal -1

[<Fact>]
let ``test EqualityComparer.Create works`` () =
    let cmp = EqualityComparer<'T>.Create((<>), hash)
    cmp.Equals(1, 1) |> equal false
    cmp.Equals(1, 2) |> equal true

[<Fact>]
let ``test LanguagePrimitives.PhysicalHash with lists works`` () =
    (LanguagePrimitives.PhysicalHash [1;2], LanguagePrimitives.PhysicalHash [1;2]) ||> notEqual
    (LanguagePrimitives.PhysicalHash [2;1], LanguagePrimitives.PhysicalHash [1;2]) ||> notEqual

[<Fact>]
let ``test LanguagePrimitives.PhysicalHash with arrays works`` () =
    (LanguagePrimitives.PhysicalHash [|1;2|], LanguagePrimitives.PhysicalHash [|1;2|]) ||> notEqual
    (LanguagePrimitives.PhysicalHash [|2;1|], LanguagePrimitives.PhysicalHash [|1;2|]) ||> notEqual


type SameCellRecord = { A: int }

[<Fact>]
let ``test Fable.Core.Zig.sameCell tells cells apart`` () =
    let xs = [ 1; 2 ]
    let ys = xs
    Fable.Core.Zig.sameCell xs ys |> equal true
    Fable.Core.Zig.sameCell xs (List.map id xs) |> equal false
    let r = ref 1
    Fable.Core.Zig.sameCell r r |> equal true
    Fable.Core.Zig.sameCell r (ref 1) |> equal false
    let f = fun (x: int) -> x + r.Value
    Fable.Core.Zig.sameCell f f |> equal true
    let o = obj ()
    Fable.Core.Zig.sameCell o o |> equal true
    Fable.Core.Zig.sameCell o (obj ()) |> equal false
    let a = { A = 1 }
#if FABLE_COMPILER_ZIG
    // (an immutable record is a value here: never the same cell)
    Fable.Core.Zig.sameCell a a |> equal false
#else
    Fable.Core.Zig.sameCell a a |> equal true
#endif
    (Fable.Core.Zig.sameCell a { A = 1 } || a = { A = 1 }) |> equal true
