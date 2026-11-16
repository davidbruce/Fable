/// What the tests of the Zig target use. Under Fable each function marked `[<Fact>]` is a Zig
/// `test` that `zig test` runs; under .NET they are xUnit tests.
module Fable.Tests.Util

open System

module Testing =
#if FABLE_COMPILER
    type FactAttribute() =
        inherit Attribute()

    let equal<'T when 'T: equality> (expected: 'T) (actual: 'T) : unit =
        if expected <> actual then
            failwith (sprintf "Expected: %A - Actual: %A" expected actual)

    let notEqual<'T when 'T: equality> (expected: 'T) (actual: 'T) : unit =
        if expected = actual then
            failwith (sprintf "Expected a value other than %A" expected)
#else
    open Xunit
    type FactAttribute = Xunit.FactAttribute

    let equal<'T> (expected: 'T) (actual: 'T) : unit = Assert.Equal<'T>(expected, actual)
    let notEqual<'T> (expected: 'T) (actual: 'T) : unit = Assert.NotEqual<'T>(expected, actual)
#endif

open Testing

/// The message of what `f` raises (Error), or that it raised nothing (Ok).
let private run (f: unit -> 'a) : Result<unit, string> =
    try
        f () |> ignore
        Ok()
    with e ->
        Error e.Message

let throwsError (expected: string) (f: unit -> 'a) : unit =
    match run f with
    | Error _ when String.IsNullOrEmpty expected -> ()
    | Error actual -> equal expected actual
    | Ok() -> failwith ("Expected an exception: " + expected)

let throwsErrorContaining (expected: string) (f: unit -> 'a) : unit =
    match run f with
    | Error actual when actual.Contains expected -> ()
    | Error actual -> equal expected actual
    | Ok() -> failwith ("Expected an exception containing: " + expected)

let throwsAnyError (f: unit -> 'a) : unit =
    match run f with
    | Error _ -> ()
    | Ok() -> failwith "Expected an exception"

let doesntThrow (f: unit -> 'a) : unit =
    match run f with
    | Ok() -> ()
    | Error msg -> failwith ("Expected no exception, got: " + msg)

/// The class of what `f` raises, the most specific first.
let raisedExceptionType (f: unit -> 'a) : string =
    try
        f () |> ignore
        "no exception"
    with
    | :? ArgumentOutOfRangeException -> "ArgumentOutOfRangeException"
    | :? ArgumentNullException -> "ArgumentNullException"
    | :? ArgumentException -> "ArgumentException"
    | :? InvalidOperationException -> "InvalidOperationException"
    | :? FormatException -> "FormatException"
    | :? IndexOutOfRangeException -> "IndexOutOfRangeException"
    | :? NotSupportedException -> "NotSupportedException"
    | :? OverflowException -> "OverflowException"
    | :? System.Collections.Generic.KeyNotFoundException -> "KeyNotFoundException"
    | e -> "Unexpected exception: " + e.Message

// ---- what MiscTests uses (as the other targets have it) ----

let Int32Array = [|1;2|]

module Float64Array =
    let Float64Array = [|3.;4.|]

module Foo =
    let update () = ()

module Bar =
    let rec nestedRecursive i = update (i+2)
    and update i = i + 5

let f2 a b = a + b

// Assignment block as expression outside a function is NOT optimized
f2(let mutable x = 5 in let mutable y = 6 in x + y) |> ignore

let mutable a = 10

module B =
  let c = a
  a <- a + 5
  let mutable a = 20
  let d = f2 2 2
  let f2 a b = a - b

  module D =
    let d = a
    a <- a + 5
    let e = f2 2 2

let rec nonNestedRecursive s = update s
and update s = String.replicate 3 s

let mutable mutableValue = 1
let mutable mutableValueOpt = Some 1

let getValueTimes2() = mutableValue * 2

module Nested =
    let mutable nestedMutableValue = "a"

    let getValueTimes2() = nestedMutableValue + nestedMutableValue

    let getOuterValueTimes4() = mutableValue * 4

let getNestedValueTimes3() = Nested.nestedMutableValue + Nested.nestedMutableValue + Nested.nestedMutableValue
