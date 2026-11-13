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
