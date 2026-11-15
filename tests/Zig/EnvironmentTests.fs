module Fable.Tests.Zig.EnvironmentTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<Fact>]
let ``test Environment.GetEnvironmentVariable returns null for a missing variable`` () =
    Environment.GetEnvironmentVariable("__FABLE_NON_EXISTENT_VAR__")
    |> equal null


[<Fact>]
let ``test Environment.CurrentDirectory works`` () =
    Environment.CurrentDirectory.Length > 0
    |> equal true


[<Fact>]
let ``test Console.Out.WriteLine works`` () =
    Console.Out.WriteLine("Hello stdout")


[<Fact>]
let ``test Console.Error.WriteLine works`` () =
    Console.Error.WriteLine("Hello stderr")
