module Fable.Tests.Zig.InteropTests

open Fable.Core
open Fable.Tests.Util
open Fable.Tests.Util.Testing

#if FABLE_COMPILER_ZIG
[<Import("add", "./native/interop.zig")>]
let add: int -> int -> int = nativeOnly

[<ImportMember("./native/interop.zig")>]
let units (s: string) : int = nativeOnly

[<ImportMember("./native/interop.zig")>]
let greet (s: string) : string = nativeOnly

[<ImportMember("./native/interop.zig")>]
let keep (s: string) : unit = nativeOnly

[<Import("kept_len", "./native/interop.zig")>]
let keptLength () : int = nativeOnly

[<Import("release_kept", "./native/interop.zig")>]
let releaseKept () : unit = nativeOnly

[<Import("answer", "./native/interop.zig")>]
let answer: int = nativeOnly

[<Import("math.maxInt(i32)", "std")>]
let maxInt: int = nativeOnly

type System.String with
    [<Emit("@as(i32, @intCast(fable_rt.unitsOf($0).len)) + $1")>]
    member s.LengthPlus(n: int) : int = nativeOnly

[<Fact>]
let ``test Zig functions and values can be imported`` () =
    add 2 3 |> equal 5
    answer |> equal 42
    maxInt |> equal System.Int32.MaxValue
    units "abcd" |> equal 4
    let name = "zig"
    greet name |> equal "hello zig"
    name |> equal "zig"

[<Fact>]
let ``test Arguments of imported functions are borrowed for the call`` () =
    let s = String.replicate 3 "ab"
    keep s
    keptLength () |> equal 6
    s |> equal "ababab"
    releaseKept ()

[<Fact>]
let ``test Emit works on instance members`` () =
    "abc".LengthPlus 2 |> equal 5
#endif
