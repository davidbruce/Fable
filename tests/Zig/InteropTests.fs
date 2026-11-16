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

// (C's library: `zig test -lc`, see src/Fable.Build/Test/Zig.fs)
[<System.Runtime.InteropServices.DllImport("libc")>]
extern int abs(int x)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "strlen")>]
extern unativeint cStrlen(string s)

[<System.Runtime.InteropServices.DllImport("libc")>]
extern nativeint memset(byte[] buf, int c, unativeint n)

[<Fact>]
let ``test C functions can be called with DllImport`` () =
    abs -5 |> equal 5
    cStrlen "hello" |> int |> equal 5
    // (UTF-8 of more than the stack buffer of a call)
    cStrlen (String.replicate 300 "é") |> int |> equal 600
    cStrlen "" |> int |> equal 0
    let buf = Array.zeroCreate<byte> 4
    memset (buf, 7, 3un) |> ignore
    buf |> equal [| 7uy; 7uy; 7uy; 0uy |]

[<Import("strlen", "c:./native/libc.zig")>]
let strlenC (s: string) : int = nativeOnly

[<Import("strchr", "c:./native/libc.zig")>]
let strchrC (s: string) (c: int) : string = nativeOnly

[<Import("abs", "c:./native/libc.zig")>]
let absC (x: int) : int = nativeOnly

[<Fact>]
let ``test C declarations of a Zig module are given C's values`` () =
    strlenC "hello" |> equal 5
    strchrC "key=value" (int '=') |> equal "=value"
    strchrC "key" (int '=') |> isNull |> equal true
    absC -3 |> equal 3

[<System.Runtime.InteropServices.UnmanagedCallersOnly(EntryPoint = "fable_test_twice")>]
let twice (x: int) : int = x * 2

[<System.Runtime.InteropServices.UnmanagedCallersOnly(EntryPoint = "fable_test_len")>]
let textLength (s: string) : int = s.Length

[<Import("call_twice", "./native/interop.zig")>]
let callTwice (x: int) : int = nativeOnly

[<Import("call_len", "c:./native/interop.zig")>]
let callLength (s: string) : int = nativeOnly

[<Fact>]
let ``test F# functions can be given to C`` () =
    callTwice 21 |> equal 42
    // (to C as UTF-8, back to F# as a string: 5 chars)
    callLength "héllo" |> equal 5
#endif
