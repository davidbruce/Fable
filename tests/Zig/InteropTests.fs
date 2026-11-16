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

[<Erase; Import("*Counter", "./native/interop.zig")>]
type ICounter =
    abstract add: x: int -> int
    abstract n: int with get, set

[<Import("counter_new", "./native/interop.zig")>]
let counterNew (start: int) : ICounter = nativeOnly

[<Import("counter_free", "./native/interop.zig")>]
let counterFree (c: ICounter) : unit = nativeOnly

[<Import("counters_live", "./native/interop.zig")>]
let countersLive () : int = nativeOnly

[<Fact>]
let ``test Erased interfaces are Zig types`` () =
    let c = counterNew 1
    c.add 2 |> equal 3
    c.n |> equal 3
    c.n <- 10
    c.add 1 |> equal 11
    counterFree c

type IResource<'T> =
    static abstract Destroy: 'T -> unit

/// (a handle of Zig's, freed after the last use of the record that owns it)
type OwnedCounter =
    { C: ICounter }

    interface IResource<OwnedCounter> with
        static member Destroy(o: OwnedCounter) = counterFree o.C

let useCounter (o: OwnedCounter) = o.C.add 5

[<Fact>]
let ``test A resource gives up a Zig handle after its last use`` () =
    let before = countersLive ()
    let total =
        let o = { C = counterNew 1 }
        countersLive () |> equal (before + 1)
        useCounter o
    total |> equal 6
    countersLive () |> equal before

let twiceText (s: string) = s + s

[<Import("call_twice_text", "./native/interop.zig")>]
let callTwiceText (s: string) : string = nativeOnly

[<Fact>]
let ``test Zig code can call F# functions`` () =
    let s = "ab"
    callTwiceText s |> equal "abab"
    s |> equal "ab"

[<Struct>]
type Vec2 = { x: float32; y: float32 }

[<Struct; System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Sequential)>]
type Vector2 =
    val x: float32
    val y: float32
    new(x, y) = { x = x; y = y }

[<Struct>]
type Rect =
    {
        pos: Vec2
        width: float32
        height: float32
        solid: bool
    }

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_vadd")>]
extern Vec2 vaddRecord(Vec2 a, Vec2 b)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_vadd")>]
extern Vector2 vaddFields(Vector2 a, Vector2 b)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_area")>]
extern float32 area(Rect r)

[<Import("fable_test_vadd", "c:./native/cvec.zig")>]
let vaddC (a: Vec2) (b: Vec2) : Vec2 = nativeOnly

[<Import("fable_test_area", "c:./native/cvec.zig")>]
let areaC (r: Rect) : float32 = nativeOnly

[<Fact>]
let ``test Structs are given to C and back by value`` () =
    vaddRecord ({ x = 1.0f; y = 2.0f }, { x = 3.0f; y = 4.0f }) |> equal { x = 4.0f; y = 6.0f }
    let v = vaddFields (Vector2(1.5f, 2.5f), Vector2(0.5f, 0.5f))
    (v.x, v.y) |> equal (2.0f, 3.0f)

    let r =
        {
            pos = { x = 1.0f; y = 0.0f }
            width = 3.0f
            height = 4.0f
            solid = true
        }

    area r |> equal 13.0f
    area { r with solid = false } |> equal 0.0f
    vaddC { x = 1.0f; y = 1.0f } { x = 2.0f; y = 2.0f } |> equal { x = 3.0f; y = 3.0f }
    areaC r |> equal 13.0f
#endif
