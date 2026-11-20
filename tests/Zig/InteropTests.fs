module Fable.Tests.Zig.InteropTests

#nowarn "9"

open System
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open FSharp.NativeInterop
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

type OwnedHandle<'T> =
    { C: ICounter; Tag: 'T }

    interface IResource<OwnedHandle<'T>> with
        static member Destroy(h: OwnedHandle<'T>) = counterFree h.C

let useHandle (h: OwnedHandle<'T>) = h.C.add 4

[<Fact>]
let ``test A generic IResource gives up a Zig handle after its last use`` () =
    let before = countersLive ()
    let n =
        let h = { C = counterNew 10; Tag = 7 }
        countersLive () |> equal (before + 1)
        useHandle h
    n |> equal 14
    countersLive () |> equal before
    let s =
        let h = { C = counterNew 20; Tag = "ok" }
        countersLive () |> equal (before + 1)
        h.Tag.Length + useHandle h
    s |> equal 26
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

type IntFn = delegate of int -> int
type NameFn = delegate of string * int -> unit

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_scale")>]
extern void scaleInPlace(Vec2& v, float32 k)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_bool4")>]
extern int bool4(bool b)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_bool1")>]
extern [<return: System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.I1)>] bool bool1(
    [<System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.I1)>] bool b
)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_is_positive")>]
extern bool isPositive(int x)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_wlen", CharSet = System.Runtime.InteropServices.CharSet.Unicode)>]
extern int wideLength(string s)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_wlen")>]
extern int wideLength2([<System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.LPWStr)>] string s)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_whello")>]
extern [<return: System.Runtime.InteropServices.MarshalAs(System.Runtime.InteropServices.UnmanagedType.LPWStr)>] string wideHello()

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_out_flag")>]
extern void outFlag(int x, [<System.Runtime.InteropServices.Out>] bool& flag)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_register")>]
extern void registerCallback(IntFn cb)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_fire")>]
extern int fireCallback(int x)

[<System.Runtime.InteropServices.DllImport("libc", EntryPoint = "fable_test_each_name")>]
extern void eachName(NameFn cb)

/// (kept alive while C may call it, as on .NET)
let private tripled = IntFn(fun x -> x * 3)

[<Fact>]
let ``test Byrefs, MarshalAs and callbacks cross to C as on .NET`` () =
    let mutable v = { x = 1.0f; y = 2.0f }
    scaleInPlace (&v, 3.0f)
    v |> equal { x = 3.0f; y = 6.0f }
    bool4 true |> equal 7
    bool4 false |> equal 3
    bool1 true |> equal false
    isPositive 5 |> equal true
    isPositive -5 |> equal false
    wideLength "héllo" |> equal 5
    wideLength2 "ab" |> equal 2
    wideHello () |> equal "héllo"
    let mutable flag = false
    outFlag (42, &flag)
    flag |> equal true
    outFlag (1, &flag)
    flag |> equal false
    // (a callback C keeps and calls later)
    registerCallback tripled
    fireCallback 5 |> equal 15
    fireCallback 7 |> equal 21
    // (one called while the call runs, with C strings)
    let seen = ResizeArray<string>()
    eachName (NameFn(fun name n -> seen.Add(sprintf "%s=%d" name n)))
    List.ofSeq seen |> equal [ "one=1"; "two=2" ]

[<Struct; StructLayout(LayoutKind.Sequential, Pack = 1)>]
type ZigPackedRec =
    {
        tag: byte
        val_: int64
        tail: uint16
    }

[<Struct; StructLayout(LayoutKind.Explicit)>]
type ZigIntFloat =
    [<FieldOffset(0)>]
    val mutable i: int32

    [<FieldOffset(0)>]
    val mutable f: float32

type Del6 = delegate of int * int * int * int * int * int -> int
type RoIntSpan = ReadOnlySpan<int>
type IntPtrT = nativeptr<int>

[<DllImport("libc", EntryPoint = "fable_test_packed_sum")>]
extern int64 packedSum (ZigPackedRec p)

[<DllImport("libc", EntryPoint = "fable_test_packed_ptr")>]
extern int64 packedPtr ([<In>] ZigPackedRec& p)

[<DllImport("libc", EntryPoint = "fable_test_union_as_bits")>]
extern int unionAsBits (ZigIntFloat u)

[<DllImport("libc", EntryPoint = "fable_test_9args")>]
extern int sum9 (int a1, int a2, int a3, int a4, int a5, int a6, int a7, int a8, int a9)

[<DllImport("libc", EntryPoint = "fable_test_inref_vec")>]
extern float32 inrefVec ([<In>] Vec2& v)

[<DllImport("libc", EntryPoint = "fable_test_byref_bool_ptr")>]
[<return: MarshalAs(UnmanagedType.I1)>]
extern bool toggleBoolAndBump ([<MarshalAs(UnmanagedType.I1)>] bool& b, IntPtrT p, int idx)

[<DllImport("libc", EntryPoint = "fable_test_null_array_span")>]
extern int sumNullArrAndSpan (int[] arr, RoIntSpan sp, int n)

[<DllImport("libc", EntryPoint = "fable_test_opt_callback")>]
extern int optCallback (int x, IntFn cb)

[<DllImport("libc", EntryPoint = "fable_test_callback6")>]
extern int callCb6 (Del6 cb)

[<UnmanagedCallersOnly(EntryPoint = "fable_test_uco_struct")>]
let ucoStruct (v: Vec2) (p: nativeptr<int>) (r: inref<int>) : Vec2 =
    NativePtr.write p (NativePtr.read p + r)
    { x = v.x * float32 r; y = v.y + 1.0f }

[<Import("fable_test_call_uco_struct", "c:./native/interop.zig")>]
let callUcoStruct (x: float32) (y: float32) (factor: int) : float32 = nativeOnly

let private readInrefVec (r: inref<Vec2>) = r.x * r.x + r.y * r.y

[<Fact>]
let ``test extern struct Pack, extern union, 9+ args, inref, null array/delegate, Span, and UnmanagedCallersOnly structs`` () =
    let mutable p: ZigPackedRec = { tag = 3uy; val_ = 100L; tail = 7us }
    Marshal.SizeOf<ZigPackedRec>() |> equal 11
    packedSum p |> equal 110L
    packedPtr &p |> equal 210L

    let mutable u = ZigIntFloat()
    u.f <- 1.0f
    unionAsBits u |> equal 0x3F800000

    sum9 (1, 2, 3, 4, 5, 6, 7, 8, 9) |> equal 45

    let mutable v: Vec2 = { x = 3.0f; y = 4.0f }
    inrefVec &v |> equal 34.0f
    let vImmut: Vec2 = { x = 3.0f; y = 4.0f }
    readInrefVec &vImmut |> equal 25.0f

    let arr = [| 10; 20; 30 |]
    use ptr = fixed arr
    let mutable flag = true
    let prev = toggleBoolAndBump (&flag, ptr, 1)
    prev |> equal true
    flag |> equal false
    arr.[1] |> equal 25

    let ro = ReadOnlySpan<int>(arr)
    sumNullArrAndSpan (Unchecked.defaultof<int[]>, ro, 3) |> equal 65

    optCallback (12, Unchecked.defaultof<IntFn>) |> equal -12
    optCallback (12, IntFn(fun x -> x + 5)) |> equal 17
    callCb6 (Del6(fun a b c d e f -> a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6)) |> equal 91

    callUcoStruct 2.0f 5.0f 4 |> equal 28.0f
#endif

// ---- Cross-platform (.NET + Fable-Zig) standard FFI parity tests ----

[<Struct; StructLayout(LayoutKind.Sequential)>]
type CrossVec3 =
    {
        x: float32
        y: float32
        z: float32
    }
    override this.ToString() = sprintf "(%.1f, %.1f, %.1f)" this.x this.y this.z

[<Struct; StructLayout(LayoutKind.Sequential, Pack = 2)>]
type CrossPack2 =
    val mutable a: byte
    val mutable b: int32

[<Struct; StructLayout(LayoutKind.Explicit)>]
type CrossUnion =
    [<FieldOffset(0)>]
    val mutable i: int32

    [<FieldOffset(0)>]
    val mutable f: float32

[<Struct; StructLayout(LayoutKind.Sequential)>]
type CrossLinkedNode =
    val mutable next: nativeptr<CrossLinkedNode>
    val mutable value: int32

type CrossAddDel = delegate of int -> int

[<Fact>]
let ``test StructLayout, Pack, Explicit union, node pointers, and NativePtr parity`` () =
    Marshal.SizeOf<CrossVec3>() |> equal 12
    Marshal.SizeOf<CrossPack2>() |> equal 6
    Marshal.OffsetOf<CrossPack2>("b") |> equal 2n

    let v = { x = 1.0f; y = 2.0f; z = 3.0f }
    v.ToString() |> equal "(1.0, 2.0, 3.0)"

    let mutable cu = CrossUnion()
    cu.f <- 2.0f
    cu.i |> equal 0x40000000

    let mutable tail = Unchecked.defaultof<CrossLinkedNode>
    tail.value <- 99
    let mutable head = Unchecked.defaultof<CrossLinkedNode>
    use pTail = fixed &tail
    head.next <- pTail
    head.value <- 11
    NativePtr.isNullPtr (NativePtr.nullPtr<CrossLinkedNode>) |> equal true
    NativePtr.isNullPtr head.next |> equal false
    (NativePtr.read head.next).value |> equal 99

    let buf = NativePtr.stackalloc<int> 5
    NativePtr.write buf 10
    NativePtr.set buf 1 20
    NativePtr.set buf 2 30
    let mid = NativePtr.add buf 2
    NativePtr.get mid -1 |> equal 20
    NativePtr.read buf |> equal 10
    let dst = NativePtr.stackalloc<int> 5
    NativePtr.copyBlock dst buf 3
    NativePtr.get dst 2 |> equal 30
    NativePtr.copy dst mid
    NativePtr.get dst 0 |> equal 30
    let bPtr = NativePtr.ofVoidPtr<byte> (NativePtr.toVoidPtr dst)
    NativePtr.initBlock bPtr 0x7Fuy 4u
    NativePtr.get dst 0 |> equal 0x7F7F7F7F
    NativePtr.clear dst
    NativePtr.get dst 0 |> equal 0
    NativePtr.toNativeInt (NativePtr.nullPtr<int>) |> equal 0n
    NativePtr.isNullPtr (NativePtr.ofNativeInt<int> 0n) |> equal true

[<Fact>]
let ``test IntPtr, UIntPtr, Marshal, NativeMemory, MemoryMarshal, Unsafe, fixed, and NativeLibrary`` () =
    IntPtr.Zero |> equal 0n
    UIntPtr.Zero |> equal 0un
    (IntPtr.Size = 4 || IntPtr.Size = 8) |> equal true
    let ip = IntPtr 100
    (IntPtr.Add(ip, 24)).ToInt32() |> equal 124
    (IntPtr.Subtract(ip, 10)).ToInt64() |> equal 90L
    let uip = UIntPtr 64u
    uip.ToUInt64() |> equal 64UL

    let mutable h = Marshal.AllocHGlobal 32
    try
        h <- Marshal.ReAllocHGlobal(h, 64n)
        Marshal.WriteByte(h, 0, 0xAAuy)
        Marshal.ReadByte(h, 0) |> equal 0xAAuy
        Marshal.WriteInt16(h, 2, -1234s)
        Marshal.ReadInt16(h, 2) |> equal -1234s
        Marshal.WriteInt32(h, 4, 0x12345678)
        Marshal.ReadInt32(h, 4) |> equal 0x12345678
        Marshal.WriteInt64(h, 16, 1234567890123L)
        Marshal.ReadInt64(h, 16) |> equal 1234567890123L
        Marshal.WriteIntPtr(h, 24, 777n)
        Marshal.ReadIntPtr(h, 24) |> equal 777n

        let sv: CrossVec3 = { x = 1.25f; y = -3.5f; z = 9.0f }
        Marshal.StructureToPtr(sv, h, false)
        Marshal.PtrToStructure<CrossVec3>(h) |> equal sv

        let srcArr = [| 10; 20; 30; 40 |]
        Marshal.Copy(srcArr, 1, h, 2)
        let dstArr = Array.zeroCreate<int> 4
        Marshal.Copy(h, dstArr, 1, 2)
        dstArr |> equal [| 0; 20; 30; 0 |]
    finally
        Marshal.FreeHGlobal h

    let pU8 = Marshal.StringToCoTaskMemUTF8 "Hello UTF8"
    Marshal.PtrToStringUTF8 pU8 |> equal "Hello UTF8"
    Marshal.PtrToStringUTF8(pU8, 5) |> equal "Hello"
    Marshal.ZeroFreeCoTaskMemUTF8 pU8

    let pAnsi = Marshal.StringToHGlobalAnsi "Hello Ansi"
    Marshal.PtrToStringAnsi pAnsi |> equal "Hello Ansi"
    Marshal.ZeroFreeGlobalAllocAnsi pAnsi

    let pU16 = Marshal.StringToHGlobalUni "Hi Uni"
    Marshal.PtrToStringUni pU16 |> equal "Hi Uni"
    Marshal.PtrToStringUni(pU16, 2) |> equal "Hi"
    Marshal.ZeroFreeGlobalAllocUnicode pU16

    let bias = 10
    let del = CrossAddDel(fun x -> x + bias)
    let fnPtr = Marshal.GetFunctionPointerForDelegate(del)
    let back = Marshal.GetDelegateForFunctionPointer<CrossAddDel>(fnPtr)
    back.Invoke(32) |> equal 42

    let nm = NativeMemory.AllocZeroed(32un)
    NativeMemory.Fill(nm, 8un, 5uy)
    let nm2 = NativeMemory.Alloc(32un)
    NativeMemory.Copy(nm, nm2, 16un)
    NativeMemory.Clear(nm, 32un)
    let np1 = NativePtr.ofVoidPtr<byte> nm
    let np2 = NativePtr.ofVoidPtr<byte> nm2
    NativePtr.read np1 |> equal 0uy
    NativePtr.get np2 7 |> equal 5uy
    NativePtr.get np2 8 |> equal 0uy
    NativeMemory.Free nm
    NativeMemory.Free nm2

    let al = NativeMemory.AlignedAlloc(24un, 64un)
    (UIntPtr(al).ToUInt64() % 64UL) |> equal 0UL
    NativePtr.write (NativePtr.ofVoidPtr<int> al) 4242
    let al2 = NativeMemory.AlignedRealloc(al, 128un, 128un)
    (UIntPtr(al2).ToUInt64() % 128UL) |> equal 0UL
    NativePtr.read (NativePtr.ofVoidPtr<int> al2) |> equal 4242
    NativeMemory.AlignedFree al2

    let ints = [| 0x04030201; 0x08070605 |]
    let sp = Span<int>(ints)
    let bytes = MemoryMarshal.Cast<int, byte>(sp)
    bytes.Length |> equal 8
    bytes.[0] |> equal 1uy
    let refData = &MemoryMarshal.GetArrayDataReference(ints)
    Unsafe.Add(&refData, 1) |> equal 0x08070605
    Unsafe.SizeOf<CrossVec3>() |> equal 12
    let pBytes = Unsafe.AsPointer(&MemoryMarshal.GetReference(bytes))
    Unsafe.WriteUnaligned<uint16>(NativePtr.toVoidPtr (NativePtr.add (NativePtr.ofVoidPtr<byte> pBytes) 1), 0xBEEFus)
    Unsafe.ReadUnaligned<uint16>(NativePtr.toVoidPtr (NativePtr.add (NativePtr.ofVoidPtr<byte> pBytes) 1)) |> equal 0xBEEFus

    use pArr = fixed ints
    use pElem = fixed &ints.[1]
    use pStr = fixed "XYZ"
    let mutable localVal = 77
    use pLocal = fixed &localVal
    let emptyArr: int[] = [||]
    use pEmpty = fixed emptyArr
    NativePtr.isNullPtr pEmpty |> equal true
    NativePtr.read pArr |> equal 0x04BEEF01
    NativePtr.read pElem |> equal 0x08070605
    int (NativePtr.read pStr) |> equal (int 'X')
    NativePtr.read pLocal |> equal 77

    try
        NativeLibrary.SetDllImportResolver(typeof<CrossVec3>.Assembly, DllImportResolver(fun _ _ _ -> 0n))
    with _ -> ()

    let mutable libHandle = 0n
    if NativeLibrary.TryLoad("libSystem.B.dylib", &libHandle) then
        let mutable absPtr = 0n
        NativeLibrary.TryGetExport(libHandle, "abs", &absPtr) |> equal true
        (absPtr <> 0n) |> equal true
        NativeLibrary.Free libHandle

