module RaylibExamples.Benchmarks

open System
open System.Diagnostics
open Microsoft.FSharp.NativeInterop
open RaylibExamples.Raylib
open RaylibExamples.Raymath

#nowarn "9"

let private benchSaveDelegate =
    SaveFileTextCallback(fun fileName text ->
        if isNull fileName || isNull text then
            0uy
        else
            1uy
    )

let private runBench (name: string) (iters: int) (warmupIters: int) (body: int -> int64) =
    let mutable warm = 0L

    for _ = 1 to 40 do
        warm <- (warm * 1315423911L) ^^^ body warmupIters

    warm <- warm ^^^ body iters

    if warm = 0L && Stopwatch.GetTimestamp() < 0L then
        printfn ""

    let freq = float Stopwatch.Frequency
    let nsPerOpRuns = Array.zeroCreate<float> 5
    let totalMsRuns = Array.zeroCreate<float> 5
    let mutable chk = 0L

    for r = 0 to 4 do
        let t0 = Stopwatch.GetTimestamp()
        let res = body iters
        let t1 = Stopwatch.GetTimestamp()
        chk <- res
        let elapsedTicks = float (t1 - t0)
        totalMsRuns[r] <- elapsedTicks * 1_000.0 / freq
        nsPerOpRuns[r] <- elapsedTicks * 1_000_000_000.0 / (freq * float iters)

    Array.sortInPlace nsPerOpRuns
    Array.sortInPlace totalMsRuns
    let minNs = nsPerOpRuns[0]
    let medNs = nsPerOpRuns[2]
    let medMs = totalMsRuns[2]

    printfn
        "%-20s iters=%8d median=%8.2f ns/op  min=%8.2f ns/op  total=%7.2f ms  chk=%d"
        name
        iters
        medNs
        minNs
        medMs
        chk

let private benchPrim (n: int) : int64 =
    let mutable acc = 0L

    for i = 0 to n - 1 do
        acc <-
            acc
            + int64 (Native.GetPixelDataSize(64 + (i &&& 63), 64, PixelFormat.UncompressedR8G8B8A8))

    acc

let private benchStructSmall (n: int) : int64 =
    let mutable dst = Colors.Blue

    let mutable src: Color =
        {
            r = 200uy
            g = 100uy
            b = 50uy
            a = 128uy
        }

    let tint = Colors.White
    let mutable acc = 0L

    for i = 0 to n - 1 do
        src.r <- byte (i &&& 255)
        let res = Native.ColorAlphaBlend(dst, src, tint)
        dst <- res
        acc <- acc + int64 res.r + int64 res.g + int64 res.b + int64 res.a

    acc

let private benchStructLarge (n: int) : int64 =
    let mutable ray: Ray =
        {
            position =
                {
                    x = 0.0f
                    y = 0.0f
                    z = 10.0f
                }
            direction =
                {
                    x = 0.0f
                    y = 0.0f
                    z = -1.0f
                }
        }

    let box: BoundingBox =
        {
            min =
                {
                    x = -2.0f
                    y = -2.0f
                    z = -2.0f
                }
            max =
                {
                    x = 2.0f
                    y = 2.0f
                    z = 2.0f
                }
        }

    let mutable acc = 0L

    for i = 0 to n - 1 do
        ray.position.x <- float32 (i &&& 7) * 0.25f - 0.75f
        let hit = Native.GetRayCollisionBox(ray, box)

        acc <-
            acc
            + (if hit.Hit then
                   1L
               else
                   0L)
            + int64 (hit.distance * 100.0f)

    acc

let private benchSpline (n: int) : int64 =
    let p0: Vector2 =
        {
            x = 0.0f
            y = 0.0f
        }

    let p1: Vector2 =
        {
            x = 100.0f
            y = 200.0f
        }

    let p2: Vector2 =
        {
            x = 200.0f
            y = 200.0f
        }

    let p3: Vector2 =
        {
            x = 300.0f
            y = 0.0f
        }

    let mutable acc = 0L

    for i = 0 to n - 1 do
        let pt =
            Native.GetSplinePointCatmullRom(p0, p1, p2, p3, float32 (i &&& 255) / 255.0f)

        acc <- acc + int64 (pt.x + pt.y)

    acc

let private makeBenchPoly () : Vector2[] =
    [|
        {
            x = 40.0f
            y = 10.0f
        }
        {
            x = 80.0f
            y = 10.0f
        }
        {
            x = 110.0f
            y = 40.0f
        }
        {
            x = 110.0f
            y = 80.0f
        }
        {
            x = 80.0f
            y = 110.0f
        }
        {
            x = 40.0f
            y = 110.0f
        }
        {
            x = 10.0f
            y = 80.0f
        }
        {
            x = 10.0f
            y = 40.0f
        }
    |]

let private benchPtrHoisted (n: int) : int64 =
    let poly = makeBenchPoly ()
    let len = poly.Length
    let mutable acc = 0L
    use pPoly = fixed poly

    for i = 0 to n - 1 do
        let pt: Vector2 =
            {
                x = float32 (i &&& 127)
                y = float32 ((i >>> 7) &&& 127)
            }

        if Native.CheckCollisionPointPoly(pt, pPoly, len) then
            acc <- acc + 1L

    acc

let private benchPtrPerCall (n: int) : int64 =
    let poly = makeBenchPoly ()
    let len = poly.Length
    let mutable acc = 0L

    for i = 0 to n - 1 do
        let pt: Vector2 =
            {
                x = float32 (i &&& 127)
                y = float32 ((i >>> 7) &&& 127)
            }

        use pPoly = fixed poly

        if Native.CheckCollisionPointPoly(pt, pPoly, len) then
            acc <- acc + 1L

    acc

let private benchByrefImage (n: int) : int64 =
    let mutable img = Native.GenImageColor(256, 256, Colors.Black)

    try
        let mutable color: Color =
            {
                r = 0uy
                g = 0uy
                b = 0uy
                a = 255uy
            }

        for i = 0 to n - 1 do
            color.r <- byte (i &&& 255)
            color.g <- byte ((i >>> 4) &&& 255)
            color.b <- byte ((i >>> 8) &&& 255)
            Native.ImageDrawPixel(&img, i &&& 255, (i >>> 8) &&& 255, color)

        int64 (Native.ColorToInt(Native.GetImageColor(img, 123, 45)))
    finally
        Native.UnloadImage(img)

let private shortStrings =
    [|
        "raylib_short_string_0001"
        "raylib_short_string_0002"
        "raylib_short_string_0003"
        "raylib_short_string_0004"
    |]

let private longStrings =
    [|
        "raylib_long_ascii_string_benchmark_payload_exceeding_the_stack_buffer_threshold_in_fable_ffi_c_string_conversion_0000001"
        "raylib_long_ascii_string_benchmark_payload_exceeding_the_stack_buffer_threshold_in_fable_ffi_c_string_conversion_0000002"
        "raylib_long_ascii_string_benchmark_payload_exceeding_the_stack_buffer_threshold_in_fable_ffi_c_string_conversion_0000003"
        "raylib_long_ascii_string_benchmark_payload_exceeding_the_stack_buffer_threshold_in_fable_ffi_c_string_conversion_0000004"
    |]

let private benchStringShort (n: int) : int64 =
    let mutable acc = 0L

    for i = 0 to n - 1 do
        acc <- acc + int64 (Native.TextLength(shortStrings[i &&& 3]))

    acc

let private benchStringLong (n: int) : int64 =
    let mutable acc = 0L

    for i = 0 to n - 1 do
        acc <- acc + int64 (Native.TextLength(longStrings[i &&& 3]))

    acc

let private benchCallback (n: int) : int64 =
    Native.SetTraceLogLevel(TraceLogLevel.None)
    Native.SetSaveFileTextCallback(benchSaveDelegate)

    try
        let mutable acc = 0L

        for _ = 0 to n - 1 do
            if Native.SaveFileText("k", "v") then
                acc <- acc + 1L

        acc
    finally
        Native.SetSaveFileTextCallback(null)
        Native.SetTraceLogLevel(TraceLogLevel.Info)

let private benchPureFSharpMath (n: int) : int64 =
    let runtimeZero =
        if Stopwatch.GetTimestamp() < 0L then
            1
        else
            0

    let count = n + runtimeZero
    let rot = Raymath.matrixRotateY (0.001f + float32 runtimeZero)

    let mutable v: Vector3 =
        {
            x = 1.0f + float32 runtimeZero
            y = 0.5f
            z = 0.25f
        }

    let mutable acc = 0L

    for _ = 0 to count - 1 do
        v <- Raymath.vector3Transform v rot

        if v.x > 0.0f then
            acc <- acc + 1L

    acc

let runAll () =
    runBench "ffi_prim" 5_000_000 1_000 benchPrim
    runBench "ffi_struct_small" 2_000_000 1_000 benchStructSmall
    runBench "ffi_struct_large" 2_000_000 1_000 benchStructLarge
    runBench "ffi_spline" 2_000_000 1_000 benchSpline
    runBench "ffi_ptr_hoisted" 2_000_000 1_000 benchPtrHoisted
    runBench "ffi_ptr_per_call" 2_000_000 1_000 benchPtrPerCall
    runBench "ffi_byref_image" 5_000_000 1_000 benchByrefImage
    runBench "ffi_string_short" 2_000_000 1_000 benchStringShort
    runBench "ffi_string_long" 1_000_000 1_000 benchStringLong
    runBench "ffi_callback" 500_000 500 benchCallback
    runBench "pure_fsharp_math" 5_000_000 1_000 benchPureFSharpMath
