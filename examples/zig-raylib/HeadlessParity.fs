module RaylibExamples.HeadlessParity

open System
open System.Collections.Generic
open System.Runtime.InteropServices
open System.Runtime.CompilerServices
open System.Text
open Microsoft.FSharp.NativeInterop
open RaylibExamples.Raylib
open RaylibExamples.Raymath
open RaylibExamples.Examples

#nowarn "9"

let private failCheck (msg: string) = failwithf "PARITY CHECK FAILED: %s" msg

let private assertTrue (label: string) (cond: bool) =
    if not cond then
        failCheck label

let private assertEqualInt (label: string) (expected: int) (actual: int) =
    if expected <> actual then
        failCheck (sprintf "%s: expected %d, got %d" label expected actual)

let private assertEqualU32 (label: string) (expected: uint32) (actual: uint32) =
    if expected <> actual then
        failCheck (sprintf "%s: expected %u, got %u" label expected actual)

let private assertEqualNative (label: string) (expected: nativeint) (actual: nativeint) =
    if expected <> actual then
        failCheck (sprintf "%s: expected %d, got %d" label (int64 expected) (int64 actual))

let private assertNear (label: string) (expected: float32) (actual: float32) =
    if abs (expected - actual) > 0.01f then
        failCheck (sprintf "%s: expected %.4f, got %.4f" label expected actual)

let private memStore = Dictionary<string, string>()

let private onSaveFileText (fileName: string) (text: string) : byte =
    if isNull fileName then
        0uy
    else
        memStore[fileName] <-
            if isNull text then
                ""
            else
                text

        1uy

let private onLoadFileText (fileName: string) : voidptr =
    if isNull fileName then
        NativePtr.toVoidPtr (NativePtr.nullPtr<byte>)
    else
        match memStore.TryGetValue(fileName) with
        | true, content ->
            let bytes = Encoding.UTF8.GetBytes(content)
            let p = Native.MemAlloc(uint32 (bytes.Length + 1))
            let bp = NativePtr.ofVoidPtr<byte> p

            for i = 0 to bytes.Length - 1 do
                NativePtr.set bp i bytes[i]

            NativePtr.set bp bytes.Length 0uy
            p
        | false, _ -> NativePtr.toVoidPtr (NativePtr.nullPtr<byte>)

let private saveTextDelegate = SaveFileTextCallback(onSaveFileText)
let private loadTextDelegate = LoadFileTextCallback(onLoadFileText)

let private checkStructLayouts () =
    assertEqualInt "sizeof Vector2" 8 (Marshal.SizeOf<Vector2>())
    assertEqualInt "sizeof Vector3" 12 (Marshal.SizeOf<Vector3>())
    assertEqualInt "sizeof Vector4" 16 (Marshal.SizeOf<Vector4>())
    assertEqualInt "sizeof Matrix" 64 (Marshal.SizeOf<Matrix>())
    assertEqualInt "sizeof Color" 4 (Marshal.SizeOf<Color>())
    assertEqualInt "sizeof Rectangle" 16 (Marshal.SizeOf<Rectangle>())
    assertEqualInt "sizeof Image" 24 (Marshal.SizeOf<Image>())
    assertEqualInt "sizeof Texture" 20 (Marshal.SizeOf<Texture>())
    assertEqualInt "sizeof RenderTexture" 44 (Marshal.SizeOf<RenderTexture>())
    assertEqualInt "sizeof NPatchInfo" 36 (Marshal.SizeOf<NPatchInfo>())
    assertEqualInt "sizeof GlyphInfo" 40 (Marshal.SizeOf<GlyphInfo>())
    assertEqualInt "sizeof Font" 48 (Marshal.SizeOf<Font>())
    assertEqualInt "sizeof Camera2D" 24 (Marshal.SizeOf<Camera2D>())
    assertEqualInt "sizeof Camera3D" 44 (Marshal.SizeOf<Camera3D>())
    assertEqualInt "sizeof Mesh" 120 (Marshal.SizeOf<Mesh>())
    assertEqualInt "sizeof Shader" 16 (Marshal.SizeOf<Shader>())
    assertEqualInt "sizeof MaterialMap" 28 (Marshal.SizeOf<MaterialMap>())
    assertEqualInt "sizeof Material" 40 (Marshal.SizeOf<Material>())
    assertEqualInt "sizeof Transform" 40 (Marshal.SizeOf<Transform>())
    assertEqualInt "sizeof BoneInfo" 36 (Marshal.SizeOf<BoneInfo>())
    assertEqualInt "sizeof ModelSkeleton" 24 (Marshal.SizeOf<ModelSkeleton>())
    assertEqualInt "sizeof Model" 136 (Marshal.SizeOf<Model>())
    assertEqualInt "sizeof Ray" 24 (Marshal.SizeOf<Ray>())
    assertEqualInt "sizeof RayCollision" 32 (Marshal.SizeOf<RayCollision>())
    assertEqualInt "sizeof BoundingBox" 24 (Marshal.SizeOf<BoundingBox>())
    assertEqualInt "sizeof Wave" 24 (Marshal.SizeOf<Wave>())
    assertEqualInt "sizeof AudioStream" 32 (Marshal.SizeOf<AudioStream>())
    assertEqualInt "sizeof Sound" 40 (Marshal.SizeOf<Sound>())
    assertEqualInt "sizeof Music" 56 (Marshal.SizeOf<Music>())

    assertEqualNative "offsetof RayCollision.distance" 4n (Marshal.OffsetOf<RayCollision>("distance"))
    assertEqualNative "offsetof RayCollision.point" 8n (Marshal.OffsetOf<RayCollision>("point"))
    assertEqualNative "offsetof RayCollision.normal" 20n (Marshal.OffsetOf<RayCollision>("normal"))
    assertEqualNative "offsetof BoneInfo.parent" 32n (Marshal.OffsetOf<BoneInfo>("parent"))
    assertEqualNative "offsetof Music.frameCount" 32n (Marshal.OffsetOf<Music>("frameCount"))
    assertEqualNative "offsetof Music.looping" 36n (Marshal.OffsetOf<Music>("looping"))
    assertEqualNative "offsetof Music.ctxType" 40n (Marshal.OffsetOf<Music>("ctxType"))
    assertEqualNative "offsetof Music.ctxData" 48n (Marshal.OffsetOf<Music>("ctxData"))

    printfn
        "structs: size(Model)=%d size(Mesh)=%d size(RayCollision)=%d size(Music)=%d"
        (Marshal.SizeOf<Model>())
        (Marshal.SizeOf<Mesh>())
        (Marshal.SizeOf<RayCollision>())
        (Marshal.SizeOf<Music>())

let private checkColors () =
    let redInt = Native.ColorToInt(Colors.Red)
    let redBack = Native.GetColor(uint32 redInt)
    assertTrue "ColorIsEqual Red" (Native.ColorIsEqual(Colors.Red, redBack))
    let hsv = Native.ColorToHSV(Colors.Orange)
    let blueFromHsv = Native.ColorFromHSV(240.0f, 1.0f, 1.0f)
    assertEqualInt "HSV Blue.b" 255 (int blueFromHsv.b)
    let tinted = Native.ColorTint(Colors.White, Colors.Gold)
    assertTrue "ColorTint White*Gold" (Native.ColorIsEqual(tinted, Colors.Gold))
    let alpha = Native.ColorAlpha(Colors.Red, 0.5f)
    let blended = Native.ColorAlphaBlend(Colors.Blue, alpha, Colors.White)
    let pds = Native.GetPixelDataSize(64, 64, PixelFormat.UncompressedR8G8B8A8)
    assertEqualInt "GetPixelDataSize 64x64 RGBA8" 16384 pds

    printfn
        "colors: red=0x%08X orangeH=%.2f blend=(%d,%d,%d,%d) dataBytes=%d"
        redInt
        hsv.x
        (int blended.r)
        (int blended.g)
        (int blended.b)
        (int blended.a)
        pds

let private checkCollisions2DAnd3D () =
    let r1: Rectangle =
        {
            x = 10.0f
            y = 10.0f
            width = 100.0f
            height = 50.0f
        }

    let r2: Rectangle =
        {
            x = 60.0f
            y = 30.0f
            width = 80.0f
            height = 40.0f
        }

    assertTrue "CheckCollisionRecs" (Native.CheckCollisionRecs(r1, r2))
    let overlap = Native.GetCollisionRec(r1, r2)
    assertNear "overlap.width" 50.0f overlap.width
    assertNear "overlap.height" 30.0f overlap.height

    assertTrue
        "CheckCollisionCircles hit"
        (Native.CheckCollisionCircles(
            {
                x = 0.0f
                y = 0.0f
            },
            10.0f,
            {
                x = 15.0f
                y = 0.0f
            },
            6.0f
        ))

    assertTrue
        "CheckCollisionCircles miss"
        (not (
            Native.CheckCollisionCircles(
                {
                    x = 0.0f
                    y = 0.0f
                },
                5.0f,
                {
                    x = 15.0f
                    y = 0.0f
                },
                5.0f
            )
        ))

    assertTrue
        "CheckCollisionCircleRec"
        (Native.CheckCollisionCircleRec(
            {
                x = 5.0f
                y = 15.0f
            },
            8.0f,
            r1
        ))

    assertTrue
        "CheckCollisionPointRec"
        (Native.CheckCollisionPointRec(
            {
                x = 50.0f
                y = 30.0f
            },
            r1
        ))

    let poly: Vector2[] =
        [|
            {
                x = 0.0f
                y = 0.0f
            }
            {
                x = 100.0f
                y = 0.0f
            }
            {
                x = 100.0f
                y = 100.0f
            }
            {
                x = 0.0f
                y = 100.0f
            }
        |]

    use pPoly = fixed poly

    assertTrue
        "CheckCollisionPointPoly in"
        (Native.CheckCollisionPointPoly(
            {
                x = 50.0f
                y = 50.0f
            },
            pPoly,
            poly.Length
        ))

    assertTrue
        "CheckCollisionPointPoly out"
        (not (
            Native.CheckCollisionPointPoly(
                {
                    x = 150.0f
                    y = 50.0f
                },
                pPoly,
                poly.Length
            )
        ))

    let ray: Ray =
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

    let sphereHit =
        Native.GetRayCollisionSphere(
            ray,
            {
                x = 0.0f
                y = 0.0f
                z = 0.0f
            },
            2.0f
        )

    assertTrue "GetRayCollisionSphere hit" sphereHit.Hit
    assertNear "GetRayCollisionSphere dist" 8.0f sphereHit.distance

    let box =
        Core3DPicking.cubeBounds
            {
                x = 0.0f
                y = 0.0f
                z = 0.0f
            }
            {
                x = 2.0f
                y = 2.0f
                z = 2.0f
            }

    let boxHit = Native.GetRayCollisionBox(ray, box)
    assertTrue "GetRayCollisionBox hit" boxHit.Hit
    assertNear "GetRayCollisionBox dist" 9.0f boxHit.distance

    let triHit =
        Native.GetRayCollisionTriangle(
            ray,
            {
                x = -5.0f
                y = -5.0f
                z = 0.0f
            },
            {
                x = 5.0f
                y = -5.0f
                z = 0.0f
            },
            {
                x = 0.0f
                y = 5.0f
                z = 0.0f
            }
        )

    assertTrue "GetRayCollisionTriangle hit" triHit.Hit
    assertNear "GetRayCollisionTriangle dist" 10.0f triHit.distance

    let quadHit =
        Native.GetRayCollisionQuad(
            ray,
            {
                x = -3.0f
                y = -3.0f
                z = 0.0f
            },
            {
                x = 3.0f
                y = -3.0f
                z = 0.0f
            },
            {
                x = 3.0f
                y = 3.0f
                z = 0.0f
            },
            {
                x = -3.0f
                y = 3.0f
                z = 0.0f
            }
        )

    assertTrue "GetRayCollisionQuad hit" quadHit.Hit
    assertNear "GetRayCollisionQuad dist" 10.0f quadHit.distance

    printfn
        "collisions: overlap=(%.1f,%.1f) sphere=%.2f box=%.2f tri=%.2f quad=%.2f"
        overlap.width
        overlap.height
        sphereHit.distance
        boxHit.distance
        triHit.distance
        quadHit.distance

let private checkSplines () =
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

    let sLin = Native.GetSplinePointLinear(p0, p3, 0.25f)
    let sBas = Native.GetSplinePointBasis(p0, p1, p2, p3, 0.5f)
    let sCat = Native.GetSplinePointCatmullRom(p0, p1, p2, p3, 0.5f)
    let sBq = Native.GetSplinePointBezierQuadratic(p0, p1, p3, 0.5f)
    let sBc = Native.GetSplinePointBezierCubic(p0, p1, p2, p3, 0.5f)

    assertNear "spline lin.x" 75.0f sLin.x

    printfn
        "splines: lin=(%.2f,%.2f) basis=(%.2f,%.2f) cat=(%.2f,%.2f) bq=(%.2f,%.2f) bc=(%.2f,%.2f)"
        sLin.x
        sLin.y
        sBas.x
        sBas.y
        sCat.x
        sCat.y
        sBq.x
        sBq.y
        sBc.x
        sBc.y

let private pixelChecksum (img: Image) : uint32 =
    let count = img.width * img.height
    let colors = Native.LoadImageColors(img)

    try
        let mutable acc = 0u

        for i = 0 to count - 1 do
            let c = NativePtr.get colors i
            acc <- acc + uint32 c.r * 3u + uint32 c.g * 5u + uint32 c.b * 7u + uint32 c.a * 11u

        acc
    finally
        Native.UnloadImageColors(colors)

let private checkImagesAndPngRoundtrip () =
    let solid = Native.GenImageColor(16, 16, Colors.SkyBlue)
    let grad = Native.GenImageGradientLinear(32, 32, 0, Colors.Red, Colors.Blue)
    let rad = Native.GenImageGradientRadial(32, 32, 0.2f, Colors.White, Colors.Black)
    let chk = Native.GenImageChecked(32, 32, 8, 8, Colors.Black, Colors.White)
    Native.SetRandomSeed(777u)
    let noise = Native.GenImageWhiteNoise(16, 16, 0.5f)
    let perlin = Native.GenImagePerlinNoise(32, 32, 10, 10, 2.0f)
    let cell = Native.GenImageCellular(32, 32, 8)
    let drawn = TexturesImageDrawing.buildComposedImage ()
    let rawImg = TexturesRawData.createCheckedRawImage 64 64

    try
        assertTrue "solid valid" (Native.IsImageValid(solid))
        let topCorner = Native.GetImageColor(solid, 3, 3)
        assertTrue "solid SkyBlue" (Native.ColorIsEqual(topCorner, Colors.SkyBlue))

        let mutable copy = Native.ImageCopy(drawn)

        try
            Native.ImageCrop(
                &copy,
                {
                    x = 0.0f
                    y = 0.0f
                    width = 128.0f
                    height = 128.0f
                }
            )

            Native.ImageResize(&copy, 64, 64)
            Native.ImageFlipVertical(&copy)
            assertEqualInt "copy width" 64 copy.width
            assertEqualInt "copy height" 64 copy.height

            let mutGradSum = pixelChecksum grad
            let drawnCorner = Native.GetImageColor(drawn, 30, 30)
            assertTrue "drawn Maroon box" (Native.ColorIsEqual(drawnCorner, Colors.Maroon))

            // Export to PNG memory & reload via LoadImageFromMemory
            let mutable pngSize = 0
            let pngPtr = Native.ExportImageToMemory(copy, ".png", &pngSize)
            assertTrue "ExportImageToMemory size > 0" (pngSize > 0 && not (NativePtr.isNullPtr pngPtr))

            let mutable reloaded =
                try
                    Native.LoadImageFromMemory(".png", pngPtr, pngSize)
                finally
                    Native.MemFree(NativePtr.toVoidPtr pngPtr)

            try
                assertTrue "reloaded valid" (Native.IsImageValid(reloaded))
                assertEqualInt "reloaded width" 64 reloaded.width
                assertEqualInt "reloaded height" 64 reloaded.height
                let copyCrc = pixelChecksum copy
                let reloadedCrc = pixelChecksum reloaded
                assertEqualU32 "PNG roundtrip checksum" copyCrc reloadedCrc

                let rawSum = pixelChecksum rawImg

                printfn
                    "images: gradSum=%u rawSum=%u cellW=%d perlinW=%d noiseW=%d radW=%d chkW=%d pngBytes=%d pngSum=%u"
                    mutGradSum
                    rawSum
                    cell.width
                    perlin.width
                    noise.width
                    rad.width
                    chk.width
                    pngSize
                    reloadedCrc
            finally
                Native.UnloadImage(reloaded)
        finally
            Native.UnloadImage(copy)
    finally
        Native.UnloadImage(solid)
        Native.UnloadImage(grad)
        Native.UnloadImage(rad)
        Native.UnloadImage(chk)
        Native.UnloadImage(noise)
        Native.UnloadImage(perlin)
        Native.UnloadImage(cell)
        Native.UnloadImage(drawn)
        Native.UnloadImage(rawImg)

let private checkCompressionAndMemoryFFI () =
    let payload = [| for i in 0..255 -> byte ((i * 7 + 13) % 64) |]
    use pPayload = fixed payload
    let crc = Native.ComputeCRC32(pPayload, payload.Length)

    let mutable compSize = 0
    let compPtr = Native.CompressData(pPayload, payload.Length, &compSize)
    assertTrue "CompressData non-null" (not (NativePtr.isNullPtr compPtr) && compSize > 0)

    let mutable decompSize = 0

    let decompPtr =
        try
            Native.DecompressData(compPtr, compSize, &decompSize)
        finally
            Native.MemFree(NativePtr.toVoidPtr compPtr)

    try
        assertEqualInt "DecompressData len" payload.Length decompSize

        for i = 0 to payload.Length - 1 do
            if NativePtr.get decompPtr i <> payload[i] then
                failCheck (sprintf "Decompress mismatch at %d" i)
    finally
        Native.MemFree(NativePtr.toVoidPtr decompPtr)

    let mutable b64Len = 0
    let b64Ptr = Native.EncodeDataBase64(pPayload, 16, &b64Len)

    let b64Text =
        try
            Marshal.PtrToStringUTF8(NativePtr.toNativeInt b64Ptr)
        finally
            Native.MemFree(NativePtr.toVoidPtr b64Ptr)

    let mutable decLen = 0
    let decPtr = Native.DecodeDataBase64(b64Text, &decLen)

    try
        assertEqualInt "DecodeDataBase64 len" 16 decLen

        for i = 0 to 15 do
            if NativePtr.get decPtr i <> payload[i] then
                failCheck (sprintf "Base64 mismatch at %d" i)
    finally
        Native.MemFree(NativePtr.toVoidPtr decPtr)

    // NativeMemory + Span/MemoryMarshal/Unsafe interop check
    let aligned = NativeMemory.AlignedAlloc(64un, 64un)

    try
        let asU32 = Span<uint32>(aligned, 4)
        asU32[0] <- 0x11223344u
        asU32[1] <- 0x55667788u
        let bytes = MemoryMarshal.AsBytes(asU32)
        let firstByte = Unsafe.Add(&MemoryMarshal.GetReference(bytes), 0)
        assertEqualInt "NativeMemory firstByte LE" 0x44 (int firstByte)
        printfn "memory: crc32=%u comp=%d decomp=%d b64=%s firstByte=0x%02X" crc compSize decompSize b64Text firstByte
    finally
        NativeMemory.AlignedFree(aligned)

let private checkCallbacks () =
    let logs =
        CoreCustomLogging.captureLogs
            [
                TraceLogLevel.Info, "Raylib 6.2 FFI check line one"
                TraceLogLevel.Warning, "Raylib 6.2 FFI check line two"
            ]

    assertEqualInt "captured logs count" 2 logs.Length

    assertEqualInt
        "log[0] prefix"
        0
        (if logs[0].Contains("FFI check line one") then
             0
         else
             1)

    memStore.Clear()
    Native.SetSaveFileTextCallback(saveTextDelegate)
    Native.SetLoadFileTextCallback(loadTextDelegate)

    let loadedText =
        try
            let saved = Native.SaveFileText("virtual://test.txt", "hello raylib 6.2 callback")
            assertTrue "SaveFileText virtual" saved
            let txtPtr = Native.LoadFileText("virtual://test.txt")
            assertTrue "LoadFileText non-null" (not (NativePtr.isNullPtr txtPtr))

            try
                Marshal.PtrToStringUTF8(NativePtr.toNativeInt txtPtr)
            finally
                Native.UnloadFileText(txtPtr)
        finally
            Native.SetSaveFileTextCallback(null)
            Native.SetLoadFileTextCallback(null)
            memStore.Clear()

    assertEqualInt "LoadFileText eq" 0 (String.CompareOrdinal("hello raylib 6.2 callback", loadedText))
    printfn "callbacks: logs=%d first=\"%s\" fileRoundtrip=\"%s\"" logs.Length logs[0] loadedText

let private checkRaymathAndSimulations () =
    let q = quaternionFromAxisAngle (vec3 0.0f 1.0f 0.0f) 90.0f
    let rotMat = quaternionToMatrix q
    let rotated = vector3Transform (vec3 1.0f 0.0f 0.0f) rotMat
    assertNear "rotated.z" -1.0f rotated.z

    let proj = matrixPerspective (float32 Math.PI / 4.0f) (16.0f / 9.0f) 0.1f 100.0f

    let view =
        matrixLookAt (vec3 0.0f 2.0f 5.0f) (vec3 0.0f 0.0f 0.0f) (vec3 0.0f 1.0f 0.0f)

    let mvp = matrixMultiply view proj

    let mutable ball: ShapesBouncingBall.BallState =
        {
            Position =
                {
                    x = 400.0f
                    y = 225.0f
                }
            Speed =
                {
                    x = 5.0f
                    y = 4.0f
                }
            Radius = 20.0f
        }

    for _ = 1 to 120 do
        ball <- ShapesBouncingBall.stepBall 800 450 ball

    let moved =
        CoreInputKeys.stepPosition
            {
                x = 400.0f
                y = 225.0f
            }
            true
            false
            false
            true

    let cam =
        Core2DCamera.updateCamera2D
            {
                offset = vec2 400.0f 225.0f
                target = vec2 0.0f 0.0f
                rotation = 0.0f
                zoom = 1.0f
            }
            450.0f
            2.0f
            1.0f

    let jIter = ShadersJuliaSet.juliaIterations 0.15f -0.25f -0.7f 0.27015f 64

    let pcm = Array.zeroCreate<int16> 128
    let endIdx = AudioRawStream.fillSineWave pcm 440.0f 44100 0.0f
    let mutPcmSum = pcm |> Array.sumBy int

    printfn
        "sim: rot=(%.2f,%.2f,%.2f) mvp0=%.3f ball=(%.1f,%.1f) moved=(%.1f,%.1f) camZ=%.3f julia=%d pcmSum=%d endIdx=%.4f"
        rotated.x
        rotated.y
        rotated.z
        mvp.m0
        ball.Position.x
        ball.Position.y
        moved.x
        moved.y
        cam.zoom
        jIter
        mutPcmSum
        endIdx

let runAll () =
    checkStructLayouts ()
    checkColors ()
    checkCollisions2DAnd3D ()
    checkSplines ()
    checkImagesAndPngRoundtrip ()
    checkCompressionAndMemoryFFI ()
    checkCallbacks ()
    checkRaymathAndSimulations ()
    printfn "ALL HEADLESS RAYLIB 6.2 PARITY CHECKS PASSED"
