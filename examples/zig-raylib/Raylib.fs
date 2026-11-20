module RaylibExamples.Raylib

open System
open System.IO
open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop

#nowarn "9"

// ---------------------------------------------------------------------------------------------
// Structs (exact C ABI layouts matching raylib 6.2 raylib.h)
// ---------------------------------------------------------------------------------------------

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Vector2 =
    {
        mutable x: float32
        mutable y: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Vector3 =
    {
        mutable x: float32
        mutable y: float32
        mutable z: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Vector4 =
    {
        mutable x: float32
        mutable y: float32
        mutable z: float32
        mutable w: float32
    }

type Quaternion = Vector4

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Matrix =
    {
        mutable m0: float32
        mutable m4: float32
        mutable m8: float32
        mutable m12: float32
        mutable m1: float32
        mutable m5: float32
        mutable m9: float32
        mutable m13: float32
        mutable m2: float32
        mutable m6: float32
        mutable m10: float32
        mutable m14: float32
        mutable m3: float32
        mutable m7: float32
        mutable m11: float32
        mutable m15: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Color =
    {
        mutable r: byte
        mutable g: byte
        mutable b: byte
        mutable a: byte
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Rectangle =
    {
        mutable x: float32
        mutable y: float32
        mutable width: float32
        mutable height: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Image =
    {
        mutable data: voidptr
        mutable width: int
        mutable height: int
        mutable mipmaps: int
        mutable format: int
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Texture =
    {
        mutable id: uint32
        mutable width: int
        mutable height: int
        mutable mipmaps: int
        mutable format: int
    }

type Texture2D = Texture
type TextureCubemap = Texture

[<Struct; StructLayout(LayoutKind.Sequential)>]
type RenderTexture =
    {
        mutable id: uint32
        mutable texture: Texture
        mutable depth: Texture
    }

type RenderTexture2D = RenderTexture

[<Struct; StructLayout(LayoutKind.Sequential)>]
type NPatchInfo =
    {
        mutable source: Rectangle
        mutable left: int
        mutable top: int
        mutable right: int
        mutable bottom: int
        mutable layout: int
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type GlyphInfo =
    {
        mutable value: int
        mutable offsetX: int
        mutable offsetY: int
        mutable advanceX: int
        mutable image: Image
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Font =
    {
        mutable baseSize: int
        mutable glyphCount: int
        mutable glyphPadding: int
        mutable texture: Texture2D
        mutable recs: nativeptr<Rectangle>
        mutable glyphs: nativeptr<GlyphInfo>
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Camera3D =
    {
        mutable position: Vector3
        mutable target: Vector3
        mutable up: Vector3
        mutable fovy: float32
        mutable projection: int
    }

type Camera = Camera3D

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Camera2D =
    {
        mutable offset: Vector2
        mutable target: Vector2
        mutable rotation: float32
        mutable zoom: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Mesh =
    {
        mutable vertexCount: int
        mutable triangleCount: int
        mutable vertices: nativeptr<float32>
        mutable texcoords: nativeptr<float32>
        mutable texcoords2: nativeptr<float32>
        mutable normals: nativeptr<float32>
        mutable tangents: nativeptr<float32>
        mutable colors: nativeptr<byte>
        mutable indices: nativeptr<uint16>
        mutable boneCount: int
        mutable boneIndices: nativeptr<byte>
        mutable boneWeights: nativeptr<float32>
        mutable animVertices: nativeptr<float32>
        mutable animNormals: nativeptr<float32>
        mutable vaoId: uint32
        mutable vboId: nativeptr<uint32>
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Shader =
    {
        mutable id: uint32
        mutable locs: nativeptr<int>
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type MaterialMap =
    {
        mutable texture: Texture2D
        mutable color: Color
        mutable value: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Float4 =
    {
        mutable v0: float32
        mutable v1: float32
        mutable v2: float32
        mutable v3: float32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Int4 =
    {
        mutable v0: int
        mutable v1: int
        mutable v2: int
        mutable v3: int
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Name32 =
    val mutable b0: byte
    val mutable b1: byte
    val mutable b2: byte
    val mutable b3: byte
    val mutable b4: byte
    val mutable b5: byte
    val mutable b6: byte
    val mutable b7: byte
    val mutable b8: byte
    val mutable b9: byte
    val mutable b10: byte
    val mutable b11: byte
    val mutable b12: byte
    val mutable b13: byte
    val mutable b14: byte
    val mutable b15: byte
    val mutable b16: byte
    val mutable b17: byte
    val mutable b18: byte
    val mutable b19: byte
    val mutable b20: byte
    val mutable b21: byte
    val mutable b22: byte
    val mutable b23: byte
    val mutable b24: byte
    val mutable b25: byte
    val mutable b26: byte
    val mutable b27: byte
    val mutable b28: byte
    val mutable b29: byte
    val mutable b30: byte
    val mutable b31: byte

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Material =
    {
        mutable shader: Shader
        mutable maps: nativeptr<MaterialMap>
        mutable params_: Float4
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Transform =
    {
        mutable translation: Vector3
        mutable rotation: Quaternion
        mutable scale: Vector3
    }

type ModelAnimPose = nativeptr<Transform>

[<Struct; StructLayout(LayoutKind.Sequential)>]
type BoneInfo =
    val mutable name: Name32
    val mutable parent: int

[<Struct; StructLayout(LayoutKind.Sequential)>]
type ModelSkeleton =
    {
        mutable boneCount: uint32
        mutable bones: nativeptr<BoneInfo>
        mutable bindPose: ModelAnimPose
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Model =
    {
        mutable transform: Matrix
        mutable meshCount: int
        mutable materialCount: int
        mutable meshes: nativeptr<Mesh>
        mutable materials: nativeptr<Material>
        mutable meshMaterial: nativeptr<int>
        mutable skeleton: ModelSkeleton
        mutable currentPose: ModelAnimPose
        mutable boneMatrices: nativeptr<Matrix>
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Ray =
    {
        mutable position: Vector3
        mutable direction: Vector3
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type RayCollision =
    val mutable hit: byte
    val mutable distance: float32
    val mutable point: Vector3
    val mutable normal: Vector3
    member this.Hit = this.hit <> 0uy

[<Struct; StructLayout(LayoutKind.Sequential)>]
type BoundingBox =
    {
        mutable min: Vector3
        mutable max: Vector3
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Wave =
    {
        mutable frameCount: uint32
        mutable sampleRate: uint32
        mutable sampleSize: uint32
        mutable channels: uint32
        mutable data: voidptr
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type AudioStream =
    {
        mutable buffer: voidptr
        mutable processor: voidptr
        mutable sampleRate: uint32
        mutable sampleSize: uint32
        mutable channels: uint32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Sound =
    {
        mutable stream: AudioStream
        mutable frameCount: uint32
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type Music =
    val mutable stream: AudioStream
    val mutable frameCount: uint32
    val mutable looping: byte
    val mutable ctxType: int
    val mutable ctxData: voidptr
    member this.Looping = this.looping <> 0uy

// ---------------------------------------------------------------------------------------------
// Standard Colors
// ---------------------------------------------------------------------------------------------

module Colors =
    let LightGray =
        {
            r = 200uy
            g = 200uy
            b = 200uy
            a = 255uy
        }

    let Gray =
        {
            r = 130uy
            g = 130uy
            b = 130uy
            a = 255uy
        }

    let DarkGray =
        {
            r = 80uy
            g = 80uy
            b = 80uy
            a = 255uy
        }

    let Yellow =
        {
            r = 253uy
            g = 249uy
            b = 0uy
            a = 255uy
        }

    let Gold =
        {
            r = 255uy
            g = 203uy
            b = 0uy
            a = 255uy
        }

    let Orange =
        {
            r = 255uy
            g = 161uy
            b = 0uy
            a = 255uy
        }

    let Pink =
        {
            r = 255uy
            g = 109uy
            b = 194uy
            a = 255uy
        }

    let Red =
        {
            r = 230uy
            g = 41uy
            b = 55uy
            a = 255uy
        }

    let Maroon =
        {
            r = 190uy
            g = 33uy
            b = 55uy
            a = 255uy
        }

    let Green =
        {
            r = 0uy
            g = 228uy
            b = 48uy
            a = 255uy
        }

    let Lime =
        {
            r = 0uy
            g = 158uy
            b = 47uy
            a = 255uy
        }

    let DarkGreen =
        {
            r = 0uy
            g = 117uy
            b = 44uy
            a = 255uy
        }

    let SkyBlue =
        {
            r = 102uy
            g = 191uy
            b = 255uy
            a = 255uy
        }

    let Blue =
        {
            r = 0uy
            g = 121uy
            b = 241uy
            a = 255uy
        }

    let DarkBlue =
        {
            r = 0uy
            g = 82uy
            b = 172uy
            a = 255uy
        }

    let Purple =
        {
            r = 200uy
            g = 122uy
            b = 255uy
            a = 255uy
        }

    let Violet =
        {
            r = 135uy
            g = 60uy
            b = 190uy
            a = 255uy
        }

    let DarkPurple =
        {
            r = 112uy
            g = 31uy
            b = 126uy
            a = 255uy
        }

    let Beige =
        {
            r = 211uy
            g = 176uy
            b = 131uy
            a = 255uy
        }

    let Brown =
        {
            r = 127uy
            g = 106uy
            b = 79uy
            a = 255uy
        }

    let DarkBrown =
        {
            r = 76uy
            g = 63uy
            b = 47uy
            a = 255uy
        }

    let White =
        {
            r = 255uy
            g = 255uy
            b = 255uy
            a = 255uy
        }

    let Black =
        {
            r = 0uy
            g = 0uy
            b = 0uy
            a = 255uy
        }

    let Blank =
        {
            r = 0uy
            g = 0uy
            b = 0uy
            a = 0uy
        }

    let Magenta =
        {
            r = 255uy
            g = 0uy
            b = 255uy
            a = 255uy
        }

    let RayWhite =
        {
            r = 245uy
            g = 245uy
            b = 245uy
            a = 255uy
        }

// ---------------------------------------------------------------------------------------------
// Enums & Constants
// ---------------------------------------------------------------------------------------------

module ConfigFlags =
    let VsyncHint = 0x00000040u
    let FullscreenMode = 0x00000002u
    let WindowResizable = 0x00000004u
    let WindowUndecorated = 0x00000008u
    let WindowHidden = 0x00000080u
    let WindowHighDpi = 0x00002000u
    let Msaa4xHint = 0x00000020u

module TraceLogLevel =
    let All = 0
    let Trace = 1
    let Debug = 2
    let Info = 3
    let Warning = 4
    let Error = 5
    let Fatal = 6
    let None = 7

module KeyboardKey =
    let Null = 0
    let Space = 32
    let A = 65
    let B = 66
    let C = 67
    let D = 68
    let E = 69
    let G = 71
    let H = 72
    let L = 76
    let M = 77
    let N = 78
    let P = 80
    let R = 82
    let S = 83
    let T = 84
    let W = 87
    let Z = 90
    let Zero = 48
    let One = 49
    let Two = 50
    let Three = 51
    let Four = 52
    let Five = 53
    let Escape = 256
    let Enter = 257
    let Tab = 258
    let Right = 262
    let Left = 263
    let Down = 264
    let Up = 265

module MouseButton =
    let Left = 0
    let Right = 1
    let Middle = 2

module CameraMode =
    let Custom = 0
    let Free = 1
    let Orbital = 2
    let FirstPerson = 3
    let ThirdPerson = 4

module CameraProjection =
    let Perspective = 0
    let Orthographic = 1

module PixelFormat =
    let UncompressedGrayscale = 1
    let UncompressedGrayAlpha = 2
    let UncompressedR5G6B5 = 3
    let UncompressedR8G8B8 = 4
    let UncompressedR8G8B8A8 = 7

module ShaderUniformDataType =
    let Float = 0
    let Vec2 = 1
    let Vec3 = 2
    let Vec4 = 3
    let Int = 4

// ---------------------------------------------------------------------------------------------
// Callback delegates
// ---------------------------------------------------------------------------------------------

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type TraceLogCallback = delegate of int * string * voidptr -> unit

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type LoadFileDataCallback = delegate of string * nativeptr<int> -> nativeptr<byte>

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type SaveFileDataCallback = delegate of string * voidptr * int -> byte

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type LoadFileTextCallback = delegate of string -> voidptr

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type SaveFileTextCallback = delegate of string * string -> byte

[<UnmanagedFunctionPointer(CallingConvention.Cdecl)>]
type AudioCallback = delegate of voidptr * uint32 -> unit

// ---------------------------------------------------------------------------------------------
// .NET DllImportResolver (ignored in Fable-Zig, which links libraylib via build.zig)
// ---------------------------------------------------------------------------------------------

let mutable private resolverInstalled = false

let private resolveRaylib () =
    if not resolverInstalled then
        resolverInstalled <- true

        try
            NativeLibrary.SetDllImportResolver(
                typeof<Vector2>.Assembly,
                DllImportResolver(fun name _ searchPath ->
                    if name <> "raylib" then
                        0n
                    else
                        let candidates =
                            [|
                                "/opt/homebrew/Cellar/raylib/6.2/lib/libraylib.dylib"
                                "/opt/homebrew/lib/libraylib.dylib"
                                "/usr/local/lib/libraylib.dylib"
                                "libraylib.dylib"
                                "libraylib.so"
                                "raylib.dll"
                            |]

                        let mutable loaded = 0n

                        for path in candidates do
                            if loaded = 0n then
                                let ok =
                                    if Path.IsPathRooted(path) then
                                        File.Exists(path) && NativeLibrary.TryLoad(path, &loaded)
                                    else
                                        NativeLibrary.TryLoad(path, typeof<Vector2>.Assembly, searchPath, &loaded)

                                if not ok then
                                    loaded <- 0n

                        loaded
                )
            )
        with _ ->
            ()

do resolveRaylib ()

let ensureInit () = resolveRaylib ()

// ---------------------------------------------------------------------------------------------
// P/Invoke declarations for raylib 6.2
// ---------------------------------------------------------------------------------------------

module Native =
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void InitWindow(int width, int height, string title)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void CloseWindow()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool WindowShouldClose()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsWindowReady()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetConfigFlags(uint32 flags)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetScreenWidth()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetScreenHeight()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetTargetFPS(int fps)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern float32 GetFrameTime()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern double GetTime()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetFPS()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ShowCursor()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DisableCursor()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EnableCursor()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ClearBackground(Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void BeginDrawing()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EndDrawing()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void BeginMode2D(Camera2D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EndMode2D()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void BeginMode3D(Camera3D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EndMode3D()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void BeginShaderMode(Shader shader)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EndShaderMode()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Ray GetScreenToWorldRay(Vector2 position, Camera3D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetWorldToScreen(Vector3 position, Camera3D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetWorldToScreen2D(Vector2 position, Camera2D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetScreenToWorld2D(Vector2 position, Camera2D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Matrix GetCameraMatrix(Camera3D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Matrix GetCameraMatrix2D(Camera2D camera)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetTraceLogLevel(int logLevel)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void TraceLog(int logLevel, string text)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetTraceLogCallback(TraceLogCallback callback)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetLoadFileTextCallback(LoadFileTextCallback callback)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetSaveFileTextCallback(SaveFileTextCallback callback)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern voidptr MemAlloc(uint32 size)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void MemFree(voidptr ptr)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* LoadFileText(string fileName)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadFileText(byte* text)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool SaveFileText(string fileName, string text)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* CompressData(byte* data, int dataSize, int& compDataSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* DecompressData(byte* compData, int compDataSize, int& dataSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* EncodeDataBase64(byte* data, int dataSize, int& outputSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* DecodeDataBase64(string text, int& outputSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern uint32 ComputeCRC32(byte* data, int dataSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetRandomSeed(uint32 seed)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetRandomValue(int min, int max)

    // Input
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsKeyPressed(int key)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsKeyDown(int key)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetExitKey(int key)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsMouseButtonPressed(int button)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsMouseButtonDown(int button)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetMouseX()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetMouseY()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetMousePosition()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetMouseDelta()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern float32 GetMouseWheelMove()

    // Camera
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UpdateCamera(Camera3D& camera, int mode)

    // Shapes & splines
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawPixel(int posX, int posY, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawLine(int startPosX, int startPosY, int endPosX, int endPosY, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawLineV(Vector2 startPos, Vector2 endPos, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawLineEx(Vector2 startPos, Vector2 endPos, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawTriangle(Vector2 v1, Vector2 v2, Vector2 v3, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawRectangle(int posX, int posY, int width, int height, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawRectangleRec(Rectangle rect, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawRectangleLines(int posX, int posY, int width, int height, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawRectangleLinesEx(Rectangle rect, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCircle(int centerX, int centerY, float32 radius, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCircleV(Vector2 center, float32 radius, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCircleLines(int centerX, int centerY, float32 radius, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSplineLinear(Vector2* points, int pointCount, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSplineBasis(Vector2* points, int pointCount, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSplineCatmullRom(Vector2* points, int pointCount, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSplineBezierQuadratic(Vector2* points, int pointCount, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSplineBezierCubic(Vector2* points, int pointCount, float32 thick, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetSplinePointLinear(Vector2 startPos, Vector2 endPos, float32 t)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetSplinePointBasis(Vector2 p1, Vector2 p2, Vector2 p3, Vector2 p4, float32 t)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetSplinePointCatmullRom(Vector2 p1, Vector2 p2, Vector2 p3, Vector2 p4, float32 t)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetSplinePointBezierQuadratic(Vector2 p1, Vector2 c2, Vector2 p3, float32 t)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 GetSplinePointBezierCubic(Vector2 p1, Vector2 c2, Vector2 c3, Vector2 p4, float32 t)

    // 2D Collisions
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool CheckCollisionRecs(Rectangle rec1, Rectangle rec2)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool CheckCollisionCircles(Vector2 center1, float32 radius1, Vector2 center2, float32 radius2)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool CheckCollisionCircleRec(Vector2 center, float32 radius, Rectangle rect)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool CheckCollisionPointRec(Vector2 point, Rectangle rect)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool CheckCollisionPointPoly(Vector2 point, Vector2* points, int pointCount)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Rectangle GetCollisionRec(Rectangle rec1, Rectangle rec2)

    // Images & Textures
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image LoadImageFromMemory(string fileType, byte* fileData, int dataSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsImageValid(Image image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadImage(Image image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern byte* ExportImageToMemory(Image image, string fileType, int& fileSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageColor(int width, int height, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageGradientLinear(int width, int height, int direction, Color start, Color endColor)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageGradientRadial(int width, int height, float32 density, Color inner, Color outer)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageGradientSquare(int width, int height, float32 density, Color inner, Color outer)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageChecked(int width, int height, int checksX, int checksY, Color col1, Color col2)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageWhiteNoise(int width, int height, float32 factor)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImagePerlinNoise(int width, int height, int offsetX, int offsetY, float32 scale)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image GenImageCellular(int width, int height, int tileSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Image ImageCopy(Image image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageCrop(Image& image, Rectangle crop)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageResize(Image& image, int newWidth, int newHeight)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageFlipVertical(Image& image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageDrawPixel(Image& dst, int posX, int posY, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageDrawRectangle(Image& dst, int posX, int posY, int width, int height, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageDrawCircle(Image& dst, int centerX, int centerY, int radius, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void ImageDrawText(Image& dst, string text, int posX, int posY, int fontSize, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color* LoadImageColors(Image image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadImageColors(Color* colors)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color GetImageColor(Image image, int x, int y)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Texture2D LoadTextureFromImage(Image image)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern RenderTexture2D LoadRenderTexture(int width, int height)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadTexture(Texture2D texture)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadRenderTexture(RenderTexture2D target)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void BeginTextureMode(RenderTexture2D target)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void EndTextureMode()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawTexture(Texture2D texture, int posX, int posY, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawTextureEx(Texture2D texture, Vector2 position, float32 rotation, float32 scale, Color tint)

    // Color ops
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool ColorIsEqual(Color col1, Color col2)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color Fade(Color color, float32 alpha)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int ColorToInt(Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector3 ColorToHSV(Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color ColorFromHSV(float32 hue, float32 saturation, float32 value)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color ColorTint(Color color, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color ColorAlpha(Color color, float32 alpha)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color ColorAlphaBlend(Color dst, Color src, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Color GetColor(uint32 hexValue)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetPixelDataSize(int width, int height, int format)

    // Shaders
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Shader LoadShaderFromMemory(string vsCode, string fsCode)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsShaderValid(Shader shader)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int GetShaderLocation(Shader shader, string uniformName)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetShaderValue(Shader shader, int locIndex, voidptr value, int uniformType)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadShader(Shader shader)

    // Text & Font
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Font GetFontDefault()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawFPS(int posX, int posY)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawText(string text, int posX, int posY, int fontSize, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawTextEx(Font font, string text, Vector2 position, float32 fontSize, float32 spacing, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawTextCodepoint(Font font, int codepoint, Vector2 position, float32 fontSize, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern int MeasureText(string text, int fontSize)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Vector2 MeasureTextEx(Font font, string text, float32 fontSize, float32 spacing)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern uint32 TextLength(string text)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool TextIsEqual(string text1, string text2)

    // 3D Shapes, Models & Collisions
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawLine3D(Vector3 startPos, Vector3 endPos, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCube(Vector3 position, float32 width, float32 height, float32 length, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCubeWires(Vector3 position, float32 width, float32 height, float32 length, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSphere(Vector3 centerPos, float32 radius, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawSphereWires(Vector3 centerPos, float32 radius, int rings, int slices, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCylinder(
        Vector3 position,
        float32 radiusTop,
        float32 radiusBottom,
        float32 height,
        int sides,
        Color color
    )

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawCylinderWires(
        Vector3 position,
        float32 radiusTop,
        float32 radiusBottom,
        float32 height,
        int sides,
        Color color
    )

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawRay(Ray ray, Color color)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawGrid(int slices, float32 spacing)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Model LoadModelFromMesh(Mesh mesh)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsModelValid(Model model)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadModel(Model model)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawModel(Model model, Vector3 position, float32 scale, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void DrawModelWires(Model model, Vector3 position, float32 scale, Color tint)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Mesh GenMeshCube(float32 width, float32 height, float32 length)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Mesh GenMeshSphere(float32 radius, int rings, int slices)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Mesh GenMeshTorus(float32 radius, float32 size, int radSeg, int sides)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern Mesh GenMeshKnot(float32 radius, float32 size, int radSeg, int sides)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern RayCollision GetRayCollisionSphere(Ray ray, Vector3 center, float32 radius)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern RayCollision GetRayCollisionBox(Ray ray, BoundingBox box)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern RayCollision GetRayCollisionTriangle(Ray ray, Vector3 p1, Vector3 p2, Vector3 p3)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern RayCollision GetRayCollisionQuad(Ray ray, Vector3 p1, Vector3 p2, Vector3 p3, Vector3 p4)

    // Audio
    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void InitAudioDevice()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void CloseAudioDevice()

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern AudioStream LoadAudioStream(uint32 sampleRate, uint32 sampleSize, uint32 channels)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UnloadAudioStream(AudioStream stream)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void UpdateAudioStream(AudioStream stream, voidptr data, int frameCount)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    [<return: MarshalAs(UnmanagedType.I1)>]
    extern bool IsAudioStreamProcessed(AudioStream stream)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void PlayAudioStream(AudioStream stream)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetAudioStreamBufferSizeDefault(int size)

    [<DllImport("raylib", CallingConvention = CallingConvention.Cdecl)>]
    extern void SetAudioStreamCallback(AudioStream stream, AudioCallback callback)
