module RaylibExamples.Examples.TexturesRawData

open System.Runtime.InteropServices
open Microsoft.FSharp.NativeInterop
open RaylibExamples.Raylib

#nowarn "9"

let createCheckedRawImage (width: int) (height: int) : Image =
    let byteCount = width * height * Marshal.SizeOf<Color>()
    let raw = Native.MemAlloc(uint32 byteCount)
    let pixels = NativePtr.ofVoidPtr<Color> raw

    for y = 0 to height - 1 do
        for x = 0 to width - 1 do
            let c =
                if ((x / 32 + y / 32) % 2) = 0 then
                    Colors.Orange
                else
                    Colors.Gold

            NativePtr.set pixels (y * width + x) c

    {
        data = raw
        width = width
        height = height
        mipmaps = 1
        format = PixelFormat.UncompressedR8G8B8A8
    }

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [textures] example - texture from raw data")

    let checkedIm = createCheckedRawImage 480 320
    let checkedTex = Native.LoadTextureFromImage(checkedIm)
    Native.UnloadImage(checkedIm)
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)

        Native.DrawTexture(
            checkedTex,
            screenWidth / 2 - checkedTex.width / 2,
            screenHeight / 2 - checkedTex.height / 2,
            Colors.White
        )

        Native.DrawText("CHECKED TEXTURE GENERATED FROM RAW MEMORY", 160, 30, 20, Colors.Brown)
        Native.EndDrawing()

    Native.UnloadTexture(checkedTex)
    Native.CloseWindow()
