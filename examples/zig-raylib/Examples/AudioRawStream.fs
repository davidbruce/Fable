module RaylibExamples.Examples.AudioRawStream

open System
open Microsoft.FSharp.NativeInterop
open RaylibExamples.Raylib

#nowarn "9"

let fillSineWave (buf: int16[]) (frequency: float32) (sampleRate: int) (startIdx: float32) : float32 =
    let mutable idx = startIdx
    let incr = frequency / float32 sampleRate

    for i = 0 to buf.Length - 1 do
        buf[i] <- int16 (32000.0f * sin (2.0f * float32 Math.PI * idx))
        idx <- idx + incr

        if idx >= 1.0f then
            idx <- idx - 1.0f

    idx

let run () =
    let screenWidth = 800
    let screenHeight = 450
    let maxSamplesPerUpdate = 4096
    let mutable frequency = 440.0f
    let mutable sineIdx = 0.0f

    Native.InitWindow(screenWidth, screenHeight, "raylib [audio] example - raw audio streaming")
    Native.InitAudioDevice()
    Native.SetAudioStreamBufferSizeDefault(maxSamplesPerUpdate)

    let stream = Native.LoadAudioStream(44100u, 16u, 1u)
    Native.PlayAudioStream(stream)

    let writeBuf = Array.zeroCreate<int16> maxSamplesPerUpdate
    Native.SetTargetFPS(30)

    while not (Native.WindowShouldClose()) do
        if Native.IsMouseButtonDown(MouseButton.Left) then
            let mp = Native.GetMousePosition()
            frequency <- 40.0f + mp.y

        if Native.IsAudioStreamProcessed(stream) then
            sineIdx <- fillSineWave writeBuf frequency 44100 sineIdx
            use ptr = fixed writeBuf
            Native.UpdateAudioStream(stream, NativePtr.toVoidPtr ptr, maxSamplesPerUpdate)

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawText(sprintf "sine frequency: %.0f Hz (hold left mouse)" frequency, 20, 20, 20, Colors.DarkGray)

        for x = 0 to screenWidth - 1 do
            let sample = writeBuf[x * writeBuf.Length / screenWidth]
            let py = screenHeight / 2 + int (float32 sample / 32000.0f * 140.0f)
            Native.DrawPixel(x, py, Colors.Red)

        Native.EndDrawing()

    Native.UnloadAudioStream(stream)
    Native.CloseAudioDevice()
    Native.CloseWindow()
