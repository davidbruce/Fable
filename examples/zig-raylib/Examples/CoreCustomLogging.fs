module RaylibExamples.Examples.CoreCustomLogging

open System
open RaylibExamples.Raylib

let private logEntries = ResizeArray<string>()

let private onLog (logLevel: int) (text: string) (_args: voidptr) =
    let tag =
        match logLevel with
        | l when l = TraceLogLevel.Trace -> "TRACE"
        | l when l = TraceLogLevel.Debug -> "DEBUG"
        | l when l = TraceLogLevel.Info -> "INFO"
        | l when l = TraceLogLevel.Warning -> "WARN"
        | l when l = TraceLogLevel.Error -> "ERROR"
        | _ -> "LOG"

    let msg =
        if isNull text then
            ""
        else
            text

    logEntries.Add(sprintf "[%s] %s" tag msg)

let private logDelegate = TraceLogCallback(onLog)

let captureLogs (messages: (int * string) list) : string array =
    logEntries.Clear()
    Native.SetTraceLogLevel(TraceLogLevel.All)
    Native.SetTraceLogCallback(logDelegate)

    try
        for lvl, msg in messages do
            Native.TraceLog(lvl, msg)

        logEntries.ToArray()
    finally
        Native.SetTraceLogCallback(null)
        Native.SetTraceLogLevel(TraceLogLevel.Info)
        logEntries.Clear()

let run () =
    logEntries.Clear()
    Native.SetTraceLogLevel(TraceLogLevel.All)
    Native.SetTraceLogCallback(logDelegate)

    try
        let screenWidth = 800
        let screenHeight = 450
        Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - custom logging")
        Native.TraceLog(TraceLogLevel.Info, "Fable Raylib custom logger attached")
        Native.TraceLog(TraceLogLevel.Warning, "Press L to emit another custom trace message")
        Native.SetTargetFPS(60)

        while not (Native.WindowShouldClose()) do
            if Native.IsKeyPressed(KeyboardKey.L) then
                Native.TraceLog(TraceLogLevel.Debug, "User pressed L key")

            Native.BeginDrawing()
            Native.ClearBackground(Colors.RayWhite)
            Native.DrawText("Custom TraceLogCallback output (press L):", 20, 20, 20, Colors.Maroon)
            let startIdx = max 0 (logEntries.Count - 14)

            for i = startIdx to logEntries.Count - 1 do
                Native.DrawText(logEntries[i], 20, 56 + (i - startIdx) * 24, 16, Colors.DarkGray)

            Native.EndDrawing()

        Native.CloseWindow()
    finally
        Native.SetTraceLogCallback(null)
        logEntries.Clear()
