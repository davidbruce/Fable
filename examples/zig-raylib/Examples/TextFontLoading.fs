module RaylibExamples.Examples.TextFontLoading

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [text] example - font loading")

    let font = Native.GetFontDefault()
    let message = "Standard F# + .NET 10 + Fable-Zig + Raylib 6.2!"
    let size = Native.MeasureTextEx(font, message, 24.0f, 2.0f)
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)

        let pos: Vector2 =
            {
                x = (float32 screenWidth - size.x) / 2.0f
                y = 180.0f
            }

        Native.DrawTextEx(font, message, pos, 24.0f, 2.0f, Colors.DarkBlue)
        Native.DrawText(sprintf "Measured width: %.1f height: %.1f" size.x size.y, 210, 230, 18, Colors.DarkGray)

        Native.DrawTextCodepoint(
            font,
            int 'R',
            {
                x = 385.0f
                y = 280.0f
            },
            48.0f,
            Colors.Maroon
        )

        Native.DrawFPS(10, 10)
        Native.EndDrawing()

    Native.CloseWindow()
