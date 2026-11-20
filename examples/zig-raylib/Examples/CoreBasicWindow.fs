module RaylibExamples.Examples.CoreBasicWindow

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - basic window")
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawText("Congrats! You created your first window!", 190, 200, 20, Colors.LightGray)
        Native.EndDrawing()

    Native.CloseWindow()
