module RaylibExamples.Examples.CoreInputMouse

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - mouse input")

    let mutable ballPosition: Vector2 =
        {
            x = -100.0f
            y = -100.0f
        }

    let mutable ballColor = Colors.DarkBlue
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        ballPosition <- Native.GetMousePosition()

        if Native.IsMouseButtonPressed(MouseButton.Left) then
            ballColor <- Colors.Maroon
        elif Native.IsMouseButtonPressed(MouseButton.Middle) then
            ballColor <- Colors.Lime
        elif Native.IsMouseButtonPressed(MouseButton.Right) then
            ballColor <- Colors.DarkBlue

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawCircleV(ballPosition, 40.0f, ballColor)
        Native.DrawText("move ball with mouse and click mouse button to change color", 10, 10, 20, Colors.DarkGray)
        Native.EndDrawing()

    Native.CloseWindow()
