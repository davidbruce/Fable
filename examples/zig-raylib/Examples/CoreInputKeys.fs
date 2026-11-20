module RaylibExamples.Examples.CoreInputKeys

open RaylibExamples.Raylib

let stepPosition (pos: Vector2) (right: bool) (left: bool) (up: bool) (down: bool) : Vector2 =
    let mutable p = pos

    if right then
        p.x <- p.x + 2.0f

    if left then
        p.x <- p.x - 2.0f

    if up then
        p.y <- p.y - 2.0f

    if down then
        p.y <- p.y + 2.0f

    p

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - keyboard input")

    let mutable ballPosition: Vector2 =
        {
            x = float32 screenWidth / 2.0f
            y = float32 screenHeight / 2.0f
        }

    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        ballPosition <-
            stepPosition
                ballPosition
                (Native.IsKeyDown(KeyboardKey.Right))
                (Native.IsKeyDown(KeyboardKey.Left))
                (Native.IsKeyDown(KeyboardKey.Up))
                (Native.IsKeyDown(KeyboardKey.Down))

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawText("move the ball with arrow keys", 10, 10, 20, Colors.DarkGray)
        Native.DrawCircleV(ballPosition, 50.0f, Colors.Maroon)
        Native.EndDrawing()

    Native.CloseWindow()
