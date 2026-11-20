module RaylibExamples.Examples.ShapesBouncingBall

open RaylibExamples.Raylib

[<Struct>]
type BallState =
    {
        mutable Position: Vector2
        mutable Speed: Vector2
        Radius: float32
    }

let stepBall (screenW: int) (screenH: int) (state: BallState) : BallState =
    let mutable s = state
    let mutable pos = s.Position
    let mutable spd = s.Speed
    pos.x <- pos.x + spd.x
    pos.y <- pos.y + spd.y

    if pos.x >= float32 screenW - s.Radius || pos.x <= s.Radius then
        spd.x <- -spd.x

    if pos.y >= float32 screenH - s.Radius || pos.y <= s.Radius then
        spd.y <- -spd.y

    {
        Position = pos
        Speed = spd
        Radius = s.Radius
    }

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.SetConfigFlags(ConfigFlags.Msaa4xHint)
    Native.InitWindow(screenWidth, screenHeight, "raylib [shapes] example - bouncing ball")

    let mutable ball =
        {
            Position =
                {
                    x = float32 screenWidth / 2.0f
                    y = float32 screenHeight / 2.0f
                }
            Speed =
                {
                    x = 5.0f
                    y = 4.0f
                }
            Radius = 20.0f
        }

    let mutable pause = false
    let mutable framesCounter = 0
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if Native.IsKeyPressed(KeyboardKey.Space) then
            pause <- not pause

        if not pause then
            ball <- stepBall screenWidth screenHeight ball
        else
            framesCounter <- framesCounter + 1

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawCircleV(ball.Position, ball.Radius, Colors.Maroon)
        Native.DrawText("PRESS SPACE to PAUSE BALL MOVEMENT", 10, screenHeight - 25, 20, Colors.LightGray)

        if pause && ((framesCounter / 30) % 2 = 0) then
            Native.DrawText("PAUSED", 350, 200, 30, Colors.Gray)

        Native.DrawFPS(10, 10)
        Native.EndDrawing()

    Native.CloseWindow()
