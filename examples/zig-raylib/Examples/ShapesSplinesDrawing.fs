module RaylibExamples.Examples.ShapesSplinesDrawing

open RaylibExamples.Raylib

#nowarn "9"

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.SetConfigFlags(ConfigFlags.Msaa4xHint)
    Native.InitWindow(screenWidth, screenHeight, "raylib [shapes] example - splines drawing")

    let points: Vector2[] =
        [|
            {
                x = 50.0f
                y = 400.0f
            }
            {
                x = 160.0f
                y = 220.0f
            }
            {
                x = 340.0f
                y = 380.0f
            }
            {
                x = 520.0f
                y = 60.0f
            }
            {
                x = 710.0f
                y = 260.0f
            }
        |]

    let mutable splineType = 2
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if Native.IsKeyPressed(KeyboardKey.One) then
            splineType <- 0

        if Native.IsKeyPressed(KeyboardKey.Two) then
            splineType <- 1

        if Native.IsKeyPressed(KeyboardKey.Three) then
            splineType <- 2

        if Native.IsKeyPressed(KeyboardKey.Four) then
            splineType <- 3

        if Native.IsKeyPressed(KeyboardKey.Five) then
            splineType <- 4

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)

        use pts = fixed points

        match splineType with
        | 0 -> Native.DrawSplineLinear(pts, points.Length, 4.0f, Colors.Red)
        | 1 -> Native.DrawSplineBasis(pts, points.Length, 4.0f, Colors.Red)
        | 2 -> Native.DrawSplineCatmullRom(pts, points.Length, 4.0f, Colors.Red)
        | 3 -> Native.DrawSplineBezierQuadratic(pts, points.Length, 4.0f, Colors.Red)
        | _ -> Native.DrawSplineBezierCubic(pts, 4, 4.0f, Colors.Red)

        for p in points do
            Native.DrawCircleV(p, 6.0f, Colors.DarkBlue)

        Native.DrawText(
            "Keys 1-5 select spline (Linear, Basis, CatmullRom, BezQuad, BezCubic)",
            20,
            20,
            16,
            Colors.DarkGray
        )

        Native.EndDrawing()

    Native.CloseWindow()
