module RaylibExamples.Examples.Core2DCamera

open RaylibExamples.Raylib

let updateCamera2D (cam: Camera2D) (playerX: float32) (rotDelta: float32) (wheel: float32) : Camera2D =
    let mutable c = cam

    c.target <-
        {
            x = playerX + 20.0f
            y = 280.0f + 20.0f
        }

    c.rotation <- max -40.0f (min 40.0f (c.rotation + rotDelta))
    let z = exp (log c.zoom + wheel * 0.1f)
    c.zoom <- max 0.1f (min 3.0f z)
    c

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - 2d camera")

    let maxBuildings = 100
    let buildings = Array.zeroCreate<Rectangle> maxBuildings
    let buildColors = Array.zeroCreate<Color> maxBuildings
    let mutable spacing = 0.0f
    Native.SetRandomSeed(42u)

    for i = 0 to maxBuildings - 1 do
        let w = float32 (Native.GetRandomValue(50, 200))
        let h = float32 (Native.GetRandomValue(100, 800))

        buildings[i] <-
            {
                x = -6000.0f + spacing
                y = float32 screenHeight - 130.0f - h
                width = w
                height = h
            }

        spacing <- spacing + w

        buildColors[i] <-
            {
                r = byte (Native.GetRandomValue(200, 240))
                g = byte (Native.GetRandomValue(200, 240))
                b = byte (Native.GetRandomValue(200, 250))
                a = 255uy
            }

    let mutable player: Rectangle =
        {
            x = 400.0f
            y = 280.0f
            width = 40.0f
            height = 40.0f
        }

    let mutable camera: Camera2D =
        {
            offset =
                {
                    x = float32 screenWidth / 2.0f
                    y = float32 screenHeight / 2.0f
                }
            target =
                {
                    x = player.x + 20.0f
                    y = player.y + 20.0f
                }
            rotation = 0.0f
            zoom = 1.0f
        }

    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if Native.IsKeyDown(KeyboardKey.Right) then
            player.x <- player.x + 2.0f
        elif Native.IsKeyDown(KeyboardKey.Left) then
            player.x <- player.x - 2.0f

        let rotDelta =
            if Native.IsKeyDown(KeyboardKey.A) then
                -1.0f
            elif Native.IsKeyDown(KeyboardKey.S) then
                1.0f
            else
                0.0f

        camera <- updateCamera2D camera player.x rotDelta (Native.GetMouseWheelMove())

        if Native.IsKeyPressed(KeyboardKey.R) then
            camera.zoom <- 1.0f
            camera.rotation <- 0.0f

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.BeginMode2D(camera)
        Native.DrawRectangle(-6000, 320, 13000, 8000, Colors.DarkGray)

        for i = 0 to maxBuildings - 1 do
            Native.DrawRectangleRec(buildings[i], buildColors[i])

        Native.DrawRectangleRec(player, Colors.Red)
        Native.DrawLine(int camera.target.x, -screenHeight * 10, int camera.target.x, screenHeight * 10, Colors.Green)
        Native.DrawLine(-screenWidth * 10, int camera.target.y, screenWidth * 10, int camera.target.y, Colors.Green)
        Native.EndMode2D()
        Native.DrawText("SCREEN AREA", 640, 10, 20, Colors.Red)
        Native.DrawRectangleLines(0, 0, screenWidth, screenHeight, Colors.Red)

        Native.DrawText(
            "Free 2d camera controls: Left/Right move, A/S rotate, Wheel zoom, R reset",
            20,
            20,
            10,
            Colors.DarkGray
        )

        Native.EndDrawing()

    Native.CloseWindow()
