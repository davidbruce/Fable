module RaylibExamples.Examples.ShapesCollisionArea

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [shapes] example - collision area")

    let mutable boxA: Rectangle =
        {
            x = 10.0f
            y = float32 screenHeight / 2.0f - 50.0f
            width = 200.0f
            height = 100.0f
        }

    let mutable boxASpeedX = 4.0f

    let mutable boxB: Rectangle =
        {
            x = float32 screenWidth / 2.0f - 30.0f
            y = float32 screenHeight / 2.0f - 30.0f
            width = 60.0f
            height = 60.0f
        }

    let screenUpperLimit = 40
    let mutable pause = false
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if not pause then
            boxA.x <- boxA.x + boxASpeedX

        if (boxA.x + boxA.width) >= float32 screenWidth || boxA.x <= 0.0f then
            boxASpeedX <- -boxASpeedX

        boxB.x <- float32 (Native.GetMouseX()) - boxB.width / 2.0f
        boxB.y <- float32 (Native.GetMouseY()) - boxB.height / 2.0f

        if boxB.x + boxB.width >= float32 screenWidth then
            boxB.x <- float32 screenWidth - boxB.width
        elif boxB.x <= 0.0f then
            boxB.x <- 0.0f

        if boxB.y + boxB.height >= float32 screenHeight then
            boxB.y <- float32 screenHeight - boxB.height
        elif boxB.y <= float32 screenUpperLimit then
            boxB.y <- float32 screenUpperLimit

        let collision = Native.CheckCollisionRecs(boxA, boxB)

        let boxCollision =
            if collision then
                Native.GetCollisionRec(boxA, boxB)
            else
                {
                    x = 0.0f
                    y = 0.0f
                    width = 0.0f
                    height = 0.0f
                }

        if Native.IsKeyPressed(KeyboardKey.Space) then
            pause <- not pause

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)

        Native.DrawRectangle(
            0,
            0,
            screenWidth,
            screenUpperLimit,
            if collision then
                Colors.Red
            else
                Colors.Black
        )

        Native.DrawRectangleRec(boxA, Colors.Gold)
        Native.DrawRectangleRec(boxB, Colors.Blue)

        if collision then
            Native.DrawRectangleRec(boxCollision, Colors.Lime)

            Native.DrawText(
                "COLLISION!",
                (screenWidth - Native.MeasureText("COLLISION!", 20)) / 2,
                screenUpperLimit / 2 - 10,
                20,
                Colors.Black
            )

            Native.DrawText(
                sprintf "Collision Area: %d" (int (boxCollision.width * boxCollision.height)),
                screenWidth / 2 - 100,
                screenUpperLimit + 10,
                20,
                Colors.Black
            )

        Native.DrawFPS(10, 10)
        Native.EndDrawing()

    Native.CloseWindow()
