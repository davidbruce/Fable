module RaylibExamples.Examples.Core3DCameraFree

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - 3d camera free")

    let mutable camera: Camera3D =
        {
            position =
                {
                    x = 10.0f
                    y = 10.0f
                    z = 10.0f
                }
            target =
                {
                    x = 0.0f
                    y = 0.0f
                    z = 0.0f
                }
            up =
                {
                    x = 0.0f
                    y = 1.0f
                    z = 0.0f
                }
            fovy = 45.0f
            projection = CameraProjection.Perspective
        }

    let cubePosition: Vector3 =
        {
            x = 0.0f
            y = 0.0f
            z = 0.0f
        }

    Native.DisableCursor()
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.UpdateCamera(&camera, CameraMode.Free)

        if Native.IsKeyPressed(KeyboardKey.Z) then
            camera.target <-
                {
                    x = 0.0f
                    y = 0.0f
                    z = 0.0f
                }

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.BeginMode3D(camera)
        Native.DrawCube(cubePosition, 2.0f, 2.0f, 2.0f, Colors.Red)
        Native.DrawCubeWires(cubePosition, 2.0f, 2.0f, 2.0f, Colors.Maroon)
        Native.DrawGrid(10, 1.0f)
        Native.EndMode3D()
        Native.DrawRectangle(10, 10, 320, 93, Native.Fade(Colors.SkyBlue, 0.5f))
        Native.DrawRectangleLines(10, 10, 320, 93, Colors.Blue)
        Native.DrawText("Free camera default controls:", 20, 20, 10, Colors.Black)
        Native.DrawText("- Mouse Wheel to Zoom in-out", 40, 40, 10, Colors.DarkGray)
        Native.DrawText("- WASD / Mouse move to fly, Z reset target", 40, 60, 10, Colors.DarkGray)
        Native.EndDrawing()

    Native.CloseWindow()
