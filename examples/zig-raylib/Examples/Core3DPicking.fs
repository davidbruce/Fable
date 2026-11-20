module RaylibExamples.Examples.Core3DPicking

open RaylibExamples.Raylib

let cubeBounds (pos: Vector3) (size: Vector3) : BoundingBox =
    {
        min =
            {
                x = pos.x - size.x / 2.0f
                y = pos.y - size.y / 2.0f
                z = pos.z - size.z / 2.0f
            }
        max =
            {
                x = pos.x + size.x / 2.0f
                y = pos.y + size.y / 2.0f
                z = pos.z + size.z / 2.0f
            }
    }

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [core] example - 3d picking")

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
            y = 1.0f
            z = 0.0f
        }

    let cubeSize: Vector3 =
        {
            x = 2.0f
            y = 2.0f
            z = 2.0f
        }

    let box = cubeBounds cubePosition cubeSize

    let mutable ray: Ray =
        {
            position =
                {
                    x = 0.0f
                    y = 0.0f
                    z = 0.0f
                }
            direction =
                {
                    x = 0.0f
                    y = 0.0f
                    z = 1.0f
                }
        }

    let mutable collision = Unchecked.defaultof<RayCollision>
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if Native.IsMouseButtonPressed(MouseButton.Left) then
            if not collision.Hit then
                ray <- Native.GetScreenToWorldRay(Native.GetMousePosition(), camera)
                collision <- Native.GetRayCollisionBox(ray, box)
            else
                collision <- Unchecked.defaultof<RayCollision>

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.BeginMode3D(camera)

        if collision.Hit then
            Native.DrawCube(cubePosition, cubeSize.x, cubeSize.y, cubeSize.z, Colors.Red)
            Native.DrawCubeWires(cubePosition, cubeSize.x, cubeSize.y, cubeSize.z, Colors.Maroon)
            Native.DrawCubeWires(cubePosition, cubeSize.x + 0.2f, cubeSize.y + 0.2f, cubeSize.z + 0.2f, Colors.Green)
        else
            Native.DrawCube(cubePosition, cubeSize.x, cubeSize.y, cubeSize.z, Colors.Gray)
            Native.DrawCubeWires(cubePosition, cubeSize.x, cubeSize.y, cubeSize.z, Colors.DarkGray)

        Native.DrawRay(ray, Colors.Maroon)
        Native.DrawGrid(10, 1.0f)
        Native.EndMode3D()
        Native.DrawText("Try clicking on the box with your mouse!", 240, 10, 20, Colors.DarkGray)

        if collision.Hit then
            Native.DrawText(
                "BOX SELECTED",
                (screenWidth - Native.MeasureText("BOX SELECTED", 30)) / 2,
                int (float32 screenHeight * 0.1f),
                30,
                Colors.Green
            )

        Native.DrawFPS(10, 10)
        Native.EndDrawing()

    Native.CloseWindow()
