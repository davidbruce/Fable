module RaylibExamples.Examples.ModelsGeometricShapes

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [models] example - geometric shapes")

    let camera: Camera3D =
        {
            position =
                {
                    x = 0.0f
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

    let torusModel = Native.LoadModelFromMesh(Native.GenMeshTorus(0.4f, 1.0f, 16, 32))
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.BeginMode3D(camera)

        Native.DrawCube(
            {
                x = -4.0f
                y = 0.0f
                z = 2.0f
            },
            2.0f,
            5.0f,
            2.0f,
            Colors.Red
        )

        Native.DrawCubeWires(
            {
                x = -4.0f
                y = 0.0f
                z = 2.0f
            },
            2.0f,
            5.0f,
            2.0f,
            Colors.Gold
        )

        Native.DrawSphere(
            {
                x = -1.0f
                y = 0.0f
                z = -2.0f
            },
            1.0f,
            Colors.Green
        )

        Native.DrawSphereWires(
            {
                x = 1.0f
                y = 0.0f
                z = 2.0f
            },
            2.0f,
            16,
            16,
            Colors.Lime
        )

        Native.DrawCylinder(
            {
                x = 4.0f
                y = 0.0f
                z = -2.0f
            },
            1.0f,
            2.0f,
            3.0f,
            12,
            Colors.SkyBlue
        )

        Native.DrawCylinderWires(
            {
                x = 4.0f
                y = 0.0f
                z = -2.0f
            },
            1.0f,
            2.0f,
            3.0f,
            12,
            Colors.DarkBlue
        )

        Native.DrawModel(
            torusModel,
            {
                x = 0.0f
                y = 1.5f
                z = 0.0f
            },
            1.0f,
            Colors.Orange
        )

        Native.DrawModelWires(
            torusModel,
            {
                x = 0.0f
                y = 1.5f
                z = 0.0f
            },
            1.02f,
            Colors.Brown
        )

        Native.DrawGrid(10, 1.0f)
        Native.EndMode3D()
        Native.DrawFPS(10, 10)
        Native.EndDrawing()

    Native.UnloadModel(torusModel)
    Native.CloseWindow()
