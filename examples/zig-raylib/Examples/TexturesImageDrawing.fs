module RaylibExamples.Examples.TexturesImageDrawing

open RaylibExamples.Raylib

let buildComposedImage () : Image =
    let mutable canvas =
        Native.GenImageChecked(256, 256, 32, 32, Colors.LightGray, Colors.White)

    let mutable badge =
        Native.GenImageGradientLinear(128, 128, 45, Colors.SkyBlue, Colors.DarkBlue)

    Native.ImageCrop(
        &badge,
        {
            x = 16.0f
            y = 16.0f
            width = 96.0f
            height = 96.0f
        }
    )

    Native.ImageFlipVertical(&badge)
    Native.ImageResize(&badge, 112, 112)
    Native.UnloadImage(badge)
    Native.ImageDrawRectangle(&canvas, 20, 20, 120, 80, Colors.Maroon)
    Native.ImageDrawCircle(&canvas, 180, 160, 42, Colors.Gold)
    Native.ImageDrawPixel(&canvas, 128, 128, Colors.Green)
    Native.ImageDrawText(&canvas, "RAYLIB 6.2", 32, 220, 20, Colors.DarkBlue)
    canvas

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [textures] example - image drawing")

    let img = buildComposedImage ()
    let texture = Native.LoadTextureFromImage(img)
    Native.UnloadImage(img)
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)

        Native.DrawTexture(
            texture,
            screenWidth / 2 - texture.width / 2,
            screenHeight / 2 - texture.height / 2,
            Colors.White
        )

        Native.DrawText("Image drawn on CPU and uploaded as Texture2D", 190, 40, 20, Colors.DarkGray)
        Native.EndDrawing()

    Native.UnloadTexture(texture)
    Native.CloseWindow()
