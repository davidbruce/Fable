module RaylibExamples.Examples.TexturesImageGeneration

open RaylibExamples.Raylib

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [textures] example - procedural images generation")

    let images =
        [|
            Native.GenImageGradientLinear(screenWidth, screenHeight, 0, Colors.Red, Colors.Blue)
            Native.GenImageGradientLinear(screenWidth, screenHeight, 45, Colors.Red, Colors.Blue)
            Native.GenImageGradientRadial(screenWidth, screenHeight, 0.0f, Colors.White, Colors.Black)
            Native.GenImageGradientSquare(screenWidth, screenHeight, 0.0f, Colors.White, Colors.Black)
            Native.GenImageChecked(screenWidth, screenHeight, 32, 32, Colors.Red, Colors.Blue)
            Native.GenImageWhiteNoise(screenWidth, screenHeight, 0.5f)
            Native.GenImagePerlinNoise(screenWidth, screenHeight, 50, 50, 4.0f)
            Native.GenImageCellular(screenWidth, screenHeight, 32)
        |]

    let textures = images |> Array.map Native.LoadTextureFromImage

    for img in images do
        Native.UnloadImage(img)

    let mutable currentTexture = 0
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        if
            Native.IsMouseButtonPressed(MouseButton.Left)
            || Native.IsKeyPressed(KeyboardKey.Right)
        then
            currentTexture <- (currentTexture + 1) % textures.Length

        Native.BeginDrawing()
        Native.ClearBackground(Colors.RayWhite)
        Native.DrawTexture(textures[currentTexture], 0, 0, Colors.White)
        Native.DrawRectangle(30, 400, 340, 30, Native.Fade(Colors.SkyBlue, 0.5f))
        Native.DrawRectangleLines(30, 400, 340, 30, Native.Fade(Colors.White, 0.5f))
        Native.DrawText("CLICK or RIGHT KEY to cycle textures", 40, 408, 14, Colors.DarkGray)
        Native.EndDrawing()

    for tex in textures do
        Native.UnloadTexture(tex)

    Native.CloseWindow()
