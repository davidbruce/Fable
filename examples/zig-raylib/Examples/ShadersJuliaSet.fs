module RaylibExamples.Examples.ShadersJuliaSet

open Microsoft.FSharp.NativeInterop
open RaylibExamples.Raylib

#nowarn "9"

let juliaIterations (zx0: float32) (zy0: float32) (cx: float32) (cy: float32) (maxIter: int) : int =
    let mutable zx = zx0
    let mutable zy = zy0
    let mutable iter = 0

    while iter < maxIter && (zx * zx + zy * zy) <= 4.0f do
        let xt = zx * zx - zy * zy + cx
        zy <- 2.0f * zx * zy + cy
        zx <- xt
        iter <- iter + 1

    iter

let private juliaFragmentShader =
    """#version 330
in vec2 fragTexCoord;
in vec4 fragColor;
uniform vec2 c;
uniform vec2 offset;
uniform float zoom;
out vec4 finalColor;
void main() {
    vec2 z = (fragTexCoord - vec2(0.5)) * (3.0 / zoom) + offset;
    int i = 0;
    for (int k = 0; k < 64; k++) {
        z = vec2(z.x * z.x - z.y * z.y, 2.0 * z.x * z.y) + c;
        if (dot(z, z) > 4.0) break;
        i++;
    }
    float t = float(i) / 64.0;
    finalColor = vec4(0.5 + 0.5 * cos(6.2831 * t + 0.0), 0.5 + 0.5 * cos(6.2831 * t + 2.1), 0.5 + 0.5 * cos(6.2831 * t + 4.2), 1.0);
}
"""

let run () =
    let screenWidth = 800
    let screenHeight = 450
    Native.InitWindow(screenWidth, screenHeight, "raylib [shaders] example - julia set")

    let shader = Native.LoadShaderFromMemory(null, juliaFragmentShader)
    let target = Native.LoadRenderTexture(screenWidth, screenHeight)
    let cLoc = Native.GetShaderLocation(shader, "c")
    let offLoc = Native.GetShaderLocation(shader, "offset")
    let zoomLoc = Native.GetShaderLocation(shader, "zoom")

    let cVals = [| -0.7f; 0.27015f |]
    let offVals = [| 0.0f; 0.0f |]
    let zoomVals = [| 1.0f |]
    let mutable angle = 0.0f
    Native.SetTargetFPS(60)

    while not (Native.WindowShouldClose()) do
        angle <- angle + Native.GetFrameTime() * 0.4f
        cVals[0] <- -0.7f + 0.1f * cos angle
        cVals[1] <- 0.27015f + 0.1f * sin angle

        use pC = fixed cVals
        use pOff = fixed offVals
        use pZoom = fixed zoomVals
        Native.SetShaderValue(shader, cLoc, NativePtr.toVoidPtr pC, ShaderUniformDataType.Vec2)
        Native.SetShaderValue(shader, offLoc, NativePtr.toVoidPtr pOff, ShaderUniformDataType.Vec2)
        Native.SetShaderValue(shader, zoomLoc, NativePtr.toVoidPtr pZoom, ShaderUniformDataType.Float)

        Native.BeginTextureMode(target)
        Native.ClearBackground(Colors.Black)
        Native.DrawRectangle(0, 0, screenWidth, screenHeight, Colors.White)
        Native.EndTextureMode()

        Native.BeginDrawing()
        Native.ClearBackground(Colors.Black)
        Native.BeginShaderMode(shader)
        Native.DrawTexture(target.texture, 0, 0, Colors.White)
        Native.EndShaderMode()
        Native.DrawText("Julia set shader", 20, 20, 20, Colors.RayWhite)
        Native.DrawFPS(screenWidth - 90, 10)
        Native.EndDrawing()

    Native.UnloadRenderTexture(target)
    Native.UnloadShader(shader)
    Native.CloseWindow()
