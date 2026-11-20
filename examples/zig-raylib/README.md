# Fable-Zig + .NET 10 Shared Raylib 6.2 Examples

This directory demonstrates **standard .NET 10 F# P/Invoke + FFI code** compiling and running **identically** on both:

- **.NET 10** (`dotnet run -- ...`)
- **Fable -> Zig (`0.17.1`)** linked against native `raylib` 6.2 (`zig build run -- ...`)

Zero `#if FABLE_COMPILER` / `#if FABLE_COMPILER_ZIG` conditionals and zero `Fable.Core` dependencies are used in any `.fs` file here.

## Included Raylib 6.2 Examples (17)

1. `core_basic_window` — Basic window creation and frame loop
2. `core_input_keys` — Keyboard movement (`IsKeyDown`)
3. `core_input_mouse` — Mouse tracking and button color switching
4. `core_2d_camera` — `Camera2D` world transform, zoom, and rotation
5. `core_3d_camera_free` — `Camera3D` via `UpdateCamera(&camera, CAMERA_FREE)` (`Camera3D&` byref)
6. `core_3d_picking` — `GetScreenToWorldRay` + `GetRayCollisionBox` (`RayCollision.Hit` byte-backed `_Bool`)
7. `core_custom_logging` — Custom `TraceLogCallback` delegate + `SetTraceLogCallback(null)` reset
8. `shapes_bouncing_ball` — Animated bouncing ball + frame pacing
9. `shapes_collision_area` — 2D `CheckCollisionRecs` / `GetCollisionRec` overlap box
10. `shapes_splines_drawing` — Interactive Linear/Basis/CatmullRom/Bezier splines (`fixed` `Vector2*`)
11. `textures_image_generation` — Procedural CPU `GenImage*` generators to GPU `Texture2D`
12. `textures_image_drawing` — CPU software image manipulation via `Image&`
13. `textures_raw_data` — `Raylib.MemAlloc` RGBA buffer with `NativePtr` -> `Image` -> `Texture2D`
14. `text_font_loading` — `GetFontDefault`, `MeasureTextEx`, `DrawTextEx`, `DrawTextCodepoint`
15. `models_geometric_shapes` — 3D geometry and `LoadModelFromMesh(GenMeshTorus(...))` (`ModelSkeleton` 6.2 ABI)
16. `shaders_julia_set` — Fragment shader `LoadShaderFromMemory` and `SetShaderValue` uniforms
17. `audio_raw_stream` — Procedural sine synthesizer streaming raw PCM `int16[]` via `fixed` pointer

## Quick Start

Verify byte-for-byte parity between `.NET 10`, `Fable-Zig` Debug, and `Fable-Zig` ReleaseFast via the headless `--verify` suite:

```bash
./run.sh
```

List or run any interactive GUI example:

```bash
dotnet run -c Release -- --list
dotnet run -c Release -- core_basic_window

# Or via Fable -> Zig:
zig build -Doptimize=ReleaseFast
./zig-out/bin/raylib_examples core_basic_window
# Or: zig build -Doptimize=ReleaseFast -Dexample=core_basic_window run
```
