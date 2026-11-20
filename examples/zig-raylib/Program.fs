module RaylibExamples.Program

open RaylibExamples.Examples

let private examples: (string * string * (unit -> unit)) list =
    [
        "core_basic_window", "Basic empty window with text", CoreBasicWindow.run
        "core_input_keys", "Move circle with keyboard arrows", CoreInputKeys.run
        "core_input_mouse", "Move circle and change color with mouse", CoreInputMouse.run
        "core_2d_camera", "2D platformer camera with zoom and rotation", Core2DCamera.run
        "core_3d_camera_free", "3D free-fly camera mode", Core3DCameraFree.run
        "core_3d_picking", "3D mouse ray picking against bounding box", Core3DPicking.run
        "core_custom_logging", "Custom TraceLogCallback capture", CoreCustomLogging.run
        "shapes_bouncing_ball", "Animated bouncing ball with pause", ShapesBouncingBall.run
        "shapes_collision_area", "2D box collision detection and overlap area", ShapesCollisionArea.run
        "shapes_splines_drawing", "Interactive 2D spline curves via fixed pointer", ShapesSplinesDrawing.run
        "textures_image_generation", "Procedural CPU image generators to GPU textures", TexturesImageGeneration.run
        "textures_image_drawing", "CPU software drawing on Image&", TexturesImageDrawing.run
        "textures_raw_data", "Create texture from MemAlloc RGBA buffer", TexturesRawData.run
        "text_font_loading", "Default font measurement and glyph drawing", TextFontLoading.run
        "models_geometric_shapes", "3D geometric primitives and generated torus model", ModelsGeometricShapes.run
        "shaders_julia_set", "GPU fragment shader Julia set with uniforms", ShadersJuliaSet.run
        "audio_raw_stream", "Real-time raw PCM sine synthesizer audio stream", AudioRawStream.run
    ]

let private printUsage () =
    printfn "Usage: raylib_examples [--verify | --bench | --list | <example_name>]"
    printfn ""
    printfn "Available Raylib 6.2 examples (%d total):" examples.Length

    for name, desc, _ in examples do
        printfn "  %-28s %s" name desc

[<EntryPoint>]
let main argv =
    Raylib.ensureInit ()

    match argv with
    | [| "--verify" |] ->
        HeadlessParity.runAll ()
        0
    | [| "--bench" |] ->
        Benchmarks.runAll ()
        0
    | [| "--list" |]
    | [||] ->
        printUsage ()
        0
    | [| name |] ->
        match examples |> List.tryFind (fun (n, _, _) -> n = name) with
        | Some(_, _, runFn) ->
            runFn ()
            0
        | None ->
            eprintfn "Unknown example: %s" name
            printUsage ()
            1
    | _ ->
        printUsage ()
        1
