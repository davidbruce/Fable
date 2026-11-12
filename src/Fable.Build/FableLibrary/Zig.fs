namespace Build.FableLibrary

open System.IO

type BuildFableLibraryZig() =
    inherit
        BuildFableLibrary(
            "zig",
            Path.Combine("src", "fable-library-zig"),
            Path.Combine("src", "fable-library-zig"),
            Path.Combine("temp", "fable-library-zig"),
            Path.Combine("temp", "fable-library-zig"),
            [
                Path.Combine("src", "fable-library-zig", "**", "*.zig")
                Path.Combine("src", "fable-library-zig", "**", "*.fs")
            ]
        )

    override this.CopyStage() =
        // The hand-written part of the runtime sits next to the part compiled from F#.
        for zigFile in Directory.GetFiles(this.SourceDir, "*.zig") do
            File.Copy(zigFile, Path.Combine(this.OutDir, Path.GetFileName(zigFile)), overwrite = true)
