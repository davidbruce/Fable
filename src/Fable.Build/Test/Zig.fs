module Build.Test.Zig

open Build.FableLibrary
open Build.Utils
open BlackFox.CommandLine
open SimpleExec

/// The Zig target's tests: the runtime library's own tests (`zig test`), then the
/// self-checking quicktest suite (`src/quicktest-zig`) compiled to Zig and run in Debug and in
/// ReleaseSafe (its exit code is the number of failed checks), and run on .NET as well, which
/// checks that what it expects is what .NET does.
let handle (args: string list) =
    let forceFableLibrary = args |> List.contains "--force-fable-library"
    let noDotnet = args |> List.contains "--no-dotnet"

    BuildFableLibraryZig().Run(forceFableLibrary)

    Command.Run("zig", "test fable_rt.zig", workingDirectory = Path.Resolve("src", "fable-library-zig"))

    let projectDir = Path.Resolve("src", "quicktest-zig")

    Command.Fable(
        CmdLine.empty
        |> CmdLine.appendRaw projectDir
        |> CmdLine.appendPrefix "--lang" "zig"
        |> CmdLine.appendPrefix "--extension" ".zig"
        |> CmdLine.appendPrefix "--exclude" "Fable.Core"
        |> CmdLine.appendRaw "--noCache",
        workingDirectory = projectDir
    )

    for mode in [ "Debug"; "ReleaseSafe" ] do
        Command.Run("zig", $"run -O %s{mode} QuickTest.zig", workingDirectory = projectDir)

    if not noDotnet then
        Command.Run("dotnet", "run", workingDirectory = projectDir)

    // tests/Zig: the tests the other targets share, ported; each `[<Fact>]` is a Zig `test`
    let testsDir = Path.Resolve("tests", "Zig")

    Command.Fable(
        CmdLine.empty
        |> CmdLine.appendRaw (Path.Resolve(testsDir, "Fable.Tests.Zig.fsproj"))
        |> CmdLine.appendPrefix "--lang" "zig"
        |> CmdLine.appendPrefix "--extension" ".zig"
        |> CmdLine.appendPrefix "--exclude" "Fable.Core"
        |> CmdLine.appendRaw "--noCache",
        workingDirectory = testsDir
    )

    Command.Fable(
        CmdLine.empty
        |> CmdLine.appendRaw (Path.Resolve(testsDir, "Fable.Tests.Zig.Nullness.fsproj"))
        |> CmdLine.appendPrefix "--lang" "zig"
        |> CmdLine.appendPrefix "--extension" ".zig"
        |> CmdLine.appendPrefix "--exclude" "Fable.Core"
        |> CmdLine.appendRaw "--noCache",
        workingDirectory = testsDir
    )

    for file in System.IO.Directory.GetFiles(testsDir, "*Tests.zig") |> Array.sort do
        let name = System.IO.Path.GetFileName file
        // (the tests of C functions, `[<DllImport>]`, link C's library; the others do not, as the
        // runtime takes C's allocator when it is linked)
        let libc =
            if name = "InteropTests.zig" then
                " -lc"
            else
                ""

        Command.Run("zig", $"test %s{name}%s{libc}", workingDirectory = testsDir)

    // (in Release: F# makes tail calls only there, and the tail-call tests recurse deeply)
    if not noDotnet then
        Command.Run("dotnet", "test -c Release Fable.Tests.Zig.fsproj", workingDirectory = testsDir)
        Command.Run("dotnet", "test -c Release Fable.Tests.Zig.Nullness.fsproj", workingDirectory = testsDir)
