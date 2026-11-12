module Build.Quicktest.Zig

open Build.FableLibrary
open Build.Quicktest.Core

let handle (args: string list) =
    genericQuicktest
        {
            Language = "zig"
            FableLibBuilder = BuildFableLibraryZig()
            ProjectDir = "src/quicktest-zig"
            Extension = ".zig"
            RunMode = RunCommand "zig run QuickTest.zig"
        }
        args
