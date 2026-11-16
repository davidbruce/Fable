module Fable.Tests.TestSystemIO

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<Fact>]
let ``test get random filename works`` () =
    let name = System.IO.Path.GetRandomFileName()
    name.Length
    |> equal 12

[<Fact>]
let ``test get temp path works`` () =
    let path = System.IO.Path.GetTempPath()
    path.Length > 0
    |> equal true

[<Fact>]
let ``test get temp file name works`` () =
    let name = System.IO.Path.GetTempFileName()
    name.Length > 0
    |> equal true

[<Fact>]
let ``test get file name works`` () =
    let name = System.IO.Path.GetFileName("temp/test.txt")
    name
    |> equal "test.txt"

[<Fact>]
let ``test get file name without extesion works`` () =
    let name = System.IO.Path.GetFileNameWithoutExtension("temp/test.txt")
    name
    |> equal "test"

[<Fact>]
let ``test get directory name works`` () =
    let name = System.IO.Path.GetDirectoryName("temp/test.txt")
    name
    |> equal "temp"

[<Fact>]
let ``test has extension works`` () =
    let hasExt = System.IO.Path.HasExtension("temp/test.txt")
    hasExt
    |> equal true
    let hasExt = System.IO.Path.HasExtension("temp/test")
    hasExt
    |> equal false

[<Fact>]
let ``test get extension works`` () =
    let ext = System.IO.Path.GetExtension("temp/test.txt")
    ext
    |> equal ".txt"

[<Fact>]
let ``test combine works`` () =
    let path = System.IO.Path.Combine("temp", "test.txt")
    System.IO.Path.GetFileName(path) |> equal "test.txt"
    System.IO.Path.GetDirectoryName(path) |> equal "temp"

[<Fact>]
let ``test combine with three parts works`` () =
    let path = System.IO.Path.Combine("temp", "sub", "test.txt")
    System.IO.Path.GetFileName(path) |> equal "test.txt"
    System.IO.Path.GetDirectoryName(path) |> equal (System.IO.Path.Combine("temp", "sub"))

[<Fact>]
let ``test get full path works`` () =
    let path = System.IO.Path.GetFullPath("temp/test.txt")
    path.Length > 0
    |> equal true

[<Fact>]
let ``test read all text works`` () =
    let file = System.IO.Path.GetTempFileName()
    System.IO.File.WriteAllText(file, "Hello World")
    let text = System.IO.File.ReadAllText(file)
    System.IO.File.Delete(file)

    text.Contains "Hello World"
    |> equal true

[<Fact>]
let ``test read all lines works`` () =
    let file = System.IO.Path.GetTempFileName()
    System.IO.File.WriteAllLines(file, [|"Hello"; "World"|])
    let lines = System.IO.File.ReadAllLines(file)
    System.IO.File.Delete(file)

    lines.Length
    |> equal 2
    lines = [|"Hello"; "World"|]
    |> equal true

[<Fact>]
let ``test file exists works`` () =
    let file = System.IO.Path.GetTempFileName()
    System.IO.File.Exists(file)
    |> equal true
    System.IO.File.Delete(file)
    System.IO.File.Exists(file)
    |> equal false

[<Fact>]
let ``test directory exists works`` () =
    System.IO.Directory.Exists(System.IO.Path.GetTempPath())
    |> equal true

[<Fact>]
let ``test directory exists returns false for non-existing directory`` () =
    let dir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), System.IO.Path.GetRandomFileName())

    System.IO.Directory.Exists(dir)
    |> equal false

[<Fact>]
let ``test directory exists returns false for a file path`` () =
    let file = System.IO.Path.GetTempFileName()
    System.IO.Directory.Exists(file)
    |> equal false
    System.IO.File.Delete(file)

[<Fact>]
let ``test create directory creates missing parent directories`` () =
    let baseDir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), System.IO.Path.GetRandomFileName())

    let nested = System.IO.Path.Combine(baseDir, "a", "b", "c")

    System.IO.Directory.Exists(nested)
    |> equal false

    System.IO.Directory.CreateDirectory(nested)
    |> ignore

    System.IO.Directory.Exists(nested)
    |> equal true
    System.IO.Directory.Exists(baseDir)
    |> equal true

[<Fact>]
let ``test create directory does not throw when directory already exists`` () =
    let dir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), System.IO.Path.GetRandomFileName())

    System.IO.Directory.CreateDirectory(dir)
    |> ignore

    System.IO.Directory.CreateDirectory(dir)
    |> ignore

    System.IO.Directory.Exists(dir)
    |> equal true

// ---- ported from tests/Js/Main (2026-11-16) ----

open System.IO

[<Fact>]
let ``test Path.Combine works with two parts`` () =
    let combined = Path.Combine("foo", "bar")
    Path.GetFileName(combined) |> equal "bar"
    Path.GetDirectoryName(combined) |> equal "foo"

[<Fact>]
let ``test Path.Combine works with three parts`` () =
    let combined = Path.Combine("foo", "bar", "baz.txt")
    Path.GetFileName(combined) |> equal "baz.txt"
    Path.GetDirectoryName(combined) |> equal (Path.Combine("foo", "bar"))

[<Fact>]
let ``test Path.GetDirectoryName works`` () =
    Path.GetDirectoryName("temp/test.txt")
    |> equal "temp"

[<Fact>]
let ``test Path.GetExtension works`` () =
    Path.GetExtension("temp/test.txt")
    |> equal ".txt"

[<Fact>]
let ``test Path.GetFileName works`` () =
    Path.GetFileName("temp/test.txt")
    |> equal "test.txt"

[<Fact>]
let ``test Path.GetFileNameWithoutExtension works`` () =
    Path.GetFileNameWithoutExtension("temp/test.txt")
    |> equal "test"

[<Fact>]
let ``test Path.HasExtension works`` () =
    Path.HasExtension("temp/test.txt")
    |> equal true

    Path.HasExtension("temp/test")
    |> equal false

[<Fact>]
let ``test Path.GetFullPath works`` () =
    (Path.GetFullPath("temp/test.txt")).Length > 0
    |> equal true

[<Fact>]
let ``test Path.GetTempPath works`` () =
    (Path.GetTempPath()).Length > 0
    |> equal true

[<Fact>]
let ``test Path.GetRandomFileName works`` () =
    (Path.GetRandomFileName()).Length > 0
    |> equal true

[<Fact>]
let ``test Path.GetTempFileName works`` () =
    let file1 = Path.GetTempFileName()
    let file2 = Path.GetTempFileName()

    File.Exists(file1) |> equal true
    File.Exists(file2) |> equal true
    (file1 = file2) |> equal false

    File.Delete(file1)
    File.Delete(file2)

[<Fact>]
let ``test File.Exists works`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    File.Exists(file) |> equal false

    File.WriteAllText(file, "Hello World")
    File.Exists(file) |> equal true

    File.Delete(file)
    File.Exists(file) |> equal false

[<Fact>]
let ``test File.WriteAllText and ReadAllText work`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    File.WriteAllText(file, "Hello World")

    File.ReadAllText(file)
    |> equal "Hello World"

    File.Delete(file)

[<Fact>]
let ``test File.WriteAllLines and ReadAllLines work`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    File.WriteAllLines(file, [| "Hello"; "World" |])

    File.ReadAllLines(file)
    |> equal [| "Hello"; "World" |]

    File.Delete(file)

[<Fact>]
let ``test File.ReadAllLines handles CRLF and a trailing newline`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    File.WriteAllText(file, "Hello\r\nWorld\r\n")

    File.ReadAllLines(file)
    |> equal [| "Hello"; "World" |]

    File.Delete(file)

[<Fact>]
let ``test File.WriteAllBytes and ReadAllBytes work`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    let bytes = [| 1uy; 2uy; 3uy |]
    File.WriteAllBytes(file, bytes)

    File.ReadAllBytes(file)
    |> equal bytes

    File.Delete(file)

[<Fact>]
let ``test File.Copy works`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    let copy = file + ".copy"
    File.WriteAllText(file, "Hello World")
    File.Copy(file, copy)

    File.Exists(copy) |> equal true
    File.ReadAllText(copy) |> equal "Hello World"

    File.Delete(file)
    File.Delete(copy)

[<Fact>]
let ``test File.Move works`` () =
    let file = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    let moved = file + ".moved"
    File.WriteAllText(file, "Hello World")
    File.Move(file, moved)

    File.Exists(file) |> equal false
    File.Exists(moved) |> equal true

    File.Delete(moved)

[<Fact>]
let ``test Directory.Exists works`` () =
    Directory.Exists(Path.GetTempPath())
    |> equal true

[<Fact>]
let ``test Directory.Exists returns false for non-existing directory`` () =
    let dir = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())

    Directory.Exists(dir)
    |> equal false

[<Fact>]
let ``test Directory.Exists returns false for a file path`` () =
    let file = Path.GetTempFileName()

    Directory.Exists(file)
    |> equal false

    File.Delete(file)

[<Fact>]
let ``test Directory.CreateDirectory creates missing parent directories`` () =
    let baseDir = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())
    let nested = Path.Combine(baseDir, "a", "b", "c")

    Directory.Exists(nested)
    |> equal false

    Directory.CreateDirectory(nested)
    |> ignore

    Directory.Exists(nested)
    |> equal true

    Directory.Exists(baseDir)
    |> equal true

[<Fact>]
let ``test Directory.CreateDirectory does not throw when directory already exists`` () =
    let dir = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName())

    Directory.CreateDirectory(dir)
    |> ignore

    Directory.CreateDirectory(dir)
    |> ignore

    Directory.Exists(dir)
    |> equal true

