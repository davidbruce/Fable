/// .NET's `System.IO.Path` on Unix (a separator `/`), written in F# and compiled by the Zig
/// target itself (see List.fs). What needs the system (the full path, the temporary directory)
/// is the runtime's (fable_io.zig).
module Fable.Library.Zig.Path

let private isNullOrEmpty (s: string) = isNull s || s.Length = 0

let private nullPath () =
    raise (System.ArgumentNullException("path", "Value cannot be null."))

/// The index where the file name starts (after the last separator)
let private nameStart (path: string) = path.LastIndexOf '/' + 1

let getFileName (path: string) : string =
    if isNull path then
        null
    else
        path.Substring(nameStart path)

let getExtension (path: string) : string =
    if isNull path then
        null
    else
        let start = nameStart path
        let dot = path.LastIndexOf '.'

        if dot >= start && dot < path.Length - 1 then
            path.Substring dot
        else
            ""

let hasExtension (path: string) : bool =
    not (isNull path) && (getExtension path).Length > 0

let getFileNameWithoutExtension (path: string) : string =
    if isNull path then
        null
    else
        let name = getFileName path
        let dot = name.LastIndexOf '.'

        if dot >= 0 then
            name.Substring(0, dot)
        else
            name

/// The directory of the path: null for a root or an empty path, "" when there is none
let getDirectoryName (path: string) : string =
    if isNullOrEmpty path then
        null
    else
        let slash = path.LastIndexOf '/'

        if slash < 0 then
            ""
        else
            // (the separators before the name, all of them)
            let mutable stop = slash

            while stop > 0 && path.[stop - 1] = '/' do
                stop <- stop - 1

            if stop = 0 then
                if path.Length = slash + 1 && slash = 0 then
                    null
                else
                    "/"
            else
                // (repeated separators within it are one, as .NET gives it)
                let dir = path.Substring(0, stop)
                let sb = System.Text.StringBuilder()

                for i in 0 .. dir.Length - 1 do
                    if not (dir.[i] = '/' && i > 0 && dir.[i - 1] = '/') then
                        sb.Append(dir.[i]) |> ignore

                sb.ToString()

let isPathRooted (path: string) : bool =
    not (isNull path) && path.StartsWith "/"

let getPathRoot (path: string) : string =
    if isNullOrEmpty path then
        null
    elif isPathRooted path then
        "/"
    else
        ""

let changeExtension (path: string) (extension: string) : string =
    if isNull path then
        null
    elif path = "" then
        ""
    else
        let start = nameStart path
        let dot = path.LastIndexOf '.'

        let stem =
            if dot >= start then
                path.Substring(0, dot)
            else
                path

        if isNull extension then
            stem
        elif extension = "" then
            stem + "."
        elif extension.StartsWith "." then
            stem + extension
        else
            stem + "." + extension

/// `Path.Combine(a, b, ...)`: a rooted part starts again
let combineAll (parts: string[]) : string =
    if isNull parts then
        raise (System.ArgumentNullException("paths", "Value cannot be null."))

    let mutable result = ""

    for p in parts do
        if isNull p then
            nullPath ()

        if p.Length > 0 then
            if isPathRooted p || result.Length = 0 then
                result <- p
            elif result.EndsWith "/" then
                result <- result + p
            else
                result <- result + "/" + p

    result

let combine (a: string) (b: string) : string = combineAll [| a; b |]

/// `Path.Join(a, b, ...)`: one separator between the parts, a rooted one too
let joinAll (parts: string[]) : string =
    let mutable result = ""

    for p in parts do
        if not (isNullOrEmpty p) then
            if result.Length = 0 then
                result <- p
            elif result.EndsWith "/" || p.StartsWith "/" then
                result <- result + p
            else
                result <- result + "/" + p

    result

let directorySeparatorChar () = '/'
let altDirectorySeparatorChar () = '/'
let pathSeparator () = ':'
let volumeSeparatorChar () = '/'

let getInvalidFileNameChars () : char[] = [| '\000'; '/' |]
let getInvalidPathChars () : char[] = [| '\000' |]

// ---- File and Directory: the runtime's (fable_io.zig), and what is made of it ----

#if FABLE_COMPILER
[<Fable.Core.Emit("try fable_rt.io.readAllText($0)")>]
let private readText (_path: string) : string = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.io.writeAllText($0, $1, $2)")>]
let private writeText (_path: string) (_text: string) (_append: bool) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.io.fullPath($0)")>]
let private fullPath (_path: string) : string = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.io.createDirectory($0)")>]
let private makeDirectory (_path: string) : unit = Fable.Core.Util.nativeOnly
#else
let private makeDirectory (path: string) : unit =
    System.IO.Directory.CreateDirectory path |> ignore

let private readText (path: string) : string = System.IO.File.ReadAllText path

let private writeText (path: string) (text: string) (append: bool) : unit =
    if append then
        System.IO.File.AppendAllText(path, text)
    else
        System.IO.File.WriteAllText(path, text)

let private fullPath (path: string) : string = System.IO.Path.GetFullPath path
#endif

/// `File.ReadAllLines(path)`: split at "\r\n", "\n" and "\r" (a last line break ends the last line)
let readAllLines (path: string) : string[] =
    let text = readText path
    let lines = ResizeArray<string>()
    let mutable start = 0
    let mutable i = 0

    while i < text.Length do
        let c = text.[i]

        if c = '\n' || c = '\r' then
            lines.Add(text.Substring(start, i - start))

            if c = '\r' && i + 1 < text.Length && text.[i + 1] = '\n' then
                i <- i + 1

            start <- i + 1

        i <- i + 1

    if start < text.Length then
        lines.Add(text.Substring start)

    lines.ToArray()

/// `File.WriteAllLines(path, lines)` and `File.AppendAllLines`: each line and a line break
let private linesText (lines: string[]) : string =
    let sb = System.Text.StringBuilder()

    for l in lines do
        sb.Append(l).Append('\n') |> ignore

    sb.ToString()

let writeAllLines (path: string) (lines: string[]) : unit = writeText path (linesText lines) false
let appendAllLines (path: string) (lines: string[]) : unit = writeText path (linesText lines) true

/// `DirectoryInfo` (what `Directory.CreateDirectory` gives): its full path
type DirectoryInfoOf = { fullName: string }

let directoryInfo (path: string) : DirectoryInfoOf = { fullName = fullPath path }

/// `Directory.CreateDirectory(path)`: it (and those above it), and its DirectoryInfo
let createDirectory (path: string) : DirectoryInfoOf =
    makeDirectory path
    directoryInfo path

let directoryInfoFullName (d: DirectoryInfoOf) = d.fullName

let directoryInfoName (d: DirectoryInfoOf) =
    let n = d.fullName.TrimEnd('/')

    if n = "" then
        "/"
    else
        n.Substring(n.LastIndexOf '/' + 1)
