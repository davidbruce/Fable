/// .NET's `System.Guid`, written in F# and compiled by the Zig target itself (see List.fs): a
/// value of its four parts as .NET orders them (`a`, then `b`, then `c`, then the last eight
/// bytes, which `rest` holds big-endian), so that comparing the record compares as
/// `Guid.CompareTo` does.
module Fable.Library.Zig.Guid

[<Struct>]
type GuidOf =
    {
        a: uint32
        /// 0 .. 65535
        b: int
        /// 0 .. 65535
        c: int
        rest: uint64
    }

    /// the text of `ToString(format)`: "D" (and ""), "N", "B", "P", "X"
    member g.Text(format: string) =
        let hex (width: int) (v: uint64) =
            let digits = "0123456789abcdef"
            let chars = Array.create width '0'
            let mutable x = v

            for i in width - 1 .. -1 .. 0 do
                chars.[i] <- digits.[int (x &&& 15UL)]
                x <- x >>> 4

            System.String(chars)

        let a = hex 8 (uint64 g.a)
        let b = hex 4 (uint64 g.b)
        let c = hex 4 (uint64 g.c)
        let d = hex 4 (g.rest >>> 48)
        let e = hex 12 (g.rest &&& 0xFFFFFFFFFFFFUL)
        let dashed = a + "-" + b + "-" + c + "-" + d + "-" + e

        match format with
        | ""
        | "D"
        | "d" -> dashed
        | "N"
        | "n" -> a + b + c + d + e
        | "B"
        | "b" -> "{" + dashed + "}"
        | "P"
        | "p" -> "(" + dashed + ")"
        | "X"
        | "x" ->
            let rest = g.rest

            let bytes =
                [ for i in 7..-1..0 -> "0x" + hex 2 ((rest >>> (8 * i)) &&& 0xFFUL) ]
                |> String.concat ","

            "{0x" + a + ",0x" + b + ",0x" + c + ",{" + bytes + "}}"
        | _ ->
            raise (
                System.FormatException
                    "Format string can be only \"D\", \"d\", \"N\", \"n\", \"P\", \"p\", \"B\", \"b\", \"X\" or \"x\"."
            )

    override g.ToString() = g.Text "D"

let empty: GuidOf =
    {
        a = 0u
        b = 0
        c = 0
        rest = 0UL
    }

/// `Unchecked.defaultof<Guid>` and `Guid()`
let create () : GuidOf = empty

let private hexValue (c: char) =
    if c >= '0' && c <= '9' then
        int c - int '0'
    elif c >= 'a' && c <= 'f' then
        int c - int 'a' + 10
    elif c >= 'A' && c <= 'F' then
        int c - int 'A' + 10
    else
        -1

/// The 32 hex digits of a Guid in the forms "N", "D", "B" and "P", if `s` is one
let private digitsOf (s: string) : string option =
    let s = s.Trim()

    let dashed (d: string) =
        if d.Length = 36 && d.[8] = '-' && d.[13] = '-' && d.[18] = '-' && d.[23] = '-' then
            Some(d.Replace("-", ""))
        else
            None

    let digits =
        if s.Length = 32 then
            Some s
        elif
            s.Length = 38
            && ((s.[0] = '{' && s.[37] = '}') || (s.[0] = '(' && s.[37] = ')'))
        then
            dashed (s.Substring(1, 36))
        else
            dashed s

    match digits with
    | Some d when d.Length = 32 && d |> Seq.forall (fun c -> hexValue c >= 0) -> Some d
    | _ -> None

let private ofDigits (d: string) : GuidOf =
    let number (start: int) (count: int) =
        let mutable v = 0UL

        for i in start .. start + count - 1 do
            v <- (v <<< 4) ||| uint64 (hexValue d.[i])

        v

    {
        a = uint32 (number 0 8)
        b = int (number 8 4)
        c = int (number 12 4)
        rest = (number 16 8 <<< 32) ||| number 24 8
    }

/// `Guid.TryParse(s)` as an option
let tryParseOption (s: string) : GuidOf option = digitsOf s |> Option.map ofDigits

/// `Guid.TryParse(s)`: whether it is one, and the Guid (empty if not)
let tryParse (s: string) : bool * GuidOf =
    match tryParseOption s with
    | Some g -> true, g
    | None -> false, empty

/// `Guid.Parse(s)` and `Guid(s)`
let parse (s: string) : GuidOf =
    match tryParseOption s with
    | Some g -> g
    | None -> raise (System.FormatException "Unrecognized Guid format.")

/// `Guid(bytes)`: the layout of `ToByteArray`
let ofBytes (bytes: byte[]) : GuidOf =
    if bytes.Length <> 16 then
        raise (System.ArgumentException("Byte array for Guid must be exactly 16 bytes long. (Parameter 'b')"))

    let u (i: int) = uint64 bytes.[i]

    {
        a = uint32 ((u 3 <<< 24) ||| (u 2 <<< 16) ||| (u 1 <<< 8) ||| u 0)
        b = int ((u 5 <<< 8) ||| u 4)
        c = int ((u 7 <<< 8) ||| u 6)
        rest = [ 8..15 ] |> List.fold (fun acc i -> (acc <<< 8) ||| u i) 0UL
    }

/// `g.ToByteArray()`: `a`, `b` and `c` little-endian, then the last eight bytes
let toByteArray (g: GuidOf) : byte[] =
    let rest = g.rest

    Array.append
        [|
            byte (g.a &&& 0xFFu)
            byte ((g.a >>> 8) &&& 0xFFu)
            byte ((g.a >>> 16) &&& 0xFFu)
            byte (g.a >>> 24)
            byte (g.b &&& 0xFF)
            byte (g.b >>> 8)
            byte (g.c &&& 0xFF)
            byte (g.c >>> 8)
        |]
        (Array.init 8 (fun i -> byte ((rest >>> (8 * (7 - i))) &&& 0xFFUL)))

let private random = System.Random()

/// `Guid.NewGuid()`: version 4, random (from System.Random, not a cryptographic source)
let newGuid () : GuidOf =
    let next16 () = uint64 (random.Next(0, 65536))
    let a = uint32 ((next16 () <<< 16) ||| next16 ())
    let b = int (next16 ())
    let c = int ((next16 () &&& 0x0FFFUL) ||| 0x4000UL)
    let d = (next16 () &&& 0x3FFFUL) ||| 0x8000UL
    let rest = (d <<< 48) ||| (next16 () <<< 32) ||| (next16 () <<< 16) ||| next16 ()

    {
        a = a
        b = b
        c = c
        rest = rest
    }

let toString (g: GuidOf) : string = g.Text "D"
let toStringFormat (g: GuidOf) (format: string) : string = g.Text format

/// `Guid.CreateVersion7(timestamp)`: version 7, of the Unix time in milliseconds (48 bits), then
/// random bits
let createVersion7Of (d: Fable.Library.Zig.DateTimeOffset.DateTimeOffsetOf) : GuidOf =
    let ms = Fable.Library.Zig.DateTimeOffset.toUnixTimeMilliseconds d

    if ms < 0L then
        raise (System.ArgumentOutOfRangeException("timestamp", "The timestamp must be at or after the Unix epoch."))

    let next16 () = uint64 (random.Next(0, 65536))
    let c = int ((next16 () &&& 0x0FFFUL) ||| 0x7000UL)
    let d = (next16 () &&& 0x3FFFUL) ||| 0x8000UL
    let rest = (d <<< 48) ||| (next16 () <<< 32) ||| (next16 () <<< 16) ||| next16 ()

    {
        a = uint32 ((uint64 ms >>> 16) &&& 0xFFFFFFFFUL)
        b = int (uint64 ms &&& 0xFFFFUL)
        c = c
        rest = rest
    }

/// `Guid.CreateVersion7()`: of the time now
let createVersion7 () : GuidOf =
    createVersion7Of (Fable.Library.Zig.DateTimeOffset.utcNow ())
