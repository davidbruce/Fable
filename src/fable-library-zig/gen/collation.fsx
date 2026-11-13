// Makes fable_collation.zig from .NET's InvariantCulture, and random pairs with .NET's answers to
// check it with: dotnet fsi gen/collation.fsx fable_collation-body.zig vectors.zig
// (the first file is the table without its header comment)
open System
open System.Globalization

let inv = CultureInfo.InvariantCulture.CompareInfo
let cmp (a: string) (b: string) o = sign (inv.Compare(a, b, o))
let loose = CompareOptions.IgnoreCase ||| CompareOptions.IgnoreNonSpace

let singles =
    [
        for c in 32..126 do
            if not (System.Char.IsUpper(char c)) then
                string (char c)
    ]

let multis = [ "ae"; "oe"; "ss"; "ij"; "dz"; "lj"; "nj"; "th" ]

let baseOf (c: char) =
    let s = string c

    if c >= ' ' && c < '\u007f' then
        if Char.IsLetter c then
            Some(string (Char.ToLowerInvariant c))
        else
            Some s
    elif cmp s "" CompareOptions.None = 0 then
        Some ""
    else
        (singles @ multis) |> List.tryFind (fun b -> cmp s b loose = 0)

let rows = [ for i in 0..0x24F -> char i, baseOf (char i) ]
// secondary rank within a base: sort the lowercase forms of the group with IgnoreCase
let groups =
    rows
    |> List.choose (fun (c, b) ->
        match b with
        | Some b when b <> "" -> Some(b, c)
        | _ -> None
    )
    |> List.groupBy fst

let rank = Collections.Generic.Dictionary<char, int>()
let ter = Collections.Generic.Dictionary<char, int>()

for (b, cs) in groups do
    let forms =
        (b :: (cs |> List.map snd |> List.map (Char.ToLowerInvariant >> string)))
        |> List.distinct

    let sorted = forms |> List.sortWith (fun x y -> cmp x y CompareOptions.IgnoreCase)
    let mutable r = 0
    let mutable prev = None
    let ranks = Collections.Generic.Dictionary<string, int>()

    for f in sorted do
        match prev with
        | Some p when cmp p f CompareOptions.IgnoreCase = 0 -> ()
        | Some _ -> r <- r + 1
        | None -> ()

        ranks[f] <- r
        prev <- Some f

    for (_, c) in cs do
        rank[c] <- ranks[string (Char.ToLowerInvariant c)]

    for (_, c) in cs do
        let peers =
            (b :: (cs |> List.map (snd >> string)))
            |> List.distinct
            |> List.filter (fun x -> cmp x (string c) CompareOptions.IgnoreCase = 0)

        let sorted = peers |> List.sortWith (fun x y -> cmp x y CompareOptions.None)
        let mutable r = 0
        let mutable prev = None

        for f in sorted do
            match prev with
            | Some p when cmp p f CompareOptions.None = 0 -> ()
            | Some _ -> r <- r + 1
            | None -> ()

            if f = string c then
                ter[c] <- r

            prev <- Some f

let asciiOrder =
    [ for c in 32..126 -> string (char c) ]
    |> List.filter (fun s -> not (Char.IsUpper s[0]))

let after = Collections.Generic.Dictionary<char, string>()

for (c, b) in rows do
    if b.IsNone && int c >= 0x80 then
        match asciiOrder |> List.filter (fun p -> cmp p (string c) loose < 0) with
        | [] -> after[c] <- "\u0000"
        | below ->
            after[c] <-
                below
                |> List.maxBy (fun p ->
                    asciiOrder |> List.sortWith (fun x y -> cmp x y loose) |> List.findIndex ((=) p)
                )

for (anchor, cs) in after |> Seq.map (fun kv -> kv.Value, kv.Key) |> Seq.groupBy fst do
    let cs =
        cs |> Seq.map snd |> Seq.map Char.ToLowerInvariant |> Seq.distinct |> List.ofSeq

    let sorted = cs |> List.sortWith (fun x y -> cmp (string x) (string y) loose)
    let mutable r = 0
    let mutable prev = None
    let ranks = Collections.Generic.Dictionary<char, int>()

    for f in sorted do
        match prev with
        | Some p when cmp (string p) (string f) loose = 0 -> ()
        | _ -> r <- r + 1

        ranks[f] <- r
        prev <- Some f

    for kv in after do
        if kv.Value = anchor then
            rank[kv.Key] <- ranks[Char.ToLowerInvariant kv.Key]
// zig: kind 0 other, 1 ignorable, 2 mapped; base up to 2 ascii; sec; upper
let sb = Text.StringBuilder()

sb.Append("// generated from .NET's InvariantCulture (fmt/collgen.fsx): U+0000..U+024F\n")
|> ignore

sb.Append("pub const Coll = struct { kind: u2, b0: u8, b1: u8, sec: u8, ter: u8 };\n")
|> ignore

sb.Append("pub const latin_coll = [_]Coll{\n") |> ignore

for (c, b) in rows do
    let kind, b0, b1 =
        match b with
        | None when after.ContainsKey c -> 3, int (after.[c].[0]), 0
        | None -> 0, 0, 0
        | Some "" -> 1, 0, 0
        | Some s ->
            2,
            int s[0],
            (if s.Length > 1 then
                 int s[1]
             else
                 0)

    let sec =
        match rank.TryGetValue c with
        | true, r -> r
        | _ -> 0

    let t =
        match ter.TryGetValue c with
        | true, r -> r
        | _ ->
            (if Char.IsUpper c then
                 1
             else
                 0)

    sb.Append(sprintf "    .{ .kind = %d, .b0 = %d, .b1 = %d, .sec = %d, .ter = %d },\n" kind b0 b1 sec t)
    |> ignore

sb.Append("};\n") |> ignore
IO.File.WriteAllText(fsi.CommandLineArgs[1], sb.ToString())

let unmapped =
    rows
    |> List.filter (fun (c, b) -> b.IsNone && int c >= 0xC0)
    |> List.map (fst >> string)

printfn "unmapped letters >= C0: %d: %s" unmapped.Length (String.Concat(unmapped |> List.truncate 60))

printfn
    "ignorable: %A"
    (rows
     |> List.filter (fun (_, b) -> b = Some "")
     |> List.map (fun (c, _) -> sprintf "%04X" (int c))
     |> List.truncate 80)
// random vectors
let rnd = Random(7)
let alphabet = " -_.,'!0129aAbBeEézZÉèêëßÆæoOøØœÅåçÇñÑ\u0001­iİı" |> Seq.toArray

let gen () =
    String(Array.init (rnd.Next(0, 6)) (fun _ -> alphabet[rnd.Next alphabet.Length]))

let esc (s: string) =
    String.Concat(s |> Seq.map (fun c -> sprintf "\\u{%x}" (int c)))

let vb = Text.StringBuilder()

vb.Append("pub const Vec = struct { a: []const u8, b: []const u8, none: i32, ic: i32 };\npub const vectors = [_]Vec{\n")
|> ignore

for _ in 1..3000 do
    let a, b = gen (), gen ()

    vb.Append(
        sprintf
            "    .{ .a = \"%s\", .b = \"%s\", .none = %d, .ic = %d },\n"
            (esc a)
            (esc b)
            (cmp a b CompareOptions.None)
            (cmp a b CompareOptions.IgnoreCase)
    )
    |> ignore

vb.Append("};\n") |> ignore
IO.File.WriteAllText(fsi.CommandLineArgs[2], vb.ToString())
