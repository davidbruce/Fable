/// .NET's `System.Uri`, written in F# and compiled by the Zig target itself (see List.fs): an
/// absolute URI split into its parts, or a relative one kept as given. The parts follow .NET:
/// the scheme and host in lower case, the default port of the scheme left out, an empty path
/// as `/`; `AbsoluteUri` escapes spaces, `ToString` unescapes what is not reserved. (A URI
/// without `//` after its scheme, `mailto:a@b.org`, is kept whole as its path: .NET splits
/// some of those schemes further.)
module Fable.Library.Zig.Uri

// UriKind: RelativeOrAbsolute = 0, Absolute = 1, Relative = 2
let private kindAbsolute = 1
let private kindRelative = 2

let private formatError () =
    raise (System.UriFormatException "Invalid URI: The format of the URI could not be determined.")

let private relativeOnly () =
    raise (System.InvalidOperationException "This operation is not supported for a relative URI.")

let private isSchemeChar (c: char) =
    System.Char.IsLetterOrDigit c || c = '+' || c = '-' || c = '.'

let private defaultPort (scheme: string) =
    match scheme with
    | "http"
    | "ws" -> 80
    | "https"
    | "wss" -> 443
    | "ftp" -> 21
    | _ -> -1

/// The index of the first of `chars` in `s` from `start`, or the length of `s`
let private indexOfAny (s: string) (chars: string) (start: int) =
    let mutable i = start

    while i < s.Length && chars.IndexOf s.[i] < 0 do
        i <- i + 1

    i

/// path, query and fragment of what follows the authority
let private splitTail (s: string) : string * string * string =
    let q = indexOfAny s "?#" 0
    let path = s.Substring(0, q)

    if q = s.Length then
        path, "", ""
    elif s.[q] = '#' then
        path, "", s.Substring q
    else
        let h = indexOfAny s "#" q
        path, s.Substring(q, h - q), s.Substring h

/// `%XX` turned back into its char where `unescaped` says so
let private unescapeWhere (unescaped: char -> bool) (s: string) : string =

    let hexValue (c: char) =
        if c >= '0' && c <= '9' then
            int c - int '0'
        elif c >= 'a' && c <= 'f' then
            int c - int 'a' + 10
        elif c >= 'A' && c <= 'F' then
            int c - int 'A' + 10
        else
            -1

    let sb = System.Text.StringBuilder()
    let mutable i = 0

    while i < s.Length do
        if
            s.[i] = '%'
            && i + 2 < s.Length
            && hexValue s.[i + 1] >= 0
            && hexValue s.[i + 2] >= 0
        then
            let c = char (hexValue s.[i + 1] * 16 + hexValue s.[i + 2])

            if not (unescaped c) then
                sb.Append(s.Substring(i, 3)) |> ignore
            else
                sb.Append c |> ignore

            i <- i + 3
        else
            sb.Append s.[i] |> ignore
            i <- i + 1

    sb.ToString()

/// what .NET's `ToString` unescapes: all but reserved and control chars
let private unescape (s: string) =
    unescapeWhere (fun c -> ":/?#[]@!$&'()*+,;=%".IndexOf c < 0 && c >= ' ') s

/// what .NET unescapes when it parses: the unreserved chars (letters, digits, `-._~`); and
/// spaces escaped
let private normalize (s: string) =
    s.Replace(" ", "%20")
    |> unescapeWhere (fun c -> (c < '\u0080' && System.Char.IsLetterOrDigit c) || "-._~".IndexOf c >= 0)


type UriOf =
    {
        original: string
        isAbsolute: bool
        scheme: string
        host: string
        /// -1: none, or the scheme's default
        port: int
        path: string
        query: string
        fragment: string
    }

    /// what follows the scheme's `:` up to the path
    member private u.Authority =
        if u.host = "" && not (u.original.Substring(u.scheme.Length + 1).StartsWith "//") then
            ""
        elif u.port >= 0 then
            "//" + u.host + ":" + string u.port
        else
            "//" + u.host

    /// the absolute URI, escaped
    member u.AbsoluteText = u.scheme + ":" + u.Authority + u.path + u.query + u.fragment

    /// `ToString()`: the URI with what is not reserved unescaped; a relative one as given
    override u.ToString() =
        if u.isAbsolute then
            unescape u.AbsoluteText
        else
            u.original

/// An absolute URI, if `s` is one: a scheme of two or more chars, then `:`
let private tryParseAbsolute (s: string) : UriOf option =
    let s = s.Trim()
    let colon = s.IndexOf ':'

    if
        colon < 2
        || not (System.Char.IsLetter s.[0])
        || not (s.Substring(0, colon) |> Seq.forall isSchemeChar)
    then
        None
    else
        let scheme = s.Substring(0, colon).ToLowerInvariant()
        let rest = s.Substring(colon + 1)

        if rest.StartsWith "//" then
            let authEnd = indexOfAny rest "/?#" 2
            let authority = rest.Substring(2, authEnd - 2)

            let hostPart, port =
                let c = authority.LastIndexOf ':'

                if
                    c >= 0
                    && c < authority.Length - 1
                    && authority.Substring(c + 1) |> Seq.forall System.Char.IsDigit
                then
                    authority.Substring(0, c), int (authority.Substring(c + 1))
                else
                    authority, -1

            let port =
                if port = defaultPort scheme then
                    -1
                else
                    port

            let path, query, fragment = splitTail (rest.Substring authEnd)

            let path =
                if path = "" then
                    "/"
                else
                    path

            Some
                {
                    original = s
                    isAbsolute = true
                    scheme = scheme
                    host = hostPart.ToLowerInvariant()
                    port = port
                    path = normalize path
                    query = normalize query
                    fragment = normalize fragment
                }
        else
            let path, query, fragment = splitTail rest

            Some
                {
                    original = s
                    isAbsolute = true
                    scheme = scheme
                    host = ""
                    port = -1
                    path = normalize path
                    query = normalize query
                    fragment = normalize fragment
                }

let private relative (s: string) : UriOf =
    {
        original = s
        isAbsolute = false
        scheme = ""
        host = ""
        port = -1
        path = ""
        query = ""
        fragment = ""
    }

/// `Unchecked.defaultof<Uri>` (null on .NET): an empty relative URI
let empty () : UriOf = relative ""

let private tryOfKind (s: string) (kind: int) : UriOf option =
    match tryParseAbsolute s with
    | Some u when kind <> kindRelative -> Some u
    | Some _ -> None
    | None when kind = kindAbsolute -> None
    | None -> Some(relative s)

/// `Uri(s)`: an absolute URI
let create (s: string) : UriOf =
    match tryParseAbsolute s with
    | Some u -> u
    | None -> formatError ()

/// `Uri(s, kind)`
let createWithKind (s: string) (kind: int) : UriOf =
    match tryOfKind s kind with
    | Some u -> u
    | None when kind = kindRelative ->
        raise (
            System.UriFormatException
                "Invalid URI: A Relative URI cannot be created because the 'uriString' parameter represents an absolute URI."
        )
    | None -> formatError ()

/// `u.AbsoluteUri`
let absoluteUri (u: UriOf) : string =
    if not u.isAbsolute then
        relativeOnly ()

    u.AbsoluteText

/// `Uri(baseUri, relative)`: the relative part resolved against the base
let private resolve (b: UriOf) (rel: string) : UriOf =
    match tryParseAbsolute rel with
    | Some u -> u
    | None ->
        let path, query, fragment = splitTail rel

        let path, query =
            if path = "" then
                b.path,
                (if query = "" then
                     b.query
                 else
                     query)
            elif path.StartsWith "/" then
                path, query
            else
                b.path.Substring(0, b.path.LastIndexOf '/' + 1) + path, query

        let combined =
            { b with
                path = normalize path
                query = normalize query
                fragment = normalize fragment
            }

        { combined with original = absoluteUri combined }

let private requireAbsolute (b: UriOf) =
    if not b.isAbsolute then
        relativeOnly ()

let createFromBase (b: UriOf) (rel: string) : UriOf =
    requireAbsolute b
    resolve b rel

let createFromBaseUri (b: UriOf) (rel: UriOf) : UriOf =
    requireAbsolute b

    if rel.isAbsolute then
        rel
    else
        resolve b rel.original

/// `Uri.TryCreate(s, kind)`: whether it is one, and the URI (a relative empty one if not;
/// .NET gives null)
let tryCreate (s: string) (kind: int) : bool * UriOf =
    match tryOfKind s kind with
    | Some u -> true, u
    | None -> false, relative ""

/// `Uri.TryCreate(baseUri, relativeUri)`
let tryCreateFromBase (b: UriOf) (rel: UriOf) : bool * UriOf =
    if not b.isAbsolute then
        false, relative ""
    elif rel.isAbsolute then
        true, rel
    else
        true, resolve b rel.original

/// The same as options (what a program's `Uri.TryCreate(s, kind, &uri)` reads)
let tryCreateOption (s: string) (kind: int) : UriOf option = tryOfKind s kind

let tryCreateFromBaseOption (b: UriOf) (rel: UriOf) : UriOf option =
    match tryCreateFromBase b rel with
    | true, u -> Some u
    | _ -> None

let isAbsoluteUri (u: UriOf) = u.isAbsolute
let originalString (u: UriOf) = u.original

let scheme (u: UriOf) =
    requireAbsolute u
    u.scheme

let host (u: UriOf) =
    requireAbsolute u
    u.host

let port (u: UriOf) =
    requireAbsolute u

    if u.port >= 0 then
        u.port
    else
        defaultPort u.scheme

let absolutePath (u: UriOf) =
    requireAbsolute u
    u.path

let query (u: UriOf) =
    requireAbsolute u
    u.query

let fragment (u: UriOf) =
    requireAbsolute u
    u.fragment

let pathAndQuery (u: UriOf) =
    requireAbsolute u
    u.path + u.query

/// `u.ToString()`
let toString (u: UriOf) : string = u.ToString()
