/// .NET's `System.Text.RegularExpressions`, written in F# and compiled by the Zig target itself
/// (see List.fs): a backtracking engine of .NET's syntax (classes, anchors, groups numbered as
/// .NET numbers them, named, non-capturing and lookaround groups, greedy and lazy quantifiers,
/// backreferences, the options), and `Regex`, `Match`, `Group` and the collections over it.
module Fable.Library.Zig.Regex

// RegexOptions
let private ignoreCase = 1
let private multiline = 2
let private explicitCapture = 4
let private singleline = 16
let private ignoreWhitespace = 32
let private ecmaScript = 256

type ClassItem =
    | Range of char * char
    /// \d \D \w \W \s \S
    | Named of char
    /// \p{Lu} (and \P{Lu}, negated): the numbers of .NET's UnicodeCategory it has
    | Category of int list * bool

/// (each node keeps the options in force where it is: case folding, `.` of any character, `^`
/// and `$` of lines)
type Node =
    | Lit of char * fold: bool
    | AnyChar of single: bool
    | Set of negated: bool * items: ClassItem list * fold: bool
    | LineStart of lines: bool
    | LineEnd of lines: bool
    | TextStart
    | TextEnd
    | TextEndOrNewline
    | WordBoundary of bool
    /// a group: its number once known (-1 while parsing a named one), and its name
    | Capture of int * string * Node
    | Sequence of Node list
    | Alternation of Node list
    | Repeat of Node * int * int * bool
    | Look of behind: bool * negated: bool * Node
    | BackRef of int * fold: bool
    | NamedBackRef of string * fold: bool
    | Empty

type RegexOf =
    {
        pattern: string
        options: int
        root: Node
        /// the names of the groups by number (an unnamed one is its number)
        names: string[]
    }

type GroupOf =
    {
        success: bool
        index: int
        length: int
        value: string
        name: string
    }

type MatchOf =
    {
        regex: RegexOf
        input: string
        /// group 0 is the match
        groups: GroupOf[]
    }

type MatchCollectionOf = { matches: MatchOf[] }

type GroupCollectionOf = { items: GroupOf[] }

/// (the items of a ResizeArray as a list: the library's List module takes no ResizeArray)
let private listOf (r: ResizeArray<'T>) : 'T list =
    let mutable acc = []

    for i in r.Count - 1 .. -1 .. 0 do
        acc <- r.[i] :: acc

    acc

let private parseError (pattern: string) (offset: int) (why: string) : 'a =
    raise (System.ArgumentException("Invalid pattern '" + pattern + "' at offset " + string offset + ". " + why))

// ---- parsing ----

let private parse (pattern: string) (options: int) : Node * string[] =
    let mutable i = 0
    let mutable unnamed = 0
    let namedOrder = ResizeArray<string>()
    // (the options in force: the regex's, as inline options change them)
    let mutable opts = options
    // (what `(?i)` leaves in force after it)
    let mutable inlineOptions: int option = None
    let extended () = opts &&& ignoreWhitespace <> 0
    let explicitOnly () = opts &&& explicitCapture <> 0
    let fold () = opts &&& ignoreCase <> 0

    let peek () =
        if i < pattern.Length then
            pattern.[i]
        else
            '\000'

    let atEnd () = i >= pattern.Length

    let hexValue (c: char) =
        if c >= '0' && c <= '9' then
            int c - int '0'
        elif c >= 'a' && c <= 'f' then
            int c - int 'a' + 10
        elif c >= 'A' && c <= 'F' then
            int c - int 'A' + 10
        else
            -1

    let hex (n: int) =
        let mutable v = 0

        for _ in 1..n do
            let d =
                if atEnd () then
                    -1
                else
                    hexValue pattern.[i]

            if d < 0 then
                parseError pattern i "Insufficient or invalid hexadecimal digits."

            v <- v * 16 + d
            i <- i + 1

        char v

    /// the character of an escape that stands for one (after the backslash)
    let escapedChar (c: char) : char option =
        match c with
        | 'n' -> Some '\n'
        | 'r' -> Some '\r'
        | 't' -> Some '\t'
        | 'f' -> Some '\012'
        | 'v' -> Some '\011'
        | 'a' -> Some '\007'
        | 'e' -> Some '\027'
        | 'x' -> Some(hex 2)
        | 'u' -> Some(hex 4)
        | 'c' ->
            let x = peek ()
            i <- i + 1
            Some(char (int (System.Char.ToUpperInvariant x) - 64))
        | '0' ->
            // (an octal number of up to three digits)
            let mutable v = 0
            let mutable n = 0

            while n < 2 && not (atEnd ()) && pattern.[i] >= '0' && pattern.[i] <= '7' do
                v <- v * 8 + (int pattern.[i] - int '0')
                i <- i + 1
                n <- n + 1

            Some(char v)
        | _ when System.Char.IsLetterOrDigit c -> None
        | _ -> Some c

    let skipWhitespace () =
        if extended () then
            let mutable go = true

            while go && not (atEnd ()) do
                let c = pattern.[i]

                if System.Char.IsWhiteSpace c then
                    i <- i + 1
                elif c = '#' then
                    while not (atEnd ()) && pattern.[i] <> '\n' do
                        i <- i + 1
                else
                    go <- false

    /// `\p{Lu}`: after the 'p'
    let category () : int list =
        if peek () <> '{' then
            parseError pattern i "Incomplete \\p{X} character escape."

        let close = pattern.IndexOf('}', i)

        if close < 0 then
            parseError pattern i "Incomplete \\p{X} character escape."

        let name = pattern.Substring(i + 1, close - i - 1)
        i <- close + 1

        let all =
            [
                "Lu", 0
                "Ll", 1
                "Lt", 2
                "Lm", 3
                "Lo", 4
                "Mn", 5
                "Mc", 6
                "Me", 7
                "Nd", 8
                "Nl", 9
                "No", 10
                "Zs", 11
                "Zl", 12
                "Zp", 13
                "Cc", 14
                "Cf", 15
                "Cs", 16
                "Co", 17
                "Pc", 18
                "Pd", 19
                "Ps", 20
                "Pe", 21
                "Pi", 22
                "Pf", 23
                "Po", 24
                "Sm", 25
                "Sc", 26
                "Sk", 27
                "So", 28
                "Cn", 29
            ]

        match all |> List.tryFind (fun (n, _) -> n = name) with
        | Some(_, k) -> [ k ]
        | None ->
            match all |> List.filter (fun (n, _) -> name.Length = 1 && n.[0] = name.[0]) with
            | [] -> parseError pattern i ("Unknown property '" + name + "'.")
            | ks -> ks |> List.map snd

    let parseClass () : Node =
        // (after '[')
        let negated =
            if peek () = '^' then
                i <- i + 1
                true
            else
                false

        let items = ResizeArray<ClassItem>()
        let mutable first = true
        let mutable go = true

        let classChar () : Choice<char, char> =
            // a character, or a named class (\d...)
            let c = pattern.[i]
            i <- i + 1

            if c = '\\' then
                if atEnd () then
                    parseError pattern i "Illegal \\ at end of pattern."

                let e = pattern.[i]
                i <- i + 1

                match e with
                | 'd'
                | 'D'
                | 'w'
                | 'W'
                | 's'
                | 'S' -> Choice2Of2 e
                | 'p'
                | 'P' ->
                    let ks = category ()
                    items.Add(Category(ks, e = 'P'))
                    // (the category is added: nothing else)
                    Choice2Of2 '\000'
                | 'b' -> Choice1Of2 '\b'
                | _ ->
                    match escapedChar e with
                    | Some x -> Choice1Of2 x
                    | None -> parseError pattern i ("Unrecognized escape sequence \\" + string e + ".")
            else
                Choice1Of2 c

        while go do
            if atEnd () then
                parseError pattern i "Unterminated [] set."

            if pattern.[i] = ']' && not first then
                i <- i + 1
                go <- false
            else
                first <- false

                match classChar () with
                | Choice2Of2 '\000' -> ()
                | Choice2Of2 n -> items.Add(Named n)
                | Choice1Of2 lo ->
                    if peek () = '-' && i + 1 < pattern.Length && pattern.[i + 1] <> ']' then
                        i <- i + 1

                        match classChar () with
                        | Choice1Of2 hi ->
                            if hi < lo then
                                parseError pattern i "[x-y] range in reverse order."

                            items.Add(Range(lo, hi))
                        | Choice2Of2 n ->
                            items.Add(Range(lo, lo))
                            items.Add(Range('-', '-'))

                            if n <> '\000' then
                                items.Add(Named n)
                    else
                        items.Add(Range(lo, lo))

        Set(negated, listOf items, fold ())

    let rec parseAlternation () : Node =
        let branches = ResizeArray<Node>()
        branches.Add(parseSequence ())

        while peek () = '|' && not (atEnd ()) do
            i <- i + 1
            branches.Add(parseSequence ())

        if branches.Count = 1 then
            branches.[0]
        else
            Alternation(listOf branches)

    and parseSequence () : Node =
        let items = ResizeArray<Node>()
        let mutable go = true

        while go do
            skipWhitespace ()

            if atEnd () || peek () = '|' || peek () = ')' then
                go <- false
            else
                let atom = parseAtom ()
                skipWhitespace ()
                items.Add(parseQuantifier atom)

        match items.Count with
        | 0 -> Empty
        | 1 -> items.[0]
        | _ -> Sequence(listOf items)

    and parseQuantifier (atom: Node) : Node =
        let lazyMark () =
            if peek () = '?' then
                i <- i + 1
                true
            else
                false

        let quantified mn mx =
            match atom with
            | LineStart _
            | LineEnd _
            | TextStart
            | TextEnd
            | TextEndOrNewline
            | WordBoundary _ -> atom
            | _ -> Repeat(atom, mn, mx, lazyMark ())

        if atEnd () then
            atom
        else
            match pattern.[i] with
            | '*' ->
                i <- i + 1
                parseQuantifier (quantified 0 -1)
            | '+' ->
                i <- i + 1
                parseQuantifier (quantified 1 -1)
            | '?' ->
                i <- i + 1
                parseQuantifier (quantified 0 1)
            | '{' ->
                // `{n}`, `{n,}`, `{n,m}`; anything else is the character
                let save = i
                i <- i + 1

                let number () =
                    let start = i

                    while not (atEnd ()) && System.Char.IsDigit pattern.[i] do
                        i <- i + 1

                    if i = start then
                        None
                    else
                        Some(int pattern.[start .. i - 1])

                match number () with
                | Some mn ->
                    let mx =
                        if peek () = ',' then
                            i <- i + 1

                            match number () with
                            | Some mx -> Some mx
                            | None -> Some -1
                        else
                            Some mn

                    if peek () = '}' then
                        i <- i + 1
                        let mx = mx.Value

                        if mx >= 0 && mx < mn then
                            parseError pattern i "Illegal {x,y} with x > y."

                        parseQuantifier (quantified mn mx)
                    else
                        i <- save
                        atom
                | None ->
                    i <- save
                    atom
            | _ -> atom

    and parseGroup () : Node =
        // (after '('; the options a group changes are its own)
        let outer = opts
        let node = parseGroupIn ()
        opts <- outer
        node

    and parseGroupIn () : Node =
        if peek () = '?' then
            i <- i + 1

            match peek () with
            | ':' ->
                i <- i + 1
                let inner = parseAlternation ()
                closeGroup ()
                inner
            | '=' ->
                i <- i + 1
                let inner = parseAlternation ()
                closeGroup ()
                Look(false, false, inner)
            | '!' ->
                i <- i + 1
                let inner = parseAlternation ()
                closeGroup ()
                Look(false, true, inner)
            | '>' ->
                // (an atomic group: as a plain one here)
                i <- i + 1
                let inner = parseAlternation ()
                closeGroup ()
                inner
            | '<' when i + 1 < pattern.Length && (pattern.[i + 1] = '=' || pattern.[i + 1] = '!') ->
                let negated = pattern.[i + 1] = '!'
                i <- i + 2
                let inner = parseAlternation ()
                closeGroup ()
                Look(true, negated, inner)
            | '<'
            | '\'' ->
                let close =
                    if peek () = '<' then
                        '>'
                    else
                        '\''

                i <- i + 1
                let start = i

                while not (atEnd ()) && pattern.[i] <> close do
                    i <- i + 1

                if atEnd () then
                    parseError pattern i "Invalid group name."

                let name = pattern.[start .. i - 1]
                i <- i + 1

                if name = "" then
                    parseError pattern i "Invalid group name."

                if not (namedOrder.Contains name) then
                    namedOrder.Add name

                let inner = parseAlternation ()
                closeGroup ()
                Capture(-1, name, inner)
            | c when c = 'i' || c = 'm' || c = 's' || c = 'x' || c = 'n' || c = '-' ->
                // `(?im-sx)`: for the rest of the group around it; `(?i:...)`: within
                let mutable on = true
                let mutable go = true

                while go do
                    if atEnd () then
                        parseError pattern i "Unrecognized grouping construct."

                    let flag =
                        match pattern.[i] with
                        | 'i' -> ignoreCase
                        | 'm' -> multiline
                        | 's' -> singleline
                        | 'x' -> ignoreWhitespace
                        | 'n' -> explicitCapture
                        | _ -> 0

                    match pattern.[i] with
                    | '-' ->
                        on <- false
                        i <- i + 1
                    | ')'
                    | ':' -> go <- false
                    | _ when flag <> 0 ->
                        opts <-
                            if on then
                                opts ||| flag
                            else
                                opts &&& ~~~flag

                        i <- i + 1
                    | _ -> parseError pattern i "Unrecognized grouping construct."

                if pattern.[i] = ')' then
                    i <- i + 1
                    // (the options go on past this group: they are the enclosing group's)
                    inlineOptions <- Some opts
                    Empty
                else
                    i <- i + 1
                    let inner = parseAlternation ()
                    closeGroup ()
                    inner
            | _ -> parseError pattern i "Unrecognized grouping construct."
        else if explicitOnly () then
            let inner = parseAlternation ()
            closeGroup ()
            inner
        else
            unnamed <- unnamed + 1
            let n = unnamed
            let inner = parseAlternation ()
            closeGroup ()
            Capture(n, string n, inner)

    and closeGroup () =
        if peek () <> ')' || atEnd () then
            parseError pattern i "Not enough )'s."

        i <- i + 1

    and parseAtom () : Node =
        let c = pattern.[i]
        i <- i + 1

        match c with
        | '.' -> AnyChar(opts &&& singleline <> 0)
        | '^' -> LineStart(opts &&& multiline <> 0)
        | '$' -> LineEnd(opts &&& multiline <> 0)
        | '(' ->
            let node = parseGroup ()

            // (`(?i)`: its options stay for the rest of the enclosing group)
            match inlineOptions with
            | Some o ->
                opts <- o
                inlineOptions <- None
            | None -> ()

            node
        | '[' -> parseClass ()
        | '*'
        | '+'
        | '?' -> parseError pattern i ("Quantifier '" + string c + "' following nothing.")
        | '\\' ->
            if atEnd () then
                parseError pattern i "Illegal \\ at end of pattern."

            let e = pattern.[i]
            i <- i + 1

            match e with
            | 'd'
            | 'D'
            | 'w'
            | 'W'
            | 's'
            | 'S' -> Set(false, [ Named e ], false)
            | 'p'
            | 'P' -> Set(false, [ Category(category (), e = 'P') ], fold ())
            | 'b' -> WordBoundary true
            | 'B' -> WordBoundary false
            | 'A' -> TextStart
            | 'z' -> TextEnd
            | 'Z' -> TextEndOrNewline
            | 'G' -> Empty
            | 'k' when peek () = '<' || peek () = '\'' ->
                let close =
                    if peek () = '<' then
                        '>'
                    else
                        '\''

                i <- i + 1
                let start = i

                while not (atEnd ()) && pattern.[i] <> close do
                    i <- i + 1

                let name = pattern.[start .. i - 1]
                i <- i + 1
                NamedBackRef(name, fold ())
            | d when d >= '1' && d <= '9' ->
                let start = i - 1

                while not (atEnd ()) && System.Char.IsDigit pattern.[i] do
                    i <- i + 1

                BackRef(int pattern.[start .. i - 1], fold ())
            | _ ->
                match escapedChar e with
                | Some x -> Lit(x, fold ())
                | None -> parseError pattern i ("Unrecognized escape sequence \\" + string e + ".")
        | _ -> Lit(c, fold ())

    let root = parseAlternation ()

    if not (atEnd ()) then
        parseError pattern i "Too many )'s."

    // the named groups are numbered after the unnamed ones (a name that is a number is that number)
    let numberOf = System.Collections.Generic.Dictionary<string, int>()
    let mutable next = unnamed + 1

    for name in namedOrder do
        match System.Int32.TryParse name with
        | true, n -> numberOf.[name] <- n
        | _ ->
            numberOf.[name] <- next
            next <- next + 1

    let mutable count = next

    for KeyValue(_, n) in numberOf do
        if n + 1 > count then
            count <- n + 1

    let names = Array.init count string

    for KeyValue(name, n) in numberOf do
        names.[n] <- name

    let rec resolve (n: Node) : Node =
        match n with
        | Capture(-1, name, inner) -> Capture(numberOf.[name], name, resolve inner)
        | Capture(k, name, inner) -> Capture(k, name, resolve inner)
        | Sequence xs -> Sequence(List.map resolve xs)
        | Alternation xs -> Alternation(List.map resolve xs)
        | Repeat(x, a, b, l) -> Repeat(resolve x, a, b, l)
        | Look(b, neg, x) -> Look(b, neg, resolve x)
        | NamedBackRef(name, f) ->
            match numberOf.TryGetValue name with
            | true, k -> BackRef(k, f)
            | _ -> parseError pattern pattern.Length ("Reference to undefined group name '" + name + "'.")
        | _ -> n

    resolve root, names

let create (pattern: string) (options: int) : RegexOf =
    if isNull pattern then
        raise (System.ArgumentNullException("pattern", "Value cannot be null."))

    let root, names = parse pattern options

    {
        pattern = pattern
        options = options
        root = root
        names = names
    }

let ofPattern (pattern: string) : RegexOf = create pattern 0

// ---- matching ----

let private isWordChar (c: char) =
    System.Char.IsLetterOrDigit c || c = '_'

let private inNamed (ecma: bool) (n: char) (c: char) : bool =
    match n with
    | 'd' ->
        if ecma then
            c >= '0' && c <= '9'
        else
            System.Char.IsDigit c
    | 'D' ->
        not (
            if ecma then
                c >= '0' && c <= '9'
            else
                System.Char.IsDigit c
        )
    | 'w' ->
        if ecma then
            (c >= 'a' && c <= 'z')
            || (c >= 'A' && c <= 'Z')
            || (c >= '0' && c <= '9')
            || c = '_'
        else
            isWordChar c
    | 'W' ->
        not (
            if ecma then
                (c >= 'a' && c <= 'z')
                || (c >= 'A' && c <= 'Z')
                || (c >= '0' && c <= '9')
                || c = '_'
            else
                isWordChar c
        )
    | 's' -> System.Char.IsWhiteSpace c
    | _ -> not (System.Char.IsWhiteSpace c)

/// The match of `re` in `input` at or after `startAt`: the start and end of each group (-1 when
/// it took no part)
let private search (re: RegexOf) (input: string) (startAt: int) : (int[] * int[]) option =
    let n = re.names.Length
    let starts = Array.create (max n 1) -1
    let ends = Array.create (max n 1) -1
    let ecma = re.options &&& ecmaScript <> 0
    let len = input.Length

    let sameChar (fold: bool) (a: char) (b: char) =
        a = b
        || (fold && System.Char.ToLowerInvariant a = System.Char.ToLowerInvariant b)

    let inSet (negated: bool) (items: ClassItem list) (fold: bool) (c: char) =
        let test (x: char) =
            items
            |> List.exists (fun item ->
                match item with
                | Range(lo, hi) -> x >= lo && x <= hi
                | Named k -> inNamed ecma k x
                | Category(ks, neg) ->
                    // (ignoring case, a cased category is all three: Lu, Ll and Lt, as in .NET)
                    let ks =
                        if fold && ks |> List.exists (fun k -> k <= 2) then
                            0 :: 1 :: 2 :: ks
                        else
                            ks

                    (List.contains (int (System.Char.GetUnicodeCategory x)) ks) <> neg
            )

        let found =
            test c
            || (fold
                && (test (System.Char.ToLowerInvariant c) || test (System.Char.ToUpperInvariant c)))

        found <> negated

    let wordAt (p: int) =
        p >= 0 && p < len && isWordChar input.[p]

    let rec m (node: Node) (i: int) (k: int -> bool) : bool =
        match node with
        | Empty -> k i
        | Lit(c, fold) -> i < len && sameChar fold input.[i] c && k (i + 1)
        | AnyChar single -> i < len && (single || input.[i] <> '\n') && k (i + 1)
        | Set(negated, items, fold) -> i < len && inSet negated items fold input.[i] && k (i + 1)
        | LineStart lines -> (i = 0 || (lines && input.[i - 1] = '\n')) && k i
        | LineEnd lines ->
            (i = len
             || (lines && input.[i] = '\n')
             || (not lines && i = len - 1 && input.[i] = '\n'))
            && k i
        | TextStart -> i = 0 && k i
        | TextEnd -> i = len && k i
        | TextEndOrNewline -> (i = len || (i = len - 1 && input.[i] = '\n')) && k i
        | WordBoundary yes -> ((wordAt (i - 1) <> wordAt i) = yes) && k i
        | Capture(g, _, inner) ->
            let oldStart = starts.[g]
            let oldEnd = ends.[g]

            m
                inner
                i
                (fun j ->
                    let s = starts.[g]
                    let e = ends.[g]
                    starts.[g] <- i
                    ends.[g] <- j

                    if k j then
                        true
                    else
                        starts.[g] <- s
                        ends.[g] <- e
                        false
                )
            || (starts.[g] <- oldStart
                ends.[g] <- oldEnd
                false)
        | Sequence xs ->
            let rec go (rest: Node list) (p: int) =
                match rest with
                | [] -> k p
                | x :: tail -> m x p (fun q -> go tail q)

            go xs i
        | Alternation xs -> xs |> List.exists (fun x -> m x i k)
        | Repeat(inner, mn, mx, isLazy) ->
            let rec loop (count: int) (p: int) : bool =
                let more () =
                    (mx < 0 || count < mx)
                    && m
                        inner
                        p
                        (fun q ->
                            if q = p && count >= mn then
                                false
                            else
                                loop (count + 1) q
                        )

                if isLazy then
                    (count >= mn && k p) || more ()
                else
                    more () || (count >= mn && k p)

            loop 0 i
        | Look(false, negated, inner) ->
            let saved = Array.copy starts, Array.copy ends
            let found = m inner i (fun _ -> true)

            if negated then
                // (what a negative lookahead captured does not count)
                Array.blit (fst saved) 0 starts 0 starts.Length
                Array.blit (snd saved) 0 ends 0 ends.Length
                not found && k i
            else
                found && k i
        | Look(true, negated, inner) ->
            let mutable found = false
            let mutable j = i

            while not found && j >= 0 do
                if m inner j (fun e -> e = i) then
                    found <- true

                j <- j - 1

            (found <> negated) && k i
        | BackRef(g, fold) ->
            if g >= n || starts.[g] < 0 then
                // (a group that took no part matches nothing, as in .NET)
                false
            else
                let s = starts.[g]
                let l = ends.[g] - s
                let mutable ok = i + l <= len
                let mutable q = 0

                while ok && q < l do
                    if not (sameChar fold input.[i + q] input.[s + q]) then
                        ok <- false

                    q <- q + 1

                ok && k (i + l)
        | NamedBackRef _ -> false

    let mutable result = None
    let mutable start = startAt

    while result.IsNone && start <= len do
        for g in 0 .. starts.Length - 1 do
            starts.[g] <- -1
            ends.[g] <- -1

        let s = start

        if
            m
                re.root
                s
                (fun e ->
                    starts.[0] <- s
                    ends.[0] <- e
                    true
                )
        then
            result <- Some(Array.copy starts, Array.copy ends)

        start <- start + 1

    result

let private makeMatch (re: RegexOf) (input: string) (found: (int[] * int[]) option) : MatchOf =
    let n = max re.names.Length 1

    match found with
    | Some(starts, ends) ->
        {
            regex = re
            input = input
            groups =
                Array.init
                    n
                    (fun g ->
                        if starts.[g] >= 0 then
                            {
                                success = true
                                index = starts.[g]
                                length = ends.[g] - starts.[g]
                                value = input.Substring(starts.[g], ends.[g] - starts.[g])
                                name =
                                    if g < re.names.Length then
                                        re.names.[g]
                                    else
                                        "0"
                            }
                        else
                            {
                                success = false
                                index = 0
                                length = 0
                                value = ""
                                name =
                                    if g < re.names.Length then
                                        re.names.[g]
                                    else
                                        "0"
                            }
                    )
        }
    | None ->
        {
            regex = re
            input = input
            groups =
                [|
                    {
                        success = false
                        index = 0
                        length = 0
                        value = ""
                        name = "0"
                    }
                |]
        }

let private checkStart (input: string) (startAt: int) =
    if isNull input then
        raise (System.ArgumentNullException("input", "Value cannot be null."))

    if startAt < 0 || startAt > input.Length then
        raise (
            System.ArgumentOutOfRangeException(
                "startat",
                "Start index cannot be less than 0 or greater than input length."
            )
        )

let matchFrom (re: RegexOf) (input: string) (startAt: int) : MatchOf =
    checkStart input startAt
    makeMatch re input (search re input startAt)

let matchOf (re: RegexOf) (input: string) : MatchOf = matchFrom re input 0

let isMatchFrom (re: RegexOf) (input: string) (startAt: int) : bool =
    checkStart input startAt
    (search re input startAt).IsSome

let isMatch (re: RegexOf) (input: string) : bool = isMatchFrom re input 0

/// The matches one after the other: after an empty one the next is looked for one further on
let private allMatches (re: RegexOf) (input: string) (startAt: int) : MatchOf list =
    let found = ResizeArray<MatchOf>()
    let mutable at = startAt
    let mutable go = true

    while go && at <= input.Length do
        match search re input at with
        | Some(starts, ends) ->
            found.Add(makeMatch re input (Some(starts, ends)))

            at <-
                if ends.[0] = starts.[0] then
                    ends.[0] + 1
                else
                    ends.[0]
        | None -> go <- false

    listOf found

let matchesFrom (re: RegexOf) (input: string) (startAt: int) : MatchCollectionOf =
    checkStart input startAt
    { matches = Array.ofList (allMatches re input startAt) }

let matches (re: RegexOf) (input: string) : MatchCollectionOf = matchesFrom re input 0

/// `m.NextMatch()`
let nextMatch (m: MatchOf) : MatchOf =
    let g = m.groups.[0]

    if not g.success then
        m
    else
        let at =
            if g.length = 0 then
                g.index + 1
            else
                g.index + g.length

        if at > m.input.Length then
            makeMatch m.regex m.input None
        else
            makeMatch m.regex m.input (search m.regex m.input at)

// ---- Match, Group and the collections ----

let groups (m: MatchOf) : GroupCollectionOf = { items = m.groups }
let matchGroup (m: MatchOf) : GroupOf = m.groups.[0]
let groupSuccess (g: GroupOf) = g.success
let groupIndex (g: GroupOf) = g.index
let groupLength (g: GroupOf) = g.length
let groupValue (g: GroupOf) = g.value
let groupName (g: GroupOf) = g.name
let groupToString (g: GroupOf) = g.value

let private noGroup (name: string) : GroupOf =
    {
        success = false
        index = 0
        length = 0
        value = ""
        name = name
    }

let groupsCount (c: GroupCollectionOf) = c.items.Length

let groupAt (c: GroupCollectionOf) (i: int) : GroupOf =
    if i >= 0 && i < c.items.Length then
        c.items.[i]
    else
        noGroup (string i)

let groupNamed (c: GroupCollectionOf) (name: string) : GroupOf =
    match c.items |> Array.tryFind (fun g -> g.name = name) with
    | Some g -> g
    | None -> noGroup name

#if FABLE_COMPILER
let groupsToSeq (c: GroupCollectionOf) : Fable.Library.Zig.Seq.SeqOf<GroupOf> = Fable.Library.Zig.Seq.ofArray c.items
#else
let groupsToSeq (c: GroupCollectionOf) : seq<GroupOf> = Seq.ofArray c.items
#endif

let matchesCount (c: MatchCollectionOf) = c.matches.Length

let matchAt (c: MatchCollectionOf) (i: int) : MatchOf =
    if i < 0 || i >= c.matches.Length then
        raise (System.ArgumentOutOfRangeException("i", "Specified argument was out of the range of valid values."))

    c.matches.[i]

#if FABLE_COMPILER
let matchesToSeq (c: MatchCollectionOf) : Fable.Library.Zig.Seq.SeqOf<MatchOf> = Fable.Library.Zig.Seq.ofArray c.matches
#else
let matchesToSeq (c: MatchCollectionOf) : seq<MatchOf> = Seq.ofArray c.matches
#endif

let options (re: RegexOf) = re.options
let pattern (re: RegexOf) = re.pattern
let toString (re: RegexOf) = re.pattern

let getGroupNames (re: RegexOf) : string[] = Array.copy re.names

let getGroupNumbers (re: RegexOf) : int[] = Array.init re.names.Length id

// ---- Replace and Split ----

/// The text of `replacement` for a match: `$1`, `${name}`, `$0` and `$&`, `` $` ``, `$'`, `$+`,
/// `$_`, `$$`
let private substitute (re: RegexOf) (m: MatchOf) (replacement: string) : string =
    let sb = System.Text.StringBuilder()
    let mutable i = 0
    let r = replacement
    let count = re.names.Length

    while i < r.Length do
        let c = r.[i]

        if c = '$' && i + 1 < r.Length then
            let d = r.[i + 1]

            if d = '$' then
                sb.Append('$') |> ignore
                i <- i + 2
            elif d = '&' then
                sb.Append(m.groups.[0].value) |> ignore
                i <- i + 2
            elif d = '`' then
                sb.Append(m.input.Substring(0, m.groups.[0].index)) |> ignore
                i <- i + 2
            elif d = '\'' then
                let g = m.groups.[0]
                sb.Append(m.input.Substring(g.index + g.length)) |> ignore
                i <- i + 2
            elif d = '_' then
                sb.Append(m.input) |> ignore
                i <- i + 2
            elif d = '+' then
                if m.groups.Length > 1 then
                    sb.Append(m.groups.[m.groups.Length - 1].value) |> ignore

                i <- i + 2
            elif System.Char.IsDigit d then
                // (all the digits are the group's number; .NET does not take a shorter one when
                // that is not a group: the `$` is then kept as it is)
                let mutable j = i + 1
                let mutable v = 0

                while j < r.Length && System.Char.IsDigit r.[j] && v < 100000 do
                    v <- v * 10 + (int r.[j] - int '0')
                    j <- j + 1

                if v < count then
                    sb.Append(m.groups.[v].value) |> ignore
                    i <- j
                else
                    sb.Append('$') |> ignore
                    i <- i + 1
            elif d = '{' then
                let close = r.IndexOf('}', i + 2)

                if close > 0 then
                    let name = r.Substring(i + 2, close - i - 2)

                    match re.names |> Array.tryFindIndex (fun x -> x = name) with
                    | Some g ->
                        sb.Append(m.groups.[g].value) |> ignore
                        i <- close + 1
                    | None ->
                        sb.Append('$') |> ignore
                        i <- i + 1
                else
                    sb.Append('$') |> ignore
                    i <- i + 1
            else
                sb.Append('$') |> ignore
                i <- i + 1
        else
            sb.Append(c) |> ignore
            i <- i + 1

    sb.ToString()

/// Replace `count` matches (all for -1) from `startAt` with what `f` makes of each
let private replaceBy (re: RegexOf) (input: string) (f: MatchOf -> string) (count: int) (startAt: int) : string =
    if isNull input then
        raise (System.ArgumentNullException("input", "Value cannot be null."))

    if count < -1 then
        raise (System.ArgumentOutOfRangeException("count", "Count cannot be less than -1."))

    checkStart input startAt

    if count = 0 then
        input
    else
        let ms = allMatches re input startAt

        let ms =
            if count > 0 then
                List.truncate count ms
            else
                ms

        match ms with
        | [] -> input
        | _ ->
            let sb = System.Text.StringBuilder()
            let mutable prev = 0

            for m in ms do
                let g = m.groups.[0]
                sb.Append(input.Substring(prev, g.index - prev)) |> ignore
                sb.Append(f m) |> ignore
                prev <- g.index + g.length

            sb.Append(input.Substring prev) |> ignore
            sb.ToString()

let replaceFrom (re: RegexOf) (input: string) (replacement: string) (count: int) (startAt: int) : string =
    if isNull replacement then
        raise (System.ArgumentNullException("replacement", "Value cannot be null."))

    replaceBy re input (fun m -> substitute re m replacement) count startAt

let replace (re: RegexOf) (input: string) (replacement: string) : string = replaceFrom re input replacement -1 0

let replaceCount (re: RegexOf) (input: string) (replacement: string) (count: int) : string =
    replaceFrom re input replacement count 0

let replaceWithFrom (re: RegexOf) (input: string) (evaluator: MatchOf -> string) (count: int) (startAt: int) : string =
    replaceBy re input evaluator count startAt

let replaceWith (re: RegexOf) (input: string) (evaluator: MatchOf -> string) : string =
    replaceBy re input evaluator -1 0

let replaceWithCount (re: RegexOf) (input: string) (evaluator: MatchOf -> string) (count: int) : string =
    replaceBy re input evaluator count 0

/// `Split`: the text between `count - 1` matches at most (all for 0), each followed by what its
/// groups captured
let splitFrom (re: RegexOf) (input: string) (count: int) (startAt: int) : string[] =
    if isNull input then
        raise (System.ArgumentNullException("input", "Value cannot be null."))

    if count < 0 then
        raise (System.ArgumentOutOfRangeException("count", "Count cannot be less than -1."))

    checkStart input startAt

    if count = 1 then
        [| input |]
    else
        let ms = allMatches re input startAt

        let ms =
            if count > 1 then
                List.truncate (count - 1) ms
            else
                ms

        match ms with
        | [] -> [| input |]
        | _ ->
            let parts = ResizeArray<string>()
            let mutable prev = 0

            for m in ms do
                let g = m.groups.[0]
                parts.Add(input.Substring(prev, g.index - prev))
                prev <- g.index + g.length

                for k in 1 .. m.groups.Length - 1 do
                    if m.groups.[k].success then
                        parts.Add(m.groups.[k].value)

            parts.Add(input.Substring prev)
            parts.ToArray()

let split (re: RegexOf) (input: string) : string[] = splitFrom re input 0 0
let splitCount (re: RegexOf) (input: string) (count: int) : string[] = splitFrom re input count 0

// ---- Escape and Unescape ----

let escape (s: string) : string =
    if isNull s then
        raise (System.ArgumentNullException("str", "Value cannot be null."))

    let sb = System.Text.StringBuilder()

    for c in s do
        match c with
        | '\\'
        | '*'
        | '+'
        | '?'
        | '|'
        | '{'
        | '['
        | '('
        | ')'
        | '^'
        | '$'
        | '.'
        | '#'
        | ' ' -> sb.Append('\\').Append(c) |> ignore
        | '\t' -> sb.Append("\\t") |> ignore
        | '\n' -> sb.Append("\\n") |> ignore
        | '\r' -> sb.Append("\\r") |> ignore
        | '\012' -> sb.Append("\\f") |> ignore
        | _ -> sb.Append(c) |> ignore

    sb.ToString()

let unescape (s: string) : string =
    if isNull s then
        raise (System.ArgumentNullException("str", "Value cannot be null."))

    let sb = System.Text.StringBuilder()
    let mutable i = 0

    let hexAt (start: int) (n: int) =
        let mutable v = 0

        for k in start .. start + n - 1 do
            let c = s.[k]

            let d =
                if c >= '0' && c <= '9' then
                    int c - int '0'
                elif c >= 'a' && c <= 'f' then
                    int c - int 'a' + 10
                elif c >= 'A' && c <= 'F' then
                    int c - int 'A' + 10
                else
                    raise (System.ArgumentException("Insufficient or invalid hexadecimal digits."))

            v <- v * 16 + d

        char v

    while i < s.Length do
        let c = s.[i]

        if c = '\\' && i + 1 < s.Length then
            let e = s.[i + 1]
            i <- i + 2

            match e with
            | 'n' -> sb.Append('\n') |> ignore
            | 'r' -> sb.Append('\r') |> ignore
            | 't' -> sb.Append('\t') |> ignore
            | 'f' -> sb.Append('\012') |> ignore
            | 'v' -> sb.Append('\011') |> ignore
            | 'a' -> sb.Append('\007') |> ignore
            | 'e' -> sb.Append('\027') |> ignore
            | 'b' -> sb.Append('\b') |> ignore
            | 'x' ->
                sb.Append(hexAt i 2) |> ignore
                i <- i + 2
            | 'u' ->
                sb.Append(hexAt i 4) |> ignore
                i <- i + 4
            | _ when System.Char.IsLetterOrDigit e ->
                raise (System.ArgumentException("Unrecognized escape sequence \\" + string e + "."))
            | _ -> sb.Append(e) |> ignore
        else
            sb.Append(c) |> ignore
            i <- i + 1

    sb.ToString()

// ---- a Match as the Group it also is ----

let matchSuccess (m: MatchOf) = m.groups.[0].success
let matchIndex (m: MatchOf) = m.groups.[0].index
let matchLength (m: MatchOf) = m.groups.[0].length
let matchValue (m: MatchOf) = m.groups.[0].value
let matchName (m: MatchOf) = m.groups.[0].name
