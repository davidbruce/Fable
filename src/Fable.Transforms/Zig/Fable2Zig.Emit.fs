/// Emission: ownership IR -> Zig source text.
module Fable.Transforms.Zig.Emit

open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Fable.Transforms.Zig.IR

let zigKeywords =
    set
        [
            "addrspace"
            "align"
            "allowzero"
            "and"
            "anyframe"
            "anytype"
            "asm"
            "break"
            "callconv"
            "catch"
            "comptime"
            "const"
            "continue"
            "defer"
            "else"
            "enum"
            "errdefer"
            "error"
            "export"
            "extern"
            "fn"
            "for"
            "if"
            "inline"
            "linksection"
            "noalias"
            "noinline"
            "nosuspend"
            "opaque"
            "or"
            "orelse"
            "packed"
            "pub"
            "resume"
            "return"
            "struct"
            "suspend"
            "switch"
            "test"
            "threadlocal"
            "try"
            "union"
            "unreachable"
            "var"
            "volatile"
            "while"
            "bool"
            "void"
            "type"
            "true"
            "false"
            "null"
            "undefined"
            "anyerror"
            "noreturn"
            "usize"
            "isize"
            "f16"
            "f32"
            "f64"
            "f80"
            "f128"
            "c_int"
            "c_uint"
            "c_long"
            "c_char"
            "comptime_int"
            "comptime_float"
            "anyopaque"
            "std"
            "main"
            "fable_rt"
        ]

/// Zig reserves `i<N>` and `u<N>` for every N.
let isReservedIdent (s: string) =
    zigKeywords.Contains s || Regex.IsMatch(s, "^[iu][0-9]+$")

let cleanIdent (s: string) =
    let s = Regex.Replace(s, "[^A-Za-z0-9_]", "_")

    if s = "" then
        "v"
    elif System.Char.IsDigit s[0] then
        "_" + s
    else
        s

/// The Zig name of a module-level declaration.
let topIdent (s: string) =
    let c = cleanIdent s

    if isReservedIdent c then
        c + "_"
    else
        c

/// The Zig name of a field or of a union case.
let fieldIdent (s: string) =
    let c = cleanIdent s

    if isReservedIdent c then
        $"@\"%s{c}\""
    else
        c

type Dest =
    | DReturn
    | DBreak of string
    | DDiscard

type Em =
    {
        Out: StringBuilder
        Names: Dictionary<int, string>
        Used: HashSet<string>
        Mutated: Set<int>
        mutable Counter: int
    }

let freshName (em: Em) (baseName: string) =
    let b = cleanIdent baseName

    let b =
        if isReservedIdent b then
            b + "_"
        else
            b

    let mutable n = b
    let mutable i = 1

    while em.Used.Contains n do
        n <- $"%s{b}_%d{i}"
        i <- i + 1

    em.Used.Add n |> ignore
    n

let vname (em: Em) (v: Var) =
    match v.Kind with
    | VGlobal -> topIdent v.Base
    | _ ->
        match em.Names.TryGetValue v.Id with
        | true, n -> n
        | _ ->
            let n = freshName em v.Base
            em.Names[v.Id] <- n
            n

let line (em: Em) (ind: string) (s: string) =
    em.Out.Append(ind).AppendLine(s) |> ignore

/// "(a < b)" -> "a < b" when the outer parentheses enclose the whole string.
let unparen (s: string) =
    if s.Length >= 2 && s[0] = '(' && s[s.Length - 1] = ')' then
        let mutable depth = 0
        let mutable closesEarly = false

        for i in 0 .. s.Length - 2 do
            if s[i] = '(' then
                depth <- depth + 1
            elif s[i] = ')' then
                depth <- depth - 1

                if depth = 0 then
                    closesEarly <- true

        if closesEarly then
            s
        else
            s.Substring(1, s.Length - 2)
    else
        s

/// A function or type of this file, or `alias.name` for one that another file declares.
let callTarget (f: string) =
    match f.IndexOf '.' with
    | -1 -> topIdent f
    | i -> f.Substring(0, i + 1) + topIdent (f.Substring(i + 1))

let rec zigType (t: Ty) : string =
    match t with
    | TPrim s -> s
    | TEnt e -> callTarget e.Name
    | TOpt t -> "?" + zigType t
    | TTuple ts -> ts |> List.map zigType |> String.concat ", " |> sprintf "@Tuple(&.{ %s })"
    | TPtr(t, c) ->
        (if c then
             "*const "
         else
             "*")
        + zigType t
    | TSlice(t, c) ->
        (if c then
             "[]const "
         else
             "[]")
        + zigType t
    | TArr(t, n) -> $"[%d{n}]%s{zigType t}"
    | TFn _ -> "anytype"
    | TTok(e, c) -> $"?*%s{e.Name}_%s{c}"

let rec ex (em: Em) (e: Expr) : string =
    match e with
    | EVar v -> vname em v
    | ELit(s, _) -> s
    | EUnit -> "{}"
    | EPrim(op, xs, t) ->
        let a = xs |> List.map (ex em)

        let argT =
            match xs with
            | x :: _ -> typeOf x
            | [] -> t

        let isFloat = isFloatTy argT
        // .NET arithmetic wraps on overflow
        let wrap o =
            if isFloat then
                o
            else
                o + "%"

        // .NET masks the shift count to the width of the shifted value
        let shiftCount (y: string) =
            $"@intCast(%s{y} & %d{max 1 (intBits argT) - 1})"

        match op, a with
        | "add", [ x; y ] -> $"""(%s{x} %s{wrap "+"} %s{y})"""
        | "sub", [ x; y ] -> $"""(%s{x} %s{wrap "-"} %s{y})"""
        | "mul", [ x; y ] -> $"""(%s{x} %s{wrap "*"} %s{y})"""
        | "div", [ x; y ] ->
            if isFloat then
                $"(%s{x} / %s{y})"
            else
                $"@divTrunc(%s{x}, %s{y})"
        | "mod", [ x; y ] -> $"@rem(%s{x}, %s{y})"
        | "neg", [ x ] ->
            if isFloat then
                $"(-%s{x})"
            else
                $"(-%%%s{x})"
        | "lt", [ x; y ] -> $"(%s{x} < %s{y})"
        | "gt", [ x; y ] -> $"(%s{x} > %s{y})"
        | "le", [ x; y ] -> $"(%s{x} <= %s{y})"
        | "ge", [ x; y ] -> $"(%s{x} >= %s{y})"
        | "eq", [ x; y ] -> $"(%s{x} == %s{y})"
        | "ne", [ x; y ] -> $"(%s{x} != %s{y})"
        | "not", [ x ] -> $"(!%s{x})"
        | "bnot", [ x ] -> $"(~%s{x})"
        | "band", [ x; y ] -> $"(%s{x} & %s{y})"
        | "bor", [ x; y ] -> $"(%s{x} | %s{y})"
        | "bxor", [ x; y ] -> $"(%s{x} ^ %s{y})"
        | "shl", [ x; y ] -> $"(%s{x} << %s{shiftCount y})"
        | "shr", [ x; y ] -> $"(%s{x} >> %s{shiftCount y})"
        | "eql", [ x; y ] -> $"std.meta.eql(%s{x}, %s{y})"
        | "tag", [ x ] -> $"@as(i32, @intFromEnum(%s{x}))"
        // (the source type is spelled out: a literal has no type of its own in Zig)
        | "conv", [ x ] -> $"fable_rt.conv(%s{zigType t}, @as(%s{zigType argT}, %s{x}))"
        | _ -> fail None "internal: unknown primitive %s/%d" op a.Length
    | ECall(f, xs, _) ->
        let args = xs |> List.map (ex em) |> String.concat ", "
        $"%s{callTarget f}(%s{args})"
    | ECon(t, case, xs, _) ->
        let args = xs |> List.map (ex em)

        let inits (fs: (string * Ty) list) =
            List.zip fs args
            |> List.map (fun ((f, _), a) -> $".%s{fieldIdent f} = %s{a}")
            |> String.concat ", "

        match t with
        | TEnt e when e.Kind = KRecord -> $"%s{zigType t}{{ %s{inits (caseFields t case)} }}"
        | TEnt _ when args.IsEmpty -> $"@as(%s{zigType t}, .%s{fieldIdent case})"
        | TEnt _ -> $"%s{zigType t}{{ .%s{fieldIdent case} = .{{ %s{inits (caseFields t case)} }} }}"
        | TOpt _ ->
            if case = "Some" then
                $"@as(%s{zigType t}, %s{args.Head})"
            else
                $"@as(%s{zigType t}, null)"
        | TTuple _ -> args |> String.concat ", " |> sprintf "@as(%s, .{ %s })" (zigType t)
        | _ -> fail None "internal: bad constructor"
    | EGet(x, p, _) ->
        let o = ex em x

        match p with
        | PField f -> $"%s{o}.%s{fieldIdent f}"
        | PCase(c, f) -> $"%s{o}.%s{fieldIdent c}.%s{fieldIdent f}"
        | PItem i -> $"%s{o}[%d{i}]"
        | PSome -> o + ".?"
    | ETest(x, c, t) ->
        match t with
        | TOpt _ ->
            let op =
                if c = "Some" then
                    "!="
                else
                    "=="

            $"(%s{ex em x} %s{op} null)"
        | _ -> $"(%s{ex em x} == .%s{fieldIdent c})"
    | EIf(c, t, f, _) when isFlat c && isFlat t && isFlat f -> simpleIf em c t f
    | _ -> fail None "internal: this expression is not part of the Zig target yet"

and simpleIf (em: Em) (c: Expr) (t: Expr) (f: Expr) =
    match t, f with
    | _, ELit("false", _) -> $"(%s{ex em c} and %s{ex em t})"
    | ELit("true", _), _ -> $"(%s{ex em c} or %s{ex em f})"
    | _ -> $"if (%s{unparen (ex em c)}) %s{ex em t} else %s{ex em f}"

/// `x = x op y` -> `x op= y` (wrapping operators for integers).
let assignText (em: Em) (lhs: string) (rhs: Expr) =
    match rhs with
    | EPrim(("add" | "sub" | "mul") as op, [ a; b ], t) when isFlat a && ex em a = lhs ->
        let sym =
            match op with
            | "add" -> "+"
            | "sub" -> "-"
            | _ -> "*"

        let wrap =
            if isFloatTy t then
                ""
            else
                "%"

        $"%s{lhs} %s{sym}%s{wrap}= %s{ex em b};"
    | _ -> $"%s{lhs} = %s{ex em rhs};"

let isSimpleIf (e: Expr) =
    match e with
    | EIf(c, t, f, ty) -> isFlat c && isFlat t && isFlat f && not (isVoid ty)
    | _ -> false

/// After a statement that has no value: leave through `dest` if that is where control goes.
let finishUnit (em: Em) (ind: string) (dest: Dest) =
    match dest with
    | DBreak l -> line em ind $"break :%s{l} {{}};"
    | DReturn
    | DDiscard -> ()

let rec stmt (em: Em) (ind: string) (e: Expr) (dest: Dest) : unit =
    let L = line em ind

    let block (rhs: Expr) (openLine: string -> string) =
        em.Counter <- em.Counter + 1
        let lbl = $"blk%d{em.Counter}"
        L(openLine lbl)
        stmt em (ind + "    ") rhs (DBreak lbl)
        L "};"

    match e with
    | ELet(v, rhs, body) ->
        if not ((fv body).Contains v.Id) then
            if isFlat rhs then
                let s = ex em rhs

                if isVoid (typeOf rhs) then
                    (match rhs with
                     | EUnit -> ()
                     | _ -> L(s + ";"))
                elif not (isPure rhs) then
                    L $"_ = %s{s};"
            else
                stmt em ind rhs DDiscard
        else
            let name = vname em v

            let kw =
                if em.Mutated.Contains v.Id then
                    "var"
                else
                    "const"

            if isFlat rhs || isSimpleIf rhs then
                L $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{ex em rhs};"
            else
                block rhs (fun lbl -> $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{lbl}: {{")

        stmt em ind body dest
    | ESeq(a, b) ->
        stmt em ind a DDiscard
        stmt em ind b dest
    | EIf _ when isSimpleIf e && dest <> DDiscard -> emitValue em ind e dest
    | EIf(c, t, f, _) ->
        L $"if (%s{unparen (ex em c)}) {{"
        stmt em (ind + "    ") t dest

        match f, dest with
        | EUnit, DDiscard -> L "}"
        | _ ->
            L "} else {"
            stmt em (ind + "    ") f dest
            L "}"
    | EWhile(c, b) ->
        L $"while (%s{unparen (ex em c)}) {{"
        stmt em (ind + "    ") b DDiscard
        L "}"
        finishUnit em ind dest
    | EFor(i, a, b, up, body) ->
        let iname = vname em i
        let endName = freshName em (iname + "_end")

        let cmp, step =
            if up then
                "<=", "+="
            else
                ">=", "-="

        // the bound is evaluated once; the loop variable does not overflow past it
        L "{"
        L $"    const %s{endName}: %s{zigType i.Ty} = %s{ex em b};"
        L $"    var %s{iname}: %s{zigType i.Ty} = %s{ex em a};"
        L $"    while (%s{iname} %s{cmp} %s{endName}) {{"
        stmt em (ind + "        ") body DDiscard
        L $"        if (%s{iname} == %s{endName}) break;"
        L $"        %s{iname} %s{step} 1;"
        L "    }"
        L "}"
        finishUnit em ind dest
    | EAssign(v, rhs) ->
        if isFlat rhs || isSimpleIf rhs then
            L(assignText em (vname em v) rhs)
        else
            block rhs (fun lbl -> $"%s{vname em v} = %s{lbl}: {{")

        finishUnit em ind dest
    | _ -> emitValue em ind e dest

and emitValue (em: Em) (ind: string) (e: Expr) (dest: Dest) =
    let L = line em ind

    match dest with
    | DReturn ->
        if isVoid (typeOf e) then
            (match e with
             | EUnit -> ()
             | _ -> L(ex em e + ";"))
        else
            L $"return %s{ex em e};"
    | DBreak l ->
        if isVoid (typeOf e) then
            (match e with
             | EUnit -> ()
             | _ -> L(ex em e + ";"))

            L $"break :%s{l} {{}};"
        else
            L $"break :%s{l} %s{ex em e};"
    | DDiscard ->
        match e with
        | EUnit -> ()
        | _ when isVoid (typeOf e) -> L(ex em e + ";")
        | _ when isPure e -> ()
        | _ -> L $"_ = %s{ex em e};"

/// Zig rejects a parameter that is never used.
let ensureUsed (names: string list) (body: string) =
    names
    |> List.filter (fun n -> not (Regex.IsMatch(body, $@"(?<![\w.])%s{Regex.Escape n}\b")))
    |> List.map (fun n -> $"    _ = %s{n};\n")
    |> String.concat ""

let emitFunction (out: StringBuilder) (rootNames: HashSet<string>) (fn: FnInfo) =
    let em =
        {
            Out = StringBuilder()
            Names = Dictionary()
            Used = HashSet(rootNames)
            Mutated = assignedIn fn.Body
            Counter = 0
        }

    let ps = fn.Params |> List.map (fun p -> vname em p, p)
    stmt em "    " fn.Body DReturn
    let bodyText = em.Out.ToString()

    let sigParams =
        ps |> List.map (fun (n, p) -> $"%s{n}: %s{zigType p.Ty}") |> String.concat ", "

    out
        .AppendLine($"pub fn %s{topIdent fn.Name}(%s{sigParams}) %s{zigType fn.Ret} {{")
        .Append(ensureUsed (ps |> List.map fst) bodyText)
        .Append(bodyText)
        .AppendLine("}")
        .AppendLine()
    |> ignore

/// The text of one file, without its imports (their paths are only known to the writer).
let emitFile (state: FileState) : string =
    let out = StringBuilder()
    let rootNames = HashSet<string>()

    for (name, _, _) in state.Consts do
        rootNames.Add(topIdent name) |> ignore

    for fn in state.Fns do
        rootNames.Add(topIdent fn.Name) |> ignore

    for alias in state.Imports.Values do
        rootNames.Add alias |> ignore

    for e in state.LocalEnts do
        rootNames.Add(topIdent e.Name) |> ignore

    for e in state.LocalEnts do
        let fields (fs: (string * Ty) list) =
            fs |> List.map (fun (f, t) -> $"%s{fieldIdent f}: %s{zigType t}")

        match e.Kind with
        | KRecord ->
            out.AppendLine($"pub const %s{topIdent e.Name} = struct {{") |> ignore

            for f in fields (caseFields (TEnt e) "") do
                out.AppendLine($"    %s{f},") |> ignore
        | _ ->
            out.AppendLine($"pub const %s{topIdent e.Name} = union(enum) {{") |> ignore

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"    %s{fieldIdent c},") |> ignore
                else
                    let payload = fields fs |> String.concat ", "
                    out.AppendLine($"    %s{fieldIdent c}: struct {{ %s{payload} }},") |> ignore

        out.AppendLine("};").AppendLine() |> ignore

    for (name, ty, text) in state.Consts do
        out.AppendLine($"pub const %s{topIdent name}: %s{zigType ty} = %s{text};")
        |> ignore

    if state.Consts.Count > 0 then
        out.AppendLine() |> ignore

    for fn in state.Fns do
        emitFunction out rootNames fn

    // The F# entry point returns the process exit code as an int; Zig's `main` returns a u8.
    for fn in state.Fns do
        if fn.IsEntryPoint then
            out.AppendLine("pub fn main() u8 {") |> ignore

            if isVoid fn.Ret then
                out.AppendLine($"    %s{topIdent fn.Name}();").AppendLine("    return 0;")
                |> ignore
            else
                out.AppendLine($"    return @truncate(@as(u32, @bitCast(@as(i32, %s{topIdent fn.Name}()))));")
                |> ignore

            out.AppendLine("}") |> ignore

    out.ToString()
