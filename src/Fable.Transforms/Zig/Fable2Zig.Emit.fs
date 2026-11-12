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

/// A function whose self tail calls are compiled as a loop.
type LoopInfo =
    {
        Self: string
        Params: Var list
        /// tail recursion modulo cons: the result is built top-down through a destination
        Trmc: bool
    }

type Em =
    {
        Out: StringBuilder
        Names: Dictionary<int, string>
        Used: HashSet<string>
        Mutated: Set<int>
        Loop: LoopInfo option
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

/// The entry of a function that other files call when managed values are passed or returned:
/// it owns its arguments and its result, whatever the function itself was inferred to borrow.
/// (`$` cannot be part of a name that comes from F#.)
let ownedEntry (f: string) =
    match f.IndexOf '.' with
    | -1 -> $"@\"%s{topIdent f}$owned\""
    | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$owned\""

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
    | TTok(e, c) -> $"?*fable_rt.Cell(%s{callTarget e.Name}, .%s{fieldIdent c})"

let dupCode (x: string) = $"fable_rt.dup(%s{x})"
let dropCode (x: string) = $"fable_rt.drop(%s{x});"

/// The field of a case, read from a value.
let projAccess (t: Ty) (case: string) (field: string) (x: string) =
    match t with
    | TTuple _ -> $"%s{x}[%s{field}]"
    | TOpt _ -> x + ".?"
    | TEnt e when e.Kind = KRecord -> $"%s{x}.%s{fieldIdent field}"
    | _ -> $"%s{x}.%s{fieldIdent case}.%s{fieldIdent field}"

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
        // (values that hold cells are compared through them)
        | "eql", [ x; y ] ->
            if isManaged argT then
                $"fable_rt.eql(%s{x}, %s{y})"
            else
                $"std.meta.eql(%s{x}, %s{y})"
        | "tag", [ x ] -> $"@as(i32, @intFromEnum(%s{x}))"
        // (the source type is spelled out: a literal has no type of its own in Zig)
        | "conv", [ x ] -> $"fable_rt.conv(%s{zigType t}, @as(%s{zigType argT}, %s{x}))"
        | _ -> fail None "internal: unknown primitive %s/%d" op a.Length
    | ECall(f, xs, t) ->
        let args = xs |> List.map (ex em) |> String.concat ", "

        let target =
            if f.Contains "." && (isManaged t || xs |> List.exists (typeOf >> isManaged)) then
                ownedEntry f
            else
                callTarget f

        $"%s{target}(%s{args})"
    | EEmit(macro, xs, _) ->
        let args = xs |> List.map (ex em) |> Array.ofList

        Regex.Replace(
            macro,
            @"\$(\d+)",
            fun m ->
                let i = int m.Groups[1].Value

                if i < args.Length then
                    args[i]
                else
                    fail None "Emit: there is no argument $%d" i
        )
    | ECon(t, case, xs, tok) ->
        let args = xs |> List.map (ex em)

        let inits (fs: (string * Ty) list) =
            List.zip fs args
            |> List.map (fun ((f, _), a) -> $".%s{fieldIdent f} = %s{a}")
            |> String.concat ", "

        match t with
        | TEnt e when e.Kind = KRecord -> $"%s{zigType t}{{ %s{inits (caseFields t case)} }}"
        | TEnt _ when args.IsEmpty -> $"@as(%s{zigType t}, .%s{fieldIdent case})"
        | TEnt e when e.Kind = KHeapUnion ->
            let init = $".{{ %s{inits (caseFields t case)} }}"
            let c = fieldIdent case

            let cell =
                match tok with
                | Some tk -> $"fable_rt.cellReuse(%s{zigType t}, .%s{c}, &%s{vname em tk}, %s{init})"
                | None -> $"fable_rt.cell(%s{zigType t}, .%s{c}, %s{init})"

            $"%s{zigType t}{{ .%s{c} = %s{cell} }}"
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
    | EDup(x, _) -> dupCode (ex em x)
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

/// The expressions a function can end with.
let rec tailSites (e: Expr) : Expr list =
    match e with
    | ELet(_, ECall _, ECon _) -> [ e ]
    | ELet(_, _, b)
    | ESeq(_, b)
    | EDrop(_, b)
    | EUnpack(_, b)
    | EPromote(_, b) -> tailSites b
    | EIf(_, t, f, _) -> tailSites t @ tailSites f
    | _ -> [ e ]

let private countUses (id: int) (es: Expr list) =
    let mutable n = 0

    let rec go e =
        match e with
        | EVar v when v.Id = id -> n <- n + 1
        | _ -> List.iter go (flatKids e)

    List.iter go es
    n

/// `let r = self(args) in Case(..., r, ...)` at the end of a function: the cell is made first,
/// with a hole where `r` goes, and the recursive call becomes the next turn of a loop that
/// fills the hole.
let trmcSite (self: string) (e: Expr) =
    match e with
    | ELet(r, ECall(f, args, _), ECon(TEnt ent, case, conArgs, tok)) when
        f = self && ent.Kind = KHeapUnion && not conArgs.IsEmpty
        ->
        let hits =
            conArgs
            |> List.indexed
            |> List.filter (fun (_, a) ->
                match a with
                | EVar v -> v.Id = r.Id
                | _ -> false
            )

        match hits with
        | [ (i, _) ] when countUses r.Id conArgs = 1 -> Some(args, ent, case, conArgs, tok, i)
        | _ -> None
    | _ -> None

/// After a statement that has no value: leave through `dest` if that is where control goes.
let finishUnit (em: Em) (ind: string) (dest: Dest) =
    match dest with
    | DReturn when em.Loop.IsSome -> line em ind "return;"
    | DBreak l -> line em ind $"break :%s{l} {{}};"
    | DReturn
    | DDiscard -> ()

/// A self tail call: give the parameters their new values and go round the loop again.
let emitTailJump (em: Em) (ind: string) (args: Expr list) =
    let loop = em.Loop.Value

    let changes =
        List.zip loop.Params args
        |> List.filter (fun (p, a) ->
            match a with
            | EVar v -> v.Id <> p.Id
            | _ -> true
        )

    match changes with
    | [ (p, a) ] -> line em ind $"%s{vname em p} = %s{ex em a};"
    | _ ->
        // every new argument is evaluated before any parameter is overwritten
        let temps =
            changes |> List.map (fun (p, a) -> p, freshName em ("next_" + p.Base), a)

        for (_, t, a) in temps do
            line em ind $"const %s{t} = %s{ex em a};"

        for (p, t, _) in temps do
            line em ind $"%s{vname em p} = %s{t};"

    line em ind "continue :tail;"

/// A dead value whose case is known: the fields that are still needed move out of it, the
/// others are dropped, and a cell is freed or kept to be built in again.
let emitUnpack (em: Em) (ind: string) (u: Unpack) =
    let L = line em ind
    let x = vname em u.Scrut

    let moves =
        u.Moves
        |> List.map (fun (f, v) -> $"%s{f} -> %s{vname em v}")
        |> String.concat ", "

    if u.Heap then
        let cell = $"%s{x}.%s{fieldIdent u.Case}"

        let fate =
            if u.Token.IsSome then
                "the cell is kept to be built in again"
            else
                "the cell is freed"

        L $"// `%s{x}` is dead: [%s{moves}] move out and %s{fate}, if it is not shared"

        match u.Token with
        | Some tk ->
            let tn = vname em tk
            let dead = freshName em "dead"
            L $"var %s{tn}: %s{zigType tk.Ty} = null;"
            L $"defer if (%s{tn}) |%s{dead}| fable_rt.free(%s{dead});"
        | None -> ()

        L $"if (fable_rt.isUnique(%s{cell})) {{"

        for (f, _) in u.Drops do
            L("    " + dropCode $"%s{cell}.%s{fieldIdent f}")

        match u.Token with
        | Some tk -> L $"    %s{vname em tk} = %s{cell};"
        | None -> L $"    fable_rt.free(%s{cell});"

        L "} else {"

        for (_, v) in u.Moves do
            if isManaged v.Ty then
                L $"    _ = %s{dupCode (vname em v)};"

        L $"    fable_rt.release(%s{cell});"
        L "}"
    elif not u.Drops.IsEmpty then
        L $"// `%s{x}` is dead: [%s{moves}] move out, the rest is dropped"

        for (f, _) in u.Drops do
            L(dropCode (projAccess u.Scrut.Ty u.Case f x))

let rec stmt (em: Em) (ind: string) (e: Expr) (dest: Dest) : unit =
    let L = line em ind

    let block (rhs: Expr) (openLine: string -> string) =
        em.Counter <- em.Counter + 1
        let lbl = $"blk%d{em.Counter}"
        L(openLine lbl)
        stmt em (ind + "    ") rhs (DBreak lbl)
        L "};"

    match e with
    | ELet _ when dest = DReturn && em.Loop.IsSome && (trmcSite em.Loop.Value.Self e).IsSome ->
        let (args, ent, case, conArgs, tok, holeIdx) = (trmcSite em.Loop.Value.Self e).Value

        let t = callTarget ent.Name
        let c = fieldIdent case
        let fields = caseFields (TEnt ent) case

        let inits =
            List.zip fields conArgs
            |> List.mapi (fun i ((f, _), a) ->
                let value =
                    if i = holeIdx then
                        "undefined"
                    else
                        ex em a

                $".%s{fieldIdent f} = %s{value}"
            )
            |> String.concat ", "

        let cell = freshName em "cell"

        match tok with
        | Some tk -> L $"const %s{cell} = fable_rt.cellReuse(%s{t}, .%s{c}, &%s{vname em tk}, .{{ %s{inits} }});"
        | None -> L $"const %s{cell} = fable_rt.cell(%s{t}, .%s{c}, .{{ %s{inits} }});"

        L "// link the new cell into the hole, then loop on the recursive call"
        L $"hole.* = .{{ .%s{c} = %s{cell} }};"
        L $"hole = &%s{cell}.%s{fieldIdent (fst fields[holeIdx])};"
        emitTailJump em ind args
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
    // (where a loop function ends, each branch is a statement: one of them may be the jump)
    | EIf _ when isSimpleIf e && dest <> DDiscard && not (dest = DReturn && em.Loop.IsSome) -> emitValue em ind e dest
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
    | EDrop(v, k) ->
        L(dropCode (vname em v))
        stmt em ind k dest
    | EUnpack(u, k) ->
        emitUnpack em ind u
        stmt em ind k dest
    | EPromote(v, k) ->
        L $"_ = %s{dupCode (vname em v)}; // this borrow outlives its owner"
        stmt em ind k dest
    | _ -> emitValue em ind e dest

and emitValue (em: Em) (ind: string) (e: Expr) (dest: Dest) =
    let L = line em ind

    let effect () =
        match e with
        | EUnit -> ()
        | _ -> L(ex em e + ";")

    match dest with
    | DReturn ->
        match em.Loop, e with
        | Some loop, ECall(f, args, _) when f = loop.Self -> emitTailJump em ind args
        | Some loop, _ when loop.Trmc ->
            L $"hole.* = %s{ex em e};"
            L "return result;"
        | _ ->
            if isVoid (typeOf e) then
                effect ()

                if em.Loop.IsSome then
                    L "return;"
            else
                L $"return %s{ex em e};"
    | DBreak l ->
        if isVoid (typeOf e) then
            effect ()
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

let private hasManaged (fn: FnInfo) =
    isManaged fn.Ret || fn.Params |> List.exists (fun p -> isManaged p.Ty)

let emitFunction (out: StringBuilder) (rootNames: HashSet<string>) (fn: FnInfo) =
    // Is there a self call, or `let r = self(..) in Case(.., r, ..)`, where the function ends?
    let sites = tailSites fn.Body

    let selfTail =
        sites
        |> List.exists (
            function
            | ECall(f, _, _) -> f = fn.Name
            | _ -> false
        )

    let trmc = sites |> List.exists (fun s -> (trmcSite fn.Name s).IsSome)

    let reassigned =
        sites
        |> List.collect (fun s ->
            let args =
                match s, trmcSite fn.Name s with
                | _, Some(a, _, _, _, _, _) -> a
                | ECall(f, a, _), _ when f = fn.Name -> a
                | _ -> []

            if args.IsEmpty then
                []
            else
                List.zip fn.Params args
                |> List.choose (fun (p, a) ->
                    match a with
                    | EVar v when v.Id = p.Id -> None
                    | _ -> Some p.Id
                )
        )
        |> Set.ofList

    let loop =
        if selfTail || trmc then
            Some
                {
                    Self = fn.Name
                    Params = fn.Params
                    Trmc = trmc
                }
        else
            None

    let em =
        {
            Out = StringBuilder()
            Names = Dictionary()
            Used = HashSet(rootNames)
            Mutated = assignedIn fn.Body
            Loop = loop
            Counter = 0
        }

    let ps =
        fn.Params
        |> List.map (fun p ->
            let n = vname em p

            let sigName =
                if reassigned.Contains p.Id then
                    freshName em (n + "_in")
                else
                    n

            sigName, n, p
        )

    for (s, n, _) in ps do
        if s <> n then
            line em "    " $"var %s{n} = %s{s};"

    match loop with
    | Some l ->
        if l.Trmc then
            line em "    " $"var result: %s{zigType fn.Ret} = undefined;"
            line em "    " $"var hole: *%s{zigType fn.Ret} = &result;"

        line em "    " "tail: while (true) {"
        stmt em "        " fn.Body DReturn
        line em "    " "}"
    | None -> stmt em "    " fn.Body DReturn

    let bodyText = em.Out.ToString()

    let sigParams =
        ps
        |> List.map (fun (s, _, p) -> $"%s{s}: %s{zigType p.Ty}")
        |> String.concat ", "

    let modes =
        List.zip fn.Params fn.Modes
        |> List.choose (fun (p, m) ->
            match m with
            | MOwned -> Some(p.Base + ": owned")
            | MBorrowed -> Some(p.Base + ": borrowed")
            | MPlain -> None
        )

    let modes =
        match fn.RetFrom with
        | Some _ -> modes @ [ "result: borrowed" ]
        | None -> modes

    if not modes.IsEmpty then
        out.AppendLine($"""/// ownership: %s{String.concat ", " modes}""") |> ignore

    if trmc then
        out.AppendLine("/// tail recursion modulo cons: a loop that builds the result top-down")
        |> ignore
    elif selfTail then
        out.AppendLine("/// self tail call: a loop") |> ignore

    out
        .AppendLine($"pub fn %s{topIdent fn.Name}(%s{sigParams}) %s{zigType fn.Ret} {{")
        .Append(ensureUsed (ps |> List.map (fun (s, _, _) -> s)) bodyText)
        .Append(bodyText)
        .AppendLine("}")
    |> ignore

    // What other files call when managed values are passed or returned: they cannot know what
    // this function was inferred to borrow, so this entry owns its arguments and its result.
    if hasManaged fn then
        let entry = ownedEntry fn.Name
        let name = topIdent fn.Name

        let borrowed =
            List.zip ps fn.Modes
            |> List.choose (fun ((s, _, _), m) ->
                if m = MBorrowed then
                    Some s
                else
                    None
            )

        if borrowed.IsEmpty && fn.RetFrom.IsNone then
            out.AppendLine($"pub const %s{entry} = %s{name};") |> ignore
        else
            let args = ps |> List.map (fun (s, _, _) -> s) |> String.concat ", "
            let call = $"%s{name}(%s{args})"

            out.AppendLine($"pub fn %s{entry}(%s{sigParams}) %s{zigType fn.Ret} {{")
            |> ignore

            if isVoid fn.Ret then
                out.AppendLine($"    %s{call};") |> ignore
            elif fn.RetFrom.IsSome then
                out.AppendLine($"    const r = %s{dupCode call};") |> ignore
            else
                out.AppendLine($"    const r = %s{call};") |> ignore

            for s in borrowed do
                out.AppendLine("    " + dropCode s) |> ignore

            if not (isVoid fn.Ret) then
                out.AppendLine("    return r;") |> ignore

            out.AppendLine("}") |> ignore

    out.AppendLine() |> ignore

/// The text of one file, without its imports (their paths are only known to the writer).
let emitFile (state: FileState) : string =
    let out = StringBuilder()
    let rootNames = HashSet<string>([ "r"; "result"; "hole"; "tail" ])

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
        | KValueUnion ->
            out.AppendLine($"pub const %s{topIdent e.Name} = union(enum) {{") |> ignore

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"    %s{fieldIdent c},") |> ignore
                else
                    let payload = fields fs |> String.concat ", "
                    out.AppendLine($"    %s{fieldIdent c}: struct {{ %s{payload} }},") |> ignore
        | KHeapUnion ->
            // a case with fields points to a reference-counted cell; one without needs none
            out.AppendLine($"pub const %s{topIdent e.Name} = union(enum) {{") |> ignore

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"    %s{fieldIdent c},") |> ignore
                else
                    let payload = "@\"$rc\": u32 = 1" :: fields fs |> String.concat ", "
                    out.AppendLine($"    %s{fieldIdent c}: *struct {{ %s{payload} }},") |> ignore

        out.AppendLine("};").AppendLine() |> ignore

    for (name, ty, text) in state.Consts do
        out.AppendLine($"pub const %s{topIdent name}: %s{zigType ty} = %s{text};")
        |> ignore

    if state.Consts.Count > 0 then
        out.AppendLine() |> ignore

    for fn in state.Fns do
        try
            emitFunction out rootNames fn
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    // The F# entry point returns the process exit code as an int; Zig's `main` returns a u8.
    // In builds that count cells, a program that ends with cells still allocated says so.
    for fn in state.Fns do
        if fn.IsEntryPoint then
            out.AppendLine("pub fn main() u8 {") |> ignore

            if isVoid fn.Ret then
                out.AppendLine($"    %s{topIdent fn.Name}();").AppendLine("    const code: i32 = 0;")
                |> ignore
            else
                out.AppendLine($"    const code: i32 = %s{topIdent fn.Name}();") |> ignore

            out
                .AppendLine("    if (fable_rt.leaked()) return 70;")
                .AppendLine("    return @truncate(@as(u32, @bitCast(code)));")
                .AppendLine("}")
            |> ignore

    out.ToString()
