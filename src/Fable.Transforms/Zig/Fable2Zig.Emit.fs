/// Emission: ownership IR -> Zig source text.
module Fable.Transforms.Zig.Emit

open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Fable.Transforms.Zig.IR

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
        /// a value without fields of the result type: when such a function is left by an
        /// exception, the hole is filled with it so that what was built so far can be dropped
        Plug: string option
    }

/// The code of a function value: it takes the environment and then the arguments, which it
/// owns, and calls the function `Target`.
type Adapter =
    {
        Name: string
        Target: string
        TypeArgs: Ty list
        NCaptures: int
        /// the types of the captured values (needed for a function of another file)
        CaptureTys: Ty list
        FnTy: Ty
        /// the type parameters of the surrounding function that the types above mention: the
        /// adapter is generic in them
        Gens: string list
    }

type Em =
    {
        Out: StringBuilder
        Names: Dictionary<int, string>
        Used: HashSet<string>
        Mutated: Set<int>
        Loop: LoopInfo option
        /// the function being emitted, and the functions of the file by name
        Self: FnInfo
        Fns: Dictionary<string, FnInfo>
        /// a call that ends the function can be a jump (see `tailTarget`)
        CanTail: bool
        /// the labels of the `try` bodies around the code being emitted
        TryLabels: Stack<string>
        /// the code of the function values made so far
        Adapters: Dictionary<string, Adapter>
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
    | VGlobal ->
        // (`alias.name`: a value of another file)
        match v.Base.LastIndexOf '.' with
        | -1 -> topIdent v.Base
        | dot -> v.Base.Substring(0, dot + 1) + topIdent (v.Base.Substring(dot + 1))
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

/// The constant that states what a function borrows, for the calls from other files (which
/// are compiled without seeing the function). `$` cannot be part of a name that comes from F#.
let sigName (f: string) =
    match f.IndexOf '.' with
    | -1 -> $"@\"%s{topIdent f}$sig\""
    | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$sig\""

/// A type parameter. (`'` cannot be part of a name that comes from F#, so a type parameter
/// never has the name of a value.)
let genName (n: string) = $"@\"'%s{n}\""

let rec zigType (t: Ty) : string =
    match t with
    | TPrim s -> s
    | TEnt(e, []) -> callTarget e.Name
    | TEnt(e, args) ->
        args
        |> List.map zigType
        |> String.concat ", "
        |> sprintf "%s(%s)" (callTarget e.Name)
    | TGen n -> genName n
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
    // (a function value may raise, whatever function is behind it)
    | TFn(args, ret) ->
        let ps = "?*fable_rt.Env" :: (args |> List.map zigType) |> String.concat ", "
        $"fable_rt.Func(*const fn (%s{ps}) fable_rt.Raised!%s{zigType ret})"
    | TTok(t, c) -> $"?*fable_rt.Cell(%s{zigType t}, .%s{fieldIdent c})"

/// A function with its type arguments: a generic function is a Zig function from types to a
/// namespace that holds the function itself, as `call`.
let fnRef (f: string) (typeArgs: Ty list) =
    match typeArgs with
    | [] -> callTarget f
    | _ ->
        typeArgs
        |> List.map zigType
        |> String.concat ", "
        |> sprintf "%s(%s).call" (callTarget f)

/// The namespace of an adapter, where it is used.
let adapterRef (a: Adapter) =
    match a.Gens with
    | [] -> a.Name
    | gens -> gens |> List.map genName |> String.concat ", " |> sprintf "%s(%s)" a.Name

/// The result type of a function: `Raised!T` if it can raise, `T` if it cannot, and if that
/// depends on functions of other files, a type that Zig works out from theirs.
let retType (fn: FnInfo) : string =
    match fn.Raises with
    | RNever -> zigType fn.Ret
    | RAlways -> $"fable_rt.Raised!%s{zigType fn.Ret}"
    | RDepends callees ->
        let refs = callees |> List.map (fun (f, tys) -> fnRef f tys) |> String.concat ", "
        $"fable_rt.MayRaise(%s{zigType fn.Ret}, .{{ %s{refs} }})"

/// Whether the cells of a type can be part of a cycle, as Zig text: yes, no, or for a generic
/// type whose own declaration says no, whether one of its type arguments holds such a cell.
/// (Nothing when it is a plain no: the cells then have no field for the collector at all.)
let cyclicDecl (e: Ent) : string option =
    if e.Cyclic then
        Some "true"
    else
        // (a type that can reach a function value or an exception is cyclic if those can be
        // part of a cycle in this program, which the root file says)
        let parts =
            [
                if e.ReachesOpaque then
                    "fable_rt.functions_in_cycles"
                for g in e.TypeParams do
                    $"fable_rt.holdsCyclic(%s{genName g})"
            ]

        match parts with
        | [] -> None
        | _ -> Some(String.concat " or " parts)

/// The fields that every cell starts with: its count, and the collector's header if the type
/// can be part of a cycle.
let cellHeader (e: Ent) : string list =
    match cyclicDecl e with
    | Some _ -> [ "@\"$rc\": u32 = 1"; "@\"$gc\": fable_rt.GcHdr(fable_cyclic) = undefined" ]
    | None -> [ "@\"$rc\": u32 = 1" ]

let dupCode (x: string) = $"fable_rt.dup(%s{x})"
let dropCode (x: string) = $"fable_rt.drop(%s{x});"

/// The field of a case, read from a value.
let projAccess (t: Ty) (case: string) (field: string) (x: string) =
    match t with
    | TTuple _ -> $"%s{x}[%s{field}]"
    | TOpt _ -> x + ".?"
    | TEnt(e, _) when e.Kind = KRecord -> $"%s{x}.%s{fieldIdent field}"
    | _ -> $"%s{x}.%s{fieldIdent case}.%s{fieldIdent field}"

let rec ex (em: Em) (e: Expr) : string =
    match e with
    | EVar v -> vname em v
    | ELit(s, _) -> s
    | EUnit -> "{}"
    | EPrim(op, xs, t) ->
        // (an operation of literals only would be computed by Zig without bounds, as
        // comptime_int: the first is given its type, so that it wraps as on .NET)
        let a =
            match xs with
            | ELit(s, (TPrim p as ty)) :: rest when
                (intBits ty > 0 || isFloatTy ty)
                && rest
                   |> List.forall (
                       function
                       | ELit _ -> true
                       | _ -> false
                   )
                ->
                $"@as(%s{p}, %s{s})" :: (rest |> List.map (ex em))
            | _ -> xs |> List.map (ex em)

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
            // (a `None` or `[]` that F# generalized has the type of the other side)
            let x, y, argT =
                match xs with
                | [ xe; ye ] when typeOf xe <> typeOf ye ->
                    let rec placeholder (t: Ty) =
                        match t with
                        | TPrim "void" -> true
                        | TOpt t -> placeholder t
                        | TEnt(_, args) -> args |> List.exists placeholder
                        | _ -> false

                    if placeholder (typeOf ye) then
                        x, $"fable_rt.emptyAs(%s{zigType (typeOf xe)}, %s{y})", typeOf xe
                    elif placeholder (typeOf xe) then
                        $"fable_rt.emptyAs(%s{zigType (typeOf ye)}, %s{x})", y, typeOf ye
                    else
                        x, y, argT
                | _ -> x, y, argT

            if isManaged argT || holdsDecimal argT then
                $"fable_rt.eql(%s{x}, %s{y})"
            else
                $"std.meta.eql(%s{x}, %s{y})"
        | "tag", [ x ] -> $"@as(i32, @intFromEnum(%s{x}))"
        // (the source type is spelled out: a literal has no type of its own in Zig)
        | "conv", [ x ] -> $"fable_rt.conv(%s{zigType t}, @as(%s{zigType argT}, %s{x}))"
        | _ -> fail None "internal: unknown primitive %s/%d" op a.Length
    | ECall(f, typeArgs, xs, t) ->
        if f.Contains "." && (isManaged t || xs |> List.exists (typeOf >> isManaged)) then
            // A function of another file: this file does not know what it borrows, so the call
            // says what the caller does with each argument and `across` settles the rest when
            // the Zig is compiled.
            let uses, args =
                xs
                |> List.map (fun x ->
                    if not (isManaged (typeOf x)) then
                        ".plain", ex em x
                    else
                        match x with
                        | EDup(inner, _) -> ".keep", ex em inner
                        | _ -> ".give", ex em x
                )
                |> List.unzip

            let tuple (items: string list) =
                match items with
                | [] -> ".{}"
                | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

            $"fable_rt.across(%s{fnRef f typeArgs}, %s{sigName f}, %s{tuple uses}, %s{tuple args})"
        else
            let args = xs |> List.map (ex em) |> String.concat ", "
            $"%s{fnRef f typeArgs}(%s{args})"
    | ECallClo(f, xs, _) ->
        let fn = ex em f
        let args = $"%s{fn}.env" :: (xs |> List.map (ex em)) |> String.concat ", "
        $"%s{fn}.code(%s{args})"
    | EClosure(target, typeArgs, caps, ty) ->
        let key = target + "<" + (typeArgs |> List.map tyKey |> String.concat ",") + ">"

        let adapter =
            match em.Adapters.TryGetValue key with
            | true, a -> a
            | _ ->
                let a =
                    {
                        Name = $"@\"%s{target}$fn%d{em.Adapters.Count}\""
                        Target = target
                        TypeArgs = typeArgs
                        NCaptures = caps.Length
                        CaptureTys = caps |> List.map typeOf
                        FnTy = ty
                        Gens = freeGens (ty :: typeArgs @ (caps |> List.map typeOf))
                    }

                em.Adapters[key] <- a
                a

        let ns = adapterRef adapter

        if caps.IsEmpty then
            $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code }}"
        else
            let inits =
                caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

            $"fable_rt.closure(%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code)"
    | EExnNew(ent, xs) ->
        let fields = caseFields (TEnt(ent, [])) ""

        if fields.Length <> xs.Length then
            fail
                None
                "internal: the exception %s has %d field(s) and is made with %d value(s)"
                ent.Name
                fields.Length
                xs.Length

        let inits =
            List.zip fields (xs |> List.map (ex em))
            |> List.map (fun ((f, _), a) -> $".%s{fieldIdent f} = %s{a}")
            |> String.concat ", "

        if inits = "" then
            $"%s{callTarget ent.Name}.new(.{{}})"
        else
            $"%s{callTarget ent.Name}.new(.{{ %s{inits} }})"
    | EExnTest(x, ent) -> $"%s{callTarget ent.Name}.is(%s{ex em x})"
    | EExnGet(x, ent, f, _) -> $"%s{callTarget ent.Name}.of(%s{ex em x}).%s{fieldIdent f}"
    // A call that may raise: on its error edge the function gives up what it still owns and
    // leaves, to the handler of the enclosing `try` or to its own caller.
    | EOnRaise(call, ds) ->
        let c = ex em call
        let edge = edgeText em ds

        let definite =
            match call with
            | ECallClo _
            | ERt _ -> true
            | ECall(f, _, _, _) ->
                match em.Fns.TryGetValue f with
                | true, g -> g.Raises = RAlways
                | _ -> false
            | _ -> false

        if definite then
            $"(%s{c} catch %s{edge})"
        else
            // whether this function raises is only known when the Zig is compiled
            em.Counter <- em.Counter + 1
            let lbl = $"call%d{em.Counter}"
            let raw = freshName em "raw"

            $"(%s{lbl}: {{ const %s{raw} = %s{c}; break :%s{lbl} if (comptime fable_rt.isRaised(@TypeOf(%s{raw}))) (%s{raw} catch %s{edge}) else %s{raw}; }})"
    | EEmit(macro, xs, ty)
    | ERt(macro, xs, ty) ->
        let args = xs |> List.map (ex em) |> Array.ofList
        // (`$R` in a call into the runtime library is the type of its result)
        let macro = macro.Replace("$R", zigType ty)

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
        | TEnt(e, _) when e.Kind = KRefRecord -> $"fable_rt.new(%s{zigType t}, .{{ %s{inits (caseFields t case)} }})"
        | TEnt(e, _) when e.Kind = KRecord -> $"%s{zigType t}{{ %s{inits (caseFields t case)} }}"
        | TEnt _ when args.IsEmpty -> $"@as(%s{zigType t}, .%s{fieldIdent case})"
        | TEnt(e, _) when e.Kind = KHeapUnion ->
            let init = $".{{ %s{inits (caseFields t case)} }}"
            let c = fieldIdent case

            let cell =
                match tok with
                | Some tk -> $"fable_rt.cellReuse(%s{zigType t}, .%s{c}, &%s{vname em tk}, %s{init})"
                | None -> $"fable_rt.cell(%s{zigType t}, .%s{c}, %s{init})"

            $"%s{zigType t}{{ .%s{c} = %s{cell} }}"
        | TEnt _ -> $"%s{zigType t}{{ .%s{fieldIdent case} = .{{ %s{inits (caseFields t case)} }} }}"
        | TOpt inner ->
            if case = "Some" then
                match inner with
                // (`Some None`: the inner null is given its type, or Zig would take it for the
                // outer one)
                | TOpt _ -> $"@as(%s{zigType t}, @as(%s{zigType inner}, %s{args.Head}))"
                | _ -> $"@as(%s{zigType t}, %s{args.Head})"
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
    // (`&x` and what a byref points at)
    | EAddr(x, _) -> "&" + ex em x
    | EDeref(x, _) -> ex em x + ".*"
    | EIf(c, t, f, _) when isFlat c && isFlat t && isFlat f -> simpleIf em c t f
    | _ -> fail None "internal: this expression is not part of the Zig target yet"

/// How the function is left when an exception is in flight.
and leaveText (em: Em) : string =
    if em.TryLabels.Count > 0 then
        $"break :%s{em.TryLabels.Peek()};"
    else
        match em.Loop with
        | Some {
                   Trmc = true
                   Plug = Some plug
               } -> $"hole.* = %s{plug}; fable_rt.drop(result); return error.Raised;"
        | _ -> "return error.Raised;"

and edgeText (em: Em) (ds: Var list) : string =
    let drops =
        ds |> List.map (fun d -> dropCode (vname em d) + " ") |> String.concat ""

    $"{{ %s{drops}%s{leaveText em} }}"

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
    | ELet(_, (ECall _ | EOnRaise(ECall _, _)), ECon _) -> [ e ]
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
    // (a recursive call that may raise needs no error edge of its own once it is the next
    // turn of the loop)
    | ELet(r, (ECall(f, _, args, _) | EOnRaise(ECall(f, _, args, _), _)), ECon(conTy, case, conArgs, tok)) when
        f = self && isHeapTy conTy && not conArgs.IsEmpty
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
        | [ (i, _) ] when countUses r.Id conArgs = 1 -> Some(args, conTy, case, conArgs, tok, i)
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

        let mayBeCyclic =
            match u.Scrut.Ty with
            | TEnt(ent, _) -> (cyclicDecl ent).IsSome
            | _ -> false

        L $"if (fable_rt.isUnique(%s{cell})) {{"

        // (the collector is told first: what the cell holds stops being held by its structure,
        // whether it is given up or moved out)
        if mayBeCyclic then
            L $"    fable_rt.forget(%s{cell});"

        for (f, _) in u.Drops do
            L("    " + dropCode $"%s{cell}.%s{fieldIdent f}")

        for (_, v) in u.Moves do
            if isManaged v.Ty && mayHoldCyclic v.Ty then
                L $"    fable_rt.touch(%s{vname em v});"

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
        let (args, conTy, case, conArgs, tok, holeIdx) =
            (trmcSite em.Loop.Value.Self e).Value

        let t = zigType conTy
        let c = fieldIdent case
        let fields = caseFields conTy case

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
    // (where a function ends, each branch is a statement if one of them may be a jump)
    | EIf(_, t, f, _) when
        isSimpleIf e
        && dest <> DDiscard
        && not (
            dest = DReturn
            && (em.Loop.IsSome || (tailTarget em t).IsSome || (tailTarget em f).IsSome)
        )
        ->
        emitValue em ind e dest
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
    // A field that owns its value: the old value is given up once the new one is in place.
    | EStore(lv, rhs) ->
        let place = ex em lv

        let value =
            if isFlat rhs || isSimpleIf rhs then
                ex em rhs
            else
                let stored = freshName em "stored"
                block rhs (fun lbl -> $"const %s{stored}: %s{zigType (typeOf lv)} = %s{lbl}: {{")
                stored

        match lv with
        // (a field of an object: the collector is told through the object's header)
        | EGet(EEmit(m, [ o ], TPtr _), PField _, _) when
            isManaged (typeOf lv)
            && m.StartsWith("fable_rt.objPart(", System.StringComparison.Ordinal)
            ->
            L $"fable_rt.objStore(%s{ex em o}, &%s{place}, %s{value});"
        // (a field of a reference record: the collector is told, a cycle may be closed here)
        | EGet(owner, PField f, _) when
            isManaged (typeOf lv)
            && (
                match typeOf owner with
                | TEnt({ Kind = KRefRecord }, _) -> true
                | _ -> false
            )
            ->
            L $"fable_rt.storeIn(%s{ex em owner}, \"%s{f}\", %s{value});"
        | _ when isManaged (typeOf lv) -> L $"fable_rt.store(&%s{place}, %s{value});"
        | _ -> L $"%s{place} = %s{value};"

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
    | ERaise(x, _) ->
        L $"fable_rt.throw(%s{ex em x});"
        L(leaveText em)
    | ETry(body, exV, handler, ty) ->
        em.Counter <- em.Counter + 1
        let okL = $"try%d{em.Counter}"
        let errL = $"raised%d{em.Counter}"
        // (the body and the handler go to a buffer first, to see which labels are used)
        let inner = { em with Out = StringBuilder() }
        em.TryLabels.Push errL

        try
            stmt inner (ind + "        ") body (DBreak okL)
        finally
            em.TryLabels.Pop() |> ignore

        let bodyText = inner.Out.ToString()
        let raises = bodyText.Contains $"break :%s{errL};"
        inner.Out.Clear() |> ignore

        if raises then
            line inner ind $"    %s{errL}: {{"
            inner.Out.Append(bodyText) |> ignore
            line inner ind "    }"
            // the handler owns the exception
            line inner ind $"    const %s{vname inner exV}: fable_rt.Exn = fable_rt.take();"
            stmt inner (ind + "    ") handler (DBreak okL)
        else
            inner.Out.Append(bodyText) |> ignore

        em.Counter <- inner.Counter
        let text = inner.Out.ToString()

        if not (text.Contains $"break :%s{okL} ") then
            // (every path raises again or returns: nothing comes after the `try`)
            L "{"
            em.Out.Append(text) |> ignore
            L "}"
        elif isVoid ty then
            L $"%s{okL}: {{"
            em.Out.Append(text) |> ignore
            L "}"
            finishUnit em ind dest
        else
            let tried = freshName em "tried"
            L $"const %s{tried}: %s{zigType ty} = %s{okL}: {{"
            em.Out.Append(text) |> ignore
            L "};"
            emitValue em ind (ELit(tried, ty)) dest
    | _ -> emitValue em ind e dest

/// A call of another function of the file that ends this one can be a jump instead of a call
/// when nothing is left to do after it (no result to store through a destination pointer, no
/// dead cell waiting to be freed) and the two functions have the same parameter and result
/// types, all of them numbers, booleans or chars: the callee then runs in the caller's frame.
/// (Zig passes and returns records and unions through pointers into the caller's frame, which
/// a jump would leave dangling, so such signatures stay calls.) Functions that call each other
/// last (`even`/`odd`, state machines over numbers) then run in constant stack, as on .NET.
and tailTarget (em: Em) (e: Expr) : string option =
    let isScalar (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    match e with
    | ECall(f, typeArgs, args, _) when em.CanTail && f <> em.Self.Name ->
        match em.Fns.TryGetValue f with
        | true, g ->
            let inst =
                if g.TypeParams.Length = typeArgs.Length then
                    Map.ofList (List.zip g.TypeParams typeArgs)
                else
                    Map.empty

            let calleeParams = g.Params |> List.map (fun p -> substTy inst p.Ty)
            let callerParams = em.Self.Params |> List.map (fun p -> p.Ty)
            let calleeRet = substTy inst g.Ret

            let same =
                g.Raises = RNever
                && List.forall isScalar (calleeRet :: calleeParams)
                && List.map zigType calleeParams = List.map zigType callerParams
                && zigType calleeRet = zigType em.Self.Ret

            if same then
                let tuple =
                    match args with
                    | [] -> ".{}"
                    | _ -> args |> List.map (ex em) |> String.concat ", " |> sprintf ".{ %s }"

                Some $"@call(fable_rt.tail_call, %s{fnRef f typeArgs}, %s{tuple})"
            else
                None
        | _ -> None
    | _ -> None

and emitValue (em: Em) (ind: string) (e: Expr) (dest: Dest) =
    let L = line em ind

    let effect () =
        match e with
        | EUnit -> ()
        | _ -> L(ex em e + ";")

    match dest with
    | DReturn ->
        match em.Loop, e with
        | Some loop, (ECall(f, _, args, _) | EOnRaise(ECall(f, _, args, _), _)) when f = loop.Self ->
            emitTailJump em ind args
        | Some loop, _ when loop.Trmc ->
            L $"hole.* = %s{ex em e};"
            L "return result;"
        | _ when (tailTarget em e).IsSome -> L $"return %s{(tailTarget em e).Value};"
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
        // (a local that is only discarded is still used, or Zig would reject it)
        | EVar _ -> L $"_ = %s{ex em e};"
        | _ when isPure e -> ()
        | _ -> L $"_ = %s{ex em e};"

/// Zig rejects a parameter that is never used.
let ensureUsed (names: string list) (body: string) =
    // (a name inside a string literal is not a use of it)
    let code = Regex.Replace(body, "\"(?:[^\"\\\\]|\\\\.)*\"", "\"\"")

    names
    |> List.filter (fun n -> not (Regex.IsMatch(code, $@"(?<![\w.])%s{Regex.Escape n}\b")))
    |> List.map (fun n -> $"    _ = %s{n};\n")
    |> String.concat ""

/// The variables that hold a value record of which a field is assigned (they are declared
/// with `var`; a reference record is assigned through its pointer).
let private storedInto (body: Expr) : Set<int> =
    let found = HashSet<int>()

    let rec root (e: Expr) =
        match e with
        | EVar v ->
            match v.Ty with
            | TEnt({ Kind = KRefRecord }, _) -> ()
            | _ -> found.Add v.Id |> ignore
        | EGet(x, _, _) ->
            match typeOf x with
            | TEnt({ Kind = KRefRecord }, _) -> ()
            | _ -> root x
        | _ -> ()

    exists
        (function
        | EStore(lv, _) ->
            root lv
            false
        | _ -> false)
        body
    |> ignore

    Set.ofSeq found

let private hasManaged (fn: FnInfo) =
    isManaged fn.Ret || fn.Params |> List.exists (fun p -> isManaged p.Ty)

/// The `[<StackArena>]` functions of the file being written.
let mutable private currentArenas = Dictionary<string, int>()

let emitFunction
    (out: StringBuilder)
    (rootNames: HashSet<string>)
    (adapters: Dictionary<string, Adapter>)
    (fns: Dictionary<string, FnInfo>)
    (fn: FnInfo)
    =
    // Is there a self call, or `let r = self(..) in Case(.., r, ..)`, where the function ends?
    let sites = tailSites fn.Body

    let selfTail =
        sites
        |> List.exists (
            function
            | ECall(f, _, _, _)
            | EOnRaise(ECall(f, _, _, _), _) -> f = fn.Name
            | _ -> false
        )

    // (When the function can be left by an exception, what it has built so far must be
    // droppable: that takes a value without fields to put in the hole.)
    let plug =
        allCases fn.Ret
        |> List.tryFind (fun c -> isHeapTy fn.Ret && (caseFields fn.Ret c).IsEmpty)
        |> Option.map (fun c -> $"@as(%s{zigType fn.Ret}, .%s{fieldIdent c})")

    let trmc =
        sites |> List.exists (fun s -> (trmcSite fn.Name s).IsSome)
        && (fn.Raises = RNever || plug.IsSome)

    let reassigned =
        sites
        |> List.collect (fun s ->
            let args =
                match s, trmcSite fn.Name s with
                | _, Some(a, _, _, _, _, _) -> a
                | (ECall(f, _, a, _) | EOnRaise(ECall(f, _, a, _), _)), _ when f = fn.Name -> a
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
                    Plug = plug
                }
        else
            None

    let em =
        {
            Out = StringBuilder()
            Names = Dictionary()
            Used = HashSet(rootNames)
            Mutated =
                // (a variable whose address is taken to be assigned through is a `var` too)
                let addressed = HashSet<int>()

                exists
                    (fun x ->
                        match x with
                        | EAddr(EVar v, false) -> addressed.Add v.Id |> ignore
                        | _ -> ()

                        false
                    )
                    fn.Body
                |> ignore

                Set.unionMany [ assignedIn fn.Body; storedInto fn.Body; Set.ofSeq addressed ]
            Loop = loop
            Self = fn
            Fns = fns
            TryLabels = Stack()
            CanTail =
                not trmc
                && fn.Raises = RNever
                && not (
                    exists
                        (function
                        | EUnpack(u, _) -> u.Token.IsSome
                        | _ -> false)
                        fn.Body
                )
            Adapters = adapters
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

    // `[<StackArena(bytes)>]`: the function's cells come from a buffer on its stack
    let bodyText =
        match currentArenas.TryGetValue fn.Name with
        | true, bytes ->
            $"    var fable_arena_buffer: [%d{bytes}]u8 align(16) = undefined;\n"
            + "    var fable_arena_fba = std.heap.FixedBufferAllocator.init(&fable_arena_buffer);\n"
            + "    const fable_arena = fable_rt.arenaEnter(&fable_arena_fba);\n"
            + "    defer fable_rt.arenaLeave(fable_arena);\n"
            + bodyText
        | _ -> bodyText

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

    let visibility =
        if fn.IsLocal then
            ""
        else
            "pub "

    let unused = ensureUsed (ps |> List.map (fun (s, _, _) -> s)) bodyText

    match fn.TypeParams with
    | [] ->
        out
            .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{sigParams}) %s{retType fn} {{")
            .Append(unused)
            .Append(bodyText)
            .AppendLine("}")
        |> ignore
    | typeParams ->
        // A generic function: a Zig function from its type arguments to a namespace that holds
        // the function, so that `name(i32).call` is an ordinary function.
        let comptimeParams =
            typeParams
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        let indented (text: string) =
            text.Split('\n')
            |> Array.map (fun l ->
                if l = "" then
                    l
                else
                    "        " + l
            )
            |> String.concat "\n"

        // (a function lifted out of a generic one has its type parameters, and may not use
        // them all)
        let signature = $"%s{sigParams} %s{retType fn}"

        let discards =
            typeParams
            |> List.filter (fun g ->
                let name = genName g
                not (bodyText.Contains name || signature.Contains name)
            )
            |> List.map (fun g -> $"    _ = %s{genName g};\n")
            |> String.concat ""

        out
            .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{comptimeParams}) type {{")
            .Append(discards)
            .AppendLine("    return struct {")
            .AppendLine($"        pub fn call(%s{sigParams}) %s{retType fn} {{")
            .Append(indented unused)
            .Append(indented bodyText)
            .AppendLine("        }")
            .AppendLine("    };")
            .AppendLine("}")
        |> ignore

    // What the function borrows, for the calls from other files.
    if hasManaged fn && not fn.IsLocal then
        let borrows =
            match fn.Modes with
            | [] -> ".{}"
            | modes ->
                modes
                |> List.map (fun m ->
                    if m = MBorrowed then
                        "true"
                    else
                        "false"
                )
                |> String.concat ", "
                |> sprintf ".{ %s }"

        let resultBorrowed =
            if fn.RetFrom.IsSome then
                "true"
            else
                "false"

        out.AppendLine(
            $"pub const %s{sigName fn.Name} = .{{ .borrows = %s{borrows}, .result_borrowed = %s{resultBorrowed} }};"
        )
        |> ignore

    out.AppendLine() |> ignore

/// The code of a function value. A function value owns its arguments and its result, and what
/// it captured stays in its environment; the function it calls may have been inferred to
/// borrow some of that, so this is where the two are brought together.
let emitAdapter (out: StringBuilder) (fns: Dictionary<string, FnInfo>) (a: Adapter) =
    let argTys, ret =
        match a.FnTy with
        | TFn(args, ret) -> args, ret
        | _ -> fail None "internal: not a function type"

    let ps = argTys |> List.mapi (fun i t -> $"a%d{i}", t)

    let sigParams =
        "env: ?*fable_rt.Env"
        :: (ps |> List.map (fun (n, t) -> $"%s{n}: %s{zigType t}"))
        |> String.concat ", "

    let line (text: string) = out.AppendLine(text) |> ignore

    match a.Gens with
    | [] -> line $"const %s{a.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{a.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if a.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    // (The function behind the value may raise or not; a function value always may. If the call
    // raised, what the function only borrowed is given up here, like after a call that did not.)
    let finish (call: string) (resultBorrowed: bool) (dropAfter: string list) =
        let drops = dropAfter |> List.map (fun n -> dropCode n + " ") |> String.concat ""
        line $"    const raw = %s{call};"

        line
            $"    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch |err| {{ %s{drops}return err; }} else raw;"

        let result =
            if resultBorrowed then
                dupCode "r"
            else
                "r"

        if dropAfter.IsEmpty then
            line $"    return %s{result};"
        else
            line $"    const result = %s{result};"

            for name in dropAfter do
                line ("    " + dropCode name)

            line "    return result;"

    match fns.TryGetValue a.Target with
    | true, fn ->
        let inst =
            if fn.TypeParams.Length = a.TypeArgs.Length then
                Map.ofList (List.zip fn.TypeParams a.TypeArgs)
            else
                Map.empty

        let captured, rest = List.splitAt a.NCaptures (List.zip fn.Params fn.Modes)

        if a.NCaptures > 0 then
            let fields =
                captured
                |> List.mapi (fun i (p, _) -> $"c%d{i}: %s{zigType (substTy inst p.Ty)}")
                |> String.concat ", "

            line $"const Env = struct {{ %s{fields} }};"

        line $"fn code(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        if a.NCaptures > 0 then
            line "    const c = fable_rt.captured(Env, env);"
        else
            line "    _ = env;"

        // (the environment keeps what it captured: a function that takes ownership gets a
        // reference of its own)
        let capturedArgs =
            captured
            |> List.mapi (fun i (_, m) ->
                if m = MOwned then
                    dupCode $"c.c%d{i}"
                else
                    $"c.c%d{i}"
            )

        let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "

        let dropAfter =
            List.zip ps rest
            |> List.choose (fun ((n, _), (_, m)) ->
                if m = MBorrowed then
                    Some n
                else
                    None
            )

        finish $"%s{fnRef a.Target a.TypeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
    | _ ->
        // a function of another file: what it borrows is settled when the Zig is compiled
        if a.NCaptures > 0 then
            let fields =
                a.CaptureTys
                |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}")
                |> String.concat ", "

            line $"const Env = struct {{ %s{fields} }};"

        line $"fn code(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        if a.NCaptures > 0 then
            line "    const c = fable_rt.captured(Env, env);"
        else
            line "    _ = env;"

        let tuple (items: string list) =
            match items with
            | [] -> ".{}"
            | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

        let capturedArgs = a.CaptureTys |> List.mapi (fun i _ -> $"c.c%d{i}")

        if
            isManaged ret
            || argTys |> List.exists isManaged
            || a.CaptureTys |> List.exists isManaged
        then
            // (the environment keeps what it captured; the arguments are given)
            let uses =
                (a.CaptureTys
                 |> List.map (fun t ->
                     if isManaged t then
                         ".keep"
                     else
                         ".plain"
                 ))
                @ (argTys
                   |> List.map (fun t ->
                       if isManaged t then
                           ".give"
                       else
                           ".plain"
                   ))

            finish
                $"fable_rt.across(%s{fnRef a.Target a.TypeArgs}, %s{sigName a.Target}, %s{tuple uses}, %s{tuple (capturedArgs @ (ps |> List.map fst))})"
                false
                []
        else
            let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "
            finish $"%s{fnRef a.Target a.TypeArgs}(%s{args})" false []

    line "}"

    if a.Gens.IsEmpty then
        out.AppendLine("};") |> ignore
    else
        out.AppendLine("    };").AppendLine("}") |> ignore

    out.AppendLine() |> ignore

/// A resource's hooks, as declarations the runtime looks for: `fable_destroy`, `fable_dup`.
/// `fable_rt.Hook(file, "name")` of a function of this file or of another (`alias.name`)
let hookOf (fn: string) =
    match fn.IndexOf '.' with
    | -1 -> $"fable_rt.Hook(@\"$file\", \"%s{topIdent fn}\")"
    | i -> $"fable_rt.Hook(%s{fn.Substring(0, i)}, \"%s{topIdent (fn.Substring(i + 1))}\")"

let hookDecls (e: Ent) (ind: string) : string =
    let overrides =
        e.Overrides
        |> List.map (fun (decl, fn) ->
            if fn = "" then
                $"%s{ind}    pub const %s{decl} = {{}};\n"
            else
                $"%s{ind}    pub const %s{decl} = %s{hookOf fn};\n"
        )
        |> String.concat ""

    overrides
    + match e.Hooks with
      | Some(destroy, dup) ->
          let one (name: string) (fn: string) =
              $"%s{ind}    pub const %s{name} = %s{callTarget fn};\n"

          one "fable_destroy" destroy
          + (
              match dup with
              | Some d -> one "fable_dup" d
              | None -> ""
          )
      | None -> ""

/// The text of one file, without its imports (their paths are only known to the writer).
let emitFile (state: FileState) : string =
    currentArenas <- state.Arenas
    let out = StringBuilder()
    let rootNames = HashSet<string>([ "result"; "hole"; "tail"; "env" ])

    for (name, _, _) in state.Consts do
        rootNames.Add(topIdent name) |> ignore

    for (name, _, _) in state.Values do
        rootNames.Add(topIdent name) |> ignore

    for fn in state.Fns do
        rootNames.Add(topIdent fn.Name) |> ignore

    for alias in state.Imports.Values do
        rootNames.Add alias |> ignore

    for e in state.LocalEnts do
        rootNames.Add(topIdent e.Name) |> ignore

    // What this file's code does that lets a function value be part of a cycle, joined with
    // what the files it uses say (see `fable_rt.functions_in_cycles`).
    let (holds, generic, instantiated) = state.Cycles

    let used =
        match
            state.Imports.Values
            |> Seq.sort
            |> Seq.map (fun alias -> alias + ".@\"$cycles\"")
            |> List.ofSeq
        with
        | [] -> ".{}"
        | items -> items |> String.concat ", " |> sprintf ".{ %s }"

    let b (x: bool) =
        if x then
            "true"
        else
            "false"

    out
        .AppendLine(
            $"pub const @\"$cycles\" = fable_rt.joinCycles(.{{ .holds = %s{b holds}, .generic = %s{b generic}, .instantiated = %s{b instantiated} }}, %s{used});"
        )
        .AppendLine()
    |> ignore

    for e in state.LocalEnts do
        let fields (fs: (string * Ty) list) =
            fs |> List.map (fun (f, t) -> $"%s{fieldIdent f}: %s{zigType t}")

        // A generic type is a Zig function from its type arguments to the type.
        let opening, closing, ind =
            match e.TypeParams with
            | [] -> (fun (kind: string) -> $"pub const %s{topIdent e.Name} = %s{kind} {{"), "};", ""
            | typeParams ->
                let comptimeParams =
                    typeParams
                    |> List.map (fun g -> $"comptime %s{genName g}: type")
                    |> String.concat ", "

                (fun (kind: string) ->
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return %s{kind} {{"
                ),
                "    };\n}",
                "    "

        match e.Kind with
        | KRefRecord ->
            // a pointer to a counted cell that holds the fields
            let decl =
                match cyclicDecl e with
                | Some verdict -> $"pub const fable_cyclic = %s{verdict}; "
                | None -> ""

            let payload =
                decl
                + (hookDecls e "").Replace("\n", " ").Trim()
                + " "
                + (cellHeader e @ fields (snd e.Cases.Head) |> String.concat ", ")

            match e.TypeParams with
            | [] ->
                out.Append($"pub const %s{topIdent e.Name} = *struct {{ %s{payload} }}")
                |> ignore
            | typeParams ->
                let comptimeParams =
                    typeParams
                    |> List.map (fun g -> $"comptime %s{genName g}: type")
                    |> String.concat ", "

                out.Append(
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return *struct {{ %s{payload} }};\n}}"
                )
                |> ignore
        | KExn ->
            let payload = fields (snd e.Cases.Head) |> String.concat ", "

            out.Append(
                $"pub const %s{topIdent e.Name} = fable_rt.ExnOf(\"%s{e.Ref.DisplayName}\", struct {{ %s{payload} }})"
            )
            |> ignore
        | KRecord ->
            out.AppendLine(opening "struct") |> ignore
            out.Append(hookDecls e ind) |> ignore

            for f in fields (snd e.Cases.Head) do
                out.AppendLine($"%s{ind}    %s{f},") |> ignore
        | KValueUnion ->
            out.AppendLine(opening "union(enum)") |> ignore
            out.Append(hookDecls e ind) |> ignore

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"%s{ind}    %s{fieldIdent c},") |> ignore
                else
                    let payload = fields fs |> String.concat ", "

                    out.AppendLine($"%s{ind}    %s{fieldIdent c}: struct {{ %s{payload} }},")
                    |> ignore
        | KHeapUnion ->
            // a case with fields points to a reference-counted cell; one without needs none
            out.AppendLine(opening "union(enum)") |> ignore

            match cyclicDecl e with
            | Some verdict -> out.AppendLine($"%s{ind}    pub const fable_cyclic = %s{verdict};") |> ignore
            | None -> ()

            out.Append(hookDecls e ind) |> ignore

            // (the trees of `Map` and `Set`: the runtime compares and writes them by what they
            // hold, not by their shape)
            match e.Ref.FullName with
            | "Fable.Library.Zig.Map.MapTree`2" ->
                out.AppendLine($"%s{ind}    pub const fable_collection = .map;") |> ignore
            | "Fable.Library.Zig.Set.SetTree`1" ->
                out.AppendLine($"%s{ind}    pub const fable_collection = .set;") |> ignore
            | _ -> ()

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"%s{ind}    %s{fieldIdent c},") |> ignore
                else
                    let payload = cellHeader e @ fields fs |> String.concat ", "

                    out.AppendLine($"%s{ind}    %s{fieldIdent c}: *struct {{ %s{payload} }},")
                    |> ignore

        if e.Kind = KRefRecord then
            (if e.TypeParams.IsEmpty then
                 out.AppendLine(";")
             else
                 out.AppendLine())
                .AppendLine()
            |> ignore
        elif e.Kind = KExn then
            out.AppendLine(";").AppendLine() |> ignore
        else
            out.AppendLine(closing).AppendLine() |> ignore

    for (name, ty, text) in state.Consts do
        out.AppendLine($"pub const %s{topIdent name}: %s{zigType ty} = %s{text};")
        |> ignore

    if state.Consts.Count > 0 then
        out.AppendLine() |> ignore

    // the anonymous records the file uses: the runtime's type of each shape
    for kv in state.Ents do
        if kv.Key.StartsWith("$anon:", System.StringComparison.Ordinal) then
            let names = kv.Key.Substring(6).Split(',')
            let quoted = names |> Array.map (fun n -> "\"" + n + "\"") |> String.concat ", "

            let alias = "fable_anon_" + String.concat "_" names

            out.AppendLine($"const %s{alias} = fable_rt.Anon%d{names.Length}(.{{ %s{quoted} }});")
            |> ignore

    // Module-level values that are computed: each has a place, filled when the program starts
    // (after the values of the files this one uses) and given up when it ends.
    for (name, ty, _) in state.Values do
        out.AppendLine($"pub var %s{topIdent name}: %s{zigType ty} = undefined;")
        |> ignore

    let aliases = state.Imports.Values |> Seq.sort |> List.ofSeq

    let initCallees =
        (aliases |> List.map (fun alias -> alias + ".@\"$init\""))
        @ (state.Values |> Seq.map (fun (_, _, init) -> topIdent init) |> List.ofSeq)
        |> String.concat ", "

    out
        .AppendLine("var @\"$ready\": bool = false;")
        .AppendLine()
        .AppendLine($"pub fn @\"$init\"() fable_rt.MayRaise(void, .{{ %s{initCallees} }}) {{")
        .AppendLine("    if (@\"$ready\") return;")
        .AppendLine("    @\"$ready\" = true;")
    |> ignore

    for alias in aliases do
        out.AppendLine(
            $"    if (comptime fable_rt.isRaised(@TypeOf(%s{alias}.@\"$init\"()))) try %s{alias}.@\"$init\"() else %s{alias}.@\"$init\"();"
        )
        |> ignore

    for (name, _, init) in state.Values do
        let call = topIdent init + "()"

        out.AppendLine(
            $"    %s{topIdent name} = if (comptime fable_rt.isRaised(@TypeOf(%s{call}))) try %s{call} else %s{call};"
        )
        |> ignore

    out
        .AppendLine("}")
        .AppendLine()
        .AppendLine("pub fn @\"$deinit\"() void {")
        .AppendLine("    if (!@\"$ready\") return;")
        .AppendLine("    @\"$ready\" = false;")
    |> ignore

    for (name, _, _) in Seq.rev state.Values do
        out.AppendLine($"    fable_rt.drop(%s{topIdent name});") |> ignore

    for alias in List.rev aliases do
        out.AppendLine($"    %s{alias}.@\"$deinit\"();") |> ignore

    out.AppendLine("}").AppendLine() |> ignore

    let adapters = Dictionary<string, Adapter>()
    let fns = Dictionary<string, FnInfo>()

    for fn in state.Fns do
        fns[fn.Name] <- fn

    for fn in state.Fns do
        try
            emitFunction out rootNames adapters fns fn
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    // the classes that take part in inheritance: the type of each, with its tables of virtual
    // members (function values of the functions that implement them)
    for d in state.Objs do
        // (an object expression's class: each member calls the function value the object holds)
        for (name, partPtr, parts, field, fnTy) in d.Thunks do
            match fnTy with
            | TFn(_ :: args, ret) ->
                let ps =
                    args
                    |> List.mapi (fun i t -> $"a%d{i}: %s{zigType t}")
                    |> List.map (fun p -> ", " + p)
                    |> String.concat ""

                let xs = args |> List.mapi (fun i _ -> $", a%d{i}") |> String.concat ""

                out
                    .AppendLine(
                        $"fn %s{topIdent name}(env: ?*fable_rt.Env, this: fable_rt.Obj%s{ps}) fable_rt.Raised!%s{zigType ret} {{"
                    )
                    .AppendLine("    _ = env;")
                    .AppendLine(
                        $"    const f = fable_rt.dup(fable_rt.objPart(%s{zigType partPtr}, &[_]type{{ %s{parts} }}, this).%s{fieldIdent field});"
                    )
                    .AppendLine("    defer fable_rt.drop(f);")
                    .AppendLine($"    return f.code(f.env, this%s{xs});")
                    .AppendLine("}")
                |> ignore
            | _ -> ()

        let tables =
            d.Tables
            |> List.mapi (fun i t ->
                match t with
                | Some(vtTy, entries) ->
                    let name = topIdent $"%s{d.TypeName}_vt%d{i}"

                    let inits =
                        entries
                        |> List.map (fun (slot, target, fnTy) ->
                            if target.StartsWith("@raw:", System.StringComparison.Ordinal) then
                                // (a function of this file with the calling convention of a function value)
                                $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{topIdent (target.Substring 5)} }}"
                            else
                                let key = target + "<>"

                                let adapter =
                                    match adapters.TryGetValue key with
                                    | true, a -> a
                                    | _ ->
                                        let a =
                                            {
                                                Name = $"@\"%s{target}$fn%d{adapters.Count}\""
                                                Target = target
                                                TypeArgs = []
                                                NCaptures = 0
                                                CaptureTys = []
                                                FnTy = fnTy
                                                Gens = []
                                            }

                                        adapters[key] <- a
                                        a

                                $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{adapterRef adapter}.code }}"
                        )
                        |> String.concat ", "

                    out.AppendLine($"const %s{name}: %s{zigType vtTy} = .{{ %s{inits} }};")
                    |> ignore

                    "&" + name
                | None -> "null"
            )
            |> String.concat ", "

        let parent =
            match d.Parent with
            | Some p -> "&" + callTarget p
            | None -> "null"

        // (the class's ToString, as the code of a function value)
        let toString =
            match d.ToString with
            | Some target ->
                let fnTy = TFn([ TPrim "fable_rt.Obj"; tVoid ], tStr)
                let key = target + "<>"

                let adapter =
                    match adapters.TryGetValue key with
                    | true, a -> a
                    | _ ->
                        let a =
                            {
                                Name = $"@\"%s{target}$fn%d{adapters.Count}\""
                                Target = target
                                TypeArgs = []
                                NCaptures = 0
                                CaptureTys = []
                                FnTy = fnTy
                                Gens = []
                            }

                        adapters[key] <- a
                        a

                $"%s{adapterRef adapter}.code"
            | None -> "null"

        out.AppendLine(
            if d.Overrides.IsEmpty then
                $"pub const %s{topIdent d.TypeName}: fable_rt.ObjType = fable_rt.objType(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString});"
            else
                let hook (name: string) (asObj: string) =
                    match d.Overrides |> List.tryFind (fun (h, _) -> h = name) with
                    | Some(_, fn) -> $"%s{hookOf fn}.%s{asObj}"
                    | None -> "null"

                let eq = hook "equals" "objEquals"
                let hs = hook "hash" "objHash"
                let cmp = hook "compare" "objCompare"

                $"pub const %s{topIdent d.TypeName}: fable_rt.ObjType = fable_rt.objTypeWith(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString}, %s{eq}, %s{hs}, %s{cmp});"
        )
        |> ignore

    for a in adapters.Values do
        emitAdapter out fns a

    for (name, fn) in state.Tests do
        let quoted = name.Replace("\\", "\\\\").Replace("\"", "\\\"")

        out
            .AppendLine("test \"" + quoted + "\" {")
            .AppendLine("    try fable_rt.testInit(@\"$init\");")
            .AppendLine($"    try fable_rt.testCase(%s{callTarget fn});")
            .AppendLine("}")
        |> ignore

    // The F# entry point returns the process exit code as an int; Zig's `main` returns a u8.
    // In builds that count cells, a program that ends with cells still allocated says so.
    for fn in state.Fns do
        if fn.IsEntryPoint then
            out
                .AppendLine("pub fn main() u8 {")
                .AppendLine(
                    "    if (comptime fable_rt.isRaised(@TypeOf(@\"$init\"()))) (@\"$init\"() catch { fable_rt.uncaught(); return 134; }) else @\"$init\"();"
                )
            |> ignore

            let call = $"%s{topIdent fn.Name}()"

            // (an exception that nothing handled ends the program, as on .NET)
            let guarded =
                match fn.Raises with
                | RNever -> call
                | RAlways -> $"%s{call} catch {{ fable_rt.uncaught(); return 134; }}"
                | RDepends _ ->
                    $"if (comptime fable_rt.isRaised(@TypeOf(%s{call}))) (%s{call} catch {{ fable_rt.uncaught(); return 134; }}) else %s{call}"

            if isVoid fn.Ret then
                out.AppendLine($"    %s{guarded};").AppendLine("    const code: i32 = 0;")
                |> ignore
            else
                out.AppendLine($"    const code: i32 = %s{guarded};") |> ignore

            out
                .AppendLine("    @\"$deinit\"();")
                .AppendLine("    if (fable_rt.leaked()) return 70;")
                .AppendLine("    return @truncate(@as(u32, @bitCast(code)));")
                .AppendLine("}")
            |> ignore

    out.ToString()
