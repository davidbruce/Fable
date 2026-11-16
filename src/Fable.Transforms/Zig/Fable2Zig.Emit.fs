/// Emission: ownership IR -> Zig source text.
module Fable.Transforms.Zig.Emit

open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Fable.Transforms.Zig.IR

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
        /// optional direct 2-arg flat companion function for curried 2-arg function values
        Target2: string option
        TypeArgs: Ty list
        NCaptures: int
        /// the types of the captured values (needed for a function of another file)
        CaptureTys: Ty list
        FnTy: Ty
        /// when true, `a0` is borrowed by the caller (used for class vtable and `ToString` adapters)
        BorrowFirst: bool
        /// the type parameters of the surrounding function that the types above mention: the
        /// adapter is generic in them
        Gens: string list
    }

type IfaceVtKind =
    | IVtObj
    | IVtBox of Ty
    | IVtCaptures of Ty list
    | IVtUpcast of Ty

/// A static vtable for a fat-pointer interface (`fable_rt.Iface(Vt)`).
type IfaceVt =
    {
        Name: string
        IfaceTy: Ty
        Kind: IfaceVtKind
        Slots: (string * (string * Ty list)) list
        Gens: string list
    }

type SccInfo =
    {
        StateTypeName: string
        TagOf: Map<string, string>
    }

type Em =
    {
        Out: StringBuilder
        Names: Dictionary<int, string>
        Used: HashSet<string>
        Mutated: Set<int>
        Loop: LoopInfo option
        /// mutual tail-recursion SCC state machine when compiling an SCC arm
        Scc: SccInfo option
        /// the function being emitted, and the functions of the file by name
        Self: FnInfo
        Fns: Dictionary<string, FnInfo>
        Curried2: Dictionary<string, string>
        /// a call that ends the function can be a jump (see `tailTarget`)
        CanTail: bool
        /// the labels of the `try` bodies around the code being emitted
        TryLabels: Stack<string>
        /// the code of the function values made so far
        Adapters: Dictionary<string, Adapter>
        /// static vtables of fat-pointer interfaces built so far
        IfaceVts: Dictionary<string, IfaceVt>
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

/// The static vtable of an interface made of a source of a kind with these slots (one per
/// distinct interface, source and slots in the file)
let ifaceVtFor
    (ifaceVts: Dictionary<string, IfaceVt>)
    (ifaceTy: Ty)
    (kind: IfaceVtKind)
    (srcKey: string)
    (srcTys: Ty list)
    (slots: (string * (string * Ty list)) list)
    : IfaceVt
    =
    let slotKeyStr =
        slots
        |> List.map (fun (s, (t, tys)) -> s + "=" + t + "<" + (tys |> List.map tyKey |> String.concat ",") + ">")
        |> String.concat ";"

    let key = tyKey ifaceTy + "|" + srcKey + "|" + slotKeyStr

    match ifaceVts.TryGetValue key with
    | true, v -> v
    | _ ->
        let slotTypeArgs = slots |> List.collect (fun (_, (_, tys)) -> tys)

        let v =
            {
                Name = $"@\"fable_iface_vt$%d{ifaceVts.Count}\""
                IfaceTy = ifaceTy
                Kind = kind
                Slots = slots
                Gens = freeGens (ifaceTy :: srcTys @ slotTypeArgs)
            }

        ifaceVts[key] <- v
        v

/// The namespace of a static interface vtable, where it is used.
let ifaceVtRef (v: IfaceVt) =
    match v.Gens with
    | [] -> v.Name
    | gens -> gens |> List.map genName |> String.concat ", " |> sprintf "%s(%s)" v.Name

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

/// Format a cross-file call concisely using `fable_rt.callM`/`callG` or `xcallM`/`xcallG`/`xcallPlain`.
let rec private formatCrossCall
    (em: Em)
    (f: string)
    (typeArgs: Ty list)
    (xs: Expr list)
    (t: Ty)
    (ds: Var list option)
    : string option
    =
    let dot = f.IndexOf '.'

    if dot < 0 then
        None
    else
        let modAlias = f.Substring(0, dot)
        let memberName = topIdent (f.Substring(dot + 1))

        let errDrops =
            match ds with
            | None
            | Some [] -> ".{}"
            | Some vs -> vs |> List.map (vname em) |> String.concat ", " |> sprintf ".{ %s }"

        if isManaged t || xs |> List.exists (typeOf >> isManaged) then
            let usesChars =
                xs
                |> List.map (fun x ->
                    if not (isManaged (typeOf x)) then
                        'p'
                    else
                        match x with
                        | EDup(inner, _) when not (touchesMutable inner) -> 'k'
                        | _ -> 'g'
                )
                |> Array.ofList

            let usesStr = System.String(usesChars)

            let args =
                xs
                |> List.map (fun x ->
                    if not (isManaged (typeOf x)) then
                        ex em x
                    else
                        match x with
                        | EDup(inner, _) when not (touchesMutable inner) -> ex em inner
                        | _ -> ex em x
                )

            let argsTuple =
                match args with
                | [] -> ".{}"
                | _ -> args |> String.concat ", " |> sprintf ".{ %s }"

            match ds with
            | Some _ when canPlainTry em && em.Self.Raises = RAlways ->
                if typeArgs.IsEmpty then
                    Some
                        $"(try fable_rt.xcallM(%s{modAlias}, \"%s{memberName}\", \"%s{usesStr}\", %s{argsTuple}, %s{errDrops}))"
                else
                    let gns =
                        typeArgs
                        |> List.map zigType
                        |> String.concat ", "
                        |> sprintf "%s.%s(%s)" modAlias memberName

                    Some $"(try fable_rt.xcallG(%s{gns}, \"%s{usesStr}\", %s{argsTuple}, %s{errDrops}))"
            | Some _ when canPlainTry em ->
                let c =
                    if typeArgs.IsEmpty then
                        $"fable_rt.callM(%s{modAlias}, \"%s{memberName}\", \"%s{usesStr}\", %s{argsTuple}, %s{errDrops})"
                    else
                        let gns =
                            typeArgs
                            |> List.map zigType
                            |> String.concat ", "
                            |> sprintf "%s.%s(%s)" modAlias memberName

                        $"fable_rt.callG(%s{gns}, \"%s{usesStr}\", %s{argsTuple}, %s{errDrops})"

                em.Counter <- em.Counter + 1
                let lbl = $"call%d{em.Counter}"
                let raw = freshName em "raw"

                Some
                    $"(%s{lbl}: {{ const %s{raw} = %s{c}; break :%s{lbl} if (comptime fable_rt.isRaised(@TypeOf(%s{raw}))) try %s{raw} else %s{raw}; }})"
            | _ ->
                if typeArgs.IsEmpty then
                    Some $"fable_rt.callM(%s{modAlias}, \"%s{memberName}\", \"%s{usesStr}\", %s{argsTuple}, .{{}})"
                else
                    let gns =
                        typeArgs
                        |> List.map zigType
                        |> String.concat ", "
                        |> sprintf "%s.%s(%s)" modAlias memberName

                    Some $"fable_rt.callG(%s{gns}, \"%s{usesStr}\", %s{argsTuple}, .{{}})"
        else
            match ds with
            | Some _ when canPlainTry em && em.Self.Raises = RAlways ->
                let args = xs |> List.map (ex em) |> String.concat ", "
                Some $"(try fable_rt.xcallPlain(%s{fnRef f typeArgs}(%s{args}), %s{errDrops}))"
            | _ -> None

and canPlainTry (em: Em) =
    em.TryLabels.Count = 0
    && (
        match em.Loop with
        | Some {
                   Trmc = true
                   Plug = Some _
               } -> false
        | _ -> true
    )

and ex (em: Em) (e: Expr) : string =
    match e with
    | EVar v -> vname em v
    | ELit(s, _) -> s
    | EUnit -> "{}"
    | EPrim(op, xs, t) ->
        // (an operation of literals only would be computed by Zig without bounds, as
        // comptime_int: the first is given its type, so that it wraps as on .NET)
        let a =
            match xs with
            // (a literal shifted by a number known only when the program runs, too)
            | ELit(s, (TPrim p as ty)) :: rest when
                (intBits ty > 0 || isFloatTy ty)
                && (op = "shl"
                    || op = "shr"
                    || rest
                       |> List.forall (
                           function
                           | ELit _ -> true
                           | _ -> false
                       ))
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
            match argT with
            | TPrim("isize" | "usize") -> $"@intCast(%s{y} & (@bitSizeOf(usize) - 1))"
            | _ -> $"@intCast(%s{y} & %d{max 1 (intBits argT) - 1})"

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
                        | TPrim "void"
                        | TOpt(TPrim "fable_rt.Obj") -> true
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

            // (a `System.Type`: compared by what it stands for, as one made when the program
            // runs is another pointer)
            if isManaged argT || holdsDecimal argT || argT = TPrim "fable_rt.reflect.Type" then
                $"fable_rt.eql(%s{x}, %s{y})"
            else
                $"std.meta.eql(%s{x}, %s{y})"
        | "tag", [ x ] -> $"@as(i32, @intFromEnum(%s{x}))"
        // (the source type is spelled out: a literal has no type of its own in Zig)
        | "conv", [ x ] -> $"fable_rt.conv(%s{zigType t}, @as(%s{zigType argT}, %s{x}))"
        | _ -> fail None "internal: unknown primitive %s/%d" op a.Length
    | ECall(f, typeArgs, xs, t) ->
        match formatCrossCall em f typeArgs xs t None with
        | Some txt -> txt
        | None ->
            let args = xs |> List.map (ex em) |> String.concat ", "
            $"%s{fnRef f typeArgs}(%s{args})"
    | ECallClo(f, xs, resTy) ->
        let fn = ex em f

        match typeOf f, xs with
        | TFn([ _ ], TFn([ _ ], _)), [ a0; a1 ] ->
            $"fable_rt.apply2(%s{zigType resTy}, %s{fn}, %s{ex em a0}, %s{ex em a1})"
        | _ ->
            let args = $"%s{fn}.env" :: (xs |> List.map (ex em)) |> String.concat ", "
            $"%s{fn}.code(%s{args})"
    | ECallVt(f, s, xs, _) ->
        let fn = ex em f

        let args =
            $"%s{fn}.env" :: ex em s :: (xs |> List.map (ex em)) |> String.concat ", "

        $"%s{fn}.code(%s{args})"
    | ECallIface(r, slot, xs, _) ->
        let recv = ex em r
        let args = $"%s{recv}.data" :: (xs |> List.map (ex em)) |> String.concat ", "
        $"%s{recv}.vt.%s{fieldIdent slot}(%s{args})"
    | EIface(ifaceTy, src, slots) ->
        let kind, srcKey, srcTys =
            match src with
            | ISrcValue v ->
                let vty = typeOf v

                if vty = TPrim "fable_rt.Obj" then
                    IVtObj, "obj", []
                else
                    IVtBox vty, "box:" + tyKey vty, [ vty ]
            | ISrcCaptures caps ->
                let ctys = caps |> List.map typeOf
                IVtCaptures ctys, "cap:" + (ctys |> List.map tyKey |> String.concat ","), ctys
            | ISrcUpcast sub ->
                let sty = typeOf sub
                IVtUpcast sty, "up:" + tyKey sty, [ sty ]

        let vt = ifaceVtFor em.IfaceVts ifaceTy kind srcKey srcTys slots

        let ns = ifaceVtRef vt

        match src with
        | ISrcValue v ->
            let vty = typeOf v

            if vty = TPrim "fable_rt.Obj" then
                $"%s{zigType ifaceTy}{{ .data = @ptrCast(%s{ex em v}), .vt = &%s{ns}.vt }}"
            else
                $"fable_rt.ifaceBox(%s{zigType ifaceTy}, %s{zigType vty}, %s{ex em v}, &%s{ns}.vt)"
        | ISrcCaptures [] -> $"%s{zigType ifaceTy}{{ .data = null, .vt = &%s{ns}.vt }}"
        | ISrcCaptures caps ->
            let inits =
                caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

            $"fable_rt.ifaceClosure(%s{zigType ifaceTy}, %s{ns}.Env, .{{ %s{inits} }}, &%s{ns}.vt)"
        | ISrcUpcast sub ->
            $"fable_rt.ifaceBox(%s{zigType ifaceTy}, %s{zigType (typeOf sub)}, %s{ex em sub}, &%s{ns}.vt)"
    | EClosure(target, typeArgs, caps, ty) ->
        let target2 =
            match ty with
            | TFn([ tyA ], TFn([ tyB ], tyR)) ->
                match em.Curried2.TryGetValue target with
                | true, t2 ->
                    match em.Fns.TryGetValue t2 with
                    | true, fn2 when fn2.Params.Length = caps.Length + 2 ->
                        let inst =
                            if fn2.TypeParams.Length = typeArgs.Length then
                                Map.ofList (List.zip fn2.TypeParams typeArgs)
                            else
                                Map.empty

                        let rest2 = List.skip caps.Length fn2.Params

                        if
                            zigType (substTy inst rest2[0].Ty) = zigType tyA
                            && zigType (substTy inst rest2[1].Ty) = zigType tyB
                            && zigType (substTy inst fn2.Ret) = zigType tyR
                        then
                            Some t2
                        else
                            None
                    | _ -> None
                | _ -> None
            | _ -> None

        let key =
            target
            + "<"
            + (typeArgs |> List.map tyKey |> String.concat ",")
            + ">"
            + (
                match target2 with
                | Some t2 -> "#2:" + t2
                | None -> ""
            )

        let adapter =
            match em.Adapters.TryGetValue key with
            | true, a -> a
            | _ ->
                let a =
                    {
                        Name = $"@\"%s{target}$fn%d{em.Adapters.Count}\""
                        Target = target
                        Target2 = target2
                        TypeArgs = typeArgs
                        NCaptures = caps.Length
                        CaptureTys = caps |> List.map typeOf
                        FnTy = ty
                        BorrowFirst = false
                        Gens = freeGens (ty :: typeArgs @ (caps |> List.map typeOf))
                    }

                em.Adapters[key] <- a
                a

        let ns = adapterRef adapter

        if adapter.Target2.IsSome then
            if caps.IsEmpty then
                $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code, .code2 = %s{ns}.code2 }}"
            else
                let inits =
                    caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

                $"fable_rt.closure2(%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code, %s{ns}.code2)"
        elif caps.IsEmpty then
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
        match call with
        | ECall(f, typeArgs, xs, t) when f.Contains "." && canPlainTry em ->
            match formatCrossCall em f typeArgs xs t (Some ds) with
            | Some txt -> txt
            | None ->
                let c = ex em call
                em.Counter <- em.Counter + 1
                let lbl = $"call%d{em.Counter}"
                let raw = freshName em "raw"
                let edge = edgeText em ds

                $"(%s{lbl}: {{ const %s{raw} = %s{c}; break :%s{lbl} if (comptime fable_rt.isRaised(@TypeOf(%s{raw}))) (%s{raw} catch %s{edge}) else %s{raw}; }})"
        | _ ->
            let definite =
                match call with
                | ECallClo _
                | ECallVt _
                | ECallIface _
                | ERt _ -> true
                | ECall(f, _, _, _) ->
                    match em.Fns.TryGetValue f with
                    | true, g -> g.Raises = RAlways
                    | _ -> false
                | _ -> false

            if definite && ds.IsEmpty && canPlainTry em then
                $"(try %s{ex em call})"
            else
                let c = ex em call
                let edge = edgeText em ds

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
            if fs.Length <> args.Length then
                fail
                    None
                    "internal: %s.%s is made of %d values, and has %d fields (%A)"
                    (zigType t)
                    case
                    args.Length
                    fs.Length
                    (fs |> List.map fst)

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
        // (a field of a value written out, `T{ ... }`, is read through parentheses)
        | PField f when o.EndsWith "}" -> $"(%s{o}).%s{fieldIdent f}"
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
    // (an assignable field of a value that may be shared between threads: read with its own
    // reference under the field's lock when it is shared; Koka's protocol)
    | EDup(EGet(owner, PField f, _), _) when
        (match typeOf owner with
         | TEnt({ Kind = KRefRecord } as ent, _) -> List.contains f ent.MutableFields
         | _ -> false)
        ->
        $"fable_rt.loadIn(%s{ex em owner}, \"%s{f}\")"
    | EDup(EGet(EEmit(m, [ o ], TPtr(TEnt(ent, _), _)) as part, PField f, t), _) when
        m.StartsWith("fable_rt.objPart(", System.StringComparison.Ordinal)
        && List.contains f ent.MutableFields
        ->
        $"fable_rt.objLoad(%s{ex em o}, &%s{ex em (EGet(part, PField f, t))})"
    | EDup(x, _) -> dupCode (ex em x)
    // (`&x` and what a byref points at)
    | EAddr(x, _) -> "&" + ex em x
    | EDeref(x, _) -> ex em x + ".*"
    | EIf(c, t, f, _) when isFlat c && isFlat t && isFlat f -> simpleIf em c t f
    | other ->
        let text = (sprintf "%A" other).Replace("\n", " ").Replace("  ", " ")

        fail
            None
            "internal: this expression is not part of the Zig target yet (%s)"
            (text.Substring(0, min 400 text.Length))

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
        match ds with
        | [] -> ""
        | [ d ] -> dropCode (vname em d) + " "
        | _ ->
            let names = ds |> List.map (vname em) |> String.concat ", "
            $"fable_rt.dropAll(.{{ %s{names} }}); "

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
    | DReturn when em.Loop.IsSome || em.Scc.IsSome -> line em ind "return;"
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

/// Does this statement always raise (end in a `raise` on every path it can take)?
let rec alwaysRaises (e: Expr) : bool =
    match e with
    | ERaise _ -> true
    | ELet(_, _, b)
    | ESeq(_, b) -> alwaysRaises b
    | EIf(_, t, f, _) -> alwaysRaises t && alwaysRaises f
    | _ -> false

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
    // (a value that always raises: the raise, and nothing after it, which could not run)
    | ELet(_, rhs, _) when alwaysRaises rhs -> stmt em ind rhs DDiscard
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

            // (a unit made by a statement, a loop: the statement, then the unit)
            match rhs with
            | EFor _
            | EWhile _ when isVoid v.Ty ->
                stmt em ind rhs DDiscard
                L $"%s{kw} %s{name}: void = {{}};"
            | _ when isFlat rhs || isSimpleIf rhs -> L $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{ex em rhs};"
            | _ -> block rhs (fun lbl -> $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{lbl}: {{")

        stmt em ind body dest
    // (after what always raises, nothing runs: Zig refuses code after its jump)
    | ESeq(a, _) when alwaysRaises a -> stmt em ind a DDiscard
    | ESeq(a, b) ->
        stmt em ind a DDiscard
        stmt em ind b dest
    // (where a function ends, each branch is a statement if one of them may be a jump)
    | EIf(_, t, f, _) when
        isSimpleIf e
        && dest <> DDiscard
        && not (
            dest = DReturn
            && (em.Loop.IsSome
                || em.Scc.IsSome
                || (tailTarget em t).IsSome
                || (tailTarget em f).IsSome)
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
    | EStore(EGet(EEmit(m, [ o ], TPtr(part, false)), PField _, _) as lv, rhs) when
        m.StartsWith("objInit:", System.StringComparison.Ordinal)
        ->
        let rest = m.Substring 8
        let colon = rest.IndexOf ':'
        let fieldIdx = rest.Substring(0, colon)
        let parts = rest.Substring(colon + 1)

        let value =
            if isFlat rhs || isSimpleIf rhs then
                ex em rhs
            else
                let stored = freshName em "stored"
                block rhs (fun lbl -> $"const %s{stored}: %s{zigType (typeOf lv)} = %s{lbl}: {{")
                stored

        L $"fable_rt.objInitField(%s{zigType part}, &[_]type{{ %s{parts} }}, %s{fieldIdx}, %s{ex em o}, %s{value});"
        finishUnit em ind dest
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
        match em.Loop, em.Scc, e with
        | Some loop, _, (ECall(f, _, args, _) | EOnRaise(ECall(f, _, args, _), _)) when f = loop.Self ->
            emitTailJump em ind args
        | Some loop, _, _ when loop.Trmc ->
            L $"hole.* = %s{ex em e};"
            L "return result;"
        | _, Some scc, (ECall(g, tArgs, args, _) | EOnRaise(ECall(g, tArgs, args, _), [])) when
            em.TryLabels.Count = 0
            && tArgs = (em.Self.TypeParams |> List.map TGen)
            && scc.TagOf.ContainsKey g
            ->
            let tag = scc.TagOf[g]

            if args.IsEmpty then
                L $"_st = .%s{tag};"
            else
                let inits =
                    args |> List.mapi (fun i a -> $".a%d{i} = %s{ex em a}") |> String.concat ", "

                L $"const _next: %s{scc.StateTypeName} = .{{ .%s{tag} = .{{ %s{inits} }} }};"
                L "_st = _next;"

            L "continue :tail;"
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
        // (a local that is only discarded is still used, or Zig would reject it; a mutable one
        // is used by its assignments, and discarding it as well is an error to Zig)
        | EVar v when v.FMutable -> ()
        | EVar _ -> L $"_ = %s{ex em e};"
        | _ when isPure e -> ()
        | _ -> L $"_ = %s{ex em e};"

/// A name given to a part of a value (`const Head: T = x.Cons.Head;`) for a pattern whose other
/// parts were then left out may be read nowhere, which Zig rejects: such lines are removed (they
/// only read, and the part is borrowed).
let dropUnreadPaths (body: string) =
    let decl = Regex(@"^\s*const (\w+): [^=]+ = [\w.\[\]@""]+;\s*$")

    let lines = body.Split('\n')
    // (what the comments say is not a use; a `//` inside a string literal is no comment)
    let code =
        Regex.Replace(
            body,
            @"""(?:[^""\\\n]|\\.)*""|//[^\n]*",
            fun m ->
                if m.Value.StartsWith "//" then
                    ""
                else
                    m.Value
        )

    // how often each name is written, not as a field (`.name`): one walk of the text
    let counts = Dictionary<string, int>()

    for m in Regex.Matches(code, @"(?<![\w.@""])\w+") do
        let n = m.Value

        match counts.TryGetValue n with
        | true, c -> counts[n] <- c + 1
        | _ -> counts[n] <- 1

    let unread =
        lines
        |> Array.choose (fun l ->
            let m = decl.Match l

            if
                m.Success
                && (
                    match counts.TryGetValue m.Groups[1].Value with
                    | true, 1 -> true
                    | _ -> false
                )
            then
                Some l
            else
                None
        )
        |> Set.ofArray

    if unread.IsEmpty then
        body
    else
        lines |> Array.filter (fun l -> not (unread.Contains l)) |> String.concat "\n"

/// Zig rejects a parameter that is never used.
let ensureUsed (names: string list) (body: string) =
    // (a name inside a string literal or comment is not a use of it)
    let code = Regex.Replace(body, "\"(?:[^\"\\\\]|\\\\.)*\"|//[^\\n]*", "\"\"")

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

/// The runtime's `cell` is inlined, so the work Zig does at compile time for each counts against
/// the function's quota of backward branches: a literal of many cells, a 9 by 9 list of lists,
/// runs out of it; and so does each inlined `dup` and `drop` (a state machine fusing many
/// functions has hundreds of them). The line that raises the quota, if the body needs it.
let branchQuota (bodyText: string) : string =
    let count (what: string) =
        let mutable n = 0
        let mutable i = bodyText.IndexOf(what, System.StringComparison.Ordinal)

        while i >= 0 do
            n <- n + 1
            i <- bodyText.IndexOf(what, i + 1, System.StringComparison.Ordinal)

        n

    let cells = count "fable_rt.cell("
    let counts = count "fable_rt.dup(" + count "fable_rt.drop("

    if cells > 32 || counts > 128 then
        "    @setEvalBranchQuota("
        + string (max 10000 (cells * 200 + counts * 50))
        + ");\n"
    else
        ""

/// The `[<StackArena>]` functions of the file being written.
let private currentArenas =
    new System.Threading.ThreadLocal<Dictionary<string, int> ref>(fun () -> ref (Dictionary<string, int>()))

let emitFunction
    (out: StringBuilder)
    (rootNames: HashSet<string>)
    (adapters: Dictionary<string, Adapter>)
    (ifaceVts: Dictionary<string, IfaceVt>)
    (fns: Dictionary<string, FnInfo>)
    (curried2: Dictionary<string, string>)
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
            Scc = None
            Self = fn
            Fns = fns
            Curried2 = curried2
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
            IfaceVts = ifaceVts
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

    let bodyText = dropUnreadPaths (em.Out.ToString())

    // `NativePtr.stackalloc`: memory of the function, given up when it returns
    let bodyText =
        if bodyText.Contains "fable_stack.alloc(" then
            "    var fable_stack: fable_rt.StackAlloc = .{};\n    defer fable_stack.deinit();\n"
            + bodyText
        else
            bodyText

    // `[<StackArena(bytes)>]`: the function's cells come from a buffer on its stack
    let bodyText =
        match currentArenas.Value.Value.TryGetValue fn.Name with
        | true, bytes ->
            $"    var fable_arena_buffer: [%d{bytes}]u8 align(16) = undefined;\n"
            + "    var fable_arena_fba = std.heap.FixedBufferAllocator.init(&fable_arena_buffer);\n"
            + "    var fable_arena: fable_rt.Arena = undefined;\n"
            + "    fable_rt.arenaEnter(&fable_arena, &fable_arena_fba);\n"
            + "    defer fable_rt.arenaLeave(&fable_arena);\n"
            + bodyText
        | _ -> bodyText

    let bodyText = branchQuota bodyText + bodyText

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

        let sigDecl =
            if hasManaged fn && not fn.IsLocal then
                $"        pub const sig = %s{sigName fn.Name};\n"
            else
                ""

        out
            .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{comptimeParams}) type {{")
            .Append(discards)
            .AppendLine("    return struct {")
            .Append(sigDecl)
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

        let callPs =
            match ps, rest with
            | (n0, _) :: psTail, (_, m0) :: _ when a.BorrowFirst ->
                let a0 =
                    if m0 = MOwned then
                        dupCode n0
                    else
                        n0

                a0 :: (psTail |> List.map fst)
            | _ -> ps |> List.map fst

        let args = capturedArgs @ callPs |> String.concat ", "

        let dropPairs =
            match List.zip ps rest with
            | _ :: tail when a.BorrowFirst -> tail
            | all -> all

        let dropAfter =
            dropPairs
            |> List.choose (fun ((n, _), (_, m)) ->
                if m = MBorrowed then
                    Some n
                else
                    None
            )

        finish $"%s{fnRef a.Target a.TypeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter

        match a.Target2, a.FnTy with
        | Some t2, TFn([ tyA ], TFn([ tyB ], tyR)) ->
            match fns.TryGetValue t2 with
            | true, fn2 ->
                line "}"
                let captured2, rest2 = List.splitAt a.NCaptures (List.zip fn2.Params fn2.Modes)

                line
                    $"fn code2(env: ?*fable_rt.Env, a0: %s{zigType tyA}, a1: %s{zigType tyB}) fable_rt.Raised!%s{zigType tyR} {{"

                if a.NCaptures > 0 then
                    line "    const c = fable_rt.captured(Env, env);"
                else
                    line "    _ = env;"

                let capturedArgs2 =
                    captured2
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"c.c%d{i}"
                        else
                            $"c.c%d{i}"
                    )

                let args2 = capturedArgs2 @ [ "a0"; "a1" ] |> String.concat ", "

                let dropAfter2 =
                    List.zip [ "a0"; "a1" ] rest2
                    |> List.choose (fun (n, (_, m)) ->
                        if m = MBorrowed then
                            Some n
                        else
                            None
                    )

                finish $"%s{fnRef t2 a.TypeArgs}(%s{args2})" fn2.RetFrom.IsSome dropAfter2
            | _ -> ()
        | _ -> ()
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
            // (the environment keeps what it captured; the arguments are given unless BorrowFirst borrows a0)
            let uses =
                (a.CaptureTys
                 |> List.map (fun t ->
                     if isManaged t then
                         ".keep"
                     else
                         ".plain"
                 ))
                @ (argTys
                   |> List.mapi (fun i t ->
                       if isManaged t then
                           if a.BorrowFirst && i = 0 then
                               ".keep"
                           else
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

/// Emit a static vtable struct (and optional captured `Env`) for a fat-pointer interface.
let emitIfaceVt (out: StringBuilder) (fns: Dictionary<string, FnInfo>) (vt: IfaceVt) =
    let line (text: string) = out.AppendLine(text) |> ignore

    match vt.Gens with
    | [] -> line $"const %s{vt.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{vt.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if vt.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    let finishInd (extra: string) (call: string) (resultBorrowed: bool) (dropAfter: string list) =
        let drops = dropAfter |> List.map (fun n -> dropCode n + " ") |> String.concat ""
        line $"%s{extra}    const raw = %s{call};"

        line
            $"%s{extra}    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch |err| {{ %s{drops}return err; }} else raw;"

        let result =
            if resultBorrowed then
                dupCode "r"
            else
                "r"

        if dropAfter.IsEmpty then
            line $"%s{extra}    return %s{result};"
        else
            line $"%s{extra}    const result = %s{result};"

            for name in dropAfter do
                line ($"%s{extra}    " + dropCode name)

            line $"%s{extra}    return result;"

    let tuple (items: string list) =
        match items with
        | [] -> ".{}"
        | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

    match vt.Kind with
    | IVtCaptures capTys when not capTys.IsEmpty ->
        let fields =
            capTys |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}") |> String.concat ", "

        line $"const Env = struct {{ %s{fields} }};"
    | _ -> ()

    let slotTys = caseFields vt.IfaceTy "" |> dict

    for (slotIdx, (slotName, (targetFn, typeArgs))) in List.indexed vt.Slots do
        let argTys, ret =
            match slotTys.TryGetValue slotName with
            | true, (TSlot(argTys, ret) | TFn(argTys, ret)) -> argTys, ret
            | _ -> fail None "internal: missing slot `%s` on interface `%A`" slotName vt.IfaceTy

        let wrapperName = $"@\"slot_%d{slotIdx}_%s{cleanIdent slotName}\""
        let ps = argTys |> List.mapi (fun i t -> $"a%d{i}", t)

        let sigParams =
            "d: ?*anyopaque" :: (ps |> List.map (fun (n, t) -> $"%s{n}: %s{zigType t}"))
            |> String.concat ", "

        line $"fn %s{wrapperName}(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        match vt.Kind with
        | IVtUpcast subTy ->
            line $"    const sub = fable_rt.boxed(%s{zigType subTy}, @ptrCast(@alignCast(d.?))).value;"
            let callArgs = "sub.data" :: (ps |> List.map fst) |> String.concat ", "
            line $"    return sub.vt.%s{fieldIdent targetFn}(%s{callArgs});"
        | IVtObj ->
            line "    const self: fable_rt.Obj = @ptrCast(@alignCast(d.?));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let inst =
                    if fn.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams typeArgs)
                    else
                        Map.empty

                ignore inst

                match List.zip fn.Params fn.Modes with
                | (_, thisMode) :: rest ->
                    let a0 =
                        if thisMode = MOwned then
                            dupCode "self"
                        else
                            "self"

                    let args = a0 :: (ps |> List.map fst) |> String.concat ", "

                    let dropAfter =
                        List.zip ps rest
                        |> List.choose (fun ((n, _), (_, m)) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
                | [] -> fail None "internal: object interface method `%s` has no self parameter" targetFn
            | _ ->
                let uses =
                    ".keep"
                    :: (argTys
                        |> List.map (fun t ->
                            if isManaged t then
                                ".give"
                            else
                                ".plain"
                        ))

                let callArgs = tuple ("self" :: (ps |> List.map fst))

                finishInd
                    ""
                    $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{tuple uses}, %s{callArgs})"
                    false
                    []
        | IVtBox valTy ->
            let valZ = zigType valTy
            line $"    const box_ptr = fable_rt.boxed(%s{valZ}, @ptrCast(@alignCast(d.?)));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let inst =
                    if fn.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams typeArgs)
                    else
                        Map.empty

                match List.zip fn.Params fn.Modes with
                | (thisParam, thisMode) :: rest ->
                    let thisIsPtr =
                        match substTy inst thisParam.Ty with
                        | TPtr _ -> true
                        | _ -> false

                    let a0 =
                        if thisIsPtr then
                            "&box_ptr.value"
                        elif thisMode = MOwned then
                            dupCode "box_ptr.value"
                        else
                            "box_ptr.value"

                    let args = a0 :: (ps |> List.map fst) |> String.concat ", "

                    let dropAfter =
                        List.zip ps rest
                        |> List.choose (fun ((n, _), (_, m)) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
                | [] -> fail None "internal: boxed interface method `%s` has no self parameter" targetFn
            | _ ->
                let target = fnRef targetFn typeArgs
                line $"    const SelfP = @typeInfo(@TypeOf(%s{target})).@\"fn\".param_types[0].?;"
                line $"    if (comptime SelfP == *%s{valZ} or SelfP == *const %s{valZ}) {{"

                if isManaged ret || argTys |> List.exists isManaged then
                    let ptrUses =
                        ".plain"
                        :: (argTys
                            |> List.map (fun t ->
                                if isManaged t then
                                    ".give"
                                else
                                    ".plain"
                            ))

                    let callArgs = tuple ("&box_ptr.value" :: (ps |> List.map fst))

                    finishInd
                        "    "
                        $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{tuple ptrUses}, %s{callArgs})"
                        false
                        []
                else
                    let args = "&box_ptr.value" :: (ps |> List.map fst) |> String.concat ", "
                    finishInd "    " $"%s{target}(%s{args})" false []

                line "    } else {"

                if isManaged valTy || isManaged ret || argTys |> List.exists isManaged then
                    let valUses =
                        (if isManaged valTy then
                             ".keep"
                         else
                             ".plain")
                        :: (argTys
                            |> List.map (fun t ->
                                if isManaged t then
                                    ".give"
                                else
                                    ".plain"
                            ))

                    let callArgs = tuple ("box_ptr.value" :: (ps |> List.map fst))

                    finishInd
                        "    "
                        $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{tuple valUses}, %s{callArgs})"
                        false
                        []
                else
                    let args = "box_ptr.value" :: (ps |> List.map fst) |> String.concat ", "
                    finishInd "    " $"%s{target}(%s{args})" false []

                line "    }"
        | IVtCaptures capTys ->
            if capTys.IsEmpty then
                line "    _ = d;"
            else
                line "    const c = fable_rt.captured(Env, @ptrCast(@alignCast(d)));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let captured, rest = List.splitAt capTys.Length (List.zip fn.Params fn.Modes)

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

                finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
            | _ ->
                let capturedArgs = capTys |> List.mapi (fun i _ -> $"c.c%d{i}")

                if
                    isManaged ret
                    || argTys |> List.exists isManaged
                    || capTys |> List.exists isManaged
                then
                    let uses =
                        (capTys
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

                    finishInd
                        ""
                        $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{tuple uses}, %s{tuple (capturedArgs @ (ps |> List.map fst))})"
                        false
                        []
                else
                    let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "
                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" false []

        line "}"

    let vtSlots =
        vt.Slots
        |> List.mapi (fun i (slotName, _) -> $".%s{fieldIdent slotName} = @\"slot_%d{i}_%s{cleanIdent slotName}\"")

    let metaExpr =
        match vt.Kind with
        | IVtObj -> "&fable_rt.obj_iface_meta"
        | IVtBox _ -> "&fable_rt.box_iface_meta"
        | IVtCaptures [] -> "&fable_rt.empty_iface_meta"
        | IVtCaptures _ -> "&fable_rt.env_iface_meta"
        | IVtUpcast subTy -> $"fable_rt.upcastIfaceMeta(%s{zigType subTy})"

    let vtFields = $".@\"$meta\" = %s{metaExpr}" :: vtSlots |> String.concat ", "
    line $"const Vt = @typeInfo(@FieldType(%s{zigType vt.IfaceTy}, \"vt\")).pointer.child;"
    line $"const vt: Vt = .{{ %s{vtFields} }};"

    if vt.Gens.IsEmpty then
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
    currentArenas.Value.Value <- state.Arenas
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
    let cyc = state.Cycles

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
            $"pub const @\"$cycles\" = fable_rt.joinCycles(.{{ .holds = %s{b cyc.Holds}, .generic = %s{b cyc.Generic}, .instantiated = %s{b cyc.Instantiated}, .captures = %s{b cyc.Captures}, .cap_generic = %s{b cyc.CapGeneric}, .cap_instantiated = %s{b cyc.CapInstantiated}, .stack_traces = %s{b state.UsesStackTrace}, .reflection = %s{b state.UsesReflection}, .exn_show = __FABLE_EXN_SHOW__, .oom_catch = %s{b state.CatchesOom} }}, %s{used});"
        )
        .AppendLine()
    |> ignore

    // (what reflection says of a record or a union: `fable_type`, its .NET name and what it is,
    // and its type arguments)
    let netTypeDecl (e: Ent) (ind: string) =
        match state.NetTypes.TryGetValue e.Name with
        | true, (fullName, kind) ->
            let args =
                match e.TypeParams with
                | [] -> ""
                | ps -> ps |> List.map genName |> String.concat ", " |> sprintf ", .args = .{ %s }"

            let kindLit =
                if kind = "union" then
                    ".@\"union\""
                else
                    ".record"

            $"%s{ind}    pub const fable_type = .{{ .full_name = \"%s{fullName}\", .kind = %s{kindLit}%s{args} }};\n"
        | _ -> ""

    for e in state.LocalEnts do
        let fields (fs: (string * Ty) list) =
            fs |> List.map (fun (f, t) -> $"%s{fieldIdent f}: %s{zigType t}")

        // (a type parameter none of the fields mention, a unit of measure, is `_`: Zig refuses
        // an unused parameter)
        let fieldText =
            (e.Cases
             |> List.collect (fun (_, fs) -> fs |> List.map (snd >> zigType))
             |> String.concat " ")
            + hookDecls e ""
            + netTypeDecl e ""

        let comptimeParam (g: string) =
            if fieldText.Contains(genName g) then
                $"comptime %s{genName g}: type"
            else
                "comptime _: type"

        // A generic type is a Zig function from its type arguments to the type.
        let opening, closing, ind =
            match e.TypeParams with
            | [] -> (fun (kind: string) -> $"pub const %s{topIdent e.Name} = %s{kind} {{"), "};", ""
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

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
                + (netTypeDecl e "").Replace("\n", " ").Trim()
                + " "
                + (cellHeader e @ fields (snd e.Cases.Head) |> String.concat ", ")

            match e.TypeParams with
            | [] ->
                out.Append($"pub const %s{topIdent e.Name} = *struct {{ %s{payload} }}")
                |> ignore
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

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
        | KIface ->
            let ifaceFields =
                "@\"$meta\": *const fable_rt.IfaceMeta" :: fields (snd e.Cases.Head)
                |> String.concat ", "

            match e.TypeParams with
            | [] ->
                out.Append($"pub const %s{topIdent e.Name} = fable_rt.Iface(struct {{ %s{ifaceFields} }})")
                |> ignore
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

                out.Append(
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return fable_rt.Iface(struct {{ %s{ifaceFields} }});\n}}"
                )
                |> ignore
        | KRecord ->
            out.AppendLine(opening "struct") |> ignore
            out.Append(hookDecls e ind) |> ignore
            out.Append(netTypeDecl e ind) |> ignore

            for f in fields (snd e.Cases.Head) do
                out.AppendLine($"%s{ind}    %s{f},") |> ignore
        | KValueUnion ->
            out.AppendLine(opening "union(enum)") |> ignore
            out.Append(hookDecls e ind) |> ignore
            out.Append(netTypeDecl e ind) |> ignore

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
            out.Append(netTypeDecl e ind) |> ignore

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

        if e.Kind = KRefRecord || e.Kind = KIface then
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

    // the anonymous records and `.NET` fat-pointer interfaces the file uses
    let emittedIfaceAliases = HashSet<string>()

    for kv in state.Ents do
        if kv.Key.StartsWith("$anon:", System.StringComparison.Ordinal) then
            let names = kv.Key.Substring(6).Split(',')
            let quoted = names |> Array.map (fun n -> "\"" + n + "\"") |> String.concat ", "

            let alias = "fable_anon_" + String.concat "_" names

            out.AppendLine($"const %s{alias} = fable_rt.Anon%d{names.Length}(.{{ %s{quoted} }});")
            |> ignore
        elif kv.Key.StartsWith("$iface:", System.StringComparison.Ordinal) then
            let rest = kv.Key.Substring(7)

            if rest = "" then
                if emittedIfaceAliases.Add "fable_iface_0" then
                    out.AppendLine("const fable_iface_0 = fable_rt.IfaceAnon0();") |> ignore
            else
                let safe = rest.Split(',') |> Array.map cleanIdent
                let quoted = safe |> Array.map (fun n -> "\"" + n + "\"") |> String.concat ", "
                let alias = "fable_iface_" + String.concat "_" safe

                if emittedIfaceAliases.Add alias then
                    out.AppendLine($"const %s{alias} = fable_rt.IfaceAnon%d{safe.Length}(.{{ %s{quoted} }});")
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
    let ifaceVts = Dictionary<string, IfaceVt>()
    let fns = Dictionary<string, FnInfo>()

    for fn in state.Fns do
        fns[fn.Name] <- fn

    // Mutual tail recursion: intra-file SCCs of >= 2 functions with matching return type, type
    // parameters, and error behavior (not already covered by scalar sibling tail jumps) fuse into a
    // single state-machine loop (`switch (_st) { ... continue :tail; }`).
    let rec isScalarTy (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    let tailEdges = Dictionary<string, Set<string>>()

    for fn in state.Fns do
        let rec collectTail (e: Expr) =
            match e with
            | ELet(_, (ECall _ | EOnRaise(ECall _, _)), ECon _) -> Set.empty
            | ELet(_, rhs, _) when alwaysRaises rhs -> Set.empty
            | ELet(_, _, b)
            | EDrop(_, b)
            | EUnpack(_, b)
            | EPromote(_, b) -> collectTail b
            | ESeq(a, _) when alwaysRaises a -> Set.empty
            | ESeq(_, b) -> collectTail b
            | EIf(_, t, f, _) -> Set.union (collectTail t) (collectTail f)
            | ECall(g, tArgs, args, _)
            | EOnRaise(ECall(g, tArgs, args, _), []) when
                fns.ContainsKey g
                && tArgs = (fn.TypeParams |> List.map TGen)
                && args.Length = fns[g].Params.Length
                ->
                Set.singleton g
            | _ -> Set.empty

        tailEdges[fn.Name] <- collectTail fn.Body

    let sccs = List<FnInfo list>()

    do
        let idx = ref 0
        let indexOf = Dictionary<string, int>()
        let lowOf = Dictionary<string, int>()
        let onStack = HashSet<string>()
        let stack = Stack<string>()

        let rec strongconnect (v: string) =
            indexOf[v] <- idx.Value
            lowOf[v] <- idx.Value
            idx.Value <- idx.Value + 1
            stack.Push v
            onStack.Add v |> ignore

            for w in tailEdges[v] do
                if not (indexOf.ContainsKey w) then
                    strongconnect w
                    lowOf[v] <- min lowOf[v] lowOf[w]
                elif onStack.Contains w then
                    lowOf[v] <- min lowOf[v] indexOf[w]

            if lowOf[v] = indexOf[v] then
                let comp = List<FnInfo>()
                let mutable stop = false

                while not stop do
                    let w = stack.Pop()
                    onStack.Remove w |> ignore
                    comp.Add fns[w]

                    if w = v then
                        stop <- true

                if comp.Count >= 2 then
                    sccs.Add(List.rev (List.ofSeq comp))

        for fn in state.Fns do
            if not (indexOf.ContainsKey fn.Name) then
                strongconnect fn.Name

    let sccByMember = Dictionary<string, FnInfo list * string * Map<string, string>>()

    for scc in sccs do
        let rep = scc.Head
        let repRet = zigType rep.Ret
        let repRetText = retType rep

        let eligible =
            scc
            |> List.forall (fun fn ->
                not (state.Arenas.ContainsKey fn.Name)
                && fn.RetFrom.IsNone
                && (trmcSite fn.Name fn.Body).IsNone
                && fn.TypeParams = rep.TypeParams
                && zigType fn.Ret = repRet
                && retType fn = repRetText
            )

        let allScalarSameSig =
            rep.Raises = RNever
            && scc
               |> List.forall (fun fn ->
                   (fn.Ret :: (fn.Params |> List.map (fun p -> p.Ty))) |> List.forall isScalarTy
                   && (fn.Params |> List.map (fun p -> zigType p.Ty)) =
                       (rep.Params |> List.map (fun p -> zigType p.Ty))
               )

        if eligible && not allScalarSameSig then
            let mutable sccBase = $"%s{rep.Name}$scc"

            while rootNames.Contains(topIdent sccBase) do
                sccBase <- sccBase + "_"

            rootNames.Add(topIdent sccBase) |> ignore

            let tagMap = scc |> List.mapi (fun i fn -> fn.Name, $"s%d{i}") |> Map.ofList

            for fn in scc do
                sccByMember[fn.Name] <- scc, sccBase, tagMap

    let emittedSccs = HashSet<string>()

    let emitScc (scc: FnInfo list) (sccBase: string) (tagMap: Map<string, string>) =
        let rep = scc.Head
        let generic = not rep.TypeParams.IsEmpty

        let stateTypeLocal =
            if generic then
                "State"
            else
                $"@\"%s{topIdent sccBase}$State\""

        let sccInfo =
            {
                StateTypeName = stateTypeLocal
                TagOf = tagMap
            }

        let variantDecls =
            scc
            |> List.map (fun fn ->
                let tag = tagMap[fn.Name]

                if fn.Params.IsEmpty then
                    tag + ","
                else
                    let fs =
                        fn.Params
                        |> List.mapi (fun i p -> $"a%d{i}: %s{zigType p.Ty}")
                        |> String.concat ", "

                    $"%s{tag}: struct {{ %s{fs} }},"
            )

        let arms =
            scc
            |> List.map (fun fn ->
                let tag = tagMap[fn.Name]
                let emUsed = HashSet(rootNames)
                emUsed.Add "_st" |> ignore
                emUsed.Add "_args" |> ignore
                emUsed.Add "_next" |> ignore

                let em =
                    {
                        Out = StringBuilder()
                        Names = Dictionary()
                        Used = emUsed
                        Mutated = Set.union (assignedIn fn.Body) (storedInto fn.Body)
                        Loop = None
                        Scc = Some sccInfo
                        Self = fn
                        Fns = fns
                        Curried2 = state.Curried2
                        CanTail = false
                        TryLabels = Stack()
                        Adapters = adapters
                        IfaceVts = ifaceVts
                        Counter = 0
                    }

                let binds = List<string>()

                let paramNames =
                    fn.Params
                    |> List.mapi (fun i p ->
                        let name = vname em p

                        let kw =
                            if em.Mutated.Contains p.Id then
                                "var"
                            else
                                "const"

                        binds.Add($"%s{kw} %s{name} = _args.a%d{i};")
                        name
                    )

                stmt em "" fn.Body DReturn
                let rawBody = dropUnreadPaths (em.Out.ToString())
                let unusedText = ensureUsed paramNames rawBody

                let bodyText =
                    (binds |> Seq.map (fun b -> b + "\n") |> String.concat "")
                    + unusedText.Replace("    _ = ", "_ = ")
                    + rawBody

                tag, not fn.Params.IsEmpty, bodyText
            )

        let retTxt = retType rep

        let quota =
            branchQuota (arms |> List.map (fun (_, _, t) -> t) |> String.concat "\n")

        if generic then
            let comptimeParams =
                rep.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            let allText =
                (variantDecls |> String.concat "\n")
                + "\n"
                + retTxt
                + "\n"
                + (arms |> List.map (fun (_, _, t) -> t) |> String.concat "\n")

            let discards =
                rep.TypeParams
                |> List.filter (fun g -> not (allText.Contains(genName g)))
                |> List.map (fun g -> $"    _ = %s{genName g};\n")
                |> String.concat ""

            out
                .AppendLine($"fn %s{topIdent sccBase}(%s{comptimeParams}) type {{")
                .Append(discards)
                .AppendLine("    return struct {")
                .AppendLine("        pub const State = union(enum) {")
            |> ignore

            for v in variantDecls do
                out.AppendLine($"            %s{v}") |> ignore

            out
                .AppendLine("        };")
                .AppendLine($"        pub fn run(init_st: State) %s{retTxt} {{")
                .Append(quota)
                .AppendLine("            var _st = init_st;")
                .AppendLine("            tail: while (true) {")
                .AppendLine("                switch (_st) {")
            |> ignore

            for (tag, hasArgs, armBody) in arms do
                let pat =
                    if hasArgs then
                        $"            .%s{tag} => |_args| {{"
                    else
                        $"            .%s{tag} => {{"

                out.AppendLine($"    %s{pat}") |> ignore

                for lineTxt in armBody.Split('\n') do
                    if lineTxt <> "" then
                        out.AppendLine("                    " + lineTxt) |> ignore

                out.AppendLine("                },") |> ignore

            out
                .AppendLine("                }")
                .AppendLine("            }")
                .AppendLine("        }")
                .AppendLine("    };")
                .AppendLine("}")
                .AppendLine()
            |> ignore
        else
            out.AppendLine($"const %s{stateTypeLocal} = union(enum) {{") |> ignore

            for v in variantDecls do
                out.AppendLine($"    %s{v}") |> ignore

            out
                .AppendLine("};")
                .AppendLine($"fn %s{topIdent sccBase}(init_st: %s{stateTypeLocal}) %s{retTxt} {{")
                .Append(quota)
                .AppendLine("    var _st = init_st;")
                .AppendLine("    tail: while (true) {")
                .AppendLine("        switch (_st) {")
            |> ignore

            for (tag, hasArgs, armBody) in arms do
                let pat =
                    if hasArgs then
                        $"            .%s{tag} => |_args| {{"
                    else
                        $"            .%s{tag} => {{"

                out.AppendLine(pat) |> ignore

                for lineTxt in armBody.Split('\n') do
                    if lineTxt <> "" then
                        out.AppendLine("                " + lineTxt) |> ignore

                out.AppendLine("            },") |> ignore

            out.AppendLine("        }").AppendLine("    }").AppendLine("}").AppendLine()
            |> ignore

    let emitSccMemberWrapper (fn: FnInfo) (sccBase: string) (tagMap: Map<string, string>) =
        let used = HashSet(rootNames)
        let names = Dictionary<int, string>()

        let paramDecls =
            fn.Params
            |> List.mapi (fun i p ->
                let n =
                    let b = cleanIdent p.Base

                    let b =
                        if isReservedIdent b then
                            b + "_"
                        else
                            b

                    let mutable cand = b
                    let mutable k = 1

                    while used.Contains cand do
                        cand <- $"%s{b}_%d{k}"
                        k <- k + 1

                    used.Add cand |> ignore
                    names[p.Id] <- cand
                    cand

                n, $"%s{n}: %s{zigType p.Ty}", i
            )

        let sigParams =
            paramDecls |> List.map (fun (_, decl, _) -> decl) |> String.concat ", "

        let tag = tagMap[fn.Name]

        let visibility =
            if fn.IsLocal then
                ""
            else
                "pub "

        let generic = not fn.TypeParams.IsEmpty

        let tArgs = fn.TypeParams |> List.map genName |> String.concat ", "

        let stateRef =
            if generic then
                $"%s{topIdent sccBase}(%s{tArgs}).State"
            else
                $"@\"%s{topIdent sccBase}$State\""

        let initVal =
            if fn.Params.IsEmpty then
                $"@as(%s{stateRef}, .%s{tag})"
            else
                let fs =
                    paramDecls
                    |> List.map (fun (n, _, i) -> $".a%d{i} = %s{n}")
                    |> String.concat ", "

                $"%s{stateRef}{{ .%s{tag} = .{{ %s{fs} }} }}"

        let dispatchCall =
            if generic then
                $"%s{topIdent sccBase}(%s{tArgs}).run(_init)"
            else
                $"%s{topIdent sccBase}(_init)"

        let tailStmt =
            match isVoid fn.Ret, fn.Raises with
            | true, RNever -> $"%s{dispatchCall};"
            | true, RAlways -> $"try %s{dispatchCall};"
            | true, RDepends _ ->
                $"if (comptime fable_rt.isRaised(@TypeOf(%s{dispatchCall}))) try %s{dispatchCall} else %s{dispatchCall};"
            | false, RNever -> $"return %s{dispatchCall};"
            | false, RAlways -> $"return try %s{dispatchCall};"
            | false, RDepends _ ->
                $"if (comptime fable_rt.isRaised(@TypeOf(%s{dispatchCall}))) return try %s{dispatchCall} else return %s{dispatchCall};"

        if generic then
            let comptimeParams =
                fn.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            let sigDecl =
                if hasManaged fn && not fn.IsLocal then
                    $"        pub const sig = %s{sigName fn.Name};\n"
                else
                    ""

            out
                .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{comptimeParams}) type {{")
                .AppendLine("    return struct {")
                .Append(sigDecl)
                .AppendLine($"        pub fn call(%s{sigParams}) %s{retType fn} {{")
                .AppendLine($"            const _init: %s{stateRef} = %s{initVal};")
                .AppendLine($"            %s{tailStmt}")
                .AppendLine("        }")
                .AppendLine("    };")
                .AppendLine("}")
            |> ignore
        else
            out
                .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{sigParams}) %s{retType fn} {{")
                .AppendLine($"    const _init: %s{stateRef} = %s{initVal};")
                .AppendLine($"    %s{tailStmt}")
                .AppendLine("}")
            |> ignore

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

    for fn in state.Fns do
        try
            match sccByMember.TryGetValue fn.Name with
            | true, (scc, sccBase, tagMap) ->
                if emittedSccs.Add sccBase then
                    emitScc scc sccBase tagMap

                emitSccMemberWrapper fn sccBase tagMap
            | _ -> emitFunction out rootNames adapters ifaceVts fns state.Curried2 fn
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    // the classes that take part in inheritance: the type of each, with its tables of virtual
    // members (function values of the functions that implement them)
    for d in state.Objs do
        let generic = not d.TypeParams.IsEmpty

        let emitThunk (indent: string) (name, partPtr, parts, field, fnTy) =
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
                        $"%s{indent}fn %s{topIdent name}(env: ?*fable_rt.Env, this: fable_rt.Obj%s{ps}) fable_rt.Raised!%s{zigType ret} {{"
                    )
                    .AppendLine($"%s{indent}    _ = env;")
                    .AppendLine(
                        $"%s{indent}    const f = fable_rt.dup(fable_rt.objPart(%s{zigType partPtr}, &[_]type{{ %s{parts} }}, this).%s{fieldIdent field});"
                    )
                    .AppendLine($"%s{indent}    defer fable_rt.drop(f);")
                    .AppendLine($"%s{indent}    return f.code(f.env, fable_rt.dup(this)%s{xs});")
                    .AppendLine($"%s{indent}}}")
                |> ignore
            | _ -> ()

        // (an object expression's class: each member calls the function value the object holds;
        // a generic one defines its thunks inside its type builder where the type params live)
        if not generic then
            for th in d.Thunks do
                emitThunk "" th

        let decls = System.Collections.Generic.List<string>()

        // (a function as the code of a function value: an adapter, generic in the class's type
        // parameters when the class is; class vtable / ToString adapters borrow `this`)
        let adapterFor (target: string) (typeArgs: Ty list) (fnTy: Ty) =
            let key =
                target
                + "<"
                + (typeArgs |> List.map zigType |> String.concat ",")
                + ">"
                + (if generic then
                       "/" + String.concat "," d.TypeParams
                   else
                       "")
                + "#vt"

            match adapters.TryGetValue key with
            | true, a -> a
            | _ ->
                let a =
                    {
                        Name = $"@\"%s{target}$fn%d{adapters.Count}\""
                        Target = target
                        Target2 = None
                        TypeArgs = typeArgs
                        NCaptures = 0
                        CaptureTys = []
                        FnTy = fnTy
                        BorrowFirst = true
                        Gens = d.TypeParams
                    }

                adapters[key] <- a
                a

        let tables =
            d.Tables
            |> List.mapi (fun i t ->
                match t with
                | Some(vtTy, entries) ->
                    let name = topIdent $"%s{d.TypeName}_vt%d{i}"

                    let inits =
                        entries
                        |> List.map (fun (slot, target, typeArgs, fnTy) ->
                            if target.StartsWith("@raw:", System.StringComparison.Ordinal) then
                                // (a function of this file with the calling convention of a function value)
                                $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{topIdent (target.Substring 5)} }}"
                            else
                                let adapter = adapterFor target typeArgs fnTy
                                $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{adapterRef adapter}.code }}"
                        )
                        |> String.concat ", "

                    decls.Add($"const %s{name}: %s{zigType vtTy} = .{{ %s{inits} }};")
                    "&" + name
                | None -> "null"
            )
            |> String.concat ", "

        let parent =
            match d.Parent with
            | Some p -> p
            | None -> "null"

        // (the class's ToString, as the code of a function value)
        let toString =
            match d.ToString with
            | Some(target, typeArgs) ->
                if target.StartsWith("@raw:", System.StringComparison.Ordinal) then
                    topIdent (target.Substring 5)
                else
                    let fnTy = TFn([ TPrim "fable_rt.Obj"; tVoid ], tStr)
                    $"%s{adapterRef (adapterFor target typeArgs fnTy)}.code"
            | None -> "null"

        let value =
            if d.Overrides.IsEmpty then
                $"fable_rt.objType(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString})"
            else
                let hook (name: string) (asObj: string) =
                    match d.Overrides |> List.tryFind (fun (h, _) -> h = name) with
                    | Some(_, fn) -> $"%s{hookOf fn}.%s{asObj}"
                    | None -> "null"

                let eq = hook "equals" "objEquals"
                let hs = hook "hash" "objHash"
                let cmp = hook "compare" "objCompare"

                $"fable_rt.objTypeWith(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString}, %s{eq}, %s{hs}, %s{cmp})"

        // (the interfaces the class implements, with its tables of them: `o :?> I`)
        let value =
            if d.Ifaces.IsEmpty then
                value
            else
                let entries =
                    d.Ifaces
                    |> List.map (fun (ifaceTy, slots) ->
                        let vt = ifaceVtFor ifaceVts ifaceTy IVtObj "obj" [] slots

                        $".{{ .id = fable_rt.ifaceId(%s{zigType ifaceTy}), .vt = @ptrCast(&%s{ifaceVtRef vt}.vt) }}"
                    )
                    |> String.concat ", "

                $"fable_rt.withIfaces(%s{value}, &.{{ %s{entries} }})"

        if generic then
            let comptimeParams =
                d.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            out
                .AppendLine($"pub fn %s{topIdent d.TypeName}(%s{comptimeParams}) *const fable_rt.ObjType {{")
                .AppendLine("    return &struct {")
            |> ignore

            for th in d.Thunks do
                emitThunk "        " th

            for dl in decls do
                out.AppendLine("        " + dl) |> ignore

            out.AppendLine($"        const ty: fable_rt.ObjType = %s{value};").AppendLine("    }.ty;").AppendLine("}")
            |> ignore
        else
            for dl in decls do
                out.AppendLine(dl) |> ignore

            out.AppendLine($"pub const %s{topIdent d.TypeName}: fable_rt.ObjType = %s{value};")
            |> ignore

    for a in adapters.Values do
        emitAdapter out fns a

    for vt in ifaceVts.Values do
        emitIfaceVt out fns vt

    // (a file that uses async: at the end of each test, the work it started and left waiting
    // is run on, so that it finishes within the test)
    let asyncAlias =
        state.Imports
        |> Seq.tryFind (fun kv -> System.IO.Path.GetFileNameWithoutExtension(kv.Key) = "Async")
        |> Option.map (fun kv -> kv.Value)

    for (name, fn) in state.Tests do
        let quoted = name.Replace("\\", "\\\\").Replace("\"", "\\\"")

        out
            .AppendLine("test \"" + quoted + "\" {")
            // (every test is a test of leaks too, where cells are counted: what is alive before the
            // modules' values are made is what is alive after they are given up again, so what
            // a test leaves in a module's state is not taken for a leak; each test starts from
            // the modules' first values)
            .AppendLine("    const fable_live = fable_rt.testLiveBefore();")
            .AppendLine("    try fable_rt.testInit(@\"$init\");")
            .AppendLine($"    try fable_rt.testCase(%s{callTarget fn});")
        |> ignore

        match asyncAlias with
        | Some alias -> out.AppendLine($"    try fable_rt.testCase(%s{alias}.finishPending);") |> ignore
        | None -> ()

        out.AppendLine("    @\"$deinit\"();").AppendLine("    try fable_rt.testNoLeak(fable_live);")
        |> ignore

        out.AppendLine("}") |> ignore

    // The F# entry point returns the process exit code as an int; Zig's `main` returns a u8.
    // In builds that count cells, a program that ends with cells still allocated says so.
    for fn in state.Fns do
        if fn.IsEntryPoint then
            // (`main argv`: the command line's arguments, which the program owns or which
            // are given up after it)
            let takesArgs = not fn.Params.IsEmpty

            let mainCallExpr =
                if takesArgs then
                    $"%s{topIdent fn.Name}(undefined)"
                else
                    $"%s{topIdent fn.Name}()"

            out.AppendLine($"pub const @\"$main_raises\" = fable_rt.isRaised(@TypeOf(%s{mainCallExpr}));")
            |> ignore

            out
                .AppendLine(
                    if takesArgs then
                        "pub fn main(init: @import(\"std\").process.Init.Minimal) u8 {"
                    else
                        "pub fn main() u8 {"
                )
                .AppendLine(
                    "    if (comptime fable_rt.isRaised(@TypeOf(@\"$init\"()))) (@\"$init\"() catch { fable_rt.uncaught(); return 134; }) else @\"$init\"();"
                )
            |> ignore

            if takesArgs then
                out.AppendLine("    const argv = fable_rt.io.programArgs(init.args);") |> ignore

            let call =
                if takesArgs then
                    $"%s{topIdent fn.Name}(argv)"
                else
                    $"%s{topIdent fn.Name}()"

            let argvOwned = takesArgs && (fn.Modes |> List.tryHead = Some MOwned)

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

            if takesArgs && not argvOwned then
                out.AppendLine("    fable_rt.drop(argv);") |> ignore

            out
                .AppendLine("    @\"$deinit\"();")
                .AppendLine("    if (fable_rt.leaked()) return 70;")
                .AppendLine("    return @truncate(@as(u32, @bitCast(code)));")
                .AppendLine("}")
            |> ignore

    let bodyText = out.ToString()

    let usesExnShow =
        state.Tests.Count > 0
        || bodyText.Contains "fable_rt.anyText"
        || bodyText.Contains "fable_rt.toText"
        || bodyText.Contains "fable_rt.genericText"
        || bodyText.Contains "fable_rt.exnMessage"
        || bodyText.Contains "fable_rt.exnText"
        || bodyText.Contains "fable_rt.toString"
        || bodyText.Contains "fable_rt.writeToString"
        || bodyText.Contains "fable_rt.threadStart"
        || bodyText.Contains ".kind = 'A'"
        || bodyText.Contains ".kind = 'O'"

    bodyText.Replace(
        "__FABLE_EXN_SHOW__",
        if usesExnShow then
            "true"
        else
            "false"
    )
