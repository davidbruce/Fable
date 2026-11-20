/// Emission: ownership IR -> Zig source text.
module internal Fable.Transforms.Zig.EmitExpr

open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Fable.Transforms.Zig.IR

type Dest =
    | DReturn
    | DTcRet
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
        /// true if any live function-value or vtable site references this adapter's `tcode`
        mutable NeedsTcode: bool
        /// the type parameters of the surrounding function that the types above mention: the
        /// adapter is generic in them
        Gens: string list
    }

/// A stack-allocated known lambda passed to a non-escaping `callK` HOF parameter.
type KnownDecl =
    {
        Name: string
        Target: string
        Target2: string option
        TypeArgs: Ty list
        NCaptures: int
        CaptureTys: Ty list
        FnTy: Ty
        Gens: string list
        mutable NeedsToFunc: bool
    }

type IfaceVtKind =
    | IVtObj
    | IVtBox of Ty
    | IVtCaptures of Ty list
    | IVtUpcast of Ty

/// A stack-allocated known interface / object-expression descriptor for `callK` / `callHof`.
type KnownIfaceDecl =
    {
        Name: string
        IfaceTy: Ty
        IsOpt: bool
        Kind: IfaceVtKind
        Slots: (string * (string * Ty list)) list
        Gens: string list
        mutable NeedsToFunc: bool
    }

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
        /// tail recursion modulo cons inside a fused mutual-recursion state machine
        Trmc: bool
        /// empty-case / nullOf plug when an exception leaves the SCC mid-construction
        Plug: string option
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
        /// stack-allocated known lambda descriptors made so far
        Knowns: Dictionary<string, KnownDecl>
        /// stack-allocated known interface / object-expression descriptors made so far
        KnownIfaces: Dictionary<string, KnownIfaceDecl>
        /// static vtables of fat-pointer interfaces built so far
        IfaceVts: Dictionary<string, IfaceVt>
        /// parameter IDs of this `callK` clone that have type `anytype`
        KParams: Set<int>
        /// true when emitting the body of a `$tcbody` entry point (`DTcRet` convention)
        IsTc: bool
        /// module aliases of imported F# files (`state.Imports.Values`)
        FableAliases: HashSet<string>
        /// same-file functions emitted without `$tc` / `$chain`
        NoTcFns: HashSet<string>
        /// functions explicitly opted out via `[<NoTailCalls>]` (or file-level `NoTailCallsFile`)
        NoTailCalls: HashSet<string>
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

/// The constant that states which parameters of a public function do not escape (`callK`).
let noEscapeName (f: string) =
    match f.IndexOf '.' with
    | -1 -> $"@\"%s{topIdent f}$noescape\""
    | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$noescape\""

/// The constant that publishes a public function's field-sensitive store summary (`$stores`).
let storesName (f: string) =
    match f.IndexOf '.' with
    | -1 -> $"@\"%s{topIdent f}$stores\""
    | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$stores\""

/// The constant that publishes whether a public function actually needs the tail-call chain (`$chain`).
let chainName (f: string) =
    match f.IndexOf '.' with
    | -1 -> $"@\"%s{topIdent f}$chain\""
    | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$chain\""

/// Comptime check for whether a cross-file function publishes `$chain == true`.
let extChainCheck (extF: string) =
    match extF.IndexOf '.' with
    | -1 -> chainName extF
    | i ->
        let m = extF.Substring(0, i)
        let f = topIdent (extF.Substring(i + 1))
        $"(@hasDecl(%s{m}, \"%s{f}$chain\") and %s{m}.@\"%s{f}$chain\")"

let fnHasTcBody (fn: FnInfo) =
    fn.NeedsChain || not fn.PendingChainDeps.IsEmpty

let fnChainConstExpr (fn: FnInfo) =
    if fn.NeedsChain then
        "true"
    elif fn.PendingChainDeps.IsEmpty then
        "false"
    else
        fn.PendingChainDeps
        |> List.distinct
        |> List.map extChainCheck
        |> String.concat " or "

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

let kRef (f: string) (typeArgs: Ty list) =
    match typeArgs with
    | [] ->
        match f.IndexOf '.' with
        | -1 -> $"@\"%s{topIdent f}$k\""
        | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$k\""
    | _ ->
        typeArgs
        |> List.map zigType
        |> String.concat ", "
        |> sprintf "%s(%s).callK" (callTarget f)

let fnRefTc (f: string) (typeArgs: Ty list) =
    match typeArgs with
    | [] ->
        match f.IndexOf '.' with
        | -1 -> $"@\"%s{topIdent f}$tc\""
        | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$tc\""
    | _ ->
        typeArgs
        |> List.map zigType
        |> String.concat ", "
        |> sprintf "%s(%s).tc" (callTarget f)

let fnTcBodyRef (f: string) (typeArgs: Ty list) =
    match typeArgs with
    | [] ->
        match f.IndexOf '.' with
        | -1 -> $"@\"%s{topIdent f}$tcbody\""
        | i -> f.Substring(0, i + 1) + $"@\"%s{topIdent (f.Substring(i + 1))}$tcbody\""
    | _ ->
        typeArgs
        |> List.map zigType
        |> String.concat ", "
        |> sprintf "%s(%s).tcbody" (callTarget f)

/// The namespace of an adapter, where it is used.
let adapterRef (a: Adapter) =
    match a.Gens with
    | [] -> a.Name
    | gens -> gens |> List.map genName |> String.concat ", " |> sprintf "%s(%s)" a.Name

let knownRef (k: KnownDecl) =
    match k.Gens with
    | [] -> k.Name
    | gens -> gens |> List.map genName |> String.concat ", " |> sprintf "%s(%s)" k.Name

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

/// Get or register a stack-allocated `KnownDecl` descriptor for a known closure expression.
let rec ensureKnownDecl (em: Em) (target: string) (typeArgs: Ty list) (caps: Expr list) (ty: Ty) : KnownDecl =
    let target2 = resolveCurried2 em target typeArgs caps.Length ty
    let capTys = caps |> List.map typeOf

    let key =
        "kn:"
        + target
        + "<"
        + (typeArgs |> List.map tyKey |> String.concat ",")
        + ">:"
        + (capTys |> List.map tyKey |> String.concat ",")
        + "->"
        + tyKey ty
        + (
            match target2 with
            | Some t2 -> "#2:" + t2
            | None -> ""
        )

    match em.Knowns.TryGetValue key with
    | true, k -> k
    | _ ->
        let k =
            {
                Name = $"@\"%s{cleanIdent target}$kn%d{em.Knowns.Count}\""
                Target = target
                Target2 = target2
                TypeArgs = typeArgs
                NCaptures = caps.Length
                CaptureTys = capTys
                FnTy = ty
                Gens = freeGens (ty :: typeArgs @ capTys)
                NeedsToFunc = false
            }

        em.Knowns[key] <- k
        k

and knownIfaceRef (k: KnownIfaceDecl) =
    match k.Gens with
    | [] -> k.Name
    | gens -> gens |> List.map genName |> String.concat ", " |> sprintf "%s(%s)" k.Name

and ifaceSrcMeta (src: IfaceSource) =
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

/// Get or register a stack-allocated `KnownIfaceDecl` descriptor for a known interface expression.
and ensureKnownIfaceDecl
    (em: Em)
    (ifaceTy: Ty)
    (src: IfaceSource)
    (slots: (string * (string * Ty list)) list)
    (isOpt: bool)
    : KnownIfaceDecl
    =
    let kind, srcKey, srcTys = ifaceSrcMeta src

    let slotKeyStr =
        slots
        |> List.map (fun (s, (t, tys)) -> s + "=" + t + "<" + (tys |> List.map tyKey |> String.concat ",") + ">")
        |> String.concat ";"

    let key = $"ki:%b{isOpt}:%s{tyKey ifaceTy}|%s{srcKey}|%s{slotKeyStr}"

    match em.KnownIfaces.TryGetValue key with
    | true, k -> k
    | _ ->
        let slotTypeArgs = slots |> List.collect (fun (_, (_, tys)) -> tys)

        let k =
            {
                Name = $"@\"fable_known_iface$ki%d{em.KnownIfaces.Count}\""
                IfaceTy = ifaceTy
                IsOpt = isOpt
                Kind = kind
                Slots = slots
                Gens = freeGens (ifaceTy :: srcTys @ slotTypeArgs)
                NeedsToFunc = false
            }

        em.KnownIfaces[key] <- k
        k

/// Format a cross-file call concisely using `fable_rt.callM`/`callG`, `callHof*`, `callAssumed*`,
/// or their `xcall*` / `xcallPlain` raising wrappers.
and formatCrossCall
    (em: Em)
    (f: string)
    (typeArgs: Ty list)
    (xs: Expr list)
    (t: Ty)
    (ds: Var list option)
    (assumedFrom: int list option)
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
            let mutable hasKnown = false

            let usesChars, args =
                xs
                |> List.map (fun x ->
                    match x with
                    | EKnown(target, kTys, caps, cloTy) ->
                        hasKnown <- true
                        let kn = ensureKnownDecl em target kTys caps cloTy
                        kn.NeedsToFunc <- true
                        'g', ex em x
                    | EKnownIface(ifaceTy, src, slots, isOpt) ->
                        hasKnown <- true
                        let ki = ensureKnownIfaceDecl em ifaceTy src slots isOpt
                        ki.NeedsToFunc <- true
                        'g', ex em x
                    | _ ->
                        if hasKnownOrKArg em.KParams x then
                            hasKnown <- true

                        match x with
                        | EUse(UPlain, inner) -> 'p', ex em inner
                        | EUse(UKeep, inner) -> 'k', ex em inner
                        | EUse(UGive, inner) -> 'g', ex em inner
                        | _ ->
                            let u =
                                if isManaged (typeOf x) then
                                    'g'
                                else
                                    'p'

                            u, ex em x
                )
                |> List.unzip

            let usesStr = System.String(Array.ofList usesChars)

            let argsTuple =
                match args with
                | [] -> ".{}"
                | _ -> args |> String.concat ", " |> sprintf ".{ %s }"

            let assumedArg =
                match assumedFrom with
                | None -> ""
                | Some [] -> ".{}, "
                | Some js ->
                    js
                    |> List.sort
                    |> List.map string<int>
                    |> String.concat ", "
                    |> sprintf ".{ %s }, "

            let callMName, callGName, xcallMName, xcallGName =
                if hasKnown && assumedFrom.IsSome then
                    "callHofAssumedM", "callHofAssumedG", "xcallHofAssumedM", "xcallHofAssumedG"
                elif hasKnown then
                    "callHofM", "callHofG", "xcallHofM", "xcallHofG"
                elif assumedFrom.IsSome then
                    "callAssumedM", "callAssumedG", "xcallAssumedM", "xcallAssumedG"
                else
                    "callM", "callG", "xcallM", "xcallG"

            let mkCall (mFn: string) (gFn: string) (dropsText: string) =
                if typeArgs.IsEmpty then
                    $"fable_rt.%s{mFn}(%s{modAlias}, \"%s{memberName}\", %s{assumedArg}\"%s{usesStr}\", %s{argsTuple}, %s{dropsText})"
                else
                    let gns =
                        typeArgs
                        |> List.map zigType
                        |> String.concat ", "
                        |> sprintf "%s.%s(%s)" modAlias memberName

                    $"fable_rt.%s{gFn}(%s{gns}, %s{assumedArg}\"%s{usesStr}\", %s{argsTuple}, %s{dropsText})"

            match ds with
            | Some _ when canPlainTry em && em.Self.Raises = RAlways ->
                Some $"(try %s{mkCall xcallMName xcallGName errDrops})"
            | Some _ when canPlainTry em -> Some $"(try fable_rt.lift(%s{mkCall callMName callGName errDrops}))"
            | _ -> Some(mkCall callMName callGName ".{}")
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
    && (
        match em.Scc with
        | Some {
                   Trmc = true
                   Plug = Some _
               } -> false
        | _ -> true
    )

and hasKnownOrKArg (kParams: Set<int>) (e: Expr) =
    match e with
    | EKnown _
    | EKnownIface _ -> true
    | EVar v -> kParams.Contains v.Id
    | EGet(EVar v, PSome, _) -> kParams.Contains v.Id
    | EUse(_, x) -> hasKnownOrKArg kParams x
    | _ -> false

and isKParamIfaceRecv (kParams: Set<int>) (r: Expr) =
    match r with
    | EVar v -> kParams.Contains v.Id
    | EGet(EVar v, PSome, _) -> kParams.Contains v.Id
    | _ -> false

and extractUses (em: Em) (xs: Expr list) : string * string =
    let usesChars, argTexts =
        xs
        |> List.map (fun x ->
            match x with
            | EUse(UPlain, inner) -> 'p', ex em inner
            | EUse(UKeep, inner) -> 'k', ex em inner
            | EUse(UGive, inner) -> 'g', ex em inner
            | _ ->
                let u =
                    if isManaged (typeOf x) then
                        'g'
                    else
                        'p'

                u, ex em x
        )
        |> List.unzip

    let usesStr = System.String(Array.ofList usesChars)

    let argsTuple =
        match argTexts with
        | [] -> ".{}"
        | _ -> argTexts |> String.concat ", " |> sprintf ".{ %s }"

    usesStr, argsTuple

and resolveCurried2 (em: Em) (target: string) (typeArgs: Ty list) (nCaps: int) (ty: Ty) : string option =
    match ty with
    | TFn([ tyA ], TFn([ tyB ], tyR)) ->
        match em.Curried2.TryGetValue target with
        | true, t2 ->
            match em.Fns.TryGetValue t2 with
            | true, fn2 when fn2.Params.Length = nCaps + 2 ->
                let inst =
                    if fn2.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip fn2.TypeParams typeArgs)
                    else
                        Map.empty

                let rest2 = List.skip nCaps fn2.Params

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

and adapterForClosure
    (adapters: Dictionary<string, Adapter>)
    (target: string)
    (target2: string option)
    (typeArgs: Ty list)
    (capTys: Ty list)
    (ty: Ty)
    : Adapter
    =
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

    match adapters.TryGetValue key with
    | true, a -> a
    | _ ->
        let a =
            {
                Name = $"@\"%s{target}$fn%d{adapters.Count}\""
                Target = target
                Target2 = target2
                TypeArgs = typeArgs
                NCaptures = capTys.Length
                CaptureTys = capTys
                FnTy = ty
                BorrowFirst = false
                NeedsTcode = false
                Gens = freeGens (ty :: typeArgs @ capTys)
            }

        adapters[key] <- a
        a

and ex (em: Em) (e: Expr) : string =
    match e with
    | EVar v -> vname em v
    | ELit(s, _) -> s
    | EUnit -> "{}"
    | EUse(_, x) -> ex em x
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
            if
                isManaged argT
                || holdsDecimal argT
                || holdsLayoutUnion argT
                || argT = TPrim "fable_rt.reflect.Type"
            then
                $"fable_rt.eql(%s{x}, %s{y})"
            else
                $"std.meta.eql(%s{x}, %s{y})"
        | "tag", [ x ] -> $"@as(i32, @intFromEnum(%s{x}))"
        // (the source type is spelled out: a literal has no type of its own in Zig)
        | "conv", [ x ] -> $"fable_rt.conv(%s{zigType t}, @as(%s{zigType argT}, %s{x}))"
        | _ -> fail None "internal: unknown primitive %s/%d" op a.Length
    | ECall(f, typeArgs, xs, t) ->
        match formatCrossCall em f typeArgs xs t None None with
        | Some txt -> txt
        | None ->
            let args = xs |> List.map (ex em) |> String.concat ", "

            let callee =
                if xs |> List.exists (hasKnownOrKArg em.KParams) then
                    kRef f typeArgs
                else
                    fnRef f typeArgs

            $"%s{callee}(%s{args})"
    | EAssumedRet(js, ECall(f, typeArgs, xs, t)) ->
        match formatCrossCall em f typeArgs xs t None (Some js) with
        | Some txt -> txt
        | None -> ex em (ECall(f, typeArgs, xs, t))
    | EAssumedRet(_, call) -> ex em call
    | ECallClo(EVar v, xs, resTy) when em.KParams.Contains v.Id ->
        let usesStr, argsTuple = extractUses em xs
        $"fable_rt.invokeK(%s{zigType resTy}, %s{vname em v}, \"%s{usesStr}\", %s{argsTuple}, .{{}})"
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
    | ECallIface(r, slot, xs, resTy) when isKParamIfaceRecv em.KParams r ->
        let usesStr, argsTuple = extractUses em xs
        $"fable_rt.invokeIfaceK(%s{zigType resTy}, %s{ex em r}, \"%s{cleanIdent slot}\", \"%s{usesStr}\", %s{argsTuple}, .{{}})"
    | ECallIface(r, slot, xs, _) ->
        let recv = ex em r
        let args = $"%s{recv}.data" :: (xs |> List.map (ex em)) |> String.concat ", "
        $"%s{recv}.vt.%s{fieldIdent slot}(%s{args})"
    | EIface(ifaceTy, src, slots) ->
        let kind, srcKey, srcTys = ifaceSrcMeta src

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
    | EKnown(target, typeArgs, caps, ty) ->
        let kn = ensureKnownDecl em target typeArgs caps ty
        let ns = knownRef kn

        if caps.IsEmpty then
            $"%s{ns}{{}}"
        else
            let inits =
                caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

            $"%s{ns}{{ .caps = .{{ %s{inits} }} }}"
    | EKnownIface(ifaceTy, src, slots, isOpt) ->
        let ki = ensureKnownIfaceDecl em ifaceTy src slots isOpt
        let ns = knownIfaceRef ki

        match src with
        | ISrcCaptures [] -> $"%s{ns}{{}}"
        | ISrcCaptures caps ->
            let inits =
                caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

            $"%s{ns}{{ .caps = .{{ %s{inits} }} }}"
        | ISrcValue v -> $"%s{ns}{{ .val = %s{ex em v} }}"
        | ISrcUpcast _ -> fail None "internal: EKnownIface cannot wrap upcast"
    | EClosure(target, typeArgs, caps, ty) ->
        let target2 = resolveCurried2 em target typeArgs caps.Length ty

        let adapter =
            adapterForClosure em.Adapters target target2 typeArgs (caps |> List.map typeOf) ty

        let ns = adapterRef adapter

        let suppressTcode =
            em.NoTailCalls.Contains em.Self.Name || em.NoTailCalls.Contains target

        let ctxArg, fnSuffix =
            if em.IsTc then
                "ctx, ", "Reuse"
            else
                "", ""

        if suppressTcode then
            if adapter.Target2.IsSome then
                if caps.IsEmpty then
                    $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code, .code2 = %s{ns}.code2 }}"
                else
                    let inits =
                        caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

                    $"fable_rt.closure2%s{fnSuffix}(%s{ctxArg}%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code, %s{ns}.code2)"
            elif caps.IsEmpty then
                $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code }}"
            else
                let inits =
                    caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

                $"fable_rt.closure%s{fnSuffix}(%s{ctxArg}%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code)"
        else
            adapter.NeedsTcode <- true

            let paramTysStr =
                match ty with
                | TFn(argTys, _) -> argTys |> List.map zigType |> String.concat ", "
                | _ -> ""

            let tcodeExpr =
                $"if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) &%s{ns}.tcode else null"

            if adapter.Target2.IsSome then
                let tcode2Expr =
                    match ty with
                    | TFn([ tyA ], TFn([ tyB ], _)) ->
                        $"if (comptime fable_rt.fitsTailArgs(&.{{ %s{zigType tyA}, %s{zigType tyB} }})) &%s{ns}.tcode2 else null"
                    | _ -> "null"

                if caps.IsEmpty then
                    $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code, .code2 = %s{ns}.code2, .tcode = %s{tcodeExpr}, .tcode2 = %s{tcode2Expr} }}"
                else
                    let inits =
                        caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

                    $"fable_rt.closure2Tc%s{fnSuffix}(%s{ctxArg}%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code, %s{ns}.code2, %s{tcodeExpr}, %s{tcode2Expr})"
            elif caps.IsEmpty then
                $"%s{zigType ty}{{ .env = null, .code = %s{ns}.code, .tcode = %s{tcodeExpr} }}"
            else
                let inits =
                    caps |> List.mapi (fun i c -> $".c%d{i} = %s{ex em c}") |> String.concat ", "

                $"fable_rt.closureTc%s{fnSuffix}(%s{ctxArg}%s{zigType ty}, %s{ns}.Env, .{{ %s{inits} }}, %s{ns}.code, %s{tcodeExpr})"
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
        | ECallClo(EVar v, xs, resTy) when em.KParams.Contains v.Id ->
            let usesStr, argsTuple = extractUses em xs

            if canPlainTry em && em.Self.Raises = RAlways then
                let errDrops =
                    match ds with
                    | [] -> ".{}"
                    | vs -> vs |> List.map (vname em) |> String.concat ", " |> sprintf ".{ %s }"

                $"(try fable_rt.invokeK(%s{zigType resTy}, %s{vname em v}, \"%s{usesStr}\", %s{argsTuple}, %s{errDrops}))"
            else
                let edge = edgeText em ds
                $"(fable_rt.invokeK(%s{zigType resTy}, %s{vname em v}, \"%s{usesStr}\", %s{argsTuple}, .{{}}) catch %s{edge})"
        | ECallIface(r, slot, xs, resTy) when isKParamIfaceRecv em.KParams r ->
            let usesStr, argsTuple = extractUses em xs

            if canPlainTry em && em.Self.Raises = RAlways then
                let errDrops =
                    match ds with
                    | [] -> ".{}"
                    | vs -> vs |> List.map (vname em) |> String.concat ", " |> sprintf ".{ %s }"

                $"(try fable_rt.invokeIfaceK(%s{zigType resTy}, %s{ex em r}, \"%s{cleanIdent slot}\", \"%s{usesStr}\", %s{argsTuple}, %s{errDrops}))"
            else
                let edge = edgeText em ds
                $"(fable_rt.invokeIfaceK(%s{zigType resTy}, %s{ex em r}, \"%s{cleanIdent slot}\", \"%s{usesStr}\", %s{argsTuple}, .{{}}) catch %s{edge})"
        | ECall(f, typeArgs, xs, t) when f.Contains "." && canPlainTry em ->
            match formatCrossCall em f typeArgs xs t (Some ds) None with
            | Some txt -> txt
            | None ->
                let c = ex em call
                let edge = edgeText em ds
                $"(fable_rt.lift(%s{c}) catch %s{edge})"
        | EAssumedRet(js, ECall(f, typeArgs, xs, t)) when f.Contains "." && canPlainTry em ->
            match formatCrossCall em f typeArgs xs t (Some ds) (Some js) with
            | Some txt -> txt
            | None ->
                let c = ex em call
                let edge = edgeText em ds
                $"(fable_rt.lift(%s{c}) catch %s{edge})"
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
                    // whether this function raises is only known when the Zig is compiled (see
                    // fable_rt.lift)
                    $"(fable_rt.lift(%s{c}) catch %s{edge})"
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
        | TEnt(e, _) when e.Kind = KRefRecord ->
            let init = $".{{ %s{inits (caseFields t case)} }}"

            match tok with
            | Some tk -> $"fable_rt.newReuse(%s{zigType t}, &%s{vname em tk}, %s{init})"
            | None -> $"fable_rt.new(%s{zigType t}, %s{init})"
        | TEnt(e, _) when e.Kind = KRecord && e.Layout = LayoutUnion ->
            let fs = caseFields t case

            if fs.Length <= 1 then
                $"%s{zigType t}{{ %s{inits fs} }}"
            else
                $"std.mem.zeroes(%s{zigType t})"
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
        | PSome ->
            match x with
            | EVar u when em.KParams.Contains u.Id -> $"fable_rt.unwrapIfaceK(%s{o})"
            | _ -> o + ".?"
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
        match em.Loop, em.Scc with
        | Some {
                   Trmc = true
                   Plug = Some plug
               },
          _
        | _,
          Some {
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
