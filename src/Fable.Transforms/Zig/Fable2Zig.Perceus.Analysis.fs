/// The ownership passes on the IR: borrow inference for parameters and results, then Perceus
/// (dup/drop insertion, drop-unpack and reuse of dead cells).
module internal Fable.Transforms.Zig.PerceusAnalysis

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Facts

type P =
    {
        State: FileState
        /// the functions of the file being compiled, by name
        Fns: Dictionary<string, FnInfo>
        /// lookup for cross-file function facts by qualified IR call name (`alias.name`)
        Ext: string -> Facts.FnFacts option
        StoredFields: Dictionary<string, Set<string>>
        CallsCallback: HashSet<string>
        CallsExtStore: HashSet<string>
        ExtStoreDeps: Dictionary<string, Set<string>>
        PureStdlibAliases: HashSet<string>
    }

// =============================================================================================
// Normalisation
// =============================================================================================

/// Remove `let x = <pure> in body` when x is unused, and what follows a `raise`.
/// If evaluating `e` always ends in a raise: `e`, with `ty` as the type that is expected where
/// it stands. What comes after it can never run, and Zig refuses code that cannot.
/// A call into the runtime that takes its first argument over (the others it borrows).
let ownsFirst (macro: string) =
    macro.StartsWith("fable_rt.strAppend(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayBufPush(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayMapBufNew(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayMapBufPush(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayFilterBufNew(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayMapInPlace(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayMapiInPlace(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayFilterInPlace(", System.StringComparison.Ordinal)

let rec asRaise (ty: Ty) (e: Expr) : Expr option =
    match e with
    | ERaise(x, _) -> Some(ERaise(x, ty))
    | ELet(v, r, b) -> asRaise ty b |> Option.map (fun b' -> ELet(v, r, b'))
    | ESeq(a, b) -> asRaise ty b |> Option.map (fun b' -> ESeq(a, b'))
    | EIf(c, t, f, _) ->
        match asRaise ty t, asRaise ty f with
        | Some t', Some f' -> Some(EIf(c, t', f', ty))
        | _ -> None
    | _ -> None

let rec cleanup (e: Expr) : Expr =
    match e with
    | ELet(_, ERaise(x, _), body) -> ERaise(x, typeOf body)
    | ESeq(ERaise(x, _), b) -> ERaise(x, typeOf b)
    | ESeq(a, b) when (asRaise (typeOf b) a).IsSome -> cleanup (asRaise (typeOf b) a).Value
    | ELet(_, rhs, body) when (asRaise (typeOf body) rhs).IsSome -> cleanup (asRaise (typeOf body) rhs).Value
    | ETry(b, v, h, t) -> ETry(cleanup b, v, cleanup h, t)
    | ELet(v, rhs, body) ->
        let body' = cleanup body

        // A slice does not own the array or string backing it: hoist bindings from the slice's
        // initializer out to the enclosing scope so the owner outlives the slice.
        match v.Ty, cleanup rhs with
        | TSlice _, ELet(innerV, innerRhs, innerBody) -> cleanup (ELet(innerV, innerRhs, ELet(v, innerBody, body')))
        | TSlice _, ESeq(first, rest) -> cleanup (ESeq(first, ELet(v, rest, body')))
        | _, rhs' ->
            if
                isPure rhs'
                && not ((fv body').Contains v.Id)
                && not (isManaged v.Ty)
                && v.Kind <> VUse
            then
                body'
            else
                ELet(v, rhs', body')
    | ESeq(a, b) ->
        match cleanup a with
        | EUnit -> cleanup b
        | a' -> ESeq(a', cleanup b)
    | EIf(c, t, f, ty) -> EIf(c, cleanup t, cleanup f, ty)
    | EWhile(c, b) -> EWhile(c, cleanup b)
    | EFor(i, a, b, up, body) -> EFor(i, a, b, up, cleanup body)
    | EAssign(v, r) -> EAssign(v, cleanup r)
    | _ -> e

/// A chain of projections that starts at a variable which is never assigned.
let rec isStablePath (e: Expr) =
    match e with
    | EVar v -> not v.FMutable && v.Kind <> VGlobal
    | EGet(x, _, _) -> isStablePath x
    | _ -> false

let projName (e: Expr) =
    match e with
    | EGet(_, PCase(_, f), _)
    | EGet(_, PField f, _) -> f
    | EGet(_, PItem i, _) -> $"item%d{i}"
    | EGet(_, PSome, _) -> "value"
    | _ -> "fld"

let projKey (proj: Proj) =
    match proj with
    | PField f -> "F:" + f
    | PCase(c, f) -> $"C:%s{c}:%s{f}"
    | PItem i -> $"I:%d{i}"
    | PSome -> "S"

/// Fable inlines a binding that is used once, so `match xs with Cons(h, t) -> Cons(h + 1, f t)`
/// arrives as `Cons(xs.Cons.head + 1, f xs.Cons.tail)`: `xs` is read after the call, so it
/// cannot be taken apart before it, and its cell cannot be built in again.
///
/// This pass names every field read of a managed value once, as early as it is certain to
/// happen: at the start of the arm (a branch, a loop body, a function body) that reads it, or
/// right after the variable it starts from is bound. A read moves up past statements but never
/// out of its arm, so it is only ever done where the original program would have done it too;
/// and since the values are immutable, when it is done does not change what it yields.
/// Each level of a path gets its own name (`tail = xs.Cons.tail`, `head = tail.Cons.head`),
/// which is the form Perceus can unpack.
let nameProjections (state: FileState) (body: Expr) : Expr =
    /// a variable that names a path -> the key of that path
    let varKey = Dictionary<int, string>()
    /// a second name for a read that already has one -> the first name
    let sameAs = Dictionary<int, Var>()

    let rec sub (x: Expr) : Expr =
        match x with
        | EVar v ->
            match sameAs.TryGetValue v.Id with
            | true, w -> EVar w
            | _ -> x
        | _ ->
            match flatKids x with
            | [] -> x
            | kids -> withFlatKids x (List.map sub kids)

    let rec rootOf (e: Expr) : Var option =
        match e with
        | EVar v -> Some v
        | EGet(x, _, _) -> rootOf x
        | _ -> None

    /// a stable path that starts at a managed variable
    let isRead (e: Expr) =
        match e with
        | EGet _ when isStablePath e && not (touchesMutable e) ->
            match rootOf e with
            | Some r -> isManaged r.Ty
            | None -> false
        | _ -> false

    let rec keyOf (e: Expr) : string =
        match e with
        | EVar v ->
            match varKey.TryGetValue v.Id with
            | true, k -> k
            | _ -> string<int> v.Id
        | EGet(x, proj, _) -> keyOf x + "/" + projKey proj
        | _ -> fail None "internal: not a path"

    let rootIdOfKey (key: string) =
        int (
            match key.IndexOf '/' with
            | -1 -> key
            | i -> key.Substring(0, i)
        )

    let rec arm (outer: Dictionary<string, Var>) (e: Expr) : Expr =
        let names = Dictionary<string, Var>(outer)
        let atStart = List<Var * Expr>()
        /// a variable bound on the spine of this arm -> the reads that start from it
        let afterRoot = Dictionary<int, List<Var * Expr>>()
        /// bindings of the program that are moved to where their path is first named
        let moved = HashSet<int>()

        let listFor (key: string) =
            match afterRoot.TryGetValue(rootIdOfKey key) with
            | true, l -> l
            | _ -> atStart

        let rec varFor (x: Expr) : Var =
            let key = keyOf x

            match names.TryGetValue key, x with
            | (true, v), _ -> v
            | _, EGet(parent, proj, t) ->
                let parent' =
                    match parent with
                    | EGet _ -> EVar(varFor parent)
                    | _ -> sub parent

                let v = state.NewVar(projName x, t, VLocal, false)
                names[key] <- v
                varKey[v.Id] <- key
                (listFor key).Add((v, EGet(parent', proj, t)))
                v
            | _ -> fail None "internal: not a path"

        let rec rw (x: Expr) : Expr =
            if isRead x then
                EVar(varFor x)
            else
                match x with
                | EVar _ -> sub x
                | _ ->
                    match flatKids x with
                    | [] -> x
                    | kids -> withFlatKids x (List.map rw kids)

        /// a binding of the program that names a read: `let t = xs.Cons.tail`
        let isNamedRead (v: Var) (rhs: Expr) = not v.FMutable && isRead rhs

        // First the reads on the spine get their names (so that the arms below see them),
        // then everything is rewritten.
        let rec scan (e: Expr) =
            match e with
            | ELet(v, rhs, rest) ->
                if isNamedRead v rhs then
                    let key = keyOf rhs

                    if names.ContainsKey key then
                        sameAs[v.Id] <- names[key]
                        varKey[v.Id] <- key
                        moved.Add v.Id |> ignore
                    else
                        match rhs with
                        | EGet(parent, proj, t) ->
                            let parent' =
                                match parent with
                                | EGet _ -> EVar(varFor parent)
                                | _ -> sub parent

                            names[key] <- v
                            varKey[v.Id] <- key
                            moved.Add v.Id |> ignore
                            (listFor key).Add((v, EGet(parent', proj, t)))
                        | _ -> ()
                else
                    if isFlat rhs then
                        rw rhs |> ignore

                    afterRoot[v.Id] <- List()

                scan rest
            | ESeq(a, rest) ->
                if isFlat a then
                    rw a |> ignore

                if isPure a then
                    scan rest
            | EIf(c, _, _, _) -> rw c |> ignore
            | EAssign(_, r) ->
                if isFlat r then
                    rw r |> ignore
            | EWhile _
            | EFor _
            | EStore _ -> ()
            | _ -> rw e |> ignore

        let wrap (binds: List<Var * Expr>) (k: Expr) =
            Seq.foldBack (fun (v, x) acc -> ELet(v, x, acc)) binds k

        let inner (x: Expr) =
            if isFlat x then
                rw x
            else
                arm names x

        let rec rewrite (e: Expr) : Expr =
            match e with
            | ELet(v, _, rest) when moved.Contains v.Id -> rewrite rest
            | ELet(v, rhs, rest) ->
                let rhs' = inner rhs
                let rest' = rewrite rest

                match afterRoot.TryGetValue v.Id with
                | true, binds -> ELet(v, rhs', wrap binds rest')
                | _ -> ELet(v, rhs', rest')
            | ESeq(a, rest) ->
                if isPure a then
                    ESeq(inner a, rewrite rest)
                else
                    ESeq(inner a, arm names rest)
            | EIf(c, t, f, ty) -> EIf(rw c, arm names t, arm names f, ty)
            | EWhile(c, b) -> EWhile(sub c, arm names b)
            | EFor(i, a, b, up, loopBody) -> EFor(i, sub a, sub b, up, arm names loopBody)
            | EAssign(v, r) -> EAssign(v, inner r)
            | EStore(lv, r) -> EStore(sub lv, sub r)
            | ETry(b, v, h, t) -> ETry(arm names b, v, arm names h, t)
            | _ -> rw e

        scan e
        let e' = rewrite e
        wrap atStart e'

    arm (Dictionary()) body

let rec projPathKey (e: Expr) : string option =
    match e with
    | EVar v -> Some(string<int> v.Id)
    | EGet(x, p, _) ->
        projPathKey x
        |> Option.map (fun k ->
            match p with
            | PField f -> $"%s{k}/F:%s{f}"
            | PCase(c, f) -> $"%s{k}/C:%s{c}:%s{f}"
            | PItem i -> $"%s{k}/I:%d{i}"
            | PSome -> k + "/S"
        )
    | _ -> None

/// `let a = e.Neg.inner.Neg.inner` becomes `let inner = e.Neg.inner in let a = inner.Neg.inner`,
/// so that every level is an alias of one field, which Perceus can unpack (nested patterns reuse
/// cells too). A path that already has a name keeps it: `Some(f, rest)` binds `mv.Some.Value[0]`
/// and `mv.Some.Value[1]`, and both must hang off one alias of `mv.Some.Value` (two aliases of
/// one field would block the unpack).
let rec splitPathsIn (state: FileState) (paths: Map<string, Var>) (e: Expr) : Expr =
    let sp = splitPathsIn state paths

    match e with
    | ELet(v, EGet((EGet _ as inner), p, t), body) when isManaged v.Ty && not v.FMutable && isManaged (typeOf inner) ->
        match projPathKey inner |> Option.bind paths.TryFind with
        | Some mid -> sp (ELet(v, EGet(EVar mid, p, t), body))
        | None ->
            let mid = state.NewVar(projName inner, typeOf inner, VLocal, false)
            sp (ELet(mid, inner, ELet(v, EGet(EVar mid, p, t), body)))
    | ELet(v, (EGet _ as r), b) when isManaged v.Ty && not v.FMutable ->
        let paths' =
            match projPathKey r with
            | Some k when not (paths.ContainsKey k) -> paths.Add(k, v)
            | _ -> paths

        ELet(v, r, splitPathsIn state paths' b)
    | ELet(v, r, b) -> ELet(v, sp r, sp b)
    | ESeq(a, b) -> ESeq(sp a, sp b)
    | EIf(c, t, f, ty) -> EIf(c, sp t, sp f, ty)
    | EWhile(c, b) -> EWhile(c, sp b)
    | EFor(i, a, b, up, body) -> EFor(i, a, b, up, sp body)
    | EAssign(v, r) -> EAssign(v, sp r)
    | ETry(b, v, h, t) -> ETry(sp b, v, sp h, t)
    | _ -> e

// =============================================================================================
// Exceptions: which functions can raise. A function that cannot keeps its plain result type
// and pays nothing.
// =============================================================================================

let joinRaises (a: Raises) (b: Raises) : Raises =
    match a, b with
    | RAlways, _
    | _, RAlways -> RAlways
    | RNever, x
    | x, RNever -> x
    | RDepends x, RDepends y ->
        let key (name: string, tys: Ty list) =
            name + "<" + (tys |> List.map tyKey |> String.concat ",") + ">"

        let all = (x @ y) |> List.distinctBy key |> List.sortBy key
        // (a long list is not worth a long type: the function is simply taken to raise)
        if all.Length > 16 then
            RAlways
        else
            RDepends all

/// Can this call raise, as far as this file can tell? A function value always can; a cross-file
/// function consults imported `FnFacts.Raises` (verified at Zig compile time via `assertNoRaise`).
let callRaises (p: P) (e: Expr) : Raises =
    match e with
    | ECallClo _
    | ECallVt _
    | ECallIface _
    | ERt _ -> RAlways
    | ECall(f, tyArgs, _, _) ->
        match p.Fns.TryGetValue f with
        | true, g ->
            match g.Raises with
            | RDepends ds when g.TypeParams.Length = tyArgs.Length && not tyArgs.IsEmpty ->
                let m = Map.ofList (List.zip g.TypeParams tyArgs)
                RDepends(ds |> List.map (fun (n, tys) -> n, tys |> List.map (substTy m)))
            | r -> r
        | _ ->
            match p.Ext f with
            | Some ff ->
                match ff.Raises with
                | Facts.PRNever -> RNever
                | Facts.PRAlways -> RAlways
                | Facts.PRDepends _ -> RDepends [ f, tyArgs ]
            | None -> RDepends [ f, tyArgs ]
    | _ -> RNever

let rec raisesOf (p: P) (e: Expr) : Raises =
    let many (es: Expr list) =
        es |> List.map (raisesOf p) |> List.fold joinRaises RNever

    match e with
    | ERaise _ -> RAlways
    // (what the body raises lands in the handler, which raises again what it does not handle;
    // when the body never raises, `ETry` itself raises `RNever` and `elideDeadTry` removes the wrapper)
    | ETry(body, _, h, _) ->
        if raisesOf p body = RNever then
            RNever
        else
            raisesOf p h
    | ECall _
    | ERt _
    | ECallClo _
    | ECallVt _
    | ECallIface _ -> joinRaises (callRaises p e) (many (flatKids e))
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b)
    | EStore(r, b) -> many [ r; b ]
    | EIf(c, t, f, _) -> many [ c; t; f ]
    | EFor(_, a, b, _, body) -> many [ a; b; body ]
    | EAssign(_, r) -> raisesOf p r
    | EDrop(_, k)
    | EUnpack(_, k)
    | EPromote(_, k) -> raisesOf p k
    | _ -> many (flatKids e)

let inferRaises (p: P) : unit =
    let mutable changed = true

    while changed do
        changed <- false

        for fn in p.State.Fns do
            let r = joinRaises fn.Raises (raisesOf p fn.Body)

            if r <> fn.Raises then
                fn.Raises <- r
                changed <- true

/// Remove `try ... with ...` wrappers whose body cannot raise.
let rec elideDeadTry (p: P) (e: Expr) : Expr =
    match e with
    | ETry(body, exV, handler, ty) ->
        let body' = elideDeadTry p body

        if raisesOf p body' = RNever then
            body'
        else
            ETry(body', exV, elideDeadTry p handler, ty)
    | ELet(v, r, b) -> ELet(v, elideDeadTry p r, elideDeadTry p b)
    | ESeq(a, b) -> ESeq(elideDeadTry p a, elideDeadTry p b)
    | EIf(c, t, f, ty) -> EIf(elideDeadTry p c, elideDeadTry p t, elideDeadTry p f, ty)
    | EWhile(c, b) -> EWhile(elideDeadTry p c, elideDeadTry p b)
    | EFor(i, a, b, up, body) -> EFor(i, elideDeadTry p a, elideDeadTry p b, up, elideDeadTry p body)
    | EAssign(v, r) -> EAssign(v, elideDeadTry p r)
    | EStore(lv, r) -> EStore(elideDeadTry p lv, elideDeadTry p r)
    | _ -> e

/// A call that may raise becomes a statement of its own, so that it is exact what the function
/// still owns when it does. What is evaluated before it in the same expression, and may have
/// an effect, is given a name first, to keep the order.
let rec hoistRaising (p: P) (e: Expr) : Expr =
    let hr = hoistRaising p
    let raising (x: Expr) = callRaises p x <> RNever
    let hasRaising (x: Expr) = exists raising x

    /// the bindings to put before `x`, and what is left of `x`
    let rec lift (keepRoot: bool) (x: Expr) : (Var * Expr) list * Expr =
        if not (hasRaising x) then
            [], x
        else
            let kids = flatKids x

            let last = kids |> List.tryFindIndexBack hasRaising |> Option.defaultValue -1

            let binds = List<Var * Expr>()

            let kids' =
                kids
                |> List.mapi (fun i k ->
                    if i > last then
                        k
                    else
                        let inner, k' = lift false k
                        binds.AddRange inner

                        if isPure k' then
                            k'
                        else
                            let v = p.State.NewVar(tempName k', typeOf k', VLocal, false)
                            binds.Add((v, k'))
                            EVar v
                )

            let x' = withFlatKids x kids'

            if raising x' && not keepRoot then
                let v = p.State.NewVar(tempName x', typeOf x', VLocal, false)
                binds.Add((v, x'))
                List.ofSeq binds, EVar v
            else
                List.ofSeq binds, x'

    let wrap (binds: (Var * Expr) list) (k: Expr) =
        List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) binds k

    match e with
    | ELet(v, rhs, body) when isFlat rhs ->
        let binds, rhs' = lift true rhs
        wrap binds (ELet(v, rhs', hr body))
    | ELet(v, rhs, body) -> ELet(v, hr rhs, hr body)
    | ESeq(a, b) when isFlat a ->
        let binds, a' = lift true a
        wrap binds (ESeq(a', hr b))
    | ESeq(a, b) -> ESeq(hr a, hr b)
    | EIf(c, t, f, ty) ->
        let binds, c' = lift false c
        wrap binds (EIf(c', hr t, hr f, ty))
    | EWhile(c, b) when hasRaising c ->
        // (a condition that can raise is tested inside the loop, where it can leave the function)
        let go = p.State.NewVar("go", tBool, VLocal, true)
        let stop = EAssign(go, ELit("false", tBool))
        hr (ELet(go, ELit("true", tBool), EWhile(EVar go, EIf(c, b, stop, tVoid))))
    | EWhile(c, b) -> EWhile(c, hr b)
    | EFor(i, a, b, up, body) ->
        let bindsA, a' = lift false a
        let bindsB, b' = lift false b
        wrap (bindsA @ bindsB) (EFor(i, a', b', up, hr body))
    | EAssign(v, r) when isFlat r ->
        let binds, r' = lift true r
        wrap binds (EAssign(v, r'))
    | EAssign(v, r) -> EAssign(v, hr r)
    | EStore(lv, r) ->
        let binds, r' = lift false r
        wrap binds (EStore(lv, r'))
    | ERaise(x, t) ->
        let binds, x' = lift false x
        wrap binds (ERaise(x', t))
    | ETry(b, v, h, t) -> ETry(hr b, v, hr h, t)
    | _ ->
        let binds, e' = lift true e
        wrap binds e'

/// A read of an assignable field that holds a counted value, of a value that may be shared
/// between threads (a reference record, an object): it is read with its own reference
/// (`loadIn`, `objLoad`; Koka's protocol), so it is never left as a borrow.
let isSharedFieldRead (e: Expr) =
    match e with
    | EGet(owner, PField f, t) when isManaged t ->
        match typeOf owner with
        | TEnt({ Kind = KRefRecord } as ent, _) -> List.contains f ent.MutableFields
        | TPtr(TEnt(ent, _), _) ->
            List.contains f ent.MutableFields
            && (
                match owner with
                | EEmit(m, [ _ ], _) -> m.StartsWith("fable_rt.objPart(", System.StringComparison.Ordinal)
                | _ -> false
            )
        | _ -> false
    | _ -> false

/// Every such read (see `isSharedFieldRead`) is given a name first, in the order of evaluation,
/// so that it holds its own reference while it is in use.
let rec hoistMutableReads (p: P) (e: Expr) : Expr =
    let hr = hoistMutableReads p
    let raising (x: Expr) = isSharedFieldRead x
    let hasRaising (x: Expr) = exists raising x

    /// the bindings to put before `x`, and what is left of `x`
    let rec lift (keepRoot: bool) (x: Expr) : (Var * Expr) list * Expr =
        if not (hasRaising x) then
            [], x
        else
            let kids = flatKids x

            let last = kids |> List.tryFindIndexBack hasRaising |> Option.defaultValue -1

            let binds = List<Var * Expr>()

            let kids' =
                kids
                |> List.mapi (fun i k ->
                    if i > last then
                        k
                    else
                        let inner, k' = lift false k
                        binds.AddRange inner

                        if isPure k' then
                            k'
                        else
                            let v = p.State.NewVar(tempName k', typeOf k', VLocal, false)
                            binds.Add((v, k'))
                            EVar v
                )

            let x' = withFlatKids x kids'

            if raising x' && not keepRoot then
                let v = p.State.NewVar(tempName x', typeOf x', VLocal, false)
                binds.Add((v, x'))
                List.ofSeq binds, EVar v
            else
                List.ofSeq binds, x'

    let wrap (binds: (Var * Expr) list) (k: Expr) =
        List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) binds k

    match e with
    | ELet(v, rhs, body) when isFlat rhs ->
        let binds, rhs' = lift true rhs
        wrap binds (ELet(v, rhs', hr body))
    | ELet(v, rhs, body) -> ELet(v, hr rhs, hr body)
    | ESeq(a, b) when isFlat a ->
        let binds, a' = lift true a
        wrap binds (ESeq(a', hr b))
    | ESeq(a, b) -> ESeq(hr a, hr b)
    | EIf(c, t, f, ty) ->
        let binds, c' = lift false c
        wrap binds (EIf(c', hr t, hr f, ty))
    | EWhile(c, b) -> EWhile(c, hr b)
    | EFor(i, a, b, up, body) ->
        let bindsA, a' = lift false a
        let bindsB, b' = lift false b
        wrap (bindsA @ bindsB) (EFor(i, a', b', up, hr body))
    | EAssign(v, r) when isFlat r ->
        let binds, r' = lift true r
        wrap binds (EAssign(v, r'))
    | EAssign(v, r) -> EAssign(v, hr r)
    | EStore(lv, r) ->
        let binds, r' = lift true r
        wrap binds (EStore(lv, r'))
    | ERaise(x, t) ->
        let binds, x' = lift false x
        wrap binds (ERaise(x', t))
    | ETry(b, v, h, t) -> ETry(hr b, v, hr h, t)
    | _ ->
        let binds, e' = lift true e
        wrap binds e'

// =============================================================================================
// Reference records: field-sensitive store tracking so a read of field A stays borrowed while
// only field B or a pure stdlib function runs, and local unescaped ref cells borrow freely.
// =============================================================================================

let fieldKey (ent: Ent) (f: string) = $"%s{ent.Ref.FullName}|%s{f}"

let rec mayCarryCallable (t: Ty) : bool =
    match t with
    | TFn _
    | TGen _
    | TPrim "fable_rt.Obj" -> true
    | TEnt(e, args) -> e.Kind = KIface || e.ReachesOpaque || List.exists mayCarryCallable args
    | TOpt x -> mayCarryCallable x
    | TTuple ts -> List.exists mayCarryCallable ts
    | _ -> false

let rec mentionsRefCell (t: Ty) : bool =
    match t with
    | TGen _
    | TPrim "fable_rt.Obj" -> true
    | TEnt(e, args) ->
        e.Ref.FullName = "Microsoft.FSharp.Core.FSharpRef`1"
        || List.exists mentionsRefCell args
    | TOpt x -> mentionsRefCell x
    | TTuple ts -> List.exists mentionsRefCell ts
    | _ -> false

let isPureStdlibCall (p: P) (fname: string) (xs: Expr list) =
    match fname.IndexOf '.' with
    | -1 -> false
    | dot ->
        let alias = fname.Substring(0, dot)

        p.PureStdlibAliases.Contains alias
        && not (xs |> List.exists (typeOf >> mentionsRefCell))

let rec scanFnStores
    (p: P)
    (stored: HashSet<string>)
    (extDeps: HashSet<string>)
    (callsCallback: bool ref)
    (callsExtStore: bool ref)
    (e: Expr)
    : unit
    =
    let go x =
        scanFnStores p stored extDeps callsCallback callsExtStore x

    match e with
    | EStore(lv, r) ->
        (match lv with
         | EGet(EEmit(m, _, _), _, _) when m.StartsWith("objInit:", System.StringComparison.Ordinal) -> ()
         | EGet(x, PField f, _) ->
             match typeOf x with
             | TEnt({ Kind = KRefRecord } as ent, _)
             | TPtr(TEnt(ent, _), _) -> stored.Add(fieldKey ent f) |> ignore
             | _ ->
                 match x with
                 | EDeref _ ->
                     match typeOf x with
                     | TEnt(ent, _) when List.contains f ent.MutableFields -> stored.Add(fieldKey ent f) |> ignore
                     | _ -> callsExtStore.Value <- true
                 | _ -> callsExtStore.Value <- true
         | _ -> callsExtStore.Value <- true)

        go lv
        go r
    | ECall(f, _, xs, _) ->
        match p.Fns.TryGetValue f with
        | true, _ ->
            for k in p.StoredFields[f] do
                stored.Add k |> ignore

            for ef in p.ExtStoreDeps[f] do
                extDeps.Add ef |> ignore

            if p.CallsCallback.Contains f then
                callsCallback.Value <- true

            if p.CallsExtStore.Contains f then
                callsExtStore.Value <- true
        | _ ->
            match p.Ext f with
            | Some ff ->
                for k in ff.StoredFields do
                    stored.Add k |> ignore

                if ff.CallsCallback then
                    callsCallback.Value <- true

                if ff.CallsExtStore then
                    callsExtStore.Value <- true

                extDeps.Add f |> ignore
            | None ->
                if xs |> List.exists (typeOf >> mayCarryCallable) then
                    callsCallback.Value <- true
                elif not (isPureStdlibCall p f xs) then
                    callsExtStore.Value <- true

        List.iter go xs
    | ECallClo _
    | ECallVt _
    | ECallIface _ ->
        callsCallback.Value <- true
        List.iter go (flatKids e)
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b) ->
        go r
        go b
    | EIf(c, t, f, _) ->
        go c
        go t
        go f
    | EFor(_, a, b, _, body) ->
        go a
        go b
        go body
    | EAssign(_, r) -> go r
    | ETry(b, _, h, _) ->
        go b
        go h
    | EDrop(_, k)
    | EUnpack(_, k)
    | EPromote(_, k) -> go k
    | _ -> List.iter go (flatKids e)

let inferStores (p: P) : unit =
    for fn in p.State.Fns do
        p.StoredFields[fn.Name] <- Set.empty
        p.ExtStoreDeps[fn.Name] <- Set.empty

    let mutable changed = true

    while changed do
        changed <- false

        for fn in p.State.Fns do
            let stored = HashSet<string>(p.StoredFields[fn.Name])
            let extDeps = HashSet<string>(p.ExtStoreDeps[fn.Name])
            let callsCb = ref (p.CallsCallback.Contains fn.Name)
            let callsExt = ref (p.CallsExtStore.Contains fn.Name)
            scanFnStores p stored extDeps callsCb callsExt fn.Body
            let storedSet = Set.ofSeq stored
            let extDepSet = Set.ofSeq extDeps

            if storedSet <> p.StoredFields[fn.Name] then
                p.StoredFields[fn.Name] <- storedSet
                changed <- true

            if extDepSet <> p.ExtStoreDeps[fn.Name] then
                p.ExtStoreDeps[fn.Name] <- extDepSet
                changed <- true

            if callsCb.Value && p.CallsCallback.Add fn.Name then
                changed <- true

            if callsExt.Value && p.CallsExtStore.Add fn.Name then
                changed <- true

            fn.Stores <- not storedSet.IsEmpty || callsCb.Value || callsExt.Value

let localUnescapedRefVars (body: Expr) : Set<int> =
    let candidates = HashSet<int>()
    let escaped = HashSet<int>()

    let rec collect (e: Expr) =
        match e with
        | ELet(v, ECon(TEnt({ Kind = KRefRecord }, _), "", args, _), b) when not v.FMutable && v.Kind = VLocal ->
            candidates.Add v.Id |> ignore
            List.iter collect args
            collect b
        | ELet(_, r, b)
        | ESeq(r, b)
        | EWhile(r, b)
        | EStore(r, b) ->
            collect r
            collect b
        | EIf(c, t, f, _) ->
            collect c
            collect t
            collect f
        | EFor(_, a, b, _, bd) ->
            collect a
            collect b
            collect bd
        | EAssign(_, r) -> collect r
        | ETry(b, _, h, _) ->
            collect b
            collect h
        | EDrop(_, k)
        | EUnpack(_, k)
        | EPromote(_, k) -> collect k
        | _ -> List.iter collect (flatKids e)

    collect body

    let rec markAll (e: Expr) =
        match e with
        | EVar v -> escaped.Add v.Id |> ignore
        | _ -> List.iter markAll (flatKids e)

    let rec scan (e: Expr) =
        match e with
        | EVar v -> escaped.Add v.Id |> ignore
        | EAddr(x, _) -> markAll x
        | EGet(EVar v, PField _, _) when candidates.Contains v.Id -> ()
        | EStore(EGet(EVar v, PField _, _), rhs) when candidates.Contains v.Id -> scan rhs
        | ELet(_, r, b) ->
            scan r
            scan b
        | ESeq(r, b)
        | EWhile(r, b) ->
            scan r
            scan b
        | EIf(c, t, f, _) ->
            scan c
            scan t
            scan f
        | EFor(_, a, b, _, bd) ->
            scan a
            scan b
            scan bd
        | EAssign(_, r) -> scan r
        | EStore(lv, r) ->
            scan lv
            scan r
        | ETry(b, _, h, _) ->
            scan b
            scan h
        | EDrop(_, k)
        | EUnpack(_, k)
        | EPromote(_, k) -> scan k
        | _ -> List.iter scan (flatKids e)

    if candidates.Count > 0 then
        scan body

    candidates |> Seq.filter (fun id -> not (escaped.Contains id)) |> Set.ofSeq

let rec mayOverwriteRead
    (p: P)
    (storeAsserts: List<string * Set<string> * bool>)
    (unescaped: Set<int>)
    (rhs: Expr)
    (body: Expr)
    : bool
    =
    let rec mutableFieldsRead e =
        match e with
        | EGet(x, proj, _) ->
            let here =
                match proj, typeOf x with
                | PField f, TEnt({ Kind = KRefRecord } as ent, _) when List.contains f ent.MutableFields -> [ ent, f ]
                | PField f, TPtr(TEnt(ent, _), _) when List.contains f ent.MutableFields -> [ ent, f ]
                | PField f, TEnt(ent, _) when
                    (match x with
                     | EDeref _ -> true
                     | _ -> false)
                    && List.contains f ent.MutableFields
                    ->
                    [ ent, f ]
                | _ -> []

            here @ mutableFieldsRead x
        | EDeref(x, _) -> mutableFieldsRead x
        | _ -> []

    let fields = mutableFieldsRead rhs

    if fields.IsEmpty then
        false
    else
        match rhs with
        | EGet(EVar owner, PField fieldName, _) when unescaped.Contains owner.Id ->
            exists
                (function
                | EStore(EGet(EVar v2, PField f2, _), _) -> v2.Id = owner.Id && f2 = fieldName
                | _ -> false)
                body
        | _ ->
            let fieldKeys = fields |> List.map (fun (ent, f) -> fieldKey ent f) |> Set.ofList

            let hasNonLocalOrRef =
                exists
                    (function
                    | EDeref _ -> true
                    | _ -> false)
                    rhs
                || (fields
                    |> List.exists (fun (ent, _) ->
                        not ent.IsLocal || ent.Ref.FullName = "Microsoft.FSharp.Core.FSharpRef`1"
                    ))

            let pending = List<string * Set<string> * bool>()

            let rec hits (e: Expr) : bool =
                match e with
                | EStore(lv, r) ->
                    let hitLv =
                        match lv with
                        | EGet(EEmit(m, _, _), _, _) when m.StartsWith("objInit:", System.StringComparison.Ordinal) ->
                            false
                        | EGet(y, PField f2, _) ->
                            match typeOf y with
                            | TEnt({ Kind = KRefRecord } as e2, _)
                            | TPtr(TEnt(e2, _), _) -> fieldKeys.Contains(fieldKey e2 f2)
                            | TEnt(e2, _) when
                                (match y with
                                 | EDeref _ -> true
                                 | _ -> false)
                                && List.contains f2 e2.MutableFields
                                ->
                                fieldKeys.Contains(fieldKey e2 f2)
                            | _ -> true
                        | _ -> true

                    hitLv || hits r
                | ECallClo _
                | ECallVt _
                | ECallIface _ -> true
                | ECall(g, _, xs, _) ->
                    let calleeHit =
                        match p.Fns.TryGetValue g with
                        | true, _ ->
                            let h =
                                not (Set.isEmpty (Set.intersect fieldKeys p.StoredFields[g]))
                                || p.CallsCallback.Contains g
                                || (hasNonLocalOrRef && p.CallsExtStore.Contains g)

                            if not h then
                                for ef in p.ExtStoreDeps[g] do
                                    pending.Add(ef, fieldKeys, hasNonLocalOrRef)

                            h
                        | _ ->
                            match p.Ext g with
                            | Some ff ->
                                let h =
                                    not (Set.isEmpty (Set.intersect fieldKeys (Set.ofList ff.StoredFields)))
                                    || ff.CallsCallback
                                    || (hasNonLocalOrRef && ff.CallsExtStore)

                                if not h then
                                    pending.Add(g, fieldKeys, hasNonLocalOrRef)

                                h
                            | None ->
                                (xs |> List.exists (typeOf >> mayCarryCallable))
                                || (hasNonLocalOrRef && not (isPureStdlibCall p g xs))

                    calleeHit || List.exists hits xs
                | ELet(_, r, b)
                | ESeq(r, b)
                | EWhile(r, b) -> hits r || hits b
                | EIf(c, t, f, _) -> hits c || hits t || hits f
                | EFor(_, a, b, _, bd) -> hits a || hits b || hits bd
                | EAssign(_, r) -> hits r
                | ETry(b, _, h, _) -> hits b || hits h
                | EDrop(_, k)
                | EUnpack(_, k)
                | EPromote(_, k) -> hits k
                | _ -> List.exists hits (flatKids e)

            let res = hits body

            if not res && pending.Count > 0 then
                storeAsserts.AddRange pending

            res

// =============================================================================================
// Borrow inference: a managed parameter is borrowed unless the body consumes it (returns it,
// stores it, passes it to an owning parameter) or matches on it while building the same type
// (a reuse site).
// =============================================================================================

/// The modes of the parameters that `args` are passed to. Consults cross-file facts when
/// available; otherwise falls back to owned for managed values (`fable_rt.across` reconciles).
let modesOf (p: P) (fname: string) (args: Expr list) : Mode list =
    match p.Fns.TryGetValue fname with
    | true, f when f.Modes.Length = args.Length -> f.Modes
    | true, _ -> fail None "internal: `%s` is called with %d arguments" fname args.Length
    | _ ->
        match p.Ext fname with
        | Some ff when ff.Modes.Length = args.Length -> ff.Modes
        | _ ->
            args
            |> List.map (fun a ->
                if isManaged (typeOf a) then
                    MOwned
                else
                    MPlain
            )

let isBorrowedRet (p: P) (fname: string) =
    match p.Fns.TryGetValue fname with
    | true, f -> f.RetFrom.IsSome
    | _ -> false

/// Cross-file borrowed-return parameter indices for the let-bound owner case (`acrossAssumed`).
/// Never used in `borrowSources`/`tailSources` (non-owner calls keep `across` dup'ing the result).
let extBorrowedRet (p: P) (fname: string) (args: Expr list) : int list option =
    if p.Fns.ContainsKey fname then
        None
    else
        match p.Ext fname with
        | Some ff ->
            match ff.RetFrom with
            | Some js when
                js
                |> List.forall (fun i -> i >= 0 && i < ff.Modes.Length && i < args.Length && ff.Modes[i] = MBorrowed)
                ->
                Some js
            | _ -> None
        | None -> None

/// Could a value of `t` be or embed a move-only resource at runtime (e.g. an unboxed
/// struct/value-union with a type parameter that may be instantiated with `IResource`)?
let rec mayBeMoveOnly (t: Ty) =
    not (isCopyable t)
    || (
        match t with
        | TGen _ -> true
        | TOpt inner -> mayBeMoveOnly inner
        | TTuple ts -> List.exists mayBeMoveOnly ts
        | TEnt(e, args) when e.Kind = KRecord || e.Kind = KValueUnion -> List.exists mayBeMoveOnly args
        | _ -> false
    )

/// Variables used in owning positions.
let rec owningUses (p: P) (tail: bool) (e: Expr) : Set<int> =
    let flat (owning: bool) (e: Expr) =
        let acc = HashSet<int>()

        let rec go owning e =
            match e with
            | EVar v ->
                if owning then
                    acc.Add v.Id |> ignore
            | ECall(f, _, xs, _) ->
                let hasExtModes =
                    match p.Ext f with
                    | Some ff -> ff.Modes.Length = xs.Length
                    | None -> false

                if p.Fns.ContainsKey f || hasExtModes then
                    List.iter2
                        (fun m x ->
                            let own =
                                match x with
                                | EKnown _
                                | EKnownIface _ -> false
                                | _ -> m = MOwned

                            go own x
                        )
                        (modesOf p f xs)
                        xs
                else
                    xs |> List.iter (fun x -> go (mayBeMoveOnly (typeOf x)) x)
            | ECallClo(f, xs, _) ->
                go false f
                List.iter (go true) xs
            | ECallVt(f, s, xs, _) ->
                go false f
                go false s
                List.iter (go true) xs
            | ECallIface(r, _, xs, _) ->
                go false r
                List.iter (go true) xs
            | EIface _ -> List.iter (go true) (flatKids e)
            | EClosure(_, _, xs, _)
            | EExnNew(_, xs)
            | ECon(_, _, xs, _) -> List.iter (go true) xs
            | EEmit(m, x :: rest, _)
            | ERt(m, x :: rest, _) when ownsFirst m ->
                go true x
                List.iter (go false) rest
            | _ -> List.iter (go false) (flatKids e)

        go owning e
        Set.ofSeq acc

    match e with
    | ELet(v, r, b) ->
        let binds =
            v.FMutable
            || not (
                match r with
                | EGet _ -> true
                | _ -> false
            )

        Set.union (owningUses p binds r) (owningUses p tail b)
    | ESeq(a, b) -> Set.union (owningUses p false a) (owningUses p tail b)
    | EIf(c, t, f, _) -> Set.unionMany [ flat false c; owningUses p tail t; owningUses p tail f ]
    | EWhile(c, b) -> Set.union (flat false c) (owningUses p false b)
    | EFor(_, a, b, _, body) -> Set.unionMany [ flat false a; flat false b; owningUses p false body ]
    | EAssign(_, r) -> owningUses p true r
    | EStore(lv, r) -> Set.union (flat false lv) (owningUses p true r)
    | ERaise(x, _) -> flat true x
    | ETry(b, _, h, _) -> Set.union (owningUses p tail b) (owningUses p tail h)
    | _ -> flat tail e

let isReuseSite (body: Expr) (param: Var) =
    match param.Ty with
    | TEnt(ent, _) when ent.Kind = KHeapUnion ->
        exists
            (function
            | ETest(EVar x, _, _) -> x.Id = param.Id
            | _ -> false)
            body
        && exists
            (function
            | ECon(TEnt(e2, _), _, xs, _) -> obj.ReferenceEquals(e2, ent) && not xs.IsEmpty
            | _ -> false)
            body
    | _ -> false

/// The parameter indices a value borrows from, or None when it is fresh or owned.
let rec borrowSources (p: P) (fn: FnInfo) (aliases: Map<int, Set<int>>) (e: Expr) : Set<int> option =
    let union (acc: Set<int> option) (x: Set<int> option) =
        match acc, x with
        | Some a, Some b -> Some(Set.union a b)
        | _ -> None

    match e with
    | EVar v ->
        match fn.Params |> List.tryFindIndex (fun q -> q.Id = v.Id) with
        | Some i -> Some(Set.singleton i)
        | None -> aliases.TryFind v.Id
    // (what was read from a field that can be assigned is never returned as a borrow)
    | EGet _ when touchesMutable e -> None
    | EGet(x, _, _) -> borrowSources p fn aliases x
    | ECon(_, _, [], _) -> Some Set.empty // a constructor without fields owns nothing
    | ECall(g, _, args, _) ->
        match p.Fns.TryGetValue g with
        // (a call that gives fewer arguments than the function takes: not known, so owned)
        | true, gi when gi.RetFrom.IsSome && gi.RetFrom.Value |> List.forall (fun i -> i < args.Length) ->
            gi.RetFrom.Value
            |> List.fold (fun acc i -> union acc (borrowSources p fn aliases args[i])) (Some Set.empty)
        | _ -> None
    | _ -> None

/// The sources of every value the function can return (None if one of them is fresh or owned).
let rec tailSources (p: P) (fn: FnInfo) (aliases: Map<int, Set<int>>) (e: Expr) : Set<int> option =
    match e with
    | ELet(v, r, b) ->
        let aliases =
            if isFlat r && not v.FMutable then
                match borrowSources p fn aliases r with
                | Some s -> aliases.Add(v.Id, s)
                | None -> aliases
            else
                aliases

        tailSources p fn aliases b
    | ESeq(_, b) -> tailSources p fn aliases b
    | EIf(_, t, f, _) ->
        match tailSources p fn aliases t, tailSources p fn aliases f with
        | Some a, Some b -> Some(Set.union a b)
        | _ -> None
    | _ when isFlat e -> borrowSources p fn aliases e
    | _ -> None

/// The functions of the file that call each other last (strongly connected components of two
/// or more over calls in tail position). As Koka's borrow inference does, their parameters are
/// owned: a borrowed argument would leave the caller a drop after the call, and the call would
/// no longer be the last thing it does (see the state machines of `Emit`).
let mutualTailFns (fns: FnInfo seq) : HashSet<string> =
    let byName = Dictionary<string, FnInfo>()

    for fn in fns do
        byName[fn.Name] <- fn

    let edges = Dictionary<string, string list>()

    for fn in fns do
        let rec collect (e: Expr) : string list =
            match e with
            | ELet(r, (ECall(g, tArgs, args, _) | EOnRaise(ECall(g, tArgs, args, _), _)), ECon(conTy, _, conArgs, _)) when
                g <> fn.Name
                && byName.ContainsKey g
                && tArgs = (fn.TypeParams |> List.map TGen)
                && args.Length = byName[g].Params.Length
                && isHeapTy conTy
                && not conArgs.IsEmpty
                && (let hits =
                        conArgs
                        |> List.indexed
                        |> List.filter (fun (_, a) ->
                            match a with
                            | EVar v -> v.Id = r.Id
                            | _ -> false
                        )

                    match hits with
                    | [ (i, _) ] ->
                        conArgs
                        |> List.indexed
                        |> List.forall (fun (j, a) -> j = i || not (Set.contains r.Id (fv a)))
                    | _ -> false)
                ->
                [ g ]
            | ELet(_, _, b)
            | EDrop(_, b)
            | EUnpack(_, b)
            | EPromote(_, b) -> collect b
            | ESeq(_, b) -> collect b
            | EIf(_, t, f, _) -> collect t @ collect f
            | ECall(g, tArgs, args, _)
            | EOnRaise(ECall(g, tArgs, args, _), _) when
                g <> fn.Name
                && byName.ContainsKey g
                && tArgs = (fn.TypeParams |> List.map TGen)
                && args.Length = byName[g].Params.Length
                ->
                [ g ]
            | _ -> []

        edges[fn.Name] <- collect fn.Body |> List.distinct

    let result = HashSet<string>()
    let index = Dictionary<string, int>()
    let low = Dictionary<string, int>()
    let onStack = HashSet<string>()
    let stack = Stack<string>()
    let mutable next = 0

    let rec connect (v: string) =
        index[v] <- next
        low[v] <- next
        next <- next + 1
        stack.Push v
        onStack.Add v |> ignore

        for w in edges[v] do
            if not (index.ContainsKey w) then
                connect w
                low[v] <- min low[v] low[w]
            elif onStack.Contains w then
                low[v] <- min low[v] index[w]

        if low[v] = index[v] then
            let comp = List<string>()
            let mutable stop = false

            while not stop do
                let w = stack.Pop()
                onStack.Remove w |> ignore
                comp.Add w
                stop <- (w = v)

            if comp.Count >= 2 then
                for w in comp do
                    result.Add w |> ignore

    for fn in fns do
        if not (index.ContainsKey fn.Name) then
            connect fn.Name

    result

let inferBorrows (p: P) : unit =
    let fns = p.State.Fns
    let mutualTail = mutualTailFns fns

    for fn in fns do
        fn.Modes <-
            fn.Params
            |> List.map (fun q ->
                if isManaged q.Ty then
                    MBorrowed
                else
                    MPlain
            )
        // optimistic start: a function that returns a managed value might return a borrow
        fn.RetFrom <-
            if isManaged fn.Ret then
                Some(
                    fn.Params
                    |> List.indexed
                    |> List.filter (fun (_, q) -> isManaged q.Ty)
                    |> List.map fst
                )
            else
                None

    let mutable changed = true

    while changed do
        changed <- false

        for fn in fns do
            let paramModes (tailOwning: bool) =
                let owning = owningUses p tailOwning fn.Body

                fn.Params
                |> List.map (fun q ->
                    if not (isManaged q.Ty) then
                        MPlain
                    elif owning.Contains q.Id || isReuseSite fn.Body q || mutualTail.Contains fn.Name then
                        MOwned
                    else
                        MBorrowed
                )
            // The result may be a borrow of the parameters iff every value the function returns
            // is a parameter, a projection of one, a call with a borrowed result on them, or a
            // constructor without fields, and those parameters do not have to be owned for
            // another reason.
            let retFrom =
                match fn.RetFrom with
                | None -> None
                | Some _ ->
                    match tailSources p fn Map.empty fn.Body with
                    | Some srcs ->
                        let modes = paramModes false

                        if srcs |> Set.forall (fun i -> modes[i] = MBorrowed) then
                            Some(Set.toList srcs)
                        else
                            None
                    | None -> None

            let modes = paramModes retFrom.IsNone

            if modes <> fn.Modes || retFrom <> fn.RetFrom then
                fn.Modes <- modes
                fn.RetFrom <- retFrom
                changed <- true
