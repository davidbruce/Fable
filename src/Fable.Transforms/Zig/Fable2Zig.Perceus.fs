/// The ownership passes on the IR: borrow inference for parameters and results, then Perceus
/// (dup/drop insertion, drop-unpack and reuse of dead cells).
module Fable.Transforms.Zig.Perceus

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Facts

type private P =
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
let private ownsFirst (macro: string) =
    macro.StartsWith("fable_rt.strAppend(", System.StringComparison.Ordinal)
    || macro.StartsWith("fable_rt.arrayBufPush(", System.StringComparison.Ordinal)

let rec private asRaise (ty: Ty) (e: Expr) : Expr option =
    match e with
    | ERaise(x, _) -> Some(ERaise(x, ty))
    | ELet(v, r, b) -> asRaise ty b |> Option.map (fun b' -> ELet(v, r, b'))
    | ESeq(a, b) -> asRaise ty b |> Option.map (fun b' -> ESeq(a, b'))
    | EIf(c, t, f, _) ->
        match asRaise ty t, asRaise ty f with
        | Some t', Some f' -> Some(EIf(c, t', f', ty))
        | _ -> None
    | _ -> None

let rec private cleanup (e: Expr) : Expr =
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
let rec private isStablePath (e: Expr) =
    match e with
    | EVar v -> not v.FMutable && v.Kind <> VGlobal
    | EGet(x, _, _) -> isStablePath x
    | _ -> false

let private projName (e: Expr) =
    match e with
    | EGet(_, PCase(_, f), _)
    | EGet(_, PField f, _) -> f
    | EGet(_, PItem i, _) -> $"item%d{i}"
    | EGet(_, PSome, _) -> "value"
    | _ -> "fld"

let private projKey (proj: Proj) =
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
let private nameProjections (state: FileState) (body: Expr) : Expr =
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

let rec private projPathKey (e: Expr) : string option =
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
let rec private splitPathsIn (state: FileState) (paths: Map<string, Var>) (e: Expr) : Expr =
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

let private joinRaises (a: Raises) (b: Raises) : Raises =
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
let private callRaises (p: P) (e: Expr) : Raises =
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

let rec private raisesOf (p: P) (e: Expr) : Raises =
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

let private inferRaises (p: P) : unit =
    let mutable changed = true

    while changed do
        changed <- false

        for fn in p.State.Fns do
            let r = joinRaises fn.Raises (raisesOf p fn.Body)

            if r <> fn.Raises then
                fn.Raises <- r
                changed <- true

/// Remove `try ... with ...` wrappers whose body cannot raise.
let rec private elideDeadTry (p: P) (e: Expr) : Expr =
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
let rec private hoistRaising (p: P) (e: Expr) : Expr =
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
let private isSharedFieldRead (e: Expr) =
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
let rec private hoistMutableReads (p: P) (e: Expr) : Expr =
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

let private fieldKey (ent: Ent) (f: string) = $"%s{ent.Ref.FullName}|%s{f}"

let rec private mayCarryCallable (t: Ty) : bool =
    match t with
    | TFn _
    | TGen _
    | TPrim "fable_rt.Obj" -> true
    | TEnt(e, args) -> e.Kind = KIface || e.ReachesOpaque || List.exists mayCarryCallable args
    | TOpt x -> mayCarryCallable x
    | TTuple ts -> List.exists mayCarryCallable ts
    | _ -> false

let rec private mentionsRefCell (t: Ty) : bool =
    match t with
    | TGen _
    | TPrim "fable_rt.Obj" -> true
    | TEnt(e, args) ->
        e.Ref.FullName = "Microsoft.FSharp.Core.FSharpRef`1"
        || List.exists mentionsRefCell args
    | TOpt x -> mentionsRefCell x
    | TTuple ts -> List.exists mentionsRefCell ts
    | _ -> false

let private isPureStdlibCall (p: P) (fname: string) (xs: Expr list) =
    match fname.IndexOf '.' with
    | -1 -> false
    | dot ->
        let alias = fname.Substring(0, dot)

        p.PureStdlibAliases.Contains alias
        && not (xs |> List.exists (typeOf >> mentionsRefCell))

let rec private scanFnStores
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

let private inferStores (p: P) : unit =
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

let private localUnescapedRefVars (body: Expr) : Set<int> =
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

let rec private mayOverwriteRead
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
let private modesOf (p: P) (fname: string) (args: Expr list) : Mode list =
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

let private isBorrowedRet (p: P) (fname: string) =
    match p.Fns.TryGetValue fname with
    | true, f -> f.RetFrom.IsSome
    | _ -> false

/// Cross-file borrowed-return parameter indices for the let-bound owner case (`acrossAssumed`).
/// Never used in `borrowSources`/`tailSources` (non-owner calls keep `across` dup'ing the result).
let private extBorrowedRet (p: P) (fname: string) (args: Expr list) : int list option =
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
let rec private mayBeMoveOnly (t: Ty) =
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
let rec private owningUses (p: P) (tail: bool) (e: Expr) : Set<int> =
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
                                | EKnown _ -> false
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
            | EEmit(m, x :: rest, _) when ownsFirst m ->
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

let private isReuseSite (body: Expr) (param: Var) =
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
let rec private borrowSources (p: P) (fn: FnInfo) (aliases: Map<int, Set<int>>) (e: Expr) : Set<int> option =
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
let rec private tailSources (p: P) (fn: FnInfo) (aliases: Map<int, Set<int>>) (e: Expr) : Set<int> option =
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
let private mutualTailFns (fns: FnInfo seq) : HashSet<string> =
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

let private inferBorrows (p: P) : unit =
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

// =============================================================================================
// Perceus
// =============================================================================================

type private PEnv =
    {
        /// managed variables this scope must consume exactly once
        Owned: Set<int>
        /// borrowed variable -> the variables it borrows from
        Owners: Map<int, int list>
        /// alias of a field -> (parent, case, field)
        Children: Map<int, int * string * string>
        /// access path ("v12", "v12.Neg.inner") -> the case it is known to be
        Known: Map<string, string>
        Excluded: Map<string, Set<string>>
        /// reuse tokens that are available: (token, cell shape)
        Tokens: (Var * (Ty * string)) list
        /// the function returns a borrow, so tail values are not made owned
        TailBorrowed: bool
        /// inside a `try` body: what the handler (or the code after the `try`) still needs, and
        /// an error edge must therefore leave alone
        RaiseKeep: Set<int>
        /// local KRefRecord (`ref` / mutable record) variables whose handle never escapes this function
        UnescapedRefs: Set<int>
        /// parameter IDs treated as `anytype` in a `callK` clone (non-escaping function parameters)
        KParams: Set<int>
        /// cross-file store assertions accumulated when mutable field reads remain borrowed
        StoreAsserts: List<string * Set<string> * bool>
    }

type private POp =
    | ODrop of Var
    | OUnpack of Unpack
    | OPromote of Var

let private vk (id: int) = $"v%d{id}"

/// The access-path key of a chain of projections that starts at a variable.
let rec private pathKey (e: Expr) : string option =
    match e with
    | EVar v -> Some(vk v.Id)
    | EGet(x, proj, _) ->
        pathKey x
        |> Option.map (fun k ->
            match proj with
            | PField f -> k + "." + f
            | PCase(c, f) -> k + "." + c + "." + f
            | PItem i -> k + "." + string<int> i
            | PSome -> k + ".Some"
        )
    | _ -> None

let rec private live (e: Expr) (after: Set<int>) : Set<int> =
    match e with
    | ELet(v, r, b) -> live r (Set.remove v.Id (live b after))
    | ESeq(a, b) -> live a (live b after)
    | EIf(c, t, f, _) -> Set.unionMany [ fv c; live t after; live f after ]
    | EWhile(c, b) -> loopLive (fun s -> Set.unionMany [ after; fv c; live b s ]) (Set.union after (fv c))
    | EFor(i, a, b, _, body) ->
        let head = loopLive (fun s -> Set.union after (Set.remove i.Id (live body s))) after
        Set.unionMany [ head; fv a; fv b ]
    | EAssign(v, r) -> live r (Set.remove v.Id after)
    | EStore(lv, r) -> Set.union (fv lv) (live r after)
    // (what the handler needs is needed throughout the body: any call in it may raise)
    | ETry(b, v, h, _) ->
        let hl = Set.remove v.Id (live h after)
        Set.union hl (live b (Set.union after hl))
    | EDrop(v, k)
    | EPromote(v, k) -> Set.add v.Id (live k after)
    | EUnpack(u, k) -> Set.add u.Scrut.Id (live k after)
    | _ -> Set.union (fv e) after

and private loopLive (step: Set<int> -> Set<int>) (init: Set<int>) =
    let next = step init

    if next = init then
        init
    else
        loopLive step (Set.union init next)

let private expand (env: PEnv) (s: Set<int>) =
    let rec go acc frontier =
        if Set.isEmpty frontier then
            acc
        else
            let next =
                frontier
                |> Seq.collect (fun id ->
                    match env.Owners.TryFind id with
                    | Some os -> os
                    | None -> []
                )
                |> Set.ofSeq

            let fresh = Set.difference next acc
            go (Set.union acc fresh) fresh

    go s s

let private ownersStar env b =
    Set.remove b (expand env (Set.singleton b))

/// Is there a constructor in `e` (outside loops) that could be built in a dead cell of `shape`?
let rec private hasConOfShape (shape: Ty * string) (e: Expr) =
    match e with
    | EWhile _
    | EFor _ -> false
    | ECon(t, c, xs, _) when isHeapTy t && not xs.IsEmpty && cellsMatch shape (t, c) -> true
    | ELet(_, r, b) -> hasConOfShape shape r || hasConOfShape shape b
    | ESeq(a, b) -> hasConOfShape shape a || hasConOfShape shape b
    | EIf(_, t, f, _) -> hasConOfShape shape t || hasConOfShape shape f
    | EAssign(_, r) -> hasConOfShape shape r
    | _ -> flatKids e |> List.exists (hasConOfShape shape)

let private caseIsNoopDrop (t: Ty) (case: string) =
    let fs = caseFields t case

    if isHeapTy t then
        fs.IsEmpty
    else
        not (fs |> List.exists (snd >> isManaged))

let private tryUnpack (p: P) (env: PEnv) (x: int) (borrowers: Set<int>) (e: Expr) (L: Set<int>) : (PEnv * POp) option =
    let allVars = p.State.Vars
    let xv = allVars[x]

    let case =
        match xv.Ty with
        // (a record by reference (one that contains itself or can be assigned) is a counted cell:
        // unpacked as a union's cell is, when it is not shared)
        | TEnt(ent, _) when ent.Kind = KRecord || ent.Kind = KRefRecord -> Some ""
        | TTuple _ -> Some ""
        | _ -> env.Known.TryFind(vk x)
    // The aliases of x's own fields move out; deeper aliases must hang off one of them (they
    // stay borrowed from the child that is now owned, and may be unpacked in turn).
    let direct =
        borrowers
        |> Set.filter (fun b ->
            match env.Children.TryFind b with
            | Some(parent, _, _) -> parent = x
            | None -> false
        )

    let viaDirect =
        borrowers
        |> Set.forall (fun b -> direct.Contains b || not (Set.isEmpty (Set.intersect (ownersStar env b) direct)))

    let borrowers = direct
    let kids = borrowers |> Set.toList |> List.map (fun b -> b, env.Children.TryFind b)

    match case with
    | Some case when viaDirect && not direct.IsEmpty && Set.isEmpty (Set.intersect borrowers L) ->
        let moved =
            kids
            |> List.map (fun (b, c) ->
                let (_, cs, f) = c.Value
                cs, f, allVars[b]
            )

        let fieldsMoved = moved |> List.map (fun (_, f, _) -> f)

        if
            moved |> List.exists (fun (cs, _, _) -> cs <> case)
            || (List.distinct fieldsMoved).Length <> fieldsMoved.Length
        then
            None
        else
            let fields = caseFields xv.Ty case

            let drops =
                fields
                |> List.filter (fun (f, t) -> isManaged t && not (List.contains f fieldsMoved))

            let heap =
                isHeapTy xv.Ty
                || (
                    match xv.Ty with
                    | TEnt(ent, _) -> ent.Kind = KRefRecord
                    | _ -> false
                )

            let token =
                if heap && hasConOfShape (xv.Ty, case) e then
                    Some(p.State.NewVar("ru_" + xv.Base, TTok(xv.Ty, case), VLocal, false))
                else
                    None

            let env' =
                { env with
                    Owned = Set.union (Set.remove x env.Owned) borrowers
                    Children = borrowers |> Set.fold (fun m b -> Map.remove b m) env.Children
                    Owners = borrowers |> Set.fold (fun m b -> Map.remove b m) env.Owners
                    Tokens =
                        match token with
                        | Some t -> (t, (xv.Ty, case)) :: env.Tokens
                        | None -> env.Tokens
                }

            let op =
                OUnpack
                    {
                        Scrut = xv
                        Case = case
                        Moves = moved |> List.map (fun (_, f, v) -> f, v)
                        Drops = drops
                        Token = token
                        Heap = heap
                    }

            Some(env', op)
    | _ -> None

/// Drop (or unpack) every owned variable that is dead on entry to `e`.
let private settle (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : PEnv * POp list =
    let allVars = p.State.Vars
    let direct = live e L
    let allLive = expand env direct
    let mutable env = env
    let ops = List<POp>()
    let visited = HashSet<int>()
    let mutable progress = true

    let dropUnlessNoop (xv: Var) =
        match env.Known.TryFind(vk xv.Id) with
        | Some c when caseIsNoopDrop xv.Ty c -> ()
        | _ -> ops.Add(ODrop xv)

    while progress do
        progress <- false

        for x in Set.toList env.Owned do
            if not (direct.Contains x) && visited.Add x then
                progress <- true

                if allLive.Contains x then
                    let borrowers =
                        allLive |> Set.filter (fun b -> b <> x && (ownersStar env b).Contains x)

                    match tryUnpack p env x borrowers e L with
                    | Some(env', op) ->
                        env <- env'
                        ops.Add op
                    | None ->
                        // x is dead and only kept alive by borrows of it. If one of them is
                        // consumed later, retain the borrows now and free x, so that the
                        // consumer sees a unique value it can reuse; otherwise keep x alive,
                        // which costs no reference counting at all.
                        let directB =
                            borrowers
                            |> Set.filter (fun b ->
                                match env.Owners.TryFind b with
                                | Some os -> List.contains x os
                                | None -> false
                            )

                        let viaDirect =
                            borrowers
                            |> Set.forall (fun b ->
                                directB.Contains b
                                || not (Set.isEmpty (Set.intersect (ownersStar env b) directB))
                            )

                        let consumedLater = owningUses p (not env.TailBorrowed) e

                        if
                            viaDirect
                            && not directB.IsEmpty
                            && Set.isEmpty (Set.intersect directB L)
                            && directB
                               |> Set.forall (fun b -> isManaged allVars[b].Ty && isCopyable allVars[b].Ty)
                            && (allVars[x].FMutable || directB |> Set.exists consumedLater.Contains)
                        then
                            for b in directB do
                                ops.Add(OPromote allVars[b])

                            env <-
                                { env with
                                    Owned = Set.union (Set.remove x env.Owned) directB
                                    Owners = directB |> Set.fold (fun m b -> Map.remove b m) env.Owners
                                    Children = directB |> Set.fold (fun m b -> Map.remove b m) env.Children
                                }

                            dropUnlessNoop allVars[x]
                else
                    env <- { env with Owned = Set.remove x env.Owned }
                    dropUnlessNoop allVars[x]

    env, List.ofSeq ops

let private wrapOps (ops: POp list) (e: Expr) =
    List.foldBack
        (fun op acc ->
            match op with
            | ODrop v -> EDrop(v, acc)
            | OUnpack u -> EUnpack(u, acc)
            | OPromote v -> EPromote(v, acc)
        )
        ops
        e

let private wrapDrops (vs: Var list) (e: Expr) =
    List.foldBack (fun v acc -> EDrop(v, acc)) vs e

let private mkDup (what: Expr) (t: Ty) =
    if isCopyable t then
        EDup(what, t)
    else
        let rec name (t: Ty) =
            match t with
            | TEnt(e, _) -> e.Name
            | TOpt t -> name t + " option"
            | TTuple ts -> ts |> List.map name |> String.concat " * "
            | _ -> "this value"

        fail
            None
            "a value of the move-only type %s is needed again after it was given away (a type that implements IResource without being an ISharedResource, or that holds such a value, cannot be copied: implement ISharedResource to allow sharing)"
            (name t)

/// Rewrite a flat expression: a use in an owning position either moves the variable (the last
/// use of an owned variable) or dups it. Returns the variables it consumed, and attaches a
/// reuse token to a constructor of the right shape.
let private rewriteFlat (p: P) (env: PEnv) (e: Expr) (rootOwning: bool) (lAfter: Set<int>) : Expr * Set<int> * PEnv =
    let occ = List<Set<int>>()

    let rec collect e =
        match e with
        | EVar v -> occ.Add(expand env (Set.singleton v.Id))
        | _ -> List.iter collect (flatKids e)

    collect e
    let later = Array.create (occ.Count + 1) Set.empty

    for i in occ.Count - 1 .. -1 .. 0 do
        later[i] <- Set.union later[i + 1] occ[i]

    let laterAfter i =
        if i + 1 < later.Length then
            later[i + 1]
        else
            Set.empty

    let lAfterX = expand env lAfter
    let consumed = HashSet<int>()
    let mutable idx = -1
    let mutable tokens = env.Tokens

    let takeToken (e: Expr) =
        match e with
        | ECon(t, c, xs, None) when isHeapTy t && not xs.IsEmpty ->
            match tokens |> List.tryFind (fun (_, shape) -> cellsMatch shape (t, c)) with
            | Some(tok, _) ->
                tokens <- tokens |> List.filter (fun (t2, _) -> t2.Id <> tok.Id)
                ECon(t, c, xs, Some tok)
            | None -> e
        | _ -> e

    let wrapExplicitUse (m: Mode) (origArg: Expr) (rewrittenArg: Expr) : Expr =
        match origArg with
        | EKnown _ -> rewrittenArg
        | _ ->
            if not (isManaged (typeOf origArg)) || m = MPlain then
                EUse(UPlain, rewrittenArg)
            elif m = MBorrowed then
                EUse(UKeep, rewrittenArg)
            else
                match rewrittenArg with
                | EDup(inner, _) when not (touchesMutable inner) -> EUse(UKeep, inner)
                | _ -> EUse(UGive, rewrittenArg)

    let rec rw (callBorrowed: Set<int>) (owning: bool) (e: Expr) : Expr =
        match e with
        | EVar v ->
            idx <- idx + 1

            if owning && isManaged v.Ty then
                let usedLater =
                    (laterAfter idx).Contains v.Id
                    || lAfterX.Contains v.Id
                    || callBorrowed.Contains v.Id

                if env.Owned.Contains v.Id && not usedLater && not (consumed.Contains v.Id) then
                    consumed.Add v.Id |> ignore
                    e
                else
                    mkDup e v.Ty
            else
                e
        | _ ->
            let kids = flatKids e

            let flags =
                match e with
                | ECall(f, _, xs, _) ->
                    List.zip (modesOf p f xs) xs
                    |> List.map (fun (m, x) ->
                        match x with
                        | EKnown _ -> false
                        | _ -> m = MOwned
                    )
                | ECallClo(_, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | ECallVt(_, _, xs, _) -> false :: false :: (xs |> List.map (fun _ -> true))
                | ECallIface(_, _, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | EIface _ -> kids |> List.map (fun _ -> true)
                | EEmit(m, _ :: rest, _) when ownsFirst m -> true :: (rest |> List.map (fun _ -> false))
                | EKnown(_, _, xs, _) -> xs |> List.map (fun _ -> false)
                | EClosure(_, _, xs, _)
                | EExnNew(_, xs)
                | ECon(_, _, xs, _) -> xs |> List.map (fun _ -> true)
                | _ -> kids |> List.map (fun _ -> false)

            // Borrowed arguments of a call must stay alive for the duration of the call, so an
            // owned argument of the same call must not move them away (e.g. `c.Method(c)`).
            // For external calls and `callK` `invokeK` sites, any root var appearing in >= 2 args
            // must also stay borrowed so `f(x, x)` does not move `x` while another arg reads it.
            let borrowedKids =
                match e with
                | ECall(f, _, _, _) when not (p.Fns.ContainsKey f) ->
                    let perArg = kids |> List.map (fv >> expand env)
                    let seen = HashSet<int>()
                    let multi = HashSet<int>()

                    for s in perArg do
                        for id in s do
                            if not (seen.Add id) then
                                multi.Add id |> ignore

                    List.zip flags perArg
                    |> List.fold
                        (fun s (own, ks) ->
                            if own then
                                s
                            else
                                Set.union s ks
                        )
                        (Set.ofSeq multi)
                | ECallClo(EVar v, _, _) when env.KParams.Contains v.Id ->
                    let argVars = kids.Tail |> List.map (fv >> expand env)
                    let seen = HashSet<int>()
                    let multi = HashSet<int>()

                    for s in argVars do
                        for id in s do
                            if not (seen.Add id) then
                                multi.Add id |> ignore

                    Set.union (expand env (fv kids.Head)) (Set.ofSeq multi)
                | ECall _
                | ECallClo _
                | ECallVt _
                | ECallIface _ ->
                    List.zip flags kids
                    |> List.fold
                        (fun s (own, k) ->
                            if own then
                                s
                            else
                                Set.union s (expand env (fv k))
                        )
                        Set.empty
                | _ -> Set.empty

            let innerBorrowed = Set.union callBorrowed borrowedKids
            let e' = withFlatKids e (List.map2 (rw innerBorrowed) flags kids)

            let e' =
                match e' with
                | ECallClo(EVar v, xs', t) when env.KParams.Contains v.Id ->
                    let wrappedXs =
                        List.zip kids.Tail xs'
                        |> List.map (fun (origX, newX) ->
                            let m =
                                if isManaged (typeOf origX) then
                                    MOwned
                                else
                                    MPlain

                            wrapExplicitUse m origX newX
                        )

                    ECallClo(EVar v, wrappedXs, t)
                | ECall(f, tArgs, xs', t) when not (p.Fns.ContainsKey f) ->
                    let wrappedXs =
                        List.zip3 (modesOf p f kids) kids xs'
                        |> List.map (fun (m, origX, newX) -> wrapExplicitUse m origX newX)

                    ECall(f, tArgs, wrappedXs, t)
                | _ -> e'

            match e' with
            | EGet _
            | EExnGet _
            | EDeref _
            | EIndex _ when owning && isManaged (typeOf e') -> mkDup e' (typeOf e')
            | ECall(g, _, _, _) when owning && isBorrowedRet p g && isManaged (typeOf e') -> mkDup e' (typeOf e')
            | ECon _ -> takeToken e'
            | _ -> e'

    let e' = rw Set.empty rootOwning e
    e', Set.ofSeq consumed, { env with Tokens = tokens }

let rec private isLocalPath (e: Expr) =
    match e with
    | EVar v -> v.Kind <> VGlobal
    | EGet(x, _, _) -> isLocalPath x
    | _ -> false

let private clearAssignedKnown (ids: Set<int>) (env: PEnv) : PEnv =
    if ids.IsEmpty || (env.Known.IsEmpty && env.Excluded.IsEmpty) then
        env
    else
        let prefixes = ids |> Set.map vk

        let invalidates (k: string) =
            prefixes
            |> Set.exists (fun p -> k = p || k.StartsWith(p + ".", System.StringComparison.Ordinal))

        { env with
            Known = env.Known |> Map.filter (fun k _ -> not (invalidates k))
            Excluded = env.Excluded |> Map.filter (fun k _ -> not (invalidates k))
        }

/// What a test tells about the value it tests. (Nothing is remembered about a variable that
/// can be assigned across an assignment: `clearAssignedKnown` drops stale facts before loops,
/// sequences, handlers and bindings.)
let rec private refine (env: PEnv) (c: Expr) : PEnv * PEnv =
    match c with
    | EPrim("not", [ inner ], _) ->
        let envT, envF = refine env inner
        envF, envT
    | ETest(x, case, ty) when (pathKey x).IsSome && isLocalPath x && not (touchesMutable x) ->
        let key = (pathKey x).Value
        let envT = { env with Known = env.Known.Add(key, case) }
        let excl = Set.add case (defaultArg (env.Excluded.TryFind key) Set.empty)
        let remaining = allCases ty |> List.filter (fun c -> not (excl.Contains c))

        let envF =
            match remaining with
            | [ only ] -> { env with Known = env.Known.Add(key, only) }
            | _ -> { env with Excluded = env.Excluded.Add(key, excl) }

        envT, envF
    | _ -> env, env

/// What an error edge gives up: everything this function still owns, except what the
/// enclosing handler (or the code after the `try`) still needs. It is the "owned and not yet
/// consumed" set that is tracked for the normal path anyway.
let private raiseEdgeDrops (p: P) (env: PEnv) (stillOwned: Set<int>) : Var list =
    stillOwned
    |> Set.filter (fun x -> not (env.RaiseKeep.Contains x))
    |> Set.toList
    |> List.map (fun x -> p.State.Vars[x])
    |> List.filter (fun xv ->
        match env.Known.TryFind(vk xv.Id) with
        | Some c -> not (caseIsNoopDrop xv.Ty c)
        | None -> true
    )

/// A call that may raise carries what is given up if it does.
let private wrapRaising (p: P) (env: PEnv) (e: Expr) (stillOwned: Set<int>) : Expr =
    match e with
    | ECall _
    | ERt _
    | ECallClo _
    | ECallVt _
    | ECallIface _ when callRaises p e <> RNever -> EOnRaise(e, raiseEdgeDrops p env stillOwned)
    | EAssumedRet(js, call) when callRaises p call <> RNever ->
        EOnRaise(EAssumedRet(js, call), raiseEdgeDrops p env stillOwned)
    | EDup((ECall _ as call), t) when callRaises p call <> RNever ->
        EDup(EOnRaise(call, raiseEdgeDrops p env stillOwned), t)
    | _ -> e

let rec private pc (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : Expr =
    let env, ops = settle p env e L
    wrapOps ops (pcNode p env e L)

and private pcNode (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : Expr =
    let allVars = p.State.Vars

    match e with
    | ELet(v, rhs, body) -> pcLet p env v rhs body L
    | ESeq(a, b) ->
        let La = live b L
        let a' = pc p { env with TailBorrowed = false } a La
        // A managed variable that `a` assigns and that is still live afterwards is owned again
        // (its old value was moved or dropped before the assignment).
        let reowned =
            assignedIn a
            |> Set.filter (fun id -> isManaged allVars[id].Ty && La.Contains id)

        let env' =
            clearAssignedKnown
                (assignedIn a)
                { env with
                    Owned = Set.union (Set.intersect env.Owned (expand env La)) reowned
                    Tokens =
                        if isFlat a then
                            env.Tokens
                        else
                            []
                }

        ESeq(a', pc p env' b L)
    | EIf(c, t, f, ty) ->
        let c', consumed, env1 = rewriteFlat p env c false (Set.union (live t L) (live f L))
        let env1 = { env1 with Owned = Set.difference env1.Owned consumed }
        let envT, envF = refine env1 c
        EIf(c', pc p envT t L, pc p envF f L, ty)
    | EWhile(c, b) ->
        let envLoop = clearAssignedKnown (assignedIn b) env
        let head = live e L
        let c', _, _ = rewriteFlat p envLoop c false head
        let envBody, _ = refine envLoop c

        let loop =
            EWhile(
                c',
                pc
                    p
                    { envBody with
                        Tokens = []
                        TailBorrowed = false
                    }
                    b
                    head
            )

        dropAfterLoop p envLoop loop L
    | EFor(i, a, b, up, body) ->
        let envLoop = clearAssignedKnown (assignedIn body) env
        let head = Set.union (live e L) L
        let a', _, _ = rewriteFlat p envLoop a false head
        let b', _, _ = rewriteFlat p envLoop b false head

        let loop =
            EFor(
                i,
                a',
                b',
                up,
                pc
                    p
                    { envLoop with
                        Tokens = []
                        TailBorrowed = false
                    }
                    body
                    head
            )

        dropAfterLoop p envLoop loop L
    | EAssign(v, rhs) ->
        let L' = Set.remove v.Id L

        let assign =
            if isFlat rhs then
                EAssign(v, pcFlat p env rhs L' true)
            else
                EAssign(v, pc p { env with TailBorrowed = false } rhs L')

        // a value that is assigned and never read is given up at once
        if isManaged v.Ty && not (L.Contains v.Id) then
            ESeq(assign, EDrop(v, EUnit))
        else
            assign
    | EStore(lv, rhs) ->
        let lv', _, _ = rewriteFlat p env lv false (Set.union (fv rhs) L)
        // The record that is stored into has to outlive the store: when this is its last use,
        // it is given up after the store, not once the new value has been computed.
        let lvVars = fv lv
        let lAfter = expand env L

        let dying =
            Set.intersect env.Owned (expand env lvVars)
            |> Set.filter (fun x -> not (lAfter.Contains x))
            |> Set.toList
            |> List.map (fun x -> p.State.Vars[x])

        let store = EStore(lv', pcFlat p env rhs (Set.union lvVars L) true)

        if dying.IsEmpty then
            store
        else
            ESeq(store, wrapDrops dying EUnit)
    | ERaise(x, ty) ->
        // the exception moves into the runtime's slot; everything else this function owns is
        // given up before it leaves
        // (inside a `try`, the handler and what follows it may still use the value raised)
        let x', consumed, _ = rewriteFlat p env x true env.RaiseKeep
        let drops = raiseEdgeDrops p env (Set.difference env.Owned consumed)

        match x', drops with
        | EVar _, _
        | _, [] -> wrapDrops drops (ERaise(x', ty))
        | _ ->
            // (the exception is taken first: it may be borrowed from what is given up)
            let raised = p.State.NewVar("raised", typeOf x', VLocal, false)
            ELet(raised, x', wrapDrops drops (ERaise(EVar raised, ty)))
    | ETry(body, exV, handler, ty) ->
        let hl = Set.remove exV.Id (live handler L)
        let Lb = Set.union L hl
        let keep = expand env Lb

        let body' =
            pc
                p
                { env with
                    TailBorrowed = false
                    Tokens = []
                    RaiseKeep = keep
                }
                body
                Lb

        // what only the handler needed is still owned when the body ends without raising
        let handlerOnly =
            Set.difference (Set.intersect env.Owned keep) (expand env L)
            |> Set.toList
            |> List.map (fun x -> p.State.Vars[x])

        let body' =
            if handlerOnly.IsEmpty then
                body'
            elif isVoid ty then
                ESeq(body', wrapDrops handlerOnly EUnit)
            else
                let tmp = p.State.NewVar("tried", ty, VLocal, false)
                ELet(tmp, body', wrapDrops handlerOnly (EVar tmp))

        let ownedH = Set.add exV.Id (Set.intersect env.Owned keep)

        let handler' =
            pc
                p
                (clearAssignedKnown
                    (assignedIn body)
                    { env with
                        Owned = ownedH
                        Tokens = []
                        TailBorrowed = false
                    })
                handler
                L

        ETry(body', exV, handler', ty)
    | _ -> pcFlat p env e L (not env.TailBorrowed)

/// Nothing that is used in a loop is given up inside it: every turn needs it again. What the
/// loop was the last to use is given up when the loop has ended.
and private dropAfterLoop (p: P) (env: PEnv) (loop: Expr) (L: Set<int>) : Expr =
    let after = expand env L

    let dead =
        env.Owned
        |> Set.filter (fun x -> not (after.Contains x))
        |> Set.toList
        |> List.map (fun x -> p.State.Vars[x])

    if dead.IsEmpty then
        loop
    else
        ESeq(loop, wrapDrops dead EUnit)

and private pcFlat (p: P) (env: PEnv) (e: Expr) (L: Set<int>) (rootOwning: bool) : Expr =
    let e', consumed, env' = rewriteFlat p env e rootOwning L
    let e' = wrapRaising p env e' (Set.difference env.Owned consumed)
    let lAfter = expand env' L

    let dropAfter =
        Set.difference env.Owned consumed
        |> Set.filter (fun x -> not (lAfter.Contains x))
        |> Set.toList
        |> List.map (fun x -> p.State.Vars[x])
        |> List.filter (fun xv ->
            match env.Known.TryFind(vk xv.Id) with
            | Some c -> not (caseIsNoopDrop xv.Ty c)
            | None -> true
        )

    if dropAfter.IsEmpty then
        e'
    elif isVoid (typeOf e') then
        ESeq(e', wrapDrops dropAfter EUnit)
    else
        let tmp = p.State.NewVar(tempName e', typeOf e', VLocal, false)
        ELet(tmp, e', wrapDrops dropAfter (EVar tmp))

and private pcLet (p: P) (env: PEnv) (v: Var) (rhs: Expr) (body: Expr) (L: Set<int>) : Expr =
    let Lb = live body L

    if isFlat rhs then
        // An immutable projection of a managed value is a borrowed alias of its root.
        let rec rootOf e =
            match e with
            | EVar r -> Some r
            | EGet(x, _, _) -> rootOf x
            | _ -> None

        // A pattern over a `let mutable` (`match cur with h :: t -> cur <- t; ...`) may borrow
        // its fields when `r` is never mutated inside `body`, or when every existing borrower of `r`
        // is a direct copyable child and `body` ends the linear projection spine with `r <- next`
        // (so `settle` unpacks `r` in place or promotes its borrows before the assignment).
        let isSafeMutableAlias (r: Var) (v: Var) (env: PEnv) (body: Expr) =
            r.FMutable
            && r.Kind <> VGlobal
            && env.Owned.Contains r.Id
            && isCopyable v.Ty
            && (not ((assignedIn body).Contains r.Id)
                || (let existingOk =
                        env.Owners
                        |> Map.forall (fun bId owners ->
                            not (List.contains r.Id owners)
                            || (
                                match env.Children.TryFind bId with
                                | Some(pId, _, _) -> pId = r.Id && isCopyable p.State.Vars[bId].Ty
                                | None -> false
                            )
                        )

                    let rec checkSpine b =
                        match b with
                        | ELet(w, EGet(EVar r2, _, _), rest) when r2.Id = r.Id && not w.FMutable && isCopyable w.Ty ->
                            checkSpine rest
                        | ELet(_, uRhs, rest) when
                            not ((fv uRhs).Contains r.Id) && not ((assignedIn uRhs).Contains r.Id)
                            ->
                            checkSpine rest
                        | EAssign(r2, assignRhs) when
                            r2.Id = r.Id && isFlat assignRhs && not ((fv assignRhs).Contains r.Id)
                            ->
                            true
                        | ESeq(EAssign(r2, assignRhs), afterAssign) when
                            r2.Id = r.Id
                            && isFlat assignRhs
                            && not ((fv assignRhs).Contains r.Id)
                            && not ((assignedIn afterAssign).Contains r.Id)
                            ->
                            true
                        | ESeq(head, tail) when not ((fv head).Contains r.Id) && not ((assignedIn head).Contains r.Id) ->
                            checkSpine tail
                        | _ -> false

                    existingOk && checkSpine body))

        // (A projection of a variable that can be assigned is not an alias unless proven safe by
        // `isSafeMutableAlias`: otherwise the variable may be given another value while the name is
        // still in use, so the name gets its own reference.)
        let env1, isAlias, assumedRet =
            match rhs with
            // (Nor is a read of a field that can be assigned, if anything while the name is in
            // use may assign that field: field-sensitive `mayOverwriteRead` lets reads across stores
            // to other fields or pure stdlib calls remain borrowed.)
            | EGet(x, proj, _) when
                isManaged v.Ty
                && not v.FMutable
                && (isStablePath x
                    || (
                        match x with
                        | EVar r -> isSafeMutableAlias r v env body
                        | EDeref(EVar r, _) -> not r.FMutable && r.Kind = VParam
                        | _ -> false
                    ))
                && not (isSharedFieldRead rhs)
                && (not (touchesMutable rhs)
                    || not (mayOverwriteRead p env.StoreAsserts env.UnescapedRefs rhs body))
                ->
                let env1 =
                    match rootOf x with
                    | Some r -> { env with Owners = env.Owners.Add(v.Id, [ r.Id ]) }
                    | None -> env

                let child (r: Var) (case: string) (field: string) =
                    { env1 with Children = env1.Children.Add(v.Id, (r.Id, case, field)) }

                let env1 =
                    match x, proj with
                    | EVar r, PField f -> child r "" f
                    | EVar r, PCase(c, f) -> child r c f
                    | EVar r, PItem i -> child r "" (string<int> i)
                    | EVar r, PSome -> child r "Some" "Value"
                    | _ -> env1

                env1, true, None
            | ECall(g, _, args, _) when
                isManaged v.Ty
                && not v.FMutable
                && isBorrowedRet p g
                && p.Fns[g].RetFrom.Value
                   |> List.forall (fun i -> i < args.Length && isStablePath args[i] && not (touchesMutable args[i]))
                ->
                // the result is a borrow of the source arguments: they stay alive while it is live
                let srcs =
                    p.Fns[g].RetFrom.Value
                    |> List.choose (fun i -> rootOf args[i])
                    |> List.map (fun r -> r.Id)

                { env with Owners = env.Owners.Add(v.Id, srcs) }, true, None
            | ECall(g, _, args, _) when
                isManaged v.Ty
                && not v.FMutable
                && (
                    match extBorrowedRet p g args with
                    | Some js ->
                        js
                        |> List.forall (fun i ->
                            i < args.Length
                            && isStablePath args[i]
                            && not (touchesMutable args[i])
                            && (
                                match args[i] with
                                | EKnown _ -> false
                                | EVar w -> not (env.KParams.Contains w.Id)
                                | _ -> true
                            )
                        )
                    | None -> false
                )
                ->
                let js = (extBorrowedRet p g args).Value

                let srcs = js |> List.choose (fun i -> rootOf args[i]) |> List.map (fun r -> r.Id)

                { env with Owners = env.Owners.Add(v.Id, srcs) }, true, Some js
            // A span views what it was made of (an array's items, another span): what it was
            // made of stays alive while it is in use.
            | _ when
                (match v.Ty with
                 | TSlice _ -> true
                 | _ -> false)
                ->
                let srcs = fv rhs |> Set.toList
                { env with Owners = env.Owners.Add(v.Id, srcs) }, true, None
            | _ -> env, false, None

        let rhs', consumed, env2 = rewriteFlat p env1 rhs (isManaged v.Ty && not isAlias) Lb

        let rhs' =
            match assumedRet with
            | Some js -> EAssumedRet(js, rhs')
            | None -> rhs'

        let remaining = Set.difference env1.Owned consumed
        let rhs' = wrapRaising p env1 rhs' remaining
        let after = Set.remove v.Id (expand env2 Lb)

        let dropAfter =
            remaining
            |> Set.filter (fun x -> not (after.Contains x))
            |> Set.toList
            |> List.map (fun x -> p.State.Vars[x])
            |> List.filter (fun xv ->
                match env.Known.TryFind(vk xv.Id) with
                | Some c -> not (caseIsNoopDrop xv.Ty c)
                | None -> true
            )

        let owned =
            Set.difference remaining (dropAfter |> List.map (fun x -> x.Id) |> Set.ofList)

        let owned =
            if isManaged v.Ty && not isAlias then
                Set.add v.Id owned
            else
                owned

        let known =
            match rhs with
            | _ when v.FMutable -> env2.Known
            | ECon(_, c, _, _) when c <> "" -> env2.Known.Add(vk v.Id, c)
            | EGet _ ->
                match pathKey rhs |> Option.bind env2.Known.TryFind with
                | Some c -> env2.Known.Add(vk v.Id, c)
                | None -> env2.Known
            | _ -> env2.Known

        let env3 =
            { env2 with
                Owned = owned
                Known = known
            }

        ELet(v, rhs', wrapDrops dropAfter (pc p env3 body L))
    else
        let lRhs = Set.remove v.Id Lb
        let rhs' = pc p { env with TailBorrowed = false } rhs lRhs
        let keep = expand env lRhs
        // (a managed variable that the right-hand side assigns and that is still live in the body
        // is owned again, as after an assignment in a sequence: `let ok = (x <- v; true)`)
        let reowned =
            assignedIn rhs
            |> Set.filter (fun id -> isManaged p.State.Vars[id].Ty && Lb.Contains id)

        let owned = Set.union (Set.intersect env.Owned keep) reowned

        let owned =
            if isManaged v.Ty then
                Set.add v.Id owned
            else
                owned

        ELet(
            v,
            rhs',
            pc
                p
                (clearAssignedKnown
                    (assignedIn rhs)
                    { env with
                        Owned = owned
                        Tokens = []
                    })
                body
                L
        )

let private emptyEnv =
    {
        Owned = Set.empty
        Owners = Map.empty
        Children = Map.empty
        Known = Map.empty
        Excluded = Map.empty
        Tokens = []
        TailBorrowed = false
        RaiseKeep = Set.empty
        UnescapedRefs = Set.empty
        KParams = Set.empty
        StoreAsserts = List()
    }

let private capsAreImmutableVars (caps: Expr list) =
    caps
    |> List.forall (
        function
        | EVar v -> not v.FMutable && v.Kind <> VGlobal
        | _ -> false
    )

let rec private dropDeadClosures (e: Expr) : Expr =
    match e with
    | ELet(v, (EClosure(_, _, caps, _) as rhs), body) ->
        let body' = dropDeadClosures body

        if not v.FMutable && capsAreImmutableVars caps && not ((fv body').Contains v.Id) then
            body'
        else
            ELet(v, rhs, body')
    | ELet(v, rhs, body) -> ELet(v, dropDeadClosures rhs, dropDeadClosures body)
    | ESeq(a, b) -> ESeq(dropDeadClosures a, dropDeadClosures b)
    | EIf(c, t, f, ty) -> EIf(dropDeadClosures c, dropDeadClosures t, dropDeadClosures f, ty)
    | EWhile(c, b) -> EWhile(dropDeadClosures c, dropDeadClosures b)
    | EFor(i, a, b, up, body) -> EFor(i, dropDeadClosures a, dropDeadClosures b, up, dropDeadClosures body)
    | EAssign(v, r) -> EAssign(v, dropDeadClosures r)
    | EStore(lv, r) -> EStore(dropDeadClosures lv, dropDeadClosures r)
    | ETry(b, v, h, ty) -> ETry(dropDeadClosures b, v, dropDeadClosures h, ty)
    | _ -> e

let private resolveKnownClosure
    (env: Map<int, string * Ty list * Expr list * Ty>)
    (e: Expr)
    : (string * Ty list * Expr list * Ty) option
    =
    match e with
    | EClosure(target, typeArgs, caps, ty) when capsAreImmutableVars caps -> Some(target, typeArgs, caps, ty)
    | EVar v -> env.TryFind v.Id
    | _ -> None

/// Turn calls to known closures (`let f = closure(...) in f(x)` or direct `closure(...)(x)`)
/// into direct `ECall`s so no closure indirect call happens and unused closures can be dropped.
let rec private foldKnownClosures
    (fns: Dictionary<string, FnInfo>)
    (curried2: Dictionary<string, string>)
    (env: Map<int, string * Ty list * Expr list * Ty>)
    (e: Expr)
    : Expr
    =
    let go = foldKnownClosures fns curried2 env

    let tryDirectCall (target: string) (cTypeArgs: Ty list) (caps: Expr list) (args: Expr list) (resTy: Ty) =
        match fns.TryGetValue target with
        | true, fn when
            fn.Params.Length = caps.Length + args.Length
            && fn.TypeParams.Length = cTypeArgs.Length
            ->
            let inst =
                if fn.TypeParams.IsEmpty then
                    Map.empty
                else
                    Map.ofList (List.zip fn.TypeParams cTypeArgs)

            let fullArgs = caps @ args

            if
                List.forall2 (fun (q: Var) a -> zigType (substTy inst q.Ty) = zigType (typeOf a)) fn.Params fullArgs
                && zigType (substTy inst fn.Ret) = zigType resTy
            then
                Some(ECall(target, cTypeArgs, fullArgs, resTy))
            else
                None
        | _ -> None

    match e with
    | ELet(v, r, b) ->
        let r' = go r

        let env' =
            match r' with
            | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
            | _ -> env

        ELet(v, r', foldKnownClosures fns curried2 env' b)
    | ESeq(a, b) -> ESeq(go a, go b)
    | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
    | EWhile(c, b) -> EWhile(go c, go b)
    | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
    | EAssign(v, r) -> EAssign(v, go r)
    | EStore(lv, r) -> EStore(go lv, go r)
    | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
    | ERaise(x, ty) -> ERaise(go x, ty)
    | _ ->
        let e' =
            match flatKids e with
            | [] -> e
            | ks -> withFlatKids e (List.map go ks)

        match e' with
        | ECallClo(fExpr, args, resTy) ->
            match resolveKnownClosure env fExpr with
            | Some(target, cTypeArgs, caps, TFn(ps, _)) when args.Length = ps.Length ->
                match tryDirectCall target cTypeArgs caps args resTy with
                | Some call -> call
                | None -> e'
            | Some(target, cTypeArgs, caps, TFn([ _ ], TFn([ _ ], _))) when args.Length = 2 ->
                match curried2.TryGetValue target with
                | true, target2 ->
                    match tryDirectCall target2 cTypeArgs caps args resTy with
                    | Some call -> call
                    | None -> e'
                | _ -> e'
            | _ -> e'
        | _ -> e'

let private genNameRx =
    System.Text.RegularExpressions.Regex("@\"'([^\"]+)\"", System.Text.RegularExpressions.RegexOptions.Compiled)

let rec private exprSize (e: Expr) =
    match e with
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b)
    | EStore(r, b) -> 1 + exprSize r + exprSize b
    | EIf(c, t, f, _) -> 1 + exprSize c + exprSize t + exprSize f
    | EFor(_, a, b, _, body) -> 1 + exprSize a + exprSize b + exprSize body
    | EAssign(_, r)
    | EDrop(_, r)
    | EUnpack(_, r)
    | EPromote(_, r)
    | ERaise(r, _) -> 1 + exprSize r
    | ETry(b, _, h, _) -> 1 + exprSize b + exprSize h
    | _ -> 1 + (flatKids e |> List.sumBy exprSize)

/// Fold calls to known closures and clone intra-file higher-order functions when passed known
/// local/file callbacks, turning indirect `f.code(...)` calls into direct calls with borrow
/// inference and TRMC preserved.
let private specializeHofs (state: FileState) (hooks: HashSet<string>) : unit =
    let fns = Dictionary<string, FnInfo>()

    for fn in state.Fns do
        fns[fn.Name] <- fn

    let polishFn (fn: FnInfo) =
        fn.Body <-
            fn.Body
            |> foldKnownClosures fns state.Curried2 Map.empty
            |> dropDeadClosures
            |> cleanup

    for fn in state.Fns do
        polishFn fn

    let substStr (inst: Map<string, Ty>) (s: string) =
        if inst.IsEmpty || not (s.Contains("@\"'")) then
            s
        else
            genNameRx.Replace(
                s,
                fun m ->
                    match inst.TryFind m.Groups.[1].Value with
                    | Some ty -> zigType ty
                    | None -> m.Value
            )

    let rec instTy (inst: Map<string, Ty>) (t: Ty) =
        if inst.IsEmpty then
            t
        else
            match t with
            | TGen n ->
                match inst.TryFind n with
                | Some x -> x
                | None -> t
            | TPrim s when s.Contains("@\"'") -> TPrim(substStr inst s)
            | TEnt(ent, args) -> TEnt(ent, args |> List.map (instTy inst))
            | TOpt x -> TOpt(instTy inst x)
            | TTuple ts -> TTuple(ts |> List.map (instTy inst))
            | TPtr(x, c) -> TPtr(instTy inst x, c)
            | TSlice(x, c) -> TSlice(instTy inst x, c)
            | TArr(x, n) -> TArr(instTy inst x, n)
            | TFn(ps, r) -> TFn(ps |> List.map (instTy inst), instTy inst r)
            | TSlot(ps, r) -> TSlot(ps |> List.map (instTy inst), instTy inst r)
            | TTok(x, c) -> TTok(instTy inst x, c)
            | TPrim _ -> t

    let calleeUsesFnParam (calleeName: string) (pId: int) (body: Expr) =
        exists
            (function
            | ECallClo(EVar v, _, _) when v.Id = pId -> true
            | ECall(g, _, xs, _) when g <> calleeName && fns.ContainsKey g ->
                xs
                |> List.exists (
                    function
                    | EVar v -> v.Id = pId
                    | _ -> false
                )
            | _ -> false)
            body

    let memo = Dictionary<string, string>()

    let freshSpecName (baseName: string) =
        let mutable i = 0
        let mutable cand = $"%s{baseName}$spec%d{i}"

        while fns.ContainsKey cand do
            i <- i + 1
            cand <- $"%s{baseName}$spec%d{i}"

        cand

    let cloneSpecializedFn
        (callee: FnInfo)
        (callTypeArgs: Ty list)
        (specTypeParams: string list)
        (specMap: Map<int, string * Ty list * Expr list * Ty>)
        (specKey: string)
        =
        match memo.TryGetValue specKey with
        | true, existing -> existing
        | _ ->
            let specName = freshSpecName callee.Name
            memo[specKey] <- specName

            let inst =
                if callee.TypeParams.IsEmpty then
                    Map.empty
                else
                    Map.ofList (List.zip callee.TypeParams callTypeArgs)

            let varMap = Dictionary<int, Var>()
            let specParams = List<Var>()
            let capVarsByIdx = Dictionary<int, Var list>()
            let localCloWrappers = List<Var * Expr>()

            callee.Params
            |> List.iteri (fun idx p ->
                match specMap.TryFind idx with
                | Some(cloTarget, cloTypeArgs, cloCaps, _) ->
                    let freshCaps =
                        cloCaps
                        |> List.mapi (fun k c -> state.NewVar($"%s{p.Base}_c%d{k}", typeOf c, VParam, false))

                    for v in freshCaps do
                        specParams.Add v

                    capVarsByIdx[idx] <- freshCaps
                    let pTy = instTy inst p.Ty
                    let freshClo = state.NewVar(p.Base, pTy, VLocal, false)
                    varMap[p.Id] <- freshClo
                    localCloWrappers.Add((freshClo, EClosure(cloTarget, cloTypeArgs, freshCaps |> List.map EVar, pTy)))
                | None ->
                    let p' = state.NewVar(p.Base, instTy inst p.Ty, VParam, p.FMutable)
                    varMap[p.Id] <- p'
                    specParams.Add p'
            )

            let mapVar (v: Var) =
                match varMap.TryGetValue v.Id with
                | true, v' -> v'
                | _ -> v

            let freshLocal (v: Var) =
                let v' = state.NewVar(v.Base, instTy inst v.Ty, v.Kind, v.FMutable)
                varMap[v.Id] <- v'
                v'

            let rec clone (e: Expr) : Expr =
                match e with
                | EVar v -> EVar(mapVar v)
                | ELit(s, t) -> ELit(substStr inst s, instTy inst t)
                | EUnit -> EUnit
                | EPrim(op, xs, t) -> EPrim(op, xs |> List.map clone, instTy inst t)
                | ECall(f, recTypeArgs, recArgs, recRetTy) when
                    f = callee.Name
                    && recTypeArgs.Length = callee.TypeParams.Length
                    && (recTypeArgs |> List.map (instTy inst)) = callTypeArgs
                    && recArgs.Length = callee.Params.Length
                    && (specMap
                        |> Map.forall (fun idx _ ->
                            match recArgs[idx] with
                            | EVar v -> v.Id = callee.Params[idx].Id
                            | _ -> false
                        ))
                    ->
                    let expandedRecArgs =
                        recArgs
                        |> List.indexed
                        |> List.collect (fun (idx, a) ->
                            match capVarsByIdx.TryGetValue idx with
                            | true, caps -> caps |> List.map EVar
                            | _ -> [ clone a ]
                        )

                    ECall(specName, specTypeParams |> List.map TGen, expandedRecArgs, instTy inst recRetTy)
                | ECall(f, tys, xs, t) -> ECall(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | ECallClo(f, xs, t) -> ECallClo(clone f, xs |> List.map clone, instTy inst t)
                | ECallVt(f, s, xs, t) -> ECallVt(clone f, clone s, xs |> List.map clone, instTy inst t)
                | EClosure(f, tys, xs, t) ->
                    EClosure(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | EKnown(f, tys, xs, t) -> EKnown(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | EUse(u, x) -> EUse(u, clone x)
                | EAssumedRet(js, call) -> EAssumedRet(js, clone call)
                | EIface(t, src, slots) ->
                    let src' =
                        match src with
                        | ISrcValue x -> ISrcValue(clone x)
                        | ISrcCaptures xs -> ISrcCaptures(xs |> List.map clone)
                        | ISrcUpcast x -> ISrcUpcast(clone x)

                    let slots' =
                        slots |> List.map (fun (s, (f, tys)) -> s, (f, tys |> List.map (instTy inst)))

                    EIface(instTy inst t, src', slots')
                | ECallIface(r, slot, xs, t) -> ECallIface(clone r, slot, xs |> List.map clone, instTy inst t)
                | ECon(t, c, xs, tok) -> ECon(instTy inst t, c, xs |> List.map clone, tok |> Option.map mapVar)
                | EGet(x, p, t) -> EGet(clone x, p, instTy inst t)
                | ETest(x, c, t) -> ETest(clone x, c, instTy inst t)
                | EAddr(x, c) -> EAddr(clone x, c)
                | EDeref(x, t) -> EDeref(clone x, instTy inst t)
                | EIndex(a, b, t) -> EIndex(clone a, clone b, instTy inst t)
                | EEmit(m, xs, t) -> EEmit(substStr inst m, xs |> List.map clone, instTy inst t)
                | ERt(m, xs, t) -> ERt(substStr inst m, xs |> List.map clone, instTy inst t)
                | EExnNew(ent, xs) -> EExnNew(ent, xs |> List.map clone)
                | EExnTest(x, ent) -> EExnTest(clone x, ent)
                | EExnGet(x, ent, f, t) -> EExnGet(clone x, ent, f, instTy inst t)
                | EOnRaise(x, ds) -> EOnRaise(clone x, ds |> List.map mapVar)
                | EDup(x, t) -> EDup(clone x, instTy inst t)
                | ELet(v, r, b) ->
                    let r' = clone r
                    let v' = freshLocal v
                    ELet(v', r', clone b)
                | ESeq(a, b) -> ESeq(clone a, clone b)
                | EIf(c, t, f, ty) -> EIf(clone c, clone t, clone f, instTy inst ty)
                | EWhile(c, b) -> EWhile(clone c, clone b)
                | EFor(i, a, b, up, body) ->
                    let a' = clone a
                    let b' = clone b
                    let i' = freshLocal i
                    EFor(i', a', b', up, clone body)
                | EAssign(v, r) -> EAssign(mapVar v, clone r)
                | EStore(lv, r) -> EStore(clone lv, clone r)
                | EDrop(v, k) -> EDrop(mapVar v, clone k)
                | EUnpack(u, k) ->
                    let u' =
                        { u with
                            Scrut = mapVar u.Scrut
                            Moves = u.Moves |> List.map (fun (s, v) -> s, freshLocal v)
                            Token = u.Token |> Option.map freshLocal
                        }

                    EUnpack(u', clone k)
                | EPromote(v, k) -> EPromote(mapVar v, clone k)
                | ERaise(x, t) -> ERaise(clone x, instTy inst t)
                | ETry(b, v, h, t) ->
                    let b' = clone b
                    let v' = freshLocal v
                    ETry(b', v', clone h, instTy inst t)

            let wrappedBody =
                Seq.foldBack (fun (v, cExpr) acc -> ELet(v, cExpr, acc)) localCloWrappers (clone callee.Body)
                |> foldKnownClosures fns state.Curried2 Map.empty
                |> dropDeadClosures
                |> cleanup

            match state.Arenas.TryGetValue callee.Name with
            | true, bytes -> state.Arenas[specName] <- bytes
            | _ -> ()

            let psList = List.ofSeq specParams

            let specFn =
                {
                    Name = specName
                    TypeParams = specTypeParams
                    Params = psList
                    Modes = psList |> List.map (fun _ -> MPlain)
                    Ret = instTy inst callee.Ret
                    Body = wrappedBody
                    RetFrom = None
                    Raises = RNever
                    Stores = false
                    IsLocal = true
                    IsEntryPoint = false
                    Range = callee.Range
                    NoEscape = []
                    BodyK = None
                    StoreFacts = [], false, false
                    AssertedNoRaise = []
                    AssertedStores = []
                    NeedsChain = false
                    PendingChainDeps = []
                    BodyTc = None
                }

            state.Fns.Add specFn
            fns[specName] <- specFn
            specName

    let rec rewriteCalls (round: int) (env: Map<int, string * Ty list * Expr list * Ty>) (e: Expr) : Expr =
        let go = rewriteCalls round env

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            ELet(v, r', rewriteCalls round env' b)
        | ESeq(a, b) -> ESeq(go a, go b)
        | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
        | EWhile(c, b) -> EWhile(go c, go b)
        | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
        | EAssign(v, r) -> EAssign(v, go r)
        | EStore(lv, r) -> EStore(go lv, go r)
        | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
        | ERaise(x, ty) -> ERaise(go x, ty)
        | _ ->
            let e' =
                match flatKids e with
                | [] -> e
                | ks -> withFlatKids e (List.map go ks)

            match e' with
            | ECall(calleeName, callTypeArgs, callArgs, callRetTy) ->
                match fns.TryGetValue calleeName with
                | true, callee when
                    not (hooks.Contains calleeName)
                    && not callee.IsEntryPoint
                    && callee.Params.Length = callArgs.Length
                    && callee.TypeParams.Length = callTypeArgs.Length
                    && exprSize callee.Body <= 250
                    && (round = 0 || not (calleeName.Contains("$spec")))
                    ->
                    let assigned = assignedIn callee.Body

                    let specEntries =
                        List.zip callee.Params callArgs
                        |> List.indexed
                        |> List.choose (fun (idx, (p, a)) ->
                            match p.Ty with
                            | TFn _ when not (assigned.Contains p.Id) ->
                                match resolveKnownClosure env a with
                                | Some(cloTarget, _, _, _) as found when
                                    fns.ContainsKey cloTarget && calleeUsesFnParam calleeName p.Id callee.Body
                                    ->
                                    Some(idx, found.Value)
                                | _ -> None
                            | _ -> None
                        )

                    if specEntries.IsEmpty then
                        e'
                    else
                        let specMap = Map.ofList specEntries

                        let inst =
                            if callee.TypeParams.IsEmpty then
                                Map.empty
                            else
                                Map.ofList (List.zip callee.TypeParams callTypeArgs)

                        let specTypeParams =
                            freeGens (
                                callTypeArgs
                                @ [ callRetTy; instTy inst callee.Ret ]
                                @ (callArgs
                                   |> List.indexed
                                   |> List.collect (fun (idx, a) ->
                                       match specMap.TryFind idx with
                                       | Some(_, cTys, cCaps, _) -> cTys @ (cCaps |> List.map typeOf)
                                       | None -> [ typeOf a ]
                                   ))
                            )

                        let typeKeyStr = callTypeArgs |> List.map tyKey |> String.concat ","

                        let cloKeyStr =
                            specEntries
                            |> List.map (fun (idx, (t, tys, caps, cty)) ->
                                let cTys = tys |> List.map tyKey |> String.concat ","
                                let capTys = caps |> List.map (typeOf >> tyKey) |> String.concat ","
                                $"%d{idx}:%s{t}<%s{cTys}>(%s{capTys}):%s{tyKey cty}"
                            )
                            |> String.concat ";"

                        let specParamsStr = String.concat "," specTypeParams

                        let specKey = $"%s{calleeName}|<%s{specParamsStr}>|<%s{typeKeyStr}>|%s{cloKeyStr}"

                        let specName = cloneSpecializedFn callee callTypeArgs specTypeParams specMap specKey

                        let expandedArgs =
                            callArgs
                            |> List.indexed
                            |> List.collect (fun (idx, a) ->
                                match specMap.TryFind idx with
                                | Some(_, _, caps, _) -> caps
                                | None -> [ a ]
                            )

                        ECall(specName, specTypeParams |> List.map TGen, expandedArgs, callRetTy)
                | _ -> e'
            | _ -> e'

    for round in 0..1 do
        for fn in List.ofSeq state.Fns do
            fn.Body <-
                rewriteCalls round Map.empty fn.Body
                |> foldKnownClosures fns state.Curried2 Map.empty
                |> dropDeadClosures
                |> cleanup

    for fn in state.Fns do
        polishFn fn

    // Prune local helper functions left dead after specialization / closure folding.
    let stripRaw (s: string) =
        if s.StartsWith("@raw:", System.StringComparison.Ordinal) then
            s.Substring 5
        else
            s

    let live = HashSet<string>()
    let work = Queue<string>()

    let enqueue name =
        if fns.ContainsKey name && live.Add name then
            work.Enqueue name

    for fn in state.Fns do
        if not fn.IsLocal || fn.IsEntryPoint || hooks.Contains fn.Name then
            enqueue fn.Name

    for (_, _, name) in state.Values do
        enqueue name

    for (_, name) in state.Tests do
        enqueue name

    for objDecl in state.Objs do
        for table in objDecl.Tables do
            match table with
            | Some(_, entries) ->
                for (_, target, _, _) in entries do
                    enqueue (stripRaw target)
            | None -> ()

        match objDecl.ToString with
        | Some(target, _) -> enqueue (stripRaw target)
        | None -> ()

        for (_, fn) in objDecl.Overrides do
            enqueue fn

    while work.Count > 0 do
        let fn = fns[work.Dequeue()]

        exists
            (fun x ->
                match x with
                | ECall(f, _, _, _) -> enqueue f
                | EClosure(f, _, _, ty) ->
                    enqueue f

                    match ty with
                    | TFn([ _ ], TFn([ _ ], _)) ->
                        match state.Curried2.TryGetValue f with
                        | true, f2 -> enqueue f2
                        | _ -> ()
                    | _ -> ()
                | EIface(_, _, slots) ->
                    for (_, (f, _)) in slots do
                        enqueue (stripRaw f)
                | _ -> ()

                false
            )
            fn.Body
        |> ignore

    let kept =
        state.Fns
        |> Seq.filter (fun fn -> not fn.IsLocal || live.Contains fn.Name)
        |> List.ofSeq

    state.Fns.Clear()
    state.Fns.AddRange kept

let rec private totalCurriedArgs (t: Ty) : int =
    match t with
    | TFn([ _ ], (TFn _ as inner)) -> 1 + totalCurriedArgs inner
    | TFn(ps, _) -> ps.Length
    | _ -> 0

let private directFullArity (t: Ty) : int option =
    match t with
    | TFn([ _ ], TFn([ _ ], innerRet)) ->
        match innerRet with
        | TFn _ -> None
        | _ -> Some 2
    | TFn(ps, innerRet) ->
        match innerRet with
        | TFn _ -> None
        | _ -> Some ps.Length
    | _ -> None

let rec private isChainConsumer (vId: int) (remArgs: int) (e: Expr) : bool =
    let has v = (fv v).Contains vId

    match e with
    | ELet(v2, ECallClo(EVar v, args2, _), rest) when v.Id = vId && not v2.FMutable ->
        args2.Length > 0
        && args2.Length < remArgs
        && List.forall (not << has) args2
        && not (has rest)
        && isChainConsumer v2.Id (remArgs - args2.Length) rest
    | ELet(_, r, b) ->
        if has r then
            not (has b) && isChainConsumer vId remArgs r
        else
            isChainConsumer vId remArgs b
    | ESeq(a, b) ->
        if has a then
            not (has b) && isChainConsumer vId remArgs a
        else
            isChainConsumer vId remArgs b
    | EIf(c, t, f, _) ->
        not (has c)
        && (not (has t) || isChainConsumer vId remArgs t)
        && (not (has f) || isChainConsumer vId remArgs f)
    | EWhile _
    | EFor _
    | EAssign _
    | EStore _
    | ERaise _
    | ETry _ -> false
    | EDrop(v, k)
    | EPromote(v, k) -> v.Id <> vId && isChainConsumer vId remArgs k
    | EUnpack(u, k) ->
        u.Scrut.Id <> vId
        && (u.Moves |> List.forall (fun (_, mv) -> mv.Id <> vId))
        && isChainConsumer vId remArgs k
    | ECallClo(EVar v, args2, _) when v.Id = vId -> args2.Length = remArgs && List.forall (not << has) args2
    | EVar v when v.Id = vId -> false
    | _ ->
        flatKids e
        |> List.forall (fun k -> not (has k) || isChainConsumer vId remArgs k)

let rec private alwaysRaisesExpr (e: Expr) =
    match e with
    | ERaise _ -> true
    | ELet(_, _, b)
    | ESeq(_, b) -> alwaysRaisesExpr b
    | EIf(_, t, f, _) -> alwaysRaisesExpr t && alwaysRaisesExpr f
    | _ -> false

let rec private peelDropsToCon (e: Expr) : (Ty * Expr list) option =
    match e with
    | ECon(conTy, _, conArgs, _) -> Some(conTy, conArgs)
    | EDrop(_, rest) -> peelDropsToCon rest
    | ELet(tmp, ECon(conTy, _, conArgs, _), body) ->
        let rec endsInTmp b =
            match b with
            | EDrop(_, rest) -> endsInTmp rest
            | EVar v when v.Id = tmp.Id -> true
            | _ -> false

        if endsInTmp body then
            Some(conTy, conArgs)
        else
            None
    | _ -> None

let private tryMatchTrmcHole (r: Var) (conBody: Expr) : Ty option =
    match peelDropsToCon conBody with
    | Some(TEnt(ent, _) as conTy, conArgs) when (ent.Kind = KHeapUnion || ent.Kind = KValueUnion) && not conArgs.IsEmpty ->
        let hits =
            conArgs
            |> List.indexed
            |> List.filter (fun (_, a) ->
                match a with
                | EVar v -> v.Id = r.Id
                | _ -> false
            )

        match hits with
        | [ (holeIdx, _) ] when
            conArgs
            |> List.indexed
            |> List.forall (fun (j, a) -> j = holeIdx || not (Set.contains r.Id (fv a)))
            ->
            Some conTy
        | _ -> None
    | _ -> None

let rec private unwrapTailCallExpr (e: Expr) =
    match e with
    | EAssumedRet(_, x)
    | EOnRaise(x, _)
    | EDup(x, _) -> unwrapTailCallExpr x
    | _ -> e

/// Functions whose tail or TRMC cycles cannot execute as stack-neutral loops inside a `$k`
/// clone (polymorphic/arity-mismatched self recursion, non-heap TRMC, or intra-file SCCs).
let private noEscapeExcludedTailFns (fns: FnInfo seq) : HashSet<string> =
    let byName = Dictionary<string, FnInfo>()

    for fn in fns do
        byName[fn.Name] <- fn

    let excluded = HashSet<string>()
    let edges = Dictionary<string, string list>()

    for fn in fns do
        let rec collect (trmcConOpt: Ty option) (e: Expr) : string list =
            match e with
            | ELet(_, rhs, _) when alwaysRaisesExpr rhs -> []
            | ELet(v, rhs, EVar v2) when v.Id = v2.Id -> collect trmcConOpt rhs
            | ELet(r, callRhs, conBody) when not (alwaysRaisesExpr callRhs) ->
                match tryMatchTrmcHole r conBody with
                | Some conTy -> collect (Some conTy) callRhs
                | None -> collect None conBody
            | ELet(_, _, b)
            | ESeq(_, b)
            | EDrop(_, b)
            | EUnpack(_, b)
            | EPromote(_, b) -> collect trmcConOpt b
            | EIf(_, t, f, _) -> collect trmcConOpt t @ collect trmcConOpt f
            | ETry _ -> []
            | _ ->
                match unwrapTailCallExpr e with
                | ECall(g, tArgs, args, _) when byName.ContainsKey g && args.Length = byName[g].Params.Length ->
                    if g = fn.Name then
                        if
                            tArgs <> (fn.TypeParams |> List.map TGen)
                            || (
                                match trmcConOpt with
                                | Some conTy -> not (isHeapTy conTy) || fn.RetFrom.IsSome
                                | None -> false
                            )
                        then
                            excluded.Add fn.Name |> ignore

                        []
                    else
                        [ g ]
                | _ -> []

        edges[fn.Name] <- collect None fn.Body |> List.distinct

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
                    excluded.Add w |> ignore

    for fn in fns do
        if not (index.ContainsKey fn.Name) then
            connect fn.Name

    excluded

let private inferNoEscape (p: P) (hooks: HashSet<string>) : unit =
    let fns = p.State.Fns
    let tailExcluded = noEscapeExcludedTailFns fns
    let noEscape = Dictionary<string, bool[]>()

    for fn in fns do
        let excluded =
            fn.IsEntryPoint || hooks.Contains fn.Name || tailExcluded.Contains fn.Name

        let assigned =
            if excluded then
                Set.empty
            else
                assignedIn fn.Body

        noEscape[fn.Name] <-
            fn.Params
            |> List.map (fun q ->
                if excluded then
                    false
                else
                    match q.Ty with
                    | TFn _ -> not (assigned.Contains q.Id)
                    | _ -> false
            )
            |> Array.ofList

    let paramOk (fn: FnInfo) (pIdx: int) (q: Var) : bool =
        let tot = totalCurriedArgs q.Ty
        let fullArity = directFullArity q.Ty

        let rec check (e: Expr) : bool =
            match e with
            | EVar v -> v.Id <> q.Id
            | ELet(vMid, ECallClo(EVar pv, args1, _), scope) when
                pv.Id = q.Id
                && not vMid.FMutable
                && args1.Length > 0
                && args1.Length < tot
                && isChainConsumer vMid.Id (tot - args1.Length) scope
                ->
                List.forall check args1 && check scope
            | ECallClo(EVar pv, args, _) when pv.Id = q.Id -> fullArity = Some args.Length && List.forall check args
            | ECall(g, tArgs, args, _) when g = fn.Name ->
                tArgs = (fn.TypeParams |> List.map TGen)
                && args.Length = fn.Params.Length
                && (
                    match args[pIdx] with
                    | EVar pv -> pv.Id = q.Id
                    | _ -> false
                )
                && (args |> List.indexed |> List.forall (fun (j, a) -> j = pIdx || check a))
            | ECall(g, _, args, _) ->
                let matchFlags (gFlags: bool list) =
                    args.Length = gFlags.Length
                    && (args
                        |> List.indexed
                        |> List.forall (fun (j, a) ->
                            match a with
                            | EVar pv when pv.Id = q.Id -> gFlags[j]
                            | _ -> check a
                        ))

                match p.Fns.TryGetValue g with
                | true, _ -> matchFlags (Array.toList noEscape[g])
                | _ ->
                    match p.Ext g with
                    | Some ff -> matchFlags ff.FnParamsNoEscape
                    | None -> List.forall check args
            | ELet(_, r, b)
            | ESeq(r, b)
            | EWhile(r, b)
            | EStore(r, b) -> check r && check b
            | EIf(c, t, f, _) -> check c && check t && check f
            | EFor(_, a, b, _, bd) -> check a && check b && check bd
            | EAssign(_, r) -> check r
            | ERaise(x, _) -> check x
            | ETry(b, _, h, _) -> check b && check h
            | EDrop(_, k)
            | EUnpack(_, k)
            | EPromote(_, k) -> check k
            | _ -> flatKids e |> List.forall check

        check fn.Body

    let mutable changed = true

    while changed do
        changed <- false

        for fn in fns do
            let flags = noEscape[fn.Name]

            fn.Params
            |> List.iteri (fun idx q ->
                if flags[idx] && not (paramOk fn idx q) then
                    flags[idx] <- false
                    changed <- true
            )

    for fn in fns do
        fn.NoEscape <- Array.toList noEscape[fn.Name]

/// Rewrite calls to intra-file and eligible cross-file HOFs when given a known closure in a
/// parameter position, passing a stack-allocated `EKnown` struct instead of a heap closure.
let private specializeCallKHofs (p: P) : unit =
    let userAliases = HashSet<string>(p.State.UserImports.Values)
    let importAliases = HashSet<string>(p.State.Imports.Values)

    let canSpecializeTarget (target: string) =
        if p.Fns.ContainsKey target then
            true
        else
            match target.IndexOf '.' with
            | -1 -> false
            | i -> not (userAliases.Contains(target.Substring(0, i)))

    let rec rw (env: Map<int, string * Ty list * Expr list * Ty>) (e: Expr) : Expr =
        let go = rw env

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            ELet(v, r', rw env' b)
        | ESeq(a, b) -> ESeq(go a, go b)
        | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
        | EWhile(c, b) -> EWhile(go c, go b)
        | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
        | EAssign(v, r) -> EAssign(v, go r)
        | EStore(lv, r) -> EStore(go lv, go r)
        | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
        | ERaise(x, ty) -> ERaise(go x, ty)
        | _ ->
            let e' =
                match flatKids e with
                | [] -> e
                | ks -> withFlatKids e (List.map go ks)

            match e' with
            | ECall(calleeName, callTypeArgs, callArgs, callRetTy) ->
                let tryWrapArgs (flagsOpt: bool list option) =
                    match flagsOpt with
                    | Some flags when flags.Length = callArgs.Length && List.exists id flags ->
                        let mutable anyKnown = false

                        let callArgs' =
                            List.zip flags callArgs
                            |> List.map (fun (noEsc, a) ->
                                if noEsc then
                                    match resolveKnownClosure env a with
                                    | Some(target, cTypeArgs, caps, cloTy) when canSpecializeTarget target ->
                                        anyKnown <- true
                                        EKnown(target, cTypeArgs, caps, cloTy)
                                    | _ -> a
                                else
                                    a
                            )

                        if anyKnown then
                            Some(ECall(calleeName, callTypeArgs, callArgs', callRetTy))
                        else
                            None
                    | _ -> None

                match p.Fns.TryGetValue calleeName with
                | true, callee -> tryWrapArgs (Some callee.NoEscape) |> Option.defaultValue e'
                | false, _ when
                    (let dot = calleeName.IndexOf '.'

                     dot > 0
                     && importAliases.Contains(calleeName.Substring(0, dot))
                     && not (userAliases.Contains(calleeName.Substring(0, dot))))
                    ->
                    match p.Ext calleeName with
                    | Some ff -> tryWrapArgs (Some ff.FnParamsNoEscape) |> Option.defaultValue e'
                    | None ->
                        let flags =
                            callArgs
                            |> List.map (fun a ->
                                match typeOf a with
                                | TFn _ -> true
                                | _ -> false
                            )

                        tryWrapArgs (Some flags) |> Option.defaultValue e'
                | _ -> e'
            | _ -> e'

    for fn in p.State.Fns do
        fn.Body <- fn.Body |> rw Map.empty |> dropDeadClosures |> cleanup

/// Mark functions that need a full chaining `$tc` entry (`NeedsChain = true`): functions whose
/// tail calls can reach an unknown callee (`ECallClo`, `ECallVt`, `ECallIface`) or an unfused
/// intra-file tail cycle. Excludes entries/hooks/arenas/stackalloc/byref frames.
let private inferNeedsChain (p: P) (hooks: HashSet<string>) : unit =
    let state = p.State
    let exportSet = state.Exports |> Seq.map fst |> HashSet
    let testSet = state.Tests |> Seq.map snd |> HashSet
    let valueSet = state.Values |> Seq.map (fun (_, _, n) -> n) |> HashSet

    let usesLocalStackPtr (e: Expr) =
        exists
            (function
            | EAddr(_, false) -> true
            | EEmit(m, _, _)
            | ERt(m, _, _) -> m.StartsWith("fable_stack.alloc(", System.StringComparison.Ordinal)
            | _ -> false)
            e

    let isExcluded (fn: FnInfo) =
        fn.IsEntryPoint
        || hooks.Contains fn.Name
        || state.Arenas.ContainsKey fn.Name
        || state.NoTailCallsFile
        || state.NoTailCalls.Contains fn.Name
        || exportSet.Contains fn.Name
        || testSet.Contains fn.Name
        || valueSet.Contains fn.Name
        || usesLocalStackPtr fn.Body

    let rec tailExprs (e: Expr) : Expr list =
        match e with
        | ELet(_, rhs, _) when alwaysRaisesExpr rhs -> []
        | ELet(v, rhs, EVar v2) when v.Id = v2.Id -> tailExprs rhs
        | ELet(r, callRhs, conBody) when not (alwaysRaisesExpr callRhs) ->
            match tryMatchTrmcHole r conBody with
            | Some _ -> tailExprs callRhs
            | None -> tailExprs conBody
        | ELet(_, _, b)
        | ESeq(_, b)
        | EDrop(_, b)
        | EUnpack(_, b)
        | EPromote(_, b) -> tailExprs b
        | EIf(_, t, f, _) -> tailExprs t @ tailExprs f
        | ETry _ -> []
        | _ -> [ e ]

    let unwrapTail = unwrapTailCallExpr

    let rec isScalarTy (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    let fns = state.Fns
    let fableAliases = HashSet<string>(state.Imports.Values)

    for fn in fns do
        fn.NeedsChain <- false
        fn.PendingChainDeps <- []

    let excluded =
        fns |> Seq.filter isExcluded |> Seq.map (fun fn -> fn.Name) |> HashSet

    let sameFileEdges = Dictionary<string, (string * Ty list * int) list>()
    let pendingExt = Dictionary<string, HashSet<string>>()

    for fn in fns do
        let pSet = HashSet<string>()
        pendingExt[fn.Name] <- pSet

        if not (excluded.Contains fn.Name) then
            let edges = List<string * Ty list * int>()

            for rawT in tailExprs fn.Body do
                match unwrapTail rawT with
                | ECallClo _
                | ECallVt _
                | ECallIface _ -> fn.NeedsChain <- true
                | ECall(g, tArgs, args, _) when p.Fns.ContainsKey g && not (excluded.Contains g) ->
                    if g = fn.Name then
                        if tArgs <> (fn.TypeParams |> List.map TGen) || args.Length <> fn.Params.Length then
                            // Polymorphic or arity-mismatched self recursion cannot loop in place.
                            fn.NeedsChain <- true
                    else
                        edges.Add(g, tArgs, args.Length)
                | ECall(extF, _, _, _) when not (p.Fns.ContainsKey extF) ->
                    let dot = extF.IndexOf '.'

                    if dot > 0 && fableAliases.Contains(extF.Substring(0, dot)) then
                        match p.Ext extF with
                        | Some ff ->
                            if ff.NeedsChain then
                                fn.NeedsChain <- true
                        | None -> pSet.Add extF |> ignore
                | _ -> ()

            sameFileEdges[fn.Name] <- List.ofSeq edges
        else
            sameFileEdges[fn.Name] <- []

    // Find all non-self strongly connected components in `sameFileEdges` (even with mismatched
    // signatures/type args) and check whether `Emit`'s `emitScc` or scalar sibling `tailTarget`
    // already fuses each SCC into O(1) stack.
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

            for (w, _, _) in sameFileEdges[v] do
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
                    comp.Add p.Fns[w]

                    if w = v then
                        stop <- true

                if comp.Count >= 2 then
                    sccs.Add(List.ofSeq comp)

        for fn in fns do
            if not (excluded.Contains fn.Name) && not (indexOf.ContainsKey fn.Name) then
                strongconnect fn.Name

    let mayHaveReuseToken (fn: FnInfo) =
        exists
            (function
            | ETest(_, _, ty) -> isHeapTy ty
            | _ -> false)
            fn.Body

    let fusedSccs = List<FnInfo list>()

    for scc in sccs do
        let rep = scc.Head
        let repRet = zigType rep.Ret
        let memberNames = scc |> List.map (fun fn -> fn.Name) |> Set.ofList

        let allEdgesDirect =
            scc
            |> List.forall (fun fn ->
                let expectedTArgs = fn.TypeParams |> List.map TGen

                sameFileEdges[fn.Name]
                |> List.forall (fun (g, tArgs, nArgs) ->
                    not (memberNames.Contains g)
                    || (tArgs = expectedTArgs && nArgs = p.Fns[g].Params.Length)
                )
            )

        let allScalarSameSig =
            allEdgesDirect
            && rep.Raises = RNever
            && (scc
                |> List.forall (fun fn ->
                    (fn.Ret :: (fn.Params |> List.map (fun q -> q.Ty))) |> List.forall isScalarTy
                    && (fn.Params |> List.map (fun q -> zigType q.Ty)) =
                        (rep.Params |> List.map (fun q -> zigType q.Ty))
                ))

        let fusedScc =
            allEdgesDirect
            && not allScalarSameSig
            && (scc
                |> List.forall (fun fn ->
                    not (state.Arenas.ContainsKey fn.Name)
                    && fn.RetFrom.IsNone
                    && fn.TypeParams = rep.TypeParams
                    && zigType fn.Ret = repRet
                    && fn.Raises = rep.Raises
                ))

        let fusedScalar =
            allScalarSameSig && (scc |> List.forall (fun fn -> not (mayHaveReuseToken fn)))

        if fusedScc then
            fusedSccs.Add scc
        elif not fusedScalar then
            for fn in scc do
                fn.NeedsChain <- true

    let mutable changed = true

    while changed do
        changed <- false

        for fn in fns do
            if not (excluded.Contains fn.Name) && not fn.NeedsChain then
                let hitsChain =
                    sameFileEdges[fn.Name] |> List.exists (fun (g, _, _) -> p.Fns[g].NeedsChain)

                if hitsChain then
                    fn.NeedsChain <- true
                    changed <- true

        for scc in fusedSccs do
            if scc |> List.exists (fun m -> m.NeedsChain) then
                for m in scc do
                    if not m.NeedsChain && not (excluded.Contains m.Name) then
                        m.NeedsChain <- true
                        changed <- true

    for fn in fns do
        if excluded.Contains fn.Name || fn.NeedsChain then
            pendingExt[fn.Name].Clear()

    let mutable pendingChanged = true

    while pendingChanged do
        pendingChanged <- false

        for fn in fns do
            if not (excluded.Contains fn.Name) && not fn.NeedsChain then
                let dst = pendingExt[fn.Name]

                for (g, _, _) in sameFileEdges[fn.Name] do
                    for extF in pendingExt[g] do
                        if dst.Add extF then
                            pendingChanged <- true

        for scc in fusedSccs do
            if scc |> List.forall (fun m -> not m.NeedsChain && not (excluded.Contains m.Name)) then
                for m in scc do
                    let dst = pendingExt[m.Name]

                    for other in scc do
                        if other.Name <> m.Name then
                            for extF in pendingExt[other.Name] do
                                if dst.Add extF then
                                    pendingChanged <- true

    for fn in fns do
        if not fn.NeedsChain && pendingExt[fn.Name].Count > 0 then
            fn.PendingChainDeps <- pendingExt[fn.Name] |> Seq.sort |> Seq.toList

/// Snapshot and prepared local state before awaiting cross-file facts.
type LocalPrepared =
    {
        State: FileState
        Hooks: HashSet<string>
        SnapshotFns: Map<string, FnInfo>
        SnapshotCurried2: Map<string, string>
    }

/// Context needed for Tier 2 cross-file `HofUnit` cloning.
type Tier2Context =
    {
        CallerZigPath: string
        ImportTargets: Facts.ImportTarget list
        ImportFacts: Map<string, Facts.FileFacts>
        ResolveLibPath: string -> string
        LookupCachedFacts: string option -> string -> Facts.FileFacts option
    }

let private emitIdentRx =
    System.Text.RegularExpressions.Regex(
        @"(?<![\w.$@])(@""[^""]+""|[A-Za-z_][A-Za-z0-9_]*)",
        System.Text.RegularExpressions.RegexOptions.Compiled
    )

/// Deterministic cycle-safe SHA-256 digest over a `HofUnit`'s bodies, signatures, `NoEscape`, and imports.
let private computeHofUnitHash
    (unitName: string)
    (noEscape: bool list)
    (unitFns: FnInfo list)
    (unitCurried2: (string * string) list)
    (unitImports: Facts.HofImport list)
    : string
    =
    let sb = System.Text.StringBuilder()
    let seenEnts = HashSet<string>()
    let extraDefs = System.Collections.Generic.List<Ent>()

    let rec writeTy (t: Ty) =
        match t with
        | TPrim s -> sb.Append("P(").Append(s).Append(')') |> ignore
        | TGen n -> sb.Append("G(").Append(n).Append(')') |> ignore
        | TOpt x ->
            sb.Append("O(") |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TTuple ts ->
            sb.Append("T(") |> ignore

            ts
            |> List.iteri (fun i x ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy x
            )

            sb.Append(')') |> ignore
        | TPtr(x, c) ->
            sb.Append("Ptr(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TSlice(x, c) ->
            sb.Append("Slc(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TArr(x, n) ->
            sb.Append("Arr(").Append(n).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TFn(ps, r) ->
            sb.Append("Fn(") |> ignore

            ps
            |> List.iteri (fun i p ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy p
            )

            sb.Append("->") |> ignore
            writeTy r
            sb.Append(')') |> ignore
        | TSlot(ps, r) ->
            sb.Append("Slot(") |> ignore

            ps
            |> List.iteri (fun i p ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy p
            )

            sb.Append("->") |> ignore
            writeTy r
            sb.Append(')') |> ignore
        | TTok(x, c) ->
            sb.Append("Tok(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TEnt(e, args) ->
            if seenEnts.Add(e.Ref.FullName + "|" + e.Name) && e.IsLocal then
                extraDefs.Add e

            sb
                .Append("Ent(")
                .Append(e.Ref.FullName)
                .Append('|')
                .Append(e.Name)
                .Append('|')
                .Append(string e.Kind)
                .Append('|')
                .Append(e.IsLocal)
                .Append('[')
            |> ignore

            args
            |> List.iteri (fun i a ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy a
            )

            sb.Append("])") |> ignore

    let writeVar (v: Var) =
        sb
            .Append("V(")
            .Append(v.Id)
            .Append(',')
            .Append(v.Base)
            .Append(',')
            .Append(string v.Kind)
            .Append(',')
            .Append(v.FMutable)
            .Append(',')
        |> ignore

        writeTy v.Ty
        sb.Append(')') |> ignore

    let rec writeExpr (e: Expr) =
        match e with
        | EVar v -> writeVar v
        | ELit(s, t) ->
            sb.Append("Lit(").Append(s).Append(',') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EUnit -> sb.Append("Unit") |> ignore
        | EPrim(op, xs, t) ->
            sb.Append("Prim(").Append(op).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("],") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECall(f, tys, xs, t) ->
            sb.Append("Call(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECallClo(f, xs, t) ->
            sb.Append("CallClo(") |> ignore
            writeExpr f
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECallVt(f, s, xs, t) ->
            sb.Append("CallVt(") |> ignore
            writeExpr f
            sb.Append(',') |> ignore
            writeExpr s
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EClosure(f, tys, xs, t) ->
            sb.Append("Clo(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EKnown(f, tys, xs, t) ->
            sb.Append("Known(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EUse(u, x) ->
            sb.Append("Use(").Append(string u).Append(',') |> ignore
            writeExpr x
            sb.Append(')') |> ignore
        | EAssumedRet(js, c) ->
            sb.Append("Assumed(") |> ignore

            for j in js do
                sb.Append(j).Append(';') |> ignore

            writeExpr c
            sb.Append(')') |> ignore
        | EIface _ -> sb.Append("Iface") |> ignore
        | ECallIface(r, slot, xs, t) ->
            sb.Append("CallIface(").Append(slot).Append(',') |> ignore
            writeExpr r
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECon(t, c, xs, tok) ->
            sb.Append("Con(").Append(c).Append(',') |> ignore
            writeTy t
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append(')') |> ignore

            match tok with
            | Some tk -> writeVar tk
            | None -> ()

            sb.Append(')') |> ignore
        | EGet(x, proj, t) ->
            sb.Append("Get(").Append(projKey proj).Append(',') |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ETest(x, c, t) ->
            sb.Append("Test(").Append(c).Append(',') |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EAddr(x, c) ->
            sb.Append("Addr(").Append(c).Append(',') |> ignore
            writeExpr x
            sb.Append(')') |> ignore
        | EDeref(x, t) ->
            sb.Append("Deref(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EIndex(a, b, t) ->
            sb.Append("Idx(") |> ignore
            writeExpr a
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EEmit(m, xs, t) ->
            sb.Append("Emit(").Append(m).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("]:") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ERt(m, xs, t) ->
            sb.Append("Rt(").Append(m).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("]:") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EExnNew(ent, xs) ->
            sb.Append("ExnNew(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append('[')
            |> ignore

            List.iter writeExpr xs
            sb.Append("])") |> ignore
        | EExnTest(x, ent) ->
            sb.Append("ExnTest(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append(',')
            |> ignore

            writeExpr x
            sb.Append(')') |> ignore
        | EExnGet(x, ent, f, t) ->
            sb.Append("ExnGet(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append('.').Append(f).Append(',')
            |> ignore

            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EOnRaise(x, ds) ->
            sb.Append("OnRaise(") |> ignore
            writeExpr x
            sb.Append('[') |> ignore
            List.iter writeVar ds
            sb.Append("])") |> ignore
        | EDup(x, t) ->
            sb.Append("Dup(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ELet(v, r, b) ->
            sb.Append("Let(") |> ignore
            writeVar v
            sb.Append('=') |> ignore
            writeExpr r
            sb.Append(" in ") |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | ESeq(a, b) ->
            sb.Append("Seq(") |> ignore
            writeExpr a
            sb.Append(';') |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | EIf(c, t, f, ty) ->
            sb.Append("If(") |> ignore
            writeExpr c
            sb.Append('?') |> ignore
            writeExpr t
            sb.Append(':') |> ignore
            writeExpr f
            sb.Append('#') |> ignore
            writeTy ty
            sb.Append(')') |> ignore
        | EWhile(c, b) ->
            sb.Append("While(") |> ignore
            writeExpr c
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | EFor(i, a, b, up, body) ->
            sb.Append("For(") |> ignore
            writeVar i
            sb.Append(',') |> ignore
            writeExpr a
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(',').Append(up).Append(',') |> ignore
            writeExpr body
            sb.Append(')') |> ignore
        | EAssign(v, r) ->
            sb.Append("Assign(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr r
            sb.Append(')') |> ignore
        | EStore(lv, r) ->
            sb.Append("Store(") |> ignore
            writeExpr lv
            sb.Append(',') |> ignore
            writeExpr r
            sb.Append(')') |> ignore
        | EDrop(v, k) ->
            sb.Append("Drop(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | EUnpack(u, k) ->
            sb.Append("Unpack(").Append(u.Case).Append(',').Append(u.Heap).Append(',')
            |> ignore

            writeVar u.Scrut
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | EPromote(v, k) ->
            sb.Append("Promote(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | ERaise(x, t) ->
            sb.Append("Raise(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ETry(b, v, h, t) ->
            sb.Append("Try(") |> ignore
            writeExpr b
            sb.Append(" catch ") |> ignore
            writeVar v
            sb.Append("=>") |> ignore
            writeExpr h
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore

    sb.Append("unit:").Append(unitName).Append(";ne:") |> ignore

    for b in noEscape do
        sb.Append(
            if b then
                '1'
            else
                '0'
        )
        |> ignore

    sb.Append(";fns:[") |> ignore

    for u in unitFns do
        sb.Append(u.Name).Append('<') |> ignore
        sb.Append(String.concat "," u.TypeParams).Append(">(") |> ignore

        for param in u.Params do
            writeVar param
            sb.Append(',') |> ignore

        sb.Append(")->") |> ignore
        writeTy u.Ret
        sb.Append('=') |> ignore
        writeExpr u.Body
        sb.Append(';') |> ignore

    sb.Append("];c2:[") |> ignore

    for (a, b) in List.sort unitCurried2 do
        sb.Append(a).Append("->").Append(b).Append(';') |> ignore

    sb.Append("];imp:[") |> ignore

    for imp in unitImports |> List.sortBy (fun i -> i.CalleeAlias, i.ZigPath) do
        sb.Append(imp.CalleeAlias).Append('=').Append(imp.ZigPath).Append(';') |> ignore

    sb.Append("];ents:[") |> ignore

    let mutable idx = 0

    while idx < extraDefs.Count do
        let e = extraDefs[idx]
        idx <- idx + 1

        sb
            .Append(e.Name)
            .Append('|')
            .Append(string e.Kind)
            .Append('|')
            .Append(e.Managed)
            .Append('|')
            .Append(e.Cyclic)
            .Append('|')
            .Append(String.concat "," e.MutableFields)
            .Append('{')
        |> ignore

        for (cName, fields) in e.Cases do
            sb.Append(cName).Append(':') |> ignore

            for (fName, fTy) in fields do
                sb.Append(fName).Append('=') |> ignore
                writeTy fTy
                sb.Append(';') |> ignore

        sb.Append("};") |> ignore

    sb.Append(']') |> ignore

    let bytes = System.Text.Encoding.UTF8.GetBytes(sb.ToString())
    use sha = System.Security.Cryptography.SHA256.Create()
    let digest = sha.ComputeHash(bytes)
    System.BitConverter.ToString(digest).Replace("-", "").ToLowerInvariant()

/// Build exportable Tier 2 `HofUnit` snapshots for eligible public HOFs (non-escaping fn params,
/// total pre-specialization size <= 250, no local-only entities/globals/emits/ifaces/arenas/hooks).
let private exportHofUnits (prep: LocalPrepared) (p: P) (tier2Opt: Tier2Context option) : Map<string, Facts.HofUnit> =
    let state = prep.State
    let hooks = prep.Hooks

    let calleeZigPath =
        tier2Opt |> Option.map (fun t -> t.CallerZigPath) |> Option.defaultValue ""

    let targetByAlias =
        match tier2Opt with
        | Some t -> t.ImportTargets |> List.map (fun tgt -> tgt.Alias, tgt) |> Map.ofList
        | None -> Map.empty

    let rawKeyByAlias =
        state.Imports |> Seq.map (fun kv -> kv.Value, kv.Key) |> Map.ofSeq

    let userAliases = HashSet<string>(state.UserImports.Values)
    let pubLocalEntNames = state.LocalEnts |> Seq.map (fun e -> e.Name) |> HashSet
    let pubGlobals = HashSet<string>()

    for (n, _, _) in state.Consts do
        pubGlobals.Add n |> ignore

    for (n, _, _) in state.Values do
        pubGlobals.Add n |> ignore

    let localFileSymbols = HashSet<string>()

    let addSym (s: string) =
        if not (System.String.IsNullOrEmpty s) then
            localFileSymbols.Add s |> ignore
            localFileSymbols.Add(cleanIdent s) |> ignore
            localFileSymbols.Add(topIdent s) |> ignore

    for fn in state.Fns do
        addSym fn.Name

    for kv in prep.SnapshotFns do
        addSym kv.Key

    for (n, _, _) in state.Consts do
        addSym n

    for (n, _, _) in state.Values do
        addSym n

    for e in state.LocalEnts do
        addSym e.Name

    for o in state.Objs do
        addSym o.TypeName

        match o.Chain with
        | TEnt(e, _) -> addSym e.Name
        | _ -> ()

        for (thName, _, _, _, _) in o.Thunks do
            addSym thName

    for a in state.Imports.Values do
        addSym a

    for a in state.UserImports.Values do
        addSym a

    localFileSymbols.Remove "fable_rt" |> ignore
    localFileSymbols.Remove "std" |> ignore

    let result = Dictionary<string, Facts.HofUnit>()

    for fn in state.Fns do
        if
            not fn.IsLocal
            && not fn.IsEntryPoint
            && not (hooks.Contains fn.Name)
            && List.exists id fn.NoEscape
        then
            match prep.SnapshotFns.TryFind fn.Name with
            | None -> ()
            | Some topSnap ->
                let reachable = System.Collections.Generic.List<FnInfo>()
                let seenFns = HashSet<string>()
                let work = Queue<FnInfo>()
                let mutable bfsOk = true

                seenFns.Add fn.Name |> ignore
                work.Enqueue topSnap

                while bfsOk && work.Count > 0 do
                    let cur = work.Dequeue()
                    reachable.Add cur

                    let tryEnqueue (target: string) =
                        if bfsOk && not (target.Contains ".") && not (seenFns.Contains target) then
                            match prep.SnapshotFns.TryFind target with
                            | Some g when g.IsLocal ->
                                seenFns.Add target |> ignore
                                work.Enqueue g
                            | Some _ -> ()
                            | None -> bfsOk <- false

                    exists
                        (fun x ->
                            match x with
                            | ECall(g, _, _, _) -> tryEnqueue g
                            | EClosure(g, _, _, ty)
                            | EKnown(g, _, _, ty) ->
                                tryEnqueue g

                                match ty with
                                | TFn([ _ ], TFn([ _ ], _)) ->
                                    match prep.SnapshotCurried2.TryFind g with
                                    | Some g2 -> tryEnqueue g2
                                    | None -> ()
                                | _ -> ()
                            | _ -> ()

                            false
                        )
                        cur.Body
                    |> ignore

                let unitFns = List.ofSeq reachable

                if bfsOk && (unitFns |> List.sumBy (fun u -> exprSize u.Body)) <= 250 then
                    let mutable ok = true
                    let usedImports = Dictionary<string, Facts.HofImport>()
                    let extraEnts = Dictionary<string, Ent>()
                    let checkedEnts = HashSet<string>()

                    let recordImportAlias (alias: string) =
                        if userAliases.Contains alias then
                            ok <- false
                        elif not (usedImports.ContainsKey alias) then
                            match targetByAlias.TryFind alias, rawKeyByAlias.TryFind alias with
                            | Some tgt, Some rawKey ->
                                usedImports[alias] <-
                                    {
                                        CalleeAlias = alias
                                        ZigPath = tgt.ZigPath
                                        FsPath = tgt.FsPath
                                        RawKey = rawKey
                                    }
                            | _ -> ok <- false

                    let rec checkEntAndTy (t: Ty) =
                        if ok then
                            match t with
                            | TPrim _
                            | TGen _ -> ()
                            | TOpt x
                            | TPtr(x, _)
                            | TSlice(x, _)
                            | TArr(x, _)
                            | TTok(x, _) -> checkEntAndTy x
                            | TTuple xs -> List.iter checkEntAndTy xs
                            | TFn(ps, r)
                            | TSlot(ps, r) ->
                                List.iter checkEntAndTy ps
                                checkEntAndTy r
                            | TEnt(ent, args) ->
                                checkEnt ent
                                List.iter checkEntAndTy args

                    and checkEnt (ent: Ent) =
                        if ok then
                            let ek = ent.Ref.FullName + "|" + ent.Name

                            if ent.IsLocal then
                                if not (pubLocalEntNames.Contains ent.Name) then
                                    ok <- false
                                elif checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            elif
                                ent.Ref.FullName.StartsWith("$anon:", System.StringComparison.Ordinal)
                                || ent.Ref.FullName.StartsWith("$iface:", System.StringComparison.Ordinal)
                            then
                                extraEnts[ent.Ref.FullName] <- ent

                                if checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            elif ent.Name.StartsWith("fable_rt.", System.StringComparison.Ordinal) then
                                if checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            else
                                match ent.Name.IndexOf '.' with
                                | dot when dot > 0 ->
                                    recordImportAlias (ent.Name.Substring(0, dot))

                                    if ok && checkedEnts.Add ek then
                                        for (_, fs) in ent.Cases do
                                            for (_, fTy) in fs do
                                                checkEntAndTy fTy
                                | _ -> ok <- false

                    let checkTargetFn (f: string) =
                        if ok then
                            match f.IndexOf '.' with
                            | -1 ->
                                if not (seenFns.Contains f) then
                                    match prep.SnapshotFns.TryFind f with
                                    | Some g when not g.IsLocal && not g.IsEntryPoint && not (hooks.Contains g.Name) ->
                                        ()
                                    | _ -> ok <- false
                            | dot -> recordImportAlias (f.Substring(0, dot))

                    let checkEmitMacro (macro: string) =
                        if macro.Contains "@This" then
                            ok <- false
                        else
                            for m in emitIdentRx.Matches macro do
                                let raw = m.Groups.[1].Value

                                let unquoted =
                                    if raw.StartsWith("@\"", System.StringComparison.Ordinal) && raw.Length >= 3 then
                                        raw.Substring(2, raw.Length - 3)
                                    else
                                        raw

                                if localFileSymbols.Contains raw || localFileSymbols.Contains unquoted then
                                    ok <- false

                    let checkGlobalVar (v: Var) =
                        checkEntAndTy v.Ty

                        if not (v.Base.Contains ".") then
                            if not (pubGlobals.Contains v.Base) then
                                ok <- false
                        else
                            let dot = v.Base.IndexOf '.'
                            let alias = v.Base.Substring(0, dot)

                            if alias <> "fable_rt" && alias <> "std" then
                                recordImportAlias alias

                    let rec walkExpr (e: Expr) =
                        if ok then
                            match e with
                            | EVar v ->
                                if v.Kind = VGlobal then
                                    checkGlobalVar v
                                else
                                    checkEntAndTy v.Ty
                            | ELit(_, t)
                            | ERaise(_, t) ->
                                checkEntAndTy t

                                match e with
                                | ERaise(x, _) -> walkExpr x
                                | _ -> ()
                            | EUnit -> ()
                            | EPrim(_, xs, t) ->
                                checkEntAndTy t
                                List.iter walkExpr xs
                            | ECall(f, tys, xs, t) ->
                                checkTargetFn f
                                List.iter checkEntAndTy tys
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECallClo(f, xs, t) ->
                                walkExpr f
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECallVt(f, s, xs, t) ->
                                walkExpr f
                                walkExpr s
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EClosure(f, tys, xs, t)
                            | EKnown(f, tys, xs, t) ->
                                checkTargetFn f
                                List.iter checkEntAndTy tys
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EUse(_, x)
                            | EAssumedRet(_, x) -> walkExpr x
                            | EIface _ -> ok <- false
                            | ECallIface(r, _, xs, t) ->
                                walkExpr r
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECon(t, _, xs, tok) ->
                                checkEntAndTy t
                                List.iter walkExpr xs

                                match tok with
                                | Some tk -> checkEntAndTy tk.Ty
                                | None -> ()
                            | EGet(x, _, t)
                            | ETest(x, _, t)
                            | EDeref(x, t)
                            | EDup(x, t) ->
                                walkExpr x
                                checkEntAndTy t
                            | EAddr(x, _) -> walkExpr x
                            | EIndex(a, b, t) ->
                                walkExpr a
                                walkExpr b
                                checkEntAndTy t
                            | EEmit(m, xs, t) ->
                                checkEmitMacro m
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ERt(_, xs, t) ->
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EExnNew(ent, xs) ->
                                checkEnt ent
                                List.iter walkExpr xs
                            | EExnTest(x, ent) ->
                                checkEnt ent
                                walkExpr x
                            | EExnGet(x, ent, _, t) ->
                                checkEnt ent
                                walkExpr x
                                checkEntAndTy t
                            | EOnRaise(x, ds) ->
                                walkExpr x

                                for d in ds do
                                    checkEntAndTy d.Ty
                            | ELet(v, r, b) ->
                                checkEntAndTy v.Ty
                                walkExpr r
                                walkExpr b
                            | ESeq(a, b)
                            | EWhile(a, b)
                            | EStore(a, b) ->
                                walkExpr a
                                walkExpr b
                            | EIf(c, t, f, ty) ->
                                walkExpr c
                                walkExpr t
                                walkExpr f
                                checkEntAndTy ty
                            | EFor(v, a, b, _, body) ->
                                checkEntAndTy v.Ty
                                walkExpr a
                                walkExpr b
                                walkExpr body
                            | EAssign(v, r) ->
                                if v.Kind = VGlobal then
                                    checkGlobalVar v
                                else
                                    checkEntAndTy v.Ty

                                walkExpr r
                            | EDrop(v, k)
                            | EPromote(v, k) ->
                                checkEntAndTy v.Ty
                                walkExpr k
                            | EUnpack(u, k) ->
                                checkEntAndTy u.Scrut.Ty

                                for (_, mv) in u.Moves do
                                    checkEntAndTy mv.Ty

                                for (_, dt) in u.Drops do
                                    checkEntAndTy dt

                                walkExpr k
                            | ETry(b, v, h, t) ->
                                checkEntAndTy v.Ty
                                checkEntAndTy t
                                walkExpr b
                                walkExpr h

                    for uFn in unitFns do
                        if
                            not ok
                            || uFn.IsEntryPoint
                            || hooks.Contains uFn.Name
                            || state.Arenas.ContainsKey uFn.Name
                        then
                            ok <- false
                        else
                            for param in uFn.Params do
                                checkEntAndTy param.Ty

                            checkEntAndTy uFn.Ret
                            walkExpr uFn.Body

                    if ok then
                        let unitCurried2 =
                            prep.SnapshotCurried2
                            |> Seq.choose (fun kv ->
                                if seenFns.Contains kv.Key && seenFns.Contains kv.Value then
                                    Some(kv.Key, kv.Value)
                                else
                                    None
                            )
                            |> Seq.sort
                            |> List.ofSeq

                        let unitImports =
                            usedImports.Values |> Seq.sortBy (fun i -> i.CalleeAlias) |> List.ofSeq

                        let unitExtraEnts =
                            extraEnts
                            |> Seq.map (fun kv -> kv.Key, kv.Value)
                            |> Seq.sortBy fst
                            |> List.ofSeq

                        let unitHash =
                            computeHofUnitHash fn.Name fn.NoEscape unitFns unitCurried2 unitImports

                        result[fn.Name] <-
                            {
                                Name = fn.Name
                                Hash = unitHash
                                CalleeZigPath = calleeZigPath
                                Fns = unitFns
                                Curried2 = unitCurried2
                                Imports = unitImports
                                ExtraEnts = unitExtraEnts
                            }

    result |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

/// Clone eligible imported `HofUnit`s into the caller when a call site passes at least one
/// known caller closure to a non-escaping parameter, then run `specializeHofs` to fold them.
let private importTier2Hofs
    (state: FileState)
    (hooks: HashSet<string>)
    (tier2: Tier2Context)
    : string list * Map<string, Facts.FileFacts>
    =
    let zigPathToAlias = Dictionary<string, string>()

    for tgt in tier2.ImportTargets do
        zigPathToAlias[tgt.ZigPath] <- tgt.Alias

    let usedAliases =
        HashSet<string>(Seq.append state.Imports.Values state.UserImports.Values)

    let usedTopNames = HashSet<string>()

    for fn in state.Fns do
        usedTopNames.Add fn.Name |> ignore

    for (n, _, _) in state.Values do
        usedTopNames.Add n |> ignore

    for (n, _, _) in state.Consts do
        usedTopNames.Add n |> ignore

    for e in state.LocalEnts do
        usedTopNames.Add e.Name |> ignore

    let callerFnNames = HashSet<string>(state.Fns |> Seq.map (fun fn -> fn.Name))
    let extraFacts = Dictionary<string, Facts.FileFacts>()
    let addedFsImports = List<string>()

    let freshAlias (hint: string) =
        let baseName = "m_" + cleanIdent hint
        let mutable cand = baseName
        let mutable i = 1

        while usedAliases.Contains cand do
            cand <- $"%s{baseName}_%d{i}"
            i <- i + 1

        usedAliases.Add cand |> ignore
        cand

    let freshUnitFnName (prefix: string) =
        let mutable i = 0
        let mutable cand = $"%s{prefix}_%d{i}"

        while usedTopNames.Contains cand do
            i <- i + 1
            cand <- $"%s{prefix}_%d{i}"

        usedTopNames.Add cand |> ignore
        cand

    let ensureImport (imp: Facts.HofImport) : string =
        match zigPathToAlias.TryGetValue imp.ZigPath with
        | true, existing -> existing
        | _ ->
            let rawKey =
                match imp.FsPath with
                | Some fsPath ->
                    addedFsImports.Add fsPath
                    fsPath
                | None ->
                    let modName = System.IO.Path.GetFileNameWithoutExtension imp.ZigPath
                    tier2.ResolveLibPath modName

            let alias =
                match state.Imports.TryGetValue rawKey with
                | true, existing -> existing
                | _ ->
                    let a = freshAlias (System.IO.Path.GetFileNameWithoutExtension imp.ZigPath)
                    state.Imports[rawKey] <- a
                    a

            zigPathToAlias[imp.ZigPath] <- alias

            match tier2.LookupCachedFacts imp.FsPath imp.ZigPath with
            | Some ff -> extraFacts[alias] <- ff
            | None -> ()

            alias

    let clonedUnits = Dictionary<string, string>()

    let cloneUnit (calleeAlias: string) (unit: Facts.HofUnit) : string =
        let memoKey = calleeAlias + ":" + unit.Name

        match clonedUnits.TryGetValue memoKey with
        | true, topName -> topName
        | _ ->
            let impAliasMap =
                unit.Imports
                |> List.map (fun imp -> imp.CalleeAlias, ensureImport imp)
                |> Map.ofList

            let remappedEnts = Dictionary<string, Ent>()
            let entKey (e: Ent) = e.Ref.FullName + "|" + e.Name

            let rec remapEnt (ent: Ent) : Ent =
                let k = entKey ent

                match remappedEnts.TryGetValue k with
                | true, existing -> existing
                | _ ->
                    match state.Ents.TryGetValue ent.Ref.FullName with
                    | true, existing ->
                        remappedEnts[k] <- existing
                        existing
                    | _ ->
                        let newName, newHooks =
                            if ent.IsLocal then
                                let h =
                                    ent.Hooks
                                    |> Option.map (fun (d, dup) ->
                                        let q (s: string) =
                                            if s.Contains "." then
                                                s
                                            else
                                                calleeAlias + "." + s

                                        q d, Option.map q dup
                                    )

                                calleeAlias + "." + ent.Name, h
                            elif ent.Name.StartsWith("fable_rt.", System.StringComparison.Ordinal) then
                                state.UsesRuntime <- true
                                ent.Name, ent.Hooks
                            elif
                                ent.Ref.FullName.StartsWith("$anon:", System.StringComparison.Ordinal)
                                || ent.Ref.FullName.StartsWith("$iface:", System.StringComparison.Ordinal)
                            then
                                state.UsesRuntime <- true
                                ent.Name, ent.Hooks
                            else
                                match ent.Name.IndexOf '.' with
                                | -1 -> calleeAlias + "." + ent.Name, ent.Hooks
                                | dot ->
                                    let oldAlias = ent.Name.Substring(0, dot)
                                    let rest = ent.Name.Substring(dot + 1)

                                    let newAlias = impAliasMap.TryFind oldAlias |> Option.defaultValue oldAlias

                                    newAlias + "." + rest, ent.Hooks

                        let e' =
                            { ent with
                                Name = newName
                                IsLocal = false
                                Cases = []
                                Hooks = newHooks
                                Overrides = []
                            }

                        remappedEnts[k] <- e'

                        e'.Cases <-
                            ent.Cases
                            |> List.map (fun (cName, fields) ->
                                cName, fields |> List.map (fun (fName, fTy) -> fName, remapTy fTy)
                            )

                        e'

            and remapTy (t: Ty) : Ty =
                match t with
                | TPrim _
                | TGen _ -> t
                | TOpt x -> TOpt(remapTy x)
                | TTuple xs -> TTuple(List.map remapTy xs)
                | TPtr(x, c) -> TPtr(remapTy x, c)
                | TSlice(x, c) -> TSlice(remapTy x, c)
                | TArr(x, n) -> TArr(remapTy x, n)
                | TFn(ps, r) -> TFn(List.map remapTy ps, remapTy r)
                | TSlot(ps, r) -> TSlot(List.map remapTy ps, remapTy r)
                | TTok(x, c) -> TTok(remapTy x, c)
                | TEnt(ent, args) -> TEnt(remapEnt ent, List.map remapTy args)

            for (extraKey, extraEnt) in unit.ExtraEnts do
                if not (state.Ents.ContainsKey extraKey) then
                    state.Ents[extraKey] <- remapEnt extraEnt

                state.UsesRuntime <- true

            let fnRename = Dictionary<string, string>()

            for uFn in unit.Fns do
                let cleanCallee = cleanIdent calleeAlias
                let cleanFn = cleanIdent uFn.Name
                fnRename[uFn.Name] <- freshUnitFnName $"%s{cleanCallee}_%s{cleanFn}$t2"

            let remapFnTarget (f: string) : string =
                match fnRename.TryGetValue f with
                | true, r -> r
                | _ ->
                    match f.IndexOf '.' with
                    | -1 -> calleeAlias + "." + f
                    | dot ->
                        let oldAlias = f.Substring(0, dot)
                        let rest = f.Substring(dot + 1)
                        let newAlias = impAliasMap.TryFind oldAlias |> Option.defaultValue oldAlias
                        newAlias + "." + rest

            for (c1, c2) in unit.Curried2 do
                match fnRename.TryGetValue c1, fnRename.TryGetValue c2 with
                | (true, r1), (true, r2) -> state.Curried2[r1] <- r2
                | _ -> ()

            for uFn in unit.Fns do
                let varMap = Dictionary<int, Var>()

                let freshVar (v: Var) =
                    let v' = state.NewVar(v.Base, remapTy v.Ty, v.Kind, v.FMutable)
                    varMap[v.Id] <- v'
                    v'

                let mapVar (v: Var) =
                    if v.Kind = VGlobal then
                        { v with
                            Base = remapFnTarget v.Base
                            Ty = remapTy v.Ty
                        }
                    else
                        match varMap.TryGetValue v.Id with
                        | true, v' -> v'
                        | _ -> v

                let newParams = uFn.Params |> List.map freshVar

                let rec remapExpr (e: Expr) : Expr =
                    match e with
                    | EVar v -> EVar(mapVar v)
                    | ELit(s, t) -> ELit(s, remapTy t)
                    | EUnit -> EUnit
                    | EPrim(op, xs, t) -> EPrim(op, List.map remapExpr xs, remapTy t)
                    | ECall(f, tys, xs, t) ->
                        ECall(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | ECallClo(f, xs, t) -> ECallClo(remapExpr f, List.map remapExpr xs, remapTy t)
                    | ECallVt(f, s, xs, t) -> ECallVt(remapExpr f, remapExpr s, List.map remapExpr xs, remapTy t)
                    | EClosure(f, tys, xs, t) ->
                        EClosure(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | EKnown(f, tys, xs, t) ->
                        EKnown(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | EUse(u, x) -> EUse(u, remapExpr x)
                    | EAssumedRet(js, x) -> EAssumedRet(js, remapExpr x)
                    | EIface(t, src, slots) -> EIface(remapTy t, src, slots)
                    | ECallIface(r, slot, xs, t) -> ECallIface(remapExpr r, slot, List.map remapExpr xs, remapTy t)
                    | ECon(t, c, xs, tok) -> ECon(remapTy t, c, List.map remapExpr xs, Option.map mapVar tok)
                    | EGet(x, p, t) -> EGet(remapExpr x, p, remapTy t)
                    | ETest(x, c, t) -> ETest(remapExpr x, c, remapTy t)
                    | EAddr(x, c) -> EAddr(remapExpr x, c)
                    | EDeref(x, t) -> EDeref(remapExpr x, remapTy t)
                    | EIndex(a, b, t) -> EIndex(remapExpr a, remapExpr b, remapTy t)
                    | EEmit(m, xs, t) ->
                        if m.Contains "fable_rt." then
                            state.UsesRuntime <- true

                        EEmit(m, List.map remapExpr xs, remapTy t)
                    | ERt(m, xs, t) ->
                        state.UsesRuntime <- true
                        ERt(m, List.map remapExpr xs, remapTy t)
                    | EExnNew(ent, xs) -> EExnNew(remapEnt ent, List.map remapExpr xs)
                    | EExnTest(x, ent) -> EExnTest(remapExpr x, remapEnt ent)
                    | EExnGet(x, ent, f, t) -> EExnGet(remapExpr x, remapEnt ent, f, remapTy t)
                    | EOnRaise(x, ds) -> EOnRaise(remapExpr x, List.map mapVar ds)
                    | EDup(x, t) -> EDup(remapExpr x, remapTy t)
                    | ELet(v, r, b) ->
                        let r' = remapExpr r
                        let v' = freshVar v
                        ELet(v', r', remapExpr b)
                    | ESeq(a, b) -> ESeq(remapExpr a, remapExpr b)
                    | EIf(c, t, f, ty) -> EIf(remapExpr c, remapExpr t, remapExpr f, remapTy ty)
                    | EWhile(c, b) -> EWhile(remapExpr c, remapExpr b)
                    | EFor(v, a, b, up, body) ->
                        let a' = remapExpr a
                        let b' = remapExpr b
                        let v' = freshVar v
                        EFor(v', a', b', up, remapExpr body)
                    | EAssign(v, r) -> EAssign(mapVar v, remapExpr r)
                    | EStore(lv, r) -> EStore(remapExpr lv, remapExpr r)
                    | EDrop(v, k) -> EDrop(mapVar v, remapExpr k)
                    | EUnpack(u, k) ->
                        let u' =
                            { u with
                                Scrut = mapVar u.Scrut
                                Moves = u.Moves |> List.map (fun (s, v) -> s, freshVar v)
                                Token = u.Token |> Option.map freshVar
                            }

                        EUnpack(u', remapExpr k)
                    | EPromote(v, k) -> EPromote(mapVar v, remapExpr k)
                    | ERaise(x, t) -> ERaise(remapExpr x, remapTy t)
                    | ETry(b, v, h, t) ->
                        let b' = remapExpr b
                        let v' = freshVar v
                        ETry(b', v', remapExpr h, remapTy t)

                let clonedBody = remapExpr uFn.Body

                state.Fns.Add
                    {
                        Name = fnRename[uFn.Name]
                        TypeParams = uFn.TypeParams
                        Params = newParams
                        Modes = newParams |> List.map (fun _ -> MPlain)
                        Ret = remapTy uFn.Ret
                        Body = clonedBody
                        RetFrom = None
                        Raises = RNever
                        Stores = false
                        IsLocal = true
                        IsEntryPoint = false
                        Range = uFn.Range
                        NoEscape = []
                        BodyK = None
                        StoreFacts = [], false, false
                        AssertedNoRaise = []
                        AssertedStores = []
                        NeedsChain = false
                        PendingChainDeps = []
                        BodyTc = None
                    }

            let topCloned = fnRename[unit.Name]
            clonedUnits[memoKey] <- topCloned
            topCloned

    let mutable anyCloned = false

    let rec rewriteCaller (env: Map<int, string * Ty list * Expr list * Ty>) (e: Expr) : Expr =
        let go = rewriteCaller env

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            ELet(v, r', rewriteCaller env' b)
        | ESeq(a, b) -> ESeq(go a, go b)
        | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
        | EWhile(c, b) -> EWhile(go c, go b)
        | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
        | EAssign(v, r) -> EAssign(v, go r)
        | EStore(lv, r) -> EStore(go lv, go r)
        | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
        | ERaise(x, ty) -> ERaise(go x, ty)
        | _ ->
            let e' =
                match flatKids e with
                | [] -> e
                | ks -> withFlatKids e (List.map go ks)

            match e' with
            | ECall(calleeName, callTypeArgs, callArgs, callRetTy) ->
                match calleeName.IndexOf '.' with
                | dot when dot > 0 ->
                    let calleeAlias = calleeName.Substring(0, dot)
                    let memberName = calleeName.Substring(dot + 1)

                    match tier2.ImportFacts.TryFind calleeAlias with
                    | Some fileFacts ->
                        match fileFacts.Fns.TryFind memberName with
                        | Some ff when ff.Hof.IsSome ->
                            let unit = ff.Hof.Value

                            match unit.Fns |> List.tryHead with
                            | Some topUnitFn when
                                callArgs.Length = topUnitFn.Params.Length
                                && callTypeArgs.Length = topUnitFn.TypeParams.Length
                                && ff.FnParamsNoEscape.Length = callArgs.Length
                                ->
                                let hasKnownCallerLambda =
                                    List.zip ff.FnParamsNoEscape callArgs
                                    |> List.exists (fun (noEsc, a) ->
                                        if not noEsc then
                                            false
                                        else
                                            match resolveKnownClosure env a with
                                            | Some(cloTarget, _, _, _) -> callerFnNames.Contains cloTarget
                                            | None -> false
                                    )

                                if hasKnownCallerLambda then
                                    anyCloned <- true
                                    let clonedTop = cloneUnit calleeAlias unit
                                    ECall(clonedTop, callTypeArgs, callArgs, callRetTy)
                                else
                                    e'
                            | _ -> e'
                        | _ -> e'
                    | None -> e'
                | _ -> e'
            | _ -> e'

    for fn in List.ofSeq state.Fns do
        fn.Body <- rewriteCaller Map.empty fn.Body

    if anyCloned then
        specializeHofs state hooks

    List.ofSeq addedFsImports |> List.distinct, extraFacts |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

/// Run the local normalization passes (cleanup, resource hooks scan, intra-file HOF specialization)
/// that need no cross-file facts.
let prepareLocal (state: FileState) : LocalPrepared =
    // The hooks of a resource only borrow the value they are given: the runtime calls them when
    // it gives the value up or copies it, and a hook that took it would give it up again.
    let hooks =
        state.Ents.Values
        |> Seq.choose (fun e -> e.Hooks)
        |> Seq.collect (fun (destroy, dup) -> destroy :: Option.toList dup)
        |> HashSet

    for fn in state.Fns do
        fn.Body <- cleanup fn.Body

    let snapshotFns =
        state.Fns
        |> Seq.map (fun fn -> fn.Name, { fn with Body = fn.Body })
        |> Map.ofSeq

    let snapshotCurried2 =
        state.Curried2 |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

    specializeHofs state hooks

    {
        State = state
        Hooks = hooks
        SnapshotFns = snapshotFns
        SnapshotCurried2 = snapshotCurried2
    }

/// Run cross-file-aware inference, publish public `FnFacts`, specialize `callK`, and run Perceus.
let inferAndFinish
    (prep: LocalPrepared)
    (extLookup: string -> Facts.FnFacts option)
    (tier2Opt: Tier2Context option)
    (publishFacts: string list -> Map<string, Facts.FnFacts> -> unit)
    : unit
    =
    let state = prep.State
    let hooks = prep.Hooks

    let addedFsImports, extraImportFacts =
        match tier2Opt with
        | Some tier2 -> importTier2Hofs state hooks tier2
        | None -> [], Map.empty

    let effectiveExtLookup (fname: string) =
        match extLookup fname with
        | Some _ as hit -> hit
        | None ->
            match fname.IndexOf '.' with
            | -1 -> None
            | dot ->
                let alias = fname.Substring(0, dot)
                let memberName = fname.Substring(dot + 1)

                match extraImportFacts.TryFind alias with
                | Some ff -> ff.Fns.TryFind memberName
                | None -> None

    let pureStdlibModules =
        HashSet
            [
                "List"
                "Array"
                "Seq"
                "Map"
                "Set"
                "Option"
                "Result"
                "Guid"
                "TimeSpan"
                "DateTime"
                "DateOnly"
                "DateTimeOffset"
                "Uri"
                "Path"
                "ResizeArray"
                "HashSet"
                "Queue"
                "Stack"
                "ListCollector"
            ]

    let hasFableLibPrefix =
        state.Imports.Keys
        |> Seq.exists (fun path -> path.Replace('\\', '/').Contains "fable-library-zig")

    let pureStdlibAliases =
        state.Imports
        |> Seq.choose (fun kv ->
            let norm = kv.Key.Replace('\\', '/')
            let baseName = System.IO.Path.GetFileNameWithoutExtension norm

            let isLibPath =
                if hasFableLibPrefix then
                    norm.Contains "fable-library-zig/"
                else
                    norm.StartsWith("./", System.StringComparison.Ordinal)
                    && norm.IndexOf('/', 2) = -1

            if isLibPath && pureStdlibModules.Contains baseName then
                Some kv.Value
            else
                None
        )
        |> HashSet

    let p =
        {
            State = state
            Fns = Dictionary()
            Ext = effectiveExtLookup
            StoredFields = Dictionary()
            CallsCallback = HashSet()
            CallsExtStore = HashSet()
            ExtStoreDeps = Dictionary()
            PureStdlibAliases = pureStdlibAliases
        }

    for fn in state.Fns do
        p.Fns[fn.Name] <- fn

    let located (fn: FnInfo) (f: unit -> unit) =
        try
            f ()
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    inferRaises p

    let collectNoRaiseAsserts (fn: FnInfo) =
        let tpSet = Set.ofList fn.TypeParams
        let seen = HashSet<string>()
        let acc = List<string * Ty list>()

        let rec scan (e: Expr) =
            match e with
            | ECall(f, tyArgs, xs, _) ->
                if not (p.Fns.ContainsKey f) then
                    match p.Ext f with
                    | Some ff when ff.Raises = Facts.PRNever ->
                        if freeGens tyArgs |> List.forall tpSet.Contains then
                            let key = f + "<" + (tyArgs |> List.map tyKey |> String.concat ",") + ">"

                            if seen.Add key then
                                acc.Add(f, tyArgs)
                    | _ -> ()

                List.iter scan xs
            | ELet(_, r, b)
            | ESeq(r, b)
            | EWhile(r, b)
            | EStore(r, b) ->
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
            | ETry(b, _, h, _) ->
                scan b
                scan h
            | EDrop(_, k)
            | EUnpack(_, k)
            | EPromote(_, k) -> scan k
            | _ -> List.iter scan (flatKids e)

        scan fn.Body
        fn.AssertedNoRaise <- List.ofSeq acc

    for fn in state.Fns do
        collectNoRaiseAsserts fn

    for fn in state.Fns do
        fn.Body <- fn.Body |> elideDeadTry p |> cleanup

    inferStores p

    for fn in state.Fns do
        located
            fn
            (fun () ->
                fn.Body <-
                    fn.Body
                    |> hoistRaising p
                    |> hoistMutableReads p
                    |> nameProjections state
                    |> splitPathsIn state Map.empty
                    |> cleanup
            )

    inferBorrows p

    for fn in state.Fns do
        if hooks.Contains fn.Name then
            fn.Modes <- fn.Modes |> List.map (fun _ -> MBorrowed)

            // A hook runs here and never on .NET: what it does must not change what the program
            // computes. It may read the value and call `[<Emit>]` code (the hardware), nothing
            // that assigns.
            let assigns =
                exists
                    (fun x ->
                        match x with
                        | EStore _ -> true
                        | EAssign(v, _) -> v.Kind = VGlobal
                        | EEmit(m, _, _) -> m.StartsWith("fable_rt.store(", System.StringComparison.Ordinal)
                        | _ -> false
                    )
                    fn.Body

            if assigns then
                raise (
                    ZigError(
                        $"%s{fn.Name}: a resource's Destroy and Dup run on the Zig target only (never on .NET), so they may not change what the program computes: they may read the value and call [<Emit>] code, but not assign",
                        fn.Range
                    )
                )

    inferNoEscape p hooks
    inferNeedsChain p hooks

    let exportedHofUnits = exportHofUnits prep p tier2Opt

    let exportedFns =
        state.Fns
        |> Seq.choose (fun fn ->
            if fn.IsLocal then
                None
            else
                let portableRaises =
                    match fn.Raises with
                    | RNever -> Facts.PRNever
                    | RAlways -> Facts.PRAlways
                    | RDepends _ -> Facts.PRDepends []

                let storedFields =
                    match p.StoredFields.TryGetValue fn.Name with
                    | true, s -> Set.toList s
                    | _ -> []

                let callsCb = p.CallsCallback.Contains fn.Name
                let callsExt = p.CallsExtStore.Contains fn.Name
                fn.StoreFacts <- (storedFields, callsCb, callsExt)

                Some(
                    fn.Name,
                    ({
                        Modes = fn.Modes
                        RetFrom = fn.RetFrom
                        Raises = portableRaises
                        StoredFields = storedFields
                        CallsCallback = callsCb
                        CallsExtStore = callsExt
                        FnParamsNoEscape = fn.NoEscape
                        NeedsChain = fn.NeedsChain
                        Hof = exportedHofUnits.TryFind fn.Name
                    }
                    : FnFacts)
                )
        )
        |> Map.ofSeq

    publishFacts addedFsImports exportedFns
    specializeCallKHofs p

    for fn in state.Fns do
        let owned =
            List.zip fn.Params fn.Modes
            |> List.choose (fun (q, m) ->
                if m = MOwned then
                    Some q.Id
                else
                    None
            )
            |> Set.ofList

        let kParams =
            if fn.NoEscape.Length = fn.Params.Length && List.exists id fn.NoEscape then
                List.zip fn.Params fn.NoEscape
                |> List.choose (fun (q, isK) ->
                    if isK then
                        Some q.Id
                    else
                        None
                )
                |> Set.ofList
            else
                Set.empty

        located
            fn
            (fun () ->
                let prePcBody = fn.Body
                let unescaped = localUnescapedRefVars prePcBody
                let storeAsserts = List<string * Set<string> * bool>()

                fn.Body <-
                    pc
                        p
                        { emptyEnv with
                            Owned = owned
                            TailBorrowed = fn.RetFrom.IsSome
                            UnescapedRefs = unescaped
                            StoreAsserts = storeAsserts
                        }
                        prePcBody
                        Set.empty

                if not kParams.IsEmpty then
                    fn.BodyK <-
                        Some(
                            pc
                                p
                                { emptyEnv with
                                    Owned = owned
                                    TailBorrowed = fn.RetFrom.IsSome
                                    UnescapedRefs = unescaped
                                    KParams = kParams
                                    StoreAsserts = storeAsserts
                                }
                                prePcBody
                                Set.empty
                        )

                if fn.NeedsChain || not fn.PendingChainDeps.IsEmpty then
                    if fn.RetFrom.IsNone && fn.Modes |> List.forall ((<>) MBorrowed) then
                        fn.BodyTc <- Some fn.Body
                    else
                        let ownedTc =
                            fn.Params
                            |> List.choose (fun q ->
                                if isManaged q.Ty then
                                    Some q.Id
                                else
                                    None
                            )
                            |> Set.ofList

                        let tcAsserts = List<string * Set<string> * bool>()

                        fn.BodyTc <-
                            Some(
                                pc
                                    p
                                    { emptyEnv with
                                        Owned = ownedTc
                                        TailBorrowed = false
                                        UnescapedRefs = unescaped
                                        StoreAsserts = tcAsserts
                                    }
                                    prePcBody
                                    Set.empty
                            )

                if storeAsserts.Count > 0 then
                    fn.AssertedStores <-
                        storeAsserts
                        |> Seq.groupBy (fun (extFn, _, _) -> extFn)
                        |> Seq.map (fun (extFn, items) ->
                            let fields =
                                items
                                |> Seq.collect (fun (_, fs, _) -> fs)
                                |> Set.ofSeq
                                |> Set.toList
                                |> List.sort

                            let checkExt = items |> Seq.exists (fun (_, _, c) -> c)
                            extFn, fields, checkExt
                        )
                        |> Seq.sortBy (fun (extFn, _, _) -> extFn)
                        |> Seq.toList
            )

/// Standalone single-file entry point running all ownership passes without external facts.
let run (state: FileState) : unit =
    let prep = prepareLocal state
    inferAndFinish prep (fun _ -> None) None (fun _ _ -> ())
