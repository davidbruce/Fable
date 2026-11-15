/// The ownership passes on the IR: borrow inference for parameters and results, then Perceus
/// (dup/drop insertion, drop-unpack and reuse of dead cells).
module Fable.Transforms.Zig.Perceus

open System.Collections.Generic
open Fable.Transforms.Zig.IR

type private P =
    {
        State: FileState
        /// the functions of the file being compiled, by name
        Fns: Dictionary<string, FnInfo>
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

/// Can this call raise, as far as this file can tell? A function value always can. A function
/// of another file can if Zig finds that it does.
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
        | _ -> RDepends [ f, tyArgs ]
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
// Reference records: which code can assign a field. A value read from such a field is only a
// borrow while nothing can assign.
// =============================================================================================

/// Can evaluating `e` assign a field of a reference record? A function of another file and a
/// function value are taken to: this file cannot see what they do.
let rec private mayStore (p: P) (e: Expr) : bool =
    let any (es: Expr list) = es |> List.exists (mayStore p)

    match e with
    | EStore(lv, r) ->
        (match lv with
         | EGet(x, _, _) ->
             match typeOf x with
             | TEnt({ Kind = KRefRecord }, _) -> true
             | _ -> false
         | _ -> false)
        || mayStore p r
    | ECall(f, _, xs, _) ->
        (match p.Fns.TryGetValue f with
         | true, g -> g.Stores
         | _ -> true)
        || any xs
    | ECallClo _
    | ECallVt _
    | ECallIface _ -> true
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b) -> any [ r; b ]
    | EIf(c, t, f, _) -> any [ c; t; f ]
    | EFor(_, a, b, _, body) -> any [ a; b; body ]
    | EAssign(_, r) -> mayStore p r
    | ETry(b, _, h, _) -> any [ b; h ]
    | EDrop(_, k)
    | EUnpack(_, k)
    | EPromote(_, k) -> mayStore p k
    | _ -> any (flatKids e)

let private inferStores (p: P) : unit =
    let mutable changed = true

    while changed do
        changed <- false

        for fn in p.State.Fns do
            if not fn.Stores && mayStore p fn.Body then
                fn.Stores <- true
                changed <- true

// =============================================================================================
// Borrow inference: a managed parameter is borrowed unless the body consumes it (returns it,
// stores it, passes it to an owning parameter) or matches on it while building the same type
// (a reuse site).
// =============================================================================================

/// The modes of the parameters that `args` are passed to. What a function of another file
/// borrows is not known here, so it is assumed to take ownership of every managed argument and
/// to return an owned result; `fable_rt.across` adjusts the call when the Zig is compiled.
let private modesOf (p: P) (fname: string) (args: Expr list) : Mode list =
    match p.Fns.TryGetValue fname with
    | true, f when f.Modes.Length = args.Length -> f.Modes
    | true, _ -> fail None "internal: `%s` is called with %d arguments" fname args.Length
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
                if p.Fns.ContainsKey f then
                    List.iter2 (fun m x -> go (m = MOwned) x) (modesOf p f xs) xs
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

let private inferBorrows (p: P) : unit =
    let fns = p.State.Fns

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
                    elif owning.Contains q.Id || isReuseSite fn.Body q then
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
        | TEnt(ent, _) when ent.Kind = KRecord -> Some ""
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

            let heap = isHeapTy xv.Ty

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
                            && directB |> Set.exists consumedLater.Contains
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
                | ECall(f, _, xs, _) -> modesOf p f xs |> List.map (fun m -> m = MOwned)
                | ECallClo(_, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | ECallVt(_, _, xs, _) -> false :: false :: (xs |> List.map (fun _ -> true))
                | ECallIface(_, _, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | EIface _ -> kids |> List.map (fun _ -> true)
                | EEmit(m, _ :: rest, _) when ownsFirst m -> true :: (rest |> List.map (fun _ -> false))
                | EClosure(_, _, xs, _)
                | EExnNew(_, xs)
                | ECon(_, _, xs, _) -> xs |> List.map (fun _ -> true)
                | _ -> kids |> List.map (fun _ -> false)

            // Borrowed arguments of a call must stay alive for the duration of the call, so an
            // owned argument of the same call must not move them away (e.g. `c.Method(c)`).
            // For external calls, any root var appearing in >= 2 args must also stay borrowed so
            // `foo(x, x)` does not move `x` while another arg of the same `across` call reads it.
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

/// What a test tells about the value it tests. (Nothing is remembered about a variable that
/// can be assigned: it may hold another value by the time the knowledge is used.)
let private refine (env: PEnv) (c: Expr) : PEnv * PEnv =
    match c with
    | ETest(x, case, ty) when (pathKey x).IsSome && isStablePath x && not (touchesMutable x) ->
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
        let head = live e L
        let c', _, _ = rewriteFlat p env c false head

        let loop =
            EWhile(
                c',
                pc
                    p
                    { env with
                        Tokens = []
                        TailBorrowed = false
                    }
                    b
                    head
            )

        dropAfterLoop p env loop L
    | EFor(i, a, b, up, body) ->
        let head = Set.union (live e L) L

        let loop =
            EFor(
                i,
                a,
                b,
                up,
                pc
                    p
                    { env with
                        Tokens = []
                        TailBorrowed = false
                    }
                    body
                    head
            )

        dropAfterLoop p env loop L
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
                { env with
                    Owned = ownedH
                    Tokens = []
                    TailBorrowed = false
                }
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

        // (A projection of a variable that can be assigned is not an alias: the variable may be
        // given another value while the name is still in use, so the name gets its own
        // reference.)
        let env1, isAlias =
            match rhs with
            // (Nor is a read of a field that can be assigned, if anything while the name is in
            // use may assign a field: the field could get another value and give this one up.
            // A walk that only reads a mutable structure stays free of reference counting.)
            | EGet(x, proj, _) when
                isManaged v.Ty
                && not v.FMutable
                && isStablePath x
                && (not (touchesMutable rhs) || not (mayStore p body))
                && not (isSharedFieldRead rhs)
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

                env1, true
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

                { env with Owners = env.Owners.Add(v.Id, srcs) }, true
            // A span views what it was made of (an array's items, another span): what it was
            // made of stays alive while it is in use.
            | _ when
                (match v.Ty with
                 | TSlice _ -> true
                 | _ -> false)
                ->
                let srcs = fv rhs |> Set.toList
                { env with Owners = env.Owners.Add(v.Id, srcs) }, true
            | _ -> env, false

        let rhs', consumed, env2 = rewriteFlat p env1 rhs (isManaged v.Ty && not isAlias) Lb

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
                { env with
                    Owned = owned
                    Tokens = []
                }
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

    let rec exprSize (e: Expr) =
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

/// Run the ownership passes on every function of a file.
let run (state: FileState) : unit =
    // The hooks of a resource only borrow the value they are given: the runtime calls them when
    // it gives the value up or copies it, and a hook that took it would give it up again.
    let hooks =
        state.Ents.Values
        |> Seq.choose (fun e -> e.Hooks)
        |> Seq.collect (fun (destroy, dup) -> destroy :: Option.toList dup)
        |> HashSet

    for fn in state.Fns do
        fn.Body <- cleanup fn.Body

    specializeHofs state hooks

    let p =
        {
            State = state
            Fns = Dictionary()
        }

    for fn in state.Fns do
        p.Fns[fn.Name] <- fn

    let located (fn: FnInfo) (f: unit -> unit) =
        try
            f ()
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    inferRaises p

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

        located
            fn
            (fun () ->
                fn.Body <-
                    pc
                        p
                        { emptyEnv with
                            Owned = owned
                            TailBorrowed = fn.RetFrom.IsSome
                        }
                        fn.Body
                        Set.empty
            )
