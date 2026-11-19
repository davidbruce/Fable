/// Perceus dup/drop insertion, drop-unpack, and in-place cell reuse rewriting.
module internal Fable.Transforms.Zig.PerceusInsert

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.PerceusAnalysis

// =============================================================================================
// Perceus
// =============================================================================================

type PEnv =
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

type POp =
    | ODrop of Var
    | OUnpack of Unpack
    | OPromote of Var

let (|KIfaceRecv|_|) (kParams: Set<int>) (e: Expr) =
    match e with
    | EVar v when kParams.Contains v.Id -> Some(v, false)
    | EGet(EVar v, PSome, _) when kParams.Contains v.Id -> Some(v, true)
    | _ -> None

let vk (id: int) = $"v%d{id}"

/// The access-path key of a chain of projections that starts at a variable.
let rec pathKey (e: Expr) : string option =
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

let rec live (e: Expr) (after: Set<int>) : Set<int> =
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

and loopLive (step: Set<int> -> Set<int>) (init: Set<int>) =
    let next = step init

    if next = init then
        init
    else
        loopLive step (Set.union init next)

let expand (env: PEnv) (s: Set<int>) =
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

let ownersStar env b =
    Set.remove b (expand env (Set.singleton b))

let isUserReuseCellTy (t: Ty) =
    match t with
    | TEnt(e, _) when e.Kind = KHeapUnion && e.Hooks.IsNone -> true
    | TEnt(e, _) when
        e.Kind = KRefRecord
        && e.Hooks.IsNone
        && (e.Name = "fable_rt.Ref"
            || not (e.Name.StartsWith("fable_rt.", System.StringComparison.Ordinal)))
        ->
        true
    | _ -> false

let hasReuseCellCon (t: Ty) (xs: Expr list) =
    isUserReuseCellTy t && (not (isHeapTy t) || not xs.IsEmpty)

/// Is there a constructor in `e` reachable by `env.Tokens` that could be built in a dead cell of `shape`?
let rec hasConOfShape (shape: Ty * string) (e: Expr) =
    match e with
    | EWhile _
    | EFor _
    | ETry _ -> false
    | ECon(t, c, xs, _) when hasReuseCellCon t xs && cellsMatch shape (t, c) -> true
    | ELet(_, r, b) -> hasConOfShape shape r || (isFlat r && hasConOfShape shape b)
    | ESeq(a, b) -> hasConOfShape shape a || (isFlat a && hasConOfShape shape b)
    | EIf(c, t, f, _) -> hasConOfShape shape c || hasConOfShape shape t || hasConOfShape shape f
    | EAssign(_, r) -> hasConOfShape shape r
    | _ -> flatKids e |> List.exists (hasConOfShape shape)

let deadHeapUnpackInfo (env: PEnv) (e: Expr) (xv: Var) : (string * (string * Ty) list * bool) option =
    if not (isUserReuseCellTy xv.Ty) then
        None
    else
        let knownCase =
            if isHeapTy xv.Ty then
                env.Known.TryFind(vk xv.Id)
            else
                Some ""

        match knownCase with
        | Some case ->
            let fields = caseFields xv.Ty case

            if isHeapTy xv.Ty && fields.IsEmpty then
                None
            else
                let hasReuse = hasConOfShape (xv.Ty, case) e

                if isHeapTy xv.Ty || hasReuse then
                    Some(case, fields, hasReuse)
                else
                    None
        | None -> None

let caseIsNoopDrop (t: Ty) (case: string) =
    let fs = caseFields t case

    if isHeapTy t then
        fs.IsEmpty
    else
        not (fs |> List.exists (snd >> isManaged))

let tryUnpack (p: P) (env: PEnv) (x: int) (borrowers: Set<int>) (e: Expr) (L: Set<int>) : (PEnv * POp) option =
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

            if heap && not (isUserReuseCellTy xv.Ty) then
                None
            else
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
let settle (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : PEnv * POp list =
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
                    let xv = allVars[x]

                    match deadHeapUnpackInfo env e xv with
                    | Some(case, fields, hasReuse) ->
                        let drops = fields |> List.filter (snd >> isManaged)

                        let token =
                            if hasReuse then
                                Some(p.State.NewVar("ru_" + xv.Base, TTok(xv.Ty, case), VLocal, false))
                            else
                                None

                        match token with
                        | Some tk -> env <- { env with Tokens = (tk, (xv.Ty, case)) :: env.Tokens }
                        | None -> ()

                        ops.Add(
                            OUnpack
                                {
                                    Scrut = xv
                                    Case = case
                                    Moves = []
                                    Drops = drops
                                    Token = token
                                    Heap = true
                                }
                        )
                    | None -> dropUnlessNoop xv

    env, List.ofSeq ops

let wrapOps (ops: POp list) (e: Expr) =
    List.foldBack
        (fun op acc ->
            match op with
            | ODrop v -> EDrop(v, acc)
            | OUnpack u -> EUnpack(u, acc)
            | OPromote v -> EPromote(v, acc)
        )
        ops
        e

let wrapDrops (vs: Var list) (e: Expr) =
    List.foldBack (fun v acc -> EDrop(v, acc)) vs e

let mkDup (what: Expr) (t: Ty) =
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
let rewriteFlat (p: P) (env: PEnv) (e: Expr) (rootOwning: bool) (lAfter: Set<int>) : Expr * Set<int> * PEnv =
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
        | ECon(t, c, xs, None) when hasReuseCellCon t xs ->
            let matchTok =
                tokens
                |> List.tryFind (fun (_, shape) -> cellsMatchExact shape (t, c))
                |> Option.orElseWith (fun () -> tokens |> List.tryFind (fun (_, shape) -> cellsMatch shape (t, c)))

            match matchTok with
            | Some(tok, _) ->
                tokens <- tokens |> List.filter (fun (t2, _) -> t2.Id <> tok.Id)
                ECon(t, c, xs, Some tok)
            | None -> e
        | _ -> e

    let wrapExplicitUse (m: Mode) (origArg: Expr) (rewrittenArg: Expr) : Expr =
        match origArg with
        | EKnown _
        | EKnownIface _ -> rewrittenArg
        | _ ->
            if not (isManaged (typeOf origArg)) || m = MPlain then
                EUse(UPlain, rewrittenArg)
            elif m = MBorrowed then
                EUse(UKeep, rewrittenArg)
            else
                match rewrittenArg with
                | EDup(inner, _) when not (touchesMutable inner) -> EUse(UKeep, inner)
                | _ -> EUse(UGive, rewrittenArg)

    let wrapKArgs (origArgs: Expr list) (newArgs: Expr list) : Expr list =
        List.zip origArgs newArgs
        |> List.map (fun (origX, newX) ->
            let m =
                if isManaged (typeOf origX) then
                    MOwned
                else
                    MPlain

            wrapExplicitUse m origX newX
        )

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
                        | EKnown _
                        | EKnownIface _ -> false
                        | _ -> m = MOwned
                    )
                | ECallClo(_, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | ECallVt(_, _, xs, _) -> false :: false :: (xs |> List.map (fun _ -> true))
                | ECallIface(_, _, xs, _) -> false :: (xs |> List.map (fun _ -> true))
                | EIface _ -> kids |> List.map (fun _ -> true)
                | EEmit(m, _ :: rest, _)
                | ERt(m, _ :: rest, _) when ownsFirst m -> true :: (rest |> List.map (fun _ -> false))
                | EKnown(_, _, xs, _) -> xs |> List.map (fun _ -> false)
                | EKnownIface _ -> kids |> List.map (fun _ -> false)
                | EClosure(_, _, xs, _)
                | EExnNew(_, xs)
                | ECon(_, _, xs, _) -> xs |> List.map (fun _ -> true)
                | _ -> kids |> List.map (fun _ -> false)

            // Borrowed arguments of a call must stay alive for the duration of the call, so an
            // owned argument of the same call must not move them away (e.g. `c.Method(c)`).
            // For external calls and `callK` `invokeK` sites, any root var appearing in >= 2 args
            // must also stay borrowed so `f(x, x)` does not move `x` while another arg reads it.
            let borrowedNonOwned () =
                List.zip flags kids
                |> List.fold
                    (fun s (own, k) ->
                        if own then
                            s
                        else
                            Set.union s (expand env (fv k))
                    )
                    Set.empty

            let kCallBorrowed () =
                let argVars = kids.Tail |> List.map (fv >> expand env)
                let seen = HashSet<int>()
                let multi = HashSet<int>()

                for s in argVars do
                    for id in s do
                        if not (seen.Add id) then
                            multi.Add id |> ignore

                Set.union (expand env (fv kids.Head)) (Set.ofSeq multi)

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
                | ECallClo(EVar v, _, _) when env.KParams.Contains v.Id -> kCallBorrowed ()
                | ECallIface(KIfaceRecv env.KParams _, _, _, _) -> kCallBorrowed ()
                | ECall _
                | ECallClo _
                | ECallVt _
                | ECallIface _ -> borrowedNonOwned ()
                | EEmit(m, _, _)
                | ERt(m, _, _) when ownsFirst m -> borrowedNonOwned ()
                | _ -> Set.empty

            let innerBorrowed = Set.union callBorrowed borrowedKids
            let e' = withFlatKids e (List.map2 (rw innerBorrowed) flags kids)

            let e' =
                match e' with
                | ECallClo(EVar v, xs', t) when env.KParams.Contains v.Id ->
                    ECallClo(EVar v, wrapKArgs kids.Tail xs', t)
                | ECallIface(KIfaceRecv env.KParams _ as r', slot, xs', t) ->
                    ECallIface(r', slot, wrapKArgs kids.Tail xs', t)
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

let rec isLocalPath (e: Expr) =
    match e with
    | EVar v -> v.Kind <> VGlobal
    | EGet(x, _, _) -> isLocalPath x
    | _ -> false

let clearAssignedKnown (ids: Set<int>) (env: PEnv) : PEnv =
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
let rec refine (env: PEnv) (c: Expr) : PEnv * PEnv =
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
let raiseEdgeDrops (p: P) (env: PEnv) (stillOwned: Set<int>) : Var list =
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
let wrapRaising (p: P) (env: PEnv) (e: Expr) (stillOwned: Set<int>) : Expr =
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

let rec pc (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : Expr =
    let env, ops = settle p env e L
    wrapOps ops (pcNode p env e L)

and pcNode (p: P) (env: PEnv) (e: Expr) (L: Set<int>) : Expr =
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
and dropAfterLoop (p: P) (env: PEnv) (loop: Expr) (L: Set<int>) : Expr =
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

and pcFlat (p: P) (env: PEnv) (e: Expr) (L: Set<int>) (rootOwning: bool) : Expr =
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

and pcLet (p: P) (env: PEnv) (v: Var) (rhs: Expr) (body: Expr) (L: Set<int>) : Expr =
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
                    | EVar r, PSome ->
                        let env1' = child r "Some" "Value"

                        if env.KParams.Contains r.Id then
                            { env1' with KParams = env1'.KParams.Add v.Id }
                        else
                            env1'
                    | _ -> env1

                env1, true, None
            | EVar u when isManaged v.Ty && not v.FMutable && env.KParams.Contains u.Id ->
                { env with
                    Owners = env.Owners.Add(v.Id, [ u.Id ])
                    KParams = env.KParams.Add v.Id
                },
                true,
                None
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
                                | EKnown _
                                | EKnownIface _ -> false
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
                | Some c when caseIsNoopDrop xv.Ty c -> false
                | _ -> (deadHeapUnpackInfo env2 body xv).IsNone
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

let emptyEnv =
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
