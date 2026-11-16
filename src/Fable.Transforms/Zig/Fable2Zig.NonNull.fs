/// The pass that proves values non-null and removes the checks it can (see Zig_Roadmap.md, "Null
/// for reference types"). Lowering already uses an object made in place, or a variable bound to
/// one, without a check. Here: a check of a variable that an earlier check of it dominates, in
/// the same straight-line code, is removed. What follows a check in a sequence or a `let` knows
/// the variable is not null; both branches of an `if` keep what they both know; a loop's body and
/// a `try` keep what was known before them and add nothing after; a variable that is assigned
/// is never known (only variables that cannot be assigned are tracked).
module Fable.Transforms.Zig.NonNull

open Fable.Transforms.Zig.IR

let private isCheck (macro: string) =
    macro = "fable_rt.checkNonNull($0)" || macro = "fable_rt.checkCellNonNull($0)"

let rec private go (known: Set<int>) (e: Expr) : Expr * Set<int> =
    let same (e': Expr) = e', known
    let sub (x: Expr) = fst (go known x)
    let subs (xs: Expr list) = List.map sub xs

    match e with
    | ERt(macro, [ EVar v ], ty) when isCheck macro && not v.FMutable ->
        if known.Contains v.Id then
            EUnit, known
        else
            e, known.Add v.Id
    | ESeq(a, b) ->
        let a', k1 = go known a
        let b', k2 = go k1 b
        ESeq(a', b'), k2
    | ELet(v, value, body) ->
        let value', k1 = go known value
        let body', k2 = go k1 body
        ELet(v, value', body'), k2
    | EAssign(v, x) ->
        let x', k1 = go known x
        EAssign(v, x'), k1.Remove v.Id
    | EIf(c, t, f, ty) ->
        let c', k1 = go known c
        let t', kt = go k1 t
        let f', kf = go k1 f
        EIf(c', t', f', ty), Set.intersect kt kf
    | EWhile(c, body) ->
        let c', k1 = go known c
        EWhile(c', fst (go k1 body)), k1
    | EFor(v, a, b, down, body) -> same (EFor(v, sub a, sub b, down, fst (go known body)))
    | ETry(body, x, handler, ty) -> same (ETry(sub body, x, sub handler, ty))
    | EVar _
    | ELit _
    | EUnit -> same e
    | EPrim(op, xs, ty) -> same (EPrim(op, subs xs, ty))
    | ECall(f, tys, xs, ty) -> same (ECall(f, tys, subs xs, ty))
    | ECallClo(f, xs, ty) -> same (ECallClo(sub f, subs xs, ty))
    | ECallVt(f, self, xs, ty) -> same (ECallVt(sub f, sub self, subs xs, ty))
    | EClosure(f, tys, xs, ty) -> same (EClosure(f, tys, subs xs, ty))
    | EIface(ty, src, slots) ->
        let src' =
            match src with
            | ISrcValue x -> ISrcValue(sub x)
            | ISrcCaptures xs -> ISrcCaptures(subs xs)
            | ISrcUpcast x -> ISrcUpcast(sub x)

        same (EIface(ty, src', slots))
    | ECallIface(i, slot, xs, ty) -> same (ECallIface(sub i, slot, subs xs, ty))
    | ECon(ty, case, xs, token) -> same (ECon(ty, case, subs xs, token))
    | EGet(x, p, ty) -> same (EGet(sub x, p, ty))
    | ETest(x, case, ty) -> same (ETest(sub x, case, ty))
    | EAddr(x, isConst) -> same (EAddr(sub x, isConst))
    | EDeref(x, ty) -> same (EDeref(sub x, ty))
    | EIndex(a, i, ty) -> same (EIndex(sub a, sub i, ty))
    | EEmit(macro, xs, ty) -> same (EEmit(macro, subs xs, ty))
    | ERt(macro, xs, ty) -> same (ERt(macro, subs xs, ty))
    | EExnNew(ent, xs) -> same (EExnNew(ent, subs xs))
    | EExnTest(x, ent) -> same (EExnTest(sub x, ent))
    | EExnGet(x, ent, field, ty) -> same (EExnGet(sub x, ent, field, ty))
    | EOnRaise(x, vs) -> same (EOnRaise(sub x, vs))
    | EDup(x, ty) -> same (EDup(sub x, ty))
    | EStore(place, x) -> same (EStore(sub place, sub x))
    | EDrop(v, k) ->
        let k', k1 = go known k
        EDrop(v, k'), k1
    | EUnpack(u, k) ->
        let k', k1 = go known k
        EUnpack(u, k'), k1
    | EPromote(v, k) ->
        let k', k1 = go known k
        EPromote(v, k'), k1
    | ERaise(x, ty) -> same (ERaise(sub x, ty))

/// The checks of every function of the file that an earlier check makes needless, removed
let run (state: FileState) =
    for fn in state.Fns do
        fn.Body <- fst (go Set.empty fn.Body)
