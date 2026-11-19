/// The ownership IR of the Zig target: what Fable's AST is lowered to before borrow inference,
/// dup/drop insertion and emission. Flat expressions have no control flow; everything a
/// statement needs is let-bound first (ANF), so every pass can reason about one use at a time.
module rec Fable.Transforms.Zig.IR

open System.Collections.Generic
open Fable.AST

exception ZigError of message: string * range: SourceLocation option

let fail (r: SourceLocation option) fmt =
    Printf.kprintf
        (fun s ->
            // (FABLE_ZIG_TRACE=1: where in the compiler an error is raised)
            if System.Environment.GetEnvironmentVariable "FABLE_ZIG_TRACE" = "1" then
                eprintfn "ZIGTRACE %s\n%s" s (System.Diagnostics.StackTrace(true).ToString())

            raise (ZigError(s, r))
        )
        fmt

type EntKind =
    /// value struct
    | KRecord
    /// non-recursive union: unboxed `union(enum)`
    | KValueUnion
    /// recursive union or reference record: `union(enum)` of refcounted cell pointers
    | KHeapUnion
    /// a record with mutable fields, or one that contains itself: a pointer to a
    /// reference-counted cell, so that it has an identity, as on .NET
    | KRefRecord
    /// an F# `exception` declaration: its values have the type `exn`
    | KExn
    /// an interface: fat pointer `{ data, vt }` with static vtable
    | KIface

[<ReferenceEquality>]
type Ent =
    {
        Name: string
        Ref: Fable.EntityRef
        Kind: EntKind
        /// the type parameters of a generic type; the field types below mention them as `TGen`
        TypeParams: string list
        /// records: one case named ""
        mutable Cases: (string * (string * Ty) list) list
        /// the fields of a record that can be assigned
        mutable MutableFields: string list
        /// its cells can be part of a reference cycle whatever its type arguments are (they
        /// carry a header of the cycle collector)
        mutable Cyclic: bool
        /// its cells can reach a function value or an exception: they can be part of a cycle
        /// if function values can, which depends on the whole program
        mutable ReachesOpaque: bool
        /// holds references to cells whatever its type arguments are
        mutable Managed: bool
        mutable Copyable: bool
        /// declared in the file being compiled (its declaration is emitted there)
        IsLocal: bool
        /// a resource (`IResource<'T>`, `ISharedResource<'T>`): the functions that destroy a
        /// value and that copy one (None: the type is move-only)
        mutable Hooks: (string * string option) option
        /// the `Equals`, `GetHashCode` and `IComparable.CompareTo` the type declares, which
        /// `=`, `hash` and `compare` call: the runtime's name of the hook, and the function
        mutable Overrides: (string * string) list
    }

type Ty =
    | TPrim of string
    /// a record or union, with its type arguments
    | TEnt of Ent * Ty list
    /// a type parameter of the function or type being compiled
    | TGen of string
    | TOpt of Ty
    | TTuple of Ty list
    | TPtr of Ty * isConst: bool
    | TSlice of Ty * isConst: bool
    | TArr of Ty * int
    | TFn of Ty list * Ty
    /// Raw vtable slot pointer in a fat-pointer interface: `*const fn (?*anyopaque, ...) fable_rt.Raised!R`.
    | TSlot of Ty list * Ty
    /// Perceus reuse token: a dead cell of a case of a recursive union, or nothing
    | TTok of Ty * string

let tVoid = TPrim "void"
let tBool = TPrim "bool"
let tI32 = TPrim "i32"

/// F#'s `exn`, and the type of every exception: a reference-counted cell of the runtime.
let tExn = TPrim "fable_rt.Exn"

/// F#'s `string`: immutable UTF-16, counted unless it is a literal.
let tStr = TPrim "fable_rt.String"

let isVoid (t: Ty) =
    match t with
    | TPrim "void" -> true
    | _ -> false

let isFloatTy (t: Ty) =
    match t with
    | TPrim("f32" | "f64") -> true
    | _ -> false

/// Bit width of an integer type ("i32" -> 32), 0 for anything else.
let intBits (t: Ty) =
    match t with
    | TPrim("isize" | "usize") -> 64
    // (F#'s uint16: a type of its own, so that it is not taken for a char)
    | TPrim "c_ushort" -> 16
    | TPrim s when s.Length > 1 && (s[0] = 'i' || s[0] = 'u') && System.Char.IsDigit s[1] -> int (s.Substring 1)
    | _ -> 0

/// Does a value of this type hold references to cells? What a type parameter stands for is
/// not known while its function is compiled, so it counts as managed: the dup and the drop of
/// such a value compile to nothing when the function is used with a type that is not.
let rec isManaged (t: Ty) =
    match t with
    | TEnt(e, args) -> e.Managed || List.exists isManaged args
    | TGen _ -> true
    | TOpt t -> isManaged t
    | TTuple ts -> List.exists isManaged ts
    // (a function value may own an environment)
    | TFn _ -> true
    | TPrim "fable_rt.Exn"
    | TPrim "fable_rt.Obj"
    | TPrim "fable_rt.BigInt"
    | TPrim "fable_rt.ThreadOf"
    | TPrim "fable_rt.String" -> true
    | _ -> false

/// Does a value hold a decimal (which is compared by value: 1.0m = 1.00m)?
let holdsDecimal (t: Ty) : bool =
    let seen = HashSet<string>()

    let rec go (t: Ty) =
        match t with
        | TPrim "fable_rt.NetDecimal" -> true
        | TOpt t
        | TArr(t, _) -> go t
        | TTuple ts -> List.exists go ts
        | TEnt(e, args) ->
            List.exists go args
            || (seen.Add e.Name
                && e.Cases |> List.exists (fun (_, fs) -> fs |> List.exists (snd >> go)))
        | _ -> false

    go t

/// The same question for the declaration of a type, whatever its parameters stand for.
let rec isManagedDecl (t: Ty) =
    match t with
    | TEnt(e, args) -> e.Managed || List.exists isManagedDecl args
    | TGen _ -> false
    | TOpt t -> isManagedDecl t
    | TTuple ts -> List.exists isManagedDecl ts
    | TFn _ -> true
    | TPrim "fable_rt.Exn"
    | TPrim "fable_rt.Obj"
    | TPrim "fable_rt.BigInt"
    | TPrim "fable_rt.ThreadOf"
    | TPrim "fable_rt.String" -> true
    | _ -> false

let isHeapTy (t: Ty) =
    match t with
    | TEnt(e, _) -> e.Kind = KHeapUnion
    | _ -> false

/// Can a value be copied implicitly? Copying a handle shares the cell (count + 1).
let rec isCopyable (t: Ty) =
    match t with
    | TEnt(e, args) -> e.Copyable && List.forall isCopyable args
    | TOpt t -> isCopyable t
    | TTuple ts -> List.forall isCopyable ts
    | _ -> true

/// Can a value of this type hold a reference to a cell that can be part of a cycle? (What a
/// type parameter, a function value or an exception holds is not known here.)
let rec mayHoldCyclic (t: Ty) : bool =
    match t with
    | TFn _
    | TGen _
    | TPrim "fable_rt.Exn"
    | TPrim "fable_rt.Obj" -> true
    | TEnt(e, args) ->
        e.Kind = KIface
        || e.Cyclic
        || e.ReachesOpaque
        || List.exists mayHoldCyclic args
        || (e.Kind <> KHeapUnion
            && e.Kind <> KRefRecord
            && e.Cases |> List.exists (fun (_, fs) -> fs |> List.exists (snd >> mayHoldCyclic)))
    | TOpt t -> mayHoldCyclic t
    | TTuple ts -> List.exists mayHoldCyclic ts
    | _ -> false

/// A name for a type that is the same wherever the type is written.
let rec tyKey (t: Ty) : string =
    match t with
    | TPrim s -> s
    | TEnt(e, []) -> e.Ref.FullName
    | TEnt(e, args) -> e.Ref.FullName + "<" + (args |> List.map tyKey |> String.concat ",") + ">"
    | TGen n -> "'" + n
    | TOpt t -> "?" + tyKey t
    | TTuple ts -> "(" + (ts |> List.map tyKey |> String.concat ",") + ")"
    | TPtr(t, c) -> $"*%b{c}%s{tyKey t}"
    | TSlice(t, c) -> $"[]%b{c}%s{tyKey t}"
    | TArr(t, n) -> $"[%d{n}]%s{tyKey t}"
    | TFn(args, ret) -> "fn(" + (args |> List.map tyKey |> String.concat ",") + ")" + tyKey ret
    | TSlot(args, ret) -> "slot(" + (args |> List.map tyKey |> String.concat ",") + ")" + tyKey ret
    | TTok(t, c) -> $"tok:%s{tyKey t}.%s{c}"

/// Replace type parameters by what they stand for.
let rec substTy (m: Map<string, Ty>) (t: Ty) : Ty =
    if m.IsEmpty then
        t
    else
        match t with
        | TGen n ->
            match m.TryFind n with
            | Some x -> x
            | None -> t
        | TEnt(e, args) -> TEnt(e, args |> List.map (substTy m))
        | TOpt t -> TOpt(substTy m t)
        | TTuple ts -> TTuple(ts |> List.map (substTy m))
        | TPtr(t, c) -> TPtr(substTy m t, c)
        | TSlice(t, c) -> TSlice(substTy m t, c)
        | TArr(t, n) -> TArr(substTy m t, n)
        | TFn(args, ret) -> TFn(args |> List.map (substTy m), substTy m ret)
        | TSlot(args, ret) -> TSlot(args |> List.map (substTy m), substTy m ret)
        | TTok(t, c) -> TTok(substTy m t, c)
        | TPrim _ -> t

/// The type parameters a type mentions, in the order they appear.
let freeGens (ts: Ty list) : string list =
    let found = List<string>()

    let rec go (t: Ty) =
        match t with
        | TGen n ->
            if not (found.Contains n) then
                found.Add n
        | TEnt(_, args) -> List.iter go args
        | TOpt t
        | TPtr(t, _)
        | TSlice(t, _)
        | TArr(t, _)
        | TTok(t, _) -> go t
        | TTuple ts -> List.iter go ts
        | TFn(args, ret)
        | TSlot(args, ret) ->
            List.iter go args
            go ret
        | TPrim _ -> ()

    List.iter go ts
    List.ofSeq found

/// The fields of a case: (name, type). Records have one case, named "".
let caseFields (t: Ty) (case: string) : (string * Ty) list =
    match t with
    | TEnt(e, args) ->
        match e.Cases |> List.tryFind (fun (c, _) -> c = case) with
        | Some(_, fs) ->
            if args.IsEmpty || args.Length <> e.TypeParams.Length then
                fs
            else
                let m = Map.ofList (List.zip e.TypeParams args)
                fs |> List.map (fun (f, ft) -> f, substTy m ft)
        | None -> fail None "internal: type %s has no case %s" e.Name case
    | TTuple ts -> ts |> List.mapi (fun i t -> string<int> i, t)
    | TOpt t ->
        if case = "Some" then
            [ ("Value", t) ]
        else
            []
    | _ -> []

let allCases (t: Ty) : string list =
    match t with
    | TEnt(e, _) -> e.Cases |> List.map fst
    | TOpt _ -> [ "None"; "Some" ]
    | _ -> [ "" ]

/// Can a constructor of `(t2, case2)` be built in a dead cell of `(t1, case1)`? Yes when the
/// fields have the same types. When it is the same case of the same generic type with other
/// type arguments, the two cells may or may not have the same layout: that is known when the
/// Zig is compiled, and the runtime only builds in the dead cell if they do.
let rec private hasRuntimeCyclicDep (t: Ty) : bool =
    match t with
    | TGen _
    | TFn _
    | TPrim("fable_rt.Exn" | "fable_rt.Obj") -> true
    | TEnt(e, args) ->
        e.Kind = KIface
        || e.Kind = KExn
        || e.ReachesOpaque
        || List.exists hasRuntimeCyclicDep args
    | TOpt x
    | TArr(x, _)
    | TPtr(x, _)
    | TSlice(x, _) -> hasRuntimeCyclicDep x
    | TTuple xs -> List.exists hasRuntimeCyclicDep xs
    | _ -> false

let private gcHeaderMode (t: Ty) : bool option =
    match t with
    | TEnt(e, args) ->
        if e.Cyclic then
            Some true
        elif e.ReachesOpaque then
            None
        elif e.TypeParams.IsEmpty then
            Some false
        elif List.exists hasRuntimeCyclicDep args then
            None
        else
            Some(List.exists mayHoldCyclic args)
    | _ -> None

let cellsMatchExact (t1: Ty, case1: string) (t2: Ty, case2: string) : bool =
    if tyKey t1 = tyKey t2 && case1 = case2 then
        true
    else
        let shape t case =
            caseFields t case |> List.map (snd >> tyKey) |> List.sort

        let compatGc =
            tyKey t1 = tyKey t2
            || (
                match gcHeaderMode t1, gcHeaderMode t2 with
                | Some g1, Some g2 -> g1 = g2
                | _ -> false
            )

        compatGc && shape t1 case1 = shape t2 case2

let private alignUp (n: int) (a: int) =
    if a <= 1 then
        n
    else
        ((n + a - 1) / a) * a

let private structLayout (fs: (int * int) list) : int * int =
    let sized = fs |> List.filter (fun (s, _) -> s > 0)

    if sized.IsEmpty then
        0, 1
    else
        let sorted = sized |> List.sortByDescending snd
        let total = sorted |> List.sumBy fst
        let maxA = sorted |> List.map snd |> List.max |> max 1
        alignUp total maxA, maxA

let rec private tyLayout (seen: Set<string>) (t: Ty) : (int * int) option =
    match t with
    | TPrim "void" -> Some(0, 1)
    | TPrim("bool" | "i8" | "u8") -> Some(1, 1)
    | TPrim("i16" | "u16" | "c_ushort") -> Some(2, 2)
    | TPrim("i32" | "u32" | "f32" | "c_int" | "c_uint") -> Some(4, 4)
    | TPrim("i64" | "u64" | "f64" | "isize" | "usize") -> Some(8, 8)
    | TPrim("i128" | "u128" | "f128") -> Some(16, 16)
    | TPrim("fable_rt.String" | "fable_rt.Exn" | "fable_rt.Obj" | "fable_rt.ThreadOf") -> Some(8, 8)
    | TPtr _ -> Some(8, 8)
    | TSlice _ -> Some(16, 8)
    | TArr(elem, n) -> tyLayout seen elem |> Option.map (fun (s, a) -> s * n, a)
    | TTuple ts ->
        let ls = ts |> List.map (tyLayout seen)

        if List.exists Option.isNone ls then
            None
        else
            Some(structLayout (List.choose id ls))
    | TEnt(e, _) when e.Kind = KRefRecord || e.Kind = KExn -> Some(8, 8)
    | TEnt(e, _) when e.Kind = KIface -> Some(16, 8)
    | TEnt(e, _) when e.Kind = KHeapUnion ->
        let anyPayload = e.Cases |> List.exists (fun (_, fs) -> not fs.IsEmpty)

        let tagSz =
            if e.Cases.Length <= 1 then
                0
            elif e.Cases.Length <= 256 then
                1
            else
                2

        if not anyPayload then
            Some(tagSz, max 1 tagSz)
        elif tagSz = 0 then
            Some(8, 8)
        else
            Some(16, 8)
    | TEnt(e, _) when e.Kind = KRecord ->
        if seen.Contains e.Name then
            None
        else
            let seen' = Set.add e.Name seen
            let fs = caseFields t "" |> List.map (snd >> tyLayout seen')

            if List.exists Option.isNone fs then
                None
            else
                Some(structLayout (List.choose id fs))
    | TEnt(e, _) when e.Kind = KValueUnion ->
        if seen.Contains e.Name then
            None
        elif e.Cases.IsEmpty then
            Some(0, 1)
        else
            let seen' = Set.add e.Name seen

            let caseLayouts =
                e.Cases
                |> List.map (fun (c, _) ->
                    let fs = caseFields t c |> List.map (snd >> tyLayout seen')

                    if List.exists Option.isNone fs then
                        None
                    else
                        Some(structLayout (List.choose id fs))
                )

            if List.exists Option.isNone caseLayouts then
                None
            else
                let ls = List.choose id caseLayouts
                let maxS = ls |> List.map fst |> List.max
                let maxPA = ls |> List.map snd |> List.max

                let tagSz =
                    if e.Cases.Length <= 1 then
                        0
                    elif e.Cases.Length <= 256 then
                        1
                    else
                        2

                let maxA = max (max 1 tagSz) maxPA
                Some(alignUp (maxS + tagSz) maxA, maxA)
    | TOpt inner ->
        match inner with
        | TPtr _
        | TEnt({ Kind = KRefRecord | KExn }, _) -> Some(8, 8)
        | _ -> tyLayout seen inner |> Option.map (fun (s, a) -> alignUp (s + 1) a, a)
    | _ -> None

let private cellLayoutWithGc (hasGc: bool) (t: Ty, case: string) : (int * int) option =
    let fs = caseFields t case |> List.map (snd >> tyLayout Set.empty)

    if List.exists Option.isNone fs then
        None
    else
        let hdr =
            if hasGc then
                [ 4, 4; 36, 4 ]
            else
                [ 4, 4 ]

        Some(structLayout (hdr @ List.choose id fs))

let cellsMatch (t1: Ty, case1: string) (t2: Ty, case2: string) : bool =
    let sameGenericEntCase () =
        not (freeGens [ t1; t2 ]).IsEmpty
        && (
            match t1, t2 with
            | TEnt(e1, _), TEnt(e2, _) -> obj.ReferenceEquals(e1, e2) && case1 = case2
            | _ -> false
        )

    if cellsMatchExact (t1, case1) (t2, case2) then
        true
    else
        match gcHeaderMode t1, gcHeaderMode t2 with
        | Some g1, Some g2 ->
            match cellLayoutWithGc g1 (t1, case1), cellLayoutWithGc g2 (t2, case2) with
            | Some l1, Some l2 -> l1 = l2
            | _ -> sameGenericEntCase ()
        | None, None when tyKey t1 = tyKey t2 ->
            match cellLayoutWithGc false (t1, case1), cellLayoutWithGc false (t2, case2) with
            | Some l1f, Some l2f when l1f = l2f ->
                match cellLayoutWithGc true (t1, case1), cellLayoutWithGc true (t2, case2) with
                | Some l1t, Some l2t -> l1t = l2t
                | _ -> sameGenericEntCase ()
            | Some _, Some _ -> false
            | _ -> sameGenericEntCase ()
        | _ -> sameGenericEntCase ()

type VarKind =
    | VLocal
    | VParam
    | VGlobal
    | VCapture
    /// `use` binding of a scope guard: disposed at the end of its scope
    | VUse

[<CustomEquality; NoComparison>]
type Var =
    {
        Id: int
        Base: string
        Ty: Ty
        Kind: VarKind
        FMutable: bool
    }

    override x.Equals(o) =
        match o with
        | :? Var as v -> v.Id = x.Id
        | _ -> false

    override x.GetHashCode() = x.Id

type Proj =
    | PField of string
    | PCase of string * string
    | PItem of int
    | PSome

type ArgUse =
    | UPlain
    | UKeep
    | UGive

type IfaceSource =
    | ISrcValue of Expr
    | ISrcCaptures of Expr list
    | ISrcUpcast of Expr

and [<NoEquality; NoComparison>] Expr =
    // ---- flat expressions (no control flow) ----
    | EVar of Var
    | ELit of string * Ty
    | EUnit
    | EPrim of string * Expr list * Ty
    /// a call of a function of the file (or `alias.name`), with its type arguments
    | ECall of string * Ty list * Expr list * Ty
    | ECallClo of Expr * Expr list * Ty
    /// Virtual method call through a class vtable: `fn` (borrowed), `self` (borrowed `Obj`),
    /// `args` (owned), result type.
    | ECallVt of Expr * Expr * Expr list * Ty
    /// a function value: the function of the file (or `alias.name`) it calls with its type
    /// arguments, the values it captures (they are that function's first parameters), and its
    /// type
    | EClosure of string * Ty list * Expr list * Ty
    /// stack-allocated known lambda passed to a non-escaping HOF parameter (captures borrowed)
    | EKnown of string * Ty list * Expr list * Ty
    /// stack-allocated known interface / object expression passed to a non-escaping HOF parameter
    | EKnownIface of Ty * IfaceSource * (string * (string * Ty list)) list * isOpt: bool
    /// explicit use marker ('p' / 'k' / 'g') recorded by Perceus on a call argument
    | EUse of ArgUse * Expr
    /// cross-file call whose result is assumed to borrow from parameter indices `indices` (acrossAssumed)
    | EAssumedRet of indices: int list * call: Expr
    /// a fat-pointer interface value backed by a class Obj / boxed value, captures, or upcast sub-interface
    | EIface of Ty * IfaceSource * (string * (string * Ty list)) list
    /// method call through a fat-pointer interface: `iface` (borrowed), `slot`, `args` (owned), result type
    | ECallIface of Expr * string * Expr list * Ty
    | ECon of Ty * string * Expr list * Var option
    | EGet of Expr * Proj * Ty
    | ETest of Expr * string * Ty
    | EAddr of Expr * bool
    | EDeref of Expr * Ty
    | EIndex of Expr * Expr * Ty
    /// `[<Emit>]`: Zig text with `$0`, `$1`, ... standing for the arguments
    | EEmit of string * Expr list * Ty
    /// a call into the runtime library that can raise: Zig text like `EEmit`, whose result is
    /// `fable_rt.Raised!T`
    | ERt of string * Expr list * Ty
    /// a new exception of the declared type, which owns the field values
    | EExnNew of Ent * Expr list
    /// is the exception of the declared type?
    | EExnTest of Expr * Ent
    /// a field of an exception that is of the declared type
    | EExnGet of Expr * Ent * string * Ty
    /// (after Perceus) a call that may raise, and what this function gives up if it does
    | EOnRaise of Expr * Var list
    /// Perceus: turn a borrowed value into an owned one
    | EDup of Expr * Ty
    // ---- control ----
    | ELet of Var * Expr * Expr
    | ESeq of Expr * Expr
    | EIf of Expr * Expr * Expr * Ty
    | EWhile of Expr * Expr
    | EFor of Var * Expr * Expr * bool * Expr
    | EAssign of Var * Expr
    | EStore of Expr * Expr
    /// Perceus: drop x; k
    | EDrop of Var * Expr
    /// Perceus: specialised drop of a dead value whose case is known; k
    | EUnpack of Unpack * Expr
    /// Perceus: a borrow outlives its owner and is consumed later, so it is retained now; k
    | EPromote of Var * Expr
    /// raise: the exception moves into the runtime's slot and the function is left. (The
    /// type is the one expected where the `raise` stands.)
    | ERaise of Expr * Ty
    /// try body / the variable that holds the caught exception / handler
    | ETry of Expr * Var * Expr * Ty

[<NoEquality; NoComparison>]
type Unpack =
    {
        Scrut: Var
        Case: string
        /// field -> the variable that takes ownership of it
        Moves: (string * Var) list
        /// managed fields that are dropped when the value was not shared
        Drops: (string * Ty) list
        /// reuse token (cells only)
        Token: Var option
        Heap: bool
    }

type Mode =
    | MPlain
    | MOwned
    | MBorrowed

/// Can a function raise?
type Raises =
    | RNever
    | RAlways
    /// only if one of these functions of other files (with these type arguments) can: that is
    /// known when the Zig is compiled
    | RDepends of (string * Ty list) list

[<ReferenceEquality>]
type FnInfo =
    {
        Name: string
        /// the type parameters of a generic function
        TypeParams: string list
        Params: Var list
        mutable Modes: Mode list
        Ret: Ty
        mutable Body: Expr
        /// Some [i; j]: the result is a borrow of parameters i and j (the callee does not dup
        /// it and the caller does not drop it)
        mutable RetFrom: int list option
        mutable Raises: Raises
        /// can it (or what it calls) assign a field of a reference record?
        mutable Stores: bool
        /// a lambda or a function declared inside another one: not visible to other files
        IsLocal: bool
        IsEntryPoint: bool
        Range: SourceLocation option
        /// parameter index -> does this function parameter never escape (eligible for callK)?
        mutable NoEscape: bool list
        /// second Perceus pass body for `callK`, when `NoEscape` has at least one true
        mutable BodyK: Expr option
        /// (stored field keys, calls callback, calls unknown external store)
        mutable StoreFacts: string list * bool * bool
        /// Cross-file callees whose `PRNever` Raises fact this function relied on
        mutable AssertedNoRaise: (string * Ty list) list
        /// Cross-file callees whose `Stores` facts this function relied on: (callee, disjoint field keys, check_ext_store)
        mutable AssertedStores: (string * string list * bool) list
        /// Part 3: does this function need a full `$tc` entry?
        mutable NeedsChain: bool
        /// Part 3: cross-file callees whose runtime `f$chain` determines whether this function needs `$tcfull`
        mutable PendingChainDeps: string list
        /// Part 3: second Perceus pass body for `$tcbody`, when `NeedsChain` or `PendingChainDeps` is non-empty
        mutable BodyTc: Expr option
    }

let rec typeOf (e: Expr) : Ty =
    match e with
    | EVar v -> v.Ty
    | ELit(_, t)
    | EPrim(_, _, t)
    | ECall(_, _, _, t)
    | ECallClo(_, _, t)
    | ECallVt(_, _, _, t)
    | EClosure(_, _, _, t)
    | EKnown(_, _, _, t)
    | EIface(t, _, _)
    | ECallIface(_, _, _, t)
    | ECon(t, _, _, _)
    | EGet(_, _, t)
    | EDeref(_, t)
    | EIndex(_, _, t)
    | EEmit(_, _, t)
    | ERt(_, _, t)
    | EExnGet(_, _, _, t)
    | ERaise(_, t)
    | ETry(_, _, _, t)
    | EDup(_, t) -> t
    | EKnownIface(t, _, _, isOpt) ->
        if isOpt then
            TOpt t
        else
            t
    | EUse(_, x)
    | EAssumedRet(_, x)
    | EOnRaise(x, _) -> typeOf x
    | EExnNew _ -> tExn
    | EUnit -> tVoid
    | EExnTest _
    | ETest _ -> tBool
    | EAddr(x, c) -> TPtr(typeOf x, c)
    | ELet(_, _, b)
    | ESeq(_, b)
    | EDrop(_, b)
    | EUnpack(_, b)
    | EPromote(_, b) -> typeOf b
    | EIf(_, _, _, t) -> t
    | EWhile _
    | EFor _
    | EAssign _
    | EStore _ -> tVoid

/// Is this a read of (or through) a field that can be assigned? What such a read yields may
/// be replaced in the record at any later time.
let rec touchesMutable (e: Expr) : bool =
    match e with
    | EUse(_, x) -> touchesMutable x
    | EGet(x, proj, _) ->
        (match proj, typeOf x with
         | PField f, TEnt(ent, _)
         // (the fields of an object, reached through a pointer to its class's part)
         | PField f, TPtr(TEnt(ent, _), _) -> List.contains f ent.MutableFields
         | _ -> false)
        || touchesMutable x
    | _ -> false

let isFlat (e: Expr) =
    match e with
    | ELet _
    | ESeq _
    | EIf _
    | EWhile _
    | EFor _
    | EAssign _
    | EStore _
    | EDrop _
    | EUnpack _
    | ERaise _
    | ETry _
    | EPromote _ -> false
    | _ -> true

/// Flat children in evaluation order.
let flatKids (e: Expr) : Expr list =
    match e with
    | EPrim(_, xs, _)
    | ECall(_, _, xs, _)
    | EEmit(_, xs, _)
    | ERt(_, xs, _)
    | EClosure(_, _, xs, _)
    | EKnown(_, _, xs, _)
    | EExnNew(_, xs)
    | ECon(_, _, xs, _) -> xs
    | ECallClo(f, xs, _) -> f :: xs
    | ECallVt(f, s, xs, _) -> f :: s :: xs
    | EIface(_, ISrcValue x, _)
    | EIface(_, ISrcUpcast x, _) -> [ x ]
    | EIface(_, ISrcCaptures xs, _) -> xs
    | EKnownIface(_, ISrcValue x, _, _)
    | EKnownIface(_, ISrcUpcast x, _, _) -> [ x ]
    | EKnownIface(_, ISrcCaptures xs, _, _) -> xs
    | ECallIface(r, _, xs, _) -> r :: xs
    | EExnTest(x, _)
    | EExnGet(x, _, _, _)
    | EUse(_, x)
    | EAssumedRet(_, x)
    | EOnRaise(x, _)
    | ERaise(x, _)
    | EGet(x, _, _)
    | ETest(x, _, _)
    | EAddr(x, _)
    | EDeref(x, _)
    | EDup(x, _) -> [ x ]
    | EIndex(a, b, _) -> [ a; b ]
    | _ -> []

let withFlatKids (e: Expr) (xs: Expr list) : Expr =
    match e, xs with
    | EPrim(op, _, t), _ -> EPrim(op, xs, t)
    | ECall(f, tys, _, t), _ -> ECall(f, tys, xs, t)
    | EEmit(m, _, t), _ -> EEmit(m, xs, t)
    | ERt(m, _, t), _ -> ERt(m, xs, t)
    | EClosure(f, tys, _, t), _ -> EClosure(f, tys, xs, t)
    | EKnown(f, tys, _, t), _ -> EKnown(f, tys, xs, t)
    | ECon(t, c, _, tok), _ -> ECon(t, c, xs, tok)
    | EExnNew(ent, _), _ -> EExnNew(ent, xs)
    | EExnTest(_, ent), [ x ] -> EExnTest(x, ent)
    | EExnGet(_, ent, f, t), [ x ] -> EExnGet(x, ent, f, t)
    | EUse(u, _), [ x ] -> EUse(u, x)
    | EAssumedRet(js, _), [ x ] -> EAssumedRet(js, x)
    | EOnRaise(_, ds), [ x ] -> EOnRaise(x, ds)
    | ERaise(_, t), [ x ] -> ERaise(x, t)
    | ECallClo(_, _, t), f :: rest -> ECallClo(f, rest, t)
    | ECallVt(_, _, _, t), f :: s :: rest -> ECallVt(f, s, rest, t)
    | EIface(t, ISrcValue _, s), [ x ] -> EIface(t, ISrcValue x, s)
    | EIface(t, ISrcUpcast _, s), [ x ] -> EIface(t, ISrcUpcast x, s)
    | EIface(t, ISrcCaptures _, s), _ -> EIface(t, ISrcCaptures xs, s)
    | EKnownIface(t, ISrcValue _, s, isOpt), [ x ] -> EKnownIface(t, ISrcValue x, s, isOpt)
    | EKnownIface(t, ISrcUpcast _, s, isOpt), [ x ] -> EKnownIface(t, ISrcUpcast x, s, isOpt)
    | EKnownIface(t, ISrcCaptures _, s, isOpt), _ -> EKnownIface(t, ISrcCaptures xs, s, isOpt)
    | ECallIface(_, slot, _, t), r :: rest -> ECallIface(r, slot, rest, t)
    | EGet(_, p, t), [ x ] -> EGet(x, p, t)
    | ETest(_, c, t), [ x ] -> ETest(x, c, t)
    | EAddr(_, c), [ x ] -> EAddr(x, c)
    | EDeref(_, t), [ x ] -> EDeref(x, t)
    | EDup(_, t), [ x ] -> EDup(x, t)
    | EIndex(_, _, t), [ a; b ] -> EIndex(a, b, t)
    | _ -> e

/// Direct variable uses.
let rec fv (e: Expr) : Set<int> =
    match e with
    | EVar v -> Set.singleton v.Id
    | ECon(_, _, xs, Some tok) -> Set.add tok.Id (xs |> List.map fv |> Set.unionMany)
    | ELet(v, r, b) -> Set.union (fv r) (Set.remove v.Id (fv b))
    | ESeq(a, b)
    | EWhile(a, b)
    | EStore(a, b) -> Set.union (fv a) (fv b)
    | EIf(c, t, f, _) -> Set.unionMany [ fv c; fv t; fv f ]
    | EFor(i, a, b, _, body) -> Set.unionMany [ fv a; fv b; Set.remove i.Id (fv body) ]
    | EAssign(v, r) -> Set.add v.Id (fv r)
    | ETry(b, v, h, _) -> Set.union (fv b) (Set.remove v.Id (fv h))
    | EOnRaise(x, ds) -> ds |> List.fold (fun s d -> Set.add d.Id s) (fv x)
    | EDrop(v, k)
    | EPromote(v, k) -> Set.add v.Id (fv k)
    | EUnpack(u, k) ->
        let s = Set.add u.Scrut.Id (fv k)
        let s = u.Moves |> List.fold (fun s (_, v) -> Set.add v.Id s) s

        match u.Token with
        | Some t -> Set.add t.Id s
        | None -> s
    | _ -> flatKids e |> List.map fv |> Set.unionMany

/// No side effects and no dependence on mutable state: may be dropped if unused.
let rec isPure (e: Expr) =
    match e with
    | EVar v -> not v.FMutable
    | ELit _
    | EUnit -> true
    | EPrim(("div" | "mod"), _, _) -> false // may trap
    | EPrim(_, xs, _) -> List.forall isPure xs
    // (a function value that captures nothing is a constant; one that captures allocates)
    | EClosure(_, _, xs, _) -> xs.IsEmpty
    | EKnown(_, _, xs, _) -> List.forall isPure xs
    | EKnownIface(_, ISrcValue x, _, _)
    | EKnownIface(_, ISrcUpcast x, _, _) -> isPure x
    | EKnownIface(_, ISrcCaptures xs, _, _) -> List.forall isPure xs
    | EUse(_, x) -> isPure x
    | EIface(_, ISrcCaptures [], _) -> true
    // (a constructor that allocates a cell is not pure)
    | ECon(TEnt({ Kind = KRefRecord }, _), _, _, _) -> false
    | ECon(t, _, xs, None) -> (not (isHeapTy t) || xs.IsEmpty) && List.forall isPure xs
    // (what a field that can be assigned holds depends on when it is read)
    | EGet(x, _, _) -> not (touchesMutable e) && isPure x
    | EExnTest(x, _)
    | EExnGet(x, _, _, _)
    | ETest(x, _, _) -> isPure x
    | _ -> false

/// Variables assigned somewhere in `e` (they are declared with `var`).
let rec assignedIn (e: Expr) : Set<int> =
    match e with
    | EAssign(v, r) -> Set.add v.Id (assignedIn r)
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b) -> Set.union (assignedIn r) (assignedIn b)
    | EIf(_, t, f, _) -> Set.union (assignedIn t) (assignedIn f)
    | EFor(_, _, _, _, body) -> assignedIn body
    | ETry(b, _, h, _) -> Set.union (assignedIn b) (assignedIn h)
    | EDrop(_, k)
    | EUnpack(_, k)
    | EPromote(_, k) -> assignedIn k
    | _ -> Set.empty

/// Is there an expression in `e` that satisfies `pred`?
let rec exists (pred: Expr -> bool) (e: Expr) : bool =
    pred e
    || (
        match e with
        | ELet(_, r, b) -> exists pred r || exists pred b
        | ESeq(a, b)
        | EWhile(a, b)
        | EStore(a, b) -> exists pred a || exists pred b
        | EIf(c, t, f, _) -> exists pred c || exists pred t || exists pred f
        | EFor(_, a, b, _, body) -> exists pred a || exists pred b || exists pred body
        | EAssign(_, r) -> exists pred r
        | ETry(b, _, h, _) -> exists pred b || exists pred h
        | EDrop(_, k)
        | EUnpack(_, k)
        | EPromote(_, k) -> exists pred k
        | _ -> flatKids e |> List.exists (exists pred)
    )

/// A name for the temporary that holds the value of `e`.
let rec tempName (e: Expr) =
    match e with
    | EAssumedRet(_, call) -> tempName call
    | ECall(f, _, _, _) -> f.Substring(f.LastIndexOf '.' + 1) + "_r"
    | ECon(_, c, _, _) when c <> "" -> c.ToLowerInvariant()
    | ECon(TTuple _, _, _, _) -> "tup"
    | ECon(TEnt(e, _), _, _, _) -> e.Name.Substring(e.Name.LastIndexOf '.' + 1).ToLowerInvariant()
    | _ -> "tmp"

/// Per-file state of the lowering: fresh variables and the functions produced so far.
/// A class that takes part in inheritance, as the file that declares it emits it: its type
/// (`Circle__type`), the struct of its chain of fields, .NET's name, its parent's type, and for
/// each class of its chain the table of virtual members: the table's type, and for each member
/// the function that implements it and the type of the function value (None: that class
/// introduces no virtual member, or this class is abstract).
type ObjDecl =
    {
        TypeName: string
        /// the class's type parameters: its object type is a function of them
        TypeParams: string list
        Chain: Ty
        DotnetName: string
        /// the parent's object type, as Zig text of a pointer to it
        Parent: string option
        /// each table: its type, and each slot with the function that fills it and that
        /// function's type arguments
        Tables: (Ty * (string * string * Ty list * Ty) list) option list
        /// the function of the class's `ToString` (its own or the nearest inherited one), and its
        /// type arguments
        ToString: (string * Ty list) option
        /// the functions of its `Equals`, `GetHashCode` and `IComparable.CompareTo` (its own or
        /// the nearest inherited ones), by the runtime's names of them
        Overrides: (string * string) list
        /// (an object expression's class) the functions of its table that call the function
        /// values it holds: name, pointer type of its fields, the Zig names of the structs of
        /// fields of its chain, the field, and the type of the function value
        Thunks: (string * Ty * string * string * Ty) list
        /// the interfaces the class implements, each with the slots of its table (as an
        /// interface value made of an object of the class has them): `o :?> I` finds them
        Ifaces: (Ty * (string * (string * Ty list)) list) list
    }

type CycleInfo =
    {
        Holds: bool
        Generic: bool
        Instantiated: bool
        Captures: bool
        CapGeneric: bool
        CapInstantiated: bool
    }

let emptyCycleInfo =
    {
        Holds = false
        Generic = false
        Instantiated = false
        Captures = false
        CapGeneric = false
        CapInstantiated = false
    }

type FileState() =
    let mutable varCounter = 0
    member val Fns = List<FnInfo>()
    /// a handler of the file can catch OutOfMemoryException (see fable_rt.oom_catchable)
    member val CatchesOom = false with get, set
    /// local generic values (`let f_opt = Some f`, generalized by F#) lifted as functions without
    /// parameters: each use calls it at its own type arguments
    member val GenericValues = HashSet<string>()
    /// type parameters a function does not take, known from those it does: `'c` of
    /// `'b :> Lazy<'c>` is the type argument of `'b` (see fable_rt.typeArg)
    member val GenAliases = Dictionary<string, Ty>()
    /// record and union types seen so far, by full name
    member val Ents = Dictionary<string, Ent>()
    /// the ones this file declares, in the order they were first needed
    member val LocalEnts = List<Ent>()
    /// module-level constants: name, type, literal text
    member val Consts = List<string * Ty * string>()

    /// the `[<StackArena(bytes)>]` functions: name, bytes
    member val Arenas = Dictionary<string, int>()

    /// the module-level values that are computed when the program starts: name, type, and the
    /// function that computes it
    member val Values = List<string * Ty * string>()
    /// the classes that take part in inheritance that this file declares
    member val Objs = List<ObjDecl>()
    /// the static fields of the types of the file (`static let`, `static member val`), as
    /// module-level values: `Type.field` to the value's name
    member val StaticFields = Dictionary<string, string>()
    /// the functions marked as tests (`[<Fact>]`, `[<Test>]`): what the test is called, and
    /// the function; each becomes a Zig `test` that `zig test` runs
    member val Tests = List<string * string>()
    /// what is known of such classes (see `objInfo`), by full name
    member val ObjInfos = Dictionary<string, obj>()
    /// imports of other files: path -> local alias
    member val Imports = Dictionary<string, string>()
    /// imports the program declares (`[<Import>]`, `[<ImportMember>]`, `[<ImportAll>]`): Zig
    /// files and packages written by hand, path -> local alias (none of the module values,
    /// `$init` and `$cycles` an F# file's Zig has)
    member val UserImports = Dictionary<string, string>()
    /// functions given to C (`[<UnmanagedCallersOnly(EntryPoint = "name")>]`): the function,
    /// and its name in C
    member val Exports = List<string * string>()
    /// the generated code calls the hand-written runtime (`fable_rt.zig`)
    member val UsesRuntime = false with get, set
    /// what the file's code does that lets a function value be part of a cycle (see
    /// `fable_rt.Cycles`)
    member val Cycles = emptyCycleInfo with get, set
    /// Does this file read an exception's `StackTrace`? (If no file of the program does,
    /// exceptions capture none.)
    member val UsesStackTrace = false with get, set
    /// Does this file reflect on values of unknown type? (Then each boxed type carries its
    /// reflection information, see `fable_rt.reflection`.)
    member val UsesReflection = false with get, set
    /// the .NET names of the records and unions this file declares, by their Zig name: what
    /// reflection says of them (`fable_type`): .NET's full name, and record or union
    member val NetTypes = Dictionary<string, string * string>()
    /// every variable made so far, by id
    member val Vars = Dictionary<int, Var>()
    /// chain types allocated via `objAlloc` (checked by cycle analysis)
    member val AllocChains = List<Ty>()
    /// how many type declarations are being mapped (they refer to each other)
    member val EntDepth = 0 with get, set
    /// 1-arg curried lifted lambda name -> companion 2-arg flat function name (sharing the same captures)
    member val Curried2 = Dictionary<string, string>()
    /// Opt-out of `$tc` / `tcode` emission for the whole file or specific functions (`[<NoTailCalls>]`)
    member val NoTailCallsFile = false with get, set
    member val NoTailCalls = HashSet<string>()

    member this.NewVar(baseName: string, ty: Ty, kind: VarKind, isMut: bool) : Var =
        varCounter <- varCounter + 1

        let v =
            {
                Id = varCounter
                Base = baseName
                Ty = ty
                Kind = kind
                FMutable = isMut
            }

        this.Vars[v.Id] <- v
        v

// ---- Zig names (the emitter's, also used where the lowering writes Zig text) ----

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
    zigKeywords.Contains s
    || System.Text.RegularExpressions.Regex.IsMatch(s, "^[iu][0-9]+$")

let cleanIdent (s: string) =
    let s = System.Text.RegularExpressions.Regex.Replace(s, "[^A-Za-z0-9_]", "_")

    // (`_` alone is not a name in Zig: F#'s `member _.X` names the object so)
    if s = "" || s = "_" then
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

/// A function or type of this file, or `alias.name` for one that another file declares.
let callTarget (f: string) =
    match f.IndexOf '.' with
    | -1 -> topIdent f
    | i -> f.Substring(0, i + 1) + topIdent (f.Substring(i + 1))

/// The Zig name of a field or of a union case.
let fieldIdent (s: string) =
    let c = cleanIdent s

    if isReservedIdent c then
        $"@\"%s{c}\""
    else
        c

/// A type parameter. (`'` cannot be part of a name that comes from F#, so a type parameter
/// never has the name of a value.)
let genName (n: string) = $"@\"'%s{n}\""

/// The Zig text of a type.
let rec zigType (t: Ty) : string =
    match t with
    | TPrim s -> s
    | TEnt(e, args) when
        e.Kind = KIface
        && e.Name.StartsWith("fable_iface_", System.StringComparison.Ordinal)
        ->
        let inner =
            args
            |> List.map zigType
            |> String.concat ", "
            |> sprintf "%s(%s)" (callTarget e.Name)

        $"fable_rt.Iface(%s{inner})"
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
    | TSlot(args, ret) ->
        let ps = "?*anyopaque" :: (args |> List.map zigType) |> String.concat ", "
        $"*const fn (%s{ps}) fable_rt.Raised!%s{zigType ret}"
    | TTok(t, "") -> "?" + zigType t
    | TTok(t, c) -> $"?*fable_rt.Cell(%s{zigType t}, .%s{fieldIdent c})"
