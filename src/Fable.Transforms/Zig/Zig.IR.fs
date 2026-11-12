/// The ownership IR of the Zig target: what Fable's AST is lowered to before borrow inference,
/// dup/drop insertion and emission. Flat expressions have no control flow; everything a
/// statement needs is let-bound first (ANF), so every pass can reason about one use at a time.
module rec Fable.Transforms.Zig.IR

open System.Collections.Generic
open Fable.AST

exception ZigError of message: string * range: SourceLocation option

let fail (r: SourceLocation option) fmt =
    Printf.kprintf (fun s -> raise (ZigError(s, r))) fmt

type EntKind =
    /// value struct
    | KRecord
    /// non-recursive union: unboxed `union(enum)`
    | KValueUnion
    /// recursive union or reference record: `union(enum)` of refcounted cell pointers
    | KHeapUnion

[<ReferenceEquality>]
type Ent =
    {
        Name: string
        Ref: Fable.EntityRef
        Kind: EntKind
        /// records: one case named ""
        mutable Cases: (string * (string * Ty) list) list
        /// holds references to cells: its values are dup'ed and dropped
        mutable Managed: bool
        mutable Copyable: bool
        /// declared in the file being compiled (its declaration is emitted there)
        IsLocal: bool
    }

type Ty =
    | TPrim of string
    | TEnt of Ent
    | TOpt of Ty
    | TTuple of Ty list
    | TPtr of Ty * isConst: bool
    | TSlice of Ty * isConst: bool
    | TArr of Ty * int
    | TFn of Ty list * Ty
    /// Perceus reuse token: `?*Ent_Case`
    | TTok of Ent * string

let tVoid = TPrim "void"
let tBool = TPrim "bool"
let tI32 = TPrim "i32"

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
    | TPrim s when s.Length > 1 && (s[0] = 'i' || s[0] = 'u') && System.Char.IsDigit s[1] -> int (s.Substring 1)
    | _ -> 0

let rec isManaged (t: Ty) =
    match t with
    | TEnt e -> e.Managed
    | TOpt t -> isManaged t
    | TTuple ts -> List.exists isManaged ts
    // (a function value may own an environment)
    | TFn _ -> true
    | _ -> false

let isHeapTy (t: Ty) =
    match t with
    | TEnt e -> e.Kind = KHeapUnion
    | _ -> false

/// Can a value be copied implicitly? Copying a handle shares the cell (count + 1).
let rec isCopyable (t: Ty) =
    match t with
    | TEnt e -> e.Copyable
    | TOpt t -> isCopyable t
    | TTuple ts -> List.forall isCopyable ts
    | _ -> true

/// A name for a type that is the same wherever the type is written.
let rec tyKey (t: Ty) : string =
    match t with
    | TPrim s -> s
    | TEnt e -> e.Ref.FullName
    | TOpt t -> "?" + tyKey t
    | TTuple ts -> "(" + (ts |> List.map tyKey |> String.concat ",") + ")"
    | TPtr(t, c) -> $"*%b{c}%s{tyKey t}"
    | TSlice(t, c) -> $"[]%b{c}%s{tyKey t}"
    | TArr(t, n) -> $"[%d{n}]%s{tyKey t}"
    | TFn(args, ret) -> "fn(" + (args |> List.map tyKey |> String.concat ",") + ")" + tyKey ret
    | TTok(e, c) -> $"tok:%s{e.Ref.FullName}.%s{c}"

/// The fields of a case: (name, type). Records have one case, named "".
let caseFields (t: Ty) (case: string) : (string * Ty) list =
    match t with
    | TEnt e ->
        match e.Cases |> List.tryFind (fun (c, _) -> c = case) with
        | Some(_, fs) -> fs
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
    | TEnt e -> e.Cases |> List.map fst
    | TOpt _ -> [ "None"; "Some" ]
    | _ -> [ "" ]

/// The layout of a cell: a dead cell can be built in again by a constructor of the same shape.
let cellShape (e: Ent) (case: string) : string =
    caseFields (TEnt e) case |> List.map (snd >> tyKey) |> String.concat ","

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

[<NoEquality; NoComparison>]
type Expr =
    // ---- flat expressions (no control flow) ----
    | EVar of Var
    | ELit of string * Ty
    | EUnit
    | EPrim of string * Expr list * Ty
    | ECall of string * Expr list * Ty
    | ECallClo of Expr * Expr list * Ty
    /// a function value: the function of the file (or `alias.name`) it calls, the values it
    /// captures (they are that function's first parameters), and its type
    | EClosure of string * Expr list * Ty
    | ECon of Ty * string * Expr list * Var option
    | EGet of Expr * Proj * Ty
    | ETest of Expr * string * Ty
    | EAddr of Expr * bool
    | EDeref of Expr * Ty
    | EIndex of Expr * Expr * Ty
    /// `[<Emit>]`: Zig text with `$0`, `$1`, ... standing for the arguments
    | EEmit of string * Expr list * Ty
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

[<ReferenceEquality>]
type FnInfo =
    {
        Name: string
        Params: Var list
        mutable Modes: Mode list
        Ret: Ty
        mutable Body: Expr
        /// Some [i; j]: the result is a borrow of parameters i and j (the callee does not dup
        /// it and the caller does not drop it)
        mutable RetFrom: int list option
        /// a lambda or a function declared inside another one: not visible to other files
        IsLocal: bool
        IsEntryPoint: bool
        Range: SourceLocation option
    }

let rec typeOf (e: Expr) : Ty =
    match e with
    | EVar v -> v.Ty
    | ELit(_, t)
    | EPrim(_, _, t)
    | ECall(_, _, t)
    | ECallClo(_, _, t)
    | EClosure(_, _, t)
    | ECon(t, _, _, _)
    | EGet(_, _, t)
    | EDeref(_, t)
    | EIndex(_, _, t)
    | EEmit(_, _, t)
    | EDup(_, t) -> t
    | EUnit -> tVoid
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
    | EPromote _ -> false
    | _ -> true

/// Flat children in evaluation order.
let flatKids (e: Expr) : Expr list =
    match e with
    | EPrim(_, xs, _)
    | ECall(_, xs, _)
    | EEmit(_, xs, _)
    | EClosure(_, xs, _)
    | ECon(_, _, xs, _) -> xs
    | ECallClo(f, xs, _) -> f :: xs
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
    | ECall(f, _, t), _ -> ECall(f, xs, t)
    | EEmit(m, _, t), _ -> EEmit(m, xs, t)
    | EClosure(f, _, t), _ -> EClosure(f, xs, t)
    | ECon(t, c, _, tok), _ -> ECon(t, c, xs, tok)
    | ECallClo(_, _, t), f :: rest -> ECallClo(f, rest, t)
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
    | EClosure(_, xs, _) -> xs.IsEmpty
    // (a constructor that allocates a cell is not pure)
    | ECon(t, _, xs, None) -> (not (isHeapTy t) || xs.IsEmpty) && List.forall isPure xs
    | EGet(x, _, _)
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
        | EDrop(_, k)
        | EUnpack(_, k)
        | EPromote(_, k) -> exists pred k
        | _ -> flatKids e |> List.exists (exists pred)
    )

/// A name for the temporary that holds the value of `e`.
let tempName (e: Expr) =
    match e with
    | ECall(f, _, _) -> f.Substring(f.LastIndexOf '.' + 1) + "_r"
    | ECon(_, c, _, _) when c <> "" -> c.ToLowerInvariant()
    | ECon(TTuple _, _, _, _) -> "tup"
    | ECon(TEnt e, _, _, _) -> e.Name.Substring(e.Name.LastIndexOf '.' + 1).ToLowerInvariant()
    | _ -> "tmp"

/// Per-file state of the lowering: fresh variables and the functions produced so far.
type FileState() =
    let mutable varCounter = 0
    member val Fns = List<FnInfo>()
    /// record and union types seen so far, by full name
    member val Ents = Dictionary<string, Ent>()
    /// the ones this file declares, in the order they were first needed
    member val LocalEnts = List<Ent>()
    /// module-level constants: name, type, literal text
    member val Consts = List<string * Ty * string>()
    /// imports of other files: path -> local alias
    member val Imports = Dictionary<string, string>()
    /// the generated code calls the hand-written runtime (`fable_rt.zig`)
    member val UsesRuntime = false with get, set
    /// every variable made so far, by id
    member val Vars = Dictionary<int, Var>()
    /// how many type declarations are being mapped (they refer to each other)
    member val EntDepth = 0 with get, set

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
