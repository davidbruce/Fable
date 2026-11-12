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
        mutable Managed: bool
        mutable DropAlloc: bool
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
    | _ -> false

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
    | ECon of Ty * string * Expr list * Var option
    | EGet of Expr * Proj * Ty
    | ETest of Expr * string * Ty
    | EAddr of Expr * bool
    | EDeref of Expr * Ty
    | EIndex of Expr * Expr * Ty
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
        mutable NeedsAlloc: bool
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
    | ECon(t, _, _, _)
    | EGet(_, _, t)
    | EDeref(_, t)
    | EIndex(_, _, t)
    | EDup(_, t) -> t
    | EUnit -> tVoid
    | ETest _ -> tBool
    | EAddr(x, c) -> TPtr(typeOf x, c)
    | ELet(_, _, b)
    | ESeq(_, b)
    | EDrop(_, b) -> typeOf b
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
    | EDrop _ -> false
    | _ -> true

/// Flat children in evaluation order.
let flatKids (e: Expr) : Expr list =
    match e with
    | EPrim(_, xs, _)
    | ECall(_, xs, _)
    | ECon(_, _, xs, _) -> xs
    | ECallClo(f, xs, _) -> f :: xs
    | EGet(x, _, _)
    | ETest(x, _, _)
    | EAddr(x, _)
    | EDeref(x, _)
    | EDup(x, _) -> [ x ]
    | EIndex(a, b, _) -> [ a; b ]
    | _ -> []

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
    | EDrop(v, k) -> Set.add v.Id (fv k)
    | _ -> flatKids e |> List.map fv |> Set.unionMany

/// No side effects and no dependence on mutable state: may be dropped if unused.
let rec isPure (e: Expr) =
    match e with
    | EVar v -> not v.FMutable
    | ELit _
    | EUnit -> true
    | EPrim(("div" | "mod"), _, _) -> false // may trap
    | EPrim(_, xs, _)
    | ECon(_, _, xs, _) -> List.forall isPure xs
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
    | EDrop(_, k) -> assignedIn k
    | _ -> Set.empty

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

    member _.NewVar(baseName: string, ty: Ty, kind: VarKind, isMut: bool) : Var =
        varCounter <- varCounter + 1

        {
            Id = varCounter
            Base = baseName
            Ty = ty
            Kind = kind
            FMutable = isMut
        }
