/// F#'s quotations (`<@ ... @>`), written in F# and compiled by the Zig target itself (see
/// List.fs): the nodes Fable's shared QuotationEmitter builds, the active patterns of
/// Patterns and DerivedPatterns over them, and an evaluator. A quotation, a node and a Var are
/// objects (`obj`), as the emitter types them; a node's children are objects too.
module Fable.Library.Zig.Quotation

open Fable.Core

/// A variable of a quotation: its name, the name of its type, whether it is mutable
type QVar =
    {
        name: string
        typ: string
        isMutable: bool
    }

type QNode =
    | QValue of value: obj * typ: string
    | QVarExpr of QVar
    | QLambda of QVar * obj
    | QApplication of obj * obj
    | QLet of QVar * obj * obj
    | QIfThenElse of obj * obj * obj
    | QCall of instance: obj * methodName: string * args: obj[] * declaringType: string
    | QSequential of obj * obj
    | QNewTuple of obj[]
    | QNewRecord of string[] * obj[]
    | QNewList of obj * obj
    | QTupleGet of obj * int
    | QUnionTag of obj
    | QUnionField of obj * int
    | QFieldGet of obj * string
    | QFieldSet of obj * string * obj
    | QVarSet of obj * obj

let private node (e: obj) : QNode = unbox<QNode> e

/// (the library's List module takes no array nor ResizeArray)
let private listOfArray (xs: obj[]) : obj list =
    let mutable acc = []

    for i in xs.Length - 1 .. -1 .. 0 do
        acc <- xs.[i] :: acc

    acc

let private joinTexts (xs: obj[]) (f: obj -> string) : string =
    let sb = System.Text.StringBuilder()

    for i in 0 .. xs.Length - 1 do
        if i > 0 then
            sb.Append(", ") |> ignore

        sb.Append(f xs.[i]) |> ignore

    sb.ToString()

let private mk (n: QNode) : obj = box n

#if FABLE_COMPILER
/// A Type of the name the emitter gives (`int32`, `string`, a type's full name)
[<Emit("fable_rt.reflect.typeNamed($0)")>]
let private typeNamed (_name: string) : System.Type = Util.nativeOnly

/// (a PropertyInfo of nothing: a quotation keeps a property's name only)
[<Emit("fable_rt.reflect.nullProperty()")>]
let private noProperty () : System.Reflection.PropertyInfo = Util.nativeOnly

/// A tuple of boxed items, which `unbox` makes the tuple of their types
[<Emit("try fable_rt.reflect.looseTuple($0)")>]
let private looseTuple (_items: obj[]) : obj = Util.nativeOnly
#else
let private typeNamed (_name: string) : System.Type = typeof<obj>
let private noProperty () : System.Reflection.PropertyInfo = null
let private looseTuple (items: obj[]) : obj = box items
#endif

// ---- making ----

let mkQuotVar (name: string) (typ: string) (isMutable: bool) : obj =
    box
        {
            name = name
            typ = typ
            isMutable = isMutable
        }

let varGetName (v: obj) : string = (unbox<QVar> v).name
let varGetType (v: obj) : System.Type = typeNamed (unbox<QVar> v).typ
let varGetIsMutable (v: obj) : bool = (unbox<QVar> v).isMutable

let mkValue (value: obj) (typ: string) : obj = mk (QValue(value, typ))
let mkNull (typ: string) : obj = mk (QValue(null, typ))
let mkVar (v: obj) : obj = mk (QVarExpr(unbox v))
let mkLambda (v: obj) (body: obj) : obj = mk (QLambda(unbox v, body))
let mkApplication (f: obj) (arg: obj) : obj = mk (QApplication(f, arg))
let mkLet (v: obj) (value: obj) (body: obj) : obj = mk (QLet(unbox v, value, body))
let mkIfThenElse (g: obj) (t: obj) (e: obj) : obj = mk (QIfThenElse(g, t, e))

let mkCall (instance: obj) (methodName: string) (args: obj[]) (declaringType: string) : obj =
    mk (QCall(instance, methodName, args, declaringType))

let mkSequential (a: obj) (b: obj) : obj = mk (QSequential(a, b))
let mkNewTuple (items: obj[]) : obj = mk (QNewTuple items)

let mkNewRecord (fieldNames: obj[]) (values: obj[]) : obj =
    mk (QNewRecord(fieldNames |> Array.map unbox<string>, values))

let mkNewList (head: obj) (tail: obj) : obj = mk (QNewList(head, tail))
let mkTupleGet (e: obj) (index: int) : obj = mk (QTupleGet(e, index))
let mkUnionTag (e: obj) : obj = mk (QUnionTag e)
let mkUnionField (e: obj) (index: int) : obj = mk (QUnionField(e, index))
let mkFieldGet (e: obj) (name: string) : obj = mk (QFieldGet(e, name))
let mkFieldSet (e: obj) (name: string) (value: obj) : obj = mk (QFieldSet(e, name, value))
let mkVarSet (target: obj) (value: obj) : obj = mk (QVarSet(target, value))

// ---- Patterns ----

/// (the instance of a call or a property: none for a static one)
let private instanceOf (instance: obj) : obj option =
    match node instance with
    | QValue(_, "novalue") -> None
    | _ -> Some instance

let isValue (e: obj) : (obj * System.Type) option =
    match node e with
    | QValue(_, "novalue") -> None
    | QValue(v, t) -> Some(v, typeNamed t)
    | _ -> None

let isVar (e: obj) : obj option =
    match node e with
    | QVarExpr v -> Some(box v)
    | _ -> None

let isLambda (e: obj) : (obj * obj) option =
    match node e with
    | QLambda(v, body) -> Some(box v, body)
    | _ -> None

let isApplication (e: obj) : (obj * obj) option =
    match node e with
    | QApplication(f, a) -> Some(f, a)
    | _ -> None

let isLet (e: obj) : (obj * obj * obj) option =
    match node e with
    | QLet(v, value, body) -> Some(box v, value, body)
    | _ -> None

let isIfThenElse (e: obj) : (obj * obj * obj) option =
    match node e with
    | QIfThenElse(g, t, f) -> Some(g, t, f)
    | _ -> None

let isCall (e: obj) : (obj option * string * obj list) option =
    match node e with
    | QCall(instance, m, args, _) -> Some(instanceOf instance, m, listOfArray args)
    | _ -> None

let isSequential (e: obj) : (obj * obj) option =
    match node e with
    | QSequential(a, b) -> Some(a, b)
    | _ -> None

let isNewTuple (e: obj) : obj list option =
    match node e with
    | QNewTuple items -> Some(listOfArray items)
    | _ -> None

let isNewRecord (e: obj) : (System.Type * obj list) option =
    match node e with
    | QNewRecord(_, values) -> Some(typeNamed "record", listOfArray values)
    | _ -> None

let isTupleGet (e: obj) : (obj * int) option =
    match node e with
    | QTupleGet(t, i) -> Some(t, i)
    | _ -> None

let isFieldGet (e: obj) : (obj option * System.Reflection.PropertyInfo * obj list) option =
    match node e with
    | QFieldGet(instance, _) -> Some(instanceOf instance, noProperty (), [])
    | _ -> None

// ---- DerivedPatterns ----

let private boolValue (e: obj) (b: bool) =
    match node e with
    | QValue(v, _) when not (isNull v) ->
        (match v with
         | :? bool as x -> x = b
         | _ -> false)
    | _ -> false

/// `a && b`: `if a then b else false` (or the operator itself)
let isAndAlso (e: obj) : (obj * obj) option =
    match node e with
    | QIfThenElse(a, b, f) when boolValue f false -> Some(a, b)
    | QCall(_, "op_BooleanAnd", args, _) when args.Length = 2 -> Some(args.[0], args.[1])
    | _ -> None

/// `a || b`: `if a then true else b` (or the operator itself)
let isOrElse (e: obj) : (obj * obj) option =
    match node e with
    | QIfThenElse(a, t, b) when boolValue t true -> Some(a, b)
    | QCall(_, "op_BooleanOr", args, _) when args.Length = 2 -> Some(args.[0], args.[1])
    | _ -> None

/// `SpecificCall <@ f @> e`: a call of the method the template calls (under its lambdas)
let isSpecificCall (template: obj) (e: obj) : (obj option * System.Type list * obj list) option =
    let rec templateCall (t: obj) =
        match node t with
        | QLambda(_, body) -> templateCall body
        | QCall(_, m, _, d) -> Some(m, d)
        | _ -> None

    match templateCall template, node e with
    | Some(m, d), QCall(instance, m2, args, d2) when m = m2 && d = d2 -> Some(instanceOf instance, [], listOfArray args)
    | _ -> None

// ---- the methods of Expr ----

let getType (e: obj) : System.Type =
    match node e with
    | QValue(_, t) -> typeNamed t
    | QVarExpr v -> typeNamed v.typ
    | _ -> typeNamed "obj"

/// `e.GetFreeVars()`: the variables it uses that it does not bind, in the order first used
let getFreeVarsList (e: obj) : obj list =
    let found = ResizeArray<obj>()
    let names = System.Collections.Generic.HashSet<string>()

    let rec walk (bound: string list) (x: obj) =
        let walkAll = Array.iter (walk bound)

        match node x with
        | QValue _ -> ()
        | QVarExpr v ->
            if not (List.contains v.name bound) && names.Add v.name then
                found.Add(box v)
        | QLambda(v, body) -> walk (v.name :: bound) body
        | QLet(v, value, body) ->
            walk bound value
            walk (v.name :: bound) body
        | QApplication(a, b)
        | QSequential(a, b)
        | QNewList(a, b)
        | QVarSet(a, b) ->
            walk bound a
            walk bound b
        | QIfThenElse(a, b, c) ->
            walk bound a
            walk bound b
            walk bound c
        | QCall(instance, _, args, _) ->
            walk bound instance
            walkAll args
        | QNewTuple items
        | QNewRecord(_, items) -> walkAll items
        | QTupleGet(a, _)
        | QUnionTag a
        | QUnionField(a, _)
        | QFieldGet(a, _) -> walk bound a
        | QFieldSet(a, _, b) ->
            walk bound a
            walk bound b

    walk [] e
    listOfArray (found.ToArray())

#if FABLE_COMPILER
let getFreeVars (e: obj) : Fable.Library.Zig.Seq.SeqOf<obj> =
    Fable.Library.Zig.Seq.ofList (getFreeVarsList e)
#else
let getFreeVars (e: obj) : seq<obj> = Seq.ofList (getFreeVarsList e)
#endif

/// `e.Substitute(f)`: each free variable that `f` gives an expression for, replaced by it
let substitute (e: obj) (f: obj -> obj option) : obj =
    let rec go (bound: string list) (x: obj) : obj =
        let all = Array.map (go bound)

        match node x with
        | QValue _ -> x
        | QVarExpr v when not (List.contains v.name bound) ->
            match f (box v) with
            | Some r -> r
            | None -> x
        | QVarExpr _ -> x
        | QLambda(v, body) -> mk (QLambda(v, go (v.name :: bound) body))
        | QLet(v, value, body) -> mk (QLet(v, go bound value, go (v.name :: bound) body))
        | QApplication(a, b) -> mk (QApplication(go bound a, go bound b))
        | QSequential(a, b) -> mk (QSequential(go bound a, go bound b))
        | QNewList(a, b) -> mk (QNewList(go bound a, go bound b))
        | QVarSet(a, b) -> mk (QVarSet(go bound a, go bound b))
        | QIfThenElse(a, b, c) -> mk (QIfThenElse(go bound a, go bound b, go bound c))
        | QCall(instance, m, args, d) -> mk (QCall(go bound instance, m, all args, d))
        | QNewTuple items -> mk (QNewTuple(all items))
        | QNewRecord(names, items) -> mk (QNewRecord(names, all items))
        | QTupleGet(a, i) -> mk (QTupleGet(go bound a, i))
        | QUnionTag a -> mk (QUnionTag(go bound a))
        | QUnionField(a, i) -> mk (QUnionField(go bound a, i))
        | QFieldGet(a, n) -> mk (QFieldGet(go bound a, n))
        | QFieldSet(a, n, b) -> mk (QFieldSet(go bound a, n, go bound b))

    go [] e

/// `e.ToString()`: as F# writes a quotation (`Call (None, op_Addition, [Value (1), Value (2)])`)
let rec exprToString (e: obj) : string =
    let list (xs: obj[]) = "[" + joinTexts xs exprToString + "]"

    let valueText (v: obj) =
        if isNull v then
            "<null>"
        else
            match v with
            | :? string as s -> "\"" + s + "\""
            | _ -> string v

    match node e with
    | QValue(_, "novalue") -> "None"
    | QValue(v, _) -> "Value (" + valueText v + ")"
    | QVarExpr v -> v.name
    | QLambda(v, body) -> "Lambda (" + v.name + ", " + exprToString body + ")"
    | QApplication(a, b) -> "Application (" + exprToString a + ", " + exprToString b + ")"
    | QLet(v, value, body) -> "Let (" + v.name + ", " + exprToString value + ", " + exprToString body + ")"
    | QIfThenElse(a, b, c) ->
        "IfThenElse ("
        + exprToString a
        + ", "
        + exprToString b
        + ", "
        + exprToString c
        + ")"
    | QCall(instance, m, args, _) ->
        let inst =
            match instanceOf instance with
            | Some i -> "Some (" + exprToString i + ")"
            | None -> "None"

        "Call (" + inst + ", " + m + ", " + list args + ")"
    | QSequential(a, b) -> "Sequential (" + exprToString a + ", " + exprToString b + ")"
    | QNewTuple items -> "NewTuple (" + joinTexts items exprToString + ")"
    | QNewRecord(_, items) -> "NewRecord (" + joinTexts items exprToString + ")"
    | QNewList(a, b) -> "NewUnionCase (Cons, " + exprToString a + ", " + exprToString b + ")"
    | QTupleGet(a, i) -> "TupleGet (" + exprToString a + ", " + string i + ")"
    | QUnionTag a -> "UnionTag (" + exprToString a + ")"
    | QUnionField(a, i) -> "UnionField (" + exprToString a + ", " + string i + ")"
    | QFieldGet(a, n) -> "PropertyGet (" + exprToString a + ", " + n + ")"
    | QFieldSet(a, n, b) -> "PropertySet (" + exprToString a + ", " + n + ", " + exprToString b + ")"
    | QVarSet(a, b) -> "VarSet (" + exprToString a + ", " + exprToString b + ")"

// ---- evaluation ----

let private notSupported (what: string) : 'a =
    raise (System.NotSupportedException("The quotation evaluator does not support " + what + "."))

/// An operator of numbers or strings, on boxed values
let private arith (op: string) (a: obj) (b: obj) : obj =
    match a, b with
    | (:? int as x), (:? int as y) ->
        match op with
        | "op_Addition" -> box (x + y)
        | "op_Subtraction" -> box (x - y)
        | "op_Multiply" -> box (x * y)
        | "op_Division" -> box (x / y)
        | "op_Modulus" -> box (x % y)
        | _ -> notSupported op
    | (:? int64 as x), (:? int64 as y) ->
        match op with
        | "op_Addition" -> box (x + y)
        | "op_Subtraction" -> box (x - y)
        | "op_Multiply" -> box (x * y)
        | "op_Division" -> box (x / y)
        | "op_Modulus" -> box (x % y)
        | _ -> notSupported op
    | (:? float as x), (:? float as y) ->
        match op with
        | "op_Addition" -> box (x + y)
        | "op_Subtraction" -> box (x - y)
        | "op_Multiply" -> box (x * y)
        | "op_Division" -> box (x / y)
        | "op_Modulus" -> box (x % y)
        | _ -> notSupported op
    | (:? string as x), (:? string as y) when op = "op_Addition" -> box (x + y)
    | _ -> notSupported (op + " of these values")

/// A comparison of boxed values
let private comparison (op: string) (a: obj) (b: obj) : obj =
    let c =
        match a, b with
        | (:? int as x), (:? int as y) -> compare x y
        | (:? int64 as x), (:? int64 as y) -> compare x y
        | (:? float as x), (:? float as y) -> compare x y
        | (:? string as x), (:? string as y) -> System.String.CompareOrdinal(x, y)
        | (:? bool as x), (:? bool as y) -> compare x y
        | _ -> notSupported (op + " of these values")

    box (
        match op with
        | "op_Equality" -> c = 0
        | "op_Inequality" -> c <> 0
        | "op_LessThan" -> c < 0
        | "op_LessThanOrEqual" -> c <= 0
        | "op_GreaterThan" -> c > 0
        | _ -> c >= 0
    )

/// `LeafExpressionConverter.EvaluateQuotation e`: the value, boxed
let evaluate (e: obj) : obj =
    let rec eval (env: (string * obj) list) (x: obj) : obj =
        match node x with
        | QValue(v, _) -> v
        | QVarExpr v ->
            match env |> List.tryFind (fun (n, _) -> n = v.name) with
            | Some(_, value) -> value
            | None -> notSupported ("the free variable " + v.name)
        | QLet(v, value, body) -> eval ((v.name, eval env value) :: env) body
        | QIfThenElse(g, t, f) ->
            if unbox<bool>(eval env g) then
                eval env t
            else
                eval env f
        | QSequential(a, b) ->
            eval env a |> ignore
            eval env b
        | QLambda(v, body) -> box (fun (arg: obj) -> eval ((v.name, arg) :: env) body)
        | QApplication(f, a) ->
            let fn = unbox<obj -> obj>(eval env f)
            fn (eval env a)
        | QNewTuple items -> looseTuple (items |> Array.map (eval env))
        | QCall(_, m, args, _) ->
            let vals = args |> Array.map (eval env)

            let two = vals.Length = 2
            let one = vals.Length = 1

            match m with
            | "op_Addition"
            | "op_Subtraction"
            | "op_Multiply"
            | "op_Division"
            | "op_Modulus" when two -> arith m vals.[0] vals.[1]
            | "op_Equality"
            | "op_Inequality"
            | "op_LessThan"
            | "op_LessThanOrEqual"
            | "op_GreaterThan"
            | "op_GreaterThanOrEqual" when two -> comparison m vals.[0] vals.[1]
            | "op_UnaryNegation" when one ->
                match vals.[0] with
                | :? int as v -> box (-v)
                | :? int64 as v -> box (-v)
                | :? float as v -> box (-v)
                | _ -> notSupported m
            | "op_BooleanAnd" when two -> box (unbox<bool> vals.[0] && unbox<bool> vals.[1])
            | "op_BooleanOr" when two -> box (unbox<bool> vals.[0] || unbox<bool> vals.[1])
            | "Not" when one -> box (not (unbox<bool> vals.[0]))
            | _ -> notSupported ("the call of " + m)
        | _ -> notSupported "this expression"

    eval [] e
