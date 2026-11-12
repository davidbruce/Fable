/// Lowering: Fable AST -> ownership IR. Anything with control flow or effects that sits in an
/// argument position is let-bound first (ANF), keeping F# evaluation order.
module Fable.Transforms.Zig.Lower

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR

type MemberKind =
    | MFunction
    | MConst of Ty

type Ctx =
    {
        Com: Compiler
        State: FileState
        /// locals in scope (Fable gives every local a name that is unique in its function)
        Vars: Dictionary<string, Var>
        /// the functions and constants this file declares
        Members: Dictionary<string, MemberKind>
        DecisionTargets: (Fable.Ident list * Fable.Expr) list
    }

let private exprKind (e: Fable.Expr) =
    match e with
    | Fable.Value _ -> "this kind of value"
    | Fable.Lambda _
    | Fable.Delegate _ -> "function values"
    | Fable.ObjectExpr _ -> "object expressions"
    | Fable.TypeCast _ -> "this type conversion"
    | Fable.Test _ -> "type and pattern tests"
    | Fable.Call _ -> "this kind of call"
    | Fable.CurriedApply _ -> "applying a function value"
    | Fable.Import _ -> "imported values"
    | Fable.Emit _ -> "Emit"
    | Fable.LetRec _ -> "local recursive functions"
    | Fable.Get _ -> "field, index and property access"
    | Fable.Set _ -> "this kind of assignment"
    | Fable.TryCatch _ -> "try/with and try/finally"
    | Fable.Extended _ -> "raise"
    | _ -> "this construct"

/// Does a record or union contain itself, directly or through other records and unions?
let private reachesSelf (com: Compiler) (start: Fable.Entity) : bool =
    let seen = HashSet<string>()

    let rec typeRefs (t: Fable.Type) : Fable.EntityRef list =
        match t with
        | Fable.DeclaredType(e, gen) -> e :: List.collect typeRefs gen
        | _ -> List.collect typeRefs t.Generics

    let fieldTypes (ent: Fable.Entity) =
        if ent.IsFSharpUnion then
            ent.UnionCases
            |> List.collect (fun c -> c.UnionCaseFields |> List.map (fun f -> f.FieldType))
        else
            ent.FSharpFields |> List.map (fun f -> f.FieldType)

    let rec go (ent: Fable.Entity) =
        fieldTypes ent
        |> List.collect typeRefs
        |> List.exists (fun r ->
            r.FullName = start.FullName
            || (seen.Add r.FullName
                && (
                    match com.TryGetEntity r with
                    | Some e when e.IsFSharpRecord || e.IsFSharpUnion -> go e
                    | _ -> false
                ))
        )

    go start

let rec mapType (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty =
    match t with
    | Fable.Unit -> tVoid
    | Fable.Boolean -> tBool
    | Fable.Char -> TPrim "u16"
    | Fable.Number(kind, _) ->
        match kind with
        | Int8 -> TPrim "i8"
        | UInt8 -> TPrim "u8"
        | Int16 -> TPrim "i16"
        | UInt16 -> TPrim "u16"
        | Int32 -> TPrim "i32"
        | UInt32 -> TPrim "u32"
        | Int64 -> TPrim "i64"
        | UInt64 -> TPrim "u64"
        | Int128 -> TPrim "i128"
        | UInt128 -> TPrim "u128"
        | NativeInt -> TPrim "isize"
        | UNativeInt -> TPrim "usize"
        | Float16 -> TPrim "f16"
        | Float32 -> TPrim "f32"
        | Float64 -> TPrim "f64"
        | BigInt -> fail r "the Zig target does not support bigint yet"
        | Decimal -> fail r "the Zig target does not support decimal yet"
    | Fable.String -> fail r "the Zig target does not support strings yet"
    | Fable.LambdaType _
    | Fable.DelegateType _ -> fail r "the Zig target does not support function values yet"
    | Fable.Tuple(ts, _) -> TTuple(ts |> List.map (mapType ctx r))
    | Fable.Option(t, _) -> TOpt(mapType ctx r t)
    | Fable.DeclaredType(ent, genArgs) -> TEnt(entOf ctx r ent genArgs)
    | _ -> fail r "the Zig target does not support this type yet (%A)" t

/// The record or union behind an entity reference. Immutable, non-recursive records and
/// unions are plain Zig values: a `struct`, or a `union(enum)` with one payload per case.
and entOf (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) (genArgs: Fable.Type list) : Ent =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e -> e
    | _ ->
        let ent =
            match ctx.Com.TryGetEntity entRef with
            | Some e -> e
            | None -> fail r "the Zig target cannot find the type %s" entRef.FullName

        if not (ent.IsFSharpRecord || ent.IsFSharpUnion) then
            fail r "the Zig target does not support the type %s yet" entRef.FullName

        if not genArgs.IsEmpty || not ent.GenericParameters.IsEmpty then
            fail r "the Zig target does not support generic types yet (%s)" ent.DisplayName

        if reachesSelf ctx.Com ent then
            fail
                r
                "the Zig target does not support recursive types yet (%s): they need the reference-counting runtime"
                ent.DisplayName

        if
            ent.IsFSharpRecord
            && not ent.IsValueType
            && ent.FSharpFields |> List.exists (fun f -> f.IsMutable)
        then
            fail
                r
                "the Zig target does not support records with mutable fields yet (%s): they need the reference-counting runtime"
                ent.DisplayName

        // a name in this file, or `alias.name` for a type another file declares
        let name, isLocal =
            match FSharp2Fable.Util.entityIdent ctx.Com entRef with
            | Fable.IdentExpr id -> id.Name, true
            | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
            | _ -> fail r "the Zig target cannot reference the type %s" entRef.FullName

        let e =
            {
                Name = name
                Ref = entRef
                Kind =
                    if ent.IsFSharpUnion then
                        KValueUnion
                    else
                        KRecord
                Cases = []
                Managed = false
                DropAlloc = false
                Copyable = true
                IsLocal = isLocal
            }

        ctx.State.Ents[entRef.FullName] <- e

        try
            e.Cases <-
                if ent.IsFSharpUnion then
                    ent.UnionCases
                    |> List.map (fun c ->
                        c.Name, c.UnionCaseFields |> List.map (fun f -> f.Name, mapType ctx r f.FieldType)
                    )
                else
                    [
                        "", ent.FSharpFields |> List.map (fun f -> f.Name, mapType ctx r f.FieldType)
                    ]
        with _ ->
            ctx.State.Ents.Remove entRef.FullName |> ignore
            reraise ()

        if isLocal then
            ctx.State.LocalEnts.Add e

        e

and importAlias (ctx: Ctx) (path: string) =
    match ctx.State.Imports.TryGetValue path with
    | true, alias -> alias
    | _ ->
        let fileName = System.IO.Path.GetFileNameWithoutExtension(path)

        let baseName =
            "m_"
            + System.Text.RegularExpressions.Regex.Replace(fileName.Replace(".fs", ""), "[^A-Za-z0-9_]", "_")

        let mutable alias = baseName
        let mutable i = 1

        while ctx.State.Imports.ContainsValue alias do
            alias <- $"%s{baseName}_%d{i}"
            i <- i + 1

        ctx.State.Imports[path] <- alias
        alias

let private isUnit (t: Fable.Type) =
    match t with
    | Fable.Unit -> true
    | _ -> false

let private floatLit (ty: string) (x: float) =
    if System.Double.IsNaN x then
        $"std.math.nan(%s{ty})"
    elif System.Double.IsPositiveInfinity x then
        $"std.math.inf(%s{ty})"
    elif System.Double.IsNegativeInfinity x then
        $"(-std.math.inf(%s{ty}))"
    else
        let s = x.ToString("R", System.Globalization.CultureInfo.InvariantCulture)

        if s.Contains "." || s.Contains "E" || s.Contains "e" then
            s
        else
            s + ".0"

let private numberLit (r: SourceLocation option) (v: Fable.NumberValue) : string * Ty =
    match v with
    | Fable.NumberValue.Int8 x -> string<sbyte> x, TPrim "i8"
    | Fable.NumberValue.UInt8 x -> string<byte> x, TPrim "u8"
    | Fable.NumberValue.Int16 x -> string<int16> x, TPrim "i16"
    | Fable.NumberValue.UInt16 x -> string<uint16> x, TPrim "u16"
    | Fable.NumberValue.Int32 x -> string<int> x, tI32
    | Fable.NumberValue.UInt32 x -> string<uint32> x, TPrim "u32"
    | Fable.NumberValue.Int64 x -> string<int64> x, TPrim "i64"
    | Fable.NumberValue.UInt64 x -> string<uint64> x, TPrim "u64"
    | Fable.NumberValue.NativeInt x -> string<int64>(int64 x), TPrim "isize"
    | Fable.NumberValue.UNativeInt x -> string<uint64>(uint64 x), TPrim "usize"
    | Fable.NumberValue.Float32 x -> floatLit "f32" (float x), TPrim "f32"
    | Fable.NumberValue.Float64 x -> floatLit "f64" x, TPrim "f64"
    | _ -> fail r "the Zig target does not support this kind of number yet"

/// ANF for argument lists: an argument that is not a flat expression is let-bound, and so is
/// any impure argument evaluated before it.
let bindArgs (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr =
    let needsBind ir = not (isFlat ir)
    let arr = List.toArray irs

    match arr |> Array.tryFindIndexBack needsBind with
    | None -> k irs
    | Some last ->
        let binds = List<Var * Expr>()

        let rec hoist (ir: Expr) =
            match ir with
            | ELet(v, r, b) ->
                binds.Add((v, r))
                hoist b
            | _ -> ir

        let outs =
            arr
            |> Array.mapi (fun i ir ->
                if i <= last && (needsBind ir || not (isPure ir)) && not (isVoid (typeOf ir)) then
                    let ir = hoist ir

                    if isFlat ir && isPure ir then
                        ir
                    else
                        let v = ctx.State.NewVar("tmp", typeOf ir, VLocal, false)
                        binds.Add((v, ir))
                        EVar v
                else
                    ir
            )

        List.foldBack (fun (v, ir) acc -> ELet(v, ir, acc)) (List.ofSeq binds) (k (List.ofArray outs))

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    | Fable.Value(kind, r) ->
        match kind with
        | Fable.UnitConstant -> EUnit
        | Fable.BoolConstant b ->
            ELit(
                (if b then
                     "true"
                 else
                     "false"),
                tBool
            )
        | Fable.NumberConstant(v, _) -> ELit(numberLit r v)
        | Fable.CharConstant c -> ELit(string<int>(int c), TPrim "u16")
        | Fable.NewRecord(values, entRef, genArgs) ->
            let ent = entOf ctx r entRef genArgs
            bindArgs ctx (values |> List.map (lw ctx)) (fun xs -> ECon(TEnt ent, "", xs, None))
        | Fable.NewUnion(values, tag, entRef, genArgs) ->
            let ent = entOf ctx r entRef genArgs
            let case = fst (List.item tag ent.Cases)
            bindArgs ctx (values |> List.map (lw ctx)) (fun xs -> ECon(TEnt ent, case, xs, None))
        | Fable.NewTuple(values, _) ->
            bindArgs ctx (values |> List.map (lw ctx)) (fun xs -> ECon(TTuple(xs |> List.map typeOf), "", xs, None))
        | Fable.NewOption(value, t, _) ->
            let ty = TOpt(mapType ctx r t)

            match value with
            | Some v -> bindArgs ctx [ lw ctx v ] (fun xs -> ECon(ty, "Some", xs, None))
            | None -> ECon(ty, "None", [], None)
        | _ -> fail r "the Zig target does not support %s yet" (exprKind e)

    | Fable.IdentExpr id ->
        match ctx.Vars.TryGetValue id.Name with
        | true, v -> EVar v
        | _ ->
            match ctx.Members.TryGetValue id.Name with
            | true, MConst ty ->
                EVar
                    {
                        Id = 0
                        Base = id.Name
                        Ty = ty
                        Kind = VGlobal
                        FMutable = false
                    }
            | true, MFunction -> fail id.Range "the Zig target does not support function values yet (`%s`)" id.Name
            | _ -> fail id.Range "the Zig target cannot resolve `%s` yet" id.Name

    | Fable.Let(id, value, body) ->
        let rhs = lw ctx value
        let ty = mapType ctx id.Range id.Type

        if isVoid ty then
            ESeq(asStmt ctx rhs, lw ctx body)
        else
            let v = ctx.State.NewVar(id.Name, ty, VLocal, id.IsMutable)
            ctx.Vars[id.Name] <- v
            ELet(v, rhs, lw ctx body)

    | Fable.Sequential es ->
        match List.rev es with
        | [] -> EUnit
        | last :: restRev ->
            let lastIr = lw ctx last
            restRev |> List.fold (fun acc s -> ESeq(lwStmt ctx s, acc)) lastIr

    | Fable.IfThenElse(guard, thenExpr, elseExpr, r) ->
        let ty = mapType ctx r e.Type
        bindArgs ctx [ lw ctx guard ] (fun xs -> EIf(xs.Head, lw ctx thenExpr, lw ctx elseExpr, ty))

    | Fable.Operation(kind, _, t, r) ->
        let ty = mapType ctx r t

        match kind with
        | Fable.Unary(op, x) ->
            let ir = lw ctx x

            match op with
            | UnaryPlus -> ir
            | UnaryMinus -> bindArgs ctx [ ir ] (fun xs -> EPrim("neg", xs, ty))
            | UnaryNot -> bindArgs ctx [ ir ] (fun xs -> EPrim("not", xs, ty))
            | UnaryNotBitwise -> bindArgs ctx [ ir ] (fun xs -> EPrim("bnot", xs, ty))
            | UnaryAddressOf -> fail r "the Zig target does not support address-of yet"
        | Fable.Binary(op, a, b) ->
            let name =
                match op with
                | BinaryEqual -> "eq"
                | BinaryUnequal -> "ne"
                | BinaryLess -> "lt"
                | BinaryLessOrEqual -> "le"
                | BinaryGreater -> "gt"
                | BinaryGreaterOrEqual -> "ge"
                | BinaryShiftLeft -> "shl"
                | BinaryShiftRightSignPropagating
                | BinaryShiftRightZeroFill -> "shr"
                | BinaryMinus -> "sub"
                | BinaryPlus -> "add"
                | BinaryMultiply -> "mul"
                | BinaryDivide -> "div"
                | BinaryModulus -> "mod"
                | BinaryOrBitwise -> "bor"
                | BinaryXorBitwise -> "bxor"
                | BinaryAndBitwise -> "band"
                | BinaryExponent -> fail r "the Zig target does not support `**` yet"

            // (only numbers, booleans and chars get this far: anything else fails in mapType)
            mapType ctx a.Range a.Type |> ignore
            bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim(name, xs, ty))
        | Fable.Logical(op, a, b) ->
            let rhs = lw ctx b

            bindArgs
                ctx
                [ lw ctx a ]
                (fun xs ->
                    match op with
                    | LogicalAnd -> EIf(xs.Head, rhs, ELit("false", tBool), tBool)
                    | LogicalOr -> EIf(xs.Head, ELit("true", tBool), rhs, tBool)
                )

    // A call that the replacements kept under its .NET name.
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path.StartsWith(Replacements.DotnetPrefix, System.StringComparison.Ordinal)
        ->
        dotnetCall ctx r (imp.Path.Substring Replacements.DotnetPrefix.Length) imp.Selector info t

    | Fable.Get(x, kind, t, r) ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let v = xs.Head

                match kind, typeOf v with
                | Fable.FieldGet info, TEnt ent when ent.Kind = KRecord -> EGet(v, PField info.Name, ty)
                | Fable.TupleIndex i, TTuple _ -> EGet(v, PItem i, ty)
                | Fable.UnionField info, TEnt ent ->
                    let case, fields = List.item info.CaseIndex ent.Cases
                    EGet(v, PCase(case, fst (List.item info.FieldIndex fields)), ty)
                | Fable.UnionTag, TEnt _ -> EPrim("tag", [ v ], tI32)
                | Fable.OptionValue, TOpt _ -> EGet(v, PSome, ty)
                | _ -> fail r "the Zig target does not support %s yet" (exprKind e)
            )

    | Fable.Test(x, kind, r) ->
        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let v = xs.Head

                match kind, typeOf v with
                | Fable.UnionCaseTest tag, (TEnt ent as t) -> ETest(v, fst (List.item tag ent.Cases), t)
                | Fable.OptionTest isSome, (TOpt _ as t) ->
                    ETest(
                        v,
                        (if isSome then
                             "Some"
                         else
                             "None"),
                        t
                    )
                | _ -> fail r "the Zig target does not support %s yet" (exprKind e)
            )

    | Fable.Call(callee, info, t, r) ->
        let ty = mapType ctx r t

        if info.ThisArg.IsSome then
            fail r "the Zig target does not support method calls yet"

        let name =
            match callee with
            | Fable.IdentExpr id when ctx.Members.ContainsKey id.Name -> id.Name
            | Fable.Import(imp, _, _) ->
                match imp.Kind with
                | Fable.MemberImport _ -> importAlias ctx imp.Path + "." + imp.Selector
                | _ -> fail r "the Zig target does not support this library call yet (%s from %s)" imp.Selector imp.Path
            | _ -> fail r "the Zig target does not support %s yet" (exprKind callee)

        let args =
            info.Args |> List.filter (fun a -> not (isUnit a.Type)) |> List.map (lw ctx)

        bindArgs ctx args (fun xs -> ECall(name, xs, ty))

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) ->
        match ctx.Vars.TryGetValue id.Name with
        | true, v -> EAssign(v, lw ctx value)
        | _ -> fail r "the Zig target does not support assigning to module-level values yet (`%s`)" id.Name

    | Fable.WhileLoop(guard, body, r) ->
        let c = lw ctx guard

        if isFlat c then
            EWhile(c, lwStmt ctx body)
        else
            fail r "the Zig target does not support a `while` condition with control flow in it yet"

    | Fable.ForLoop(id, start, limit, body, isUp, _) ->
        let iv = ctx.State.NewVar(id.Name, mapType ctx id.Range id.Type, VLocal, false)
        ctx.Vars[id.Name] <- iv
        bindArgs ctx [ lw ctx start; lw ctx limit ] (fun xs -> EFor(iv, xs[0], xs[1], isUp, lwStmt ctx body))

    | Fable.TypeCast(x, t) ->
        let ir = lw ctx x

        if typeOf ir = mapType ctx e.Range t then
            ir
        else
            fail e.Range "the Zig target does not support %s yet" (exprKind e)

    // Pattern matching arrives as a decision tree whose leaves name a target and the values
    // its variables are bound to. A target reached from several leaves is lowered once per leaf.
    | Fable.DecisionTree(expr, targets) -> lw { ctx with DecisionTargets = targets } expr

    | Fable.DecisionTreeSuccess(idx, boundValues, _) ->
        let idents, target = List.item idx ctx.DecisionTargets

        List.foldBack2 (fun id v body -> Fable.Let(id, v, body)) idents boundValues target
        |> lw ctx

    | _ -> fail e.Range "the Zig target does not support %s yet" (exprKind e)

/// What the target does for a .NET or FSharp.Core member. This table is keyed by .NET names
/// only, so it does not depend on how any other target implements the same member.
and dotnetCall
    (ctx: Ctx)
    (r: SourceLocation option)
    (entity: string)
    (name: string)
    (info: Fable.CallInfo)
    (t: Fable.Type)
    : Expr
    =
    let isNumber (ty: Ty) = intBits ty > 0 || isFloatTy ty

    match entity, name, info.Args with
    // structural equality of records, unions, tuples and options: plain values, compared
    // field by field
    | "Microsoft.FSharp.Core.Operators", "op_Equality", [ a; b ] ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("eql", xs, tBool))
    | "Microsoft.FSharp.Core.Operators", "op_Inequality", [ a; b ] ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("not", [ EPrim("eql", xs, tBool) ], tBool))
    | "Microsoft.FSharp.Core.Operators", "Ignore", [ x ] -> lwStmt ctx x
    | "Microsoft.FSharp.Core.Operators", "Identity", [ x ] -> lw ctx x
    | "Microsoft.FSharp.Core.Operators", "Fst", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 0, mapType ctx r t))
    | "Microsoft.FSharp.Core.Operators", "Snd", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 1, mapType ctx r t))
    // int, int64, byte, float, char, ...: conversions between numbers, with .NET's results
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), _, [ x ] when
        name.StartsWith("To", System.StringComparison.Ordinal)
        ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let from = typeOf xs.Head

                if from = ty then
                    xs.Head
                elif isNumber from && isNumber ty then
                    ctx.State.UsesRuntime <- true
                    EPrim("conv", xs, ty)
                else
                    fail r "the Zig target does not support %s.%s yet" entity name
            )
    | _ -> fail r "the Zig target does not support %s.%s yet" entity name

/// A statement: its value, if it has one, is not used.
and asStmt (ctx: Ctx) (ir: Expr) : Expr =
    if isVoid (typeOf ir) then
        ir
    else
        ELet(ctx.State.NewVar("discard", typeOf ir, VLocal, false), ir, EUnit)

and lwStmt (ctx: Ctx) (e: Fable.Expr) : Expr = asStmt ctx (lw ctx e)

let private isEntryPoint (info: Fable.MemberFunctionOrValue) =
    info.Attributes
    |> Seq.exists (fun att -> att.Entity.FullName = "Microsoft.FSharp.Core.EntryPointAttribute")

let lowerFile (com: Compiler) (file: Fable.File) : FileState =
    let state = FileState()
    let members = Dictionary<string, MemberKind>()

    let newCtx () =
        {
            Com = com
            State = state
            Vars = Dictionary()
            Members = members
            DecisionTargets = []
        }

    let report (r: SourceLocation option) (msg: string) =
        com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)

    let rec membersOf (decls: Fable.Declaration list) : Fable.MemberDecl list =
        decls
        |> List.collect (fun d ->
            match d with
            | Fable.MemberDeclaration m -> [ m ]
            | Fable.ModuleDeclaration m -> membersOf m.Members
            | Fable.ActionDeclaration a ->
                report a.Body.Range "the Zig target does not support top-level statements yet"
                []
            | Fable.ClassDeclaration c ->
                match com.TryGetEntity c.Entity with
                | Some ent when ent.IsFSharpRecord || ent.IsFSharpUnion ->
                    try
                        entOf (newCtx ()) None c.Entity [] |> ignore

                        if not c.AttachedMembers.IsEmpty then
                            report None $"the Zig target does not support members of types yet (%s{c.Name})"
                    with ZigError(msg, r) ->
                        report r msg
                | _ -> report None $"the Zig target does not support this kind of type declaration yet (%s{c.Name})"

                []
        )

    let decls = membersOf file.Declarations

    // What the file declares is known before any body is lowered: bodies call each other.
    for d in decls do
        let info = com.GetMember d.MemberRef

        try
            if info.IsValue then
                members[d.Name] <- MConst(mapType (newCtx ()) d.Body.Range d.Body.Type)
            else
                members[d.Name] <- MFunction
        with ZigError(msg, r) ->
            report r msg

    for d in decls do
        let info = com.GetMember d.MemberRef
        let ctx = newCtx ()

        try
            if info.IsValue then
                match members.TryGetValue d.Name, lw ctx d.Body with
                | (true, MConst ty), ELit(text, _) -> state.Consts.Add((d.Name, ty, text))
                | (true, MConst _), _ ->
                    fail d.Body.Range "the Zig target only supports literal module-level values so far (`%s`)" d.Name
                | _ -> () // its type was rejected above
            else
                let entry = isEntryPoint info

                let ps =
                    if entry then
                        [] // (the argument array is not available yet)
                    else
                        d.Args
                        |> List.filter (fun a -> not (isUnit a.Type))
                        |> List.map (fun a ->
                            let v = state.NewVar(a.Name, mapType ctx a.Range a.Type, VParam, false)
                            ctx.Vars[a.Name] <- v
                            v
                        )

                let ret = mapType ctx d.Body.Range d.Body.Type
                let body = lw ctx d.Body

                state.Fns.Add
                    {
                        Name = d.Name
                        Params = ps
                        Modes = ps |> List.map (fun _ -> MPlain)
                        Ret = ret
                        Body = body
                        NeedsAlloc = false
                        IsEntryPoint = entry
                        Range = d.Body.Range
                    }
        with ZigError(msg, r) ->
            report
                (match r with
                 | Some _ -> r
                 | None -> d.Body.Range)
                msg

    state
