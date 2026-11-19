/// Core .NET / FSharp.Core member dispatch (`dotnetCall`), `for...in` source lowering, and
/// F# runtime library call resolution (`libraryCall`).
module Fable.Transforms.Zig.LowerDotnet

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes
open Fable.Transforms.Zig.LowerHelpers
open Fable.Transforms.Zig.LowerFormat
open Fable.Transforms.Zig.Lower

/// What the target does for a .NET or FSharp.Core member. This table is keyed by .NET names
/// only, so it does not depend on how any other target implements the same member.
let rec dotnetCall
    (ctx: Ctx)
    (r: SourceLocation option)
    (entity: string)
    (name: string)
    (info: Fable.CallInfo)
    (t: Fable.Type)
    : Expr
    =
    // (other names of structural hashing, equality and comparison, and of values with a unit of
    // measure: what `hash`, `=`, `compare` and the value are)
    match entity, name with
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Hash" | "GenericHash" | "GenericLimitedHash" | "GenericHashWithComparer") when not info.Args.IsEmpty ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "Hash" { info with Args = [ List.last info.Args ] } t
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Equals" | "GenericEquality" | "GenericEqualityER" | "GenericEqualityWithComparer") when info.Args.Length >= 2 ->
        let n = info.Args.Length
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "op_Equality" { info with Args = info.Args.[n - 2 ..] } t
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Compare" | "GenericComparison" | "GenericComparisonWithComparer") when info.Args.Length >= 2 ->
        let n = info.Args.Length
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "Compare" { info with Args = info.Args.[n - 2 ..] } t
    | "Microsoft.FSharp.Core.LanguagePrimitives", "PhysicalHash" when info.Args.Length = 1 ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx info.Args.Head ] (fun xs -> EEmit("fable_rt.physicalHash($0)", xs, tI32))
    | "Microsoft.FSharp.Core.LanguagePrimitives", m when
        m.EndsWith("WithMeasure", System.StringComparison.Ordinal)
        && info.Args.Length = 1
        ->
        lw ctx info.Args.Head
    // (`c.Compare(a, b)` of a `Comparer<'T>`: an IComparer here, `Default` or one of `Create`)
    | "System.Collections.Generic.Comparer`1", "Compare" when info.Args.Length = 2 && info.ThisArg.IsSome ->
        libraryCall ctx r "Array" "comparerCompare" info (info.ThisArg.Value :: info.Args) t
    | "System.Collections.Generic.Comparer`1", "Create" when info.Args.Length = 1 ->
        libraryCall ctx r "Array" "comparerOfDelegate" info info.Args t
    // (a format provider given to a number's, a date's or Convert's member: the culture is the
    // invariant one here, as without it; see `isCulture`)
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single" | "System.Decimal" | "System.Numerics.BigInteger" | "System.Convert" | "System.DateTime" | "System.DateTimeOffset" | "System.TimeSpan" | "System.DateOnly" | "System.TimeOnly"),
      ("Parse" | "TryParse" | "ToString" | "ParseExact" | "TryParseExact") when info.Args |> List.exists isCulture ->
        dotnetCall ctx r entity name { info with Args = info.Args |> List.filter (isCulture >> not) } t
    | "System.Convert", m when
        m.StartsWith("To", System.StringComparison.Ordinal)
        && info.Args |> List.exists isCulture
        ->
        dotnetCall ctx r entity name { info with Args = info.Args |> List.filter (isCulture >> not) } t
    // (a culture as a value: nothing here, the invariant culture is the only one)
    | "System.Globalization.CultureInfo",
      ("get_InvariantCulture" | "get_CurrentCulture" | "get_CurrentUICulture" | "get_InvariantUICulture") -> EUnit
    | ("System.Double" | "System.Single"), ("Max" | "Min") when info.Args.Length = 2 ->
        dotnetCall ctx r "System.Math" name info t
    // (`byte x` and `sbyte x`, as F# names them in ExtraTopLevelOperators: Operators' conversions)
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("ToByte" | "ToSByte" | "ToDouble" | "ToSingle" | "ToInt32") when
        info.Args.Length = 1 && unwrapNullness info.Args.Head.Type <> Fable.String
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "Microsoft.FSharp.Control.FSharpAsync", "Parallel" when info.Args.Length = 2 ->
        libraryCall ctx r "Async" "parallelAllMax" info info.Args t
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "Reduce" ->
        dotnetCall ctx r "Microsoft.FSharp.Collections.ArrayModule" "Reduce" info t
    // (`for x in s do` and `while c do` in `async { }` whose body completes at once, no `let!` or
    // `do!` in it: one loop of the library's, not a computation made and run for each item)
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder", "For" when
        (match info.Args with
         | [ _; Fable.Lambda(_, body, _) ] -> (syncAsyncBody body).IsSome
         | _ -> false)
        ->
        match info.Args with
        | [ source; Fable.Lambda(arg, body, name) ] ->
            let lambda = Fable.Lambda(arg, (syncAsyncBody body).Value, name)

            libraryCall
                ctx
                r
                "Async"
                "builderForSync"
                { info with
                    ThisArg = None
                    MemberRef = None
                }
                [ source; lambda ]
                t
        | _ -> fail r "internal: an async for"
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder", "While" when
        (match info.Args with
         | [ guard; AsyncBuilderCall("Delay", { Args = [ Fable.Lambda(_, body, _) ] }) ] ->
             not (usesAsyncBuilder guard) && (syncAsyncBody body).IsSome
         | _ -> false)
        ->
        match info.Args with
        | [ guard; AsyncBuilderCall("Delay", { Args = [ Fable.Lambda(arg, body, name) ] }) ] ->
            let lambda = Fable.Lambda(arg, (syncAsyncBody body).Value, name)

            libraryCall
                ctx
                r
                "Async"
                "builderWhileSync"
                { info with
                    ThisArg = None
                    MemberRef = None
                    GenericArgs = []
                }
                [ guard; lambda ]
                t
        | _ -> fail r "internal: an async while"
    // (a member of a .NET collection, StringBuilder or Random whose object may be null: checked
    // first, as .NET does. Not where it is known not to be: an object made there, or a variable
    // bound to one. The object is a variable or a field of one, read again by the call)
    | _ when
        nullCellEntity entity
        && not (List.contains "cellChecked" info.Tags)
        && (
            match info.ThisArg with
            | Some this -> mayBeNullCell ctx this
            | None -> false
        )
        ->
        match info.ThisArg.Value with
        | Uncast(Fable.IdentExpr _) ->
            ctx.State.UsesRuntime <- true

            ESeq(
                ERt("fable_rt.checkCellNonNull($0)", [ lw ctx info.ThisArg.Value ], tVoid),
                dotnetCall ctx r entity name { info with Tags = "cellChecked" :: info.Tags } t
            )
        // (a field or an item: read once, into a variable that is checked)
        | this ->
            let v = AST.makeTypedIdent this.Type (tempName ctx "cell")

            let call =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = name
                            Path = Replacements.DotnetPrefix + entity
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                        },
                        Fable.Any,
                        None
                    ),
                    { info with ThisArg = Some(Fable.IdentExpr v) },
                    t,
                    r
                )

            lw ctx (Fable.Let(v, this, call))
    | _ ->

        let isNumber (ty: Ty) = intBits ty > 0 || isFloatTy ty

        // (the object of a property or method comes first)
        let args =
            match info.ThisArg with
            | Some this -> this :: info.Args
            | None -> info.Args

        let contents (cell: Expr) =
            match typeOf cell with
            | TEnt(_, [ elem ]) -> EGet(cell, PField "contents", elem)
            | _ -> fail r "internal: not a ref cell"

        /// a call into the runtime library that can raise
        let rt (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
            ctx.State.UsesRuntime <- true
            bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> ERt(macro, irs, ty))

        /// a call into the runtime library that cannot
        let pure' (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
            ctx.State.UsesRuntime <- true
            bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> EEmit(macro, irs, ty))

        let tChar = TPrim "u16"
        let tF64 = TPrim "f64"

        // (the Zig name of a number type)
        let zigTypeName (ty: Ty) =
            match ty with
            | TPrim name -> name
            | _ -> fail r "internal: not a number type"

        // (an enum's value is not a number argument: `IndexOf(c, StringComparison.Ordinal)`)
        let isInt (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(Int32, Fable.NumberInfo.IsEnum _) -> false
            | Fable.Number(Int32, _) -> true
            | _ -> false

        let tBig = TPrim "fable_rt.BigInt"
        let tDec = TPrim "fable_rt.NetDecimal"

        let isDec (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(Decimal, _) -> true
            | _ -> false

        let decLit (m: string) (scale: int) =
            ctx.State.UsesRuntime <- true
            ELit($"fable_rt.decLit(%s{m}, %d{scale})", tDec)

        let isBig (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(BigInt, _) -> true
            | _ -> false

        match entity, name, args with
        // ref cells: `ref x`, `!r` and `r.Value`, `r := x` and `r.Value <- x`, `incr`, `decr`
        | "Microsoft.FSharp.Core.Operators", "Ref", [ x ] ->
            bindArgsIn true ctx [ lw ctx x ] (fun xs -> ECon(TEnt(refEnt ctx.State, [ typeOf xs.Head ]), "", xs, None))
        | "Microsoft.FSharp.Core.Operators", "op_Dereference", [ cell ]
        | "Microsoft.FSharp.Core.FSharpRef`1", ("get_Value" | "get_contents"), cell :: _ ->
            bindArgs ctx [ lw ctx cell ] (fun xs -> contents xs.Head)
        | "Microsoft.FSharp.Core.Operators", "op_ColonEquals", [ cell; value ]
        | "Microsoft.FSharp.Core.FSharpRef`1", ("set_Value" | "set_contents"), [ cell; value ] ->
            bindArgs ctx [ lw ctx cell; lw ctx value ] (fun xs -> EStore(contents xs[0], xs[1]))
        | "Microsoft.FSharp.Core.Operators", ("Increment" | "Decrement"), [ cell ] ->
            let op =
                if name = "Increment" then
                    "add"
                else
                    "sub"

            bindArgs
                ctx
                [ lw ctx cell ]
                (fun xs -> EStore(contents xs.Head, EPrim(op, [ contents xs.Head; ELit("1", tI32) ], tI32)))
        // lists: what does not need a loop is a test or a field
        | ("Microsoft.FSharp.Collections.FSharpList`1" | "Microsoft.FSharp.Collections.ListModule"),
          ("get_IsEmpty" | "IsEmpty"),
          x :: _ -> bindArgs ctx [ lw ctx x ] (fun xs -> ETest(xs.Head, "Empty", typeOf xs.Head))
        // (`xs.Head` and `xs.Tail` of an empty list raise, as on .NET)
        | "Microsoft.FSharp.Collections.FSharpList`1", ("get_Head" | "get_Tail"), x :: _ ->
            let field =
                if name = "get_Head" then
                    "Head"
                else
                    "Tail"

            let ty = mapType ctx r t

            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs ->
                    let empty = ELit(stringLiteral "The input list was empty.", tStr)

                    EIf(
                        ETest(xs.Head, "Empty", typeOf xs.Head),
                        raiseDotnet ctx r "System.InvalidOperationException" empty t,
                        EGet(xs.Head, PCase("Cons", field), ty),
                        ty
                    )
                )
        // structural equality of records, unions, tuples and options: plain values, compared
        // field by field
        | "Microsoft.FSharp.Core.Operators", "op_Equality", [ a; b ] ->
            bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("eql", xs, tBool))
        | "Microsoft.FSharp.Core.Operators", "op_Inequality", [ a; b ] ->
            bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("not", [ EPrim("eql", xs, tBool) ], tBool))
        // ---- numbers that are not numbers ----
        | "Microsoft.FSharp.Core.Operators", "NaN", [] -> ELit("std.math.nan(f64)", TPrim "f64")
        | "Microsoft.FSharp.Core.Operators", "NaNSingle", [] -> ELit("std.math.nan(f32)", TPrim "f32")
        | "Microsoft.FSharp.Core.Operators", "Infinity", [] -> ELit("std.math.inf(f64)", TPrim "f64")
        | "Microsoft.FSharp.Core.Operators", "InfinitySingle", [] -> ELit("std.math.inf(f32)", TPrim "f32")
        // `box x :? int`: a test of what an `obj` holds
        | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "TypeTestGeneric", [ x ] when
            info.GenericArgs.Length = 1
            && (unwrapNullness x.Type = Fable.Any
                || (isInterfaceType ctx.Com x.Type && isFatIfaceTy (mapType ctx r x.Type))
                || isInterfaceType ctx.Com (unwrapNullness info.GenericArgs.Head))
            ->
            lw ctx (Fable.Test(x, Fable.TypeTest info.GenericArgs.Head, r))
        // `x :? T` where Fable keeps it a call: of an exception class, or of a class of objects
        | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "TypeTestGeneric", [ x ] when
            (match info.GenericArgs with
             | [ g ] ->
                 match unwrapNullness g with
                 | Fable.DeclaredType(cls, _) -> (tryExnEnt ctx r cls).IsSome || (objInfo ctx r cls).IsSome
                 | _ -> false
             | _ -> false)
            ->
            match unwrapNullness info.GenericArgs.Head with
            | Fable.DeclaredType(cls, _) when (tryExnEnt ctx r cls).IsSome ->
                let ent = (tryExnEnt ctx r cls).Value
                bindArgs ctx [ lw ctx x ] (fun xs -> EExnTest(xs.Head, ent))
            | Fable.DeclaredType(cls, gs) ->
                let o = (objInfo ctx r cls).Value
                let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
                bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.objIs($0, %s{typeRef})", xs, tBool))
            | _ -> fail r "internal: a type test"
        // `x :?> Circle`: an object of that class, or InvalidCastException
        | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ Uncast x ] when
            (objOfType ctx r t).IsSome && (objOfType ctx r x.Type).IsSome
            ->
            let o = (objOfType ctx r t).Value
            let source = (objOfType ctx r x.Type).Value

            if ancestors source |> List.exists (fun k -> k.FullName = o.FullName) then
                lw ctx x
            else
                rt $"fable_rt.objCast($0, %s{objTypeRef o (objArgs ctx r t)})" [ x ] tAny
        // (a cast that changes nothing here: an exception of a known class is an `exn`)
        | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ x ] when
            mapType ctx r x.Type = mapType ctx r t
            && unwrapNullness x.Type <> Fable.Any
            && (not (isFatIfaceTy (mapType ctx r x.Type))
                || unwrapNullness x.Type = unwrapNullness t)
            ->
            lw ctx x
        // ---- ranges: `a .. b`, `a .. step .. b` ----
        | "Microsoft.FSharp.Core.Operators", ("op_Range" | "op_RangeStep"), _ ->
            let lo, step, hi =
                match args with
                | [ a; b ] -> a, None, b
                | [ a; s; b ] -> a, Some s, b
                | _ -> fail r "internal: a range"

            let one (lit: string) =
                match step with
                | Some s -> lw ctx s
                | None -> ELit(lit, mapType ctx r lo.Type)

            let fn, irs =
                match lo.Type with
                | Fable.Number(Int32, _) -> "rangeInt", [ lw ctx lo; one "1"; lw ctx hi ]
                | Fable.Number(Int64, _) -> "rangeInt64", [ lw ctx lo; one "1"; lw ctx hi ]
                | Fable.Number(UInt64, _) -> "rangeUInt64", [ lw ctx lo; one "1"; lw ctx hi ]
                | Fable.Number(Decimal, _) -> "rangeDecimal", [ lw ctx lo; one "fable_rt.decLit(1, 0)"; lw ctx hi ]
                | Fable.Number(BigInt, _) ->
                    "rangeBigInt",
                    [
                        lw ctx lo
                        (match step with
                         | Some s -> lw ctx s
                         | None -> EEmit("fable_rt.bigOf(@as(i32, 1))", [], mapType ctx r lo.Type))
                        lw ctx hi
                    ]
                | Fable.Number(Float64, _) -> "rangeFloat", [ lw ctx lo; one "1.0"; lw ctx hi ]
                | Fable.Char when step.IsNone -> "rangeChar", [ lw ctx lo; lw ctx hi ]
                | other -> fail r "the Zig target does not support a range of this type yet (%A)" other

            bindArgs ctx irs (fun xs -> ECall(libraryTarget ctx "Seq" fn, [], xs, mapType ctx r t))
        | "Microsoft.FSharp.Collections.SeqModule", ("Sum" | "Average" | "SumBy" | "AverageBy"), _ ->
            let item =
                match t with
                | _ when name.EndsWith "By" -> t
                | _ -> t

            let seqArg = List.last args

            let listIr =
                match seqArg with
                | Fable.TypeCast(inner, _) when (listItem inner.Type).IsSome -> lw ctx inner
                | _ ->
                    let itemTy =
                        match seqArg.Type with
                        | Fable.DeclaredType(_, [ i ]) -> mapType ctx r i
                        | _ -> mapType ctx r item

                    bindArgs
                        ctx
                        [ lw ctx seqArg ]
                        (fun xs ->
                            ECall(
                                libraryTarget ctx "Seq" "toList",
                                [ itemTy ],
                                xs,
                                TEnt(listEnt ctx.State, [ itemTy ])
                            )
                        )

            let ty = mapType ctx r t

            match name, args with
            | "Sum", [ _ ] when ty = TPrim "fable_rt.NetDecimal" ->
                bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listSumDec($0)", xs, ty))
            | "Sum", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.listSum($0)", xs, ty))
            | "Average", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listAverage($0)", xs, ty))
            | "SumBy", [ f; _ ] ->
                bindArgs
                    ctx
                    [ lw ctx f; listIr ]
                    (fun xs -> ERt($"fable_rt.listSumBy(%s{zigTypeName ty}, $0, $1)", xs, ty))
            | "AverageBy", [ f; _ ] ->
                bindArgs
                    ctx
                    [ lw ctx f; listIr ]
                    (fun xs -> ERt($"fable_rt.listAverageBy(%s{zigTypeName ty}, $0, $1)", xs, ty))
            | _ -> fail r "internal: a sum"

        // .NET's members by domain: tasks and async (Fable2Zig.Dotnet.Async.fs)
        | DomainCall "async" ctx r info t lowered -> lowered
        // ---- the entry of a map ----
        // (an entry is a pair here: making one is making the pair, and `KeyValue(k, v)` is the pair)
        | "System.Collections.Generic.KeyValuePair`2", ".ctor", [ k; v ] ->
            lw ctx (Fable.Value(Fable.NewTuple([ k; v ], false), r))
        | "Microsoft.FSharp.Core.Operators", "KeyValuePattern", [ kv ] -> lw ctx kv
        | "System.Collections.Generic.KeyValuePair`2", ("get_Key" | "get_Value"), [ kv ] ->
            bindArgs
                ctx
                [ lw ctx kv ]
                (fun xs ->
                    EGet(
                        xs.Head,
                        PItem(
                            if name = "get_Key" then
                                0
                            else
                                1
                        ),
                        mapType ctx r t
                    )
                )
        // ---- the item of this round of a `for ... in` loop ----
        | _, "get_Current", [ Fable.IdentExpr e ] when ctx.Enumerators.ContainsKey e.Name ->
            EVar ctx.Enumerators[e.Name]

        // .NET's members by domain: arrays, 2D arrays, .NET's mutable collections, lazy, spans, weak references (Fable2Zig.Dotnet.Collections.fs)
        | DomainCall "collections" ctx r info t lowered -> lowered
        // .NET's members by domain: StringBuilder, Split, Join, Format, chars and strings (Fable2Zig.Dotnet.Text.fs)
        | DomainCall "text" ctx r info t lowered -> lowered
        // ---- comparison of what is not a number: by `compare` ----
        | "Microsoft.FSharp.Core.Operators", "Max", [ a; b ] ->
            pure' "fable_rt.maxOf(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
        | "Microsoft.FSharp.Core.Operators", "Min", [ a; b ] ->
            pure' "fable_rt.minOf(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
        | "Microsoft.FSharp.Core.Operators", "Hash", [ x ] ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.hash(%s{typedArg ctx r x 0})", xs, tI32))
        | "Microsoft.FSharp.Core.Operators",
          ("op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual" | "op_GreaterThanOrEqual" | "Compare"),
          [ a; b ] ->
            let op =
                match name with
                | "op_LessThan" -> Some "lt"
                | "op_GreaterThan" -> Some "gt"
                | "op_LessThanOrEqual" -> Some "le"
                | "op_GreaterThanOrEqual" -> Some "ge"
                | _ -> None

            bindArgs
                ctx
                [ lw ctx a; lw ctx b ]
                (fun xs ->
                    let order = EEmit("fable_rt.compareOf($0, $1)", xs, tI32)

                    match op with
                    | Some op -> EPrim(op, [ order; ELit("0", tI32) ], tBool)
                    | None -> order
                )
        // ---- failures (Fable2Zig.Dotnet.Exceptions.fs) ----
        | DomainCall "exceptions" ctx r info t lowered -> lowered
        | "Microsoft.FSharp.Core.Operators", "Ignore", [ x ] -> lwStmt ctx x
        | "Microsoft.FSharp.Core.Operators", "Identity", [ x ] -> lw ctx x
        | "Microsoft.FSharp.Core.Operators", "Fst", [ x ] ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 0, mapType ctx r t))
        | "Microsoft.FSharp.Core.Operators", "Snd", [ x ] ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 1, mapType ctx r t))
        // .NET's members by domain: decimal, bigint, checked arithmetic (Fable2Zig.Dotnet.Numbers.fs)
        | DomainCall "numbers" ctx r info t lowered -> lowered
        // .NET's members by domain, in Fable2Zig.Dotnet.fs (enums, Convert and BitConverter,
        // Random, Nullable, Stack and Queue, tuples): here, in their place among the cases
        | DomainCall "misc" ctx r info t lowered -> lowered
        // ---- obj ----
        | "Microsoft.FSharp.Core.Operators", "Box", [ x ] when unwrapNullness x.Type <> Fable.Any -> boxed ctx x
        | "Microsoft.FSharp.Core.Operators", "Box", [ x ] -> lw ctx x
        | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
          ("Unbox" | "UnboxGeneric" | "UnboxFast"),
          [ Uncast x ] when unwrapNullness x.Type = Fable.Any && unwrapNullness t <> Fable.Any -> unboxed ctx r x t
        | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
          ("Unbox" | "UnboxGeneric" | "UnboxFast"),
          [ Uncast x ] when
            isInterfaceType ctx.Com x.Type
            && isFatIfaceTy (mapType ctx r x.Type)
            && unwrapNullness t <> Fable.Any
            ->
            ifaceDowncast ctx r x t
        // `obj.ReferenceEquals(a, b)` and `PhysicalEquality a b`: the same cell (what F# boxes for
        // the call is looked through: a record is not copied by it on .NET)
        | ("System.Object" | "Microsoft.FSharp.Core.LanguagePrimitives"),
          ("ReferenceEquals" | "PhysicalEquality"),
          [ Uncast a; Uncast b ] ->
            let a, b =
                if a.Type = b.Type then
                    a, b
                else
                    Fable.TypeCast(a, Fable.Any), Fable.TypeCast(b, Fable.Any)

            // (numbers, chars and bools are boxed one by one for the call: never the same object)
            match a.Type, b.Type with
            | (Fable.Number _ | Fable.Char | Fable.Boolean), _
            | _, (Fable.Number _ | Fable.Char | Fable.Boolean) ->
                lw ctx (Fable.Sequential [ a; b; Fable.Value(Fable.BoolConstant false, r) ])
            | _ ->

                // (a record, a union or a tuple that is a value here has no identity to compare)
                match mapType ctx r a.Type with
                | TEnt(e, _) when e.Kind = KRecord || e.Kind = KValueUnion ->
                    fail
                        r
                        "the Zig target keeps %s as a value, which has no identity: ReferenceEquals and PhysicalEquality cannot be answered as on .NET (mark the type [<ReferenceEquality>] to give its values one)"
                        e.Ref.FullName
                | TTuple _ ->
                    fail
                        r
                        "the Zig target keeps tuples as values, which have no identity: ReferenceEquals cannot be answered as on .NET"
                | _ -> pure' "fable_rt.refEql($0, $1)" [ a; b ] tBool
        // `x.Equals(o)`: by the type's `Equals`, through an object
        | "System.Object", "Equals", [ a; b ] ->
            let asObj (x: Fable.Expr) =
                match x with
                | Uncast inner when unwrapNullness inner.Type <> Fable.Any -> Fable.TypeCast(inner, Fable.Any)
                | _ -> x

            pure' "fable_rt.eql($0, $1)" [ asObj a; asObj b ] tBool
        | ("System.Object" | "System.String" | "System.Boolean" | "System.Char" | "System.SByte" | "System.Byte" | "System.Int16" | "System.UInt16" | "System.Int32" | "System.UInt32" | "System.Int64" | "System.UInt64" | "System.Single" | "System.Double" | "System.Decimal" | "System.Numerics.BigInteger"),
          "GetHashCode",
          [ x ] -> pure' "fable_rt.hash($0)" [ x ] tI32
        // (`EqualityComparer<'T>.Default`: F#'s equality and hash, called directly; another
        // comparer, one of `Create`, is called through its IEqualityComparer)
        | "System.Collections.Generic.EqualityComparer`1", "Equals", [ IsDefaultEqualityComparer; a; b ] ->
            pure' "fable_rt.eql($0, $1)" [ a; b ] tBool
        | "System.Collections.Generic.EqualityComparer`1", "GetHashCode", [ IsDefaultEqualityComparer; x ] ->
            pure' "fable_rt.hash($0)" [ x ] tI32
        | "System.Collections.Generic.EqualityComparer`1", "Equals", [ c; a; b ] ->
            libraryCall ctx r "Array" "equalityComparerEquals" info [ c; a; b ] t
        | "System.Collections.Generic.EqualityComparer`1", "GetHashCode", [ c; x ] ->
            libraryCall ctx r "Array" "equalityComparerHash" info [ c; x ] t
        | "System.Collections.Generic.EqualityComparer`1", "get_Default", [] ->
            libraryCall ctx r "Array" "structuralEqualityComparer" info [ Fable.Value(Fable.UnitConstant, None) ] t
        | "System.Collections.Generic.EqualityComparer`1", "Create", [ eq; h ] ->
            libraryCall ctx r "Array" "equalityComparerOfDelegates" info [ eq; h ] t
        // ---- numbers & math (Fable2Zig.Dotnet.Math.fs) ----
        | DomainCall "math" ctx r info t lowered -> lowered

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
        | _ ->
            // (where the value is a function that is applied at once, Fable gives the read the type
            // of the application: the option's item type is the one to go by)
            let t =
                match entity, name, args with
                | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1"),
                  "get_Value",
                  o :: _ ->
                    match o.Type with
                    | Fable.Option(item, _) -> item
                    | _ -> t
                | _ -> t

            // (a member of F#'s list reached through a trait call, `(^a: (member Length: int) x)`,
            // comes with the list's type as its type argument; the functions take the item's)
            let info =
                match entity, info.ThisArg with
                | "Microsoft.FSharp.Collections.FSharpList`1", Some this ->
                    match this.Type with
                    | Fable.List item -> { info with GenericArgs = [ item ] }
                    | _ -> info
                | _ -> info

            match libraryFunction entity name with
            | Some(file, fn) -> libraryCall ctx r file fn info args t
            | None -> fail r "the Zig target does not support %s.%s yet" entity name


/// What a `for ... in` loop walks, lowered: a list (of a list, a set, or a map's entries) or
/// a string. None for a source that is walked some other way.
and forInSource (ctx: Ctx) (source: Fable.Expr) : (Expr * string) option =
    let (Uncast inner) = source

    match inner.Type with
    | Fable.List _ -> Some(lw ctx inner, "list")
    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> Some(lw ctx inner, "array")
    // (a `ReadOnlyCollection<'T>`, `IList<'T>`: an array here)
    | Fable.DeclaredType(ent, [ _ ]) when
        ent.FullName = "System.Collections.ObjectModel.ReadOnlyCollection`1"
        || ent.FullName = "System.Collections.Generic.IList`1"
        ->
        Some(lw ctx inner, "array")
    | Fable.DeclaredType(ent, _) when
        ent.FullName = "System.Collections.Generic.ICollection`1"
        || ent.FullName = "System.Collections.Generic.Dictionary`2.KeyCollection"
        || ent.FullName = "System.Collections.Generic.Dictionary`2.ValueCollection"
        ->
        Some(lw ctx inner, "list")
    | Fable.String -> Some(lw ctx inner, "string")
    | t when isSeqType t -> Some(lw ctx inner, "seq")
    // (the matches and the groups of a regular expression: their sequences)
    | Fable.DeclaredType(coll, []) when
        coll.FullName = "System.Text.RegularExpressions.MatchCollection"
        || coll.FullName = "System.Text.RegularExpressions.GroupCollection"
        ->
        let isMatches =
            coll.FullName.EndsWith("MatchCollection", System.StringComparison.Ordinal)

        let item =
            Fable.DeclaredType(
                {
                    FullName =
                        (if isMatches then
                             "System.Text.RegularExpressions.Match"
                         else
                             "System.Text.RegularExpressions.Group")
                    Path = Fable.CoreAssemblyName "System.Text.RegularExpressions"
                },
                []
            )

        let seqType =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            )

        Some(
            libraryCall
                ctx
                None
                "Regex"
                (if isMatches then
                     "matchesToSeq"
                 else
                     "groupsToSeq")
                (Fable.CallInfo.Create(args = [ inner ]))
                [ inner ]
                seqType,
            "seq"
        )
    | Fable.Array(_, Fable.ResizeArray) ->
        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs ->
                    cellChecked ctx inner xs.Head
                    <| EEmit("fable_rt.raToList($0)", xs, TEnt(listEnt ctx.State, [ itemOf xs.Head ]))
                ),
            "list"
        )
    | Fable.DeclaredType(ent, [ k; v ]) when isDictionaryName ent.FullName ->
        let pairTy = TTuple [ mapType ctx None k; mapType ctx None v ]

        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs ->
                    cellChecked ctx inner xs.Head
                    <| EEmit("fable_rt.dictToList($0)", xs, TEnt(listEnt ctx.State, [ pairTy ]))
                ),
            "list"
        )
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.HashSet`1" ->
        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs ->
                    cellChecked ctx inner xs.Head
                    <| EEmit("fable_rt.setToList($0)", xs, TEnt(listEnt ctx.State, [ mapType ctx None item ]))
                ),
            "list"
        )
    | Fable.DeclaredType(ent, [ item ]) when
        ent.FullName = "System.Collections.Generic.Stack`1"
        || ent.FullName = "System.Collections.Generic.Queue`1"
        ->
        let file =
            if ent.FullName.EndsWith("Stack`1", System.StringComparison.Ordinal) then
                "Stack"
            else
                "Queue"

        let info = Fable.CallInfo.Create(args = [ inner ], genArgs = [ item ])
        Some(libraryCall ctx None file "toList" info [ inner ] (Fable.List item), "list")
    | Fable.DeclaredType(ent, genArgs) when ent.FullName = mapName || ent.FullName = setName ->
        let file =
            if ent.FullName = mapName then
                "Map"
            else
                "Set"

        let info = Fable.CallInfo.Create(args = [ inner ], genArgs = genArgs)

        let listTy =
            match genArgs with
            | [ k; v ] -> Fable.List(Fable.Tuple([ k; v ], false))
            | [ item ] -> Fable.List item
            | _ -> Fable.Any

        Some(libraryCall ctx None file "toList" info [ inner ] listTy, "list")
    | _ -> None

/// A call of a function of the part of the runtime library that is written in F# (`List.fs`,
/// ...). Its type parameters are found by name, from the signature of the FSharp.Core
/// function it stands for, and given in the order of their names: that is the order in which
/// the library declares them.

and libraryCall
    (ctx: Ctx)
    (r: SourceLocation option)
    (file: string)
    (fn: string)
    (info: Fable.CallInfo)
    (args: Fable.Expr list)
    (t: Fable.Type)
    : Expr
    =
    // (an empty generic value of the library made at obj, as a generalized `let xs = Seq.empty`
    // is: made again at the type the parameter wants. The type arguments are taken in the order
    // the signature first names its type parameters, and only when every other argument agrees)
    let args =
        let rec namesIn (acc: string list) (t: Fable.Type) =
            match t with
            | Fable.GenericParam(n, _, _) ->
                if List.contains n acc then
                    acc
                else
                    acc @ [ n ]
            | _ -> t.Generics |> List.fold namesIn acc

        let rec hasAny (t: Fable.Type) =
            match t with
            | Fable.Any -> true
            | _ -> t.Generics |> List.exists hasAny

        let isOpenEmpty (a: Fable.Expr) =
            match a with
            | Fable.Call(Fable.Import(imp, _, _), ci, typ, _) ->
                (match imp.Kind with
                 | Fable.LibraryImport _ -> true
                 | _ -> false)
                && ci.Args.IsEmpty
                && ci.ThisArg.IsNone
                && hasAny typ
            | _ -> false

        let names = info.SignatureArgTypes |> List.fold namesIn []

        if
            args |> List.exists isOpenEmpty
            && info.SignatureArgTypes.Length = args.Length
            && not names.IsEmpty
            && names.Length = info.GenericArgs.Length
            && not (info.GenericArgs |> List.exists (fun t -> hasAny t || hasTypeParams t))
        then
            let subst = List.zip names info.GenericArgs |> Map.ofList
            let wanted = info.SignatureArgTypes |> List.map (substFableType subst)

            let agrees =
                List.forall2
                    (fun (w: Fable.Type) (a: Fable.Expr) ->
                        isOpenEmpty a
                        || hasAny a.Type
                        || (
                            match w, a.Type with
                            | (Fable.LambdaType _ | Fable.DelegateType _), _ -> true
                            | _ -> w = a.Type
                        )
                    )
                    wanted
                    args

            if agrees then
                List.map2
                    (fun (w: Fable.Type) (a: Fable.Expr) ->
                        match a with
                        | Fable.Call(callee, ci, _, r) when
                            isOpenEmpty a && not (hasAny w) && w.Generics.Length = ci.GenericArgs.Length
                            ->
                            Fable.Call(callee, { ci with GenericArgs = w.Generics }, w, r)
                        | _ -> a
                    )
                    wanted
                    args
            else
                args
        else
            args

    let found = Dictionary<string, Fable.Type>()

    // `Seq.collect` and `Seq.concat` are generic in the type of the collections too
    // (`'Collection :> seq<'U>`): the library's take sequences, so a function that gives a list
    // gives the sequence of it.
    let info, args =
        match file, fn, info.GenericArgs, args with
        | "Seq", "collect", [ t; _; u ], [ mapping; source ] when
            (match mapping.Type with
             | Fable.LambdaType(_, ret) -> not (isSeqType ret)
             | _ -> false)
            ->
            let x: Fable.Ident =
                {
                    Name = "collected"
                    Type = t
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }

            let seqU = Fable.DeclaredType(seqEntRef, [ u ])

            let wrapped =
                Fable.Lambda(
                    x,
                    Fable.TypeCast(
                        Fable.CurriedApply(
                            mapping,
                            [ Fable.IdentExpr x ],
                            (match mapping.Type with
                             | Fable.LambdaType(_, ret) -> ret
                             | _ -> Fable.Any),
                            None
                        ),
                        seqU
                    ),
                    None
                )

            { info with
                GenericArgs = [ t; u ]
                SignatureArgTypes = []
                MemberRef = None
            },
            [ wrapped; source ]
        | "Seq", "collect", [ t; _; u ], _ ->
            { info with
                GenericArgs = [ t; u ]
                SignatureArgTypes = []
                MemberRef = None
            },
            args
        // (a sequence of lists or arrays: each is seen as a sequence first)
        | "Seq", ("concat" | "transpose"), [ coll; t ], [ source ] when not (isSeqType coll) ->
            let seqT = Fable.DeclaredType(seqEntRef, [ t ])

            let x: Fable.Ident =
                {
                    Name = "part"
                    Type = coll
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }

            let asSeq = Fable.Lambda(x, Fable.TypeCast(Fable.IdentExpr x, seqT), None)

            let mapped =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "Map"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    { Fable.CallInfo.Create(args = [ asSeq; source ]) with GenericArgs = [ coll; seqT ] },
                    Fable.DeclaredType(seqEntRef, [ seqT ]),
                    None
                )

            { info with
                GenericArgs = [ t ]
                SignatureArgTypes = []
                MemberRef = None
            },
            [ mapped ]
        | "Seq", ("concat" | "transpose"), [ _; t ], _ ->
            { info with
                GenericArgs = [ t ]
                SignatureArgTypes = []
                MemberRef = None
            },
            args
        | _ -> info, args

    let args =
        args
        |> List.filter (fun a ->
            match a.Type with
            | Fable.DeclaredType(ent, _) -> ent.FullName <> "Microsoft.FSharp.Control.FSharpAsyncBuilder"
            | _ -> true
        )

    // (the optional timeout and cancellation of `Async.RunSynchronously` and `Start` are not
    // taken)
    let args =
        match file, fn with
        | "Async", ("runSynchronously" | "startImmediate" | "startAsync") -> List.truncate 1 args
        | _ -> args

    // (where FSharp.Core takes a sequence and is given a list, the library takes the list; an
    // empty value whose item type F# left open, `obj` on .NET, gets `unit`: nothing can depend
    // on it)
    // (`Seq.empty` whose type argument Fable gives as `obj`: the result's type says it)
    let info =
        match file, fn, info.GenericArgs, t with
        | "Seq", "empty", [ Fable.Any ], Fable.DeclaredType(_, [ item ]) when item <> Fable.Any ->
            { info with GenericArgs = [ item ] }
        | _ -> info

    // (a function of one type argument: an untyped `None` given to it is of that type)
    let emptyItem =
        match info.GenericArgs with
        | [ only ] when only <> Fable.Any -> only
        | _ -> Fable.Any

    let args =
        args
        |> List.map (fun arg ->
            match arg with
            | _ when
                file = "Seq"
                || file = "Async"
                || file = "Task"
                || file = "ResizeArray"
                || file = "HashSet"
                || file = "Stack"
                || file = "Queue"
                || file = "ListCollector"
                ->
                arg
            | Fable.Value(Fable.NewOption(None, Fable.Any, isStruct), r) ->
                Fable.Value(Fable.NewOption(None, emptyItem, isStruct), r)
            | Uncast inner when
                (match arg.Type with
                 | Fable.DeclaredType(seq, _) -> seq.FullName = "System.Collections.Generic.IEnumerable`1"
                 | _ -> false)
                && (listItem inner.Type).IsSome
                ->
                inner
            | _ -> arg
        )

    // (an instance member: the object's type has the type parameters of its type)
    let calledMember = info.MemberRef |> Option.bind ctx.Com.TryGetMember

    let ownerParams =
        match info.MemberRef with
        | Some(Fable.MemberRef(entRef, _)) ->
            match ctx.Com.TryGetEntity entRef with
            | Some ent when not ent.IsFSharpModule -> ent.GenericParameters |> List.map (fun g -> g.Name)
            | _ -> []
        | _ -> []

    match info.ThisArg, info.MemberRef with
    | Some this, Some(Fable.MemberRef(entRef, _)) when not ownerParams.IsEmpty ->
        unify
            found
            (Fable.DeclaredType(entRef, ownerParams |> List.map (fun n -> Fable.GenericParam(n, false, []))))
            this.Type
    | _ -> ()

    let sigArgs =
        match info.ThisArg with
        | Some _ when info.SignatureArgTypes.Length + 1 = args.Length -> args.Tail
        | _ -> args

    if info.SignatureArgTypes.Length = sigArgs.Length then
        List.iter2
            (fun (pattern: Fable.Type) (arg: Fable.Expr) ->
                match pattern, arg.Type with
                | Fable.DeclaredType(seq, [ item ]), actual when
                    seq.FullName = "System.Collections.Generic.IEnumerable`1"
                    && (listItem actual).IsSome
                    ->
                    unify found item (listItem actual).Value
                | _ -> unify found pattern arg.Type
            )
            info.SignatureArgTypes
            sigArgs

    // what no argument tells (`Map.empty`) is in the call's own type arguments
    let allParams =
        ownerParams
        @ (
            match calledMember with
            | Some m -> m.GenericParameters |> List.map (fun g -> g.Name)
            | None -> []
        )

    if allParams.Length = info.GenericArgs.Length then
        for (n, ty) in List.zip allParams info.GenericArgs do
            if not (found.ContainsKey n) then
                found[n] <- ty

    // (a member of a generic type that is not generic itself: the type arguments of the
    // call are those of the object's type, in their order)
    match info.ThisArg with
    | Some this when
        found.Count <> info.GenericArgs.Length
        && (
            match this.Type with
            | Fable.DeclaredType(_, targs) -> targs.Length = info.GenericArgs.Length
            | _ -> false
        )
        ->
        found.Clear()
        info.GenericArgs |> List.iteri (fun i ty -> found[$"%03d{i}"] <- ty)
    | _ -> ()

    if found.Count <> info.GenericArgs.Length then
        // (no argument tells: the call's own type arguments, in their order, which is the
        // order of their names in FSharp.Core and in the library)
        match info.GenericArgs with
        | given when found.Count = 0 -> given |> List.iteri (fun i ty -> found[$"%03d{i}"] <- ty)
        | _ ->
            fail
                r
                "the Zig target cannot tell the type arguments of this call of %s yet (%A from %A of %A)"
                fn
                (List.ofSeq found.Keys)
                allParams
                info.GenericArgs

    let typeArgs =
        found
        |> Seq.sortWith (fun a b -> System.String.CompareOrdinal(a.Key, b.Key))
        |> Seq.map (fun kv ->
            match kv.Value with
            | Fable.Any -> tAny
            | other -> mapType ctx r other
        )
        |> List.ofSeq

    // (inside the library file itself the function is one of the file's own)
    let own =
        System.IO.Path.GetFileNameWithoutExtension(ctx.Com.CurrentFile) = file
        && ctx.Members.ContainsKey fn

    let target =
        if own then
            fn
        else
            importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + fn

    // (a property is read with a unit argument that the library function does not take; a
    // collection given where FSharp.Core takes a sequence is walked as the list of what it
    // holds)
    let lowerArg (arg: Fable.Expr) : Expr =
        match arg with
        // (these modules take sequences as they are)
        | _ when
            file = "Seq"
            || file = "Async"
            || file = "Task"
            || file = "ResizeArray"
            || file = "HashSet"
            || file = "Stack"
            || file = "Queue"
            || file = "ListCollector"
            ->
            lw ctx arg
        // (a sequence given to a function that takes a list: the list of what it gives)
        | Fable.TypeCast(inner, _)
        | inner when isSeqType inner.Type && isSeqType arg.Type ->
            match inner.Type with
            | Fable.DeclaredType(_, [ item ]) ->
                let itemTy = mapType ctx r item

                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs ->
                        ECall(libraryTarget ctx "Seq" "toList", [ itemTy ], xs, TEnt(listEnt ctx.State, [ itemTy ]))
                    )
            | _ -> lw ctx arg
        | Fable.TypeCast(inner, Fable.DeclaredType(seq, _)) when
            seq.FullName = "System.Collections.Generic.IEnumerable`1"
            && (listItem inner.Type).IsNone
            && (forInSource ctx inner).IsSome
            ->
            match forInSource ctx inner with
            | Some(listExpr, "list") -> listExpr
            | _ -> lw ctx arg
        | _ -> lw ctx arg

    // (a unit argument is not given to the library function, unless it instantiates a generic
    // type parameter like `ReplyChannel<'R>.Reply(())` or `MailboxProcessor<'Msg>.Post(())`, where
    // Zig still has that parameter; otherwise what computes it runs in its place:
    // `async { return raise e }` raises)
    let isPlainUnit (arg: Fable.Expr) =
        match arg with
        | Fable.Value(Fable.UnitConstant, _)
        | Fable.IdentExpr _ -> true
        | _ -> false

    let sigArgGeneric =
        let aligned =
            if info.SignatureArgTypes.Length = args.Length then
                info.SignatureArgTypes |> List.map Some
            elif info.ThisArg.IsSome && info.SignatureArgTypes.Length + 1 = args.Length then
                None :: (info.SignatureArgTypes |> List.map Some)
            else
                args |> List.map (fun _ -> None)

        aligned
        |> List.map (
            function
            | Some(Fable.GenericParam _) -> true
            | _ -> false
        )

    let dropUnitFlags =
        List.zip args sigArgGeneric
        |> List.map (fun (arg, isGenParam) -> isUnit arg.Type && (args.Length = 1 || not isGenParam))

    let keptEntries =
        List.zip args dropUnitFlags
        |> List.filter (fun (arg, dropUnit) -> not (dropUnit && isPlainUnit arg))

    let kept = keptEntries |> List.map fst
    let keptDropFlags = keptEntries |> List.map snd
    let lowered = kept |> List.map lowerArg

    bindArgs
        ctx
        lowered
        (fun xs ->
            let given =
                List.zip keptDropFlags xs
                |> List.filter (fun (dropUnit, _) -> not dropUnit)
                |> List.map snd

            let effects =
                List.zip keptDropFlags xs
                |> List.filter (fun (dropUnit, _) -> dropUnit)
                |> List.map snd

            let call =
                ECall(
                    target,
                    typeArgs,
                    (match given with
                     | [] -> [ EUnit ]
                     | _ -> given),
                    mapType ctx r t
                )

            List.foldBack (fun effect acc -> ESeq(effect, acc)) effects call
        )
