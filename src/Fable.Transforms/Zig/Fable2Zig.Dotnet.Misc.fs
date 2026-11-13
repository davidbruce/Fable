/// .NET's members: enums, Convert and BitConverter (with Base64 and hex), Random, Nullable,
/// Stack and Queue, tuples. The lowering (`Lower.dotnetCall`) asks here in the place these cases
/// had among its own.
module Fable.Transforms.Zig.DotnetMisc

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Lower
open Fable.Transforms.Zig.DotnetHelpers

/// The lowered call, or null when the member is not one of this file's.
let call
    (ctx: Ctx)
    (r: SourceLocation option)
    (entity: string)
    (name: string)
    (info: Fable.CallInfo)
    (t: Fable.Type)
    : Expr
    =
    // (the object of a property or method comes first)
    let args =
        match info.ThisArg with
        | Some this -> this :: info.Args
        | None -> info.Args

    let rt = rt ctx
    let pure' = pure' ctx
    let zigTypeName = zigTypeName r
    let decLit = decLit ctx
    let contents = contents r

    match entity, name, args with
    // `source.Add f` and `source.Subscribe f` of an observable: the Observable module's
    | "Microsoft.FSharp.Control.CommonExtensions", ("AddToObservable" | "SubscribeToObservable"), [ source; f ] ->
        // (an event is given as the observable it also is)
        let source =
            match source.Type, t with
            | Fable.DeclaredType(e, [ _; item ]), _ when e.FullName = "Microsoft.FSharp.Control.IEvent`2" ->
                Fable.TypeCast(
                    source,
                    Fable.DeclaredType(
                        {
                            FullName = "System.IObservable`1"
                            Path = Fable.CoreAssemblyName "System.Runtime"
                        },
                        [ item ]
                    )
                )
            | _ -> source

        libraryCall
            ctx
            r
            "Observable"
            (if name = "AddToObservable" then
                 "add"
             else
                 "subscribe")
            { info with
                ThisArg = None
                SignatureArgTypes = []
            }
            [ f; source ]
            t
    // a member of a .NET interface called on a value of that interface: its function in the
    // struct of function values (`d.Dispose()` of an `IDisposable`)
    | _, _, this :: rest when
        info.ThisArg.IsSome
        && this.Type =
            (match this.Type with
             | Fable.DeclaredType(e, _) when
                 (match e.Path with
                  | Fable.SourcePath _ -> false
                  | _ -> true)
                 && (
                     match ctx.Com.TryGetEntity e with
                     // (the interface, or one it inherits: its members are in its struct too)
                     | Some ent -> ent.IsInterface
                     | None -> false
                 )
                 ->
                 this.Type
             | _ -> Fable.Unit)
        ->
        bindArgs
            ctx
            (lw ctx this :: (rest |> List.map (lw ctx)))
            (fun xs ->
                match caseFields (typeOf xs.Head) "" |> List.tryFind (fun (f, _) -> f = name) with
                | Some(f, fty) ->
                    let args =
                        if xs.Tail.IsEmpty then
                            [ EUnit ]
                        else
                            xs.Tail

                    ECallClo(EGet(xs.Head, PField f, fty), args, mapType ctx r t)
                | None -> fail r "the Zig target cannot find the member %s of %s" name entity
            )
    // (a value boxed and unboxed to its own type, as `use` does with an interface value)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxGeneric" | "UnboxFast"), [ Unboxed inner ] when
        inner.Type <> Fable.Any && mapType ctx r inner.Type = mapType ctx r t
        ->
        lw ctx inner
    // `d.Invoke(a, b)` of a delegate: a call of the function value it is
    | _, "Invoke", f :: rest when
        (match f.Type with
         | Fable.DelegateType _ -> true
         | _ -> false)
        ->
        bindArgs
            ctx
            (lw ctx f :: (rest |> List.map (lw ctx)))
            (fun xs ->
                ECallClo(
                    xs.Head,
                    (if xs.Tail.IsEmpty then
                         [ EUnit ]
                     else
                         xs.Tail),
                    mapType ctx r t
                )
            )
    // F#'s `Event<'T>`: the library's Event.fs
    | "Microsoft.FSharp.Control.FSharpEvent`1", ".ctor", _ -> libraryCall ctx r "Event" "create" info [] t
    | "Microsoft.FSharp.Control.FSharpEvent`1", "Trigger", _ -> libraryCall ctx r "Event" "trigger" info args t
    | "Microsoft.FSharp.Control.FSharpEvent`1", "get_Publish", _ -> libraryCall ctx r "Event" "publish" info args t
    // `using resource f`: `f resource`, then `resource.Dispose()`, also when it raises
    | "Microsoft.FSharp.Core.Operators", "Using", [ resource; f ] ->
        let rid = AST.makeTypedIdent resource.Type "resource"

        let dispose =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "Dispose"
                        Path = Replacements.DotnetPrefix + "System.IDisposable"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(thisArg = Fable.IdentExpr rid),
                Fable.Unit,
                r
            )

        lw
            ctx
            (Fable.Let(
                rid,
                resource,
                Fable.TryCatch(Fable.CurriedApply(f, [ Fable.IdentExpr rid ], t, r), None, Some dispose, r)
            ))
    // ---- enums: numbers of their underlying type ----
    | "System.Enum", "HasFlag", [ v; Uncast flag ] -> pure' "(($0 & $1) == $1)" [ v; flag ] tBool
    | "Microsoft.FSharp.Core.LanguagePrimitives", ("EnumOfValue" | "EnumToValue"), [ x ] ->
        if mapType ctx r x.Type = mapType ctx r t then
            lw ctx x
        else
            bindArgs ctx [ lw ctx x ] (fun xs -> EPrim("conv", xs, mapType ctx r t))
    | "System.Enum", "TryParse", s :: rest ->
        let enumTy =
            match info.GenericArgs with
            | [ e ] -> e
            | _ -> fail r "internal: Enum.TryParse"

        match enumTy with
        | Fable.Number(_, Fable.NumberInfo.IsEnum entRef) ->
            let cases =
                match ctx.Com.TryGetEntity entRef with
                | Some ent ->
                    ent.FSharpFields
                    |> List.choose (fun f ->
                        match f.LiteralValue with
                        | Some v when f.IsStatic -> Some(f.Name, string v)
                        | _ -> None
                    )
                | None -> fail r "the Zig target cannot see the cases of %s" entRef.FullName

            let num = zigTypeName (mapType ctx r enumTy)
            let names = cases |> List.map (fun (n, _) -> "\"" + n + "\"") |> String.concat ", "
            let values = cases |> List.map snd |> String.concat ", "

            let macro =
                $"fable_rt.enumTryParse($R, %s{num}, $0, &.{{ %s{names} }}, &[_]%s{num}{{ %s{values} }})"

            let pairTy = TTuple [ tBool; mapType ctx r enumTy ]

            match rest with
            // (`Enum.TryParse(s, &v)`: the value goes to `v`)
            | [ Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
                ctx.Vars.ContainsKey out.Name
                ->
                let outVar = ctx.Vars[out.Name]
                let pair = ctx.State.NewVar("parsed", pairTy, VLocal, false)
                ctx.State.UsesRuntime <- true

                bindArgs
                    ctx
                    [ lw ctx s ]
                    (fun xs ->
                        ELet(
                            pair,
                            EEmit(macro, xs, pairTy),
                            ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool))
                        )
                    )
            | _ -> pure' macro [ s ] pairTy
        | _ -> fail r "the Zig target does not support Enum.TryParse of this type"
    // (`(||)` and `(&&)` given as functions: their arguments are values already)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators", ("op_BooleanOr" | "op_BooleanAnd"), [ a; b ] ->
        bindArgs
            ctx
            [ lw ctx a; lw ctx b ]
            (fun xs ->
                EEmit(
                    (if name = "op_BooleanOr" then
                         "($0 or $1)"
                     else
                         "($0 and $1)"),
                    xs,
                    tBool
                )
            )
    // `Option.toObj` and `Option.ofObj`: of a type that has null here
    | ("Microsoft.FSharp.Core.OptionModule" | "Microsoft.FSharp.Core.ValueOption"), ("ToObj" | "OfObj"), [ x ] when
        (match
            (if name = "ToObj" then
                 t
             else
                 x.Type)
         with
         | Fable.String
         | Fable.Any -> true
         | _ -> false)
        ->
        if name = "ToObj" then
            pure' "fable_rt.optToObj($0)" [ x ] (mapType ctx r t)
        else
            pure' "fable_rt.optOfObj($0)" [ x ] (mapType ctx r t)
    // ---- System.Convert's text in a base, BitConverter, Base64 and hex ----
    | "System.BitConverter", "GetBytes", [ x ] ->
        pure' $"fable_rt.bitGetBytes(%s{typedArg ctx r x 0})" [ x ] (mapType ctx r t)
    | "System.BitConverter", "get_IsLittleEndian", [] ->
        ELit("(@import(\"builtin\").cpu.arch.endian() == .little)", tBool)
    | "System.BitConverter",
      ("Int64BitsToDouble" | "DoubleToInt64Bits" | "Int32BitsToSingle" | "SingleToInt32Bits" | "UInt64BitsToDouble" | "DoubleToUInt64Bits" | "UInt32BitsToSingle" | "SingleToUInt32Bits"),
      [ x ] -> pure' $"@as($R, @bitCast(%s{typedArg ctx r x 0}))" [ x ] (mapType ctx r t)
    | "System.BitConverter", "ToString", b :: rest ->
        match rest with
        | [] -> rt "fable_rt.bitToString($0, null, null)" [ b ] tStr
        | [ start ] -> rt "fable_rt.bitToString($0, $1, null)" [ b; start ] tStr
        | [ start; n ] -> rt "fable_rt.bitToString($0, $1, $2)" [ b; start; n ] tStr
        | _ -> fail r "the Zig target does not support this BitConverter.ToString yet"
    | "System.BitConverter", conv, [ b; i ] when conv.StartsWith("To", System.StringComparison.Ordinal) ->
        rt "fable_rt.bitTo($R, $0, $1)" [ b; i ] (mapType ctx r t)
    | "System.Convert", ("ToHexString" | "ToHexStringLower"), b :: rest ->
        let lower =
            if name = "ToHexStringLower" then
                "true"
            else
                "false"

        match rest with
        | [] -> rt $"fable_rt.hexOf($0, null, null, %s{lower})" [ b ] tStr
        | [ o; n ] -> rt $"fable_rt.hexOf($0, $1, $2, %s{lower})" [ b; o; n ] tStr
        | _ -> fail r "the Zig target does not support this Convert.%s yet" name
    | "System.Convert", "FromHexString", [ s ] -> rt "fable_rt.hexParse($0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToBase64String", [ b ] -> pure' "fable_rt.base64Of($0)" [ b ] tStr
    | "System.Convert", "FromBase64String", [ s ] -> rt "fable_rt.base64Parse($0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToString", [ x; b ] when
        isInt b
        && (
            match x.Type with
            | Fable.Number _ -> true
            | _ -> false
        )
        ->
        rt $"fable_rt.convToStringBase(%s{typedArg ctx r x 0}, $1)" [ x; b ] tStr
    | "System.Convert", conv, [ s; b ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && s.Type = Fable.String
        && isInt b
        ->
        rt "fable_rt.convParseBase($R, $0, $1)" [ s; b ] (mapType ctx r t)
    | "System.Convert", conv, [ s ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && s.Type = Fable.String
        && conv <> "ToString"
        && conv <> "ToChar"
        ->
        rt "fable_rt.convParse($R, $0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToChar", [ c ] when c.Type = Fable.Char -> lw ctx c
    // (of a char: its number, which must fit)
    | "System.Convert", conv, [ c ] when c.Type = Fable.Char && conv <> "ToString" ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" conv info t
    // (of a float: rounded half to even, and raising where it does not fit)
    | "System.Convert", conv, [ x ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && (
            match x.Type with
            | Fable.Number((Float32 | Float64), _) -> true
            | _ -> false
        )
        && intBits (mapType ctx r t) > 0
        ->
        rt $"fable_rt.convFloatToInt($R, %s{typedArg ctx r x 0})" [ x ] (mapType ctx r t)
    // (of a whole number: the value, which must fit, as a checked conversion has it)
    | "System.Convert", conv, [ x ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && conv <> "ToString"
        && (
            match x.Type with
            | Fable.Number((Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 | NativeInt | UNativeInt), _) ->
                true
            | _ -> false
        )
        && intBits (mapType ctx r t) > 0
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" conv info t
    | "System.Convert", ("ToSingle" | "ToDouble"), [ x ] ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("ToSingle" | "ToDouble"), [ x ] when x.Type <> Fable.String ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "System.Convert", "ToChar", [ x ] -> dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" "ToChar" info t
    // ---- System.Random ----
    | "System.Random", ".ctor", [] -> pure' "fable_rt.randomUnseeded()" [] (mapType ctx r t)
    | "System.Random", ".ctor", [ seed ] -> pure' "fable_rt.randomNew($0)" [ seed ] (mapType ctx r t)
    | "System.Random", "get_Shared", [] -> pure' "fable_rt.randomShared()" [] (mapType ctx r t)
    | "System.Random", "Next", [ rnd ] -> pure' "fable_rt.randomNext($0)" [ rnd ] tI32
    | "System.Random", "Next", [ rnd; max ] -> rt "fable_rt.randomNextMax($0, $1)" [ rnd; max ] tI32
    | "System.Random", "Next", [ rnd; min; max ] -> rt "fable_rt.randomNextRange($0, $1, $2)" [ rnd; min; max ] tI32
    | "System.Random", "NextDouble", [ rnd ] -> pure' "fable_rt.randomNextDouble($0)" [ rnd ] tF64
    | "System.Random", "NextBytes", [ rnd; buffer ] -> pure' "fable_rt.randomNextBytes($0, $1)" [ rnd; buffer ] tVoid
    // ---- `Nullable<T>`: an option ----
    | "System.Nullable`1", ".ctor", [] -> ECon(mapType ctx r t, "None", [], None)
    | "System.Nullable`1", ".ctor", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ECon(mapType ctx r t, "Some", xs, None))
    | "System.Nullable`1", "get_HasValue", [ n ] ->
        bindArgs ctx [ lw ctx n ] (fun xs -> EPrim("not", [ ETest(xs.Head, "None", typeOf xs.Head) ], tBool))
    | "System.Nullable`1", "get_Value", [ n ] -> rt "fable_rt.nullableValue($0)" [ n ] (mapType ctx r t)
    | "System.Nullable`1", "GetValueOrDefault", [ n ] when hasDefault t ->
        pure' "fable_rt.orDefault($R, $0)" [ n ] (mapType ctx r t)
    | "System.Nullable`1", "GetValueOrDefault", [ n; d ] -> pure' "($0 orelse $1)" [ n; d ] (mapType ctx r t)
    // `Nullable.int n` and the other conversions of a nullable: the value converted, if any
    | "Microsoft.FSharp.Linq.NullableModule", conv, [ value ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        ->
        let sourceType =
            match value.Type with
            | Fable.Nullable(s, _)
            | Fable.Option(s, _) -> s
            | s -> s

        let targetType =
            match t with
            | Fable.Nullable(s, _)
            | Fable.Option(s, _) -> s
            | s -> s

        let v = AST.makeTypedIdent sourceType "v"

        let converted =
            if conv = "ToEnum" then
                Fable.TypeCast(Fable.IdentExpr v, targetType)
            else
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = conv
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(args = [ Fable.IdentExpr v ], genArgs = [ sourceType ]),
                    targetType,
                    r
                )

        let mapping = Fable.Delegate([ v ], converted, None, [])

        lw
            ctx
            (Fable.Call(
                Fable.Import(
                    {
                        Selector = "Map"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.OptionModule"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                { info with
                    Args = [ mapping; value ]
                    GenericArgs = [ sourceType; targetType ]
                    SignatureArgTypes = []
                    MemberRef = None
                },
                Fable.Option(targetType, false),
                r
            ))
    // ---- .NET's stack and queue: the library's Stack.fs and Queue.fs ----
    | ("System.Collections.Generic.Stack`1" | "System.Collections.Generic.Queue`1"), _, _ ->
        let file =
            if entity.EndsWith("Stack`1", System.StringComparison.Ordinal) then
                "Stack"
            else
                "Queue"

        let small (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring(1)

        match name, args with
        | ".ctor", [] -> libraryCall ctx r file "create" info [] t
        // (a capacity: nothing to do here)
        | ".ctor", [ n ] when isInt n ->
            bindArgs ctx [ lwStmt ctx n ] (fun _ -> libraryCall ctx r file "create" { info with Args = [] } [] t)
        | ".ctor", [ _ ] -> libraryCall ctx r file "ofSeq" info args t
        | "get_Count", _ -> libraryCall ctx r file "count" info args t
        // `TryPop(&v)` and the others: the value goes to `v`
        | ("TryPop" | "TryPeek" | "TryDequeue"),
          [ q; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]

            let found =
                libraryCall ctx r file (small name) { info with Args = [] } [ q ] (Fable.Option(out.Type, false))

            let opt = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)

            ELet(
                opt,
                found,
                EIf(
                    EPrim("not", [ ETest(EVar opt, "None", TOpt outVar.Ty) ], tBool),
                    ESeq(EAssign(outVar, EGet(EVar opt, PSome, outVar.Ty)), ELit("true", tBool)),
                    ELit("false", tBool),
                    tBool
                )
            )
        | _ -> libraryCall ctx r file (small name) info args t
    // ---- tuples: `Tuple(a, b)`, `Tuple.Create`, struct tuples, and the conversions between
    // them (a tuple is a Zig tuple, struct or not) ----
    | ("System.Tuple`1" | "System.Tuple`2" | "System.Tuple`3" | "System.Tuple`4" | "System.Tuple`5" | "System.Tuple`6" | "System.Tuple`7" | "System.ValueTuple`1" | "System.ValueTuple`2" | "System.ValueTuple`3" | "System.ValueTuple`4" | "System.ValueTuple`5" | "System.ValueTuple`6" | "System.ValueTuple`7"),
      ".ctor",
      items
    | ("System.Tuple" | "System.ValueTuple"), "Create", items ->
        lw ctx (Fable.Value(Fable.NewTuple(items, entity.StartsWith "System.ValueTuple"), r))
    | "System.TupleExtensions", ("ToValueTuple" | "ToTuple"), [ x ] ->
        let items =
            match x.Type with
            | Fable.Tuple(ts, _) -> ts
            | _ -> fail r "internal: not a tuple"

        let tmp = AST.makeTypedIdent x.Type "tuple"

        lw
            ctx
            (Fable.Let(
                tmp,
                x,
                Fable.Value(
                    Fable.NewTuple(
                        items
                        |> List.mapi (fun i t -> Fable.Get(Fable.IdentExpr tmp, Fable.TupleIndex i, t, r)),
                        name = "ToValueTuple"
                    ),
                    r
                )
            ))
    | ("System.Tuple`1" | "System.ValueTuple`1"), "get_Item1", [ x ] -> lw ctx (Fable.Get(x, Fable.TupleIndex 0, t, r))
    | _ -> Unchecked.defaultof<Expr>
