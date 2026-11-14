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

/// `X.TryParse(s, ..., &v)`: the variable of the last argument, a local's address
let private outArgOf (ctx: Ctx) (rest: Fable.Expr list) : Fable.Ident option =
    match List.tryLast rest with
    | Some(Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _)) when
        ctx.Vars.ContainsKey out.Name
        ->
        Some out
    | _ -> None

/// `X.TryParse(s, ..., &v)` of a library type: its `tryParse` gives the pair, the value goes to
/// `v` and the flag is the result
let private tryParseInto (ctx: Ctx) r (info: Fable.CallInfo) (lib: string) (s: Fable.Expr) (out: Fable.Ident) =
    let outVar = ctx.Vars[out.Name]

    let pairIr =
        libraryCall
            ctx
            r
            lib
            "tryParse"
            { info with
                ThisArg = None
                GenericArgs = []
                SignatureArgTypes = []
            }
            [ s ]
            (Fable.Tuple([ Fable.Boolean; out.Type ], false))

    let pair = ctx.State.NewVar("parsed", typeOf pairIr, VLocal, false)

    ELet(pair, pairIr, ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool)))

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
    // `(s :> IEnumerable<'T>).GetEnumerator()` of a sequence: an enumerator over a walk of it
    | "System.Collections.Generic.IEnumerable`1", "GetEnumerator", [ Uncast source ] when
        isSeqType source.Type || (forInSource ctx source).IsSome
        ->
        // (a list or an array: the sequence of it)
        let source =
            if isSeqType source.Type then
                source
            else
                match t with
                | Fable.DeclaredType(_, [ item ]) ->
                    Fable.TypeCast(
                        source,
                        Fable.DeclaredType(
                            {
                                FullName = "System.Collections.Generic.IEnumerable`1"
                                Path = Fable.CoreAssemblyName "System.Runtime"
                            },
                            [ item ]
                        )
                    )
                | _ -> source

        libraryCall
            ctx
            r
            "Seq"
            "getEnumerator"
            { info with
                ThisArg = None
                SignatureArgTypes = []
            }
            [ source ]
            t
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
         | Fable.DeclaredType(e, _) ->
             e.FullName.StartsWith("System.Func`", System.StringComparison.Ordinal)
             || e.FullName.StartsWith("System.Action", System.StringComparison.Ordinal)
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
    // `LanguagePrimitives.GenericZero` and `GenericOne` of a number
    | "Microsoft.FSharp.Core.LanguagePrimitives", ("GenericZero" | "GenericOne" as which), [] when
        (match t with
         | Fable.GenericParam _ -> true
         | _ -> false)
        ->
        ctx.State.UsesRuntime <- true

        EEmit($"""fable_rt.genericNumber($R, %b{which = "GenericOne"})""", [], mapType ctx r t)
    | "Microsoft.FSharp.Core.LanguagePrimitives", ("GenericZero" | "GenericOne" as which), [] when
        (match t with
         | Fable.Number _ -> true
         | _ -> false)
        ->
        let get =
            if which = "GenericZero" then
                "get_Zero"
            else
                "get_One"

        match t with
        | Fable.Number(Decimal, _) -> dotnetCall ctx r "System.Decimal" get info t
        | Fable.Number(BigInt, _) -> dotnetCall ctx r "System.Numerics.BigInteger" get info t
        | _ ->
            let v =
                if which = "GenericZero" then
                    "0"
                else
                    "1"

            EEmit($"@as($R, %s{v})", [], mapType ctx r t)
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
    // (`ExceptionDispatchInfo.Capture(e)`: the exception itself; its `Throw` raises it again)
    | "System.Runtime.ExceptionServices.ExceptionDispatchInfo", "Capture", [ x ] -> lw ctx x
    | "System.Runtime.ExceptionServices.ExceptionDispatchInfo", "Throw", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ERaise(xs.Head, mapType ctx r t))
    // (`unbox` between types kept alike, as UMX's `%` between a type and the same type with a
    // unit of measure: the value itself)
    | "Microsoft.FSharp.Core.Operators", "Unbox", [ x ] when
        x.Type <> Fable.Any && mapType ctx r x.Type = mapType ctx r t
        ->
        lw ctx x
    | "Microsoft.FSharp.Core.Operators", "Unbox", [ Fable.TypeCast(x, Fable.Any) ] when
        x.Type <> Fable.Any && mapType ctx r x.Type = mapType ctx r t
        ->
        lw ctx x
    // (`box e.InnerException`: null when there is none, as on .NET)
    | "Microsoft.FSharp.Core.Operators", "Box", [ Fable.Call(Fable.Import(imp, _, _), inner, _, _) ] when
        imp.Selector = "get_InnerException" && inner.ThisArg.IsSome
        ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx inner.ThisArg.Value ] (fun xs -> EEmit("fable_rt.exnInnerBoxed($0)", xs, tAny))
    // ---- `Fable.Core.Compiler`: what the compiler knows (each other target's flag is false) ----
    | "Fable.Core.Compiler", name, [] ->
        let str (x: string) =
            lw ctx (Fable.Value(Fable.StringConstant x, r))

        let bool (b: bool) =
            lw ctx (Fable.Value(Fable.BoolConstant b, r))

        match name with
        | "version" -> str Literals.VERSION
        | "majorMinorVersion" ->
            let m = System.Text.RegularExpressions.Regex.Match(Literals.VERSION, @"^\d+\.\d+")

            lw
                ctx
                (Fable.Value(Fable.NumberConstant(Fable.NumberValue.Float64(float m.Value), Fable.NumberInfo.Empty), r))
        | "debugMode" -> bool ctx.Com.Options.DebugMode
        | "typedArrays" -> bool ctx.Com.Options.TypedArrays
        | "extension" -> str ctx.Com.Options.FileExtension
        | "triggeredByDependency" -> bool ctx.Com.Options.TriggeredByDependency
        | "isDotnet"
        | "isJavaScript"
        | "isTypeScript"
        | "isPython"
        | "isDart"
        | "isRust"
        | "isPhp"
        | "isBeam" -> bool false
        | _ -> fail r "the Zig target does not support Fable.Core.Compiler.%s yet" name
    // (`type C() as this`: F#'s checks that the object is made before it is used)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "CheckThis", [ x ] -> lw ctx x
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "FailInit", _ ->
        raiseDotnet
            ctx
            r
            "System.InvalidOperationException"
            (ELit(
                "fable_rt.str(\"The initialization of an object or value resulted in an object or value being accessed recursively before it was fully initialized.\")",
                tStr
            ))
            t
    // (`d + t`, `d1 - d2` and the other operators of the dates and times, as F# gives them)
    | "Microsoft.FSharp.Core.Operators", ("op_Addition" | "op_Subtraction"), (a :: _ as args) when
        (match a.Type with
         | Fable.DeclaredType(e, _) ->
             e.FullName = "System.DateTime"
             || e.FullName = "System.DateTimeOffset"
             || e.FullName = "System.TimeOnly"
         | _ -> false)
        ->
        let typ =
            match a.Type with
            | Fable.DeclaredType(e, _) -> e.FullName
            | _ -> "System.DateTime"

        dotnetCall
            ctx
            r
            typ
            name
            { info with
                ThisArg = None
                Args = args
            }
            t
    // (`t1 + t2` and the other operators of TimeSpan, as F# gives them)
    | "Microsoft.FSharp.Core.Operators",
      ("op_Addition" | "op_Subtraction" | "op_Multiply" | "op_Division" | "op_UnaryNegation" | "op_UnaryPlus"),
      args when
        args
        |> List.exists (fun a ->
            match a.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.TimeSpan"
            | _ -> false
        )
        ->
        dotnetCall
            ctx
            r
            "System.TimeSpan"
            name
            { info with
                ThisArg = None
                Args = args
            }
            t
    // ---- reflection: the runtime's fable_reflect.zig ----
    // (`FSharpValue.GetUnionFields(v, t, allowAccessToPrivateRepresentation = true)`: an extension
    // of FSharp.Core's, the same member)
    | "Microsoft.FSharp.Reflection.FSharpReflectionExtensions", extName, _ when
        extName.StartsWith("FSharpValue.", System.StringComparison.Ordinal)
        || extName.StartsWith("FSharpType.", System.StringComparison.Ordinal)
        ->
        let owner = extName.Substring(0, extName.IndexOf '.')
        let rest = extName.Substring(extName.IndexOf '.' + 1)

        let memberName =
            if rest.EndsWith ".Static" then
                rest.Substring(0, rest.Length - 7)
            else
                rest

        dotnetCall ctx r ("Microsoft.FSharp.Reflection." + owner) memberName info t
    // (`Enum.Parse<'T>(s)`: of the type's information, as the value)
    | "System.Enum", "Parse", (s :: rest) when info.GenericArgs.Length = 1 && s.Type = Fable.String ->
        let enumT = info.GenericArgs.Head

        let typeOfT =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "TypeOf"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(genArgs = [ enumT ]),
                Fable.MetaType,
                r
            )

        let parsed =
            dotnetCall
                ctx
                r
                "System.Enum"
                "Parse"
                { info with
                    GenericArgs = []
                    ThisArg = None
                    Args = typeOfT :: s :: rest
                }
                Fable.Any

        bindArgs ctx [ parsed ] (fun xs -> ERt("fable_rt.unbox($R, $0)", xs, mapType ctx r enumT))
    // (`Enum.GetNames(t)` and the others of a Type)
    | "System.Enum", ("GetUnderlyingType" | "GetNames" | "GetName" | "IsDefined" | "Parse"), (t0 :: _ as args) when
        t0.Type = Fable.MetaType
        ->
        ctx.State.UsesRuntime <- true

        match name, args with
        | "GetUnderlyingType", [ x ] ->
            rt "fable_rt.reflect.enumUnderlyingType($0)" [ x ] (TPrim "fable_rt.reflect.Type")
        | "GetNames", [ x ] -> rt "fable_rt.reflect.enumNames($0)" [ x ] (mapType ctx r t)
        | "GetName", [ x; v ] -> rt "fable_rt.reflect.enumName($0, $1)" [ x; Fable.TypeCast(v, Fable.Any) ] tStr
        | "IsDefined", [ x; v ] -> rt "fable_rt.reflect.enumIsDefined($0, $1)" [ x; Fable.TypeCast(v, Fable.Any) ] tBool
        | "Parse", [ x; v ] -> rt "fable_rt.reflect.enumParse($0, $1, false)" [ x; v ] tAny
        | "Parse", [ x; v; ignoreCase ] -> rt "fable_rt.reflect.enumParse($0, $1, $2)" [ x; v; ignoreCase ] tAny
        | _ -> fail r "the Zig target does not support Enum.%s with these arguments yet" name
    | ("Microsoft.FSharp.Core.Operators" | "System.Type" | "System.Object" | "Microsoft.FSharp.Reflection.FSharpType" | "Microsoft.FSharp.Reflection.FSharpValue" | "System.Reflection.PropertyInfo" | "System.Reflection.MemberInfo" | "Microsoft.FSharp.Reflection.UnionCaseInfo"),
      name,
      args when
        (entity <> "Microsoft.FSharp.Core.Operators"
         || name = "TypeOf"
         || name = "TypeDefOf"
         || (name = "IsNull" && args |> List.exists (fun a -> a.Type = Fable.MetaType)))
        && (entity <> "System.Object"
            || name = "GetType"
            || (name = "ReferenceEquals"
                && args |> List.forall (fun a -> (let (Unboxed i) = a in i.Type = Fable.MetaType))))
        ->
        ctx.State.UsesRuntime <- true
        let tType = TPrim "fable_rt.reflect.Type"

        // (the information of a type: of a record, a union, a tuple... from its Zig type; a class,
        // an interface or an enum by its .NET name)
        let rec typeExpr (t: Fable.Type) : string =
            let named (ent: Fable.Entity) (kind: string) (genArgs: Fable.Type list) =
                let args =
                    match genArgs with
                    | [] -> ""
                    | gs ->
                        gs
                        |> List.map (fun g -> IR.zigType (mapType ctx r g))
                        |> String.concat ", "
                        |> sprintf ", .args = .{ %s }"

                // (the type's own type parameters, as these arguments)
                let subst (x: Fable.Type) =
                    let pairs =
                        List.zip
                            (ent.GenericParameters |> List.map (fun p -> p.Name))
                            (if genArgs.Length = ent.GenericParameters.Length then
                                 genArgs
                             else
                                 ent.GenericParameters |> List.map (fun _ -> Fable.Any))
                        |> Map.ofList

                    let rec go (x: Fable.Type) =
                        match x with
                        | Fable.GenericParam(n, _, _) when pairs.ContainsKey n -> pairs[n]
                        | Fable.DeclaredType(e, gs) -> Fable.DeclaredType(e, List.map go gs)
                        | other -> other

                    go x

                let parent =
                    match ent.BaseType with
                    | Some b when kind = ".@\"enum\"" -> ""
                    | Some b when b.Entity.FullName = "System.Object" -> ""
                    | Some b ->
                        match b.Entity.Path with
                        | Fable.SourcePath _ ->
                            $", .parent = %s{typeExpr (subst (Fable.DeclaredType(b.Entity, b.GenericArgs)))}"
                        // (a class of .NET's: by its name)
                        | _ ->
                            $", .parent = fable_rt.reflect.named(.{{ .full_name = \"%s{b.Entity.FullName}\", .kind = .class }})"
                    | None -> ""

                let interfaces =
                    match List.ofSeq ent.DeclaredInterfaces with
                    | [] -> ""
                    | ifs ->
                        ifs
                        |> List.map (fun i -> typeExpr (subst (Fable.DeclaredType(i.Entity, i.GenericArgs))))
                        |> String.concat ", "
                        |> sprintf ", .interfaces = .{ %s }"

                let underlying =
                    if kind = ".@\"enum\"" then
                        let numberType =
                            ent.FSharpFields
                            |> List.tryFind (fun f -> f.Name = "value__")
                            |> Option.map (fun f -> IR.zigType (mapType ctx r f.FieldType))
                            |> Option.defaultValue "i32"

                        // (the cases: names and values)
                        let cases =
                            ent.FSharpFields
                            |> List.filter (fun f -> f.Name <> "value__")
                            |> List.choose (fun f ->
                                match f.LiteralValue with
                                | Some v -> Some(f.Name, System.Convert.ToInt64 v)
                                | None -> None
                            )

                        let names = cases |> List.map (fun (n, _) -> $"\"%s{n}\"") |> String.concat ", "
                        let values = cases |> List.map (fun (_, v) -> $"%d{v}") |> String.concat ", "

                        let valueList =
                            if cases.IsEmpty then
                                ""
                            else
                                $"@as(i64, %s{values})"

                        $", .underlying = %s{numberType}, .enum_names = [_][]const u8{{ %s{names} }}, .enum_values = [_]i64{{ %s{values} }}"
                    else
                        ""

                $"fable_rt.reflect.named(.{{ .full_name = \"%s{dotnetTypeName ctx.Com ent}\", .kind = %s{kind}%s{args}%s{parent}%s{interfaces}%s{underlying} }})"

            match t with
            | Fable.Number(_, Fable.NumberInfo.IsEnum entRef) ->
                match ctx.Com.TryGetEntity entRef with
                | Some ent -> named ent ".@\"enum\"" []
                | None -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"
            | Fable.DeclaredType(entRef, genArgs) ->
                match ctx.Com.TryGetEntity entRef with
                // (an erased union of one field: the type it erases to)
                | Some ent when
                    ent.IsFSharpUnion
                    && ent.Attributes
                       |> Seq.exists (fun a -> a.Entity.FullName = "Fable.Core.EraseAttribute")
                    && ent.UnionCases.Length = 1
                    && ent.UnionCases.Head.UnionCaseFields.Length = 1
                    ->
                    let field = ent.UnionCases.Head.UnionCaseFields.Head.FieldType

                    let pairs =
                        List.zip (ent.GenericParameters |> List.map (fun p -> p.Name)) genArgs
                        |> Map.ofList

                    let rec go (x: Fable.Type) =
                        match x with
                        | Fable.GenericParam(n, _, _) when pairs.ContainsKey n -> pairs[n]
                        | Fable.DeclaredType(e, gs) -> Fable.DeclaredType(e, List.map go gs)
                        | other -> other

                    typeExpr (go field)
                | Some ent when ent.IsInterface -> named ent ".interface" genArgs
                | Some ent when
                    not ent.IsFSharpRecord
                    && not ent.IsFSharpUnion
                    && (
                        match entRef.Path with
                        | Fable.SourcePath _ -> true
                        | _ -> false
                    )
                    ->
                    named ent ".class" genArgs
                | _ when libraryValueTypes.ContainsKey entRef.FullName ->
                    $"fable_rt.reflect.named(.{{ .full_name = \"%s{entRef.FullName}\", .kind = .class }})"
                | _ -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"
            | _ -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"

        let typeOfIr (t: Fable.Type) = EEmit(typeExpr t, [], tType)

        // (a boxed argument: the type it is of, when it is known here)
        let staticTypeOf (x: Fable.Expr) =
            let (Unboxed inner) = x
            inner.Type

        let rfl (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            rt $"fable_rt.reflect.%s{fn}(%s{holes})" xs ty

        let pureRfl (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            pure' $"fable_rt.reflect.%s{fn}(%s{holes})" xs ty

        // (the optional `allowAccessToPrivateRepresentation` and binding flags: nothing here)
        let isFlag (x: Fable.Expr) =
            match x.Type with
            | Fable.Option(Fable.Boolean, _) -> true
            | Fable.Option(Fable.Number(_, Fable.NumberInfo.IsEnum _), _)
            | Fable.Number(_, Fable.NumberInfo.IsEnum _) -> true
            | _ -> false

        let args = args |> List.filter (fun a -> not (isFlag a) && a.Type <> Fable.Unit)
        let resultTy = mapType ctx r t

        // (a value of a type known here: its type's information and the value boxed)
        let withType (o: Fable.Expr) (k: Expr -> Expr -> Expr) =
            let st = staticTypeOf o

            let typeIr =
                if st = Fable.Any then
                    fail r "the Zig target needs the type of the value given to reflection to be known (here it is obj)"
                else
                    typeOfIr st

            bindArgs ctx [ typeIr; lw ctx (Fable.TypeCast(o, Fable.Any)) ] (fun xs -> k xs.[0] xs.[1])

        match entity, name, args with
        | _, "TypeOf", [] -> typeOfIr info.GenericArgs.Head
        | _, "TypeDefOf", [] -> EEmit($"fable_rt.reflect.definitionOf(%s{typeExpr info.GenericArgs.Head})", [], tType)
        | "System.Object", "GetType", [ x ] -> bindArgs ctx [ lw ctx x ] (fun _ -> typeOfIr x.Type)
        // (two Type objects: the same type information)
        | "System.Object", "ReferenceEquals", [ Unboxed a; Unboxed b ] -> pure' "($0 == $1)" [ a; b ] tBool
        // System.Type
        | _, ("get_FullName" | "get_Name" | "get_Namespace" | "ToString"), [ x ] when
            x.Type = Fable.MetaType
            || (
                match x.Type with
                | Fable.DeclaredType(e, _) -> e.FullName = "System.Type"
                | _ -> false
            )
            ->
            let fn =
                match name with
                | "get_FullName" -> "fullName"
                | "get_Name" -> "name"
                | "get_Namespace" -> "namespace"
                | _ -> "toString"

            pureRfl fn [ x ] tStr
        | _, "get_IsGenericType", [ x ] -> pureRfl "isGenericType" [ x ] tBool
        | _, "get_IsGenericTypeDefinition", [ x ] -> pureRfl "isGenericTypeDefinition" [ x ] tBool
        | _, "get_IsArray", [ x ] -> pureRfl "isArray" [ x ] tBool
        | _, "get_IsEnum", [ x ] -> pureRfl "isEnum" [ x ] tBool
        | _, "get_IsClass", [ x ] -> pureRfl "isClass" [ x ] tBool
        | _, "get_IsInterface", [ x ] -> pureRfl "isInterface" [ x ] tBool
        | _, "GetElementType", [ x ] -> pureRfl "elementOrNull" [ x ] tType
        | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] -> pureRfl "isNullType" [ x ] tBool
        | _, "IsSubclassOf", [ a; b ] -> pureRfl "isSubclassOf" [ a; b ] tBool
        | _, "GetInterface", [ x; n ] ->
            pureRfl "getInterface" [ x; n; Fable.Value(Fable.BoolConstant false, None) ] tType
        | _, "GetInterface", [ x; n; ignoreCase ] -> pureRfl "getInterface" [ x; n; ignoreCase ] tType
        | _, "GetEnumUnderlyingType", [ x ] -> rfl "enumUnderlyingType" [ x ] tType
        | _, "GetEnumNames", [ x ] -> rfl "enumNames" [ x ] resultTy
        | _, "IsAssignableFrom", [ a; b ] -> pureRfl "isAssignableFrom" [ a; b ] tBool
        // (a value whose type cannot hold others (a record, a union, a number...): by that type;
        // an object: by its class)
        | _, "IsInstanceOfType", [ x; o ] ->
            let (Unboxed inner) = o

            let dynamic =
                match inner.Type with
                | Fable.Any -> true
                | Fable.DeclaredType(e, _) ->
                    (objInfo ctx r e).IsSome
                    || (
                        match ctx.Com.TryGetEntity e with
                        | Some ent -> ent.IsInterface
                        | None -> false
                    )
                | _ -> false

            if dynamic then
                pureRfl "isInstanceOf" [ x; Fable.TypeCast(inner, Fable.Any) ] tBool
            else
                bindArgs
                    ctx
                    [ lw ctx x; lw ctx inner; typeOfIr inner.Type ]
                    (fun xs -> EEmit("fable_rt.reflect.isAssignableFrom($0, $2)", xs, tBool))
        | _, "GetGenericTypeDefinition", [ x ] -> rfl "genericDefinition" [ x ] tType
        | _, ("get_GenericTypeArguments" | "GetGenericArguments"), [ x ] -> pureRfl "genericArguments" [ x ] resultTy
        | _, "Equals", [ a; b ] -> pureRfl "equals" [ a; b ] tBool
        // FSharpType
        | "Microsoft.FSharp.Reflection.FSharpType", ("IsRecord" | "IsUnion" | "IsTuple" | "IsFunction"), [ x ] ->
            pureRfl (name.Substring(0, 1).ToLowerInvariant() + name.Substring 1) [ x ] tBool
        | "Microsoft.FSharp.Reflection.FSharpType", "GetRecordFields", [ x ] -> rfl "recordFields" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetUnionCases", [ x ] -> rfl "unionCases" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetTupleElements", [ x ] -> rfl "tupleElements" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetFunctionElements", [ x ] ->
            rfl "functionElements" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "MakeTupleType", [ xs ] -> pureRfl "makeTupleType" [ xs ] tType
        // FSharpValue
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetRecordFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getRecordFields($0, $1)", [ t; v ], resultTy))
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetTupleFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getTupleFields($0, $1)", [ t; v ], resultTy))
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetTupleField", [ o; i ] ->
            withType
                o
                (fun t v ->
                    bindArgs
                        ctx
                        [ lw ctx i ]
                        (fun is -> ERt("fable_rt.reflect.getTupleField($0, $1, $2)", [ t; v; is.Head ], resultTy))
                )
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetRecordField", [ o; p ] ->
            rfl "getRecordField" [ o; p ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeRecord", [ ty; vals ] ->
            rfl "makeRecord" [ ty; vals ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeTuple", [ vals; ty ] -> rfl "makeTuple" [ vals; ty ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeUnion", [ c; vals ] -> rfl "makeUnion" [ c; vals ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetUnionFields", [ o; ty ] ->
            rfl "getUnionFields" [ ty; o ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetUnionFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getUnionFields($0, $1)", [ t; v ], resultTy))
        // PropertyInfo, UnionCaseInfo
        | _, "get_Name", [ x ] when
            (match x.Type with
             | Fable.DeclaredType(e, _) -> e.FullName.EndsWith "PropertyInfo" || e.FullName.EndsWith "MemberInfo"
             | _ -> false)
            ->
            pureRfl "propertyName" [ x ] tStr
        | _, "get_PropertyType", [ x ] -> pureRfl "propertyType" [ x ] tType
        | _, "GetValue", p :: o :: _ -> rfl "propertyValue" [ p; o ] resultTy
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_Name", [ c ] -> pureRfl "caseName" [ c ] tStr
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_Tag", [ c ] -> pureRfl "caseTag" [ c ] tI32
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "GetFields", [ c ] -> pureRfl "caseFieldsOf" [ c ] resultTy
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_DeclaringType", [ c ] ->
            pureRfl "caseDeclaringType" [ c ] tType
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet (%A)"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
                (args |> List.map (fun a -> a.Type))
    // ---- files, directories, paths, the environment: the library's Path.fs and fable_io.zig ----
    | ("System.IO.Path" | "System.IO.File" | "System.IO.Directory" | "System.IO.DirectoryInfo" | "System.Environment"),
      name,
      args when
        not (
            entity = "System.Environment"
            && name <> "GetEnvironmentVariable"
            && name <> "get_CurrentDirectory"
        )
        ->
        let call fn xs =
            libraryCall
                ctx
                r
                "Path"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let io (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            ctx.State.UsesRuntime <- true
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            rt $"fable_rt.io.%s{fn}(%s{holes})" xs ty

        let pure'' (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            ctx.State.UsesRuntime <- true
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            pure' $"fable_rt.io.%s{fn}(%s{holes})" xs ty

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        let boolConst (b: bool) = Fable.Value(Fable.BoolConstant b, None)

        // (Path.Combine(a, b, c) and the array form: an array of the parts)
        let partsArray (parts: Fable.Expr list) =
            match parts with
            | [ single ] when
                (match single.Type with
                 | Fable.Array _ -> true
                 | _ -> false)
                ->
                single
            | _ -> Fable.Value(Fable.NewArray(Fable.ArrayValues parts, Fable.String, Fable.MutableArray), None)

        match entity, name, args with
        // Path
        | "System.IO.Path",
          ("GetFileName" | "GetExtension" | "HasExtension" | "GetFileNameWithoutExtension" | "GetDirectoryName" | "IsPathRooted" | "GetPathRoot"),
          [ p ] -> call (lowerFirst name) [ p ]
        | "System.IO.Path", "ChangeExtension", [ p; e ] -> call "changeExtension" [ p; e ]
        | "System.IO.Path", "Combine", parts -> call "combineAll" [ partsArray parts ]
        | "System.IO.Path", "Join", parts -> call "joinAll" [ partsArray parts ]
        | "System.IO.Path", "GetFullPath", [ p ] -> io "fullPath" [ p ] tStr
        | "System.IO.Path", "GetTempPath", [] -> pure'' "tempPath" [] tStr
        | "System.IO.Path", "GetTempFileName", [] -> io "tempFileName" [] tStr
        | "System.IO.Path", "GetRandomFileName", [] -> pure'' "randomFileName" [] tStr
        | "System.IO.Path",
          ("get_DirectorySeparatorChar" | "get_AltDirectorySeparatorChar" | "get_PathSeparator" | "get_VolumeSeparatorChar"),
          [] -> call (lowerFirst (name.Substring 4)) [ Fable.Value(Fable.UnitConstant, None) ]
        | "System.IO.Path", ("GetInvalidFileNameChars" | "GetInvalidPathChars"), [] ->
            call (lowerFirst name) [ Fable.Value(Fable.UnitConstant, None) ]
        // File
        | "System.IO.File", "ReadAllText", p :: _ -> io "readAllText" [ p ] tStr
        | "System.IO.File", "ReadAllBytes", [ p ] -> io "readAllBytes" [ p ] (mapType ctx r t)
        | "System.IO.File", "WriteAllText", p :: text :: _ -> io "writeAllText" [ p; text; boolConst false ] tVoid
        | "System.IO.File", "AppendAllText", p :: text :: _ -> io "writeAllText" [ p; text; boolConst true ] tVoid
        | "System.IO.File", "WriteAllBytes", [ p; bytes ] -> io "writeAllBytes" [ p; bytes ] tVoid
        | "System.IO.File", "ReadAllLines", p :: _ -> call "readAllLines" [ p ]
        | "System.IO.File", "WriteAllLines", p :: lines :: _ when
            (match lines.Type with
             | Fable.Array _ -> true
             | _ -> false)
            ->
            call "writeAllLines" [ p; lines ]
        | "System.IO.File", "AppendAllLines", p :: lines :: _ when
            (match lines.Type with
             | Fable.Array _ -> true
             | _ -> false)
            ->
            call "appendAllLines" [ p; lines ]
        | "System.IO.File", "Exists", [ p ] -> pure'' "fileExists" [ p ] tBool
        | "System.IO.File", "Delete", [ p ] -> io "deleteFile" [ p ] tVoid
        // Directory
        | "System.IO.Directory", "Exists", [ p ] -> pure'' "dirExists" [ p ] tBool
        | "System.IO.Directory", "CreateDirectory", [ p ] -> call "createDirectory" [ p ]
        | "System.IO.Directory", "Delete", [ p ] -> io "deleteDirectory" [ p ] tVoid
        | "System.IO.Directory", "GetCurrentDirectory", [] -> pure'' "currentDirectory" [] tStr
        | "System.IO.DirectoryInfo", "get_FullName", [ d ] -> call "directoryInfoFullName" [ d ]
        | "System.IO.DirectoryInfo", "get_Name", [ d ] -> call "directoryInfoName" [ d ]
        // Environment
        | "System.Environment", "GetEnvironmentVariable", [ n ] -> pure'' "getEnv" [ n ] tStr
        | "System.Environment", "get_CurrentDirectory", [] -> pure'' "currentDirectory" [] tStr
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
    // ---- regular expressions: the library's Regex.fs ----
    | ("System.Text.RegularExpressions.Regex" | "System.Text.RegularExpressions.Match" | "System.Text.RegularExpressions.Group" | "System.Text.RegularExpressions.Capture" | "System.Text.RegularExpressions.MatchCollection" | "System.Text.RegularExpressions.GroupCollection"),
      name,
      args ->
        let call fn xs =
            libraryCall
                ctx
                r
                "Regex"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let typeName (x: Fable.Expr) =
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName.Substring(e.FullName.LastIndexOf '.' + 1)
            | _ -> ""

        let regexType =
            Fable.DeclaredType(
                {
                    FullName = "System.Text.RegularExpressions.Regex"
                    Path = Fable.CoreAssemblyName "System.Text.RegularExpressions"
                },
                []
            )

        let int32 (x: Fable.Expr) =
            Fable.TypeCast(x, Fable.Number(Int32, Fable.NumberInfo.Empty))

        let zero =
            Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 0, Fable.NumberInfo.Empty), None)

        // (a static member's regex: a new one of the pattern and the options)
        let made (pattern: Fable.Expr) (options: Fable.Expr option) =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = ".ctor"
                        Path = Replacements.DotnetPrefix + "System.Text.RegularExpressions.Regex"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(
                    args =
                        (match options with
                         | Some o -> [ pattern; o ]
                         | None -> [ pattern ])
                ),
                regexType,
                r
            )

        let isString (x: Fable.Expr) = x.Type = Fable.String

        // (a MatchEvaluator: a function of the match)
        let replaceIn (re: Fable.Expr) (input: Fable.Expr) (rep: Fable.Expr) (rest: Fable.Expr list) =
            let fn, count =
                if isString rep then
                    "replace", "replaceCount"
                else
                    "replaceWith", "replaceWithCount"

            match rest with
            | [] -> call fn [ re; input; rep ]
            | [ c ] -> call count [ re; input; rep; c ]
            | [ c; s ] ->
                call
                    (fn
                     + if isString rep then
                           "From"
                       else
                           "From")
                    [ re; input; rep; c; s ]
            | _ -> fail r "the Zig target does not support this Regex.Replace yet"

        let isRegex (x: Fable.Expr) =
            x.Type = Fable.Regex || typeName x = "Regex"

        let isMatch (x: Fable.Expr) = typeName x = "Match"

        match name, args with
        // Regex
        | ".ctor", [ p ] -> call "ofPattern" [ p ]
        | ".ctor", [ p; o ] -> call "create" [ p; int32 o ]
        | ".ctor", [ p; o; _timeout ] -> call "create" [ p; int32 o ]
        | "Escape", [ s ] -> call "escape" [ s ]
        | "Unescape", [ s ] -> call "unescape" [ s ]
        | "IsMatch", [ re; s ] when isRegex re -> call "isMatch" [ re; s ]
        | "IsMatch", [ re; s; at ] when isRegex re -> call "isMatchFrom" [ re; s; at ]
        | "IsMatch", s :: p :: rest -> call "isMatch" [ made p (List.tryHead rest); s ]
        | "Match", [ re; s ] when isRegex re -> call "matchOf" [ re; s ]
        | "Match", [ re; s; at ] when isRegex re -> call "matchFrom" [ re; s; at ]
        | "Match", s :: p :: rest -> call "matchOf" [ made p (List.tryHead rest); s ]
        | "Matches", [ re; s ] when isRegex re -> call "matches" [ re; s ]
        | "Matches", [ re; s; at ] when isRegex re -> call "matchesFrom" [ re; s; at ]
        | "Matches", s :: p :: rest -> call "matches" [ made p (List.tryHead rest); s ]
        | "Replace", re :: s :: rep :: rest when isRegex re -> replaceIn re s rep rest
        | "Replace", s :: p :: rep :: rest -> replaceIn (made p (List.tryHead rest)) s rep []
        | "Split", [ re; s ] when isRegex re -> call "split" [ re; s ]
        | "Split", [ re; s; c ] when isRegex re -> call "splitCount" [ re; s; c ]
        | "Split", [ re; s; c; at ] when isRegex re -> call "splitFrom" [ re; s; c; at ]
        | "Split", s :: p :: rest -> call "split" [ made p (List.tryHead rest); s ]
        | "get_Options", [ re ] -> call "options" [ re ]
        | "GetGroupNames", [ re ] -> call "getGroupNames" [ re ]
        | "GetGroupNumbers", [ re ] -> call "getGroupNumbers" [ re ]
        | "ToString", [ re ] when isRegex re -> call "toString" [ re ]
        // Match (also a Group), Group
        | "get_Groups", [ m ] -> call "groups" [ m ]
        | "NextMatch", [ m ] -> call "nextMatch" [ m ]
        | ("get_Success" | "get_Index" | "get_Length" | "get_Value" | "get_Name"), [ g ] ->
            let field = name.Substring 4

            call
                ((if isMatch g then
                      "match"
                  else
                      "group")
                 + field)
                [ g ]
        | "ToString", [ g ] ->
            call
                (if isMatch g then
                     "matchValue"
                 else
                     "groupToString")
                [ g ]
        // the collections
        | "get_Count", [ c ] ->
            call
                (if typeName c = "MatchCollection" then
                     "matchesCount"
                 else
                     "groupsCount")
                [ c ]
        | "get_Item", [ c; i ] when typeName c = "MatchCollection" -> call "matchAt" [ c; i ]
        | "get_Item", [ c; key ] when isString key -> call "groupNamed" [ c; key ]
        | "get_Item", [ c; i ] -> call "groupAt" [ c; i ]
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
    // ---- `System.Diagnostics.Stopwatch` and `Thread.Sleep`: the library's Stopwatch.fs ----
    | ("System.Diagnostics.Stopwatch" | "System.Threading.Thread"), name, args ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "Stopwatch"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        // (`Thread.Sleep`: the library's Async.fs, whose timers run while it sleeps)
        let sleep ms =
            libraryCall
                ctx
                r
                "Async"
                "threadSleep"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ ms ]
                t

        match name, args with
        | "Sleep", [ ms ] when ms.Type = Fable.Number(Int32, Fable.NumberInfo.Empty) -> sleep ms
        | "Sleep", [ span ] ->
            // (`Thread.Sleep(timeSpan)`: its whole milliseconds)
            let ms =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "get_TotalMilliseconds"
                            Path = Replacements.DotnetPrefix + "System.TimeSpan"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(thisArg = span),
                    Fable.Number(Float64, Fable.NumberInfo.Empty),
                    r
                )

            sleep (Fable.TypeCast(ms, Fable.Number(Int32, Fable.NumberInfo.Empty)))
        | ".ctor", [] -> call "create" unitArg
        | ("StartNew" | "GetTimestamp" | "get_Frequency" | "get_IsHighResolution"), [] ->
            let n =
                if name.StartsWith("get_", System.StringComparison.Ordinal) then
                    name.Substring 4
                else
                    name

            call (lowerFirst n) unitArg
        | "GetElapsedTime", [ start ] -> call "getElapsedTimeSince" [ start ]
        | "GetElapsedTime", [ start; finish ] -> call "getElapsedTime" [ start; finish ]
        | ("Start" | "Stop" | "Reset" | "Restart"), [ w ] -> call (lowerFirst name) [ w ]
        | ("get_IsRunning" | "get_Elapsed" | "get_ElapsedMilliseconds" | "get_ElapsedTicks"), [ w ] ->
            call (lowerFirst (name.Substring 4)) [ w ]
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
    // ---- `System.DateOnly` and `System.TimeOnly`: the library's DateOnly.fs ----
    | ("System.DateOnly" | "System.TimeOnly" as typ), name, args ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]
        let isDate = typ = "System.DateOnly"

        let call fn xs =
            libraryCall
                ctx
                r
                "DateOnly"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        // (TimeOnly's functions are named `time...` where DateOnly has the same name)
        let timeName (n: string) =
            "time" + n.Substring(0, 1).ToUpperInvariant() + n.Substring 1

        let fn (n: string) =
            if isDate then
                n
            else
                timeName n

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        let isTypeArg (fullName: string) (x: Fable.Expr) =
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = fullName
            | _ -> false

        let kindArg (x: Fable.Expr) =
            Fable.TypeCast(x, Fable.Number(Int32, Fable.NumberInfo.Empty))

        let int32Const (v: int) =
            Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 v, Fable.NumberInfo.Empty), None)

        match name, args with
        | ".ctor", [] -> call (fn "minValue") unitArg
        | ".ctor", [ y; m; d ] when isDate -> call "create" [ y; m; d ]
        | ".ctor", [ ticks ] when not isDate -> call "timeOfTicks" [ ticks ]
        | ".ctor", [ h; m ] -> call "time2" [ h; m ]
        | ".ctor", [ h; m; s ] -> call "time3" [ h; m; s ]
        | ".ctor", [ h; m; s; ms ] -> call "time4" [ h; m; s; ms ]
        | ".ctor", [ h; m; s; ms; us ] -> call "time5" [ h; m; s; ms; us ]
        | ("get_MinValue" | "get_MaxValue"), [] -> call (fn (lowerFirst (name.Substring 4))) unitArg
        | "FromDayNumber", [ n ] -> call "fromDayNumber" [ n ]
        | "FromDateTime", [ d ] -> call (fn "fromDateTime") [ d ]
        | "FromTimeSpan", [ s ] -> call "timeFromTimeSpan" [ s ]
        | "get_Ticks", [ x ] -> call "timeTicks" [ x ]
        | getter, [ x ] when getter.StartsWith("get_", System.StringComparison.Ordinal) ->
            call (lowerFirst (getter.Substring 4)) [ x ]
        | ("AddDays" | "AddMonths" | "AddYears"), [ d; v ] when isDate -> call (lowerFirst name) [ d; v ]
        | ("Add" | "AddHours" | "AddMinutes"), [ x; v ] when not isDate -> call (timeName (lowerFirst name)) [ x; v ]
        | ("Add" | "AddHours" | "AddMinutes"), [ x; v; _ ] when not isDate ->
            // (the days wrapped, an out argument: not given)
            call (timeName (lowerFirst name)) [ x; v ]
        | "op_Subtraction", [ a; b ] when not isDate -> call "timeSubtract" [ a; b ]
        | "IsBetween", [ x; a; b ] -> call "isBetween" [ x; a; b ]
        | "ToTimeSpan", [ x ] -> call "toTimeSpan" [ x ]
        | "ToDateTime", [ d; tm ] -> call "toDateTime" [ d; tm; int32Const 0 ]
        | "ToDateTime", [ d; tm; k ] -> call "toDateTime" [ d; tm; kindArg k ]
        | ("Compare" | "CompareTo"), [ a; b ] ->
            call
                (if isDate then
                     "compare"
                 else
                     "timeCompare")
                [ a; b ]
        | "ToString", [ x ] -> call (fn "toString") [ x ]
        | "ToString", x :: format :: _ when format.Type = Fable.String -> call (fn "toStringFormat") [ x; format ]
        | "ToString", [ x; _ ] -> call (fn "toString") [ x ]
        | ("op_Equality" | "op_Inequality" | "op_LessThan" | "op_LessThanOrEqual" | "op_GreaterThan" | "op_GreaterThanOrEqual"),
          [ a; b ] when isTypeArg typ b ->
            let op =
                match name with
                | "op_Equality" -> "=="
                | "op_Inequality" -> "!="
                | "op_LessThan" -> "<"
                | "op_LessThanOrEqual" -> "<="
                | "op_GreaterThan" -> ">"
                | _ -> ">="

            EPrim(
                op,
                [
                    call
                        (if isDate then
                             "compare"
                         else
                             "timeCompare")
                        [ a; b ]
                    ELit("0", tI32)
                ],
                tBool
            )
        | _ -> fail r "the Zig target does not support %s.%s with these arguments yet" (typ.Substring 7) name
    // ---- `System.DateTimeOffset`: the library's DateTimeOffset.fs ----
    | "System.DateTimeOffset", name, args ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "DateTimeOffset"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let isType (fullName: string) (x: Fable.Expr) =
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = fullName
            | _ -> false

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        match name, args with
        | ".ctor", [] -> call "minValue" unitArg
        | (".ctor" | "op_Implicit"), [ d ] -> call "ofDateTime" [ d ]
        | ".ctor", [ d; o ] when isType "System.DateTime" d -> call "ofDateTimeOffset" [ d; o ]
        | ".ctor", [ ticks; o ] -> call "ofTicks" [ ticks; o ]
        | ".ctor", [ d; tm; o ] -> call "ofDateAndTime" [ d; tm; o ]
        | ".ctor", [ y; mo; d; h; mi; s; o ] -> call "create7" [ y; mo; d; h; mi; s; o ]
        | ".ctor", [ y; mo; d; h; mi; s; ms; o ] -> call "create8" [ y; mo; d; h; mi; s; ms; o ]
        | ".ctor", [ y; mo; d; h; mi; s; ms; us; o ] -> call "create9" [ y; mo; d; h; mi; s; ms; us; o ]
        | ("get_Now" | "get_UtcNow" | "get_MinValue" | "get_MaxValue" | "get_UnixEpoch"), [] ->
            call (lowerFirst (name.Substring 4)) unitArg
        | ("FromUnixTimeSeconds" | "FromUnixTimeMilliseconds"), [ v ] -> call (lowerFirst name) [ v ]
        | getter, [ x ] when getter.StartsWith("get_", System.StringComparison.Ordinal) ->
            call (lowerFirst (getter.Substring 4)) [ x ]
        | ("Add" | "op_Addition"), [ a; b ] -> call "add" [ a; b ]
        | ("Subtract" | "op_Subtraction"), [ a; b ] when isType "System.DateTimeOffset" b ->
            call "subtractOffset" [ a; b ]
        | ("Subtract" | "op_Subtraction"), [ a; b ] -> call "subtract" [ a; b ]
        | ("AddTicks" | "AddDays" | "AddHours" | "AddMinutes" | "AddSeconds" | "AddMilliseconds" | "AddMicroseconds" | "AddMonths" | "AddYears" | "ToOffset"),
          [ a; v ] -> call (lowerFirst name) [ a; v ]
        | ("ToUniversalTime" | "ToLocalTime" | "ToUnixTimeSeconds" | "ToUnixTimeMilliseconds"), [ a ] ->
            call (lowerFirst name) [ a ]
        | ("Compare" | "CompareTo"), [ a; b ] -> call "compare" [ a; b ]
        | "Equals", [ a; b ] -> call "equals" [ a; b ]
        | "EqualsExact", [ a; b ] -> call "equalsExact" [ a; b ]
        | ("op_Equality" | "op_Inequality" | "op_LessThan" | "op_LessThanOrEqual" | "op_GreaterThan" | "op_GreaterThanOrEqual"),
          [ a; b ] ->
            let op =
                match name with
                | "op_Equality" -> "=="
                | "op_Inequality" -> "!="
                | "op_LessThan" -> "<"
                | "op_LessThanOrEqual" -> "<="
                | "op_GreaterThan" -> ">"
                | _ -> ">="

            EPrim(op, [ call "compare" [ a; b ]; ELit("0", tI32) ], tBool)
        | "ToString", [ x ] -> call "toString" [ x ]
        | "ToString", x :: format :: _ when format.Type = Fable.String -> call "toStringFormat" [ x; format ]
        | "ToString", [ x; _ ] -> call "toString" [ x ]
        | "Parse", s :: _ -> call "parse" [ s ]
        | "TryParse", s :: rest when
            (match t with
             | Fable.Tuple _ -> true
             | _ -> false)
            && rest.Length <= 2
            ->
            call "tryParse" [ s ]
        | "TryParse", s :: rest when (outArgOf ctx rest).IsSome ->
            tryParseInto ctx r info "DateTimeOffset" s (outArgOf ctx rest).Value
        | _ -> fail r "the Zig target does not support DateTimeOffset.%s with these arguments yet" name
    // ---- `System.DateTime`: the library's DateTime.fs ----
    | "System.DateTime", name, args ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "DateTime"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let isType (fullName: string) (x: Fable.Expr) =
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = fullName
            | Fable.Number(_, Fable.NumberInfo.IsEnum e) -> e.FullName = fullName
            | _ -> false

        let isKind = isType "System.DateTimeKind"
        let isTimeSpan = isType "System.TimeSpan"
        let isDate = isType "System.DateTime"

        // (a DateTimeKind, an enum, as its number)
        let kindArg (x: Fable.Expr) =
            Fable.TypeCast(x, Fable.Number(Int32, Fable.NumberInfo.Empty))

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        match name, args with
        | ".ctor", [] -> call "minValue" unitArg
        | ".ctor", [ ticks ] -> call "ofTicks" [ ticks ]
        | ".ctor", [ ticks; k ] when isKind k -> call "ofTicksKind" [ ticks; kindArg k ]
        | ".ctor", [ y; m; d ] -> call "create3" [ y; m; d ]
        | ".ctor", [ y; mo; d; h; mi; s ] -> call "create6" [ y; mo; d; h; mi; s ]
        | ".ctor", [ y; mo; d; h; mi; s; k ] when isKind k -> call "create6Kind" [ y; mo; d; h; mi; s; kindArg k ]
        | ".ctor", [ y; mo; d; h; mi; s; ms ] -> call "create7" [ y; mo; d; h; mi; s; ms ]
        | ".ctor", [ y; mo; d; h; mi; s; ms; k ] when isKind k ->
            call "create7Kind" [ y; mo; d; h; mi; s; ms; kindArg k ]
        | ".ctor", [ y; mo; d; h; mi; s; ms; us ] -> call "create8" [ y; mo; d; h; mi; s; ms; us ]
        | ".ctor", [ y; mo; d; h; mi; s; ms; us; k ] when isKind k ->
            call "create8Kind" [ y; mo; d; h; mi; s; ms; us; kindArg k ]
        | ("get_Now" | "get_UtcNow" | "get_Today" | "get_MinValue" | "get_MaxValue"), [] ->
            call (lowerFirst (name.Substring 4)) unitArg
        | "get_UnixEpoch", [] ->
            call
                "ofTicksKind"
                [
                    Fable.Value(
                        Fable.NumberConstant(Fable.NumberValue.Int64 621355968000000000L, Fable.NumberInfo.Empty),
                        None
                    )
                    Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, Fable.NumberInfo.Empty), None)
                ]
        | getter, [ x ] when getter.StartsWith("get_", System.StringComparison.Ordinal) ->
            call (lowerFirst (getter.Substring 4)) [ x ]
        | ("IsLeapYear" | "DaysInMonth" | "SpecifyKind"), _ ->
            call
                (lowerFirst name)
                (args
                 |> List.map (fun a ->
                     if isKind a then
                         kindArg a
                     else
                         a
                 ))
        | ("Add" | "op_Addition"), [ a; b ] when isTimeSpan b -> call "add" [ a; b ]
        | ("Subtract" | "op_Subtraction"), [ a; b ] when isTimeSpan b -> call "subtract" [ a; b ]
        | ("Subtract" | "op_Subtraction"), [ a; b ] when isDate b -> call "subtractDate" [ a; b ]
        | ("AddTicks" | "AddDays" | "AddHours" | "AddMinutes" | "AddSeconds" | "AddMilliseconds" | "AddMicroseconds" | "AddMonths" | "AddYears"),
          [ a; v ] -> call (lowerFirst name) [ a; v ]
        | ("ToUniversalTime" | "ToLocalTime" | "ToShortDateString" | "ToLongDateString" | "ToShortTimeString" | "ToLongTimeString"),
          [ a ] -> call (lowerFirst name) [ a ]
        | ("Compare" | "CompareTo"), [ a; b ] -> call "compare" [ a; b ]
        | "Equals", [ a; b ] -> call "equals" [ a; b ]
        | ("op_Equality" | "op_Inequality" | "op_LessThan" | "op_LessThanOrEqual" | "op_GreaterThan" | "op_GreaterThanOrEqual"),
          [ a; b ] ->
            let op =
                match name with
                | "op_Equality" -> "=="
                | "op_Inequality" -> "!="
                | "op_LessThan" -> "<"
                | "op_LessThanOrEqual" -> "<="
                | "op_GreaterThan" -> ">"
                | _ -> ">="

            EPrim(op, [ call "compare" [ a; b ]; ELit("0", tI32) ], tBool)
        | "ToString", [ x ] -> call "toString" [ x ]
        | "ToString", x :: format :: _ when format.Type = Fable.String -> call "toStringFormat" [ x; format ]
        | "ToString", [ x; _ ] -> call "toString" [ x ]
        | "Parse", s :: _ -> call "parse" [ s ]
        | "TryParse", s :: rest when
            (match t with
             | Fable.Tuple _ -> true
             | _ -> false)
            && rest.Length <= 2
            ->
            call "tryParse" [ s ]
        | "TryParse", s :: rest when (outArgOf ctx rest).IsSome ->
            tryParseInto ctx r info "DateTime" s (outArgOf ctx rest).Value
        | _ -> fail r "the Zig target does not support DateTime.%s with these arguments yet" name
    // ---- `System.TimeSpan`: the library's TimeSpan.fs ----
    | "System.TimeSpan", name, args ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "TimeSpan"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let isFloat (x: Fable.Expr) =
            match x.Type with
            | Fable.Number((Float64 | Float32), _) -> true
            | _ -> false

        let int64T = Fable.Number(Int64, Fable.NumberInfo.Empty)

        let asInt64 (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(Int64, _) -> x
            | _ ->
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "ToInt64"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(args = [ x ], genArgs = [ x.Type ]),
                    int64T,
                    r
                )

        // (a part given as an option, an optional argument, or as itself)
        let asPart (x: Fable.Expr) =
            match x.Type with
            | Fable.Option(inner, _) ->
                let v = AST.makeTypedIdent inner "part"

                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "Map"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.OptionModule"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(
                        args = [ Fable.Delegate([ v ], asInt64 (Fable.IdentExpr v), None, []); x ],
                        genArgs = [ inner; int64T ]
                    ),
                    Fable.Option(int64T, false),
                    r
                )
            | _ -> Fable.Value(Fable.NewOption(Some(asInt64 x), int64T, false), r)

        let nonePart = Fable.Value(Fable.NewOption(None, int64T, false), r)

        let int64Const (v: int64) =
            Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int64 v, Fable.NumberInfo.Empty), None)

        let units =
            dict
                [
                    "FromDays", 864_000_000_000L
                    "FromHours", 36_000_000_000L
                    "FromMinutes", 600_000_000L
                    "FromSeconds", 10_000_000L
                    "FromMilliseconds", 10_000L
                    "FromMicroseconds", 10L
                ]

        match name, args with
        | ".ctor", [] -> call "zero" unitArg
        | ".ctor", [ ticks ] -> call "ofTicks" [ ticks ]
        | ".ctor", [ h; m; s ] -> call "create3" [ h; m; s ]
        | ".ctor", [ d; h; m; s ] -> call "create4" [ d; h; m; s ]
        | ".ctor", [ d; h; m; s; ms ] -> call "create5" [ d; h; m; s; ms ]
        | ".ctor", [ d; h; m; s; ms; us ] -> call "create6" [ d; h; m; s; ms; us ]
        | from, [ v ] when units.ContainsKey from && isFloat v ->
            call (from.Substring(0, 1).ToLowerInvariant() + from.Substring 1) [ v ]
        | from, [ v ] when units.ContainsKey from -> call "ofUnits" [ asInt64 v; int64Const units[from] ]
        | from, parts when units.ContainsKey from && parts.Length > 1 ->
            let skip =
                match from with
                | "FromDays" -> 0
                | "FromHours" -> 1
                | "FromMinutes" -> 2
                | "FromSeconds" -> 3
                | "FromMilliseconds" -> 4
                | _ -> 5

            let given = parts |> List.map asPart

            let all =
                List.replicate skip nonePart
                @ given
                @ List.replicate (6 - skip - given.Length) nonePart

            call "ofComponents" all
        | "FromTicks", [ v ] -> call "ofTicks" [ v ]
        | ("get_Zero" | "get_MinValue" | "get_MaxValue"), [] ->
            call
                (match name with
                 | "get_Zero" -> "zero"
                 | "get_MinValue" -> "minValue"
                 | _ -> "maxValue")
                unitArg
        | "get_TicksPerDay", [] -> lw ctx (int64Const 864_000_000_000L)
        | "get_TicksPerHour", [] -> lw ctx (int64Const 36_000_000_000L)
        | "get_TicksPerMinute", [] -> lw ctx (int64Const 600_000_000L)
        | "get_TicksPerSecond", [] -> lw ctx (int64Const 10_000_000L)
        | "get_TicksPerMillisecond", [] -> lw ctx (int64Const 10_000L)
        | getter, [ x ] when getter.StartsWith("get_", System.StringComparison.Ordinal) ->
            let n = getter.Substring 4
            call (n.Substring(0, 1).ToLowerInvariant() + n.Substring 1) [ x ]
        | ("Add" | "op_Addition"), [ a; b ] -> call "add" [ a; b ]
        | ("Subtract" | "op_Subtraction"), [ a; b ] -> call "subtract" [ a; b ]
        | ("Negate" | "op_UnaryNegation"), [ a ] -> call "negate" [ a ]
        | "op_UnaryPlus", [ a ] -> lw ctx a
        | "Duration", [ a ] -> call "duration" [ a ]
        | ("Multiply" | "op_Multiply"), [ a; b ] when isFloat b -> call "multiply" [ a; b ]
        | "op_Multiply", [ a; b ] when isFloat a -> call "multiply" [ b; a ]
        | ("Divide" | "op_Division"), [ a; b ] when isFloat b -> call "divide" [ a; b ]
        | ("Divide" | "op_Division"), [ a; b ] -> call "divideBy" [ a; b ]
        | ("Compare" | "CompareTo"), [ a; b ] -> call "compare" [ a; b ]
        | "Equals", [ a; b ] -> lw ctx (Fable.Operation(Fable.Binary(BinaryEqual, a, b), [], Fable.Boolean, r))
        | "ToString", [ x ] -> call "toString" [ x ]
        | "ToString", x :: format :: _ -> call "toStringFormat" [ x; format ]
        | "Parse", s :: _ -> call "parse" [ s ]
        | "TryParse", s :: rest when
            (match t with
             | Fable.Tuple _ -> true
             | _ -> false)
            && rest.Length <= 1
            ->
            call "tryParse" [ s ]
        | "TryParse", s :: rest when (outArgOf ctx rest).IsSome ->
            tryParseInto ctx r info "TimeSpan" s (outArgOf ctx rest).Value
        | _ -> fail r "the Zig target does not support TimeSpan.%s with these arguments yet" name
    // ---- `System.Guid`: the library's Guid.fs ----
    | "System.Guid", name, args when
        (match name with
         | ".ctor"
         | "NewGuid"
         | "CreateVersion7"
         | "get_Empty"
         | "Parse"
         | "TryParse"
         | "ToString"
         | "ToByteArray" -> true
         | _ -> false)
        ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "Guid"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                }
                xs
                t

        match name, args with
        | (".ctor" | "get_Empty"), [] -> call "create" unitArg
        | ".ctor", [ s ] when s.Type = Fable.String -> call "parse" [ s ]
        | ".ctor", [ bytes ] -> call "ofBytes" [ bytes ]
        | "NewGuid", [] -> call "newGuid" unitArg
        | "CreateVersion7", [] -> call "createVersion7" unitArg
        | "CreateVersion7", [ d ] -> call "createVersion7Of" [ d ]
        | "Parse", [ s ] -> call "parse" [ s ]
        | "TryParse", [ s ] -> call "tryParse" [ s ]
        // (`Guid.TryParse(s, &g)`: the Guid goes to `g`)
        | "TryParse", [ s; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]

            let pairIr =
                libraryCall
                    ctx
                    r
                    "Guid"
                    "tryParse"
                    { info with ThisArg = None }
                    [ s ]
                    (Fable.Tuple([ Fable.Boolean; out.Type ], false))

            let pair = ctx.State.NewVar("parsed", typeOf pairIr, VLocal, false)

            ELet(
                pair,
                pairIr,
                ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool))
            )
        | "ToString", [ g ] -> call "toString" [ g ]
        | "ToString", [ g; format ] -> call "toStringFormat" [ g; format ]
        | "ToByteArray", [ g ] -> call "toByteArray" [ g ]
        | _ -> fail r "the Zig target does not support Guid.%s with these arguments yet" name
    // ---- `System.Uri`: the library's Uri.fs ----
    | "System.Uri", ".ctor", args ->
        let fn =
            match args with
            | [ _ ] -> "create"
            | [ _; kind ] when
                kind.Type <> Fable.String
                && (
                    match kind.Type with
                    | Fable.DeclaredType(e, _) -> e.FullName <> "System.Uri"
                    | _ -> true
                )
                ->
                "createWithKind"
            | [ _; rel ] when rel.Type = Fable.String -> "createFromBase"
            | _ -> "createFromBaseUri"

        libraryCall ctx r "Uri" fn { info with ThisArg = None } args t
    // (`Uri.TryCreate(s, kind, &uri)`: the URI goes to `uri`)
    | "System.Uri", "TryCreate", [ a; b; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
        ctx.Vars.ContainsKey out.Name
        ->
        let outVar = ctx.Vars[out.Name]

        let fn =
            if a.Type = Fable.String then
                "tryCreate"
            else
                "tryCreateFromBase"

        let pairT = Fable.Tuple([ Fable.Boolean; out.Type ], false)
        let pairIr = libraryCall ctx r "Uri" fn info [ a; b ] pairT
        let pair = ctx.State.NewVar("created", typeOf pairIr, VLocal, false)

        ELet(pair, pairIr, ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool)))
    | "System.Uri", "TryCreate", [ a; b ] ->
        let fn =
            if a.Type = Fable.String then
                "tryCreate"
            else
                "tryCreateFromBase"

        libraryCall ctx r "Uri" fn info [ a; b ] t
    | "System.Uri", getter, [ u ] when
        getter.StartsWith("get_", System.StringComparison.Ordinal)
        || getter = "ToString"
        ->
        let fn =
            if getter = "ToString" then
                "toString"
            else
                let n = getter.Substring 4
                n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        libraryCall ctx r "Uri" fn { info with ThisArg = None } [ u ] t
    // ---- F#'s nullness operators (a value of a type without null here is never null) ----
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] -> pure' "fable_rt.isNullValue($0)" [ x ] tBool
    | "Microsoft.FSharp.Core.Operators", ("NonNull" | "NonNullQuickPattern"), [ x ] ->
        rt "fable_rt.nonNullValue($0)" [ x ] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators", "NullArgCheck", [ name; x ] ->
        rt "fable_rt.nullArgCheck($0, $1)" [ name; x ] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "NonNull", [ x ] -> lw ctx x
    // `match x with Null -> ... | NonNull y -> ...`: the choice of the two
    | "Microsoft.FSharp.Core.Operators", "NullMatchPattern", [ x ] ->
        match t with
        | Fable.DeclaredType(choice, genArgs) ->
            let v = AST.makeTypedIdent x.Type "nullable"

            let test =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "IsNull"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(args = [ Fable.IdentExpr v ], genArgs = [ x.Type ]),
                    Fable.Boolean,
                    r
                )

            let case tag value =
                Fable.Value(Fable.NewUnion([ value ], tag, choice, genArgs), r)

            lw
                ctx
                (Fable.Let(
                    v,
                    x,
                    Fable.IfThenElse(
                        test,
                        case 0 (Fable.Value(Fable.UnitConstant, None)),
                        case 1 (Fable.IdentExpr v),
                        r
                    )
                ))
        | _ -> fail r "internal: the null pattern of %A" t
    // the same of `Nullable<T>`, an option
    | "Microsoft.FSharp.Core.Operators", "WithNullV", [ x ] ->
        dotnetCall
            ctx
            r
            "System.Nullable`1"
            ".ctor"
            { info with
                ThisArg = None
                Args = [ x ]
            }
            t
    | "Microsoft.FSharp.Core.Operators", "NullV", [] ->
        dotnetCall
            ctx
            r
            "System.Nullable`1"
            ".ctor"
            { info with
                ThisArg = None
                Args = []
            }
            t
    | "Microsoft.FSharp.Core.Operators", "NonNullV", [ x ] ->
        dotnetCall
            ctx
            r
            "System.Nullable`1"
            "get_Value"
            { info with
                ThisArg = None
                Args = [ x ]
            }
            t
    | "Microsoft.FSharp.Core.Operators", "IsNullV", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ETest(xs.Head, "None", typeOf xs.Head))
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
    // `t.Item1` ... `t.Item7` of a tuple
    | e, item, [ x ] when
        (e.StartsWith("System.Tuple`", System.StringComparison.Ordinal)
         || e.StartsWith("System.ValueTuple`", System.StringComparison.Ordinal))
        && item.Length = 9
        && item.StartsWith("get_Item", System.StringComparison.Ordinal)
        && System.Char.IsDigit item[8]
        ->
        lw ctx (Fable.Get(x, Fable.TupleIndex(int item[8] - int '1'), t, r))
    // `OptimizedClosures.FSharpFunc<_, _, _>.Adapt f` and its `Invoke(a, b, ...)`: the function
    // itself, applied to the arguments
    | ("Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`3" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`4" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`5" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`6"),
      "Adapt",
      [ f ] -> lw ctx f
    | ("Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`3" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`4" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`5" | "Microsoft.FSharp.Core.OptimizedClosures.FSharpFunc`6"),
      "Invoke",
      f :: args -> lw ctx (Fable.CurriedApply(f, args, t, r))
    | _ -> Unchecked.defaultof<Expr>
