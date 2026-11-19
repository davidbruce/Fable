/// .NET's core members: enumerators, enums, Convert/BitConverter, Random, Interlocked/Thread,
/// nullness/Nullable, mutable collections, tuples. Delegates domain blocks to Dotnet{Time,Reflection,IoRegex}.
module Fable.Transforms.Zig.DotnetMisc

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
open Fable.Transforms.Zig.LowerDotnet
open Fable.Transforms.Zig.DotnetHelpers

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

    let (|SubDomain|_|)
        (f: Ctx -> SourceLocation option -> string -> string -> Fable.CallInfo -> Fable.Type -> Expr)
        (_: string * string * Fable.Expr list)
        =
        let res = f ctx r entity name info t

        if obj.ReferenceEquals(res, null) then
            None
        else
            Some res

    match entity, name, args with
    // `(s :> IEnumerable<'T>).GetEnumerator()` of a sequence: an enumerator over a walk of it
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers", "EnumerateFromFunctions", [ create; moveNext; current ] ->
        libraryCall
            ctx
            r
            "Seq"
            "enumerateFromFunctions"
            { info with
                ThisArg = None
                SignatureArgTypes = []
                MemberRef = None
            }
            [ create; moveNext; current ]
            t
    // (`System.Array`, an array of objects here: the enumerator of its items)
    | "System.Array", "GetEnumerator", [ a ] ->
        let objSeq =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ Fable.Any ]
            )

        let items =
            Fable.TypeCast(Fable.TypeCast(a, Fable.Array(Fable.Any, Fable.MutableArray)), objSeq)

        libraryCall
            ctx
            r
            "Seq"
            "getEnumerator"
            { info with
                ThisArg = None
                GenericArgs = [ Fable.Any ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ items ]
            t
    // (the non-generic IEnumerable is a sequence of objects here)
    | "System.Collections.IEnumerable", "GetEnumerator", _ ->
        dotnetCall ctx r "System.Collections.Generic.IEnumerable`1" name info t
    | "System.Collections.Generic.IEnumerable`1", "GetEnumerator", [ Uncast source ] when
        isSeqType source.Type
        || (forInSource ctx source).IsSome
        // (a value of a type parameter constrained to a sequence, `#seq<'T>`: the sequence of the
        // type Zig instantiates it with, see fable_rt.flexSeq)
        || (
            match unwrapNullness source.Type with
            | Fable.GenericParam _ -> true
            | _ -> false
        )
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
            (match unwrapNullness this.Type with
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
        && isFatIfaceTy (mapType ctx r this.Type)
        ->
        let ifaceStructTy =
            match mapType ctx r this.Type with
            | TOpt s -> s
            | s -> s

        match caseFields ifaceStructTy "" |> List.tryFind (fun (f, _) -> f = name) with
        | Some(f, fty) ->
            let ptys, ret =
                match fty with
                | TSlot(ptys, ret)
                | TFn(ptys, ret) -> ptys, ret
                | _ -> [], mapType ctx r t

            let rawArgs =
                match rest with
                | [ a ] when isUnit a.Type -> []
                | xs -> xs

            let args =
                if rawArgs.IsEmpty then
                    [ EUnit ]
                else
                    let lowered = rawArgs |> List.map (lw ctx)

                    if ptys.Length = lowered.Length then
                        List.map2 (coerceTy ctx) ptys lowered
                    else
                        lowered

            bindArgs
                ctx
                (lw ctx this :: args)
                (fun given ->
                    withBorrowedIface
                        ctx
                        this
                        given.Head
                        (fun iface -> coerceTy ctx (mapType ctx r t) (ECallIface(iface, f, given.Tail, ret)))
                )
        | None -> fail r "the Zig target cannot find the member %s of %s" name entity
    // (a value boxed and unboxed to its own type, as `use` does with an interface value)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxGeneric" | "UnboxFast"), [ Unboxed inner ] when
        unwrapNullness inner.Type <> Fable.Any
        && mapType ctx r inner.Type = mapType ctx r t
        ->
        lw ctx inner
    // `d.Invoke(a, b)` of a delegate: a call of the function value it is
    | _, "Invoke", f :: rest when
        (match f.Type with
         | Fable.DelegateType _ -> true
         // (a `Func<'T>` made of a function value, as Fable types it)
         | Fable.LambdaType _ -> true
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
    // (a `[<CLIEvent>]` member, as F# makes it: the library's Event.createEvent)
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers", "CreateEvent", [ add; remove; create ] ->
        libraryCall
            ctx
            r
            "Event"
            "createEvent"
            { info with
                MemberRef = None
                SignatureArgTypes = []
            }
            [ add; remove; create ]
            t
    // (`Event<'Delegate, 'Args>`: the library's DelegateEventOf)
    | "Microsoft.FSharp.Control.FSharpEvent`2", name, _ ->
        let args' =
            match t, info.GenericArgs, args with
            | _, [ _; a ], _ -> a
            | _, _, e :: _ ->
                match e.Type with
                | Fable.DeclaredType(_, [ _; a ]) -> a
                | _ -> Fable.Any
            | _ -> Fable.Any

        let call fn xs =
            libraryCall
                ctx
                r
                "Event"
                fn
                { info with
                    GenericArgs = [ args' ]
                    MemberRef = None
                    SignatureArgTypes = []
                }
                xs
                t

        match name, args |> List.filter (fun a -> a.Type <> Fable.Unit) with
        | ".ctor", _ -> call "createDelegate" []
        | "Trigger", [ e; sender; a ] -> call "triggerDelegate" [ e; sender; a ]
        | "get_Publish", [ e ] -> call "publishDelegate" [ e ]
        | _ ->
            fail
                r
                "the Zig target does not support Event<'Delegate, 'Args>.%s yet (this %A, args %A)"
                name
                (info.ThisArg |> Option.map (fun x -> x.Type))
                (args |> List.map (fun x -> x.Type))
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
        (let target =
            if name = "ToObj" then
                t
            else
                x.Type

         match unwrapNullness target with
         | Fable.String
         | Fable.Any -> true
         | _ -> mapType ctx r t = mapType ctx r x.Type)
        ->
        let target =
            if name = "ToObj" then
                t
            else
                x.Type

        match unwrapNullness target with
        | Fable.String
        | Fable.Any ->
            if name = "ToObj" then
                pure' "fable_rt.optToObj($0)" [ x ] (mapType ctx r t)
            else
                pure' "fable_rt.optOfObj($0)" [ x ] (mapType ctx r t)
        | _ -> lw ctx x
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
        unwrapNullness x.Type <> Fable.Any && mapType ctx r x.Type = mapType ctx r t
        ->
        lw ctx x
    | "Microsoft.FSharp.Core.Operators", "Unbox", [ Fable.TypeCast(x, nt) ] when
        unwrapNullness nt = Fable.Any
        && unwrapNullness x.Type <> Fable.Any
        && mapType ctx r x.Type = mapType ctx r t
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
    | SubDomain DotnetTime.call res -> res
    | SubDomain DotnetReflection.call res -> res
    | SubDomain DotnetIoRegex.call res -> res
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
    // (`unbox<'T> o` as an inline function leaves it: `:?>`)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "UnboxGeneric", [ x ] ->
        match t with
        // (an object seen as the non-generic IEnumerable: the items of its collection)
        | Fable.DeclaredType(e, []) when e.FullName = "System.Collections.IEnumerable" -> lw ctx (Fable.TypeCast(x, t))
        | _ ->
            if unwrapNullness x.Type = Fable.Any then
                unboxed ctx r x t
            else
                lw ctx (Fable.TypeCast(x, t))
    // (`x.CompareTo(y)` of an IComparable, an object here)
    | "System.IComparable", "CompareTo", [ x; y ] ->
        bindArgs ctx [ lw ctx x; lw ctx y ] (fun xs -> EEmit("fable_rt.compare($0, $1)", xs, tI32))
    // `lock o f`: .NET's Monitor (the runtime's lockRun, re-entrant); `obj ()`: an object to lock on
    | "Microsoft.FSharp.Core.Operators", "Lock", [ o; f ] -> rt "fable_rt.lockRun($0, $1)" [ o; f ] (mapType ctx r t)
    | "System.Object", ".ctor", [] -> pure' "fable_rt.objectNew()" [] tAny
    // ---- `Interlocked`: atomic operations on the place of an integer (a variable, a field) ----
    | "System.Threading.Interlocked", name, place :: rest when
        (match place.Type with
         | Fable.Number((Int32 | Int64 | UInt32 | UInt64), _) -> true
         | Fable.DeclaredType(e, [ Fable.Number((Int32 | Int64 | UInt32 | UInt64), _) ]) ->
             e.FullName = "Microsoft.FSharp.Core.byref`2"
             || e.FullName = "Microsoft.FSharp.Core.byref`3"
         | _ -> false)
        ->
        let macro =
            match name, rest.Length with
            | "Increment", 0 -> "(@atomicRmw($R, $0, .Add, 1, .seq_cst) +% 1)"
            | "Decrement", 0 -> "(@atomicRmw($R, $0, .Sub, 1, .seq_cst) -% 1)"
            | "Add", 1 -> "(@atomicRmw($R, $0, .Add, $1, .seq_cst) +% $1)"
            | "Exchange", 1 -> "@atomicRmw($R, $0, .Xchg, $1, .seq_cst)"
            | "CompareExchange", 2 -> "(@cmpxchgStrong($R, $0, $2, $1, .seq_cst, .seq_cst) orelse $2)"
            | "Read", 0 -> "@atomicLoad($R, $0, .seq_cst)"
            | _ -> fail r "the Zig target does not support Interlocked.%s yet" name

        match tryAddress (lw ctx place) with
        | Some p -> bindArgs ctx (p :: List.map (lw ctx) rest) (fun xs -> EEmit(macro, xs, mapType ctx r t))
        | None -> fail r "the Zig target cannot take the address of this place for Interlocked yet"
    // `Parallel.For(from, to, body)`: on threads (the runtime's parallelForRange); what it gives,
    // ParallelLoopResult, is nothing here
    | "System.Threading.Tasks.Parallel", "For", [ from; upto; body ] ->
        rt "fable_rt.parallelForRange($0, $1, $2)" [ from; upto; body ] tVoid
    // ---- threads (the runtime's ThreadOf: what the function captured is shared when it starts) ----
    | "System.Threading.Thread", ".ctor", [ start ] ->
        pure' "fable_rt.threadNew($0)" [ start ] (TPrim "fable_rt.ThreadOf")
    | "System.Threading.Thread", "Start", [ th ] -> rt "fable_rt.threadStart($0)" [ th ] tVoid
    | "System.Threading.Thread", "Join", [ th ] -> pure' "fable_rt.threadJoin($0)" [ th ] tVoid
    | "System.Threading.Thread", "get_IsAlive", [ th ] -> pure' "fable_rt.threadIsAlive($0)" [ th ] tBool
    | "System.Threading.Thread", "get_CurrentThread", [] -> ELit("{}", tVoid)
    | "System.Threading.Thread", "get_ManagedThreadId", _ -> pure' "fable_rt.threadId()" [] tI32
    | "System.Threading.Thread", "Sleep", [ arg ] ->
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

        if arg.Type = Fable.Number(Int32, Fable.NumberInfo.Empty) then
            sleep arg
        else
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
                    Fable.CallInfo.Create(thisArg = arg),
                    Fable.Number(Float64, Fable.NumberInfo.Empty),
                    r
                )

            sleep (Fable.TypeCast(ms, Fable.Number(Int32, Fable.NumberInfo.Empty)))
    // ---- F#'s nullness operators (a value of a type without null here is never null) ----
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] -> pure' "fable_rt.isNullValue($0)" [ x ] tBool
    | "Microsoft.FSharp.Core.Operators", ("NonNull" | "NonNullQuickPattern"), [ x ] ->
        let inTy = mapType ctx r x.Type
        let outTy = mapType ctx r t

        if inTy = TOpt outTy && inTy <> outTy then
            rt "fable_rt.nonNullUnwrap($0)" [ x ] outTy
        else
            rt "fable_rt.nonNullValue($0)" [ x ] outTy
    | "Microsoft.FSharp.Core.Operators", "NullArgCheck", [ name; x ] ->
        let inTy = mapType ctx r x.Type
        let outTy = mapType ctx r t

        if inTy = TOpt outTy && inTy <> outTy then
            rt "fable_rt.nullArgCheckUnwrap($0, $1)" [ name; x ] outTy
        else
            rt "fable_rt.nullArgCheck($0, $1)" [ name; x ] outTy
    | "Microsoft.FSharp.Core.Operators.Unchecked", "NonNull", [ x ] ->
        let inTy = mapType ctx r x.Type
        let outTy = mapType ctx r t

        if inTy = TOpt outTy && inTy <> outTy then
            rt "fable_rt.nonNullUnwrap($0)" [ x ] outTy
        else
            lw ctx x
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
    | "System.Nullable`1", "GetValueOrDefault", [ n ] when hasDefault ctx t ->
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
    // `ConditionalWeakTable<'K, 'V>`: the library's ConditionalWeakTable.fs
    | "System.Runtime.CompilerServices.ConditionalWeakTable`2", name, args ->
        let file = "ConditionalWeakTable"

        let genArgs =
            match args with
            | t0 :: _ ->
                match t0.Type with
                | Fable.DeclaredType(_, [ k; v ]) -> [ k; v ]
                | _ -> info.GenericArgs
            | [] ->
                match t with
                | Fable.DeclaredType(_, [ k; v ]) -> [ k; v ]
                | _ -> info.GenericArgs

        let call fn (xs: Fable.Expr list) ty =
            libraryCall
                ctx
                r
                file
                fn
                { info with
                    ThisArg = None
                    Args = xs
                    GenericArgs = genArgs
                    SignatureArgTypes = []
                    MemberRef = None
                }
                xs
                ty

        match name, args with
        | ".ctor", [] -> call "create" [] t
        | "Add", [ tbl; k; v ] -> call "add" [ tbl; k; v ] t
        | "AddOrUpdate", [ tbl; k; v ] -> call "addOrUpdate" [ tbl; k; v ] t
        | "Remove", [ tbl; k ] -> call "remove" [ tbl; k ] t
        | "Clear", [ tbl ] -> call "clear" [ tbl ] t
        // (the callback, a .NET delegate: the function it is)
        | "GetValue", [ tbl; k; f ] -> call "getValue" [ tbl; k; f ] t
        | "TryGetValue", [ tbl; k; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]
            let tmp = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)
            let found = call "tryFind" [ tbl; k ] (Fable.Option(out.Type, false))

            ELet(
                tmp,
                found,
                EIf(
                    EPrim("not", [ ETest(EVar tmp, "None", TOpt outVar.Ty) ], tBool),
                    ESeq(EAssign(outVar, EGet(EVar tmp, PSome, outVar.Ty)), ELit("true", tBool)),
                    ELit("false", tBool),
                    tBool
                )
            )
        | _ -> fail r "the Zig target does not support ConditionalWeakTable.%s yet" name
    // `ListCollector<'T>`: the library's ListCollector.fs
    | "Microsoft.FSharp.Core.CompilerServices.ListCollector`1", name, args ->
        match name with
        | ".ctor" -> libraryCall ctx r "ListCollector" "create" { info with Args = [] } [] t
        | "Add" -> libraryCall ctx r "ListCollector" "add" info args t
        | "AddMany"
        | "AddManyAndClose" ->
            // (what is added: a sequence, whatever collection it is)
            let args =
                match args with
                | [ c; xs ] ->
                    let item =
                        match c.Type with
                        | Fable.DeclaredType(_, [ item ]) -> item
                        | _ -> Fable.Any

                    let seqT =
                        Fable.DeclaredType(
                            {
                                FullName = "System.Collections.Generic.IEnumerable`1"
                                Path = Fable.CoreAssemblyName "System.Runtime"
                            },
                            [ item ]
                        )

                    [ c; Fable.TypeCast(xs, seqT) ]
                | _ -> args

            let fn =
                if name = "AddMany" then
                    "addMany"
                else
                    "addManyAndClose"

            libraryCall ctx r "ListCollector" fn info args t
        | "Close" -> libraryCall ctx r "ListCollector" "close" info args t
        | _ -> fail r "the Zig target does not support ListCollector.%s yet" name
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
