/// .NET date, time, timezone, Timer, and Stopwatch member lowering.
module internal Fable.Transforms.Zig.DotnetTime

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
let private tryParseIntoWith
    (fn: string)
    (ctx: Ctx)
    r
    (info: Fable.CallInfo)
    (lib: string)
    (s: Fable.Expr)
    (out: Fable.Ident)
    =
    let outVar = ctx.Vars[out.Name]

    let pairIr =
        libraryCall
            ctx
            r
            lib
            fn
            { info with
                ThisArg = None
                GenericArgs = []
                SignatureArgTypes = []
            }
            [ s ]
            (Fable.Tuple([ Fable.Boolean; out.Type ], false))

    let pair = ctx.State.NewVar("parsed", typeOf pairIr, VLocal, false)

    ELet(pair, pairIr, ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool)))

let private tryParseInto = tryParseIntoWith "tryParse"


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
    // ---- `TimeZoneInfo.Local` and `TimeZoneInfo.Utc` ----
    | "System.TimeZoneInfo", "get_Local", _ -> ELit("true", tBool)
    | "System.TimeZoneInfo", "get_Utc", _ -> ELit("false", tBool)
    | "System.TimeZoneInfo", "GetUtcOffset", [ zone; d ] when
        (match d.Type with
         | Fable.DeclaredType(e, _) -> e.FullName = "System.DateTime"
         | _ -> false)
        ->
        libraryCall
            ctx
            r
            "DateTime"
            "zoneUtcOffset"
            { info with
                ThisArg = None
                SignatureArgTypes = []
                MemberRef = None
            }
            [ zone; d ]
            t
    // ---- `System.Timers.Timer`: the library's Timer.fs ----
    | "System.Timers.Timer", name, args ->
        let call fn xs =
            libraryCall
                ctx
                r
                "Timer"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let field (tm: Fable.Expr) (f: string) (ty: Ty) =
            bindArgs ctx [ lw ctx tm ] (fun xs -> EGet(xs.Head, PField f, ty))

        match name, args |> List.filter (fun a -> a.Type <> Fable.Unit) with
        | ".ctor", [] ->
            call
                "create"
                [
                    Fable.Value(Fable.NumberConstant(Fable.NumberValue.Float64 100.0, Fable.NumberInfo.Empty), None)
                ]
        | ".ctor", [ ms ] -> call "create" [ ms ]
        | "Start", [ tm ] -> call "start" [ tm ]
        | ("Stop" | "Close" | "Dispose"), [ tm ] -> call "stop" [ tm ]
        | "set_Enabled", [ tm; v ] -> call "setEnabled" [ tm; v ]
        | "set_Interval", [ tm; v ] -> call "setInterval" [ tm; v ]
        | "set_AutoReset", [ tm; v ] -> call "setAutoReset" [ tm; v ]
        | "get_Enabled", [ tm ] -> field tm "enabled" tBool
        | "get_Interval", [ tm ] -> field tm "interval" (TPrim "f64")
        | "get_AutoReset", [ tm ] -> field tm "autoReset" tBool
        | "add_Elapsed", _
        | "remove_Elapsed", _ ->
            fail r "the Zig target does not support Timer.%s yet; use timer.Elapsed.Add or Subscribe" name
        | ("get_Elapsed" | "Elapsed"), [ tm ] -> call "elapsed" [ tm ]
        | _ -> fail r "the Zig target does not support Timer.%s yet" name
    | "System.Timers.ElapsedEventArgs", "get_SignalTime", [ a ] ->
        bindArgs ctx [ lw ctx a ] (fun xs -> EGet(xs.Head, PField "signalTime", mapType ctx r t))
    // ---- `System.Diagnostics.Stopwatch`: the library's Stopwatch.fs ----
    | "System.Diagnostics.Stopwatch", name, args ->
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

        match name, args with
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
        // (the days wrapped, as F# gives the out argument: the second item)
        | ("Add" | "AddHours" | "AddMinutes"), (x :: v :: _) when
            not isDate
            && (
                match t with
                | Fable.Tuple _ -> true
                | _ -> false
            )
            ->
            call (timeName (lowerFirst name) + "Wrapped") [ x; v ]
        | ("Add" | "AddHours" | "AddMinutes"), [ x; v ] when not isDate -> call (timeName (lowerFirst name)) [ x; v ]
        | ("Add" | "AddHours" | "AddMinutes"), [ x; v; out ] when not isDate && (outArgOf ctx [ out ]).IsSome ->
            // (the days wrapped, an out argument: the second item of what the library gives)
            let outVar = ctx.Vars[(outArgOf ctx [ out ]).Value.Name]

            let pairIr =
                libraryCall
                    ctx
                    r
                    "DateOnly"
                    (timeName (lowerFirst name) + "Wrapped")
                    { info with
                        ThisArg = None
                        GenericArgs = []
                        SignatureArgTypes = []
                    }
                    [ x; v ]
                    (Fable.Tuple([ t; Fable.Number(Int32, Fable.NumberInfo.Empty) ], false))

            let pair = ctx.State.NewVar("added", typeOf pairIr, VLocal, false)

            ELet(
                pair,
                pairIr,
                ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, mapType ctx r t))
            )
        | ("Add" | "AddHours" | "AddMinutes"), [ x; v; _ ] when not isDate -> call (timeName (lowerFirst name)) [ x; v ]
        | "op_Subtraction", [ a; b ] when not isDate -> call "timeSubtract" [ a; b ]
        | "Parse", s :: _ -> call (fn "parse") [ s ]
        | "TryParse", s :: rest when
            (match t with
             | Fable.Tuple _ -> true
             | _ -> false)
            && rest.Length <= 2
            ->
            call (fn "tryParse") [ s ]
        | "TryParse", s :: rest when (outArgOf ctx rest).IsSome ->
            tryParseIntoWith (fn "tryParse") ctx r info "DateOnly" s (outArgOf ctx rest).Value
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
        | "ToString", x :: format :: _ when unwrapNullness format.Type = Fable.String ->
            call (fn "toStringFormat") [ x; format ]
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
        | "ToString", x :: format :: _ when unwrapNullness format.Type = Fable.String ->
            call "toStringFormat" [ x; format ]
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
        | "ToString", x :: format :: _ when unwrapNullness format.Type = Fable.String ->
            call "toStringFormat" [ x; format ]
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
    | _ -> Unchecked.defaultof<Expr>
