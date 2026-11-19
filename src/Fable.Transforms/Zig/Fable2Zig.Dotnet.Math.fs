/// `System.Math` / `System.MathF`, BigInteger bitwise ops, and numeric `Parse`/`TryParse`.
/// The lowering (`LowerDotnet.dotnetCall`) asks here in the place these cases had among its own.
module internal Fable.Transforms.Zig.DotnetMath

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
    let args =
        match info.ThisArg with
        | Some this -> this :: info.Args
        | None -> info.Args

    let rt = rt ctx
    let pure' = pure' ctx
    let zigTypeName = zigTypeName r
    let decLit = decLit ctx

    match entity, name, args with
    // ---- numbers ----
    | "System.MathF", _, _ -> dotnetCall ctx r "System.Math" name info t
    | ("System.Double" | "System.Single"),
      ("IsNaN" | "IsInfinity" | "IsPositiveInfinity" | "IsNegativeInfinity" | "IsFinite"),
      [ x ] ->
        let f =
            match name with
            | "IsNaN" -> "isNan"
            | "IsInfinity" -> "isInf"
            | "IsPositiveInfinity" -> "isPositiveInf"
            | "IsNegativeInfinity" -> "isNegativeInf"
            | _ -> "isFinite"

        pure' $"std.math.%s{f}($0)" [ x ] tBool
    // `Math.DivRem(a, b)`: `struct (a / b, a % b)`; with `&rem`, the remainder goes there
    | ("System.Math" | "System.Numerics.BigInteger"), "DivRem", a :: b :: rest ->
        let n = divRemTemps.Value.Value
        divRemTemps.Value.Value <- n + 1
        let ai = AST.makeTypedIdent a.Type $"divRemA%d{n}"
        let bi = AST.makeTypedIdent b.Type $"divRemB%d{n}"

        let op k =
            if isBig a then
                // (bigint's operators are calls)
                let selector =
                    if k = BinaryDivide then
                        "op_Division"
                    else
                        "op_Modulus"

                Fable.Call(
                    Fable.Import(
                        {
                            Selector = selector
                            Path = Replacements.DotnetPrefix + "System.Numerics.BigInteger"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create())
                        },
                        Fable.Any,
                        None
                    ),
                    { info with
                        Args = [ Fable.IdentExpr ai; Fable.IdentExpr bi ]
                        ThisArg = None
                    },
                    a.Type,
                    r
                )
            else
                Fable.Operation(Fable.Binary(k, Fable.IdentExpr ai, Fable.IdentExpr bi), [], a.Type, r)

        let body =
            match rest, t with
            | [ Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.IdentExpr _ as out)), _, _, _) ], _ ->
                Fable.Sequential [ Fable.Set(out, Fable.ValueSet, a.Type, op BinaryModulus, r); op BinaryDivide ]
            | [], Fable.Tuple(_, isStruct) ->
                Fable.Value(Fable.NewTuple([ op BinaryDivide; op BinaryModulus ], isStruct), r)
            // (the contents of a ref cell given for the remainder, as F# passes `&r.contents`)
            | [ Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, Fable.FieldGet fi, _, _)), _, _, _) ], _
            | [ Fable.Get(cell, Fable.FieldGet fi, _, _) ], _ ->
                Fable.Sequential
                    [
                        Fable.Set(cell, Fable.FieldSet fi.Name, a.Type, op BinaryModulus, r)
                        op BinaryDivide
                    ]
            // (a ref cell given for the remainder: its contents)
            | [ cell ], _ when
                (match unwrapNullness cell.Type with
                 | Fable.DeclaredType(e, _) -> e.FullName = "Microsoft.FSharp.Core.FSharpRef`1"
                 | _ -> false)
                ->
                Fable.Sequential
                    [
                        Fable.Set(cell, Fable.FieldSet "contents", a.Type, op BinaryModulus, r)
                        op BinaryDivide
                    ]
            | _ ->
                let text = (sprintf "%A" rest).Replace("\n", " ")

                fail r "the Zig target does not support this DivRem yet (%s)" (text.Substring(0, min 300 text.Length))

        lw ctx (Fable.Let(ai, a, Fable.Let(bi, b, body)))
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"),
      ("op_BitwiseAnd" | "op_BitwiseOr" | "op_ExclusiveOr" | "op_LeftShift" | "op_RightShift"),
      [ a; b ] when isBig a ->
        let f =
            match name with
            | "op_BitwiseAnd" -> "bigAnd"
            | "op_BitwiseOr" -> "bigOr"
            | "op_ExclusiveOr" -> "bigXor"
            | "op_LeftShift" -> "bigShl"
            | _ -> "bigShr"

        pure' $"fable_rt.%s{f}($0, $1)" [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Abs", [ x ] ->
        rt "fable_rt.absOf(@as($R, $0))" [ x ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Sign", [ x ] ->
        rt $"fable_rt.signOf(%s{typedArg ctx r x 0})" [ x ] tI32
    | "Microsoft.FSharp.Core.Operators", "PowInteger", [ x; n ] ->
        pure' "fable_rt.pown(@as($R, $0), $1)" [ x; n ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), ("op_Exponentiation" | "Pow"), [ x; y ] ->
        pure' "std.math.pow($R, $0, $1)" [ x; y ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Round", [ x ] ->
        pure' "fable_rt.roundEven(@as($R, $0))" [ x ] (mapType ctx r x.Type)
    | "System.Math", "Round", [ x; digits ] when isInt digits ->
        rt "fable_rt.roundTo(@as($R, $0), $1)" [ x; digits ] (mapType ctx r x.Type)
    | "System.Math", "Round", [ x; mode ] ->
        rt "fable_rt.roundModeOnly(@as($R, $0), @as(i32, @intCast($1)))" [ x; mode ] (mapType ctx r x.Type)
    | "System.Math", "Round", [ x; digits; mode ] ->
        rt "fable_rt.roundMode(@as($R, $0), $1, @as(i32, @intCast($2)))" [ x; digits; mode ] (mapType ctx r x.Type)
    | "System.Math", "Log", [ x; b ] -> pure' "fable_rt.logBase($0, $1)" [ x; b ] tF64
    | ("System.Math" | "System.Double" | "System.Single"), ("MaxMagnitude" | "MinMagnitude"), [ a; b ] ->
        let f =
            if name = "MaxMagnitude" then
                "maxMagnitude"
            else
                "minMagnitude"

        pure' $"fable_rt.%s{f}(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
    | "System.Math", "Clamp", [ x; lo; hi ] ->
        rt "fable_rt.clamp(@as($R, $0), $1, $2)" [ x; lo; hi ] (mapType ctx r x.Type)
    | "System.Math", ("Max" | "Min"), [ a; b ] ->
        let f =
            if name = "Max" then
                "mathMax"
            else
                "mathMin"

        pure' $"fable_rt.%s{f}(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
    | "System.Math", "get_PI", [] -> ELit("std.math.pi", tF64)
    | "System.Math", "get_E", [] -> ELit("std.math.e", tF64)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"),
      ("Sqrt" | "Sin" | "Cos" | "Tan" | "Exp" | "Log" | "Log10" | "Floor" | "Ceiling" | "Truncate" | "Asin" | "Acos" | "Atan" | "Sinh" | "Cosh" | "Tanh" | "Log2"),
      [ x ] ->
        let zig =
            match name with
            | "Sqrt" -> "@sqrt($0)"
            | "Sin" -> "@sin($0)"
            | "Cos" -> "@cos($0)"
            | "Tan" -> "@tan($0)"
            | "Exp" -> "@exp($0)"
            | "Log" -> "@log($0)"
            | "Log10" -> "@log10($0)"
            | "Log2" -> "@log2($0)"
            | "Floor" -> "@floor($0)"
            | "Ceiling" -> "@ceil($0)"
            | "Truncate" -> "@trunc($0)"
            | "Asin" -> "std.math.asin($0)"
            | "Acos" -> "std.math.acos($0)"
            | "Atan" -> "std.math.atan($0)"
            | "Sinh" -> "std.math.sinh($0)"
            | "Cosh" -> "std.math.cosh($0)"
            | _ -> "std.math.tanh($0)"

        pure' (zig.Replace("$0", "@as($R, $0)")) [ x ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), ("Atan2" | "Atan2"), [ y; x ] ->
        pure' "std.math.atan2(@as(f64, $0), @as(f64, $1))" [ y; x ] tF64
    // `char "a"` and `Char.Parse "a"`: a string of exactly one char
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), "ToChar", [ x ]
    | "System.Char", "Parse", [ x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strToChar($0)" [ x ] (TPrim "u16")
    // text to numbers: F#'s conversions read `0x`, `0o`, `0b` and `_`; .NET's `Parse` does not
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), _, [ x ] when
        name.StartsWith("To", System.StringComparison.Ordinal)
        && unwrapNullness x.Type = Fable.String
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            rt "fable_rt.parseFloatFs($R, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt "fable_rt.parseIntFs($R, $0)" [ x ] ty
        elif t = Fable.Boolean then
            rt "fable_rt.parseBool($0)" [ x ] ty
        else
            fail r "the Zig target does not support %s.%s of a string yet" entity name
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64"),
      "Parse",
      [ x ] -> rt "fable_rt.parseInt($R, $0)" [ x ] (mapType ctx r t)
    | ("System.Double" | "System.Single"), "Parse", [ x ] -> rt "fable_rt.parseFloat($R, $0)" [ x ] (mapType ctx r t)
    | ("System.Double" | "System.Single"), "Parse", [ x; style ] ->
        rt "fable_rt.parseFloatStyle($R, $0, @as(i32, @intCast($1)))" [ x; style ] (mapType ctx r t)
    | "System.Boolean", "Parse", [ x ] -> rt "fable_rt.parseBool($0)" [ x ] tBool
    // (`Int32.Parse(s, provider)`: the invariant culture's, as without one)
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single"),
      "Parse",
      [ x; provider ] when
        (match unwrapNullness provider.Type with
         | Fable.DeclaredType(e, _) ->
             e.FullName = "System.IFormatProvider"
             || e.FullName = "System.Globalization.CultureInfo"
         | _ -> false)
        ->
        dotnetCall ctx r entity name { info with Args = [ x ] } t
    // `TryParse(s, &v)`: what F# gives is `(ok, v)`, with `v` an out-variable of its own; or
    // `TryParse` given as a function, whose `v` is a ref cell (`f(s, r)`). On failure `v` is the
    // type's default, as on .NET.
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single" | "System.Decimal" | "System.Boolean" | "System.Numerics.BigInteger"),
      "TryParse",
      x :: (([ _ ] | [ _; _ ]) as rest) when
        (let out = List.last rest
         // (with a NumberStyles before the place: of a float only, see parseFloatStyle)
         (rest.Length = 1
          || entity = "System.Double"
          || entity = "System.Single"
          || entity = "System.Decimal")
         && match out with
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) -> ctx.Vars.ContainsKey o.Name
            // (`&r.contents` of a ref cell)
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, Fable.FieldGet info, _, _)), _, _, _) ->
                info.Name = "contents"
                && (
                    match cell.Type with
                    | Fable.DeclaredType(e, [ _ ]) -> e.FullName = refName
                    | _ -> false
                )
            | _ ->
                match out.Type with
                | Fable.DeclaredType(e, [ _ ]) -> e.FullName = refName
                | _ -> false)
        ->
        let out = List.last rest

        let style =
            if rest.Length = 2 then
                Some rest.Head
            else
                None

        let valueType =
            match out with
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) -> unByref o.Type
            | Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.Get _ as place)), _, _, _) -> place.Type
            | _ ->
                match out.Type with
                | Fable.DeclaredType(_, [ v ]) -> v
                | _ -> fail r "internal: TryParse"

        let ty = mapType ctx r valueType
        // (a name of its own: the program's variable may be called `parsed`)
        let tmp =
            AST.makeTypedIdent (Fable.Option(valueType, false)) (tempName ctx "parsed")

        let parsed =
            Fable.Emit(
                {
                    Macro =
                        match style with
                        | Some _ when entity = "System.Decimal" ->
                            "fable_rt.decTryParseStyle($0, @as(i32, @intCast($1)))"
                        | Some _ -> $"fable_rt.tryParseFloatStyle(%s{zigTypeName ty}, $0, @as(i32, @intCast($1)))"
                        | None -> $"fable_rt.tryParseAny(%s{zigTypeName ty}, $0)"
                    IsStatement = false
                    CallInfo = Fable.CallInfo.Create(args = x :: Option.toList style)
                },
                Fable.Option(valueType, false),
                r
            )

        let orDefault =
            Fable.Emit(
                {
                    Macro = $"fable_rt.orDefault(%s{zigTypeName ty}, $0)"
                    IsStatement = false
                    CallInfo = Fable.CallInfo.Create(args = [ Fable.IdentExpr tmp ])
                },
                valueType,
                r
            )

        let store =
            match out with
            | Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.IdentExpr _ as v)), _, _, _) ->
                Fable.Set(v, Fable.ValueSet, valueType, orDefault, r)
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, _, _, _)), _, _, _) ->
                Fable.Set(cell, Fable.FieldSet "contents", valueType, orDefault, r)
            | refCell -> Fable.Set(refCell, Fable.FieldSet "contents", valueType, orDefault, r)

        let isSome = Fable.Test(Fable.IdentExpr tmp, Fable.OptionTest true, r)

        lw ctx (Fable.Let(tmp, parsed, Fable.Sequential [ store; isSome ]))
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64"),
      "Parse",
      [ s; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32(512 | 515), _), _) ] ->
        rt "fable_rt.parseHex($R, $0)" [ s ] (mapType ctx r t)
    | _ -> Unchecked.defaultof<Expr>
