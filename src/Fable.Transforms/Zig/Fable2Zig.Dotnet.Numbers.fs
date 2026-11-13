/// .NET's members: decimal, bigint, checked arithmetic. The lowering (`Lower.dotnetCall`) asks here in the place these
/// cases had among its own.
module Fable.Transforms.Zig.DotnetNumbers

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
    // ---- decimal: a value of the runtime (`fable_rt.NetDecimal`) ----
    | ("Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions" | "System.Decimal"),
      ("MakeDecimal" | ".ctor"),
      [ lo; mid; hi; negative; scale ] ->
        match lo, mid, hi, negative, scale with
        | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 lo, _), _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 mid, _), _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 hi, _), _),
          Fable.Value(Fable.BoolConstant negative, _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.UInt8 scale, _), _) ->
            let m =
                (bigint (uint32 hi) <<< 64) + (bigint (uint32 mid) <<< 32) + bigint (uint32 lo)

            let m =
                if negative then
                    -m
                else
                    m

            decLit (string m) (int scale)
        | _ -> rt "fable_rt.decOfParts($0, $1, $2, $3, $4)" [ lo; mid; hi; negative; scale ] tDec
    | "System.Decimal", ".ctor", [ Uncast bits ] when
        (match bits.Type with
         | Fable.Array(Fable.Number(Int32, _), _) -> true
         | _ -> false)
        ->
        rt "fable_rt.decOfBits($0)" [ bits ] tDec
    | "System.Decimal", "GetBits", [ d ] -> pure' "fable_rt.decGetBits($0)" [ d ] (mapType ctx r t)
    | "System.Decimal", ("get_Zero" | "get_One" | "get_MinusOne" | "get_MaxValue" | "get_MinValue"), [] ->
        match name with
        | "get_Zero" -> decLit "0" 0
        | "get_One" -> decLit "1" 0
        | "get_MinusOne" -> decLit "-1" 0
        | "get_MaxValue" -> decLit "79228162514264337593543950335" 0
        | _ -> decLit "-79228162514264337593543950335" 0
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators" | "System.Convert"),
      "ToDecimal",
      [ x ] ->
        match x.Type with
        | Fable.String -> rt "fable_rt.decParse($0, true)" [ x ] tDec
        | _ when isDec x -> lw ctx x
        | _ -> rt $"fable_rt.decOf(%s{typedArg ctx r x 0})" [ x ] tDec
    | "System.Decimal", (".ctor" | "op_Implicit" | "op_Explicit"), [ x ] when not (isDec x) ->
        rt $"fable_rt.decOf(%s{typedArg ctx r x 0})" [ x ] tDec
    | "System.Decimal", "Parse", [ x ] -> rt "fable_rt.decParse($0, false)" [ x ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal"),
      ("op_Addition" | "op_Subtraction" | "op_Multiply" | "op_Division" | "op_Modulus" | "Add" | "Subtract" | "Multiply" | "Divide" | "Remainder"),
      [ a; b ] when isDec a ->
        let f =
            match name with
            | "op_Addition"
            | "Add" -> "decAdd"
            | "op_Subtraction"
            | "Subtract" -> "decSub"
            | "op_Multiply"
            | "Multiply" -> "decMul"
            | "op_Division"
            | "Divide" -> "decDiv"
            | _ -> "decRem"

        rt $"fable_rt.%s{f}($0, $1)" [ a; b ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal"),
      ("op_UnaryNegation" | "Negate"),
      [ a ] when isDec a -> pure' "fable_rt.decNeg($0)" [ a ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Decimal"), "op_UnaryPlus", [ a ] when isDec a -> lw ctx a
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Abs", [ a ] when isDec a ->
        pure' "fable_rt.decAbs($0)" [ a ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Sign", [ a ] when isDec a ->
        pure' "fable_rt.decSign($0)" [ a ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Round", [ a ] when isDec a ->
        pure' "fable_rt.decRound($0, 0, true)" [ a ] tDec
    | ("System.Math" | "System.Decimal"), "Round", [ a; digits ] when isDec a && isInt digits ->
        pure' "fable_rt.decRound($0, $1, true)" [ a; digits ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), ("Floor" | "Ceiling" | "Truncate"), [ a ] when
        isDec a
        ->
        let how =
            match name with
            | "Floor" -> "down"
            | "Ceiling" -> "up"
            | _ -> "toward_zero"

        pure' $"fable_rt.decWhole($0, .%s{how})" [ a ] tDec
    | "System.Decimal", "Compare", [ a; b ] -> pure' "fable_rt.decCompare($0, $1)" [ a; b ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal" | "System.Convert"),
      _,
      [ x ] when
        isDec x
        && (name.StartsWith("To", System.StringComparison.Ordinal) || name = "op_Explicit")
        && name <> "ToString"
        && name <> "ToDecimal"
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            pure' $"fable_rt.decToFloat(%s{zigTypeName ty}, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt $"fable_rt.decToInt(%s{zigTypeName ty}, $0)" [ x ] ty
        else
            fail r "the Zig target cannot convert a decimal to %A yet" t

    // ---- bigint: a counted cell of the runtime (`fable_rt.BigInt`) ----
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", ("FromZero" | "FromOne"), ([] | [ _ ]) ->
        pure'
            (if name = "FromZero" then
                 "fable_rt.bigOf(@as(i32, 0))"
             else
                 "fable_rt.bigOf(@as(i32, 1))")
            []
            tBig
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", ("FromInt32" | "FromInt64"), [ x ] ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", "FromString", [ x ] ->
        rt "fable_rt.bigParse($0)" [ x ] tBig
    | "System.Numerics.BigInteger", ".ctor", [ x ] when not (isBig x) ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig
    | "System.Numerics.BigInteger", "get_Zero", [] -> pure' "fable_rt.bigOf(@as(i32, 0))" [] tBig
    | "System.Numerics.BigInteger", "get_One", [] -> pure' "fable_rt.bigOf(@as(i32, 1))" [] tBig
    | "System.Numerics.BigInteger", "get_MinusOne", [] -> pure' "fable_rt.bigOf(@as(i32, -1))" [] tBig
    | "System.Numerics.BigInteger", "Parse", [ x ] -> rt "fable_rt.bigParse($0)" [ x ] tBig
    | "System.Numerics.BigInteger", "Pow", [ x; n ]
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked"), "PowInteger", [ x; n ] when
        isBig x
        ->
        rt "fable_rt.bigPow($0, $1)" [ x; n ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      ("op_Addition" | "op_Subtraction" | "op_Multiply" | "Add" | "Subtract" | "Multiply"),
      [ a; b ] when isBig a ->
        let f =
            match name with
            | "op_Addition"
            | "Add" -> "bigAdd"
            | "op_Subtraction"
            | "Subtract" -> "bigSub"
            | _ -> "bigMul"

        pure' $"fable_rt.%s{f}($0, $1)" [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"),
      ("op_Division" | "op_Modulus" | "Divide" | "Remainder"),
      [ a; b ] when isBig a ->
        let quotient =
            if name = "op_Division" || name = "Divide" then
                "true"
            else
                "false"

        rt ("fable_rt.bigDivRem($0, $1, " + quotient + ")") [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      ("op_UnaryNegation" | "Negate"),
      [ a ] when isBig a -> pure' "fable_rt.bigNeg($0)" [ a ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"), "op_UnaryPlus", [ a ] when isBig a -> lw ctx a
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger" | "System.Math"), "Abs", [ a ] when isBig a ->
        pure' "fable_rt.bigAbs($0)" [ a ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Sign", [ a ] when isBig a ->
        pure' "fable_rt.bigSign($0)" [ a ] tI32
    | "System.Numerics.BigInteger", "get_Sign", [ a ] -> pure' "fable_rt.bigSign($0)" [ a ] tI32
    | "System.Numerics.BigInteger", "get_IsZero", [ a ] -> pure' "(fable_rt.bigSign($0) == 0)" [ a ] tBool
    | "System.Numerics.BigInteger", "Compare", [ a; b ] -> pure' "fable_rt.bigCompare($0, $1)" [ a; b ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      _,
      [ x ] when
        isBig x
        && (name.StartsWith("To", System.StringComparison.Ordinal) || name = "op_Explicit")
        && name <> "ToString"
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            pure' $"fable_rt.bigToFloat(%s{zigTypeName ty}, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt $"fable_rt.bigToInt(%s{zigTypeName ty}, $0)" [ x ] ty
        elif ty = tBig then
            lw ctx x
        else
            fail r "the Zig target cannot convert a bigint to %A yet" t
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"), ("ToBigInt" | "op_Implicit"), [ x ] ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig

    // ---- `open Checked`: whole-number arithmetic and conversions that raise on overflow ----
    | "Microsoft.FSharp.Core.Operators.Checked", ("op_Addition" | "op_Subtraction" | "op_Multiply"), [ a; b ] ->
        let ty = mapType ctx r a.Type

        if intBits ty > 0 then
            let f =
                match name with
                | "op_Addition" -> "Add"
                | "op_Subtraction" -> "Sub"
                | _ -> "Mul"

            rt $"fable_rt.checked%s{f}(@as($R, $0), $1)" [ a; b ] ty
        else
            let op =
                match name with
                | "op_Addition" -> "add"
                | "op_Subtraction" -> "sub"
                | _ -> "mul"

            bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim(op, xs, ty))
    | "Microsoft.FSharp.Core.Operators.Checked", "op_UnaryNegation", [ a ] ->
        let ty = mapType ctx r a.Type

        if intBits ty > 0 then
            rt "fable_rt.checkedNeg(@as($R, $0))" [ a ] ty
        else
            bindArgs ctx [ lw ctx a ] (fun xs -> EPrim("neg", xs, ty))
    | "Microsoft.FSharp.Core.Operators.Checked", _, [ x ] when name.StartsWith("To", System.StringComparison.Ordinal) ->
        let ty = mapType ctx r t

        if x.Type = Fable.String then
            dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
        elif intBits ty > 0 then
            bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.checkedConv(%s{zigTypeName ty}, $0)", xs, ty))
        else
            dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t

    // `use x = resource` in `seq { }`: what follows, then `x.Dispose()`
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers", "EnumerateUsing", [ resource; body ] ->
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

        let unitArg = AST.makeTypedIdent Fable.Unit "unitVar"

        let thenFinally =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "EnumerateThenFinally"
                        Path =
                            Replacements.DotnetPrefix
                            + "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                { info with
                    Args =
                        [
                            Fable.CurriedApply(body, [ Fable.IdentExpr rid ], t, r)
                            Fable.Lambda(unitArg, dispose, None)
                        ]
                    GenericArgs =
                        (match t with
                         | Fable.DeclaredType(_, [ item ]) -> [ item ]
                         | _ -> [])
                    SignatureArgTypes = []
                    MemberRef = None
                },
                t,
                r
            )

        lw ctx (Fable.Let(rid, resource, thenFinally))
    | _ -> Unchecked.defaultof<Expr>
