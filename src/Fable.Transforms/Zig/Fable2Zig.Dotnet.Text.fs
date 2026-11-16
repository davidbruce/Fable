/// .NET's members: StringBuilder, Split, Join, Format, chars and strings. The lowering (`Lower.dotnetCall`) asks here in the place these
/// cases had among its own.
module Fable.Transforms.Zig.DotnetText

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes
open Fable.Transforms.Zig.LowerHelpers
open Fable.Transforms.Zig.Lower
open Fable.Transforms.Zig.DotnetHelpers

/// (a StringComparison: an enum of that type)
let private isComparison (x: Fable.Expr) =
    match x.Type with
    | Fable.Number(Int32, Fable.NumberInfo.IsEnum e) -> e.FullName = "System.StringComparison"
    | _ -> false

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

    // `Console.Write`/`WriteLine`: the text as `String.Format` makes it (a lone value as `{0}`),
    // to standard output or error
    let console (toErr: bool) (newline: bool) (rest: Fable.Expr list) =
        let text =
            match rest with
            | [] -> lw ctx (Fable.Value(Fable.StringConstant "", r))
            | [ x ] when unwrapNullness x.Type = Fable.String -> lw ctx x
            | [ x ] -> compositeFormat ctx r "{0}" [ x ] Fable.String
            | (Fable.Value(Fable.StringConstant fmt, _)) :: values -> compositeFormat ctx r fmt values Fable.String
            | _ -> fail r "the Zig target cannot write a format known only when the program runs to the console yet"

        ctx.State.UsesRuntime <- true

        let err =
            if toErr then
                "true"
            else
                "false"

        let nl =
            if newline then
                "true"
            else
                "false"

        bindArgs ctx [ text ] (fun xs -> EEmit($"fable_rt.io.consoleWrite($0, %s{err}, %s{nl})", xs, tVoid))

    // (a runtime function that fails only when the string `s` is null: no failure where `s` is
    // known not to be null)
    let ofString (s: Fable.Expr) (template: string) (xs: Fable.Expr list) (ty: Ty) =
        if neverNullIn ctx s then
            pure' $"(%s{template} catch unreachable)" xs ty
        else
            rt template xs ty

    match entity, name, args with
    // ---- the console ----
    | "System.Console", ("Write" | "WriteLine"), _ -> console false (name = "WriteLine") args
    // (`Console.Error.WriteLine`, `Console.Out.Write`: the writer is the console's)
    | "System.IO.TextWriter",
      ("Write" | "WriteLine"),
      (Fable.Call(Fable.Import({
                                   Selector = ("get_Error" | "get_Out") as which
                                   Path = path
                               },
                               _,
                               _),
                  _,
                  _,
                  _)) :: rest when path.EndsWith("System.Console", System.StringComparison.Ordinal) ->
        console (which = "get_Error") (name = "WriteLine") rest
    // ---- StringBuilder ----
    // (a format of printf given as a value, `f $"x %d{x}"` with `f (fmt: StringFormat<_>)`)
    | ("Microsoft.FSharp.Core.PrintfFormat`4" | "Microsoft.FSharp.Core.PrintfFormat`5"), ".ctor", [ text ] ->
        pure' "fable_rt.printfFormatNew($0, {})" [ text ] (mapType ctx r t)
    | ("Microsoft.FSharp.Core.PrintfFormat`4" | "Microsoft.FSharp.Core.PrintfFormat`5"), ".ctor", text :: captures :: _ ->
        pure' "fable_rt.printfFormatNew($0, $1)" [ text; captures ] (mapType ctx r t)
    | ("Microsoft.FSharp.Core.PrintfFormat`4" | "Microsoft.FSharp.Core.PrintfFormat`5"), "get_Value", f :: _ ->
        pure' "fable_rt.printfFormatValue($0)" [ f ] tStr
    // (`sprintf fmt` of a format given as a value that takes no more values)
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", "PrintFormatToString", [ f ] when
        t = Fable.String
        && (
            match f.Type with
            | Fable.DeclaredType(e, _) ->
                e.FullName.StartsWith("Microsoft.FSharp.Core.PrintfFormat", System.StringComparison.Ordinal)
            | _ -> false
        )
        ->
        rt "fable_rt.printfFormatText($0)" [ f ] tStr
    // `s.Normalize()` and `s.IsNormalized()`: Unicode's forms (fable_normalize.zig); FormC unless
    // one is given
    | "System.String", "Normalize", [ s ] -> rt "fable_rt.strNormalize($0, 1)" [ s ] tStr
    | "System.String", "Normalize", [ s; form ] -> rt "fable_rt.strNormalize($0, @intCast($1))" [ s; form ] tStr
    | "System.String", "IsNormalized", [ s ] -> rt "fable_rt.strIsNormalized($0, 1)" [ s ] tBool
    | "System.String", "IsNormalized", [ s; form ] -> rt "fable_rt.strIsNormalized($0, @intCast($1))" [ s; form ] tBool
    | "System.Text.StringBuilder", ".ctor", [] -> pure' "fable_rt.sbNew(null)" [] (mapType ctx r t)
    // (a capacity, or a string and a capacity: the capacity is only a hint)
    | "System.Text.StringBuilder", ".ctor", [ n ] when isInt n ->
        bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.sbNew(null)" [] (mapType ctx r t))
    | "System.Text.StringBuilder", ".ctor", [ init; n ] when unwrapNullness init.Type = Fable.String && isInt n ->
        bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.sbNew($0)" [ init ] (mapType ctx r t))
    | "System.Text.StringBuilder", ".ctor", [ init ] when init.Type = Fable.String ->
        pure' "fable_rt.sbNew($0)" [ init ] (mapType ctx r t)
    | "System.Text.StringBuilder", ("Append" | "AppendLine"), sb :: rest when rest.Length <= 1 ->
        let f =
            if name = "Append" then
                "sbAppend"
            else
                "sbAppendLine"

        match rest with
        | [] -> pure' $"fable_rt.%s{f}($0, @as(fable_rt.String, null))" [ sb ] (mapType ctx r t)
        | [ x ] ->
            bindArgs
                ctx
                [ lw ctx sb; lw ctx x ]
                (fun xs -> EEmit($"fable_rt.%s{f}($0, %s{typedArg ctx r x 1})", xs, mapType ctx r t))
        | _ -> fail r "the Zig target does not support this StringBuilder.%s yet" name
    | "System.Text.StringBuilder", "get_Length", [ sb ] -> pure' "fable_rt.sbLength($0)" [ sb ] tI32
    | "System.Text.StringBuilder", "Clear", [ sb ] -> pure' "fable_rt.sbClear($0)" [ sb ] (mapType ctx r t)
    | ("System.Object" | "System.Text.StringBuilder" | "Microsoft.FSharp.Core.Operators"), "ToString", [ sb ] when
        (match sb.Type with
         | Fable.DeclaredType(ent, _) -> ent.FullName = "System.Text.StringBuilder"
         | _ -> false)
        ->
        pure' "fable_rt.sbToString($0)" [ sb ] tStr

    // ---- Split, Join, Format ----
    | "System.String", "Split", s0 :: rest ->
        // (separators, then a count of parts (a number), then options (an enum))
        let isEnum (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(_, Fable.NumberInfo.IsEnum _) -> true
            | _ -> false

        let sepArg, more =
            match rest with
            | [] -> None, []
            | x :: more -> Some x, more

        let count =
            match more with
            | c :: _ when not (isEnum c) -> lw ctx c
            | _ -> ELit("2147483647", tI32)

        let opts =
            match more |> List.tryFind isEnum with
            | Some o -> lw ctx o
            | None -> ELit("0", tI32)

        let call macro (xs: Fable.Expr list) =
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                (s0 :: xs |> List.map (lw ctx) |> fun l -> l @ [ count; opts ])
                (fun irs -> ERt(macro, irs, mapType ctx r t))

        match sepArg |> Option.map (fun a -> a, a.Type) with
        | None -> call "fable_rt.strSplitChars($0, &.{}, $1, @intCast($2))" []
        | Some(c, Fable.Char) -> call "fable_rt.strSplitChars($0, &.{ $1 }, $2, @intCast($3))" [ c ]
        | Some(a, Fable.Array(Fable.Char, _)) -> call "fable_rt.strSplitChars($0, $1.items, $2, @intCast($3))" [ a ]
        | Some(sep, Fable.String) -> call "fable_rt.strSplitString($0, $1, $2, @intCast($3))" [ sep ]
        | Some(a, Fable.Array(Fable.String, _)) -> call "fable_rt.strSplitStrings($0, $1.items, $2, @intCast($3))" [ a ]
        | _ -> fail r "the Zig target does not support this String.Split yet"
    | "System.String", "Join", [ sep; items ]
    | "Microsoft.FSharp.Core.StringModule", "Concat", [ sep; items ] when sep.Type = Fable.String ->
        let (Uncast inner) = items

        let listIr =
            match inner.Type with
            | Fable.Array(item, Fable.ResizeArray) ->
                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs -> EEmit("fable_rt.raToList($0)", xs, TEnt(listEnt ctx.State, [ mapType ctx r item ])))
            | Fable.Array(item, _) ->
                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs -> EEmit("fable_rt.arrayToList($0)", xs, TEnt(listEnt ctx.State, [ mapType ctx r item ])))
            | t when isSeqType t ->
                let itemTy = itemOf (lw ctx inner)

                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs ->
                        ECall(libraryTarget ctx "Seq" "toList", [ itemTy ], xs, TEnt(listEnt ctx.State, [ itemTy ]))
                    )
            | _ ->
                match forInSource ctx inner with
                | Some(listExpr, "list") -> listExpr
                | _ -> fail r "the Zig target cannot join a value of this type yet (%A)" inner.Type

        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx sep; listIr ] (fun xs -> EEmit("fable_rt.joinList($0, $1)", xs, tStr))
    // (a pattern known only when the program runs: its arguments as objects)
    | "System.String", "Format", pattern :: values when
        (match pattern with
         | Fable.Value(Fable.StringConstant _, _) -> false
         | _ -> unwrapNullness pattern.Type = Fable.String)
        ->
        let objs =
            match values with
            | [ arr ] when unwrapNullness arr.Type = Fable.Array(Fable.Any, Fable.MutableArray) -> arr
            | _ ->
                Fable.Value(
                    Fable.NewArray(
                        Fable.ArrayValues(
                            values
                            |> List.map (fun v ->
                                if unwrapNullness v.Type = Fable.Any then
                                    v
                                else
                                    Fable.TypeCast(v, Fable.Any)
                            )
                        ),
                        Fable.Any,
                        Fable.MutableArray
                    ),
                    r
                )

        rt "fable_rt.strFormatObjs($0, $1)" [ pattern; objs ] tStr
    // (the values as an array known only when the program runs: `String.Format(fmt, args)`)
    | "System.String", "Format", ((Fable.Value(Fable.StringConstant _, _)) as pattern) :: [ Uncast arr ] when
        (match arr with
         | Fable.Value(Fable.NewArray(Fable.ArrayValues _, _, _), _) -> false
         | _ ->
             match arr.Type with
             | Fable.Array(Fable.Any, _) -> true
             | _ -> false)
        ->
        rt "fable_rt.strFormatObjs($0, $1)" [ pattern; arr ] tStr
    | "System.String", "Format", (Fable.Value(Fable.StringConstant fmt, _)) :: values ->
        compositeFormat ctx r fmt values t
    // (a culture changes nothing here: formatting is the invariant culture's)
    | "System.String", "Format", culture :: (Fable.Value(Fable.StringConstant fmt, _)) :: values when isCulture culture ->
        compositeFormat ctx r fmt values t
    | "System.Text.StringBuilder", "AppendFormat", sb :: rest ->
        let rest =
            match rest with
            | culture :: more when isCulture culture -> more
            | _ -> rest

        match rest with
        | (Fable.Value(Fable.StringConstant fmt, _)) :: values ->
            bindArgs
                ctx
                [ lw ctx sb; compositeFormat ctx r fmt values Fable.String ]
                (fun xs -> EEmit("fable_rt.sbAppend($0, $1)", xs, mapType ctx r t))
        | _ -> fail r "the Zig target needs the format of AppendFormat to be a literal"
    | _, "ToString", [ x; culture ] when isCulture culture ->
        dotnetCall
            ctx
            r
            "Microsoft.FSharp.Core.Operators"
            "ToString"
            { info with
                Args = [ x ]
                ThisArg = None
            }
            t
    | "System.String", "LastIndexOf", [ s; x; start ] when x.Type = Fable.Char && isInt start ->
        rt "fable_rt.strLastIndexOfCharFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x; start ] when x.Type = Fable.String && isInt start ->
        rt "fable_rt.strLastIndexOfFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when
        x.Type = Fable.String
        ->
        rt "fable_rt.strLastIndexOf($0, $1)" [ s; x ] tI32
    | "System.String",
      "LastIndexOf",
      [ s; x; start; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when x.Type = Fable.String ->
        rt "fable_rt.strLastIndexOfFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "IndexOf", [ s; x; start; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when
        x.Type = Fable.String
        ->
        rt "fable_rt.strIndexOf($0, $1, $2)" [ s; x; start ] tI32
    // (with a StringComparison other than Ordinal: see fable_rt.strIndexOfCmp)
    | "System.String", "IndexOf", [ s; x; start; cmp ] when unwrapNullness x.Type = Fable.String && isComparison cmp ->
        rt "fable_rt.strIndexOfCmp($0, $1, $2, @as(i32, @intCast($3)))" [ s; x; start; cmp ] tI32
    | "System.String", "LastIndexOf", [ s; x; cmp ] when unwrapNullness x.Type = Fable.String && isComparison cmp ->
        rt "fable_rt.strLastIndexOfCmp($0, $1, null, @as(i32, @intCast($2)))" [ s; x; cmp ] tI32
    | "System.String", "LastIndexOf", [ s; x; start; cmp ] when unwrapNullness x.Type = Fable.String && isComparison cmp ->
        rt "fable_rt.strLastIndexOfCmp($0, $1, $2, @as(i32, @intCast($3)))" [ s; x; start; cmp ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars ] ->
        rt "fable_rt.strIndexOfAny($0, $1, 0, null)" [ s; chars ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars; start ] ->
        rt "fable_rt.strIndexOfAny($0, $1, $2, null)" [ s; chars; start ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars; start; count ] ->
        rt "fable_rt.strIndexOfAny($0, $1, $2, $3)" [ s; chars; start; count ] tI32
    | "System.String", ("Trim" | "TrimStart" | "TrimEnd"), [ s; Uncast chars ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        let ends =
            match name with
            | "Trim" -> "true, true"
            | "TrimStart" -> "true, false"
            | _ -> "false, true"

        rt $"fable_rt.strTrimAny($0, %s{ends}, $1)" [ s; chars ] tStr
    | "System.String", ("Trim" | "TrimStart" | "TrimEnd"), s :: chars when
        chars.Length > 1 && chars |> List.forall (fun c -> c.Type = Fable.Char)
        ->
        let arr =
            Fable.Value(Fable.NewArray(Fable.ArrayValues chars, Fable.Char, Fable.MutableArray), r)

        dotnetCall
            ctx
            r
            entity
            name
            { info with
                Args = [ arr ]
                ThisArg = Some s
            }
            t
    | "System.String", "ToCharArray", [ s; start; n ] ->
        rt "fable_rt.strToCharsRange($0, $1, $2)" [ s; start; n ] (mapType ctx r t)
    | "System.String", ".ctor", [ Uncast chars; start; n ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        rt "fable_rt.strOfCharsRange($0, $1, $2)" [ chars; start; n ] tStr
    | "System.String", "Join", [ sep; Uncast values; start; n ] when
        (match values.Type with
         | Fable.Array(Fable.String, _) -> true
         | _ -> false)
        ->
        rt "fable_rt.strJoinRange($0, $1, $2, $3)" [ sep; values; start; n ] tStr
    | "System.String", "Compare", [ a; ia; b; ib; n ] ->
        rt "fable_rt.strCompareCultureRange($0, $1, $2, $3, $4, false)" [ a; ia; b; ib; n ] tI32
    | "System.String", "Compare", [ a; ia; b; ib; n; ignoreCase ] when ignoreCase.Type = Fable.Boolean ->
        rt "fable_rt.strCompareCultureRange($0, $1, $2, $3, $4, $5)" [ a; ia; b; ib; n; ignoreCase ] tI32
    | "System.String", "Compare", [ a; ia; b; ib; n; ignoreCase; culture ] when
        ignoreCase.Type = Fable.Boolean && isCulture culture
        ->
        rt "fable_rt.strCompareCultureRange($0, $1, $2, $3, $4, $5)" [ a; ia; b; ib; n; ignoreCase ] tI32
    | "System.String", "Compare", [ a; ia; b; ib; n; culture ] when isCulture culture ->
        rt "fable_rt.strCompareCultureRange($0, $1, $2, $3, $4, false)" [ a; ia; b; ib; n ] tI32
    | "System.String",
      "Compare",
      [ a; ia; b; ib; n; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 kind, _), _) ] when
        kind >= 0 && kind <= 5
        ->
        match kind with
        | 4 -> rt "fable_rt.strCompareRange($0, $1, $2, $3, $4, false)" [ a; ia; b; ib; n ] tI32
        | 5 -> rt "fable_rt.strCompareRange($0, $1, $2, $3, $4, true)" [ a; ia; b; ib; n ] tI32
        | _ ->
            let ig =
                if kind = 1 || kind = 3 then
                    "true"
                else
                    "false"

            rt $"fable_rt.strCompareCultureRange($0, $1, $2, $3, $4, %s{ig})" [ a; ia; b; ib; n ] tI32
    | "System.String", "Compare", [ a; ia; b; ib; n; cmp ] when
        (match cmp.Type with
         | Fable.Number(_, Fable.NumberInfo.IsEnum ent) -> ent.FullName = "System.StringComparison"
         | _ -> false)
        ->
        rt "fable_rt.strCompareRangeWith($0, $1, $2, $3, $4, $5)" [ a; ia; b; ib; n; cmp ] tI32
    // (`String.Concat` of a sequence, a list or an array of strings: their join)
    | "System.String", "Concat", [ Uncast values ] when values.Type <> Fable.String ->
        dotnetCall
            ctx
            r
            "System.String"
            "Join"
            { info with
                Args = [ Fable.Value(Fable.StringConstant "", None); values ]
                ThisArg = None
            }
            t
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetStringSlice", [ s; lo; hi ] ->
        rt "fable_rt.strSliceRange($0, $1, $2)" [ s; lo; hi ] tStr
    | "System.Environment", "get_NewLine", [] -> pure' "fable_rt.newLine()" [] tStr
    | "System.Uri", "EscapeDataString", [ s ] -> rt "fable_rt.uriEscape($0, false)" [ s ] tStr
    | "System.Uri", "EscapeUriString", [ s ] -> rt "fable_rt.uriEscape($0, true)" [ s ] tStr
    | "System.Uri", "UnescapeDataString", [ s ] -> rt "fable_rt.uriUnescape($0)" [ s ] tStr
    | "System.Text.StringBuilder", ("get_Chars" | "get_Item"), [ sb; i ] ->
        rt "fable_rt.sbCharAt($0, $1)" [ sb; i ] (TPrim "u16")
    | "System.Text.StringBuilder", ("set_Chars" | "set_Item"), [ sb; i; c ] ->
        rt "fable_rt.sbSetChar($0, $1, $2)" [ sb; i; c ] tVoid
    | "System.Text.StringBuilder", "ToString", [ sb; start; n ] ->
        rt "fable_rt.sbToStringRange($0, $1, $2)" [ sb; start; n ] tStr
    | "System.Text.StringBuilder", "Remove", [ sb; start; n ] ->
        rt "fable_rt.sbRemove($0, $1, $2)" [ sb; start; n ] (mapType ctx r t)
    | "System.Text.StringBuilder", "set_Length", [ sb; n ] -> rt "fable_rt.sbSetLength($0, $1)" [ sb; n ] tVoid
    | "System.Text.StringBuilder", "Replace", [ sb; a; b ] when a.Type = Fable.Char ->
        pure' "fable_rt.sbReplaceChar($0, $1, $2)" [ sb; a; b ] (mapType ctx r t)
    | "System.Text.StringBuilder", "Append", [ sb; c; n ] when c.Type = Fable.Char && isInt n ->
        rt "fable_rt.sbAppendRepeat($0, $1, $2)" [ sb; c; n ] (mapType ctx r t)
    | "System.Text.StringBuilder", "Replace", [ sb; a; b ] when a.Type = Fable.String ->
        rt "fable_rt.sbReplace($0, $1, $2)" [ sb; a; b ] (mapType ctx r t)
    | "System.String", "ToCharArray", [ s0 ] -> rt "fable_rt.strToChars($0)" [ s0 ] (mapType ctx r t)
    | "System.String", ".ctor", [ chars ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        pure' "fable_rt.strOfChars($0)" [ chars ] tStr
    | "System.Char",
      ("IsDigit" | "IsLetter" | "IsLetterOrDigit" | "IsUpper" | "IsLower" | "IsNumber" | "IsPunctuation" | "IsSymbol" | "IsSeparator" | "IsControl" | "IsSurrogate"),
      [ c ] -> pure' $"fable_rt.unicode.is%s{name.Substring 2}($0)" [ c ] tBool
    | "System.Char", "GetNumericValue", [ c ] -> pure' "fable_rt.charNumericValue($0)" [ c ] tF64
    | "System.Char",
      ("IsDigit" | "IsLetter" | "IsLetterOrDigit" | "IsUpper" | "IsLower" | "IsNumber" | "IsPunctuation" | "IsSymbol" | "IsSeparator" | "IsControl" | "IsSurrogate" | "IsWhiteSpace"),
      [ s; i ] when s.Type = Fable.String ->
        rt $"fable_rt.strCharIs($0, $1, fable_rt.unicode.is%s{name.Substring 2})" [ s; i ] tBool
    | "System.Char", "GetUnicodeCategory", [ c ] -> pure' "fable_rt.charCategory($0)" [ c ] tI32
    | "System.Char", "GetUnicodeCategory", [ s; i ] -> rt "fable_rt.strCharCategory($0, $1)" [ s; i ] tI32
    | "System.Char", "ToString", [ c ] when c.Type = Fable.Char ->
        dotnetCall
            ctx
            r
            "Microsoft.FSharp.Core.Operators"
            "ToString"
            { info with
                Args = [ c ]
                ThisArg = None
            }
            t
    | "System.String", "CompareTo", [ a; b ] -> rt "fable_rt.strCompareTo($0, $1)" [ a; b ] tI32
    | "System.String", "Compare", [ a; b ] -> pure' "fable_rt.strCompareCulture($0, $1, false)" [ a; b ] tI32
    | "System.String", "Compare", [ a; b; ignoreCase ] when ignoreCase.Type = Fable.Boolean ->
        pure' "fable_rt.strCompareCulture($0, $1, $2)" [ a; b; ignoreCase ] tI32
    | "System.String", "Compare", [ a; b; culture ] when isCulture culture ->
        pure' "fable_rt.strCompareCulture($0, $1, false)" [ a; b ] tI32
    | "System.String", "Compare", [ a; b; ignoreCase; culture ] when
        ignoreCase.Type = Fable.Boolean && isCulture culture
        ->
        pure' "fable_rt.strCompareCulture($0, $1, $2)" [ a; b; ignoreCase ] tI32
    | "System.String", "StartsWith", [ s; x; ignoreCase; culture ] when
        ignoreCase.Type = Fable.Boolean && isCulture culture
        ->
        rt "fable_rt.strStartsWithOpt($0, $1, $2)" [ s; x; ignoreCase ] tBool
    | "System.String", "EndsWith", [ s; x; ignoreCase; culture ] when
        ignoreCase.Type = Fable.Boolean && isCulture culture
        ->
        rt "fable_rt.strEndsWithOpt($0, $1, $2)" [ s; x; ignoreCase ] tBool
    // comparisons that say how: ordinal or culture-based (current culture is treated as
    // invariant culture here)
    | "System.String", ("Equals" | "StartsWith" | "EndsWith" | "IndexOf" | "Compare" | "Contains"), _ when
        (match List.tryLast args with
         | Some last ->
             match last.Type with
             | Fable.Number(_, Fable.NumberInfo.IsEnum ent) -> ent.FullName = "System.StringComparison"
             | _ -> false
         | None -> false)
        ->
        let how =
            match List.last args with
            | Fable.Value(Fable.NumberConstant(v, _), _) ->
                match v with
                | Fable.NumberValue.Int32 n -> n
                | _ -> -1
            | _ -> -1

        let a, b =
            match args with
            | [ a; b; _ ] -> a, b
            | _ -> fail r "the Zig target does not support this String.%s yet" name

        match name, how with
        | "Compare", 4 -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
        | "Compare", 5 -> pure' "fable_rt.strCompareIgnoreCase($0, $1)" [ a; b ] tI32
        | "Compare", (0 | 2) -> pure' "fable_rt.strCompareCulture($0, $1, false)" [ a; b ] tI32
        | "Compare", (1 | 3) -> pure' "fable_rt.strCompareCulture($0, $1, true)" [ a; b ] tI32
        | "Compare", -1 -> rt "fable_rt.strCompareWith($0, $1, $2)" args tI32
        | _, (0 | 2 | 4) ->
            match name with
            | "Equals" -> pure' "fable_rt.strEql($0, $1)" [ a; b ] tBool
            | "StartsWith" -> rt "fable_rt.strStartsWith($0, $1)" [ a; b ] tBool
            | "EndsWith" -> rt "fable_rt.strEndsWith($0, $1)" [ a; b ] tBool
            | "IndexOf" when b.Type = Fable.Char -> rt "fable_rt.strIndexOfChar($0, $1, 0)" [ a; b ] tI32
            | "IndexOf" -> rt "fable_rt.strIndexOf($0, $1, 0)" [ a; b ] tI32
            | "Contains" when b.Type = Fable.Char -> rt "fable_rt.strContainsChar($0, $1)" [ a; b ] tBool
            | "Contains" -> rt "fable_rt.strContains($0, $1)" [ a; b ] tBool
            | _ -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
        | _, (1 | 3 | 5) ->
            match name with
            | "Equals" -> pure' "fable_rt.strEqualsIgnoreCase($0, $1)" [ a; b ] tBool
            | "StartsWith" -> rt "fable_rt.strStartsWithIgnoreCase($0, $1)" [ a; b ] tBool
            | "EndsWith" -> rt "fable_rt.strEndsWithIgnoreCase($0, $1)" [ a; b ] tBool
            | "IndexOf" when b.Type = Fable.Char -> rt "fable_rt.strIndexOfCharIgnoreCase($0, $1)" [ a; b ] tI32
            | "IndexOf" -> rt "fable_rt.strIndexOfIgnoreCase($0, $1)" [ a; b ] tI32
            | "Contains" ->
                let call =
                    if b.Type = Fable.Char then
                        rt "fable_rt.strIndexOfCharIgnoreCase($0, $1)" [ a; b ] tI32
                    else
                        rt "fable_rt.strIndexOfIgnoreCase($0, $1)" [ a; b ] tI32

                bindArgs ctx [ call ] (fun xs -> EPrim("ge", [ xs.Head; ELit("0", tI32) ], tBool))
            | _ -> pure' "fable_rt.strCompareIgnoreCase($0, $1)" [ a; b ] tI32
        | _ -> fail r "the Zig target does not support String.%s with StringComparison %d" name how

    // ---- chars: each code unit to what .NET maps it to (there is no current culture) ----
    | "System.Char", ("ToUpper" | "ToUpperInvariant"), [ c ] -> pure' "fable_rt.unicode.toUpper($0)" [ c ] tChar
    | "System.Char", ("ToLower" | "ToLowerInvariant"), [ c ] -> pure' "fable_rt.unicode.toLower($0)" [ c ] tChar
    | "System.Char", "IsWhiteSpace", [ c ] -> pure' "fable_rt.unicode.isWhiteSpace($0)" [ c ] tBool
    // ---- strings ----
    // (what a null string or an argument out of range raises on .NET, it raises here: those
    // calls are `ERt`. The `String` module takes a null string for an empty one.)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "DefaultOf", [] when unwrapNullness t = Fable.String ->
        ELit("@as(fable_rt.String, null)", tStr)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "DefaultOf", [] ->
        match t with
        | Fable.Number(BigInt, _) -> pure' "fable_rt.bigOf(@as(i32, 0))" [] (mapType ctx r t)
        | Fable.Number(Decimal, _) -> ELit("fable_rt.NetDecimal{}", mapType ctx r t)
        | Fable.Number _
        | Fable.Char -> ELit("0", mapType ctx r t)
        | Fable.Boolean -> ELit("false", tBool)
        | Fable.Unit -> EUnit
        // (a struct tuple: each item's default)
        | Fable.Tuple(items, true) when items |> List.forall (hasDefault ctx) ->
            let defaults =
                items
                |> List.map (fun it ->
                    Fable.Call(
                        Fable.Import(
                            {
                                Selector = "DefaultOf"
                                Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators.Unchecked"
                                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                            },
                            Fable.Any,
                            None
                        ),
                        Fable.CallInfo.Create(genArgs = [ it ]),
                        it,
                        r
                    )
                )

            lw ctx (Fable.Value(Fable.NewTuple(defaults, true), r))
        | Fable.Any -> ELit("@as(fable_rt.Any, null)", tAny)
        | Fable.Option _ -> ECon(mapType ctx r t, "None", [], None)
        | Fable.Nullable(inner, false) ->
            match mapType ctx r t with
            | TOpt _ as optTy -> ECon(optTy, "None", [], None)
            | _ ->
                dotnetCall
                    ctx
                    r
                    "Microsoft.FSharp.Core.Operators.Unchecked"
                    "DefaultOf"
                    { info with GenericArgs = [ inner ] }
                    inner
        | Fable.Nullable(_, true) -> ECon(mapType ctx r t, "None", [], None)
        | Fable.DeclaredType(entRef, [ _ ]) when
            entRef.FullName = "System.Span`1" || entRef.FullName = "System.ReadOnlySpan`1"
            ->
            pure' "fable_rt.spanEmpty($R)" [] (mapType ctx r t)
        // (a struct: each field's default, as .NET zeroes it)
        | Fable.DeclaredType(entRef, genArgs) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent ->
                 ent.IsValueType
                 && not ent.IsFSharpUnion
                 && (ent.FSharpFields
                     |> List.filter (fun f -> not f.IsStatic)
                     |> List.forall (fun f -> hasDefault ctx f.FieldType))
             | None -> false)
            && (
                match entRef.Path with
                | Fable.SourcePath _ -> true
                | _ -> false
            )
            ->
            let ent = ctx.Com.GetEntity entRef

            let sub =
                if ent.GenericParameters.Length = genArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                    |> Map.ofList
                else
                    Map.empty

            let defaults =
                ent.FSharpFields
                |> List.filter (fun f -> not f.IsStatic)
                |> List.map (fun f ->
                    let ft = substFableType sub f.FieldType

                    dotnetCall
                        ctx
                        r
                        "Microsoft.FSharp.Core.Operators.Unchecked"
                        "DefaultOf"
                        { info with GenericArgs = [ ft ] }
                        ft
                )

            ECon(mapType ctx r t, "", defaults, None)
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.DateOnly" || entRef.FullName = "System.TimeOnly" ->
            libraryCall
                ctx
                r
                "DateOnly"
                (if entRef.FullName = "System.DateOnly" then
                     "minValue"
                 else
                     "timeMinValue")
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.DateTimeOffset" ->
            libraryCall
                ctx
                r
                "DateTimeOffset"
                "minValue"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.DateTime" ->
            libraryCall
                ctx
                r
                "DateTime"
                "minValue"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.TimeSpan" ->
            libraryCall
                ctx
                r
                "TimeSpan"
                "zero"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.Guid" ->
            libraryCall
                ctx
                r
                "Guid"
                "create"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        // (a struct `ListCollector<'T>()`: an empty collector)
        | Fable.DeclaredType(entRef, [ item ]) when
            entRef.FullName = "Microsoft.FSharp.Core.CompilerServices.ListCollector`1"
            ->
            libraryCall
                ctx
                r
                "ListCollector"
                "create"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = [ item ]
                }
                []
                t
        | Fable.DeclaredType(entRef, []) when entRef.FullName = "System.Uri" ->
            libraryCall
                ctx
                r
                "Uri"
                "empty"
                { info with
                    ThisArg = None
                    Args = []
                    GenericArgs = []
                }
                [ Fable.Value(Fable.UnitConstant, None) ]
                t
        // (a union of one case without fields has one value, which stands for it; null on
        // .NET, where nothing but a test for null tells them apart)
        | Fable.DeclaredType(entRef, _) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent ->
                 ent.IsFSharpUnion
                 && ent.UnionCases.Length = 1
                 && ent.UnionCases.Head.UnionCaseFields.IsEmpty
             | None -> false)
            ->
            let ent = ctx.Com.GetEntity entRef
            ECon(mapType ctx r t, ent.UnionCases.Head.Name, [], None)
        // (a Type: its null)
        | Fable.MetaType -> pure' "fable_rt.reflect.nullType()" [] (TPrim "fable_rt.reflect.Type")
        // (a class that has no values but null, a witness of SRTP: nothing)
        | Fable.DeclaredType(entRef, _) when isWitnessClass ctx entRef -> EUnit
        // (a class: null)
        | Fable.DeclaredType _ when (objOfType ctx r t).IsSome -> lw ctx (Fable.Value(Fable.Null t, r))
        // (an interface whose Zig type is nullable: None)
        | Fable.DeclaredType _ when
            isInterfaceType ctx.Com t
            && (
                match mapType ctx r t with
                | TOpt _ -> true
                | _ -> false
            )
            ->
            ECon(mapType ctx r t, "None", [], None)
        // (an array: the array's null, see fable_array.zig)
        | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> lw ctx (Fable.Value(Fable.Null t, r))
        // (of a type parameter: chosen for each type it stands for, see fable_rt.defaultOf)
        | Fable.GenericParam _ ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.defaultOf($R)", [], mapType ctx r t)
        // (a record, a union, a function, a tuple of them: .NET's null, or the nearest value,
        // see fable_rt.nullOf)
        | Fable.DeclaredType(entRef, _) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent -> ent.IsFSharpRecord || ent.IsFSharpUnion
             | None -> false)
            ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.nullOf($R)", [], mapType ctx r t)
        | Fable.LambdaType _
        | Fable.DelegateType _
        | Fable.List _
        | Fable.Tuple _
        | Fable.AnonymousRecordType _ ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.nullOf($R)", [], mapType ctx r t)
        | _ -> fail r "the Zig target has no default value of this type (%A); .NET's is null" t
    // ---- System.Text.Encoding: UTF-8 and UTF-16 (the runtime's TextEncoding) ----
    | "System.Text.Encoding", "get_UTF8", [] ->
        ctx.State.UsesRuntime <- true
        EEmit("fable_rt.TextEncoding.utf8", [], TPrim "fable_rt.TextEncoding")
    | "System.Text.Encoding", "get_Unicode", [] ->
        ctx.State.UsesRuntime <- true
        EEmit("fable_rt.TextEncoding.utf16le", [], TPrim "fable_rt.TextEncoding")
    | ("System.Text.Encoding" | "System.Text.UTF8Encoding" | "System.Text.UnicodeEncoding"), "GetBytes", [ enc; s ] when
        s.Type = Fable.String
        ->
        rt "fable_rt.encodingGetBytes($0, $1)" [ enc; s ] (mapType ctx r t)
    | ("System.Text.Encoding" | "System.Text.UTF8Encoding" | "System.Text.UnicodeEncoding"),
      "GetBytes",
      [ enc; chars; i; n ] -> rt "fable_rt.encodingGetBytesRange($0, $1, $2, $3)" [ enc; chars; i; n ] (mapType ctx r t)
    | ("System.Text.Encoding" | "System.Text.UTF8Encoding" | "System.Text.UnicodeEncoding"), "GetString", [ enc; bytes ] ->
        rt "fable_rt.encodingGetString($0, $1)" [ enc; bytes ] tStr
    | ("System.Text.Encoding" | "System.Text.UTF8Encoding" | "System.Text.UnicodeEncoding"),
      "GetString",
      [ enc; bytes; i; n ] -> rt "fable_rt.encodingGetStringRange($0, $1, $2, $3)" [ enc; bytes; i; n ] tStr
    | ("System.Text.Encoding" | "System.Text.UTF8Encoding" | "System.Text.UnicodeEncoding"), "GetByteCount", [ enc; s ] when
        s.Type = Fable.String
        ->
        rt "fable_rt.encodingGetByteCount($0, $1)" [ enc; s ] tI32
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] when
        unwrapNullness x.Type = Fable.String || unwrapNullness x.Type = Fable.Any
        ->
        pure' "($0 == null)" [ x ] tBool
    | "System.Decimal", "Equals", [ a; b ] when isDec a && isDec b -> pure' "fable_rt.eql($0, $1)" [ a; b ] tBool
    // `x.Equals y` and `x.CompareTo y` of numbers, chars and bools (NaN equals NaN, as .NET's
    // `Equals` has it)
    | ("System.Double" | "System.Single" | "System.Int32" | "System.Int64" | "System.Int16" | "System.SByte" | "System.Byte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Char" | "System.Boolean" | "System.Decimal" | "System.Numerics.BigInteger"),
      ("Equals" | "CompareTo"),
      [ a; b ] when a.Type = b.Type ->
        if name = "Equals" then
            pure' "(fable_rt.compare($0, $1) == 0)" [ a; b ] tBool
        else
            pure' "fable_rt.compare($0, $1)" [ a; b ] tI32
    | "System.String", "get_Length", [ s ] when neverNullIn ctx s -> pure' "fable_rt.strLength($0)" [ s ] tI32
    | "System.String", "get_Length", [ s ] -> rt "fable_rt.strLen($0)" [ s ] tI32
    | "Microsoft.FSharp.Core.StringModule", "Length", [ s ] -> pure' "fable_rt.strLength($0)" [ s ] tI32
    // (`for i in 0 .. s.Length - 1` or guarded `while i < s.Length`: in range, and not null)
    | "System.String", "get_Chars", [ s; i ]
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetString", [ s; i ] when
        Fable.Transforms.Zig.LowerHelpers.isArrayIndexInBounds ctx s i
        ->
        pure' "$0.?.units()[@as(usize, @intCast($1))]" [ s; i ] tChar
    | "System.String", "get_Chars", [ s; i ]
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetString", [ s; i ] ->
        rt "fable_rt.strAt($0, $1)" [ s; i ] tChar
    | "System.String", "IsNullOrEmpty", [ s ] -> pure' "fable_rt.strIsNullOrEmpty($0)" [ s ] tBool
    | "System.String", "IsNullOrWhiteSpace", [ s ] -> pure' "fable_rt.strIsNullOrWhiteSpace($0)" [ s ] tBool
    | "System.String", "CompareOrdinal", [ a; b ] -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
    // `x.Equals y` of a value of F#'s: its equality (structural for records, unions, lists, ...)
    // (`Equals` of arrays is that of .NET's objects: they are the same array)
    | "System.Object", "Equals", Uncast a :: Uncast b :: _ when
        a.Type = b.Type
        && (
            match a.Type with
            | Fable.Array _ -> true
            | _ -> false
        )
        ->
        pure' "($0 == $1)" [ a; b ] tBool
    | "System.Object", "Equals", Uncast a :: Uncast b :: _ when
        unwrapNullness a.Type = unwrapNullness b.Type
        && unwrapNullness a.Type <> Fable.String
        ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("eql", xs, tBool))
    | "System.String", "Equals", [ a; b ] when
        unwrapNullness a.Type = Fable.String && unwrapNullness b.Type = Fable.String
        ->
        if info.ThisArg.IsSome then
            rt "fable_rt.strEquals($0, $1)" [ a; b ] tBool
        else
            pure' "fable_rt.strEql($0, $1)" [ a; b ] tBool
    | "System.String", "ToString", [ s ] -> lw ctx s
    | "System.String", ".ctor", [ c; n ] when c.Type = Fable.Char -> rt "fable_rt.strOfChar($0, $1)" [ c; n ] tStr
    | "System.String", "Substring", [ s; start ] -> rt "fable_rt.strSubstring($0, $1, null)" [ s; start ] tStr
    | "System.String", "Substring", [ s; start; n ] -> rt "fable_rt.strSubstring($0, $1, $2)" [ s; start; n ] tStr
    | "System.String", "IndexOf", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strIndexOfChar($0, $1, 0)" [ s; x ] tI32
    | "System.String", "IndexOf", [ s; x; start ] when x.Type = Fable.Char && isInt start ->
        rt "fable_rt.strIndexOfChar($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "IndexOf", [ s; x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strIndexOf($0, $1, 0)" [ s; x ] tI32
    | "System.String", "IndexOf", [ s; x; start ] when unwrapNullness x.Type = Fable.String && isInt start ->
        rt "fable_rt.strIndexOf($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strLastIndexOfChar($0, $1)" [ s; x ] tI32
    | "System.String", "LastIndexOf", [ s; x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strLastIndexOf($0, $1)" [ s; x ] tI32
    | "System.String", "Contains", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strContainsChar($0, $1)" [ s; x ] tBool
    | "System.String", "Contains", [ s; x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strContains($0, $1)" [ s; x ] tBool
    | "System.String", "StartsWith", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strStartsWithChar($0, $1)" [ s; x ] tBool
    | "System.String", "StartsWith", [ s; x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strStartsWith($0, $1)" [ s; x ] tBool
    | "System.String", "EndsWith", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strEndsWithChar($0, $1)" [ s; x ] tBool
    | "System.String", "EndsWith", [ s; x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strEndsWith($0, $1)" [ s; x ] tBool
    // (there is no current culture here: `ToUpper` is `ToUpperInvariant`)
    | "System.String", ("ToUpper" | "ToUpperInvariant"), [ s ] -> ofString s "fable_rt.strCase($0, true)" [ s ] tStr
    | "System.String", ("ToLower" | "ToLowerInvariant"), [ s ] -> ofString s "fable_rt.strCase($0, false)" [ s ] tStr
    | "System.String", "Trim", [ s ] -> ofString s "fable_rt.strTrim($0, true, true, null)" [ s ] tStr
    | "System.String", "TrimStart", [ s ] -> ofString s "fable_rt.strTrim($0, true, false, null)" [ s ] tStr
    | "System.String", "TrimEnd", [ s ] -> ofString s "fable_rt.strTrim($0, false, true, null)" [ s ] tStr
    | "System.String", "Trim", [ s; c ] when c.Type = Fable.Char ->
        ofString s "fable_rt.strTrim($0, true, true, $1)" [ s; c ] tStr
    | "System.String", "TrimStart", [ s; c ] when c.Type = Fable.Char ->
        ofString s "fable_rt.strTrim($0, true, false, $1)" [ s; c ] tStr
    | "System.String", "TrimEnd", [ s; c ] when c.Type = Fable.Char ->
        ofString s "fable_rt.strTrim($0, false, true, $1)" [ s; c ] tStr
    | "System.String", "Replace", [ s; a; b ] when a.Type = Fable.Char && b.Type = Fable.Char ->
        ofString s "fable_rt.strReplaceChar($0, $1, $2)" [ s; a; b ] tStr
    | "System.String", "Replace", [ s; a; b ] when
        unwrapNullness a.Type = Fable.String && unwrapNullness b.Type = Fable.String
        ->
        rt "fable_rt.strReplace($0, $1, $2)" [ s; a; b ] tStr
    | "System.String", "Insert", [ s; at; x ] -> rt "fable_rt.strInsert($0, $1, $2)" [ s; at; x ] tStr
    | "System.String", "Remove", [ s; start ] -> rt "fable_rt.strRemove($0, $1, null)" [ s; start ] tStr
    | "System.String", "Remove", [ s; start; n ] -> rt "fable_rt.strRemove($0, $1, $2)" [ s; start; n ] tStr
    | "System.String", "PadLeft", [ s; n ] -> rt "fable_rt.strPad($0, true, $1, ' ')" [ s; n ] tStr
    | "System.String", "PadLeft", [ s; n; c ] -> rt "fable_rt.strPad($0, true, $1, $2)" [ s; n; c ] tStr
    | "System.String", "PadRight", [ s; n ] -> rt "fable_rt.strPad($0, false, $1, ' ')" [ s; n ] tStr
    | "System.String", "PadRight", [ s; n; c ] -> rt "fable_rt.strPad($0, false, $1, $2)" [ s; n; c ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Concat", [ sep; Uncast xs ] when xs.Type = Fable.List Fable.String ->
        pure' "fable_rt.strJoin($0, $1)" [ sep; xs ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Replicate", [ n; s ] -> rt "fable_rt.strReplicate($0, $1)" [ n; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Initialize", [ n; f ] -> rt "fable_rt.strInit($0, $1)" [ n; f ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Map", [ f; s ] -> rt "fable_rt.strMap($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "MapIndexed", [ f; s ] -> rt "fable_rt.strMapi($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Iterate", [ f; s ] -> rt "fable_rt.strIter($0, $1)" [ f; s ] tVoid
    | "Microsoft.FSharp.Core.StringModule", "IterateIndexed", [ f; s ] -> rt "fable_rt.strIteri($0, $1)" [ f; s ] tVoid
    | "Microsoft.FSharp.Core.StringModule", "ForAll", [ f; s ] -> rt "fable_rt.strForall($0, $1)" [ f; s ] tBool
    | "Microsoft.FSharp.Core.StringModule", "Exists", [ f; s ] -> rt "fable_rt.strExists($0, $1)" [ f; s ] tBool
    | "Microsoft.FSharp.Core.StringModule", "Filter", [ f; s ] -> rt "fable_rt.strFilter($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Collect", [ f; s ] -> rt "fable_rt.strCollect($0, $1)" [ f; s ] tStr
    // (`String.Concat(a, b, c)` of objects: the text of each, a null one as nothing)
    | "System.String", "Concat", parts when
        parts.Length >= 2
        && parts |> List.exists (fun x -> unwrapNullness x.Type <> Fable.String)
        && parts
           |> List.forall (fun x ->
               match x.Type with
               | Fable.Array _ -> false
               | _ -> true
           )
        ->
        let holes =
            parts
            |> List.mapi (fun i x ->
                if unwrapNullness x.Type = Fable.String then
                    $"$%d{i}"
                else
                    $"fable_rt.arg(.{{ .kind = 'T' }}, $%d{i})"
            )
            |> String.concat ", "

        pure' $"fable_rt.format(.{{ %s{holes} }})" parts tStr
    | "System.String", "Concat", parts when
        not parts.IsEmpty
        && parts |> List.forall (fun x -> unwrapNullness x.Type = Fable.String)
        ->
        let holes = parts |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "
        pure' $"fable_rt.format(.{{ %s{holes} }})" parts tStr
    | "Microsoft.FSharp.Core.Operators", ("op_Addition" | "op_Subtraction"), [ a; _ ] when
        (match a.Type with
         | Fable.DeclaredType(ent, _) -> ent.FullName = setName
         | _ -> false)
        ->
        let fn =
            if name = "op_Addition" then
                "opAddition"
            else
                "opSubtraction"

        let item =
            match a.Type with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Any

        libraryCall
            ctx
            r
            "Set"
            fn
            { info with
                GenericArgs = [ item ]
                MemberRef = None
                SignatureArgTypes = []
            }
            args
            t
    // `a + b + c`: one new string, whatever the number of parts
    | "Microsoft.FSharp.Core.Operators", "op_Addition", [ a; b ] when
        unwrapNullness a.Type = Fable.String && unwrapNullness b.Type = Fable.String
        ->
        let rec parts (x: Fable.Expr) : Fable.Expr list =
            match x with
            | Fable.Call(Fable.Import(imp, _, _), inner, t, _) when
                unwrapNullness t = Fable.String
                && imp.Selector = "op_Addition"
                && imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                && inner.Args.Length = 2
                && inner.Args |> List.forall (fun arg -> unwrapNullness arg.Type = Fable.String)
                ->
                inner.Args |> List.collect parts
            | _ -> [ x ]

        match parts a @ parts b with
        // (the left string is given up to the append, which grows it in place when nothing
        // else refers to it: `s <- s + x` in a loop is not quadratic)
        | [ a; b ] -> bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EEmit("fable_rt.strAppend($0, $1)", xs, tStr))
        | many ->
            // (literal text among the parts is written into the result directly)
            let values = List<Fable.Expr>()

            let texts =
                many
                |> List.map (fun part ->
                    match part with
                    | Fable.Value(Fable.StringConstant text, _) when (zigQuoted text).IsSome -> (zigQuoted text).Value
                    | _ ->
                        values.Add part
                        $"$%d{values.Count - 1}"
                )
                |> String.concat ", "

            bindArgs
                ctx
                (values |> Seq.map (lw ctx) |> List.ofSeq)
                (fun xs -> EEmit($"fable_rt.format(.{{ %s{texts} }})", xs, tStr))
    // `string x`
    // (a whole-number format, `B`, `X` or `D`, of a float or a decimal: .NET's FormatException,
    // when the program runs)
    | _, "ToString", [ x; Fable.Value(Fable.StringConstant net, _) ] when
        net.Length >= 1
        && net.Length <= 3
        && "BbXxDd".Contains(string net.[0])
        && (net.Length = 1 || System.Char.IsDigit net.[1])
        && (
            match x.Type with
            | Fable.Number((Float16 | Float32 | Float64 | Decimal), _) -> true
            | _ -> false
        )
        ->
        ctx.State.UsesRuntime <- true

        bindArgs ctx [ lw ctx x ] (fun _ -> ERt("fable_rt.formatSpecifierInvalid($R)", [], tStr))
    // `x.ToString("N2")` of a number: one of .NET's standard formats
    | _, "ToString", [ x; Fable.Value(Fable.StringConstant net, _) ] when
        (match x.Type with
         | Fable.Number _ -> true
         | _ -> false)
        ->
        checkNetFormat r net
        let net = zigEscape net

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EEmit(
                    $"fable_rt.format(.{{ fable_rt.arg(.{{ .net = \"%s{net}\" }}, %s{typedArg ctx r x 0}) }})",
                    xs,
                    tStr
                )
            )
    | _, "ToString", [ x ] when
        entity <> "Microsoft.FSharp.Core.Operators"
        && (
            match x.Type with
            | Fable.Number _ -> true
            | _ -> false
        )
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when unwrapNullness x.Type = Fable.Any ->
        if entity = "System.Object" then
            rt "fable_rt.anyToString($0, false)" [ x ] tStr
        else
            rt "fable_rt.anyToString($0, true)" [ x ] tStr
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when (ownToString ctx x.Type).IsSome ->
        let fn = (ownToString ctx x.Type).Value

        // (a member of a struct class takes its object by reference)
        let byRef =
            match x.Type with
            | Fable.DeclaredType(e, _) ->
                match ctx.Com.TryGetEntity e with
                | Some ent -> ent.IsValueType && not (ent.IsFSharpRecord || ent.IsFSharpUnion)
                | None -> false
            | _ -> false

        if byRef then
            let ir = lw ctx x
            let v = ctx.State.NewVar("this", typeOf ir, VLocal, false)
            ELet(v, ir, ECall(fn, [], [ EAddr(EVar v, true); EUnit ], tStr))
        else
            bindArgs ctx [ lw ctx x ] (fun xs -> ECall(fn, [], xs @ [ EUnit ], tStr))
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when x.Type <> unByref x.Type ->
        dotnetCall
            ctx
            r
            entity
            name
            { info with
                Args = [ readByref x ]
                ThisArg = None
            }
            t
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] ->
        let shapeCall fn shapeFn strict =
            match showShapeOf ctx r strict x.Type with
            | Some shape -> pure' $"%s{shapeFn}(%s{shape}, $0)" [ x ] tStr
            | None -> pure' $"%s{fn}($0)" [ x ] tStr

        match x.Type with
        // (the text of a null string is the empty string)
        | Fable.String when neverNullIn ctx x -> lw ctx x
        | Fable.String -> pure' "fable_rt.strConcat($0, null)" [ x ] tStr
        // (a record or a union is written by its `ToString`, which is `%A`)
        | Fable.AnonymousRecordType _ -> shapeCall "fable_rt.anyText" "fable_rt.anyTextShape" true
        | Fable.DeclaredType(entRef, _) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent -> ent.IsFSharpRecord || ent.IsFSharpUnion
             | None -> false)
            ->
            shapeCall "fable_rt.anyText" "fable_rt.anyTextShape" true
        | Fable.Option _
        | Fable.Tuple _
        | Fable.List _ -> shapeCall "fable_rt.toText" "fable_rt.toTextShape" false
        | Fable.DeclaredType(ent, _) when ent.FullName = mapName || ent.FullName = setName ->
            shapeCall "fable_rt.toText" "fable_rt.toTextShape" false
        // (a `Uri`: the library's Uri.fs writes it)
        | Fable.DeclaredType(e, []) when e.FullName = "System.Uri" ->
            libraryCall
                ctx
                r
                "Uri"
                "toString"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        | Fable.DeclaredType(e, []) when e.FullName = "System.DateOnly" || e.FullName = "System.TimeOnly" ->
            libraryCall
                ctx
                r
                "DateOnly"
                (if e.FullName = "System.DateOnly" then
                     "toString"
                 else
                     "timeToString")
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        | Fable.DeclaredType(e, []) when e.FullName = "System.DateTimeOffset" ->
            libraryCall
                ctx
                r
                "DateTimeOffset"
                "toString"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        | Fable.DeclaredType(e, []) when e.FullName = "System.DateTime" ->
            libraryCall
                ctx
                r
                "DateTime"
                "toString"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        | Fable.DeclaredType(e, []) when e.FullName = "System.TimeSpan" ->
            libraryCall
                ctx
                r
                "TimeSpan"
                "toString"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        | Fable.DeclaredType(e, []) when e.FullName = "System.Guid" ->
            libraryCall
                ctx
                r
                "Guid"
                "toString"
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                [ x ]
                t
        // (an exception: .NET's "Type: message", without the frames of its stack trace)
        | Fable.DeclaredType _ when mapType ctx r x.Type = TPrim "fable_rt.Exn" ->
            rt "fable_rt.exnToString($0)" [ x ] tStr
        // (an object: its class's ToString, or .NET's name of its class)
        | Fable.DeclaredType _ when (objOfType ctx r x.Type).IsSome -> rt "fable_rt.objText($0)" [ x ] tStr
        | Fable.Char ->
            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs -> EEmit("fable_rt.format(.{ fable_rt.arg(.{ .kind = 'c' }, @as(u16, $0)) })", xs, tStr))
        | Fable.Boolean
        | Fable.Number _ ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.format(.{{ %s{typedArg ctx r x 0} }})", xs, tStr))
        // (a type parameter: what the type it stands for gives, known when the Zig is compiled)
        | Fable.GenericParam _ -> rt "fable_rt.genericText($0)" [ x ] tStr
        // (`string ()`: the empty string, as .NET's null)
        | Fable.Unit -> ESeq(lwStmt ctx x, ELit("fable_rt.str(\"\")", tStr))
        | other -> fail r "the Zig target cannot turn a value of this type into text yet (%A)" other
    | _ -> Unchecked.defaultof<Expr>
