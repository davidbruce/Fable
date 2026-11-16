/// What the lowering asks about expressions and types before it lowers them; part of Fable2Zig.Lower.fs
module Fable.Transforms.Zig.LowerHelpers

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes

/// What the type parameters of `pattern` stand for, if `actual` is an instance of it.
let rec unify (found: Dictionary<string, Fable.Type>) (pattern: Fable.Type) (actual: Fable.Type) : unit =
    let all (ps: Fable.Type list) (xs: Fable.Type list) =
        if ps.Length = xs.Length then
            List.iter2 (unify found) ps xs

    /// a function type as the list of its arguments and its last result
    let rec uncurried (t: Fable.Type) : Fable.Type list * Fable.Type =
        match t with
        | Fable.LambdaType(a, ret) ->
            let rest, last = uncurried ret
            a :: rest, last
        | Fable.DelegateType(args, ret) ->
            let rest, last = uncurried ret
            args @ rest, last
        | _ -> [], t

    match pattern, actual with
    | Fable.GenericParam(name = name), _ ->
        if not (found.ContainsKey name) then
            found[name] <- actual
    | Fable.LambdaType(a1, r1), Fable.LambdaType(a2, r2) ->
        unify found a1 a2
        unify found r1 r2
    | (Fable.LambdaType _ | Fable.DelegateType _), (Fable.LambdaType _ | Fable.DelegateType _) ->
        // (one of them is written with its arguments in one step, the other is not)
        let args1, ret1 = uncurried pattern
        let args2, ret2 = uncurried actual

        if args1.Length = args2.Length then
            all args1 args2
            unify found ret1 ret2
    | Fable.Tuple(ts1, _), Fable.Tuple(ts2, _) -> all ts1 ts2
    | Fable.Option(t1, _), Fable.Option(t2, _) -> unify found t1 t2
    | Fable.DeclaredType(_, g1), Fable.DeclaredType(_, g2) -> all g1 g2
    | _ -> all pattern.Generics actual.Generics

/// The text of a Zig string literal (UTF-8) for F# text (UTF-16), or None when the text is
/// not well-formed (a surrogate on its own). `$` is written as an escape: the text may become
/// part of an `Emit` macro, where `$0` stands for an argument.
let zigQuoted (text: string) : string option =
    let sb = System.Text.StringBuilder("\"")
    let mutable ok = true
    let mutable i = 0

    while ok && i < text.Length do
        let c = text[i]

        if
            System.Char.IsHighSurrogate c
            && i + 1 < text.Length
            && System.Char.IsLowSurrogate text[i + 1]
        then
            sb.Append($"\\u{{%X{System.Char.ConvertToUtf32(c, text[i + 1])}}}") |> ignore
            i <- i + 1
        elif System.Char.IsSurrogate c then
            ok <- false
        else
            match c with
            | '"' -> sb.Append("\\\"") |> ignore
            | '\\' -> sb.Append("\\\\") |> ignore
            | '\n' -> sb.Append("\\n") |> ignore
            | '\r' -> sb.Append("\\r") |> ignore
            | '\t' -> sb.Append("\\t") |> ignore
            | '$' -> sb.Append("\\x24") |> ignore
            | c when c < ' ' || c = '\127' -> sb.Append($"\\x%02x{int c}") |> ignore
            | c when c < '\128' -> sb.Append(c) |> ignore
            | c -> sb.Append($"\\u{{%X{int c}}}") |> ignore

        i <- i + 1

    if ok then
        Some(sb.Append('"').ToString())
    else
        None

/// A string literal: static data of the generated program.
let stringLiteral (text: string) : string =
    match zigQuoted text with
    | Some quoted -> $"fable_rt.str(%s{quoted})"
    | None ->
        let units = text |> Seq.map (fun c -> string<int>(int c)) |> String.concat ", "
        $"fable_rt.strOf(&[_]u16{{ %s{units} }})"

/// One part of an F# format string: literal text, or a specifier that takes a value.
type FormatPart =
    | Text of string
    /// flags, width, precision, the letter, and the .NET format of a hole (`{x:N2}`)
    | Spec of string * int * int option * char * string

/// "%5d items%%" -> [ Spec("", 5, None, 'd'); Text " items%" ]. In an interpolated string every
/// hole is `%P()`, after a specifier of its own if it has one (`%d%P()`).
let parseFormat (r: SourceLocation option) (fmt: string) : FormatPart list =
    let parts = List<FormatPart>()
    let text = System.Text.StringBuilder()

    let flush () =
        if text.Length > 0 then
            parts.Add(Text(text.ToString()))
            text.Clear() |> ignore

    let mutable i = 0
    // the last part is a specifier that has not got its hole yet
    let mutable pending = false

    while i < fmt.Length do
        if fmt[i] <> '%' then
            text.Append(fmt[i]) |> ignore
            pending <- false
            i <- i + 1
        elif i + 1 < fmt.Length && fmt[i + 1] = '%' then
            text.Append('%') |> ignore
            pending <- false
            i <- i + 2
        else
            i <- i + 1
            let start = i

            while i < fmt.Length && "0-+ ".IndexOf(fmt[i]) >= 0 do
                i <- i + 1

            let flags = fmt.Substring(start, i - start)
            let widthStart = i

            while i < fmt.Length && System.Char.IsDigit fmt[i] do
                i <- i + 1

            let width =
                if i > widthStart then
                    int (fmt.Substring(widthStart, i - widthStart))
                else
                    0

            let precision =
                if i < fmt.Length && fmt[i] = '.' then
                    i <- i + 1
                    let precisionStart = i

                    while i < fmt.Length && System.Char.IsDigit fmt[i] do
                        i <- i + 1

                    Some(int (fmt.Substring(precisionStart, i - precisionStart)))
                else
                    None

            if i >= fmt.Length then
                fail r "the format string ends in the middle of a specifier"

            let letter = fmt[i]
            i <- i + 1

            if letter = 'P' then
                // (the hole of an interpolated string: `%P()`, or `%P(format)` with a .NET format)
                let net =
                    if i < fmt.Length && fmt[i] = '(' then
                        let close = fmt.IndexOf(')', i)
                        let text = fmt.Substring(i + 1, close - i - 1)
                        i <- close + 1
                        text
                    else
                        ""

                // a specifier right before the hole is the hole's (`%d{x}`)
                if pending then
                    pending <- false
                else
                    flush ()
                    parts.Add(Spec(flags, width, precision, 'P', net))
            else
                flush ()
                parts.Add(Spec(flags, width, precision, letter, ""))
                pending <- true

    flush ()
    List.ofSeq parts

/// `printfn "..."` and its relatives, and an interpolated string: which of them, the format
/// string, and the values of the holes of an interpolated string.
let (|PrintfCall|_|) (e: Fable.Expr) : (string * string * Fable.Expr list) option =
    let rec uncast (x: Fable.Expr) =
        match x with
        | Fable.TypeCast(inner, _) -> uncast inner
        | _ -> x

    let isDotnet (imp: Fable.ImportInfo) (entityPrefix: string) =
        imp.Path.StartsWith(Replacements.DotnetPrefix + entityPrefix, System.StringComparison.Ordinal)

    match e with
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        isDotnet imp "Microsoft.FSharp.Core.ExtraTopLevelOperators"
        && imp.Selector.StartsWith("PrintFormat", System.StringComparison.Ordinal)
        ->
        match info.Args |> List.map uncast with
        | [ Fable.Call(Fable.Import(ctor, _, _), ctorInfo, _, _) ] when
            ctor.Selector = ".ctor" && isDotnet ctor "Microsoft.FSharp.Core.PrintfFormat"
            ->
            match ctorInfo.Args with
            | Fable.Value(Fable.StringConstant fmt, _) :: rest ->
                let holes =
                    match rest with
                    | Fable.Value(Fable.NewArray(Fable.ArrayValues values, _, _), _) :: _ ->
                        values
                        |> List.map (fun v ->
                            match uncast v with
                            | Fable.Call(Fable.Import(box, _, _), boxInfo, _, _) when box.Selector = "Box" ->
                                boxInfo.Args.Head
                            | other -> other
                        )
                    | _ -> []

                Some(imp.Selector, fmt, holes)
            | _ -> None
        | _ -> None
    | _ -> None

/// `kprintf cont fmt args` as `cont (sprintf fmt args)`.
/// A name for a variable a rewrite binds around the program's code, which no name of the
/// program can be (`parsed$12`)
let tempName (ctx: Ctx) (baseName: string) : string =
    baseName + "$" + string (ctx.State.NewVar(baseName, tVoid, VLocal, false).Id)

/// (for the names of the values of a printf that is used as a function)
let internal printfValues =
    new System.Threading.ThreadLocal<int ref>(fun () -> ref 0)

let kprintf
    (imp: Fable.ImportInfo)
    (info: Fable.CallInfo)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (r: SourceLocation option)
    : Fable.Expr
    =
    let cont, fmtArg =
        match info.Args with
        | [ cont; fmtArg ] -> Some cont, fmtArg
        | [ fmtArg ] -> None, fmtArg
        | _ -> raise (ZigError("the Zig target does not support this kind of printf yet", r))

    let toString =
        Fable.Call(
            Fable.Import(
                { imp with
                    Selector = "PrintFormatToString"
                    Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.ExtraTopLevelOperators"
                },
                Fable.Any,
                None
            ),
            { info with Args = [ fmtArg ] },
            Fable.String,
            r
        )

    // (how many values the format takes: none more for an interpolated string, which has them)
    let needed =
        match toString with
        | PrintfCall(_, fmt, []) ->
            parseFormat r fmt
            |> List.filter (
                function
                | Spec _ -> true
                | Text _ -> false
            )
            |> List.length
        | _ -> args.Length

    // (the types a function type takes, the first `n` of them, and what is left)
    let rec peel (n: int) (t: Fable.Type) =
        match t with
        | Fable.LambdaType(a, rest) when n > 0 ->
            let ps, ret = peel (n - 1) rest
            a :: ps, ret
        | _ -> [], t

    // (the values of the format, the text given to the continuation, and what is left of the
    // values for what the continuation gives: `ksprintf append "%d" 42 "x"` is
    // `append (sprintf "%d" 42) "x"`)
    let finish (values: Fable.Expr list) (extra: Fable.Expr list) (t: Fable.Type) =
        let text =
            if values.IsEmpty then
                toString
            else
                Fable.CurriedApply(toString, values, Fable.String, r)

        match cont with
        | Some cont when extra.IsEmpty -> Fable.CurriedApply(cont, [ text ], t, r)
        | Some cont ->
            let contRet =
                match cont.Type with
                | Fable.LambdaType(_, ret) -> ret
                | _ -> Fable.Any

            Fable.CurriedApply(Fable.CurriedApply(cont, [ text ], contRet, r), extra, t, r)
        | None when extra.IsEmpty -> text
        | None -> Fable.CurriedApply(text, extra, t, r)

    if args.Length >= needed then
        let values, extra = List.splitAt needed args
        finish values extra t
    else
        // (fewer values than the format takes: the function of the others)
        let missing, ret = peel (needed - args.Length) t
        let n = printfValues.Value.Value + 1
        printfValues.Value.Value <- n

        let names =
            missing |> List.mapi (fun i ty -> AST.makeTypedIdent ty $"kfmt%d{n}_%d{i}")

        let body = finish (args @ (names |> List.map Fable.IdentExpr)) [] ret

        List.foldBack (fun (name: Fable.Ident) body -> Fable.Lambda(name, body, None)) names body

/// `Printf.bprintf sb fmt a b` and `Printf.kbprintf cont sb fmt a b`: the text appended to the
/// StringBuilder, then the continuation called
let bprintf
    (imp: Fable.ImportInfo)
    (info: Fable.CallInfo)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (r: SourceLocation option)
    : Fable.Expr
    =
    let cont, sb, fmtArg =
        match info.Args with
        | [ cont; sb; fmtArg ] -> Some cont, sb, fmtArg
        | [ sb; fmtArg ] -> None, sb, fmtArg
        | _ -> raise (ZigError("the Zig target does not support this kind of printf yet", r))

    let toString =
        Fable.Call(
            Fable.Import(
                { imp with
                    Selector = "PrintFormatToString"
                    Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.ExtraTopLevelOperators"
                },
                Fable.Any,
                None
            ),
            { info with Args = [ fmtArg ] },
            Fable.String,
            r
        )

    let text =
        if args.IsEmpty then
            toString
        else
            Fable.CurriedApply(toString, args, Fable.String, r)

    let sbType = sb.Type

    let append =
        Fable.Call(
            Fable.Import(
                {
                    Selector = "Append"
                    Path = Replacements.DotnetPrefix + "System.Text.StringBuilder"
                    Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                },
                Fable.Any,
                None
            ),
            Fable.CallInfo.Create(thisArg = sb, args = [ text ], sigArgTypes = [ Fable.String ]),
            sbType,
            r
        )

    let appended =
        Fable.Call(
            Fable.Import(
                {
                    Selector = "Ignore"
                    Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                    Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                },
                Fable.Any,
                None
            ),
            Fable.CallInfo.Create(args = [ append ], genArgs = [ sbType ]),
            Fable.Unit,
            r
        )

    match cont with
    | Some cont ->
        Fable.Sequential
            [
                appended
                Fable.CurriedApply(cont, [ Fable.Value(Fable.UnitConstant, None) ], t, r)
            ]
    | None -> appended

/// (for the names of the operands of `Math.DivRem`)
let internal divRemTemps =
    new System.Threading.ThreadLocal<int ref>(fun () -> ref 0)

/// Is this a culture or a format provider given to a .NET method (`CultureInfo.InvariantCulture`)?
let isCulture (x: Fable.Expr) =
    match unwrapNullness x.Type with
    | Fable.DeclaredType(e, _) ->
        e.FullName = "System.Globalization.CultureInfo"
        || e.FullName = "System.IFormatProvider"
    | _ -> false

/// A printf that has not been given all the values its format takes: the printf, and the
/// values it has.
let (|PrintfPartial|_|) (e: Fable.Expr) : (Fable.Expr * Fable.Expr list) option =
    let holes (fmt: string) =
        parseFormat None fmt
        |> List.filter (
            function
            | Spec _ -> true
            | Text _ -> false
        )
        |> List.length

    match e with
    | PrintfCall(_, fmt, []) when holes fmt > 0 -> Some(e, [])
    | Fable.CurriedApply(PrintfCall(_, fmt, []) as call, given, _, _) when given.Length < holes fmt -> Some(call, given)
    | _ -> None

/// The expression under the casts that F# puts where a list is given for a sequence.
let rec (|Uncast|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(Uncast inner, _) -> inner
    | _ -> e

/// The item type of what is a list here: a list, or a collection that `Map.keys` gives.
let listItem (t: Fable.Type) : Fable.Type option =
    match t with
    | Fable.List item -> Some item
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.ICollection`1" -> Some item
    | _ -> None

/// The functions of FSharp.Core that the part of the runtime library written in F# has: the
/// file, and the name there (the name FSharp.Core compiles the function to).
let libraryFunction (entity: string) (name: string) : (string * string) option =
    let has (names: string) =
        names.Split([| ' '; '\n' |], System.StringSplitOptions.RemoveEmptyEntries)
        |> Array.contains name

    // (the library names its functions as FSharp.Core compiles them, with a small first letter:
    // a name like `Map` is one that Fable would not leave alone)
    let small (s: string) =
        s.Substring(0, 1).ToLowerInvariant() + s.Substring(1)

    match entity with
    | "Microsoft.FSharp.Collections.ListModule" when
        has
            "Length Head Tail TryHead Last TryLast TryItem Item Singleton Reverse Append Concat Map MapIndexed Map2
             Iterate IterateIndexed Fold FoldBack Reduce Filter Choose Collect Exists ForAll Contains TryFind Find
             TryFindIndex FindIndex TryPick Pick Initialize Replicate Zip Unzip Take Truncate Skip TakeWhile SkipWhile
             Partition Indexed Pairwise Distinct ExactlyOne OfArray ToArray SortWith Sort SortBy SortDescending
             SortByDescending Max Min MaxBy MinBy DistinctBy GroupBy CountBy Except Scan SplitAt ChunkBySize
             Windowed Iterate2 ForAll2 Exists2 Fold2 Map3 Zip3 Head Permute AllPairs TryExactlyOne Where Get
             Cons Empty IsEmpty Transpose InsertAt RemoveAt UpdateAt MapFold MapFoldBack Unzip3 Unfold TryFindIndexBack
             TryFindBack FindIndexBack FindBack SplitInto ScanBack ReduceBack MapIndexed2 IterateIndexed2 FoldBack2
             InsertManyAt RemoveManyAt"
        ->
        Some("List", small name)
    // (the List module's random functions are in Array.fs, which can use both)
    | "Microsoft.FSharp.Collections.ListModule" when name.StartsWith("Random", System.StringComparison.Ordinal) ->
        Some("Array", "list" + name)
    // (a value option is an option here: its module is the same functions)
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "GetSlice" -> Some("List", "getSlice")
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "Cons" -> Some("List", "cons")
    | "Microsoft.FSharp.Collections.ListModule" when name = "ToSeq" -> Some("Seq", "ofList")
    | "Microsoft.FSharp.Collections.ArrayModule" when name = "ToSeq" -> Some("Seq", "ofArray")
    | "Microsoft.FSharp.Collections.MapModule" when name = "ToSeq" -> Some("Map", "toSeq")
    | "Microsoft.FSharp.Collections.SetModule" when name = "ToSeq" -> Some("Set", "toSeq")
    | "Microsoft.FSharp.Collections.SetModule" when name = "IntersectMany" -> Some("Set", "intersectMany")
    | "Microsoft.FSharp.Collections.ArrayModule" when name = "OfSeq" -> Some("Seq", "toArray")
    | "Microsoft.FSharp.Collections.SeqModule" when name = "Tail" -> Some("Seq", "tail")
    | "Microsoft.FSharp.Control.ObservableModule" -> Some("Observable", small name)
    | "Microsoft.FSharp.Control.EventModule" -> Some("Event", small name)
    | "Microsoft.FSharp.Collections.SeqModule" when name.StartsWith("Random", System.StringComparison.Ordinal) ->
        Some("Seq", small name)
    // (what `while`, `try ... finally` and `try ... with` in `seq { }` are)
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers" when
        name = "EnumerateWhile"
        || name = "EnumerateThenFinally"
        || name = "EnumerateTryWith"
        ->
        Some("Seq", small name)
    | "Microsoft.FSharp.Core.OptionModule"
    | "Microsoft.FSharp.Core.ValueOption" when
        has
            "Map Bind DefaultValue DefaultWith IsSome IsNone GetValue Iterate Filter Exists ForAll Fold OrElse
             OrElseWith ToList ToArray Count Contains Flatten Map2 FoldBack Map3 OfValueOption ToValueOption"
        ->
        Some("Option", small name)
    | "Microsoft.FSharp.Core.ValueOption" when name = "ToOption" -> Some("Option", "ofValueOption")
    | "Microsoft.FSharp.Core.ValueOption" when name = "OfOption" -> Some("Option", "toValueOption")
    | "Microsoft.FSharp.Core.Operators" when name = "DefaultArg" || name = "DefaultValueArg" ->
        Some("Option", "defaultArg")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_IsSome" ->
        Some("Option", "isSome")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_IsNone" ->
        Some("Option", "isNone")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_Value" ->
        Some("Option", "memberValue")
    | "Microsoft.FSharp.Core.ResultModule" when
        has
            "Map Bind MapError IsOk IsError Contains Count DefaultValue DefaultWith Exists ForAll Fold FoldBack
             Iterate ToArray ToList ToOption ToValueOption"
        ->
        Some("Result", small name)
    | "Microsoft.FSharp.Collections.MapModule" when
        has
            "Empty IsEmpty Add Find TryFind ContainsKey Remove Change Iterate Fold FoldBack ToList ToArray OfList OfArray
             OfSeq Count Exists ForAll Filter Partition Map TryPick Pick TryFindKey FindKey Keys Values MinKeyValue
             MaxKeyValue"
        ->
        Some(
            "Map",
            (if name = "OfSeq" then
                 "ofList"
             else
                 small name)
        )
    | "Microsoft.FSharp.Collections.FSharpMap`2" ->
        match name with
        | "get_Item" -> Some("Map", "getItem")
        | "Add"
        | "Remove"
        | "ContainsKey"
        | "TryFind"
        | "Change" -> Some("Map", "member" + name)
        | "get_Count" -> Some("Map", "memberCount")
        | "get_IsEmpty" -> Some("Map", "memberIsEmpty")
        // `Map [ (k, v); ... ]`
        | ".ctor" -> Some("Map", "ofList")
        | _ -> None
    | "Microsoft.FSharp.Collections.SetModule" when
        has
            "Empty IsEmpty Add Singleton Contains Remove Iterate Fold FoldBack ToList ToArray OfList OfArray OfSeq Count
             Exists ForAll Filter Partition Map Union UnionMany Intersect Difference IsSubset IsSuperset IsProperSubset
             IsProperSuperset MinElement MaxElement"
        ->
        Some(
            "Set",
            (if name = "OfSeq" then
                 "ofList"
             else
                 small name)
        )
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators" when name = "CreateSet" -> Some("Set", "ofList")
    | "Microsoft.FSharp.Collections.ListModule" when name = "OfSeq" -> Some("List", "ofSeq")
    | "Microsoft.FSharp.Collections.ArrayModule" when
        has
            "Singleton Replicate Head TryHead Last TryLast Item TryItem ExactlyOne TryFindIndex FindIndex TryFind Find
             TryFindBack TryPick Pick Choose Collect Concat FoldBack Reduce Scan Max Min MaxBy MinBy SortWith Sort SortBy
             SortDescending SortByDescending SortInPlaceWith SortInPlace SortInPlaceBy Distinct DistinctBy GroupBy
             CountBy Indexed Zip Unzip Map2 Iterate2 Fold2 Exists2 ForAll2 Partition Take Truncate Skip TakeWhile
             SkipWhile SplitAt ChunkBySize Windowed Pairwise AllPairs Except CopyTo InsertAt InsertManyAt RemoveAt
             RemoveManyAt UpdateAt Where Tail TryExactlyOne TryFindIndexBack FindIndexBack FindBack ReduceBack ScanBack
             MapFold MapFoldBack Map3 MapIndexed2 IterateIndexed2 FoldBack2 Zip3 Unzip3 Transpose SplitInto Permute
             CompareWith RandomShuffle RandomShuffleWith RandomShuffleBy RandomChoice RandomChoiceWith RandomChoiceBy RandomChoices RandomChoicesWith RandomChoicesBy RandomSample RandomSampleWith RandomSampleBy RandomShuffleInPlace RandomShuffleInPlaceWith RandomShuffleInPlaceBy"
        ->
        Some(
            "Array",
            (if name = "CopyTo" then
                 "blit"
             else
                 small name)
        )
    | "Microsoft.FSharp.Collections.SeqModule" when
        has
            "Empty Singleton Delay OfList OfArray Append Map MapIndexed Filter Where Choose Collect Concat Initialize InitializeInfinite Unfold Take Truncate Skip TakeWhile SkipWhile Zip Indexed Pairwise Iterate IterateIndexed Fold ToList ToArray Length IsEmpty TryHead Head TryLast Last TryItem Item TryFind Find TryPick Pick Exists ForAll Contains Reduce Reverse Sort SortBy SortWith SortDescending Distinct Max Min MaxBy MinBy GroupBy CountBy Cache
             Map2 Zip3 Scan Replicate DistinctBy Except Windowed ChunkBySize Cast ReadOnly Iterate2 Fold2 Exists2 ForAll2
             CompareWith TryFindIndex FindIndex TryFindBack FindBack TryFindIndexBack FindIndexBack FoldBack FoldBack2
             ExactlyOne TryExactlyOne ReduceBack SortByDescending SplitInto Permute MapFold MapFoldBack AllPairs
             InsertAt InsertManyAt RemoveAt RemoveManyAt UpdateAt Transpose"
        ->
        Some("Seq", small name)
    | "Microsoft.FSharp.Core.Operators" when name = "CreateSequence" -> Some("Seq", "createSequence")
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder" when
        has "Return ReturnFrom Zero Delay Bind Combine TryWith TryFinally While For"
        ->
        Some("Async", "builder" + name)
    | "Microsoft.FSharp.Control.FSharpAsync" ->
        match name with
        | "RunSynchronously" -> Some("Async", "runSynchronously")
        | "StartImmediate" -> Some("Async", "startImmediate")
        | "Start" -> Some("Async", "startAsync")
        | "Sleep" -> Some("Async", "sleep")
        | "Ignore" -> Some("Async", "ignoreAsync")
        | "Catch" -> Some("Async", "catch")
        | "Parallel" -> Some("Async", "parallelAll")
        | _ -> None
    | "Microsoft.FSharp.Collections.FSharpSet`1" ->
        match name with
        | ".ctor" -> Some("Set", "ofList")
        | "Add"
        | "Remove"
        | "Contains" -> Some("Set", "member" + name)
        | "get_Count"
        | "get_IsEmpty"
        | "get_MinimumElement"
        | "get_MaximumElement" -> Some("Set", "member" + name.Substring 4)
        | "IsSubsetOf"
        | "IsSupersetOf"
        | "IsProperSubsetOf"
        | "IsProperSupersetOf" -> Some("Set", "member" + name)
        | "op_Addition" -> Some("Set", "opAddition")
        | "op_Subtraction" -> Some("Set", "opSubtraction")
        | _ -> None
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "get_Item" -> Some("List", "getItem")
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "get_Length" -> Some("List", "length")
    | "Microsoft.FSharp.Core.Operators" when name = "op_Append" -> Some("List", "append")
    | _ -> None

/// The type a byref points at; any other type as it is.
let unByref (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" -> inner
    | _ -> t

/// A read of what a byref points at, typed as that: `string s.[i]`, `%d` of it.
let readByref (e: Fable.Expr) : Fable.Expr =
    match e.Type with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
        Fable.TypeCast(e, inner)
    | _ -> e

/// Pull a pointer (`byref`) out of a dereference or variable, keeping any enclosing bindings.
let rec tryAddress (ir: Expr) : Expr option =
    match ir with
    | EDeref(p, _) -> Some p
    | _ when
        (match typeOf ir with
         | TPtr _ -> true
         | _ -> false)
        ->
        Some ir
    | EVar v -> Some(EAddr(EVar v, not v.FMutable))
    // (a field of a reference record that holds a plain value, as `&counter.contents` for
    // `Interlocked`: what is written through it needs no count)
    | EGet(EVar _ as cell, PField f, ty) when
        not (isManaged ty)
        && (
            match typeOf cell with
            | TEnt({ Kind = KRefRecord }, _) -> true
            | _ -> false
        )
        ->
        Some(EAddr(EGet(cell, PField f, ty), false))
    // (a module-level mutable value, read: its own place)
    | EEmit("fable_rt.dup($0)", [ EVar v ], _) when v.Kind = VGlobal -> Some(EAddr(EVar v, not v.FMutable))
    | ELet(v, rhs, body) -> tryAddress body |> Option.map (fun b -> ELet(v, rhs, b))
    | ESeq(s, body) -> tryAddress body |> Option.map (fun b -> ESeq(s, b))
    | _ -> None

/// The expression under the casts and unboxing that F# puts around `x` in `use x = ...`.
let rec (|Unboxed|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(Unboxed inner, _) -> inner
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "UnboxGeneric" || imp.Selector = "UnboxFast")
        && info.Args.Length = 1
        ->
        let (Unboxed inner) = info.Args.Head
        inner
    | _ -> e

let rec (|UnboxedOrBox|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(UnboxedOrBox inner, _) -> inner
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "UnboxGeneric"
         || imp.Selector = "UnboxFast"
         || imp.Selector = "Box")
        && info.Args.Length = 1
        ->
        let (UnboxedOrBox inner) = info.Args.Head
        inner
    | _ -> e

/// Does a declared type (not an interface) implement the interface? None when that is not
/// known here.
let implements (com: Compiler) (t: Fable.Type) (ifaceFullName: string) : bool option =
    match unwrapNullness t with
    | Fable.DeclaredType(entRef, _) ->
        match com.TryGetEntity entRef with
        | Some ent when not ent.IsInterface ->
            Some(ent.AllInterfaces |> Seq.exists (fun i -> i.Entity.FullName = ifaceFullName))
        | _ -> None
    | _ -> None

let implementsType (com: Compiler) (t: Fable.Type) (ifaceType: Fable.Type) : bool option =
    let rec hasGenParam (ty: Fable.Type) =
        match ty with
        | Fable.GenericParam _ -> true
        | _ -> ty.Generics |> List.exists hasGenParam

    match unwrapNullness t, unwrapNullness ifaceType with
    | Fable.DeclaredType(entRef, typeArgs), Fable.DeclaredType(ifaceRef, ifaceArgs) ->
        match com.TryGetEntity entRef with
        | Some ent when not ent.IsInterface ->
            let subst =
                if ent.GenericParameters.Length = typeArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) typeArgs
                    |> Map.ofList
                else
                    Map.empty

            let candidates =
                ent.AllInterfaces
                |> Seq.filter (fun i -> i.Entity.FullName = ifaceRef.FullName)
                |> Seq.map (fun i -> i.GenericArgs |> List.map (substFableType subst))
                |> Seq.toList

            if candidates.IsEmpty then
                Some false
            elif ifaceArgs.IsEmpty then
                Some true
            elif
                ifaceArgs |> List.exists hasGenParam
                || candidates |> List.exists (List.exists hasGenParam)
            then
                if candidates |> List.contains ifaceArgs then
                    Some true
                else
                    None
            else
                Some(candidates |> List.contains ifaceArgs)
        | Some ent when ent.IsInterface ->
            let subst =
                if ent.GenericParameters.Length = typeArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) typeArgs
                    |> Map.ofList
                else
                    Map.empty

            if
                entRef.FullName = ifaceRef.FullName
                && (ifaceArgs.IsEmpty || typeArgs = ifaceArgs)
            then
                Some true
            else
                let hasBase =
                    ent.AllInterfaces
                    |> Seq.exists (fun i ->
                        i.Entity.FullName = ifaceRef.FullName
                        && (ifaceArgs.IsEmpty
                            || (i.GenericArgs |> List.map (substFableType subst)) = ifaceArgs)
                    )

                if hasBase then
                    Some true
                else
                    None
        | _ -> None
    | _ -> None

/// The entity of `seq<'T>`.
let seqEntRef: Fable.EntityRef =
    {
        FullName = "System.Collections.Generic.IEnumerable`1"
        Path = Fable.CoreAssemblyName "System.Runtime"
    }


let taskCodeOf (t: Fable.Type) : Fable.Type =
    Fable.DeclaredType(
        {
            FullName = taskCodeName
            Path = Fable.CoreAssemblyName "FSharp.Core"
        },
        [ t ]
    )

/// F#'s resumable code (`TaskCode`): a delegate of a byref to a state machine.
let rec isResumableCode (t: Fable.Type) : bool =
    match t with
    | Fable.DelegateType(args, _) ->
        args
        |> List.exists (fun a ->
            match a with
            | Fable.DeclaredType(_, [ Fable.DeclaredType(sm, _); _ ]) ->
                sm.FullName.StartsWith(
                    "Microsoft.FSharp.Core.CompilerServices.ResumableStateMachine",
                    System.StringComparison.Ordinal
                )
            | _ -> false
        )
    | Fable.DeclaredType(ent, _) ->
        ent.FullName.StartsWith("Microsoft.FSharp.Control.TaskCode", System.StringComparison.Ordinal)
    | _ -> false

/// The calls of `task { }` have no type in what Fable gives (`Any`): the type of each is found
/// here from its arguments, from the inside out.
let typeTaskBuilders (body: Fable.Expr) : Fable.Expr =
    let itemOf (t: Fable.Type) =
        match t with
        | Fable.DeclaredType(_, [ item ]) -> item
        | _ -> Fable.Any

    let retOf (t: Fable.Type) =
        match t with
        | Fable.LambdaType(_, ret) -> ret
        | Fable.DelegateType(_, ret) -> ret
        | _ -> Fable.Any

    body
    |> AST.visitFromInsideOut (fun e ->
        match e with
        | Fable.Call(Fable.Import(imp, it, ir) as callee, info, callTy, r) when
            imp.Path.StartsWith(
                Replacements.DotnetPrefix + "Microsoft.FSharp.Control.TaskBuilder",
                System.StringComparison.Ordinal
            )
            && (callTy = Fable.Any || isResumableCode callTy)
            ->
            let name = imp.Selector.Substring(imp.Selector.LastIndexOf '.' + 1)

            let t =
                match name, info.Args with
                | "Return", [ x ] -> taskCodeOf x.Type
                | "Zero", _ -> taskCodeOf Fable.Unit
                | "Delay", [ f ] -> retOf f.Type
                | "Bind", [ _; cont ] -> retOf cont.Type
                | "ReturnFrom", [ task ] -> taskCodeOf (itemOf task.Type)
                | "Combine", [ _; second ] -> second.Type
                | ("While" | "For"), _ -> taskCodeOf Fable.Unit
                | ("TryWith" | "TryFinally"), b :: _ -> b.Type
                | "Using", [ _; binder ] -> retOf binder.Type
                | _ -> Fable.Any

            Fable.Call(callee, info, t, r)
        | _ -> e
    )

/// Is this F#'s `seq<'T>`?
let isSeqType (t: Fable.Type) : bool =
    match t with
    | Fable.DeclaredType(ent, [ _ ]) -> ent.FullName = "System.Collections.Generic.IEnumerable`1"
    // (the non-generic IEnumerable: a sequence of objects here)
    | Fable.DeclaredType(ent, []) -> ent.FullName = "System.Collections.IEnumerable"
    | _ -> false

/// Is this the type of an interface?
let isInterfaceType (com: Compiler) (t: Fable.Type) : bool =
    match unwrapNullness t with
    | Fable.DeclaredType(entRef, _) ->
        match com.TryGetEntity entRef with
        | Some ent -> ent.IsInterface
        | None -> false
    | _ -> false

/// A class's constructor as a function that makes the object: the fields are computed in
/// order, as locals, and the object is made of them at the end. (`this` cannot be used before
/// all its fields are there.)
/// The class and its ancestors, the class first.
let rec ancestors (o: ObjInfo) : ObjInfo list =
    o
    :: (
        match o.Parent with
        | Some p -> ancestors p
        | None -> []
    )

let chainType (o: ObjInfo) : Fable.Type = Fable.DeclaredType(o.Chain.Ref, [])

/// A class's own type parameters, as F# types (the arguments of its structs within its code)
let ownArgs (o: ObjInfo) : Fable.Type list =
    o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, []))

/// The type of the chain of a class of these type arguments
let chainTypeOf (o: ObjInfo) (genArgs: Fable.Type list) : Fable.Type =
    Fable.DeclaredType(
        o.Chain.Ref,
        (if o.Gens.IsEmpty then
             []
         else
             genArgs)
    )

/// The Zig name of a class's type (`Circle__type`).
let objTypeName (o: ObjInfo) : string = callTarget (o.Prefix + "__type")

/// The structs of fields of a class and the classes above it, the root's first, as Zig text.
let partNames (o: ObjInfo) : string =
    ancestors o
    |> List.rev
    |> List.map (fun k -> callTarget k.Part.Name)
    |> String.concat ", "

/// Each class of an object's chain with its type arguments, the object's class first: `args` are
/// the class's own; a base class's are what the class gives it.
let levelArgs (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (args: Ty list) : (ObjInfo * Ty list) list =
    let rec go (k: ObjInfo) (kargs: Ty list) =
        (k, kargs)
        :: (
            match k.Parent with
            | Some p ->
                let subst =
                    if k.Gens.Length = kargs.Length then
                        List.zip k.Gens kargs |> Map.ofList
                    else
                        Map.empty

                go p (k.ParentArgs |> List.map (mapTypeArg ctx r >> substTy subst))
            | None -> []
        )

    go o args

/// The type arguments of an object's class, from its F# type
let objArgs (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty list =
    match t with
    | Fable.DeclaredType(_, gs) -> gs |> List.map (mapTypeArg ctx r)
    | _ -> []

/// The type arguments of the level `level` of the chain of an object of type `t`
let argsOfLevel (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (t: Fable.Type) (level: ObjInfo) : Ty list =
    levelArgs ctx r o (objArgs ctx r t)
    |> List.tryFind (fun (k, _) -> k.FullName = level.FullName)
    |> Option.map snd
    |> Option.defaultValue []

/// A pointer to a class's object type, of these type arguments (`&Circle__type`, or
/// `Box__type(i32)` for a generic class)
let objTypeRef (o: ObjInfo) (args: Ty list) : string =
    if o.Gens.IsEmpty then
        "&" + objTypeName o
    else
        objTypeName o + "(" + (args |> List.map zigType |> String.concat ", ") + ")"

/// `partNames` of a chain of type arguments
let partNamesOf (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (args: Ty list) : string =
    levelArgs ctx r o args
    |> List.rev
    |> List.map (fun (k, kargs) -> zigType (TEnt(k.Part, kargs)))
    |> String.concat ", "

/// The class of the chain that declares a field.
let fieldOwner (o: ObjInfo) (field: string) : ObjInfo option =
    ancestors o
    |> List.tryFind (fun k -> caseFields (TEnt(k.Part, [])) "" |> List.exists (fun (f, _) -> f = field))

/// The class that introduced a virtual member, and the type of its function value.
let virtualSlot (o: ObjInfo) (slot: string) : (ObjInfo * Ty) option =
    ancestors o
    |> List.tryPick (fun k ->
        k.Slots
        |> List.tryFind (fun (s, _) -> s = slot)
        |> Option.map (fun (_, ty) -> k, ty)
    )

/// Does the class itself implement the virtual member (`override`, or `default` in the class that
/// introduces it)?
let classImplements (com: Compiler) (k: ObjInfo) (slot: string) : bool =
    match com.TryGetEntity k.Ref with
    | Some ent ->
        ent.MembersFunctionsAndValues
        |> Seq.exists (fun m ->
            m.IsOverrideOrExplicitInterfaceImplementation
            && not m.IsDispatchSlot
            && m.CompiledName = slot
        )
    | None -> false

/// The function that implements a virtual member for objects of class `o`: the one of the most
/// derived class of its chain that has one.
let implementationOf (com: Compiler) (r: SourceLocation option) (o: ObjInfo) (slot: string) : string =
    match ancestors o |> List.tryFind (fun k -> classImplements com k slot) with
    | Some k -> implName k.Prefix slot
    | None -> fail r "the Zig target finds no implementation of %s for %s" slot o.FullName

/// The compiled name of the member a call goes to.
let slotName (com: Compiler) (call: Fable.CallInfo) (fieldName: string) : string =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m ->
        // (an overload of an interface's member: its field says which)
        match m.DeclaringEntity |> Option.bind com.TryGetEntity with
        | Some owner when owner.IsInterface && m.IsDispatchSlot -> slotKey owner m.CompiledName (paramTypesOf m)
        | _ -> m.CompiledName
    | None -> fieldName.Substring(fieldName.LastIndexOf '.' + 1)

/// The field of an interface's struct that a member implements (an object expression's, or a
/// class's `interface ... with`)
let implementedSlot (com: Compiler) (m: Fable.MemberFunctionOrValue) : string =
    let compiled = m.CompiledName.Substring(m.CompiledName.LastIndexOf '.' + 1)

    // (some members cannot say what they implement: those of .NET's own interfaces)
    let signature =
        try
            m.ImplementedAbstractSignatures |> Seq.tryHead
        with _ ->
            None

    match signature with
    | Some sg ->
        match sg.DeclaringType with
        | Fable.DeclaredType(i, _) ->
            match com.TryGetEntity i with
            | Some owner when owner.IsInterface -> slotKey owner compiled (paramTypesOf m)
            | _ -> compiled
        | _ -> compiled
    | None -> compiled

/// The compiled name an implementation's function is named by: an overload's with its slot
let implFnName (com: Compiler) (m: Fable.MemberFunctionOrValue) : string =
    let slot = implementedSlot com m

    if slot.Contains "$" then
        m.CompiledName.Substring(0, m.CompiledName.LastIndexOf '.' + 1) + slot
    else
        m.CompiledName


let isConstructorCall (com: Compiler) (call: Fable.CallInfo) : bool =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m -> m.IsConstructor
    | None -> false

/// The prefix of the functions of a class's members: for an object, of the class of its chain
/// that implements `iface` when one is given.
let classPrefixWith
    (com: Compiler)
    (objOf: Fable.EntityRef -> ObjInfo option)
    (entName: Fable.EntityRef -> string)
    (classRef: Fable.EntityRef)
    (iface: string option)
    : string
    =
    match objOf classRef with
    | Some o ->
        match iface with
        | Some i ->
            ancestors o
            |> List.tryFind (fun k ->
                match com.TryGetEntity k.Ref with
                | Some ent -> ent.DeclaredInterfaces |> Seq.exists (fun d -> d.Entity.FullName = i)
                | None -> false
            )
            |> Option.defaultValue o
            |> fun k -> k.Prefix
        | None -> o.Prefix
    | None -> entName classRef

let classPrefix (ctx: Ctx) (r: SourceLocation option) (classRef: Fable.EntityRef) (iface: string option) : string =
    classPrefixWith ctx.Com (objInfo ctx r) (fun c -> (entOf ctx r c).Name) classRef iface

/// The function that implements member `name` of interface `iface` for a class: the class's
/// own, or the one of the nearest class above it that has one. (A member is implemented under
/// the name of the interface written in `interface X with`, which may inherit `iface`.)
let interfaceImpl
    (ctx: Ctx)
    (r: SourceLocation option)
    (classRef: Fable.EntityRef)
    (iface: string)
    (name: string)
    : string
    =
    let classes =
        match objInfo ctx r classRef with
        | Some o -> ancestors o |> List.map (fun k -> k.Ref, k.Prefix)
        | None -> [ classRef, (entOf ctx r classRef).Name ]

    let found =
        classes
        |> List.tryPick (fun (ref, prefix) ->
            match ctx.Com.TryGetEntity ref with
            | Some ent ->
                ent.MembersFunctionsAndValues
                |> Seq.tryFind (fun m ->
                    m.IsOverrideOrExplicitInterfaceImplementation
                    && (if name.Contains "$" then
                            implementedSlot ctx.Com m = name
                        else
                            m.CompiledName.EndsWith("." + name, System.StringComparison.Ordinal))
                )
                |> Option.map (fun m -> implName prefix (implFnName ctx.Com m))
            | None -> None
        )

    match found with
    | Some f -> f
    | None -> implName (classPrefix ctx r classRef (Some iface)) (iface + "." + name)

/// Like `interfaceImpl`, paired with the implementing ancestor's type arguments for `srcType`.
let interfaceImplSlot
    (ctx: Ctx)
    (r: SourceLocation option)
    (srcType: Fable.Type)
    (classRef: Fable.EntityRef)
    (iface: string)
    (name: string)
    : string * Ty list
    =
    match objInfo ctx r classRef with
    | Some o ->
        let found =
            ancestors o
            |> List.tryPick (fun k ->
                match ctx.Com.TryGetEntity k.Ref with
                | Some ent ->
                    ent.MembersFunctionsAndValues
                    |> Seq.tryFind (fun m ->
                        m.IsOverrideOrExplicitInterfaceImplementation
                        && (if name.Contains "$" then
                                implementedSlot ctx.Com m = name
                            else
                                m.CompiledName.EndsWith("." + name, System.StringComparison.Ordinal))
                    )
                    |> Option.map (fun m -> implName k.Prefix (implFnName ctx.Com m), argsOfLevel ctx r o srcType k)
                | None -> None
            )

        match found with
        | Some res -> res
        | None ->
            let owner =
                ancestors o
                |> List.tryFind (fun k ->
                    match ctx.Com.TryGetEntity k.Ref with
                    | Some ent -> ent.DeclaredInterfaces |> Seq.exists (fun d -> d.Entity.FullName = iface)
                    | None -> false
                )
                |> Option.defaultValue o

            implName owner.Prefix (iface + "." + name), argsOfLevel ctx r o srcType owner
    | None ->
        let typeArgs =
            match srcType with
            | Fable.DeclaredType(_, gs) -> gs |> List.map (mapTypeArg ctx r)
            | _ -> []

        interfaceImpl ctx r classRef iface name, typeArgs

/// What the file emits for a class that takes part in inheritance that it declares.
let objDecl (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (dotnetName: string) : ObjDecl =
    let com = ctx.Com
    // (each class of the chain with its type arguments, in terms of this class's own)
    let levels = levelArgs ctx r o (o.Gens |> List.map TGen)

    let argsOf (k: ObjInfo) =
        levels
        |> List.tryFind (fun (x, _) -> x.FullName = k.FullName)
        |> Option.map snd
        |> Option.defaultValue []

    // (the class of the chain whose member fills a slot)
    let implementer (slot: string) =
        match ancestors o |> List.tryFind (fun k -> classImplements com k slot) with
        | Some k -> k
        | None -> fail r "the Zig target finds no implementation of %s for %s" slot o.FullName

    let tables =
        levels
        |> List.rev
        |> List.map (fun (level, largs) ->
            match level.Table with
            | Some vt when not o.IsAbstract ->
                let subst =
                    if level.Gens.Length = largs.Length then
                        List.zip level.Gens largs |> Map.ofList
                    else
                        Map.empty

                let entries =
                    level.Slots
                    |> List.map (fun (slot, slotTy) ->
                        let k = implementer slot
                        slot, implName k.Prefix slot, argsOf k, substTy subst slotTy
                    )

                Some(TEnt(vt, largs), entries)
            | _ -> None
        )

    // (the interfaces of the class, with the tables a value of each made of its object has)
    let ifaces =
        if o.IsAbstract then
            []
        else
            match com.TryGetEntity o.Ref with
            | Some ent ->
                let srcType =
                    Fable.DeclaredType(o.Ref, o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, [])))

                ent.AllInterfaces
                |> Seq.toList
                // (the interfaces of the program: .NET's have tables of their own here)
                |> List.filter (fun i ->
                    match i.Entity.Path with
                    | Fable.SourcePath _
                    | Fable.PrecompiledLib _ -> true
                    | _ -> false
                )
                |> List.choose (fun i ->
                    let ifaceType = Fable.DeclaredType(i.Entity, i.GenericArgs)

                    try
                        if not (isInterfaceType com ifaceType) then
                            None
                        else
                            match mapType ctx r ifaceType with
                            | TOpt(TEnt(e, _) as s)
                            | (TEnt(e, _) as s) when e.Kind = KIface ->
                                let slots =
                                    caseFields s ""
                                    |> List.map (fun (f, _) ->
                                        f, interfaceImplSlot ctx r srcType o.Ref i.Entity.FullName f
                                    )

                                Some(s, slots)
                            | _ -> None
                    with _ ->
                        None
                )
            | None -> []

    {
        Ifaces = ifaces
        TypeName = o.Prefix + "__type"
        TypeParams = o.Gens
        Chain = TEnt(o.Chain, o.Gens |> List.map TGen)
        DotnetName = dotnetName
        Parent = o.Parent |> Option.map (fun p -> objTypeRef p (argsOf p))
        Tables = tables
        ToString =
            ancestors o
            |> List.tryFind (fun k -> classImplements com k "ToString")
            |> Option.map (fun k -> k.Prefix + "__ToString", argsOf k)
        Thunks = []
        Overrides =
            [
                "equals", "Equals"
                "hash", "GetHashCode"
                "compare", "System.IComparable.CompareTo"
            ]
            |> List.choose (fun (hook, slot) ->
                ancestors o
                |> List.tryFind (fun k -> classImplements com k slot)
                |> Option.map (fun k -> hook, implName k.Prefix slot)
            )
    }

/// A constructor as a function that computes the fields in order and ends with `finish` of
/// their values.
let constructorBodyWith
    (fieldNames: string list)
    (defaults: string -> Fable.Expr option)
    (finish: Fable.Expr list -> Fable.Expr)
    (body: Fable.Expr)
    : Fable.Expr
    =
    let fieldIdent (name: string) (t: Fable.Type) : Fable.Ident =
        {
            Name = "field_" + name
            Type = t
            IsMutable = false
            IsThisArgument = false
            IsCompilerGenerated = true
            Range = None
            IsInlineIfLambda = false
        }

    let set = Dictionary<string, Fable.Ident>()
    /// the field of the self reference, when the constructor fills it with the object
    let mutable selfField: (string * Fable.Type) option = None

    let rec usesThis (e: Fable.Expr) =
        match e with
        | Fable.Value(Fable.ThisValue _, _) -> true
        | _ -> getSubExpressions e |> List.exists usesThis

    let rec fieldsOf (e: Fable.Expr) : Fable.Expr =
        match e with
        // (the object read through its self reference before it is made: .NET's error)
        | Fable.Get(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet _, refT, _), Fable.FieldGet ci, t, r) when
            ci.Name = "contents" && isSelfRefType owner refT
            ->
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "FailInit"
                        Path =
                            Replacements.DotnetPrefix
                            + "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(),
                t,
                r
            )
        | Fable.Get(Fable.Value(Fable.ThisValue _, _), Fable.FieldGet info, t, _) when set.ContainsKey info.Name ->
            Fable.IdentExpr set[info.Name]
        | _ ->
            match e with
            | Fable.Value(Fable.ThisValue _, r) ->
                raise (ZigError("the Zig target does not support using `this` in a constructor yet", r))
            | _ -> e |> AST.visit fieldsOf

    let rec build (stmts: Fable.Expr list) : Fable.Expr =
        match stmts with
        | [] ->
            let values =
                fieldNames
                |> List.map (fun f ->
                    match set.TryGetValue f, defaults f with
                    | (true, id), _ -> Fable.IdentExpr id
                    // (`[<DefaultValue>] val mutable`: the default of its type)
                    | _, Some d -> d
                    | _ ->
                        raise (
                            ZigError(
                                $"the Zig target needs every field of a class to be given a value in its constructor (`%s{f}`)",
                                None
                            )
                        )
                )

            match selfField with
            | None -> finish values
            | Some(name, refT) ->
                // the object, then its self reference filled with it
                let made = finish values

                match made.Type with
                // (a class in a hierarchy: its constructor gives the chain of fields, and where the
                // object is made of it, the self reference is filled; see the constructor call)
                | Fable.DeclaredType(e, _) when e.FullName.EndsWith("$chain", System.StringComparison.Ordinal) -> made
                | _ ->

                    let obj = AST.makeTypedIdent made.Type "made"

                    let optT =
                        match refT with
                        | Fable.DeclaredType(_, [ o ]) -> o
                        | _ -> raise (ZigError("internal: a self reference", None))

                    let fieldInfo: Fable.FieldInfo =
                        {
                            Name = name
                            FieldType = Some refT
                            IsMutable = true
                            MaybeCalculated = false
                            Tags = []
                        }

                    let cell =
                        Fable.Get(Fable.IdentExpr obj, Fable.GetKind.FieldGet fieldInfo, refT, None)

                    Fable.Let(
                        obj,
                        made,
                        Fable.Sequential
                            [
                                Fable.Set(
                                    cell,
                                    Fable.FieldSet "contents",
                                    optT,
                                    Fable.Value(Fable.NewOption(Some(Fable.IdentExpr obj), made.Type, false), None),
                                    None
                                )
                                Fable.IdentExpr obj
                            ]
                    )
        | stmt :: rest ->
            match stmt with
            | Fable.Sequential xs -> build (xs @ rest)
            | Fable.Value(Fable.UnitConstant, _) -> build rest
            // (the constructor of System.Object)
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) when
                imp.Selector = ".ctor" && imp.Path.EndsWith "System.Object"
                ->
                build rest
            // (`type C() as this`: the self reference starts empty)
            | Fable.Set(Fable.Value(Fable.ThisValue owner, _), Fable.FieldSet name, t, _, _) when isSelfRefType owner t ->
                let kept = selfRefType t

                let empty =
                    match kept with
                    | Fable.DeclaredType(refEntRef, [ Fable.Option(c, _) as optT ]) ->
                        Fable.Value(
                            Fable.NewRecord([ Fable.Value(Fable.NewOption(None, c, false), None) ], refEntRef, [ optT ]),
                            None
                        )
                    | _ -> raise (ZigError("internal: a self reference", None))

                let id = fieldIdent name kept
                set[name] <- id
                Fable.Let(id, empty, build rest)
            // (and is filled with the object once it is made: see `finish`)
            | Fable.Set(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet fi, refT, _),
                        Fable.FieldSet "contents",
                        _,
                        Fable.Value(Fable.ThisValue _, _),
                        _) when isSelfRefType owner refT ->
                selfField <- Some(fi.Name, selfRefType refT)
                build rest
            | Fable.Set(Fable.Value(Fable.ThisValue _, _), Fable.FieldSet name, t, value, _) ->
                let id = fieldIdent name t
                let value = fieldsOf value
                set[name] <- id
                Fable.Let(id, value, build rest)
            | Fable.Let(id, value, body) -> Fable.Let(id, fieldsOf value, build (body :: rest))
            | other -> Fable.Sequential [ fieldsOf other; build rest ]

    build [ body ]

let constructorBody
    (classRef: Fable.EntityRef)
    (genArgs: Fable.Type list)
    (fieldNames: string list)
    (defaults: string -> Fable.Expr option)
    (body: Fable.Expr)
    : Fable.Expr
    =
    constructorBodyWith
        fieldNames
        defaults
        (fun values -> Fable.Value(Fable.NewRecord(values, classRef, genArgs), None))
        body

/// Build the self identifier parameter for an object-first constructor of class `o`.
let objSelfIdent (o: ObjInfo) : Fable.Ident =
    let genArgs = o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, []))

    {
        Name = "self_obj"
        Type = Fable.DeclaredType(o.Ref, genArgs)
        IsMutable = false
        IsThisArgument = true
        IsCompilerGenerated = true
        Range = None
        IsInlineIfLambda = false
    }

/// The constructor of an object class (`objAlloc` allocates `selfId` first; the base constructor
/// runs with the same `selfId`, then the fields, `init@`, and `do` statements execute in order
/// directly against the live heap object).
let objConstructorBody
    (o: ObjInfo)
    (selfId: Fable.Ident)
    (defaults: string -> Fable.Expr option)
    (baseCall: Fable.Expr option)
    (body: Fable.Expr)
    : Fable.Expr
    =
    let fields = caseFields (TEnt(o.Part, [])) "" |> List.map fst
    let assigned = HashSet<string>()
    let typedThisAliases = HashSet<string>()

    let rec rewriteCtor (e: Fable.Expr) : Fable.Expr =
        match e with
        // (the constructor of System.Object)
        | Fable.Call(Fable.Import(imp, _, _), _, _, _) when imp.Selector = ".ctor" && imp.Path.EndsWith "System.Object" ->
            Fable.Value(Fable.UnitConstant, None)
        // (`FSharp2Fable` binds `_this: Any = ThisValue Any` around object expressions inside an
        // implicit constructor; give `_this` the class type so member/field lookups recognize it)
        | Fable.Let(id, Fable.Value(Fable.ThisValue _, r), body) when id.Type = Fable.Any ->
            typedThisAliases.Add id.Name |> ignore

            let id =
                { id with
                    Type = selfId.Type
                    IsThisArgument = true
                }

            Fable.Let(id, Fable.IdentExpr { selfId with Range = r }, rewriteCtor body)
        | Fable.IdentExpr id when typedThisAliases.Contains id.Name && id.Type = Fable.Any ->
            Fable.IdentExpr
                { id with
                    Type = selfId.Type
                    IsThisArgument = true
                }
        // (`type C() as this`: the self reference starts empty)
        | Fable.Set(Fable.Value(Fable.ThisValue owner, _), Fable.FieldSet name, t, _, r) when isSelfRefType owner t ->
            assigned.Add name |> ignore
            let kept = selfRefType t

            let empty =
                match kept with
                | Fable.DeclaredType(refEntRef, [ Fable.Option(c, _) as optT ]) ->
                    Fable.Value(
                        Fable.NewRecord([ Fable.Value(Fable.NewOption(None, c, false), None) ], refEntRef, [ optT ]),
                        None
                    )
                | _ -> raise (ZigError("internal: a self reference", r))

            Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet name, kept, empty, r)
        // (and is filled with `Some self_obj` right where F# puts the store)
        | Fable.Set(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet fi, refT, r1),
                    Fable.FieldSet "contents",
                    _,
                    Fable.Value(Fable.ThisValue _, _),
                    r2) when isSelfRefType owner refT ->
            let kept = selfRefType refT

            let optT, itemT =
                match kept with
                | Fable.DeclaredType(_, [ Fable.Option(c, _) as optT ]) -> optT, c
                | _ -> raise (ZigError("internal: a self reference", r2))

            let cell =
                Fable.Get(Fable.IdentExpr selfId, Fable.FieldGet { fi with FieldType = Some kept }, kept, r1)

            Fable.Set(
                cell,
                Fable.FieldSet "contents",
                optT,
                Fable.Value(Fable.NewOption(Some(Fable.IdentExpr selfId), itemT, false), r2),
                r2
            )
        | Fable.Set(Fable.Value(Fable.ThisValue _, _), Fable.FieldSet name, t, value, r) ->
            assigned.Add name |> ignore
            Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet name, t, rewriteCtor value, r)
        | Fable.Value(Fable.ThisValue _, r) -> Fable.IdentExpr { selfId with Range = r }
        | _ -> e |> AST.visit rewriteCtor

    let rewritten = rewriteCtor body

    let missingDefaults =
        fields
        |> List.choose (fun f ->
            if assigned.Contains f then
                None
            else
                match defaults f with
                | Some d -> Some(Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet f, d.Type, d, None))
                | None ->
                    raise (
                        ZigError(
                            $"the Zig target needs every field of a class to be given a value in its constructor (`%s{f}`)",
                            None
                        )
                    )
        )

    let baseStep =
        match o.Parent, baseCall with
        | Some p, Some(Fable.Call(callee, info, retTy, r)) ->
            let pArgs =
                match retTy with
                | Fable.DeclaredType(_, gs) when not gs.IsEmpty -> gs
                | _ -> o.ParentArgs

            let call =
                Fable.Call(
                    callee,
                    { info with
                        ThisArg = Some(Fable.IdentExpr selfId)
                        GenericArgs =
                            if info.GenericArgs.IsEmpty then
                                pArgs
                            else
                                info.GenericArgs
                    },
                    Fable.Unit,
                    r
                )

            [ call ]
        | Some _, _ ->
            raise (
                ZigError(
                    $"the Zig target does not support this call of the base constructor of %s{o.FullName} yet",
                    None
                )
            )
        | None, _ -> []

    Fable.Sequential(
        baseStep
        @ missingDefaults
        @ [ rewritten; Fable.Value(Fable.UnitConstant, None) ]
    )

/// A module-level value, of this file or (`alias.name`) of another.
let globalVar (name: string) (ty: Ty) (isMutable: bool) : Expr =
    EVar
        {
            Id = 0
            Base = name
            Ty = ty
            Kind = VGlobal
            FMutable = isMutable
        }

/// Is the variable used inside a function that is declared in `e`?
let usedInFunction (name: string) (e: Fable.Expr) : bool =
    let rec go (inside: bool) (e: Fable.Expr) : bool =
        match e with
        | Fable.IdentExpr id -> inside && id.Name = name
        | Fable.Lambda(_, body, _)
        | Fable.Delegate(_, body, _, _) -> go true body
        | Fable.ObjectExpr(members, _, _) -> members |> List.exists (fun m -> go true m.Body)
        | _ -> getSubExpressions e |> List.exists (go inside)

    go false e

let hasAddressOfIdent (name: string) (e: Fable.Expr) : bool =
    let rec go e =
        match e with
        | Fable.Operation(Fable.Unary(UnaryAddressOf, Uncast(Fable.IdentExpr id)), _, _, _) when id.Name = name -> true
        | _ -> getSubExpressions e |> List.exists go

    go e

let mutatedIdentsIn (e: Fable.Expr) : HashSet<string> =
    let acc = HashSet<string>()

    let rec go e =
        match e with
        | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, _) ->
            acc.Add id.Name |> ignore
            go value
        | _ -> getSubExpressions e |> List.iter go

    go e
    acc

/// A string that is certainly not null: its length needs no test.
let rec neverNull (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.StringConstant _, _) -> true
    | Fable.TypeCast(x, _) -> neverNull x
    | PrintfCall("PrintFormatToString", _, _)
    | Fable.CurriedApply(PrintfCall("PrintFormatToString", _, _), _, _, _) -> true
    | Fable.Call(Fable.Import(imp, _, _), _, Fable.String, _) ->
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.StringModule"
        || (imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
            && (imp.Selector = "op_Addition" || imp.Selector = "ToString"))
        // (.NET's string methods that give a string never give null)
        || (imp.Path = Replacements.DotnetPrefix + "System.String"
            && (
                match imp.Selector with
                | "Substring"
                | "Trim"
                | "TrimStart"
                | "TrimEnd"
                | "Replace"
                | "ToUpper"
                | "ToLower"
                | "ToUpperInvariant"
                | "ToLowerInvariant"
                | "PadLeft"
                | "PadRight"
                | "Insert"
                | "Remove"
                | "Concat"
                | "Format"
                | "Join"
                | "ToString" -> true
                | _ -> false
            ))
    | Fable.Value(Fable.StringTemplate _, _) -> true
    | _ -> false

/// What a condition tells, from what its leaves tell (`atom`): the variables (immutable) of
/// which something is known where it is true, and where it is false; through `not`, `&&` and
/// `||` (also as F# compiles them: `if a then true else b`, `if a then b else false`)
let rec factsOf (atom: Fable.Expr -> string list * string list) (cond: Fable.Expr) : string list * string list =
    match cond with
    | Fable.Operation(Fable.Unary(UnaryNot, x), _, _, _) ->
        let t, f = factsOf atom x
        f, t
    | Fable.Operation(Fable.Logical(LogicalAnd, a, b), _, _, _)
    | Fable.IfThenElse(a, b, Fable.Value(Fable.BoolConstant false, _), _) ->
        let ta, _ = factsOf atom a
        let tb, _ = factsOf atom b
        ta @ tb, []
    | Fable.Operation(Fable.Logical(LogicalOr, a, b), _, _, _)
    | Fable.IfThenElse(a, Fable.Value(Fable.BoolConstant true, _), b, _) ->
        let _, fa = factsOf atom a
        let _, fb = factsOf atom b
        [], fa @ fb
    | _ -> atom cond

let internal namedImmutable (e: Fable.Expr) =
    match e with
    | Fable.IdentExpr i when not i.IsMutable -> Some i.Name
    | _ -> None

/// What a condition tells of nulls: the variables known not to be null where it is true, and
/// where it is false. `isNull x`, `x = null`, `x <> null`, `String.IsNullOrEmpty x`
let nullFacts (cond: Fable.Expr) : string list * string list =
    let isNullValue (e: Fable.Expr) =
        match e with
        | Fable.Value(Fable.Null _, _) -> true
        | Fable.Call(Fable.Import(imp, _, _), info, _, _) -> imp.Selector = "DefaultOf" && info.Args.IsEmpty
        | _ -> false

    let named = namedImmutable

    factsOf
        (fun cond ->
            match cond with
            | Fable.Call(Fable.Import(imp, _, _), info, _, _) ->
                match imp.Selector, info.Args with
                | ("IsNull" | "IsNullOrEmpty" | "IsNullOrWhiteSpace"), [ x ] -> [], Option.toList (named x)
                | "ReferenceEquals", [ x; n ] when isNullValue n -> [], Option.toList (named x)
                | "ReferenceEquals", [ n; x ] when isNullValue n -> [], Option.toList (named x)
                | ("NonNull" | "NonNullQuickPattern"), [ x ] -> Option.toList (named x), []
                | "op_Equality", [ x; n ] when isNullValue n -> [], Option.toList (named x)
                | "op_Equality", [ n; x ] when isNullValue n -> [], Option.toList (named x)
                | "op_Inequality", [ x; n ] when isNullValue n -> Option.toList (named x), []
                | "op_Inequality", [ n; x ] when isNullValue n -> Option.toList (named x), []
                | _ -> [], []
            | Fable.Operation(Fable.Binary(BinaryEqual, x, n), _, _, _) when isNullValue n ->
                [], Option.toList (named x)
            | Fable.Operation(Fable.Binary(BinaryUnequal, x, n), _, _, _) when isNullValue n ->
                Option.toList (named x), []
            | _ -> [], []
        )
        cond

/// What a condition tells of whole numbers: the variables known to be greater than zero (a
/// divisor that is neither zero nor -1) where it is true, and where it is false. `x > 0`,
/// `x >= 1`, `0 < x`, `x <= 0`, `x < 1`, and of an unsigned `x`, `x <> 0` and `x = 0`
let positiveFacts (cond: Fable.Expr) : string list * string list =
    let constOf (e: Fable.Expr) : int64 option =
        match e with
        | Fable.Value(Fable.NumberConstant(v, _), _) ->
            match v with
            | Fable.NumberValue.Int8 n -> Some(int64 n)
            | Fable.NumberValue.Int16 n -> Some(int64 n)
            | Fable.NumberValue.Int32 n -> Some(int64 n)
            | Fable.NumberValue.Int64 n -> Some n
            | Fable.NumberValue.UInt8 n -> Some(int64 n)
            | Fable.NumberValue.UInt16 n -> Some(int64 n)
            | Fable.NumberValue.UInt32 n -> Some(int64 n)
            | Fable.NumberValue.UInt64 n when n <= uint64 System.Int64.MaxValue -> Some(int64 n)
            | _ -> None
        | _ -> None

    let isUnsigned (t: Fable.Type) =
        match t with
        | Fable.Number((UInt8 | UInt16 | UInt32 | UInt64), _) -> true
        | _ -> false

    let named (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i when not i.IsMutable ->
            match i.Type with
            | Fable.Number((Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64), _) -> Some i.Name
            | _ -> None
        | _ -> None

    let leaf (op: BinaryOperator) (x: Fable.Expr) (c: int64) : string list * string list =
        match named x with
        | None -> [], []
        | Some n ->
            match op with
            | BinaryGreater when c >= 0L -> [ n ], []
            | BinaryGreaterOrEqual when c >= 1L -> [ n ], []
            | BinaryLessOrEqual when c >= 0L -> [], [ n ]
            | BinaryLess when c >= 1L -> [], [ n ]
            | BinaryUnequal when c = 0L && isUnsigned x.Type -> [ n ], []
            | BinaryEqual when c = 0L && isUnsigned x.Type -> [], [ n ]
            | _ -> [], []

    let flip (op: BinaryOperator) =
        match op with
        | BinaryGreater -> BinaryLess
        | BinaryGreaterOrEqual -> BinaryLessOrEqual
        | BinaryLess -> BinaryGreater
        | BinaryLessOrEqual -> BinaryGreaterOrEqual
        | o -> o

    factsOf
        (fun cond ->
            match cond with
            | Fable.Operation(Fable.Binary(op, x, k), _, _, _) ->
                match constOf k, constOf x with
                | Some c, _ -> leaf op x c
                | None, Some c -> leaf (flip op) k c
                | _ -> [], []
            | _ -> [], []
        )
        cond

/// What a condition tells of whole numbers: the variables known to be non-negative (`>= 0`)
/// where it is true, and where it is false.
let nonNegFacts (cond: Fable.Expr) : string list * string list =
    let constOf (e: Fable.Expr) : int64 option =
        match e with
        | Fable.Value(Fable.NumberConstant(v, _), _) ->
            match v with
            | Fable.NumberValue.Int8 n -> Some(int64 n)
            | Fable.NumberValue.Int16 n -> Some(int64 n)
            | Fable.NumberValue.Int32 n -> Some(int64 n)
            | Fable.NumberValue.Int64 n -> Some n
            | Fable.NumberValue.UInt8 n -> Some(int64 n)
            | Fable.NumberValue.UInt16 n -> Some(int64 n)
            | Fable.NumberValue.UInt32 n -> Some(int64 n)
            | Fable.NumberValue.UInt64 n when n <= uint64 System.Int64.MaxValue -> Some(int64 n)
            | _ -> None
        | _ -> None

    let named (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i when not i.IsMutable ->
            match i.Type with
            | Fable.Number((Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64), _) -> Some i.Name
            | _ -> None
        | _ -> None

    let leaf (op: BinaryOperator) (x: Fable.Expr) (c: int64) : string list * string list =
        match named x with
        | None -> [], []
        | Some n ->
            match op with
            | BinaryGreaterOrEqual when c >= 0L -> [ n ], []
            | BinaryGreater when c >= -1L -> [ n ], []
            | BinaryLess when c >= 0L && c <= 0L -> [], [ n ]
            | BinaryLessOrEqual when c >= -1L && c <= -1L -> [], [ n ]
            | _ -> [], []

    let flip (op: BinaryOperator) =
        match op with
        | BinaryGreater -> BinaryLess
        | BinaryGreaterOrEqual -> BinaryLessOrEqual
        | BinaryLess -> BinaryGreater
        | BinaryLessOrEqual -> BinaryGreaterOrEqual
        | o -> o

    factsOf
        (fun cond ->
            match cond with
            | Fable.Operation(Fable.Binary(op, x, k), _, _, _) ->
                match constOf k, constOf x with
                | Some c, _ -> leaf op x c
                | None, Some c -> leaf (flip op) k c
                | _ -> [], []
            | _ -> [], []
        )
        cond

/// Does this always raise (`raise`, `failwith`, `nullArg`, `invalidArg`, `invalidOp`)?
let rec alwaysRaises (e: Fable.Expr) : bool =
    match e with
    | Fable.Extended(Fable.Throw _, _) -> true
    | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
        imp.Path.EndsWith("Microsoft.FSharp.Core.Operators", System.StringComparison.Ordinal)
        && (
            match imp.Selector with
            | "Raise"
            | "FailWith"
            | "InvalidArg"
            | "InvalidOp"
            | "NullArg" -> true
            | _ -> false
        )
    | Fable.Sequential es -> not es.IsEmpty && alwaysRaises (List.last es)
    | Fable.Let(_, _, body) -> alwaysRaises body
    | Fable.IfThenElse(_, a, b, _) -> alwaysRaises a && alwaysRaises b
    | Fable.TypeCast(x, _) -> alwaysRaises x
    | _ -> false

/// What a statement leaves known for what follows it (by `facts`): a guard whose other branch
/// always raises (`if isNull s then nullArg "s"`, `if n <= 0 then invalidArg ...`)
let factsAfter (facts: Fable.Expr -> string list * string list) (stmt: Fable.Expr) : string list =
    match stmt with
    | Fable.IfThenElse(guard, thenExpr, elseExpr, _) ->
        let whenTrue, whenFalse = facts guard

        (if alwaysRaises thenExpr then
             whenFalse
         else
             [])
        @ (if alwaysRaises elseExpr then
               whenTrue
           else
               [])
    | _ -> []

/// `f ()` with these names in `set` (what is known of them) while it runs
let withFacts (set: HashSet<string>) (names: string list) (f: unit -> 'a) : 'a =
    let added = names |> List.filter (fun n -> set.Add n)

    try
        f ()
    finally
        for n in added do
            set.Remove n |> ignore

/// `f ()` with these variables known not to be null, and these known positive
let withKnown (ctx: Ctx) (nonNull: string list) (positive: string list) (f: unit -> 'a) : 'a =
    withFacts ctx.NonNull nonNull (fun () -> withFacts ctx.Positive positive f)

/// `f ()` with these variables known non-null, positive, and non-negative
let withKnownFacts
    (ctx: Ctx)
    (nonNull: string list)
    (positive: string list)
    (nonNeg: string list)
    (f: unit -> 'a)
    : 'a
    =
    withFacts ctx.NonNull nonNull (fun () -> withFacts ctx.Positive positive (fun () -> withFacts ctx.NonNeg nonNeg f))

let clearIdentFacts (ctx: Ctx) (name: string) : unit =
    ctx.NonNull.Remove name |> ignore
    ctx.Positive.Remove name |> ignore
    ctx.NonNeg.Remove name |> ignore
    ctx.BoundedBelowMax.Remove name |> ignore
    ctx.Lengths.Remove name |> ignore

    let depKeys =
        ctx.Lengths
        |> Seq.choose (fun kv ->
            if fst kv.Value = name then
                Some kv.Key
            else
                None
        )
        |> List.ofSeq

    for k in depKeys do
        ctx.Lengths.Remove k |> ignore

    ctx.ConstLen.Remove name |> ignore
    ctx.KnownTypes.Remove name |> ignore

    ctx.InBounds.RemoveWhere(fun k ->
        k.StartsWith(name + "|", System.StringComparison.Ordinal)
        || k.EndsWith("|" + name, System.StringComparison.Ordinal)
    )
    |> ignore

let withScopedIdent (ctx: Ctx) (id: Fable.Ident) (f: unit -> 'a) : 'a =
    let name = id.Name

    let savedVar =
        match ctx.Vars.TryGetValue name with
        | true, v -> Some v
        | _ -> None

    let savedBoxed = ctx.Boxed.Contains name
    let savedNonNull = ctx.NonNull.Contains name
    let savedPositive = ctx.Positive.Contains name
    let savedNonNeg = ctx.NonNeg.Contains name
    let savedBounded = ctx.BoundedBelowMax.Contains name

    let savedLenKey =
        match ctx.Lengths.TryGetValue name with
        | true, v -> Some v
        | _ -> None

    let savedLenVals =
        ctx.Lengths
        |> Seq.choose (fun kv ->
            if fst kv.Value = name then
                Some(kv.Key, kv.Value)
            else
                None
        )
        |> List.ofSeq

    let savedConstLen =
        match ctx.ConstLen.TryGetValue name with
        | true, n -> Some n
        | _ -> None

    let savedKnownType =
        match ctx.KnownTypes.TryGetValue name with
        | true, t -> Some t
        | _ -> None

    let savedBounds =
        ctx.InBounds
        |> Seq.filter (fun k ->
            k.StartsWith(name + "|", System.StringComparison.Ordinal)
            || k.EndsWith("|" + name, System.StringComparison.Ordinal)
        )
        |> List.ofSeq

    ctx.Vars.Remove name |> ignore
    ctx.Boxed.Remove name |> ignore
    clearIdentFacts ctx name

    try
        f ()
    finally
        ctx.Vars.Remove name |> ignore
        ctx.Boxed.Remove name |> ignore
        clearIdentFacts ctx name

        match savedVar with
        | Some v -> ctx.Vars[name] <- v
        | None -> ()

        if savedBoxed then
            ctx.Boxed.Add name |> ignore

        if savedNonNull then
            ctx.NonNull.Add name |> ignore

        if savedPositive then
            ctx.Positive.Add name |> ignore

        if savedNonNeg then
            ctx.NonNeg.Add name |> ignore

        if savedBounded then
            ctx.BoundedBelowMax.Add name |> ignore

        match savedLenKey with
        | Some v -> ctx.Lengths[name] <- v
        | None -> ()

        for (k, v) in savedLenVals do
            ctx.Lengths[k] <- v

        match savedConstLen with
        | Some n -> ctx.ConstLen[name] <- n
        | None -> ()

        match savedKnownType with
        | Some t -> ctx.KnownTypes[name] <- t
        | None -> ()

        for k in savedBounds do
            ctx.InBounds.Add k |> ignore

let tryLengthTarget (ctx: Ctx) (e: Fable.Expr) : (string * Fable.Type) option =
    let ofArgs (info: Fable.CallInfo) =
        match info.ThisArg, info.Args with
        | Some(Fable.IdentExpr c), []
        | None, [ Fable.IdentExpr c ] when not c.IsMutable -> Some(c.Name, c.Type)
        | _ -> None

    match e with
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when imp.Selector = "get_Length" || imp.Selector = "Length" ->
        ofArgs info
    | Fable.IdentExpr n when not n.IsMutable ->
        match ctx.Lengths.TryGetValue n.Name with
        | true, (cName, cTy) when ctx.Vars.ContainsKey cName -> Some(cName, cTy)
        | _ -> None
    | _ -> None

let tryConstArrayLen (e: Fable.Expr) : int option =
    match e with
    | Fable.Value(Fable.NewArray(Fable.ArrayValues vs, _, _), _) -> Some vs.Length
    | Fable.Value(Fable.NewArray(Fable.ArrayAlloc(Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _)),
                                 _,
                                 _),
                  _) when k >= 0 -> Some k
    | Fable.Call(Fable.Import(imp, _, _),
                 {
                     ThisArg = None
                     Args = [ Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) ]
                 },
                 _,
                 _) when
        (imp.Selector = "ZeroCreate" || imp.Selector = "Create")
        && imp.Path.EndsWith("ArrayModule", System.StringComparison.Ordinal)
        && k >= 0
        ->
        Some k
    | _ -> None

let isKnownPosExpr (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) -> k > 0
    | Fable.IdentExpr id -> ctx.Positive.Contains id.Name
    | _ -> false

let isKnownNonNegExpr (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) -> k >= 0
    | Fable.IdentExpr id -> ctx.NonNeg.Contains id.Name || ctx.Positive.Contains id.Name
    | _ when (tryLengthTarget ctx e).IsSome -> true
    | Fable.Operation(Fable.Binary(BinaryPlus,
                                   Fable.IdentExpr v,
                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _)),
                      _,
                      _,
                      _)
    | Fable.Operation(Fable.Binary(BinaryPlus,
                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _),
                                   Fable.IdentExpr v),
                      _,
                      _,
                      _) when ctx.BoundedBelowMax.Contains v.Name -> true
    | _ -> false

let isArrayIndexInBounds (ctx: Ctx) (a: Fable.Expr) (i: Fable.Expr) : bool =
    match a, i with
    | Fable.IdentExpr ai, Fable.IdentExpr ii -> ctx.InBounds.Contains(ai.Name + "|" + ii.Name)
    | Fable.IdentExpr ai, Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) when k >= 0 ->
        match ctx.ConstLen.TryGetValue ai.Name with
        | true, len -> k < len
        | _ -> false
    | _ -> false

/// The type a `Type` value stands for, where it is known here: `typeof<T>`, `typedefof<T>`, a
/// `MakeGenericType` of known types, a variable bound to one (what an ahead-of-time compiler can
/// see, as .NET's NativeAOT does)
let rec staticTypeOf (ctx: Ctx) (e: Fable.Expr) : Fable.Type option =
    match e with
    | Fable.IdentExpr i when not i.IsMutable ->
        match ctx.KnownTypes.TryGetValue i.Name with
        | true, t -> Some t
        | _ -> None
    | Fable.Value(Fable.TypeInfo(t, _), _) -> Some t
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "TypeOf" || imp.Selector = "TypeDefOf") && info.Args.IsEmpty
        ->
        List.tryHead info.GenericArgs
    | Fable.Call(Fable.Import(imp, _, _), ({ ThisArg = Some def } as info), _, _) when imp.Selector = "MakeGenericType" ->
        let typeArgs =
            match info.Args with
            | [ Fable.Value(Fable.NewArray(Fable.ArrayValues ts, _, _), _) ] -> ts
            | ts -> ts

        match staticTypeOf ctx def with
        | Some(Fable.DeclaredType(ent, gs)) when gs.Length = typeArgs.Length ->
            let known = typeArgs |> List.map (staticTypeOf ctx)

            if known |> List.forall Option.isSome then
                Some(Fable.DeclaredType(ent, known |> List.map Option.get))
            else
                None
        | _ -> None
    | Fable.TypeCast(x, _) -> staticTypeOf ctx x
    | _ -> None

/// `neverNull`, or a variable bound to such a string and never assigned (`Ctx.NonNull`)
let neverNullIn (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.IdentExpr i -> ctx.NonNull.Contains i.Name
    | _ -> neverNull e

/// Has this type a default value here (what .NET's is: zero, false, null of a string, None)?
let rec hasDefault (ctx: Ctx) (t: Fable.Type) : bool =
    match t with
    | Fable.Number _
    | Fable.Char
    | Fable.Boolean
    | Fable.String
    | Fable.Unit
    | Fable.Any
    | Fable.MetaType
    | Fable.Option _
    | Fable.Nullable _ -> true
    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> true
    // (a function: one that raises NullReferenceException, see fable_rt.nullOf)
    | Fable.LambdaType _
    | Fable.DelegateType _ -> true
    | Fable.Tuple(ts, _) -> List.forall (hasDefault ctx) ts
    | Fable.DeclaredType(entRef, _) when
        entRef.FullName = "System.Span`1"
        || entRef.FullName = "System.ReadOnlySpan`1"
        || entRef.FullName = "System.DateOnly"
        || entRef.FullName = "System.TimeOnly"
        || entRef.FullName = "System.DateTimeOffset"
        || entRef.FullName = "System.DateTime"
        || entRef.FullName = "System.TimeSpan"
        || entRef.FullName = "System.Guid"
        || entRef.FullName = "System.Uri"
        ->
        true
    | Fable.DeclaredType(entRef, _) when (objInfo ctx None entRef).IsSome -> true
    | Fable.DeclaredType _ when
        isInterfaceType ctx.Com t
        && (
            match mapType ctx None t with
            | TOpt _ -> true
            | _ -> false
        )
        ->
        true
    | Fable.DeclaredType(entRef, genArgs) ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when
            ent.IsFSharpUnion
            && ent.UnionCases.Length = 1
            && ent.UnionCases.Head.UnionCaseFields.IsEmpty
            ->
            true
        | Some ent when
            ent.IsValueType
            && not ent.IsFSharpUnion
            && not ent.IsInterface
            && (
                match entRef.Path with
                | Fable.SourcePath _ -> true
                | _ -> false
            )
            ->
            let sub =
                if ent.GenericParameters.Length = genArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                    |> Map.ofList
                else
                    Map.empty

            ent.FSharpFields
            |> List.filter (fun f -> not f.IsStatic)
            |> List.forall (fun f -> hasDefault ctx (substFableType sub f.FieldType))
        | _ -> isWitnessClass ctx entRef
    | _ -> false

/// Adapt a lowered IR expression between `T` and `T | null` when their Zig types differ
/// (wrapping `T` into `Some` for `?T`, or unwrapping generic `?inner` to nullable `inner`).
let rec coerceTy (ctx: Ctx) (expectedTy: Ty) (expr: Expr) : Expr =
    let actualTy = typeOf expr

    if actualTy = expectedTy then
        expr
    else
        match expr with
        | ERaise(ex, _) -> ERaise(ex, expectedTy)
        | ESeq(s, last) -> ESeq(s, coerceTy ctx expectedTy last)
        | _ ->
            match actualTy, expectedTy with
            | _, TOpt inner when inner = actualTy ->
                bindArgsIn true ctx [ expr ] (fun xs -> ECon(expectedTy, "Some", xs, None))
            | TOpt inner, _ when inner = expectedTy ->
                let nullVal =
                    match expectedTy with
                    | TOpt _ -> Some(ECon(expectedTy, "None", [], None))
                    | TPrim "fable_rt.String" -> Some(ELit("@as(fable_rt.String, null)", expectedTy))
                    | TPrim "fable_rt.reflect.Type" ->
                        ctx.State.UsesRuntime <- true
                        Some(EEmit("fable_rt.reflect.nullType()", [], expectedTy))
                    | TEnt({ Name = "fable_rt.Array" }, _) ->
                        ctx.State.UsesRuntime <- true
                        Some(EEmit("fable_rt.arrayNull($R)", [], expectedTy))
                    | _ -> None

                match nullVal with
                | Some nv ->
                    bindArgs
                        ctx
                        [ expr ]
                        (fun xs ->
                            EIf(ETest(xs.Head, "None", actualTy), nv, EGet(xs.Head, PSome, expectedTy), expectedTy)
                        )
                | None -> expr
            | _ -> expr

/// Unwrap an interface struct option, raising NullReferenceException when null.
let unwrapIface (ctx: Ctx) (x: Expr) : Expr =
    match typeOf x with
    | TOpt innerTy ->
        ctx.State.UsesRuntime <- true
        ERt("fable_rt.nonNullUnwrap($0)", [ x ], innerTy)
    | _ -> x

/// The default value of a class's field the constructor does not set (`[<DefaultValue>] val
/// mutable`), if its type has one
let fieldDefaults (ctx: Ctx) (ent: Fable.Entity) (name: string) : Fable.Expr option =
    ent.FSharpFields
    |> List.tryFind (fun f -> f.Name = name && not f.IsStatic && hasDefault ctx f.FieldType)
    |> Option.map (fun f ->
        // (a function field is kept uncurried: its null is made at that shape, not adapted to it)
        let ty =
            match f.FieldType with
            | Fable.LambdaType _ -> FableTransforms.uncurryType f.FieldType
            | t -> t

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
            Fable.CallInfo.Create(genArgs = [ ty ]),
            ty,
            None
        )
    )

/// The item type of `IEnumerator<T>`.
let enumeratorItem (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(_, [ item ]) -> item
    | _ -> Fable.Any

/// What Fable makes of `for x in s do body` after `let enumerator = s.GetEnumerator()`:
/// `try (while enumerator.MoveNext() do body) finally enumerator.Dispose()`, perhaps followed
/// by more code. The body of the loop, and what follows the loop.
let forInLoop (enumerator: string) (rest: Fable.Expr) : (Fable.Expr * Fable.Expr option) option =
    let isMoveNext (c: Fable.Expr) =
        match c with
        | Fable.Call(Fable.Import(imp, _, _), info, _, _) when imp.Selector = "MoveNext" ->
            match info.ThisArg with
            | Some(Fable.IdentExpr e) -> e.Name = enumerator
            | _ -> false
        | _ -> false

    let rec loopOf (e: Fable.Expr) =
        match e with
        | Fable.WhileLoop(c, body, _) when isMoveNext c -> Some body
        | Fable.TryCatch(body, None, Some _, _) -> loopOf body
        | _ -> None

    match rest with
    | Fable.Sequential(first :: next) when (loopOf first).IsSome ->
        Some(
            (loopOf first).Value,
            (if next.IsEmpty then
                 None
             else
                 Some(Fable.Sequential next))
        )
    | _ -> loopOf rest |> Option.map (fun body -> body, None)

/// A delegate's body that applies an expression to the delegate's own parameters, in order and
/// nothing else, when that expression is a computation (not a variable, a function or an
/// import): the expression, and the body with another in its place
let etaHead (args: Fable.Ident list) (body: Fable.Expr) : (Fable.Expr * (Fable.Expr -> Fable.Expr)) option =
    let names = args |> List.map (fun a -> a.Name)

    let isParams (xs: Fable.Expr list) =
        xs.Length = names.Length
        && List.forall2
            (fun (x: Fable.Expr) n ->
                match x with
                | Fable.IdentExpr i -> i.Name = n
                | _ -> false
            )
            xs
            names

    // (the applications from the outside in, until those peeled give exactly the parameters)
    let rec peel (e: Fable.Expr) (given: Fable.Expr list) : (Fable.Expr * (Fable.Expr -> Fable.Expr)) option =
        if not given.IsEmpty && isParams given then
            Some(e, id)
        elif given.Length >= names.Length then
            None
        else
            match e with
            // (an application of more than the parameters: the arguments before them are applied
            // once, `f x` of `f x a b`)
            | Fable.CurriedApply(f, xs, t, r) when
                (xs @ given).Length > names.Length
                && isParams (List.skip ((xs @ given).Length - names.Length) (xs @ given))
                ->
                let inXs = names.Length - given.Length
                let before = List.take (xs.Length - inXs) xs
                let after = List.skip (xs.Length - inXs) xs

                // (the type of `f` with `before` applied)
                let rec drop (n: int) (ty: Fable.Type) =
                    if n = 0 then
                        ty
                    else
                        match ty with
                        | Fable.LambdaType(_, ret) -> drop (n - 1) ret
                        | other -> other

                let head = Fable.CurriedApply(f, before, drop before.Length f.Type, r)
                Some(head, (fun h -> Fable.CurriedApply(h, after, t, r)))
            | Fable.CurriedApply(f, xs, t, r) ->
                peel f (xs @ given)
                |> Option.map (fun (head, rebuild) -> head, (fun h -> Fable.CurriedApply(rebuild h, xs, t, r)))
            | _ -> None

    match peel body [] with
    | Some(head, rebuild) ->
        let isComputation =
            match head with
            | Fable.IdentExpr _
            | Fable.Import _
            | Fable.Lambda _
            | Fable.Delegate _
            | Fable.Value _ -> false
            | _ -> true

        let rec uses (e: Fable.Expr) =
            match e with
            | Fable.IdentExpr i -> List.contains i.Name names
            | _ -> AST.getSubExpressions e |> List.exists uses

        if isComputation && not (uses head) then
            Some(head, rebuild)
        else
            None
    | None -> None

/// Whether a type still has type parameters in it
let rec hasTypeParams (t: Fable.Type) : bool =
    match t with
    | Fable.GenericParam _ -> true
    | _ -> t.Generics |> List.exists hasTypeParams

/// The names of the type parameters a type mentions
let rec typeParamNames (t: Fable.Type) : string list =
    match t with
    | Fable.GenericParam(name, _, _) -> [ name ]
    | _ -> t.Generics |> List.collect typeParamNames

/// Whether a type is another with obj in some of its places
let rec moreGeneral (t: Fable.Type) (wanted: Fable.Type) : bool =
    match t, wanted with
    | Fable.Any, _ -> true
    | Fable.LambdaType(a, r), Fable.LambdaType(a2, r2) -> moreGeneral a a2 && moreGeneral r r2
    | _ -> t = wanted

/// Propagates an outer `T | null` type into inner `DefaultOf` (`null` literal) expressions.
let rec wrapNullCast (wanted: Fable.Type) (e: Fable.Expr) : Fable.Expr =
    match wanted with
    | Fable.Nullable(inner, false) ->
        match e with
        | Fable.Call(Fable.Import(imp, ct, cr), info, t, r) when
            imp.Selector = "DefaultOf" && unwrapNullness inner = unwrapNullness t
            ->
            Fable.Call(Fable.Import(imp, ct, cr), { info with GenericArgs = [ wanted ] }, wanted, r)
        | Fable.TypeCast(Fable.Call(Fable.Import(imp, ct, cr), info, t, r), _) when
            imp.Selector = "DefaultOf" && unwrapNullness inner = unwrapNullness t
            ->
            Fable.Call(Fable.Import(imp, ct, cr), { info with GenericArgs = [ wanted ] }, wanted, r)
        | Fable.TypeCast(x, _) ->
            let x' = wrapNullCast wanted x

            if x'.Type = wanted then
                x'
            else
                Fable.TypeCast(x', wanted)
        | Fable.IfThenElse(g, a, b, r) ->
            let ifE = Fable.IfThenElse(g, wrapNullCast wanted a, wrapNullCast wanted b, r)

            if ifE.Type = wanted then
                ifE
            else
                Fable.TypeCast(ifE, wanted)
        | Fable.Let(id, v, body) -> Fable.Let(id, v, wrapNullCast wanted body)
        | Fable.Sequential es when not es.IsEmpty ->
            let rev = List.rev es
            Fable.Sequential(List.rev (wrapNullCast wanted rev.Head :: rev.Tail))
        | Fable.DecisionTree(expr, targets) ->
            let targets' =
                targets |> List.map (fun (ids, body) -> ids, wrapNullCast wanted body)

            let dt = Fable.DecisionTree(expr, targets')

            if dt.Type = wanted then
                dt
            else
                Fable.TypeCast(dt, wanted)
        | _ -> e
    | _ -> e

let rec wrapFnNullCast (fnTy: Fable.Type) (fnExpr: Fable.Expr) : Fable.Expr =
    let rec peel (n: int) (t: Fable.Type) =
        match n, t with
        | 0, _ -> Some t
        | n, Fable.LambdaType(_, r) when n > 0 -> peel (n - 1) r
        | _, Fable.DelegateType(_, r) -> Some r
        | _ -> None

    match fnExpr, fnTy with
    | Fable.Lambda(arg, body, name), Fable.LambdaType(_, rest) -> Fable.Lambda(arg, wrapFnNullCast rest body, name)
    | Fable.Delegate(args, body, name, tags), _ ->
        match peel args.Length fnTy with
        | Some ret -> Fable.Delegate(args, wrapNullCast ret body, name, tags)
        | None -> fnExpr
    | _ -> wrapNullCast fnTy fnExpr

/// A value made at a more general type than the variable it is bound to has: F# generalizes
/// `let a = Ok string`, and where Fable puts the value in at its use, its type parameters are obj
/// (`Ok (fun (v: obj) -> string v)`) though the use is at `Result<int -> string, _>`. The value,
/// fitted to the type wanted: a function taking obj where a value of a type is given takes that
/// value and boxes it, as .NET's generic code would see it as that type.
let rec adaptTo (com: Compiler) (wanted: Fable.Type) (e: Fable.Expr) : Fable.Expr =
    if e.Type = wanted then
        e
    else
        match e, wanted with
        // (a function: applied in the body, so it keeps its type there)
        | Fable.Lambda(arg, body, name), Fable.LambdaType((Fable.LambdaType _ as ta), tr) when
            arg.Type <> ta && moreGeneral arg.Type ta
            ->
            let typed = { arg with Type = ta }

            let body =
                body
                |> AST.visitFromInsideOut (fun x ->
                    match x with
                    | Fable.IdentExpr i when i.Name = arg.Name -> Fable.IdentExpr typed
                    | Fable.CurriedApply(Fable.IdentExpr i, args, Fable.Any, r) when i.Name = arg.Name ->
                        let ret =
                            List.fold
                                (fun t _ ->
                                    match t with
                                    | Fable.LambdaType(_, r) -> r
                                    | _ -> t
                                )
                                ta
                                args

                        // (each argument as the parameter's type wants it)
                        let args =
                            List.fold
                                (fun (t, acc) (a: Fable.Expr) ->
                                    match t with
                                    | Fable.LambdaType(p, rest) -> rest, adaptTo com p a :: acc
                                    | _ -> t, a :: acc
                                )
                                (ta, [])
                                args
                            |> snd
                            |> List.rev

                        Fable.TypeCast(Fable.CurriedApply(Fable.IdentExpr typed, args, ret, r), Fable.Any)
                    | _ -> x
                )

            Fable.Lambda(typed, adaptTo com tr body, name)
        | Fable.Lambda(arg, body, name), Fable.LambdaType(ta, tr) when arg.Type = Fable.Any && ta <> Fable.Any ->
            let typed =
                { arg with
                    Name = arg.Name + "_typed"
                    Type = ta
                }

            Fable.Lambda(
                typed,
                Fable.Let(arg, Fable.TypeCast(Fable.IdentExpr typed, Fable.Any), adaptTo com tr body),
                name
            )
        | Fable.Lambda(arg, body, name), Fable.LambdaType(ta, tr) when arg.Type = ta ->
            Fable.Lambda(arg, adaptTo com tr body, name)
        | Fable.Value(Fable.NewUnion(values, tag, ent, genArgs), r), Fable.DeclaredType(ent2, targs) when
            ent.FullName = ent2.FullName && genArgs.Length = targs.Length
            ->
            match com.TryGetEntity ent with
            | Some entity when tag < entity.UnionCases.Length ->
                let subst =
                    List.zip (entity.GenericParameters |> List.map (fun g -> g.Name)) targs
                    |> Map.ofList

                let fields =
                    entity.UnionCases[tag].UnionCaseFields
                    |> List.map (fun f -> substFableType subst f.FieldType)

                if fields.Length = values.Length then
                    Fable.Value(Fable.NewUnion(List.map2 (adaptTo com) fields values, tag, ent, targs), r)
                else
                    e
            | _ -> e
        | Fable.Value(Fable.NewOption(Some v, _, isStruct), r), Fable.Option(item, _) ->
            Fable.Value(Fable.NewOption(Some(adaptTo com item v), item, isStruct), r)
        | Fable.Value(Fable.NewTuple(values, isStruct), r), Fable.Tuple(ts, _) when ts.Length = values.Length ->
            Fable.Value(Fable.NewTuple(List.map2 (adaptTo com) ts values, isStruct), r)
        | _, Fable.Nullable(inner, false) ->
            let e = wrapNullCast wanted e

            if e.Type = wanted then
                e
            else
                let adapted = adaptTo com inner e

                if adapted.Type = wanted then
                    adapted
                else
                    Fable.TypeCast(adapted, wanted)
        // (a value boxed and unboxed again)
        | Fable.TypeCast(inner, Fable.Any), _ when inner.Type = wanted -> inner
        // (an object where a value of a type is wanted: unboxed)
        | _, _ when
            unwrapNullness e.Type = Fable.Any
            && not (hasTypeParams wanted)
            && unwrapNullness wanted <> Fable.Any
            ->
            match wanted with
            | Fable.LambdaType _
            | Fable.DelegateType _ -> e
            | _ -> Fable.TypeCast(e, wanted)
        | _ -> e

/// What the shared QuotationEmitter makes of a quotation, with the plain values it gives where
/// the library takes objects boxed (a value, the items of an array of objects)
let boxQuotationArgs (e: Fable.Expr) : Fable.Expr =
    let asObj (x: Fable.Expr) =
        if x.Type = Fable.Any then
            x
        else
            Fable.TypeCast(x, Fable.Any)

    let rec go (x: Fable.Expr) =
        match x with
        | Fable.Call(Fable.Import(imp, it, ir), info, t, r) when imp.Selector = "mkValue" ->
            let args =
                match info.Args |> List.map go with
                | v :: rest -> asObj v :: rest
                | [] -> []

            Fable.Call(Fable.Import(imp, it, ir), { info with Args = args }, t, r)
        | Fable.Value(Fable.NewArray(Fable.ArrayValues items, Fable.Any, kind), r) ->
            Fable.Value(Fable.NewArray(Fable.ArrayValues(items |> List.map (go >> asObj)), Fable.Any, kind), r)
        | _ -> AST.visit go x

    go e

/// The names an expression reads that it does not bind itself (over-approximated where a decision
/// tree binds them: that only makes a caller more careful)
let rec freeNamesOf (e: Fable.Expr) : Set<string> =
    match e with
    | Fable.IdentExpr i -> Set.singleton i.Name
    | Fable.Lambda(a, b, _) -> (freeNamesOf b).Remove a.Name
    | Fable.Delegate(ps, b, _, _) -> ps |> List.fold (fun (acc: Set<string>) p -> acc.Remove p.Name) (freeNamesOf b)
    | Fable.Let(id, v, b) -> Set.union (freeNamesOf v) ((freeNamesOf b).Remove id.Name)
    | _ ->
        AST.getSubExpressions e
        |> List.fold (fun acc x -> Set.union acc (freeNamesOf x)) Set.empty

/// How many arguments a function value really takes before it gives a function of the rest:
/// its lambdas' parameters, or a known function's (0 when not known)
let rec stageArityOf (ctx: Ctx) (g: Fable.Expr) : int =
    match g with
    | Fable.Lambda(_, (Fable.Lambda _ as inner), _) -> 1 + stageArityOf ctx inner
    | Fable.Lambda _ -> 1
    | Fable.Delegate(ps, _, _, _) -> ps.Length
    // (a variable that holds a function value: what its type takes at once)
    | Fable.IdentExpr i when ctx.Vars.ContainsKey i.Name ->
        match ctx.Vars[i.Name].Ty with
        | TFn(ps, _) -> ps.Length
        | _ -> 0
    | Fable.IdentExpr _ ->
        match tryCallable ctx g with
        | Some c -> c.Arity
        | None -> 0
    | _ -> 0

/// The type of what a function value gives after `k` of its arguments
let rec peelArgs (t: Fable.Type) (k: int) : Fable.Type =
    if k <= 0 then
        t
    else
        match t with
        | Fable.LambdaType(_, ret) -> peelArgs ret (k - 1)
        | Fable.DelegateType(ps, ret) when ps.Length <= k -> peelArgs ret (k - ps.Length)
        | _ -> t

/// Resolve an interface member access/call against a `KIface` vtable struct: returns
/// `(directSlot, getterSlot)` where `directSlot` matches a callable slot (or indexed getter)
/// and `getterSlot` matches a 0-arg `"get_..."` property slot (e.g. a property returning a function).
let resolveIfaceSlot
    (ctx: Ctx)
    (xType: Fable.Type)
    (ifaceStructTy: Ty)
    (infoName: string)
    (argCount: int option)
    : (string * Ty list * Ty) option * (string * Ty) option
    =
    let fields = caseFields ifaceStructTy ""
    // (a mangled interface's member is named in full: `Ns.IFoo.get_Bar`)
    let short = infoName.Substring(infoName.LastIndexOf '.' + 1)

    // (and its overload's hash, `SumZ35CD86D0`)
    let name =
        if fields |> List.exists (fun (f, _) -> f = short || f = "get_" + short) then
            short
        else
            System.Text.RegularExpressions.Regex.Replace(short, "Z?[0-9A-F]{8}$", "")

    // (an overload: the one whose hash Fable gave the name, `get_ItemZ524259A4`)
    let name =
        if fields |> List.exists (fun (f, _) -> f = name || f = "get_" + name) then
            name
        else
            match unwrapNullness xType with
            | Fable.DeclaredType(iref, _) ->
                match ctx.Com.TryGetEntity iref with
                | Some ient ->
                    let genParams = ient.GenericParameters |> List.map (fun g -> g.Name)

                    ient.MembersFunctionsAndValues
                    |> Seq.filter (fun m -> m.IsDispatchSlot && m.CompiledName = name)
                    |> Seq.tryFind (fun m ->
                        let groups = m.CurriedParameterGroups |> List.map (List.map (fun p -> p.Type))

                        short = name + OverloadSuffix.getHash genParams groups
                    )
                    |> Option.map (fun m -> slotKey ient m.CompiledName (paramTypesOf m))
                    |> Option.defaultValue name
                | None -> name
            | _ -> name

    let directSlot =
        fields
        |> List.tryPick (fun (f, fty) ->
            match fty with
            | TSlot(ptys, ret) when
                (f = name
                 || (argCount.IsSome
                     && f = "get_" + name
                     && not (ptys.Length = 1 && isVoid ptys.Head)))
                && (
                    match argCount with
                    | Some n -> ptys.Length = n
                    | None -> true
                )
                ->
                Some(f, ptys, ret)
            | _ -> None
        )

    let getterSlot =
        fields
        |> List.tryPick (fun (f, fty) ->
            match fty with
            | TSlot([ p ], ret) when isVoid p && (f = "get_" + name || f = name) -> Some(f, ret)
            | _ -> None
        )

    directSlot, getterSlot

/// `EqualityComparer<'T>.Default`, as it is read where a member of it is called
let (|IsDefaultEqualityComparer|_|) (e: Fable.Expr) =
    match e with
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        imp.Selector = "get_Default"
        && info.ThisArg.IsNone
        && imp.Path.EndsWith("System.Collections.Generic.EqualityComparer`1", System.StringComparison.Ordinal)
        ->
        Some()
    | Fable.Get(_, Fable.FieldGet fi, Fable.DeclaredType(ent, _), _) when
        fi.Name = "Default"
        && ent.FullName = "System.Collections.Generic.EqualityComparer`1"
        ->
        Some()
    | _ -> None
