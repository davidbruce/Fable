/// .NET's members: arrays, 2D arrays, .NET's mutable collections, lazy, spans, weak references. The lowering (`Lower.dotnetCall`) asks here in the place these
/// cases had among its own.
module Fable.Transforms.Zig.DotnetCollections

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

    // (a call of the library's Array.fs; the strings' functions are not generic)
    let arrayLib (fn: string) (xs: Fable.Expr list) =
        libraryCall
            ctx
            r
            "Array"
            fn
            { info with
                ThisArg = None
                SignatureArgTypes = []
                GenericArgs =
                    if fn.StartsWith("binarySearchStrings", System.StringComparison.Ordinal) then
                        []
                    else
                        // (of the array's items: the non-generic overloads have none)
                        match xs with
                        | a :: _ ->
                            match a.Type with
                            | Fable.Array(item, _) -> [ item ]
                            | _ -> info.GenericArgs
                        | [] -> info.GenericArgs
            }
            xs
            t

    // (`null` given for a comparer, as F# gives it: the default comparer)
    let isNullArg (x: Fable.Expr) =
        match x with
        | Uncast(Fable.Value(Fable.Null _, _)) -> true
        | Uncast(Fable.Call(Fable.Import(imp, _, _), _, _, _)) -> imp.Selector = "DefaultOf"
        | _ -> false

    let isStringArray (x: Fable.Expr) =
        match x.Type with
        | Fable.Array(Fable.String, _) -> true
        | _ -> false

    match entity, name, args with
    // ---- arrays ----
    // `Array.BinarySearch`: the library's Array.fs, by the comparer given or the default one (a
    // culture's for strings)
    | "System.Array", "BinarySearch", (Uncast a :: rest) when
        (match a.Type with
         | Fable.Array _ -> true
         | _ -> false)
        ->
        let strings = isStringArray a

        // (the value of the non-generic overloads is boxed: the value itself)
        let item =
            match a.Type with
            | Fable.Array(item, _) -> item
            | _ -> Fable.Any

        let rest =
            rest
            |> List.map (fun x ->
                match x with
                | Fable.Call(Fable.Import(imp, _, _), boxInfo, _, _) when
                    imp.Selector = "Box" && boxInfo.Args.Length = 1 && boxInfo.Args.Head.Type = item
                    ->
                    boxInfo.Args.Head
                | Unboxed inner when x.Type = Fable.Any && inner.Type = item -> inner
                | _ -> x
            )

        match rest with
        | [ v ]
        | [ v; _ ] when rest.Length = 1 || isNullArg rest.[1] ->
            arrayLib
                (if strings then
                     "binarySearchStringsAll"
                 else
                     "binarySearchAll")
                [ a; v ]
        | [ v; c ] -> arrayLib "binarySearchWithAll" [ a; v; c ]
        | [ i; n; v ]
        | [ i; n; v; _ ] when rest.Length = 3 || isNullArg rest.[3] ->
            arrayLib
                (if strings then
                     "binarySearchStrings"
                 else
                     "binarySearch")
                [ a; i; n; v ]
        | [ i; n; v; c ] -> arrayLib "binarySearchWith" [ a; i; n; v; c ]
        | _ -> fail r "the Zig target does not support this Array.BinarySearch yet"
    // `Seq.cast<'T> xs` of a collection whose items are `'T` already: the collection as a sequence
    // `Seq.cast<'T>` of objects (a `System.Array`, an array of `obj`): each unboxed
    | "Microsoft.FSharp.Collections.SeqModule", "Cast", [ Uncast source ] when
        (match t, source.Type with
         | Fable.DeclaredType(_, [ item ]), Fable.DeclaredType(a, []) ->
             a.FullName = "System.Array" && item <> Fable.Any
         | Fable.DeclaredType(_, [ item ]), Fable.Array(Fable.Any, _) -> item <> Fable.Any
         | _ -> false)
        ->
        let item =
            match t with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Any

        let objSeq =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ Fable.Any ]
            )

        let o = AST.makeTypedIdent Fable.Any "item"

        lw
            ctx
            (Fable.Call(
                Fable.Import(
                    {
                        Selector = "Map"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(
                    args =
                        [
                            Fable.Lambda(o, Fable.TypeCast(Fable.IdentExpr o, item), None)
                            Fable.TypeCast(source, objSeq)
                        ],
                    genArgs = [ Fable.Any; item ]
                ),
                t,
                r
            ))
    | "Microsoft.FSharp.Collections.SeqModule", "Cast", [ Uncast source ] when
        (match t with
         | Fable.DeclaredType(seqRef, [ item ]) when seqRef.FullName = "System.Collections.Generic.IEnumerable`1" ->
             match source.Type with
             | Fable.Array(x, _)
             | Fable.List x -> x = item
             | Fable.DeclaredType(e, [ x ]) when e.FullName = "System.Collections.Generic.IEnumerable`1" -> x = item
             | Fable.DeclaredType(e, []) when e.FullName = "System.Text.RegularExpressions.MatchCollection" ->
                 (match item with
                  | Fable.DeclaredType(i, []) -> i.FullName = "System.Text.RegularExpressions.Match"
                  | _ -> false)
             | Fable.DeclaredType(e, []) when e.FullName = "System.Text.RegularExpressions.GroupCollection" ->
                 (match item with
                  | Fable.DeclaredType(i, []) -> i.FullName = "System.Text.RegularExpressions.Group"
                  | _ -> false)
             | _ -> false
         | _ -> false)
        ->
        lw ctx (Fable.TypeCast(source, t))
    | "Microsoft.FSharp.Collections.ComparisonIdentity", "FromFunction", [ f ] -> arrayLib "comparerOfFunction" [ f ]
    | "Microsoft.FSharp.Collections.ComparisonIdentity", "Structural", [] ->
        arrayLib "structuralComparer" [ Fable.Value(Fable.UnitConstant, None) ]
    // `Comparer<'T>.Default`: F#'s comparison, as an IComparer
    | "System.Collections.Generic.Comparer`1", "get_Default", [] ->
        arrayLib "structuralComparer" [ Fable.Value(Fable.UnitConstant, None) ]
    // ---- two-dimensional arrays: arrays that know their rows and columns ----
    | "Microsoft.FSharp.Collections.Array2DModule", "ZeroCreate", [ rows; cols ] ->
        rt "fable_rt.array2DZero($R, $0, $1)" [ rows; cols ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Create", [ rows; cols; x ] ->
        rt "fable_rt.array2DCreate($R, $0, $1, $2)" [ rows; cols; x ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Initialize", [ rows; cols; f ] ->
        rt "fable_rt.array2DInit($R, $0, $1, $2)" [ rows; cols; f ] (mapType ctx r t)
    | ("Microsoft.FSharp.Collections.Array2DModule" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Get" | "GetArray2D"),
      [ a; i; j ] -> rt "fable_rt.array2DGet($0, $1, $2)" [ a; i; j ] (mapType ctx r t)
    | ("Microsoft.FSharp.Collections.Array2DModule" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Set" | "SetArray2D"),
      [ a; i; j; v ] -> rt "fable_rt.array2DSet($0, $1, $2, $3)" [ a; i; j; v ] tVoid
    | "Microsoft.FSharp.Collections.Array2DModule", ("Length1" | "Length2"), [ a ] ->
        pure'
            $"""fable_rt.array2DLength($0, %s{if name = "Length1" then
                                                  "0"
                                              else
                                                  "1"})"""
            [ a ]
            tI32
    | "Microsoft.FSharp.Collections.Array2DModule", ("Base1" | "Base2"), [ a ] -> ESeq(lwStmt ctx a, ELit("0", tI32))
    | "System.Array", "GetLength", [ a; d ] -> rt "fable_rt.arrayGetLength($0, $1)" [ a; d ] tI32
    // `Array.Resize(&a, n)`: the variable is given a new array
    | "System.Array", "Resize", [ place; n ] ->
        match tryAddress (lw ctx place) with
        | Some p -> bindArgs ctx [ p; lw ctx n ] (fun xs -> ERt("fable_rt.arrayResize($0, $1)", xs, tVoid))
        | None -> fail r "the Zig target cannot take the address of this array yet"
    | "Microsoft.FSharp.Collections.Array2DModule", ("Copy" | "Rebase"), [ a ] ->
        pure' "fable_rt.array2DCopy($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "CopyTo", [ src; si; sj; dst; ti; tj; n1; n2 ] ->
        rt "fable_rt.array2DBlit($0, $1, $2, $3, $4, $5, $6, $7)" [ src; si; sj; dst; ti; tj; n1; n2 ] tVoid
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetArraySlice2D", [ a; lo1; hi1; lo2; hi2 ] ->
        pure' "fable_rt.array2DSlice($0, $1, $2, $3, $4)" [ a; lo1; hi1; lo2; hi2 ] (mapType ctx r t)
    // `array2D rows`: rows given as a list or an array of lists or arrays
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", "CreateArray2D", [ Uncast rows ] when
        (match rows.Type with
         | Fable.List(Fable.List _ | Fable.Array _)
         | Fable.Array((Fable.List _ | Fable.Array _), _) -> true
         | _ -> false)
        ->
        rt "fable_rt.array2DOfRows($R, $0)" [ rows ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Map", [ f; a ] ->
        rt "fable_rt.array2DMap($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "MapIndexed", [ f; a ] ->
        rt "fable_rt.array2DMapi($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Iterate", [ f; a ] ->
        rt "fable_rt.array2DIter($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Collections.Array2DModule", "IterateIndexed", [ f; a ] ->
        rt "fable_rt.array2DIteri($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetArray", [ a; i ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Get", [ a; i ] ->
        // (where the item is a function that is applied at once, Fable gives the read the type
        // of the application: the type of the array is the one to go by)
        let itemTy =
            match a.Type with
            | Fable.Array(item, _) -> item
            | _ -> t

        if Fable.Transforms.Zig.LowerHelpers.isArrayIndexInBounds ctx a i then
            pure' "fable_rt.arrayItemAt($0, @as(usize, @intCast($1)))" [ a; i ] (mapType ctx r itemTy)
        else
            rt "fable_rt.arrayGet($0, $1)" [ a; i ] (mapType ctx r itemTy)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "SetArray", [ a; i; x ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Set", [ a; i; x ] ->
        if Fable.Transforms.Zig.LowerHelpers.isArrayIndexInBounds ctx a i then
            pure' "fable_rt.arraySetAt($0, @as(usize, @intCast($1)), $2)" [ a; i; x ] tVoid
        else
            rt "fable_rt.arraySet($0, $1, $2)" [ a; i; x ] tVoid
    | "System.Array", "get_Length", [ a ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Length", [ a ] -> pure' "fable_rt.arrayLen($0)" [ a ] tI32
    | "Microsoft.FSharp.Collections.ArrayModule", "IsEmpty", [ a ] -> pure' "(fable_rt.arrayLen($0) == 0)" [ a ] tBool
    | "Microsoft.FSharp.Collections.ArrayModule", "Empty", [] -> pure' "fable_rt.arrayOf($R, .{})" [] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetArraySlice", [ a; lo; hi ] ->
        pure' "fable_rt.arraySlice($0, $1, $2)" [ a; lo; hi ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "ZeroCreate", [ n ] ->
        rt "fable_rt.arrayZero($R, $0)" [ n ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Create", [ n; x ] ->
        rt "fable_rt.arrayCreate($R, $0, $1)" [ n; x ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Initialize", [ n; f ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayInit($R, $0, $1)" args' (mapType ctx r t))
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayInit($R, $0, $1)" [ n; f ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", "Copy", [ a ] ->
        pure' "fable_rt.arrayCopy($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Append", [ a; b ] ->
        pure' "fable_rt.arrayAppend($0, $1)" [ a; b ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Reverse", [ a ] ->
        pure' "fable_rt.arrayRev($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "GetSubArray", [ a; start; n ] ->
        rt "fable_rt.arraySub($0, $1, $2)" [ a; start; n ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Fill", [ a; start; n; x ] ->
        rt "fable_rt.arrayFill($0, $1, $2, $3)" [ a; start; n; x ] tVoid
    | "Microsoft.FSharp.Collections.ArrayModule", "OfList", [ xs ] ->
        pure' "fable_rt.arrayOfList($R, $0)" [ xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "ToList", [ a ] ->
        pure' "fable_rt.arrayToList($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Contains", [ x; a ] ->
        pure' "fable_rt.arrayContains(@as(fable_rt.ItemOf(@TypeOf($1)), $0), $1)" [ x; a ] tBool
    // `Array.Parallel`: on threads (the runtime's parallelFor)
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "Map", [ f; a ] ->
        rt "fable_rt.arrayParallelMap($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "MapIndexed", [ f; a ] ->
        rt "fable_rt.arrayParallelMapi($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "Initialize", [ n; f ] ->
        rt "fable_rt.arrayParallelInit($R, $0, $1)" [ n; f ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "Iterate", [ f; a ] ->
        rt "fable_rt.arrayParallelIter($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Collections.ArrayModule", "Map", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayMap($R, $0, $1)" args' (mapType ctx r t))
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayMap($R, $0, $1)" [ f; a ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", "MapIndexed", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayMapi($R, $0, $1)" args' (mapType ctx r t))
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayMapi($R, $0, $1)" [ f; a ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", "Iterate", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayIter($0, $1)" args' tVoid)
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayIter($0, $1)" [ f; a ] tVoid)
    | "Microsoft.FSharp.Collections.ArrayModule", "IterateIndexed", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayIteri($0, $1)" args' tVoid)
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayIteri($0, $1)" [ f; a ] tVoid)
    | "Microsoft.FSharp.Collections.ArrayModule", "Fold", [ f; state; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayFold($0, @as($R, $1), $2)" args' (mapType ctx r t))
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayFold($0, @as($R, $1), $2)" [ f; state; a ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", ("Filter" | "Where"), [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayFilter($0, $1)" args' (mapType ctx r t))
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayFilter($0, $1)" [ f; a ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", "Exists", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayExists($0, $1)" args' tBool)
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayExists($0, $1)" [ f; a ] tBool)
    | "Microsoft.FSharp.Collections.ArrayModule", "ForAll", [ f; a ] ->
        Fable.Transforms.Zig.Lower.trySpecArrayHof
            ctx
            r
            name
            args
            t
            (fun args' -> rt "fable_rt.arrayForall($0, $1)" args' tBool)
        |> Option.defaultWith (fun () -> rt "fable_rt.arrayForall($0, $1)" [ f; a ] tBool)

    // ---- .NET's mutable collections ----
    | "System.Collections.Generic.List`1", ".ctor", ([] | [ _ ]) when
        (match args with
         | [ (Uncast inner as x) ] -> (listItem inner.Type).IsSome || isInt x
         | _ -> true)
        ->
        let ty = mapType ctx r t

        match args with
        | [ Uncast x ] when (listItem x.Type).IsSome -> pure' "fable_rt.raOfList($R, $0)" [ x ] ty
        | [ n ] -> bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.raNew($R)" [] ty)
        | _ -> pure' "fable_rt.raNew($R)" [] ty
    // (from any other sequence)
    | "System.Collections.Generic.List`1", ".ctor", [ items ] when not (isInt items) ->
        libraryCall ctx r "ResizeArray" "ofSeq" info args t
    | "System.Collections.Generic.List`1", _, r0 :: rest ->
        match name, rest with
        | "Add", [ x ] -> pure' "fable_rt.raAdd($0, $1)" [ r0; x ] tVoid
        | "AddRange", [ Uncast xs ] when (listItem xs.Type).IsSome ->
            pure' "fable_rt.raAddList($0, $1)" [ r0; xs ] tVoid
        | "get_Item", [ i ] -> rt "fable_rt.raGet($0, $1)" [ r0; i ] (mapType ctx r t)
        | "set_Item", [ i; x ] -> rt "fable_rt.raSet($0, $1, $2)" [ r0; i; x ] tVoid
        | "get_Count", [] -> pure' "fable_rt.raCount($0)" [ r0 ] tI32
        | "Insert", [ i; x ] -> rt "fable_rt.raInsert($0, $1, $2)" [ r0; i; x ] tVoid
        | "RemoveAt", [ i ] -> rt "fable_rt.raRemoveAt($0, $1)" [ r0; i ] tVoid
        | "Remove", [ x ] -> pure' "fable_rt.raRemove($0, $1)" [ r0; x ] tBool
        | "Contains", [ x ] -> pure' "fable_rt.raContains($0, $1)" [ r0; x ] tBool
        | "IndexOf", [ x ] -> pure' "fable_rt.raIndexOf($0, $1)" [ r0; x ] tI32
        | "Clear", [] -> pure' "fable_rt.raClear($0)" [ r0 ] tVoid
        | "Reverse", [] -> pure' "fable_rt.raReverse($0)" [ r0 ] tVoid
        | "Sort", [] -> pure' "fable_rt.raSort($0)" [ r0 ] tVoid
        | "ToArray", [] -> pure' "fable_rt.raToArray($0)" [ r0 ] (mapType ctx r t)
        // (`Find` gives `default(T)` when nothing matches: the library's `tryFind`, and the
        // default where the type has one)
        | ("Find" | "FindLast"), [ _ ] ->
            if not (hasDefault ctx t) then
                fail
                    r
                    "the Zig target does not support ResizeArray.%s of items whose default is null on .NET; use a function of the List or Seq module"
                    name

            let found =
                libraryCall ctx r "ResizeArray" ("try" + name) info args (Fable.Option(t, false))

            bindArgs ctx [ found ] (fun xs -> EEmit("fable_rt.orDefault($R, $0)", xs, mapType ctx r t))
        | "IndexOf", [ _; _ ] -> libraryCall ctx r "ResizeArray" "indexOfFrom" info args t
        | "IndexOf", [ _; _; _ ] -> libraryCall ctx r "ResizeArray" "indexOfRange" info args t
        | "BinarySearch", [ _ ] -> libraryCall ctx r "ResizeArray" "binarySearch" info args t
        // (with a comparer or a range: Array.BinarySearch over the items, which takes the same
        // arguments after the array)
        | "BinarySearch", _ ->
            let item =
                match r0.Type with
                | Fable.Array(item, _)
                | Fable.DeclaredType(_, [ item ]) -> item
                | _ -> Fable.Any

            let items =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "ToArray"
                            Path = Replacements.DotnetPrefix + "System.Collections.Generic.List`1"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(thisArg = r0),
                    Fable.Array(item, Fable.MutableArray),
                    r
                )

            dotnetCall
                ctx
                r
                "System.Array"
                "BinarySearch"
                { info with
                    ThisArg = None
                    Args = items :: rest
                }
                t
        | ("FindAll" | "FindIndex" | "FindLastIndex" | "Exists" | "TrueForAll" | "ForEach" | "RemoveAll" | "RemoveRange" | "GetRange" | "InsertRange" | "ConvertAll"),
          _
        | "AddRange", [ _ ] ->
            let fn = name.Substring(0, 1).ToLowerInvariant() + name.Substring(1)
            libraryCall ctx r "ResizeArray" fn info args t
        | _ -> fail r "the Zig target does not support ResizeArray.%s yet" name
    // (F#'s `dict` and `readOnlyDict`: dictionaries that cannot be changed)
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("CreateDictionary" | "CreateReadOnlyDictionary"), [ pairs ] ->
        let ofSeq (seqIr: Expr) =
            let itemTy = itemOf seqIr

            bindArgs
                ctx
                [ seqIr ]
                (fun xs ->
                    bindArgs
                        ctx
                        [
                            ECall(
                                libraryTarget ctx "Seq" "toList",
                                [ itemTy ],
                                xs,
                                TEnt(listEnt ctx.State, [ itemTy ])
                            )
                        ]
                        (fun ls -> EEmit("fable_rt.dictOfList($R, $0, true)", ls, mapType ctx r t))
                )

        match forInSource ctx pairs with
        | Some(listIr, "list") ->
            bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.dictOfList($R, $0, true)", xs, mapType ctx r t))
        | Some(seqIr, "seq") -> ofSeq seqIr
        // (an array, or anything else that is a sequence of pairs: the sequence of it)
        | _ ->
            match t with
            | Fable.DeclaredType(_, [ k; v ]) ->
                Fable.TypeCast(
                    pairs,
                    Fable.DeclaredType(
                        {
                            FullName = "System.Collections.Generic.IEnumerable`1"
                            Path = Fable.CoreAssemblyName "System.Runtime"
                        },
                        [ Fable.Tuple([ k; v ], false) ]
                    )
                )
                |> lw ctx
                |> ofSeq
            | _ -> fail r "the Zig target does not support dict of this kind of sequence yet"
    // `Dictionary(other)`: a copy of another dictionary or of a map
    | "System.Collections.Generic.Dictionary`2", ".ctor", [ Uncast source ] when
        (match source.Type with
         | Fable.DeclaredType(ent, _) -> isDictionaryName ent.FullName || ent.FullName = mapName
         | _ -> false)
        ->
        match forInSource ctx source with
        | Some(listIr, "list") ->
            bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.dictOfList($R, $0, false)", xs, mapType ctx r t))
        | _ -> fail r "the Zig target cannot copy this into a Dictionary yet"
    // (a map seen as `IDictionary` or `ICollection` is read-only: .NET's NotSupportedException)
    | ("System.Collections.Generic.IDictionary`2" | "System.Collections.Generic.ICollection`1"),
      ("Add" | "Remove" | "set_Item" | "Clear"),
      Uncast m :: _ when
        (match m.Type with
         | Fable.DeclaredType(ent, _) ->
             ent.FullName = mapName
             // (an `ICollection` that is a list here: a map's entries, keys or values)
             || (ent.FullName = "System.Collections.Generic.ICollection`1"
                 && entity = "System.Collections.Generic.ICollection`1")
         | _ -> false)
        ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx (args |> List.map (lw ctx)) (fun _ -> ERt("fable_rt.mapNotMutable($R)", [], mapType ctx r t))
    | ("System.Collections.Generic.IDictionary`2" | "System.Collections.Generic.IReadOnlyDictionary`2"), _, _ ->
        dotnetCall ctx r "System.Collections.Generic.Dictionary`2" name info t
    // (what a dictionary is as a collection of its entries)
    | ("System.Collections.Generic.ICollection`1" | "System.Collections.Generic.IReadOnlyCollection`1"),
      ("get_Count" | "Clear"),
      [ d ] when
        (match d.Type with
         | Fable.DeclaredType(ent, _) -> isDictionaryName ent.FullName
         | _ -> false)
        ->
        if name = "Clear" then
            rt "fable_rt.htClear($0)" [ d ] tVoid
        else
            pure' "fable_rt.htCount($0)" [ d ] tI32
    // (an `IList<'T>` is an array here)
    | ("System.Collections.Generic.ICollection`1" | "System.Collections.Generic.IList`1"), "get_Count", [ Uncast xs ] when
        (match xs.Type with
         | Fable.Array _ -> true
         | Fable.DeclaredType(e, _) -> e.FullName = "System.Collections.Generic.IList`1"
         | _ -> false)
        ->
        pure' "fable_rt.arrayLen($0)" [ xs ] tI32
    // (a `ReadOnlyCollection<'T>` is an array here too)
    | "System.Collections.ObjectModel.ReadOnlyCollection`1", "get_Count", [ xs ] ->
        pure' "fable_rt.arrayLen($0)" [ xs ] tI32
    | ("System.Collections.Generic.IList`1" | "System.Collections.ObjectModel.ReadOnlyCollection`1"),
      "get_Item",
      [ xs; i ] -> rt "fable_rt.arrayGet($0, $1)" [ xs; i ] (mapType ctx r t)
    | "System.Collections.Generic.IList`1", "set_Item", [ xs; i; x ] ->
        rt "fable_rt.arraySet($0, $1, $2)" [ xs; i; x ] tVoid
    | ("System.Collections.Generic.Dictionary`2.KeyCollection" | "System.Collections.Generic.Dictionary`2.ValueCollection" | "System.Collections.Generic.ICollection`1"),
      "get_Count",
      [ xs ] -> pure' "fable_rt.listCount($0)" [ xs ] tI32
    | ("System.Collections.Generic.Dictionary`2" | "System.Collections.Generic.HashSet`1"), ".ctor", [] ->
        pure' "fable_rt.htNew($R)" [] (mapType ctx r t)
    // (with an IEqualityComparer, after a capacity or not: its Equals and GetHashCode hash and
    // compare the keys)
    | ("System.Collections.Generic.Dictionary`2" | "System.Collections.Generic.HashSet`1"),
      ".ctor",
      ([ cmp ] | [ _; cmp ]) when
        (args.Length = 1 || isInt args.Head)
        && (let comparerName = "System.Collections.Generic.IEqualityComparer`1"

            match cmp.Type with
            | Fable.DeclaredType(e, _) when e.FullName = comparerName -> true
            | other -> implements ctx.Com other comparerName = Some true)
        ->
        let key =
            match t with
            | Fable.DeclaredType(_, k :: _) -> k
            | _ -> Fable.Any

        let iface =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEqualityComparer`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ key ]
            )

        let cmp =
            match cmp.Type with
            | Fable.DeclaredType(e, _) when e.FullName = "System.Collections.Generic.IEqualityComparer`1" -> cmp
            | _ -> Fable.TypeCast(cmp, iface)

        pure' "fable_rt.htNewWith($R, $0)" [ cmp ] (mapType ctx r t)
    | "System.Collections.Generic.HashSet`1", ".ctor", [ Uncast xs ] when (listItem xs.Type).IsSome ->
        pure' "fable_rt.setOfList($R, $0)" [ xs ] (mapType ctx r t)
    // (a capacity: nothing to do here)
    | "System.Collections.Generic.HashSet`1", ".ctor", [ n ] when isInt n ->
        bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.htNew($R)" [] (mapType ctx r t))
    | "System.Collections.Generic.HashSet`1", ".ctor", [ _ ] -> libraryCall ctx r "HashSet" "ofSeq" info args t
    // (items and an IEqualityComparer: the library's HashSet.ofSeqWith)
    | "System.Collections.Generic.HashSet`1", ".ctor", [ xs; cmp ] when not (isInt xs) ->
        let key =
            match t with
            | Fable.DeclaredType(_, k :: _) -> k
            | _ -> Fable.Any

        let iface =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEqualityComparer`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ key ]
            )

        let cmp =
            match cmp.Type with
            | Fable.DeclaredType(e, _) when e.FullName = "System.Collections.Generic.IEqualityComparer`1" -> cmp
            | _ -> Fable.TypeCast(cmp, iface)

        libraryCall ctx r "HashSet" "ofSeqWith" { info with GenericArgs = [ key ] } [ xs; cmp ] t
    // `m.TryGetValue(key, &value)` of an F# map: its tryFind, and the variable set when found
    | "Microsoft.FSharp.Collections.FSharpMap`2",
      "TryGetValue",
      [ m; k; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
        ctx.Vars.ContainsKey out.Name
        ->
        let outVar = ctx.Vars[out.Name]
        let tmp = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)

        let found =
            libraryCall
                ctx
                r
                "Map"
                "memberTryFind"
                { info with
                    ThisArg = None
                    Args = [ m; k ]
                    GenericArgs =
                        (match m.Type with
                         | Fable.DeclaredType(_, [ kt; vt ]) -> [ kt; vt ]
                         | _ -> [ k.Type; out.Type ])
                    SignatureArgTypes = []
                    MemberRef = None
                }
                [ m; k ]
                (Fable.Option(out.Type, false))

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
    | "System.Collections.Generic.Dictionary`2", _, d :: rest ->
        match name, rest with
        | "Add", [ k; v ] -> rt "fable_rt.dictAdd($0, $1, $2)" [ d; k; v ] tVoid
        | "set_Item", [ k; v ] -> rt "fable_rt.dictSet($0, $1, $2)" [ d; k; v ] tVoid
        | "get_Item", [ k ] -> rt "fable_rt.dictGet($0, $1)" [ d; k ] (mapType ctx r t)
        | "ContainsKey", [ k ] -> pure' "fable_rt.dictContainsKey($0, $1)" [ d; k ] tBool
        | "ContainsValue", [ v ] -> pure' "fable_rt.dictContainsValue($0, $1)" [ d; v ] tBool
        | "Remove", [ k ] -> rt "fable_rt.htRemove($0, $1)" [ d; k ] tBool
        | "get_Count", [] -> pure' "fable_rt.htCount($0)" [ d ] tI32
        | "Clear", [] -> rt "fable_rt.htClear($0)" [ d ] tVoid
        | "get_Keys", [] -> pure' "fable_rt.dictKeys($0)" [ d ] (mapType ctx r t)
        | "get_Values", [] -> pure' "fable_rt.dictValues($0)" [ d ] (mapType ctx r t)
        | "TryGetValue", [ k; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]
            let tmp = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                [ lw ctx d; lw ctx k ]
                (fun xs ->
                    ELet(
                        tmp,
                        EEmit("fable_rt.dictTryGet($0, $1)", xs, TOpt outVar.Ty),
                        EIf(
                            EPrim("not", [ ETest(EVar tmp, "None", TOpt outVar.Ty) ], tBool),
                            ESeq(EAssign(outVar, EGet(EVar tmp, PSome, outVar.Ty)), ELit("true", tBool)),
                            ELit("false", tBool),
                            tBool
                        )
                    )
                )
        | _ -> fail r "the Zig target does not support Dictionary.%s yet" name
    | "System.Collections.Generic.HashSet`1", _, h :: rest ->
        match name, rest with
        | "Add", [ x ] -> pure' "fable_rt.setAdd($0, $1)" [ h; x ] tBool
        | "Contains", [ x ] -> pure' "fable_rt.dictContainsKey($0, $1)" [ h; x ] tBool
        | "Remove", [ x ] -> rt "fable_rt.htRemove($0, $1)" [ h; x ] tBool
        | "get_Count", [] -> pure' "fable_rt.htCount($0)" [ h ] tI32
        | "Clear", [] -> rt "fable_rt.htClear($0)" [ h ] tVoid
        | "UnionWith", [ Uncast xs ] when (listItem xs.Type).IsSome ->
            pure' "fable_rt.setUnionList($0, $1)" [ h; xs ] tVoid
        | "CopyTo", [ _ ] ->
            libraryCall
                ctx
                r
                "HashSet"
                "copyTo"
                { info with SignatureArgTypes = [] }
                (args
                 @ [
                     Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 0, Fable.NumberInfo.Empty), None)
                 ])
                t
        | "CopyTo", [ _; _; _ ] -> libraryCall ctx r "HashSet" "copyToCount" info args t
        | ("UnionWith" | "IntersectWith" | "ExceptWith" | "SymmetricExceptWith" | "Overlaps" | "SetEquals" | "IsSubsetOf" | "IsSupersetOf" | "IsProperSubsetOf" | "IsProperSupersetOf" | "CopyTo"),
          _ ->
            let fn = name.Substring(0, 1).ToLowerInvariant() + name.Substring(1)
            libraryCall ctx r "HashSet" fn info args t
        | _ -> fail r "the Zig target does not support HashSet.%s yet" name

    // ---- lazy ----
    // (`Lazy<T>(fun () -> ...)`: as `lazy`)
    | "System.Lazy`1", ".ctor", [ f ]
    | "Microsoft.FSharp.Control.LazyExtensions", "Create", [ f ] ->
        pure' "fable_rt.lazyNew($R, $0)" [ f ] (mapType ctx r t)
    | "Microsoft.FSharp.Control.LazyExtensions", "CreateFromValue", [ v ] ->
        pure' "fable_rt.lazyOf($R, $0)" [ v ] (mapType ctx r t)
    | ("Microsoft.FSharp.Control.LazyExtensions" | "System.Lazy`1"), ("Force" | "get_Value"), l :: _ ->
        rt "fable_rt.lazyForce($0)" [ l ] (mapType ctx r t)
    | "System.Lazy`1", "get_IsValueCreated", [ l ] -> pure' "fable_rt.lazyIsCreated($0)" [ l ] tBool

    // ---- native pointers: `stackalloc` (memory of the function, see fable_rt.StackAlloc) ----
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", "StackAllocate", [ n ] ->
        let item = mapType ctx r info.GenericArgs.Head
        rt $"fable_stack.alloc(%s{zigType item}, $0)" [ n ] (TPrim("[*]" + zigType item))
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ToVoidPtrInlined" | "ToVoidPtr"), [ p ] ->
        pure' "@as(*anyopaque, @ptrCast($0))" [ p ] (TPrim "*anyopaque")
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("OfVoidPtrInlined" | "OfVoidPtr"), [ p ] ->
        pure' "@as($R, @ptrCast(@alignCast($0)))" [ p ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("GetPointerInlined" | "Get"), [ p; i ] ->
        pure' "$0[@intCast($1)]" [ p; i ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("SetPointerInlined" | "Set"), [ p; i; x ] ->
        pure' "$0[@intCast($1)] = $2" [ p; i; x ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ReadPointerInlined" | "Read"), [ p ] ->
        pure' "$0[0]" [ p ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("WritePointerInlined" | "Write"), [ p; x ] ->
        pure' "$0[0] = $1" [ p; x ] tVoid
    | ("System.Span`1" | "System.ReadOnlySpan`1"), ".ctor", [ p; n ] when
        (match unwrapNullness p.Type with
         | Fable.DeclaredType(e, _) ->
             e.FullName = "voidptr"
             || e.FullName.StartsWith("nativeptr", System.StringComparison.Ordinal)
         | Fable.Any -> true
         | _ -> false)
        ->
        rt "fable_rt.spanOfPtr($R, $0, $1)" [ p; n ] (mapType ctx r t)

    // ---- spans: slices of the arrays or string units they view ----
    | ("System.Span`1" | "System.ReadOnlySpan`1"), (".ctor" | "get_Empty"), [] ->
        pure' "fable_rt.spanEmpty($R)" [] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), ".ctor", [ a ] when
        (match a.Type with
         | Fable.Array _ -> true
         | _ -> false)
        ->
        pure' "$0.items" [ a ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), ".ctor", [ a; start; n ] ->
        rt "fable_rt.spanSlice($0.items, $1, $2)" [ a; start; n ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "get_Length", [ sp ] ->
        pure' "@as(i32, @intCast($0.len))" [ sp ] tI32
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "get_IsEmpty", [ sp ] -> pure' "($0.len == 0)" [ sp ] tBool
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "get_Item", [ sp; i ] ->
        // (the item's place: a byref, which is read here, or kept by a byref variable)
        let item =
            match mapType ctx r t with
            | TPtr(item, _) -> item
            | other -> other

        let ptr =
            rt "fable_rt.spanRef($0, $1)" [ sp; i ] (TPtr(item, entity = "System.ReadOnlySpan`1"))

        bindArgs ctx [ ptr ] (fun xs -> EDeref(xs.Head, item))
    | "System.Span`1", "set_Item", [ sp; i; x ] -> rt "fable_rt.spanSet($0, $1, $2)" [ sp; i; x ] tVoid
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "Slice", [ sp; start ] ->
        rt "fable_rt.spanSlice($0, $1, null)" [ sp; start ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "Slice", [ sp; start; n ] ->
        rt "fable_rt.spanSlice($0, $1, $2)" [ sp; start; n ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "op_Implicit", [ x ] ->
        match x.Type with
        | Fable.Array _ -> pure' "$0.items" [ x ] (mapType ctx r t)
        | Fable.String -> pure' "fable_rt.unitsOf($0)" [ x ] (mapType ctx r t)
        | _ -> lw ctx x
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "ToArray", [ sp ] ->
        pure' "fable_rt.spanToArray($R, $0)" [ sp ] (mapType ctx r t)
    | "System.Span`1", "Fill", [ sp; x ] -> pure' "fable_rt.spanFill($0, $1)" [ sp; x ] tVoid
    | "System.Span`1", "Clear", [ sp ] -> rt "fable_rt.spanClear($0)" [ sp ] tVoid
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "CopyTo", [ sp; dst ] ->
        rt "fable_rt.spanCopyTo($0, $1)" [ sp; dst ] tVoid
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "TryCopyTo", [ sp; dst ] ->
        pure' "fable_rt.spanTryCopyTo($0, $1)" [ sp; dst ] tBool
    | "System.MemoryExtensions", "AsSpan", [ x ] ->
        match x.Type with
        | Fable.Array _ -> pure' "$0.items" [ x ] (mapType ctx r t)
        | Fable.String -> pure' "fable_rt.unitsOf($0)" [ x ] (mapType ctx r t)
        | _ -> fail r "the Zig target only supports AsSpan on arrays and strings"
    | "System.MemoryExtensions", "AsSpan", [ x; start ] ->
        match x.Type with
        | Fable.Array _ -> rt "fable_rt.spanSlice($0.items, $1, null)" [ x; start ] (mapType ctx r t)
        | Fable.String -> rt "fable_rt.spanSlice(fable_rt.unitsOf($0), $1, null)" [ x; start ] (mapType ctx r t)
        | _ -> fail r "the Zig target only supports AsSpan on arrays and strings"
    | "System.MemoryExtensions", "AsSpan", [ x; start; n ] ->
        match x.Type with
        | Fable.Array _ -> rt "fable_rt.spanSlice($0.items, $1, $2)" [ x; start; n ] (mapType ctx r t)
        | Fable.String -> rt "fable_rt.spanSlice(fable_rt.unitsOf($0), $1, $2)" [ x; start; n ] (mapType ctx r t)
        | _ -> fail r "the Zig target only supports AsSpan on arrays and strings"
    | "System.MemoryExtensions", "Fill", [ sp; x ] -> pure' "fable_rt.spanFill($0, $1)" [ sp; x ] tVoid
    | "System.MemoryExtensions", "Reverse", [ sp ] -> pure' "fable_rt.spanReverse($0)" [ sp ] tVoid
    | "System.MemoryExtensions", "SequenceEqual", [ a; b ] -> pure' "fable_rt.eql($0, $1)" [ a; b ] tBool

    // ---- weak references ----
    | "System.WeakReference`1", ".ctor", [ target ] -> rt "fable_rt.weakNew($R, $0)" [ target ] (mapType ctx r t)
    | "System.WeakReference`1", "SetTarget", [ w; target ] -> rt "fable_rt.weakSet($0, $1)" [ w; target ] tVoid
    | "System.WeakReference`1",
      "TryGetTarget",
      [ w; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
        ctx.Vars.ContainsKey out.Name
        ->
        let outVar = ctx.Vars[out.Name]
        let tmp = ctx.State.NewVar("target", TOpt outVar.Ty, VLocal, false)
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lw ctx w ]
            (fun xs ->
                ELet(
                    tmp,
                    EEmit("fable_rt.weakTryGet($0)", xs, TOpt outVar.Ty),
                    EIf(
                        EPrim("not", [ ETest(EVar tmp, "None", TOpt outVar.Ty) ], tBool),
                        ESeq(EAssign(outVar, EGet(EVar tmp, PSome, outVar.Ty)), ELit("true", tBool)),
                        ELit("false", tBool),
                        tBool
                    )
                )
            )
    // `GC.Collect()`: free every cycle that is dead now
    | "System.GC", "Collect", [] -> pure' "_ = fable_rt.collect()" [] tVoid

    | _ -> Unchecked.defaultof<Expr>
