/// From F# types to Zig types: mapType, the entities and the objects of classes; part of Fable2Zig.Lower.fs
module Fable.Transforms.Zig.LowerTypes

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext

/// Unwrap F# 9 nullness (`T | null` = `Fable.Nullable(t, false)`), leaving `System.Nullable<T>` untouched.
let rec unwrapNullness (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.Nullable(inner, false) -> unwrapNullness inner
    | _ -> t

let rec mapType (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty =
    match t with
    | Fable.Unit -> tVoid
    // (an interface of a Zig type, `[<Erase; Import("Counter", "./counter.zig")>]`: that type,
    // which the program does not count; `*Counter` is a pointer to one)
    | Fable.DeclaredType(ent, _) when (erasedZigType ctx ent).IsSome -> TPrim (erasedZigType ctx ent).Value
    // (a class deriving from `Dictionary` or `HashSet` with members only: the collection)
    | Fable.DeclaredType _ when (collectionBase ctx.Com t).IsSome -> mapType ctx r (collectionBase ctx.Com t).Value
    | Fable.Boolean -> tBool
    | Fable.Char -> TPrim "u16"
    | Fable.Number(kind, _) ->
        match kind with
        | Int8 -> TPrim "i8"
        | UInt8 -> TPrim "u8"
        | Int16 -> TPrim "i16"
        // (Zig's u16 is a char here: a uint16 is a type of its own of the same size)
        | UInt16 -> TPrim "c_ushort"
        | Int32 -> TPrim "i32"
        | UInt32 -> TPrim "u32"
        | Int64 -> TPrim "i64"
        | UInt64 -> TPrim "u64"
        | Int128 -> TPrim "i128"
        | UInt128 -> TPrim "u128"
        | NativeInt -> TPrim "isize"
        | UNativeInt -> TPrim "usize"
        | Float16 -> TPrim "f16"
        | Float32 -> TPrim "f32"
        | Float64 -> TPrim "f64"
        | BigInt -> TPrim "fable_rt.BigInt"
        | Decimal -> TPrim "fable_rt.NetDecimal"
    | Fable.String -> tStr
    // (a unit argument stays, as `void`: a function value has one shape whatever its type
    // parameters stand for)
    | Fable.LambdaType(arg, ret) -> TFn([ mapType ctx r arg ], mapType ctx r ret)
    // (a delegate of no parameters, `delegate of unit -> int`: as a function value here, it takes
    // the unit)
    | Fable.DelegateType([], ret) -> TFn([ tVoid ], mapType ctx r ret)
    | Fable.DelegateType(args, ret) -> TFn(args |> List.map (mapType ctx r), mapType ctx r ret)
    | Fable.Tuple(ts, _) -> TTuple(ts |> List.map (mapType ctx r))
    // (`Tuple<'T>`, which F# does not write as a tuple)
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Tuple`1" || ent.FullName = "System.ValueTuple`1" ->
        TTuple [ mapType ctx r t ]
    // (`None` and `[]` whose item type F# leaves as `obj` are of `obj` here too)
    | Fable.Option(t, _) -> TOpt(mapType ctx r t)
    // (`Nullable<T>`: an option; `T | null`: the same Zig type when already nullable here)
    | Fable.Nullable(t, false) ->
        let inner = mapType ctx r t

        match t with
        | Fable.String
        | Fable.Any
        | Fable.MetaType -> inner
        | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> inner
        | _ when (objOfType ctx r t).IsSome -> inner
        | Fable.DeclaredType(ent, _) when
            (match ctx.Com.TryGetEntity ent with
             | Some e -> e.IsInterface
             | None -> false)
            && (
                match inner with
                | TOpt _ -> true
                | _ -> false
            )
            ->
            inner
        | _ -> TOpt inner
    | Fable.Nullable(t, true) -> TOpt(mapType ctx r t)
    // (reflection: the runtime's fable_reflect.zig)
    | Fable.MetaType -> TPrim "fable_rt.reflect.Type"
    // (quotations and their variables: objects of the library's Quotation.fs; a method by its name)
    | Fable.DeclaredType(ent, _) when
        ent.FullName = "Microsoft.FSharp.Quotations.FSharpExpr"
        || ent.FullName = "Microsoft.FSharp.Quotations.FSharpExpr`1"
        || ent.FullName = "Microsoft.FSharp.Quotations.FSharpVar"
        ->
        tAny
    | Fable.DeclaredType(ent, []) when
        ent.FullName = "System.Reflection.MethodInfo"
        || ent.FullName = "System.Reflection.MethodBase"
        ->
        tStr
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Type" -> TPrim "fable_rt.reflect.Type"
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Reflection.PropertyInfo" ->
        TPrim "fable_rt.reflect.Property"
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Reflection.UnionCaseInfo" ->
        TPrim "fable_rt.reflect.UnionCase"
    | Fable.List t -> TEnt(listEnt ctx.State, [ mapType ctx r t ])
    | Fable.Array(t, Fable.ResizeArray) -> TEnt(netEnt ctx.State "ResizeArray", [ mapType ctx r t ])
    | Fable.AnonymousRecordType(names, genArgs, _) ->
        TEnt(anonEnt ctx.State names, genArgs |> List.map (FableTransforms.uncurryType >> mapTypeArg ctx r))
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Lazy`1" -> TEnt(lazyEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.WeakReference`1" ->
        TEnt(netEnt ctx.State "Weak", [ mapType ctx r t ])
    // (`Fable.Core.Zig.Iso<'T>`: fable_rt.Iso, which holds its value as bytes the runtime does
    // not walk)
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "Fable.Core.Zig.Iso`1" ->
        TEnt(netEnt ctx.State "Iso", [ mapType ctx r t ])
    // a byref: a pointer (`inref` to what cannot be assigned)
    | Fable.DeclaredType(ent, [ t; kind ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
        let isIn =
            match kind with
            | Fable.DeclaredType(k, _) -> k.FullName.EndsWith(".In", System.StringComparison.Ordinal)
            | _ -> false

        TPtr(mapType ctx r t, isIn)
    // a native pointer (`NativePtr.stackalloc`): a many-item pointer; `voidptr`: an opaque one
    | Fable.DeclaredType(ent, [ t ]) when
        ent.FullName = "nativeptr`1"
        || ent.FullName = "Microsoft.FSharp.Core.nativeptr`1"
        ->
        TPrim("[*]" + zigType (mapType ctx r t))
    | Fable.DeclaredType(ent, []) when ent.FullName = "voidptr" || ent.FullName = "System.Void*" -> TPrim "*anyopaque"
    // a span: a slice of what it views
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Span`1" || ent.FullName = "System.ReadOnlySpan`1" ->
        TSlice(mapType ctx r t, ent.FullName = "System.ReadOnlySpan`1")
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Text.StringBuilder" ->
        TEnt(netEnt ctx.State "StringBuilder", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Random" -> TEnt(netEnt ctx.State "Random", [])
    | Fable.Array(t, _) -> TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, [ k; v ]) when isDictionaryName ent.FullName ->
        TEnt(netEnt ctx.State "Dictionary", [ mapType ctx r k; mapType ctx r v ])
    // (`d.Keys` and `d.Values`: the list of them)
    | Fable.DeclaredType(ent, [ k; _ ]) when ent.FullName = "System.Collections.Generic.Dictionary`2.KeyCollection" ->
        TEnt(listEnt ctx.State, [ mapType ctx r k ])
    | Fable.DeclaredType(ent, [ _; v ]) when ent.FullName = "System.Collections.Generic.Dictionary`2.ValueCollection" ->
        TEnt(listEnt ctx.State, [ mapType ctx r v ])
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Collections.Generic.HashSet`1" ->
        TEnt(netEnt ctx.State "HashSet", [ mapType ctx r t ])
    | Fable.GenericParam(name = name) when ctx.State.GenAliases.ContainsKey name -> ctx.State.GenAliases[name]
    | Fable.GenericParam(name = name) -> TGen name
    | Fable.DeclaredType(ent, _) when dotnetExceptions.ContainsKey ent.FullName -> tExn
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = refName -> TEnt(refEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, _) when (tryExnEnt ctx r ent).IsSome -> tExn
    // (a class whose only value is null: nothing)
    | Fable.DeclaredType(ent, _) when isWitnessClass ctx ent -> tVoid
    // (an object of a class: null or the object, as on .NET)
    | Fable.DeclaredType(ent, _) when (objInfo ctx r ent).IsSome -> TOpt tObj
    // an async computation: the record of the library's Async.fs; the builder has no state
    // (F#'s `Event<'T>`: the record of the library's Event.fs)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpEvent`1" ->
        TEnt(libRecordEnt ctx "Event" "EventOf_1", [ mapType ctx r item ])
    // (`Event<'Delegate, 'Args>`: of a delegate of the sender and the arguments)
    | Fable.DeclaredType(ent, [ _; args ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpEvent`2" ->
        TEnt(libRecordEnt ctx "Event" "DelegateEventOf_1", [ mapType ctx r args ])
    // (a unit of measure given as a type argument: nothing here; the numbers it marks are
    // plain numbers)
    | Fable.Measure _ -> tVoid
    | Fable.DeclaredType(ent, _) when
        ent.FullName.StartsWith("Microsoft.FSharp.Core.CompilerServices.Measure", System.StringComparison.Ordinal)
        ->
        tVoid
    // (.NET's `Uri`, `Guid`, `TimeSpan`, the dates and times: records of the library)
    | Fable.DeclaredType(ent, []) when libraryValueTypes.ContainsKey ent.FullName ->
        let file, record = libraryValueTypes[ent.FullName]
        TEnt(libRecordEnt ctx file record, [])
    // (.NET's stack and queue: records of the library's Stack.fs and Queue.fs)
    // (.NET's regular expressions: records of the library's Regex.fs)
    | Fable.Regex -> TEnt(libRecordEnt ctx "Regex" "RegexOf", [])
    | Fable.DeclaredType(ent, []) when regexTypes.ContainsKey ent.FullName ->
        TEnt(libRecordEnt ctx "Regex" regexTypes[ent.FullName], [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.IO.DirectoryInfo" ->
        TEnt(libRecordEnt ctx "Path" "DirectoryInfoOf", [])
    // (what `Parallel.For` gives: nothing here)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Tasks.ParallelLoopResult" -> tVoid
    // (a culture or a format provider: nothing, the invariant culture is the only one)
    | Fable.DeclaredType(ent, []) when
        ent.FullName = "System.Globalization.CultureInfo"
        || ent.FullName = "System.IFormatProvider"
        ->
        tVoid
    // (`Comparer<'T>`, as `Comparer<'T>.Default` gives it: the IComparer it is used as)
    // (`EqualityComparer<'T>`: the IEqualityComparer it is used as, `Default` or one of `Create`)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.EqualityComparer`1" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEqualityComparer`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            ))
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Comparer`1" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IComparer`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            ))
    // (.NET's text encodings: the runtime's TextEncoding, UTF-8 or UTF-16)
    | Fable.DeclaredType(ent, []) when
        ent.FullName = "System.Text.Encoding"
        || ent.FullName = "System.Text.UTF8Encoding"
        || ent.FullName = "System.Text.UnicodeEncoding"
        ->
        TPrim "fable_rt.TextEncoding"
    // (a format of printf given as a value: its text and what an interpolated string captured)
    | Fable.DeclaredType(ent, _) when
        ent.FullName = "Microsoft.FSharp.Core.PrintfFormat`4"
        || ent.FullName = "Microsoft.FSharp.Core.PrintfFormat`5"
        // (`FormattableString`: its composite format and its arguments, the same pair)
        || ent.FullName = "System.FormattableString"
        ->
        TTuple [ tStr; mapType ctx r (Fable.Array(Fable.Any, Fable.MutableArray)) ]
    // (`IList<'T>`, as an array is seen through it: the array; `System.Array`: an array of objects)
    | Fable.DeclaredType(ent, [ item ]) when
        ent.FullName = "System.Collections.Generic.IList`1"
        || ent.FullName = "System.Collections.ObjectModel.ReadOnlyCollection`1"
        ->
        mapType ctx r (Fable.Array(item, Fable.MutableArray))
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Array" ->
        mapType ctx r (Fable.Array(Fable.Any, Fable.MutableArray))
    // (`IComparable`, as F# types a key whose type it leaves open (`Map []`): an object, as on
    // .NET, which compares by what it holds)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.IComparable" -> tAny
    // (.NET's threads: the runtime's ThreadOf)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Thread" -> TPrim "fable_rt.ThreadOf"
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Diagnostics.Stopwatch" ->
        TEnt(libRecordEnt ctx "Stopwatch" "StopwatchOf", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Timers.Timer" ->
        TEnt(libRecordEnt ctx "Timer" "TimerOf", [])
    // (the non-generic IEnumerator: an enumerator of objects)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Collections.IEnumerator" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerator`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ Fable.Any ]
            ))
    // (the non-generic IEnumerable: a sequence of objects)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Collections.IEnumerable" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ Fable.Any ]
            ))
    // (`TimeZoneInfo.Local` and `TimeZoneInfo.Utc`, the zones there are here: whether it is local)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.TimeZoneInfo" -> tBool
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Timers.ElapsedEventArgs" ->
        TEnt(libRecordEnt ctx "Timer" "ElapsedEventArgsOf", [])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Stack`1" ->
        TEnt(libRecordEnt ctx "Stack" "StackOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = "System.Runtime.CompilerServices.ConditionalWeakTable`2" ->
        TEnt(libRecordEnt ctx "ConditionalWeakTable" "ConditionalWeakTableOf_2", [ mapType ctx r k; mapType ctx r v ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Core.CompilerServices.ListCollector`1" ->
        TEnt(libRecordEnt ctx "ListCollector" "ListCollectorOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Queue`1" ->
        TEnt(libRecordEnt ctx "Queue" "QueueOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsync`1" ->
        TEnt(libRecordEnt ctx "Async" "AsyncOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsyncBuilder" -> tVoid
    // (.NET's cancellation: records of the library's Async.fs; a registration is what disposes it)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationTokenSource" ->
        TEnt(libRecordEnt ctx "Async" "CancellationSource", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationToken" ->
        TEnt(libRecordEnt ctx "Async" "CancellationTokenOf", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationTokenRegistration" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.IDisposable"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                []
            ))
    // a task and what the builder makes of `task { }`: records of the library's Task.fs; the
    // builder has no state
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.Task`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Tasks.Task" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ tVoid ])
    // (a task's awaiter is the task itself)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Runtime.CompilerServices.TaskAwaiter`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Runtime.CompilerServices.TaskAwaiter" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ tVoid ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpMailboxProcessor`1" ->
        TEnt(libRecordEnt ctx "Async" "MailboxOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsyncReplyChannel`1" ->
        TEnt(libRecordEnt ctx "Async" "ReplyChannelOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.TaskCompletionSource`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskSourceOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = taskCodeName ->
        TEnt(libRecordEnt ctx "Task" "TaskCode_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Control.TaskBuilder" -> tVoid
    // a sequence: the record of the library's Seq.fs
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.IEnumerable`1" ->
        TEnt(seqEnt ctx, [ mapTypeArg ctx r item ])
    // (an entry of a map, as a `for ... in` loop over the map gives it: a pair here)
    | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = "System.Collections.Generic.KeyValuePair`2" ->
        TTuple [ mapType ctx r k; mapType ctx r v ]
    // (what `Map.keys` and `Map.values` give: a list here, which is what they hold, in order)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.ICollection`1" ->
        TEnt(listEnt ctx.State, [ mapType ctx r item ])
    | Fable.DeclaredType(ent, genArgs) when ent.FullName = mapName || ent.FullName = setName ->
        TEnt(treeEnt ctx (ent.FullName = mapName), genArgs |> List.map (mapTypeArg ctx r))
    // (an interface of .NET's, `IDisposable`: a struct of function values as the program's own
    // interfaces are, of the runtime's type for its member names, so that it is one type in
    // every file)
    | Fable.DeclaredType(ent, genArgs) when
        (match ent.Path with
         | Fable.SourcePath _ -> false
         | _ -> true)
        && (
            match ctx.Com.TryGetEntity ent with
            | Some e -> e.IsInterface
            | None -> false
        )
        ->
        let e = ctx.Com.GetEntity ent

        let subst =
            List.zip (e.GenericParameters |> List.map (fun g -> g.Name)) genArgs
            |> Map.ofList

        let members =
            allInterfaceMembers ctx.Com e subst |> List.sortBy (fun (_, n, _, _) -> n)

        TOpt(
            TEnt(
                ifaceAnonEnt ctx.State (members |> List.map (fun (_, n, _, _) -> n) |> Array.ofList),
                // (functions in the signatures as values have them: uncurried)
                members
                |> List.map (fun (_, _, args, ret) ->
                    TSlot(
                        args |> List.map (FableTransforms.uncurryType >> mapType ctx r),
                        mapType ctx r (FableTransforms.uncurryType ret)
                    )
                )
            )
        )
    | Fable.DeclaredType(ent, genArgs) ->
        let ty = TEnt(entOf ctx r ent, genArgs |> List.map (mapTypeArg ctx r))

        match ctx.Com.TryGetEntity ent with
        | Some e when e.IsInterface -> TOpt ty
        | _ -> ty
    | Fable.Any -> tAny

/// A type argument (`obj`, as for the item type of something empty, is `obj` here too).
and mapTypeArg (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty =
    match t with
    | Fable.Any -> tAny
    | _ -> mapType ctx r t

/// The record or union behind an entity reference. Immutable, non-recursive records and
/// unions are plain Zig values: a `struct`, or a `union(enum)` with one payload per case.
/// A union that contains itself is a handle: a `union(enum)` whose cases with fields point to
/// reference-counted cells. (A record that reaches itself only through such unions is still a
/// plain value.)
and entOf (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : Ent =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e -> e
    | _ when entRef.FullName = resultName -> resultEnt ctx.State
    | _ when entRef.FullName.StartsWith("Microsoft.FSharp.Core.FSharpChoice`", System.StringComparison.Ordinal) ->
        choiceEnt ctx.State entRef.FullName
    | _ ->
        let ent =
            match ctx.Com.TryGetEntity entRef with
            | Some e -> e
            | None -> fail r "the Zig target cannot find the type %s" entRef.FullName

        let isStruct =
            ent.IsValueType
            && not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || ent.IsFSharpModule)

        if not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || isStruct) then
            fail r "the Zig target does not support the type %s yet" entRef.FullName

        let recursive = reachesSelf ctx.Com true ent

        // (a record or union compared by reference, `[<ReferenceEquality>]` or `[<NoEquality>]`
        // without an `Equals` of its own: its values are cells, so that each has an identity)
        let byReference =
            (ent.IsFSharpRecord || ent.IsFSharpUnion)
            && not ent.IsValueType
            && (ent.Attributes
                |> Seq.exists (fun a -> a.Entity.FullName = "Microsoft.FSharp.Core.ReferenceEqualityAttribute")
                || ent.Attributes
                   |> Seq.exists (fun a -> a.Entity.FullName = "Microsoft.FSharp.Core.NoEqualityAttribute")
                   && not (
                       ent.MembersFunctionsAndValues
                       |> Seq.exists (fun m ->
                           m.IsOverrideOrExplicitInterfaceImplementation && m.CompiledName = "Equals"
                       )
                   ))

        // A record that can be assigned to (and is not a struct), or that contains itself, is a
        // reference: a pointer to a counted cell.
        let isReference =
            ent.IsFSharpRecord
            && (byReference
                || (recursive && reachesSelf ctx.Com false ent)
                || (not ent.IsValueType
                    && (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                       |> List.exists (fun f -> f.IsMutable)))

        // a name in this file, or `alias.name` for a type another file declares
        let name, isLocal =
            match FSharp2Fable.Util.entityIdent ctx.Com entRef with
            | Fable.IdentExpr id -> id.Name, true
            | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
            | _ -> fail r "the Zig target cannot reference the type %s" entRef.FullName

        let e =
            {
                Name = name
                Ref = entRef
                Kind =
                    if ent.IsInterface then
                        KIface
                    elif isReference then
                        KRefRecord
                    elif not ent.IsFSharpUnion then
                        KRecord
                    elif recursive || byReference then
                        KHeapUnion
                    else
                        KValueUnion
                TypeParams = ent.GenericParameters |> List.map (fun g -> g.Name)
                Cases = []
                MutableFields =
                    if ent.IsFSharpRecord || isStruct then
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.filter (fun f -> f.IsMutable)
                        |> List.map (fun f -> f.Name)
                    else
                        []
                Managed = ent.IsInterface
                Cyclic = false
                ReachesOpaque = ent.IsInterface
                Copyable = true
                IsLocal = isLocal
                Hooks = None
                Overrides = []
            }

        if ent.IsInterface then
            ctx.State.UsesRuntime <- true

        // a resource: `IResource<'T>` (destroyed after its last use, move-only) or
        // `ISharedResource<'T>` (copies share it)
        let resourceKind =
            if ent.IsInterface then
                Seq.empty
            else
                ent.DeclaredInterfaces
            |> Seq.map (fun i -> i.Entity.FullName)
            |> Seq.fold
                (fun acc n ->
                    if n.EndsWith("ISharedResource`1", System.StringComparison.Ordinal) then
                        Some true
                    elif n.EndsWith("IResource`1", System.StringComparison.Ordinal) && acc.IsNone then
                        Some false
                    else
                        acc
                )
                None

        match resourceKind with
        | Some shared ->
            if e.Kind = KHeapUnion || e.Kind = KRefRecord then
                fail
                    r
                    "%s: a record that can be assigned or a type that contains itself is already a counted reference; IResource is for values that stand for something outside the program"
                    entRef.FullName

            let hook (member': string) =
                ent.MembersFunctionsAndValues
                |> Seq.tryFind (fun m ->
                    m.CompiledName.IndexOf("Resource<", System.StringComparison.Ordinal) >= 0
                    && m.CompiledName.EndsWith("." + member', System.StringComparison.Ordinal)
                )
                |> Option.map (fun m -> implName name m.CompiledName)

            let destroy =
                match hook "Destroy" with
                | Some d -> d
                | None -> fail r "%s: a resource needs its static member Destroy" entRef.FullName

            e.Hooks <-
                Some(
                    destroy,
                    if shared then
                        hook "Dup"
                    else
                        None
                )

            e.Copyable <- shared
        | None -> ()

        // the `Equals`, `GetHashCode` and `IComparable.CompareTo` of its own, which `=`, `hash`
        // and `compare` call (F#'s own for a record or a union unless it says otherwise)
        let hasAttr (name: string) =
            ent.Attributes |> Seq.exists (fun a -> a.Entity.FullName = name)

        let ownEquality =
            not (ent.IsFSharpRecord || ent.IsFSharpUnion)
            || hasAttr "Microsoft.FSharp.Core.CustomEqualityAttribute"
            || hasAttr "Microsoft.FSharp.Core.NoEqualityAttribute"

        let ownComparison =
            not (ent.IsFSharpRecord || ent.IsFSharpUnion)
            || hasAttr "Microsoft.FSharp.Core.CustomComparisonAttribute"
            || hasAttr "Microsoft.FSharp.Core.NoComparisonAttribute"

        let declares (compiled: string) =
            ent.MembersFunctionsAndValues
            |> Seq.exists (fun m ->
                m.IsInstance
                && m.IsOverrideOrExplicitInterfaceImplementation
                && m.CompiledName = compiled
            )

        if isLocal && not ent.IsInterface then
            e.Overrides <-
                [
                    if byReference then
                        "fable_reference_equality", ""
                    if declares "ToString" && (ent.IsFSharpRecord || ent.IsFSharpUnion) then
                        "fable_to_string", name + "__ToString"
                    if ownEquality && declares "Equals" then
                        "fable_equals", name + "__Equals"
                    if ownEquality && declares "GetHashCode" then
                        "fable_hash", name + "__GetHashCode"
                    if ownComparison && declares "System.IComparable.CompareTo" then
                        "fable_compare", implName name "System.IComparable.CompareTo"
                ]

            if not e.Overrides.IsEmpty && not ent.GenericParameters.IsEmpty then
                fail
                    r
                    "the Zig target does not support Equals, GetHashCode or CompareTo of a generic type yet (%s)"
                    entRef.FullName

        ctx.State.Ents[entRef.FullName] <- e
        ctx.State.EntDepth <- ctx.State.EntDepth + 1

        try
            e.Cases <-
                if ent.IsInterface then
                    [
                        "",
                        allInterfaceMembers ctx.Com ent Map.empty
                        |> List.map (fun (_, name, args, ret) ->
                            // (functions in the signatures as values have them: uncurried)
                            name,
                            TSlot(
                                args |> List.map (FableTransforms.uncurryType >> mapType ctx r),
                                mapType ctx r (FableTransforms.uncurryType ret)
                            )
                        )
                    ]
                elif ent.IsFSharpUnion then
                    ent.UnionCases
                    |> List.map (fun c ->
                        c.Name,
                        c.UnionCaseFields
                        |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))
                    )
                else
                    [
                        "",
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.map (fun f ->
                            f.Name, mapType ctx r (FableTransforms.uncurryType (fieldTypeIn entRef f))
                        )
                    ]
        with _ ->
            ctx.State.EntDepth <- ctx.State.EntDepth - 1
            ctx.State.Ents.Remove entRef.FullName |> ignore
            reraise ()

        ctx.State.EntDepth <- ctx.State.EntDepth - 1

        if isLocal then
            ctx.State.LocalEnts.Add e

            // (what reflection says of it: .NET's name, and what it is)
            if ent.IsFSharpRecord || ent.IsFSharpUnion then
                ctx.State.NetTypes[e.Name] <-
                    (dotnetTypeName ctx.Com ent,
                     if ent.IsFSharpRecord then
                         "record"
                     else
                         "union")

        // (the types this one refers to are all known once the outermost one is finished)
        if ctx.State.EntDepth = 0 then
            settleManaged ctx.State

        e

/// The F# `exception` declaration behind an entity reference, if it is one. Its values have
/// the type `exn`; the declaration says what fields they have.
/// What is known of a class that takes part in inheritance: one that is abstract, derives from
/// a class, has virtual members, or that a class of the project derives from. (None for every
/// other type.)
and objInfo (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : ObjInfo option =
    match ctx.State.ObjInfos.TryGetValue entRef.FullName with
    | true, o when isNull o -> None
    | true, o -> Some(o :?> ObjInfo)
    | _ ->
        let found =
            match entRef.Path with
            | Fable.SourcePath _ ->
                match ctx.Com.TryGetEntity entRef with
                // (a struct is a value, not an object; a class deriving from System.Exception is
                // an exception)
                | Some ent when
                    isClassEntity ent
                    && not ent.IsValueType
                    && not (isExceptionClass ent)
                    && (collectionBase
                            ctx.Com
                            (Fable.DeclaredType(
                                entRef,
                                ent.GenericParameters
                                |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                            )))
                        .IsNone
                    ->
                    Some ent
                | _ -> None
            | _ -> None

        match found with
        | None ->
            ctx.State.ObjInfos[entRef.FullName] <- null
            None
        | Some ent ->
            let gens = ent.GenericParameters |> List.map (fun g -> g.Name)

            let parentArgs =
                match ent.BaseType with
                | Some bt when bt.Entity.FullName <> "System.Object" -> bt.GenericArgs
                | _ -> []

            let parent =
                match ent.BaseType with
                | Some bt when bt.Entity.FullName <> "System.Object" ->
                    match objInfo ctx r bt.Entity with
                    | Some p -> Some p
                    | None -> fail r "the Zig target does not support deriving from %s yet" bt.Entity.FullName
                | _ -> None

            let name, isLocal =
                match FSharp2Fable.Util.entityIdent ctx.Com entRef with
                | Fable.IdentExpr id -> id.Name, true
                | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
                | _ -> fail r "the Zig target cannot reference the type %s" entRef.FullName

            let synth (suffix: string) : Ent =
                {
                    Name = name + "__" + suffix
                    Ref =
                        {
                            FullName = entRef.FullName + "$" + suffix
                            Path = entRef.Path
                        }
                    Kind = KRecord
                    TypeParams = gens
                    Cases = []
                    MutableFields = []
                    Managed = false
                    Cyclic = false
                    ReachesOpaque = false
                    Copyable = true
                    IsLocal = isLocal
                    Hooks = None
                    Overrides = []
                }

            let part = synth "part"
            let chain = synth "chain"

            // (a property is there as itself and as its accessors: the accessors are the slots)
            let dispatch =
                ent.MembersFunctionsAndValues
                |> Seq.filter (fun m -> m.IsDispatchSlot && not m.IsProperty)
                |> List.ofSeq

            let table =
                if dispatch.IsEmpty then
                    None
                else
                    Some(synth "vt")

            let info =
                {
                    Ref = entRef
                    FullName = entRef.FullName
                    Prefix = name
                    Depth =
                        match parent with
                        | Some p -> p.Depth + 1
                        | None -> 0
                    Parent = parent
                    Part = part
                    Chain = chain
                    Slots = []
                    Table = table
                    IsAbstract = ent.IsAbstractClass
                    IsLocal = isLocal
                    Gens = gens
                    ParentArgs = parentArgs
                }

            // (registered before its fields are mapped: they may mention the class)
            ctx.State.ObjInfos[entRef.FullName] <- box info

            let fields =
                (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType (fieldTypeIn entRef f)))

            part.Cases <- [ "", fields ]
            part.MutableFields <- fields |> List.map fst

            chain.Cases <-
                [
                    "",
                    (match parent with
                     | Some p -> [ "base", TEnt(p.Chain, parentArgs |> List.map (mapTypeArg ctx r)) ]
                     | None -> [])
                    @ [ "own", TEnt(part, gens |> List.map TGen) ]
                ]

            let slots =
                dispatch
                |> List.map (fun m ->
                    let ps =
                        m.CurriedParameterGroups
                        |> List.concat
                        |> List.map (fun p -> mapType ctx r p.Type)

                    let ps =
                        if ps.IsEmpty then
                            [ tVoid ]
                        else
                            ps

                    m.CompiledName, TFn(tObj :: ps, mapType ctx r m.ReturnParameter.Type)
                )

            if (slots |> List.map fst |> List.distinct).Length <> slots.Length then
                fail r "the Zig target does not support overloaded virtual members yet (%s)" entRef.FullName

            match table with
            | Some vt -> vt.Cases <- [ "", slots ]
            | None -> ()

            let info = { info with Slots = slots }
            ctx.State.ObjInfos[entRef.FullName] <- box info

            for e in [ Some part; Some chain; table ] |> List.choose id do
                ctx.State.Ents[e.Ref.FullName] <- e

                if isLocal then
                    ctx.State.LocalEnts.Add e

            if ctx.State.EntDepth = 0 then
                settleManaged ctx.State

            Some info

/// The class of an object, if its type is one that takes part in inheritance.
and objOfType (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : ObjInfo option =
    match unwrapNullness t with
    | Fable.DeclaredType(e, _) -> objInfo ctx r e
    | _ -> None

and tryExnEnt (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : Ent option =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e when e.Kind = KExn -> Some e
    | true, _ -> None
    | _ when
        entRef.FullName <> "System.Exception"
        && dotnetExceptions.ContainsKey entRef.FullName
        ->
        Some(dotnetExnEntIn ctx.State entRef.FullName)
    | _ ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when ent.IsFSharpExceptionDeclaration || isExceptionClass ent ->
            let name, isLocal =
                match FSharp2Fable.Util.entityIdent ctx.Com entRef with
                | Fable.IdentExpr id -> id.Name, true
                | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
                | _ -> fail r "the Zig target cannot reference the exception %s" entRef.FullName

            let e =
                {
                    Name = name
                    Ref = entRef
                    Kind = KExn
                    TypeParams = []
                    Cases = []
                    MutableFields = []
                    Managed = false
                    Cyclic = false
                    ReachesOpaque = false
                    Copyable = true
                    IsLocal = isLocal
                    Hooks = None
                    Overrides = []
                }

            ctx.State.Ents[entRef.FullName] <- e

            try
                let fields =
                    (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                    |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))

                // (a class: its message first, which its base constructor was given)
                e.Cases <-
                    [
                        "",
                        if isExceptionClass ent then
                            ("fable_message", tStr) :: fields
                        else
                            fields
                    ]
            with _ ->
                ctx.State.Ents.Remove entRef.FullName |> ignore
                reraise ()

            if isLocal then
                ctx.State.LocalEnts.Add e

            Some e
        | _ -> None

and importAlias (ctx: Ctx) (path: string) =
    match ctx.State.Imports.TryGetValue path with
    | true, alias -> alias
    | _ ->
        let fileName = System.IO.Path.GetFileNameWithoutExtension(path)

        let baseName =
            "m_"
            + System.Text.RegularExpressions.Regex.Replace(fileName.Replace(".fs", ""), "[^A-Za-z0-9_]", "_")

        let mutable alias = baseName
        let mutable i = 1

        while ctx.State.Imports.ContainsValue alias do
            alias <- $"%s{baseName}_%d{i}"
            i <- i + 1

        ctx.State.Imports[path] <- alias
        alias

/// The alias of a Zig file or package the program imports (`[<Import>]`): `@import` of it, as
/// written (a package: `std`; a file: its path, which the CLI copies under the output)
and userImportAlias (ctx: Ctx) (path: string) =
    match ctx.State.UserImports.TryGetValue path with
    | true, alias -> alias
    | _ ->
        let fileName = System.IO.Path.GetFileNameWithoutExtension(path)

        let baseName =
            "z_"
            + System.Text.RegularExpressions.Regex.Replace(fileName, "[^A-Za-z0-9_]", "_")

        let mutable alias = baseName
        let mutable i = 1

        while ctx.State.UserImports.ContainsValue alias
              || ctx.State.Imports.ContainsValue alias do
            alias <- $"%s{baseName}_%d{i}"
            i <- i + 1

        ctx.State.UserImports[path] <- alias
        alias

/// The Zig type an `[<Erase>]` interface stands for (its `[<Import>]`), if it is one
and erasedZigType (ctx: Ctx) (entRef: Fable.EntityRef) : string option =
    match ctx.Com.TryGetEntity entRef with
    | Some ent when ent.IsInterface ->
        let has (name: string) =
            ent.Attributes |> Seq.tryFind (fun a -> a.Entity.FullName = name)

        match has "Fable.Core.EraseAttribute", has "Fable.Core.ImportAttribute" with
        | Some _, Some imp ->
            match imp.ConstructorArgs with
            | [ :? string as selector; :? string as path ] ->
                let pointer = selector.StartsWith("*", System.StringComparison.Ordinal)

                let info: Fable.ImportInfo =
                    {
                        Selector = selector.TrimStart('*')
                        Path = path
                        Kind = Fable.UserImport false
                    }

                Some(
                    (if pointer then
                         "*"
                     else
                         "")
                    + userImportTarget ctx info
                )
            | _ -> None
        | _ -> None
    | _ -> None

/// What an imported name is in Zig: the alias of its file (`[<ImportAll>]`), or a declaration of
/// it (quoted where it is not a plain identifier)
and userImportTarget (ctx: Ctx) (imp: Fable.ImportInfo) =
    let alias = userImportAlias ctx (userImportPath imp)

    match imp.Selector with
    | "*"
    | "default"
    | "" -> alias
    // (a name, or a Zig expression of the file's declarations: `math.maxInt(i32)`)
    | sel when System.Text.RegularExpressions.Regex.IsMatch(sel, "^[A-Za-z_]") -> alias + "." + sel
    | sel -> alias + ".@\"" + sel + "\""

/// What is imported: the path, without the `c:` that marks a module of C's declarations
and userImportPath (imp: Fable.ImportInfo) =
    if imp.Path.StartsWith("c:", System.StringComparison.Ordinal) then
        imp.Path.Substring 2
    else
        imp.Path

/// A call of an imported Zig function: an Emit of it with its arguments (not those of unit). A C
/// function (`c:`) is given C's values for F#'s, see fable_rt.cCall.
and userImportCall (ctx: Ctx) (imp: Fable.ImportInfo) (info: Fable.CallInfo) (t: Fable.Type) r : Fable.Expr =
    let n =
        (Option.toList info.ThisArg @ info.Args)
        |> List.filter (fun a -> a.Type <> Fable.Unit)
        |> List.length

    let holes = List.init n (fun i -> $"$%d{i}") |> String.concat ", "

    let macro =
        if imp.Path.StartsWith("c:", System.StringComparison.Ordinal) then
            $"fable_rt.cCall($R, %s{userImportTarget ctx imp}, .{{ %s{holes} }})"
        else
            $"%s{userImportTarget ctx imp}(%s{holes})"

    Fable.Emit(
        {
            Macro = macro
            IsStatement = false
            CallInfo = info
        },
        t,
        r
    )

/// F#'s `seq`: the record of the library's Seq.fs, around the function that starts a walk.
and seqEnt (ctx: Ctx) : Ent =
    match ctx.State.Ents.TryGetValue "$seq" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = libraryTarget ctx "Seq" "SeqOf_1"
                Ref =
                    {
                        FullName = "Fable.Library.Zig.Seq.SeqOf`1"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = [ "T" ]
                Cases = [ "", [ "fable_seq", TFn([ tVoid ], TEnt(walkEnt ctx, [ TGen "T" ])) ] ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents["$seq"] <- e
        e

/// A record of the library's (`AsyncOf_1` of Async.fs, `Cont_1`): what a program sees of it
/// is its type; its fields are the library's own business.
and libRecordEnt (ctx: Ctx) (file: string) (name: string) : Ent =
    let key = $"$lib:%s{file}.%s{name}"

    match ctx.State.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        let contTy () =
            TEnt(libRecordEnt ctx "Async" "Cont_1", [ TGen "T" ])

        let fields =
            match name with
            | "AsyncOf_1" -> [ "fable_async", TFn([ contTy () ], tVoid) ]
            | "Cont_1" ->
                [
                    "ok", TFn([ TGen "T" ], tVoid)
                    "fail", TFn([ tExn ], tVoid)
                    "cancel", TFn([ tExn ], tVoid)
                    "token", TEnt(libRecordEnt ctx "Async" "CancellationTokenOf", [])
                    "handOver", TOpt(TEnt(libRecordEnt ctx "Async" "HandOver", []))
                ]
            | "HandOver" -> [ "handedOver", tBool ]
            | "Timer" ->
                [
                    "due", TPrim "i64"
                    "order", tI32
                    "action", TFn([ tVoid ], tVoid)
                    "live", tBool
                ]
            | "CancellationSource" ->
                [
                    "cancelled", tBool
                    "handlers", TEnt(netEnt ctx.State "ResizeArray", [ TOpt(TFn([ tVoid ], tVoid)) ])
                    "disposed", tBool
                    "canCancel", tBool
                ]
            | "CancellationTokenOf" -> [ "source", TEnt(libRecordEnt ctx "Async" "CancellationSource", []) ]
            | "TaskOf_1" ->
                [
                    "fable_task", TOpt(TEnt(resultEnt ctx.State, [ TGen "T"; tExn ]))
                    "fable_iso", TOpt(TEnt(netEnt ctx.State "Iso", [ TEnt(resultEnt ctx.State, [ TGen "T"; tExn ]) ]))
                    "fable_thread", TOpt(TPrim "fable_rt.ThreadOf")
                    "fable_owner", tI32
                ]
            | "TaskSourceOf_1" -> [ "task", TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ TGen "T" ]) ]
            | "ReplyChannelOf_1" -> [ "reply", TFn([ TGen "T" ], tVoid) ]
            // (its body takes the mailbox itself: what a program sees of it is a cell)
            | "MailboxOf_1" ->
                [
                    "queue", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ])
                    "waiting", TOpt(TFn([ TGen "T" ], tVoid))
                    "started", tBool
                    "begun", tBool
                    "running", tBool
                    "turnToken", tI32
                ]
            | "TaskCode_1" -> [ "code", TFn([ tVoid ], TGen "T") ]
            | "StackOf_1" -> [ "items", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ]) ]
            | "QueueOf_1" ->
                [
                    "items", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ])
                    "head", TPrim "i32"
                ]
            | "EventOf_1" ->
                [
                    "handlers", TEnt(netEnt ctx.State "ResizeArray", [ TFn([ tAny; TGen "T" ], tVoid) ])
                ]
            | "DelegateEventOf_1" ->
                [
                    "dhandlers", TEnt(netEnt ctx.State "ResizeArray", [ TFn([ tAny; TGen "T" ], tVoid) ])
                ]
            | "TimeSpanOf" -> [ "ticks", TPrim "i64" ]
            | "DateTimeOf" -> [ "ticks", TPrim "i64"; "kind", TPrim "i32" ]
            | "DateOnlyOf" -> [ "dayNumber", TPrim "i32" ]
            | "DateTimeOffsetOf" -> [ "utcTicks", TPrim "i64"; "offsetMinutes", TPrim "i32" ]
            | "TimeOnlyOf" -> [ "timeTicks", TPrim "i64" ]
            | "StopwatchOf" -> [ "elapsed", TPrim "i64"; "startedAt", TPrim "i64"; "running", tBool ]
            | "ElapsedEventArgsOf" -> [ "signalTime", TEnt(libRecordEnt ctx "DateTime" "DateTimeOf", []) ]
            | "TimerOf" ->
                [
                    "interval", TPrim "f64"
                    "autoReset", tBool
                    "enabled", tBool
                    "elapsed",
                    TEnt(
                        libRecordEnt ctx "Event" "DelegateEventOf_1",
                        [ TEnt(libRecordEnt ctx "Timer" "ElapsedEventArgsOf", []) ]
                    )
                    "generation", tI32
                ]
            | "DirectoryInfoOf" -> [ "fullName", tStr ]
            | "GuidOf" -> [ "a", TPrim "u32"; "b", tI32; "c", tI32; "rest", TPrim "u64" ]
            | "UriOf" ->
                [
                    "original", tStr
                    "isAbsolute", tBool
                    "scheme", tStr
                    "host", tStr
                    "port", tI32
                    "path", tStr
                    "query", tStr
                    "fragment", tStr
                ]
            | _ -> []

        // (records with fields that can be assigned are counted cells, as the library declares them)
        let mutableFields =
            match name with
            | "StackOf_1" -> [ "items" ]
            | "QueueOf_1" -> [ "items"; "head" ]
            | "EventOf_1" -> [ "handlers" ]
            | "DelegateEventOf_1" -> [ "dhandlers" ]
            | "CancellationSource" -> [ "cancelled"; "handlers"; "disposed" ]
            | "HandOver" -> [ "handedOver" ]
            | "Timer" -> [ "live" ]
            | "StopwatchOf" -> [ "elapsed"; "startedAt"; "running" ]
            | "TimerOf" -> [ "interval"; "autoReset"; "enabled"; "generation" ]
            | "TaskOf_1" -> [ "fable_task"; "fable_iso"; "fable_thread" ]
            | "MailboxOf_1" -> [ "waiting"; "started"; "begun"; "running"; "turnToken" ]
            | _ -> []

        let e =
            {
                Name = libraryTarget ctx file name
                Ref =
                    {
                        FullName = $"Fable.Library.Zig.%s{file}.%s{name.Replace('_', '`')}"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind =
                    (if mutableFields.IsEmpty then
                         KRecord
                     else
                         KRefRecord)
                // (`AsyncOf_1` and the others of one type parameter; `UriOf` of none)
                TypeParams =
                    (if name.EndsWith("_1", System.StringComparison.Ordinal) then
                         [ "T" ]
                     else
                         [])
                Cases = [ "", fields ]
                MutableFields = mutableFields
                // (as the library's own declaration has it: a record of numbers only, as `GuidOf`,
                // is a plain value)
                Managed =
                    not mutableFields.IsEmpty
                    || fields.IsEmpty
                    || fields |> List.exists (snd >> isManaged)
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents[key] <- e
        e

/// A walk of a sequence (Seq.fs): the record of the function that gives the next item.
and walkEnt (ctx: Ctx) : Ent =
    match ctx.State.Ents.TryGetValue "$walk" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = libraryTarget ctx "Seq" "Walk_1"
                Ref =
                    {
                        FullName = "Fable.Library.Zig.Seq.Walk`1"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = [ "T" ]
                Cases =
                    [
                        "",
                        [
                            "next", TFn([ tVoid ], TOpt(TGen "T"))
                            "close", TFn([ tVoid ], tVoid)
                            "reset", tBool
                        ]
                    ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents["$walk"] <- e
        e

/// A function of the part of the library written in F#: `m_Seq.toList`, or `toList` inside
/// Seq.fs itself.
and libraryTarget (ctx: Ctx) (file: string) (fn: string) : string =
    if System.IO.Path.GetFileNameWithoutExtension(ctx.Com.CurrentFile) = file then
        fn
    else
        importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + fn

/// F#'s `Map` and `Set`: the trees of the part of the runtime library written in F#
/// (`Map.fs`, `Set.fs`).
and treeEnt (ctx: Ctx) (isMap: bool) : Ent =
    let key =
        if isMap then
            "$map"
        else
            "$set"

    match ctx.State.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        // (the names Fable gives the declarations of the library's files)
        let file, typeName =
            if isMap then
                "Map", "MapTree_2"
            else
                "Set", "SetTree_1"

        let pre =
            if isMap then
                "Map"
            else
                "Set"

        let e =
            {
                Name = importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + typeName
                Ref =
                    {
                        FullName = $"Fable.Library.Zig.%s{file}.%s{typeName.Replace('_', '`')}"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KHeapUnion
                TypeParams =
                    if isMap then
                        [ "Key"; "Value" ]
                    else
                        [ "T" ]
                Cases = []
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        let self = TEnt(e, e.TypeParams |> List.map TGen)

        e.Cases <-
            [
                pre + "Empty", []
                pre + "Node",
                [
                    "key", TGen e.TypeParams.Head
                    if isMap then
                        "value", TGen "Value"
                    "left", self
                    "right", self
                    "height", tI32
                ]
            ]

        ctx.State.Ents[key] <- e
        e

/// Is this an interface of a Zig type (`[<Erase; Import(...)>]`, see erasedZigType)?
let isErasedZig (ctx: Ctx) (t: Fable.Type) =
    match t with
    | Fable.DeclaredType(ent, _) -> (erasedZigType ctx ent).IsSome
    | _ -> false

let isUnit (t: Fable.Type) =
    match t with
    | Fable.Unit -> true
    | _ -> false

let floatLit (ty: string) (x: float) =
    if System.Double.IsNaN x then
        $"std.math.nan(%s{ty})"
    elif System.Double.IsPositiveInfinity x then
        $"std.math.inf(%s{ty})"
    elif System.Double.IsNegativeInfinity x then
        $"(-std.math.inf(%s{ty}))"
    else
        let s = x.ToString("R", System.Globalization.CultureInfo.InvariantCulture)

        if s.Contains "." || s.Contains "E" || s.Contains "e" then
            s
        else
            s + ".0"

let numberLit (r: SourceLocation option) (v: Fable.NumberValue) : string * Ty =
    match v with
    | Fable.NumberValue.Int8 x -> string<sbyte> x, TPrim "i8"
    | Fable.NumberValue.UInt8 x -> string<byte> x, TPrim "u8"
    | Fable.NumberValue.Int16 x -> string<int16> x, TPrim "i16"
    | Fable.NumberValue.UInt16 x -> string<uint16> x, TPrim "c_ushort"
    | Fable.NumberValue.Int32 x -> string<int> x, tI32
    | Fable.NumberValue.UInt32 x -> string<uint32> x, TPrim "u32"
    | Fable.NumberValue.Int64 x -> string<int64> x, TPrim "i64"
    | Fable.NumberValue.UInt64 x -> string<uint64> x, TPrim "u64"
    | Fable.NumberValue.NativeInt x -> string<int64>(int64 x), TPrim "isize"
    | Fable.NumberValue.UNativeInt x -> string<uint64>(uint64 x), TPrim "usize"
    | Fable.NumberValue.Float32 x -> floatLit "f32" (float x), TPrim "f32"
    | Fable.NumberValue.Float64 x -> floatLit "f64" x, TPrim "f64"
    | _ -> fail r "the Zig target does not support this kind of number yet"

/// ANF for argument lists: an argument that is not a flat expression or that produces a managed
/// value is let-bound, and so is any impure argument evaluated before it.
let bindArgsIn (conArgs: bool) (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr =
    let needsBind ir =
        not (isFlat ir)
        || (isManaged (typeOf ir)
            && (
                match ir with
                | ECall _
                | ECallClo _
                | ECallVt _
                | ECallIface _
                | EClosure _
                | EIface _
                | EKnownIface _
                | ERt _
                | EEmit _ -> true
                // (a constructor argument is an owning position)
                | ECon(TEnt({ Kind = KRefRecord }, _), _, _, _) -> not conArgs
                | ECon(_, _, xs, _) -> not conArgs && not xs.IsEmpty
                | EExnNew _ -> not conArgs
                // (what a field that can be assigned holds is read where the program reads it)
                | EGet _ -> touchesMutable ir
                | _ -> false
            ))

    let arr = List.toArray irs

    match arr |> Array.tryFindIndexBack needsBind with
    | None -> k irs
    | Some last ->
        let binds = List<Var * Expr>()

        let rec hoist (ir: Expr) =
            match ir with
            | ELet(v, r, b) ->
                binds.Add((v, r))
                hoist b
            | _ -> ir

        let outs =
            arr
            |> Array.mapi (fun i ir ->
                if i <= last && (needsBind ir || not (isPure ir)) && not (isVoid (typeOf ir)) then
                    let ir = hoist ir

                    // (what is left after hoisting may need no name: a variable, a literal)
                    if isFlat ir && isPure ir && not (needsBind ir) then
                        ir
                    else
                        let v = ctx.State.NewVar(tempName ir, typeOf ir, VLocal, false)
                        binds.Add((v, ir))
                        EVar v
                // (a unit made by statements, a loop: run before, the unit given)
                elif i <= last && not (isFlat ir) && isVoid (typeOf ir) then
                    let v = ctx.State.NewVar("unitArg", tVoid, VLocal, false)
                    binds.Add((v, ir))
                    EUnit
                else
                    ir
            )

        List.foldBack (fun (v, ir) acc -> ELet(v, ir, acc)) (List.ofSeq binds) (k (List.ofArray outs))

let bindArgs (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr = bindArgsIn false ctx irs k

/// The surrounding variables that `bodies` use, in the order they are first used. A use of a
/// function declared in the surroundings counts as a use of what that function captures.
let freeNames (ctx: Ctx) (bodies: (Fable.Ident list * Fable.Expr) list) : string list =
    let found = List<string>()
    let seen = HashSet<string>()

    let add (bound: Set<string>) (name: string) =
        if not (bound.Contains name) && ctx.Vars.ContainsKey name && seen.Add name then
            found.Add name

    let names (ids: Fable.Ident list) =
        ids |> List.map (fun i -> i.Name) |> Set.ofList

    let rec walk (bound: Set<string>) (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr id ->
            if bound.Contains id.Name || ctx.Vars.ContainsKey id.Name then
                add bound id.Name
            else
                match ctx.LocalFns.TryGetValue id.Name with
                | true, fn -> fn.CaptureNames |> List.iter (add bound)
                | _ -> ()
        | Fable.Lambda(arg, body, _) -> walk (bound.Add arg.Name) body
        | Fable.Delegate(args, body, _, _) -> walk (Set.union bound (names args)) body
        | Fable.Let(id, value, body) ->
            walk bound value
            walk (bound.Add id.Name) body
        | Fable.LetRec(bindings, body) ->
            let bound = Set.union bound (names (bindings |> List.map fst))
            bindings |> List.iter (snd >> walk bound)
            walk bound body
        | Fable.ForLoop(id, start, limit, body, _, _) ->
            walk bound start
            walk bound limit
            walk (bound.Add id.Name) body
        | Fable.DecisionTree(expr, targets) ->
            walk bound expr

            for (ids, target) in targets do
                walk (Set.union bound (names ids)) target
        | Fable.TryCatch(body, catch, finalizer, _) ->
            walk bound body
            catch |> Option.iter (fun (id, handler) -> walk (bound.Add id.Name) handler)
            finalizer |> Option.iter (walk bound)
        | _ -> AST.getSubExpressions e |> List.iter (walk bound)

    for (args, body) in bodies do
        walk (names args) body

    List.ofSeq found

/// Can a `with` handler catch OutOfMemoryException? It catches everything unless it raises again
/// what it caught (F# makes `| :? T -> ...` a handler that tests and re-raises the rest); then
/// only if it tests for a type of which OutOfMemoryException is one, or tests in a way not known
/// here.
let handlerMayCatchOom (caught: Fable.Ident) (handler: Fable.Expr) : bool =
    let mutable reraises = false
    let mutable catches = false

    let rec isCaught (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i -> i.Name = caught.Name
        | Fable.TypeCast(x, _) -> isCaught x
        | _ -> false

    let rec walk (e: Fable.Expr) =
        match e with
        | Fable.Extended(Fable.Throw(None, _), _) -> reraises <- true
        | Fable.Extended(Fable.Throw(Some x, _), _) when isCaught x -> reraises <- true
        | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(ent, _)), _) when isCaught x ->
            match ent.FullName with
            | "System.Exception"
            | "System.SystemException"
            | "System.OutOfMemoryException" -> catches <- true
            | _ -> ()
        | Fable.Test(x, _, _) when isCaught x -> catches <- true
        | _ -> ()

        AST.getSubExpressions e |> List.iter walk

    walk handler
    not reraises || catches

let uniqueName (ctx: Ctx) (wanted: string) =
    let mutable name = wanted
    let mutable i = 1

    while not (ctx.Reserved.Add name) do
        name <- $"%s{wanted}_%d{i}"
        i <- i + 1

    name

let captureExprs (ctx: Ctx) (r: SourceLocation option) (names: string list) : Expr list =
    names
    |> List.map (fun n ->
        match ctx.Vars.TryGetValue n with
        | true, v -> EVar v
        | _ -> fail r "internal: the captured variable `%s` is not in scope" n
    )

/// What `e` is, if it names a function: one declared inside the function being lowered, one of
/// this file, or one of another file.
let tryCallable (ctx: Ctx) (e: Fable.Expr) : Callable option =
    match e with
    | Fable.IdentExpr id when not (ctx.Vars.ContainsKey id.Name) ->
        match ctx.LocalFns.TryGetValue id.Name with
        // (a generic value is not called by name: its value is, see `lw`)
        | true, fn when ctx.State.GenericValues.Contains fn.FnName -> None
        | true, fn ->
            Some
                {
                    Target = fn.FnName
                    Captures = captureExprs ctx id.Range fn.CaptureNames
                    OuterTypeArgs = fn.OuterTypeParams |> List.map TGen
                    TypeParams = fn.TypeParams
                    ArgTypes = fn.ArgTypes
                    Ret = fn.Ret
                }
        | _ ->
            match ctx.Members.TryGetValue id.Name with
            | true, MFunction(typeParams, argTypes, ret) ->
                Some
                    {
                        Target = id.Name
                        Captures = []
                        OuterTypeArgs = []
                        TypeParams = typeParams
                        ArgTypes = argTypes
                        Ret = ret
                    }
            | _ -> None
    | Fable.Import(imp, _, _) ->
        match imp.Kind with
        | Fable.MemberImport memberRef ->
            match ctx.Com.TryGetMember memberRef with
            | Some m when not m.IsValue ->
                let ctorSelf =
                    if m.IsConstructor then
                        m.DeclaringEntity
                        |> Option.bind (fun entRef ->
                            objInfo ctx None entRef
                            |> Option.map (fun _ ->
                                let gs =
                                    match ctx.Com.TryGetEntity entRef with
                                    | Some ent ->
                                        ent.GenericParameters
                                        |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                                    | None -> []

                                Fable.DeclaredType(entRef, gs)
                            )
                        )
                    else
                        None

                let ps = m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type)

                let argTypes =
                    match ctorSelf with
                    | Some selfTy -> selfTy :: ps
                    | None ->
                        match ps with
                        | [] -> [ Fable.Unit ]
                        | ts -> ts

                Some
                    {
                        Target = importAlias ctx imp.Path + "." + imp.Selector
                        Captures = []
                        OuterTypeArgs = []
                        TypeParams =
                            // (those of the type it is a member of, then its own)
                            (match m.DeclaringEntity |> Option.bind ctx.Com.TryGetEntity with
                             | Some ent when not ent.IsFSharpModule ->
                                 ent.GenericParameters |> List.map (fun g -> g.Name)
                             | _ -> [])
                            @ (m.GenericParameters |> List.map (fun g -> g.Name))
                            |> List.distinct
                        ArgTypes = argTypes
                        Ret =
                            if ctorSelf.IsSome then
                                Fable.Unit
                            else
                                m.ReturnParameter.Type
                    }
            | _ -> None
        | _ -> None
    | _ -> None

/// A module-level value of another file: its name there, and whether it can be assigned.
let importedValue (ctx: Ctx) (imp: Fable.ImportInfo) : (string * bool) option =
    match imp.Kind with
    | Fable.MemberImport memberRef ->
        match ctx.Com.TryGetMember memberRef with
        | Some m when m.IsValue -> Some(importAlias ctx imp.Path + "." + imp.Selector, m.IsMutable)
        | _ -> None
    | _ -> None
