/// .NET's members: tasks and async. The lowering (`Lower.dotnetCall`) asks here in the place these
/// cases had among its own.
module Fable.Transforms.Zig.DotnetAsync

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

    let lib fn (xs: Fable.Expr list) =
        libraryCall
            ctx
            r
            "Async"
            fn
            { info with
                ThisArg = None
                SignatureArgTypes = []
            }
            xs
            t

    let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

    let disposable (x: Fable.Expr) =
        Fable.TypeCast(
            x,
            Fable.DeclaredType(
                {
                    FullName = "System.IDisposable"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                []
            )
        )

    match entity, name, args with
    // ---- cancellation: the library's Async.fs ----
    | "System.Threading.CancellationTokenSource", ".ctor", [] -> lib "sourceCreate" unitArg
    | "System.Threading.CancellationTokenSource", ".ctor", [ ms ] when ms.Type <> Fable.Any ->
        lib "sourceCreateWithDelay" [ ms ]
    | "System.Threading.CancellationTokenSource", "Cancel", s :: _ -> lib "sourceCancel" [ s ]
    | "System.Threading.CancellationTokenSource", "CancelAfter", [ s; ms ] -> lib "sourceCancelAfter" [ s; ms ]
    | "System.Threading.CancellationTokenSource", "get_Token", [ s ] -> lib "sourceToken" [ s ]
    | "System.Threading.CancellationTokenSource", "get_IsCancellationRequested", [ s ] ->
        lib "sourceIsCancellationRequested" [ s ]
    | "System.Threading.CancellationTokenSource", "Dispose", [ s ] -> lib "sourceDispose" [ s ]
    | "System.Threading.CancellationToken", "get_None", [] -> lib "tokenNone" unitArg
    | "System.Threading.CancellationToken", "get_IsCancellationRequested", [ tk ] ->
        lib "tokenIsCancellationRequested" [ tk ]
    | "System.Threading.CancellationToken", "ThrowIfCancellationRequested", [ tk ] ->
        lib "tokenThrowIfCancellationRequested" [ tk ]
    | "System.Threading.CancellationToken", "Register", [ tk; f ] -> lib "tokenRegister" [ tk; f ]
    | "System.Threading.CancellationToken", "Register", [ tk; f; state ] -> lib "tokenRegisterWith" [ tk; f; state ]
    | "System.Threading.CancellationTokenRegistration", "Dispose", [ reg ] ->
        dotnetCall
            ctx
            r
            "System.IDisposable"
            "Dispose"
            { info with
                ThisArg = Some(disposable reg)
                Args = []
            }
            t
    // ---- the Async module and builder members that take a token, continuations, or a resource
    | "Microsoft.FSharp.Control.FSharpAsync", "StartWithContinuations", [ c; ok; fail; cancel ] ->
        lib "startWithContinuations" [ c; ok; fail; cancel ]
    | "Microsoft.FSharp.Control.FSharpAsync", "StartWithContinuations", [ c; ok; fail; cancel; tk ] ->
        lib "startWithContinuationsToken" [ c; ok; fail; cancel; tk ]
    | "Microsoft.FSharp.Control.FSharpAsync", "FromContinuations", [ f ] -> lib "fromContinuations" [ f ]
    | "Microsoft.FSharp.Control.FSharpAsync", "StartChild", [ c; timeout ] -> lib "startChildWith" [ c; timeout ]
    | "Microsoft.FSharp.Control.FSharpAsync", "StartChild", c :: _ -> lib "startChild" [ c ]
    | "Microsoft.FSharp.Control.FSharpAsync", "get_CancellationToken", _ -> lib "cancellationToken" unitArg
    | "Microsoft.FSharp.Control.FSharpAsync", "OnCancel", [ f ] -> lib "onCancel" [ f ]
    | "Microsoft.FSharp.Control.FSharpAsync", "Choice", [ cs ] -> lib "choice" [ cs ]
    | "Microsoft.FSharp.Control.FSharpAsync", "TryCancelled", [ c; f ] -> lib "tryCancelled" [ c; f ]
    | "Microsoft.FSharp.Control.FSharpAsync", "Sequential", [ cs ] -> lib "sequential" [ cs ]
    | "Microsoft.FSharp.Control.FSharpAsync", "Sleep", [ span ] when
        (match span.Type with
         | Fable.DeclaredType(e, _) -> e.FullName = "System.TimeSpan"
         | _ -> false)
        ->
        lib "sleepSpan" [ span ]
    | "Microsoft.FSharp.Control.FSharpAsync", "AwaitEvent", ev :: rest ->
        let cancelAction =
            match rest with
            | [ a ] -> a
            | _ -> Fable.Value(Fable.NewOption(None, Fable.LambdaType(Fable.Unit, Fable.Unit), false), None)

        lib "awaitEvent" [ ev; cancelAction ]
    | "Microsoft.FSharp.Control.FSharpAsync", "AwaitTask", [ task ] ->
        libraryCall
            ctx
            r
            "Task"
            "awaitTask"
            { info with
                ThisArg = None
                SignatureArgTypes = []
            }
            [ task ]
            t
    // (`StartImmediateAsTask`: `StartAsTask` here starts the computation at once too)
    | "Microsoft.FSharp.Control.FSharpAsync", "StartImmediateAsTask", args ->
        dotnetCall ctx r "Microsoft.FSharp.Control.FSharpAsync" "StartAsTask" info t
    | "Microsoft.FSharp.Control.FSharpAsync", "StartAsTask", c :: rest ->
        // (the token, F#'s optional argument, is the last)
        let token =
            match rest with
            | [ _; tk ]
            | [ tk ] when
                (match tk.Type with
                 | Fable.Option(Fable.DeclaredType(e, _), _) -> e.FullName = "System.Threading.CancellationToken"
                 | _ -> false)
                ->
                tk
            | _ ->
                Fable.Value(
                    Fable.NewOption(
                        None,
                        Fable.DeclaredType(
                            {
                                FullName = "System.Threading.CancellationToken"
                                Path = Fable.CoreAssemblyName "System.Runtime"
                            },
                            []
                        ),
                        false
                    ),
                    None
                )

        libraryCall
            ctx
            r
            "Task"
            "startAsTaskToken"
            { info with
                ThisArg = None
                SignatureArgTypes = []
            }
            [ c; token ]
            t
    | "Microsoft.FSharp.Control.FSharpAsync", "RunSynchronously", [ c; _; tk ] when
        tk.Type <> Fable.Option(Fable.Any, false)
        ->
        lib "runSynchronouslyToken" [ c; tk ]
    | "Microsoft.FSharp.Control.FSharpAsync", "RunSynchronously", c :: _ -> lib "runSynchronously" [ c ]
    | "Microsoft.FSharp.Control.FSharpAsync", ("StartImmediate" | "Start"), [ c; tk ] ->
        lib "startImmediateToken" [ c; tk ]
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder", "Using", [ _; resource; binder ]
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder", "Using", [ resource; binder ] ->
        lib "builderUsing" [ resource; disposable resource; binder ]
    // ---- task: the builder (which has no state) and the members of a task ----
    | "Microsoft.FSharp.Control.TaskBuilderModule", "task", _ -> EUnit
    | ("Microsoft.FSharp.Control.TaskBuilder" | "Microsoft.FSharp.Control.TaskBuilderBase" | "Microsoft.FSharp.Control.TaskBuilderExtensions.LowPriority" | "Microsoft.FSharp.Control.TaskBuilderExtensions.HighPriority" | "Microsoft.FSharp.Control.TaskBuilderExtensions.MediumPriority"),
      _,
      _ when entity.StartsWith("Microsoft.FSharp.Control.TaskBuilder", System.StringComparison.Ordinal) ->
        let member' = name.Substring(name.LastIndexOf '.' + 1)

        let given =
            args
            |> List.filter (fun a ->
                match a.Type with
                | Fable.DeclaredType(ent, _) -> ent.FullName <> "Microsoft.FSharp.Control.TaskBuilder"
                | _ -> true
            )

        let itemOf (t: Fable.Type) =
            match t with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        // (`let!`, `do!` and `return!` of an Async: the task it is started as, as F# binds it)
        let given =
            match member', given with
            | ("Bind" | "ReturnFrom"), c :: rest when
                (match c.Type with
                 | Fable.DeclaredType(e, [ _ ]) -> e.FullName = "Microsoft.FSharp.Control.FSharpAsync`1"
                 | _ -> false)
                ->
                let item = itemOf c.Type

                let asTask =
                    Fable.Call(
                        Fable.Import(
                            {
                                Selector = "StartAsTask"
                                Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Control.FSharpAsync"
                                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                            },
                            Fable.Any,
                            None
                        ),
                        Fable.CallInfo.Create(args = [ c ], genArgs = [ item ]),
                        Fable.DeclaredType(
                            {
                                FullName = "System.Threading.Tasks.Task`1"
                                Path = Fable.CoreAssemblyName "System.Runtime"
                            },
                            [ item ]
                        ),
                        r
                    )

                asTask :: rest
            | _ -> given

        let retItem (f: Fable.Expr) =
            match f.Type with
            | Fable.LambdaType(_, ret)
            | Fable.DelegateType(_, ret) -> itemOf ret
            | _ -> Fable.Unit

        let typeArgs =
            match member', given with
            | "Run", [ c ] -> [ itemOf c.Type ]
            | "Delay", [ f ] -> [ retItem f ]
            | "Return", [ x ] -> [ x.Type ]
            | "Bind", [ task; cont ] -> [ itemOf task.Type; retItem cont ]
            | "ReturnFrom", [ task ] -> [ itemOf task.Type ]
            | "Combine", [ _; second ] -> [ itemOf second.Type ]
            | ("TryWith" | "TryFinally"), b :: _ -> [ itemOf b.Type ]
            | "For", [ sq; _ ] -> [ itemOf sq.Type ]
            | "Using", [ resource; binder ] -> [ resource.Type; retItem binder ]
            | _ -> []

        // (`use`: the resource, and the same seen as an IDisposable to dispose of)
        let given =
            match member', given with
            | "Using", [ resource; binder ] -> [ resource; disposable resource; binder ]
            | _ -> given

        let resultTy =
            match member' with
            | "Run" -> t
            | _ when t <> Fable.Any -> t
            | "Using" -> taskCodeOf (List.last typeArgs)
            | _ -> taskCodeOf (List.tryHead typeArgs |> Option.defaultValue Fable.Unit)

        libraryCall
            ctx
            r
            "Task"
            ("builder" + member')
            { info with
                GenericArgs = typeArgs
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = given
            }
            given
            resultTy
    | "System.Threading.Tasks.Task`1", ("get_Result" | "Wait" | "get_IsCompleted" | "get_IsFaulted"), [ task ] ->
        let fn =
            match name with
            | "get_Result" -> "resultOf"
            | "Wait" -> "waitFor"
            | "get_IsCompleted" -> "isCompleted"
            | _ -> "isFaulted"

        let item =
            match task.Type with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            fn
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = [ task ]
            }
            [ task ]
            t
    | "System.Threading.Tasks.Task", ("Wait" | "get_IsCompleted" | "get_IsFaulted"), [ task ] ->
        let fn =
            match name with
            | "Wait" -> "waitFor"
            | "get_IsCompleted" -> "isCompleted"
            | _ -> "isFaulted"

        // (a member of Task called on a Task<'T>: the item type is the object's)
        let item =
            match task.Type with
            | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.Task`1" -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            fn
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = [ task ]
            }
            [ task ]
            t
    // (`t.GetAwaiter()`: the task; `GetResult()`: its result, or its exception itself)
    | ("System.Threading.Tasks.Task`1" | "System.Threading.Tasks.Task"), "GetAwaiter", [ task ] -> lw ctx task
    | ("System.Runtime.CompilerServices.TaskAwaiter`1" | "System.Runtime.CompilerServices.TaskAwaiter"),
      "GetResult",
      [ awaiter ] ->
        let item =
            match awaiter.Type with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            "getResult"
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = [ awaiter ]
            }
            [ awaiter ]
            t
    | "System.Threading.Tasks.Task", "FromException", [ e ] ->
        let item =
            match t with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            "fromException"
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ e ]
            t
    // ---- MailboxProcessor and its reply channels: the library's Async.fs ----
    | ("Microsoft.FSharp.Control.FSharpMailboxProcessor`1" | "Microsoft.FSharp.Control.FSharpAsyncReplyChannel`1"),
      name,
      args ->
        // (`mb.Start()` and the others of no arguments are given unit)
        let args =
            match args with
            | [ x; Fable.Value(Fable.UnitConstant, _) ] when name = "Start" || name = "Dispose" -> [ x ]
            | _ -> args

        let itemOf (x: Fable.Type) =
            match x with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        let msg =
            match name, args with
            | (".ctor" | "Start"), body :: _ when
                (match body.Type with
                 | Fable.LambdaType _
                 | Fable.DelegateType _ -> true
                 | _ -> false)
                ->
                itemOf t
            | _, x :: _ -> itemOf x.Type
            | _ -> Fable.Unit

        let callWithSig sigTys fn (typeArgs: Fable.Type list) xs =
            libraryCall
                ctx
                r
                "Async"
                fn
                { info with
                    GenericArgs = typeArgs
                    SignatureArgTypes = sigTys
                    MemberRef = None
                    ThisArg = None
                }
                xs
                t

        let call fn (typeArgs: Fable.Type list) xs = callWithSig [] fn typeArgs xs

        // (an optional argument left out: None)
        let opt (ty: Fable.Type) (x: Fable.Expr option) =
            match x with
            | Some v -> v
            | None -> Fable.Value(Fable.NewOption(None, ty, false), None)

        let tokenType =
            Fable.DeclaredType(
                {
                    FullName = "System.Threading.CancellationToken"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                []
            )

        let intType = Fable.Number(Int32, Fable.NumberInfo.Empty)

        // (the reply's type: what the builder's channel replies)
        let replyOf (build: Fable.Expr) =
            match build.Type with
            | Fable.LambdaType(Fable.DeclaredType(_, [ reply ]), _)
            | Fable.DelegateType([ Fable.DeclaredType(_, [ reply ]) ], _) -> reply
            | _ -> Fable.Unit

        let isMailboxThis =
            match args with
            | x :: _ ->
                match x.Type with
                | Fable.DeclaredType(e, _) -> e.FullName = "Microsoft.FSharp.Control.FSharpMailboxProcessor`1"
                | _ -> false
            | [] -> false

        match entity, name, args with
        | _, "Reply", [ c; v ] ->
            callWithSig [ c.Type; Fable.GenericParam("'R", false, []) ] "replyChannelReply" [ msg ] [ c; v ]
        | _, ".ctor", body :: rest -> call "mailboxCreate" [ msg ] [ body; opt tokenType (List.tryHead rest) ]
        | _, "Start", [ mb ] when isMailboxThis -> call "mailboxStart" [ msg ] [ mb ]
        | _, "Start", body :: rest -> call "mailboxStartNew" [ msg ] [ body; opt tokenType (List.tryHead rest) ]
        | _, "Post", [ mb; m ] ->
            callWithSig [ mb.Type; Fable.GenericParam("'Msg", false, []) ] "mailboxPost" [ msg ] [ mb; m ]
        | _, "get_CurrentQueueLength", [ mb ] -> call "mailboxQueueLength" [ msg ] [ mb ]
        | _, "Receive", mb :: rest -> call "mailboxReceive" [ msg ] [ mb; opt intType (List.tryHead rest) ]
        | _, "TryReceive", mb :: rest -> call "mailboxTryReceive" [ msg ] [ mb; opt intType (List.tryHead rest) ]
        | _, "Scan", mb :: f :: _ ->
            let result =
                match f.Type with
                | Fable.LambdaType(_, Fable.Option(Fable.DeclaredType(_, [ x ]), _)) -> x
                | _ -> Fable.Unit

            call "mailboxScan" [ msg; result ] [ mb; f ]
        | _, "PostAndAsyncReply", mb :: build :: _ ->
            call "mailboxPostAndAsyncReply" [ msg; replyOf build ] [ mb; build ]
        | _, "PostAndReply", mb :: build :: _ -> call "mailboxPostAndReply" [ msg; replyOf build ] [ mb; build ]
        | _, "PostAndTryAsyncReply", mb :: build :: rest ->
            call "mailboxPostAndTryAsyncReply" [ msg; replyOf build ] [ mb; build; opt intType (List.tryHead rest) ]
        | _, "Dispose", _ -> EUnit
        | _ -> fail r "the Zig target does not support MailboxProcessor.%s with these arguments yet" name
    // `TaskCompletionSource<'T>`: the library's TaskSourceOf
    | "System.Threading.Tasks.TaskCompletionSource`1", name, args ->
        let item =
            match
                (if name = ".ctor" then
                     t
                 else
                     args.Head.Type)
            with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        let callWithSig sigTys fn xs =
            libraryCall
                ctx
                r
                "Task"
                fn
                { info with
                    GenericArgs = [ item ]
                    SignatureArgTypes = sigTys
                    MemberRef = None
                    ThisArg = None
                }
                xs
                t

        let call fn xs = callWithSig [] fn xs

        match name, args with
        | ".ctor", _ -> call "sourceCreate" [ Fable.Value(Fable.UnitConstant, None) ]
        | "get_Task", [ s ] -> call "sourceTask" [ s ]
        | ("SetResult" | "TrySetResult"), [ s; x ] ->
            callWithSig
                [ s.Type; Fable.GenericParam("'T", false, []) ]
                (name.Substring(0, 1).ToLowerInvariant() + name.Substring 1)
                [ s; x ]
        | ("SetException" | "TrySetException"), [ s; x ] ->
            call (name.Substring(0, 1).ToLowerInvariant() + name.Substring 1) [ s; x ]
        | ("SetCanceled" | "TrySetCanceled"), s :: _ ->
            call (name.Substring(0, 1).ToLowerInvariant() + name.Substring 1) [ s ]
        | _ -> fail r "the Zig target does not support TaskCompletionSource.%s with these arguments yet" name
    | "System.Threading.Tasks.Task", "FromResult", [ x ] ->
        libraryCall
            ctx
            r
            "Task"
            "fromResult"
            { info with
                GenericArgs = [ x.Type ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ x ]
            t
    // `Task.Run(fun () -> ...)`: on a thread of its own (the library's Task.run)
    | "System.Threading.Tasks.Task", "Run", [ f ] ->
        let item =
            match t with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            "run"
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ f ]
            t
    // (`Task.Delay(timeSpan)`: its whole milliseconds)
    | "System.Threading.Tasks.Task", "Delay", [ span ] when
        (match span.Type with
         | Fable.DeclaredType(e, _) -> e.FullName = "System.TimeSpan"
         | _ -> false)
        ->
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

        let whole =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "ToInt32"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(args = [ ms ]),
                Fable.Number(Int32, Fable.NumberInfo.Empty),
                r
            )

        dotnetCall
            ctx
            r
            "System.Threading.Tasks.Task"
            "Delay"
            { info with
                ThisArg = None
                Args = [ whole ]
            }
            t
    | "System.Threading.Tasks.Task", "Delay", [ ms; token ] ->
        libraryCall
            ctx
            r
            "Task"
            "delayToken"
            { info with
                ThisArg = None
                SignatureArgTypes = []
                MemberRef = None
            }
            [ ms; token ]
            t
    | "System.Threading.Tasks.Task", "Delay", [ ms ] ->
        libraryCall
            ctx
            r
            "Task"
            "delay"
            { info with
                GenericArgs = []
                SignatureArgTypes = []
                MemberRef = None
            }
            [ ms ]
            t
    | "System.Threading.Tasks.Task", "get_CompletedTask", [] ->
        libraryCall
            ctx
            r
            "Task"
            "completedTask"
            { info with
                GenericArgs = []
                SignatureArgTypes = []
                MemberRef = None
            }
            []
            t
    | "System.Threading.Tasks.Task", "WhenAll", [ tasks ] ->
        let item =
            match t with
            | Fable.DeclaredType(_, [ Fable.Array(item, _) ]) -> item
            | _ -> Fable.Unit

        let tasksSeq =
            match tasks with
            | Fable.Value(Fable.NewArray(Fable.ArrayValues _, _, _), _) ->
                Fable.TypeCast(
                    tasks,
                    Fable.DeclaredType(
                        seqEntRef,
                        [
                            (match tasks.Type with
                             | Fable.Array(i, _) -> i
                             | i -> i)
                        ]
                    )
                )
            | _ -> tasks

        libraryCall
            ctx
            r
            "Task"
            "whenAll"
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ tasksSeq ]
            t

    // ---- async: `async` is the builder, which has no state ----
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", "DefaultAsyncBuilder", _ -> EUnit

    | _ -> Unchecked.defaultof<Expr>
