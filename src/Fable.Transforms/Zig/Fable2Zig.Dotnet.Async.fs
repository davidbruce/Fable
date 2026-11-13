/// .NET's members: tasks and async. The lowering (`Lower.dotnetCall`) asks here in the place these
/// cases had among its own.
module Fable.Transforms.Zig.DotnetAsync

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
            | _ -> []

        let resultTy =
            match member' with
            | "Run" -> t
            | _ when t <> Fable.Any -> t
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
