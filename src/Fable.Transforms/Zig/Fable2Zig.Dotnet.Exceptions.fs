/// .NET and F# exception constructors, message/ParamName helpers, Flatten, Raise/Reraise.
/// The lowering (`LowerDotnet.dotnetCall`) asks here in the place these cases had among its own.
module internal Fable.Transforms.Zig.DotnetExceptions

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

/// "message (Parameter 'name')", as .NET puts the name of a parameter into a message
let private withParameter (ctx: Ctx) (message: Expr) (parameter: Fable.Expr) : Expr =
    bindArgs
        ctx
        [ message; lw ctx parameter ]
        (fun xs -> EEmit("fable_rt.format(.{ $0, \" (Parameter '\", $1, \"')\" })", xs, tStr))


/// Raise an ArgumentException (or one of its classes) about the parameter `parameter`: its message
/// names it, and so does its `ParamName`
let private raiseArgument
    (ctx: Ctx)
    (r: SourceLocation option)
    (fullName: string)
    (message: Expr)
    (parameter: Fable.Expr)
    (t: Fable.Type)
    : Expr
    =
    bindArgsIn
        true
        ctx
        [ withParameter ctx message parameter; lw ctx parameter ]
        (fun xs ->
            withParamName
                ctx
                (EExnNew(dotnetExnEnt ctx fullName, [ xs.Head ]))
                xs.[1]
                (fun e -> ERaise(e, mapType ctx r t))
        )


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

    match entity, name, args with
    // ---- failures ----
    | "Microsoft.FSharp.Core.Operators", "FailWith", [ msg ] -> raiseDotnet ctx r "System.Exception" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidOp", [ msg ] ->
        raiseDotnet ctx r "System.InvalidOperationException" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidArg", [ arg; msg ] ->
        raiseArgument ctx r "System.ArgumentException" (lw ctx msg) arg t
    | "Microsoft.FSharp.Core.Operators", "NullArg", [ arg ] ->
        let message = ELit(stringLiteral "Value cannot be null.", tStr)
        raiseArgument ctx r "System.ArgumentNullException" message arg t
    // `AggregateException(exceptions)` and `AggregateException(message, exceptions)`: the
    // exception with them inside it
    | "System.AggregateException", ".ctor", args when
        (match args with
         | [ arr ]
         | [ _; arr ] ->
             (match arr.Type with
              | Fable.Array(Fable.DeclaredType(e, _), _) ->
                  e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName
              | Fable.DeclaredType(s, [ Fable.DeclaredType(e, _) ]) ->
                  s.FullName = "System.Collections.Generic.IEnumerable`1"
                  && (e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName)
              | _ -> false)
             && (args.Length = 1 || args.Head.Type = Fable.String)
         | _ -> false)
        ->
        let message, arr =
            match args with
            | [ arr ] -> ELit(stringLiteral "One or more errors occurred.", tStr), arr
            | message :: arr :: _ -> lw ctx message, arr
            | _ -> failwith "unreachable"

        // (a sequence of them: its array)
        let arr =
            match arr.Type with
            | Fable.DeclaredType(_, [ item ]) ->
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "ToArray"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(args = [ arr ], genArgs = [ item ]),
                    Fable.Array(item, Fable.MutableArray),
                    r
                )
            | _ -> arr

        bindArgsIn
            true
            ctx
            [ message ]
            (fun xs ->
                let outer = EExnNew(dotnetExnEnt ctx "System.AggregateException", xs)
                bindArgs ctx [ outer; lw ctx arr ] (fun ys -> EEmit("fable_rt.exnWithInners($0, $1)", ys, tExn))
            )
    // `System.Exception("...")` and the other classes: a new exception with that message
    // `Exception(message, inner)`: the exception, with the one inside it
    | cls, ".ctor", [ message; inner ] when
        dotnetExceptions.ContainsKey cls
        && message.Type = Fable.String
        && (
            match inner.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName
            | _ -> false
        )
        ->
        bindArgsIn
            true
            ctx
            [ lw ctx message ]
            (fun xs ->
                let outer = EExnNew(dotnetExnEnt ctx cls, xs)
                bindArgs ctx [ outer; lw ctx inner ] (fun ys -> EEmit("fable_rt.exnWithInner($0, $1)", ys, tExn))
            )
    | cls, ".ctor", args when
        dotnetExceptions.ContainsKey cls
        && args |> List.forall (fun a -> a.Type = Fable.String)
        ->
        let message =
            match cls, args with
            | "System.ObjectDisposedException", [ objectName ] ->
                bindArgs
                    ctx
                    [ lw ctx objectName ]
                    (fun xs ->
                        EEmit(
                            "fable_rt.format(.{ \"Cannot access a disposed object.\\nObject name: '\", $0, \"'.\" })",
                            xs,
                            tStr
                        )
                    )
            | _, [] when defaultExnMessages.ContainsKey cls -> ELit(stringLiteral defaultExnMessages[cls], tStr)
            | "System.ArgumentNullException", [ parameter ] ->
                withParameter ctx (ELit(stringLiteral "Value cannot be null.", tStr)) parameter
            | "System.ArgumentOutOfRangeException", [ parameter ] ->
                let text = "Specified argument was out of the range of valid values."
                withParameter ctx (ELit(stringLiteral text, tStr)) parameter
            | ("System.ArgumentNullException" | "System.ArgumentOutOfRangeException"), [ parameter; message ] ->
                withParameter ctx (lw ctx message) parameter
            | "System.ArgumentException", [ message; parameter ] -> withParameter ctx (lw ctx message) parameter
            | _, [ message ] -> lw ctx message
            | _ -> fail r "the Zig target does not support this way of making a %s yet" cls

        // (the parameter an ArgumentException is about, its `ParamName`)
        let parameter =
            match cls, args with
            | ("System.ArgumentNullException" | "System.ArgumentOutOfRangeException"), parameter :: _ -> Some parameter
            | "System.ArgumentException", [ _; parameter ] -> Some parameter
            | _ -> None

        match parameter with
        | Some p ->
            bindArgsIn
                true
                ctx
                [ message; lw ctx p ]
                (fun xs -> withParamName ctx (EExnNew(dotnetExnEnt ctx cls, [ xs.Head ])) xs.[1] id)
        | None -> bindArgsIn true ctx [ message ] (fun xs -> EExnNew(dotnetExnEnt ctx cls, xs))
    // `ArgumentException(message, parameter, inner)`
    | "System.ArgumentException", ".ctor", [ message; parameter; inner ] when
        message.Type = Fable.String && parameter.Type = Fable.String
        ->
        bindArgsIn
            true
            ctx
            [ withParameter ctx (lw ctx message) parameter; lw ctx parameter; lw ctx inner ]
            (fun xs ->
                let made = EExnNew(dotnetExnEnt ctx "System.ArgumentException", [ xs.Head ])

                withParamName
                    ctx
                    made
                    xs.[1]
                    (fun named ->
                        bindArgs ctx [ named; xs.[2] ] (fun ys -> EEmit("fable_rt.exnWithInner($0, $1)", ys, tExn))
                    )
            )
    | ("System.ArgumentException" | "System.ArgumentNullException" | "System.ArgumentOutOfRangeException"),
      "get_ParamName",
      [ x ] -> bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnParamName($0)", xs, tStr))
    // `Failure msg` in a pattern: the message, if the exception is a failure
    | "Microsoft.FSharp.Core.Operators", "FailurePattern", [ x ] ->
        let failure = failureEnt ctx

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EIf(
                    EExnTest(xs.Head, failure),
                    ECon(TOpt tStr, "Some", [ EExnGet(xs.Head, failure, "Message", tStr) ], None),
                    ECon(TOpt tStr, "None", [], None),
                    TOpt tStr
                )
            )
    | "Microsoft.FSharp.Collections.FSharpList`1", "get_Empty", _ -> ECon(mapType ctx r t, "Empty", [], None)
    | "System.AggregateException", "Flatten", [ x ] -> pure' "fable_rt.exnFlatten($0)" [ x ] tExn
    | "System.AggregateException", "get_InnerExceptions", [ x ] ->
        pure' "fable_rt.exnInnerList($0)" [ x ] (mapType ctx r t)
    | entity, "get_InnerException", [ x ] when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        rt "fable_rt.exnInner($0)" [ x ] tExn
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ Fable.Call(Fable.Import(imp, _, _), inner, _, _) ] when
        imp.Selector = "get_InnerException"
        ->
        pure' "fable_rt.exnHasNoInner($0)" [ inner.ThisArg.Value ] tBool
    | entity, "get_Message", x :: _ when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnMessage($0)", xs, tStr))
    | entity, "get_StackTrace", x :: _ when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        ctx.State.UsesStackTrace <- true

        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnStackTrace($0)", xs, tStr))
    | "Microsoft.FSharp.Core.Operators", "Raise", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ERaise(xs.Head, mapType ctx r t))
    | "Microsoft.FSharp.Core.Operators", "Reraise", _ ->
        match ctx.CaughtExn with
        | Some exV -> ERaise(EVar exV, mapType ctx r t)
        | None -> fail r "`reraise ()` is only possible inside a `with` handler"
    | _ -> Unchecked.defaultof<Expr>
