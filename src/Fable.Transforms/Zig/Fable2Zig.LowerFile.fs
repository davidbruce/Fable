/// File-level lowering (`lowerFile`), class constructors, type hierarchies, and `extern`/P/Invoke wrappers.
module Fable.Transforms.Zig.LowerFile

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

/// The body F# gives an `extern` function (`[<DllImport>] extern int f(int x)`)
let isExternBody (body: Fable.Expr) =
    match body with
    | Fable.Call(Fable.Import({ Selector = "FailWith" }, _, _),
                 { Args = [ Fable.Value(Fable.StringConstant "extern was not given a DllImport attribute", _) ] },
                 _,
                 _) -> true
    | _ -> false

/// The `EntryPoint` given to an attribute of a member (DllImport's, UnmanagedCallersOnly's)
let attEntryPoint (attFullName: string) (info: Fable.MemberFunctionOrValue) : string option =
    info.Attributes
    |> Seq.tryPick (fun att ->
        match att with
        | :? Fable.Transforms.FSharp2Fable.FsAtt as a when att.Entity.FullName = attFullName ->
            a.NamedArguments
            |> List.tryPick (fun (name, value) ->
                match value with
                | :? string as s when name = "EntryPoint" -> Some s
                | _ -> None
            )
        | _ -> None
    )

/// An `extern` function's body here: a call of the C function it names (DllImport's
/// `EntryPoint`, or its own name), see fable_rt.callC
let externBody (com: Compiler) (m: Fable.MemberDecl) : Fable.Expr =
    let info = com.TryGetMember m.MemberRef

    let entryPoint =
        info
        |> Option.bind (attEntryPoint "System.Runtime.InteropServices.DllImportAttribute")

    let name =
        entryPoint
        |> Option.orElse (info |> Option.map (fun i -> i.CompiledName))
        |> Option.defaultValue m.Name

    // How each value crosses (fable_rt.CKind): `[<MarshalAs>]` of a parameter or the result,
    // else by its type: a bool as .NET's 4-byte `BOOL`, a string as UTF-8, or UTF-16 under
    // DllImport's `CharSet = CharSet.Unicode`
    let dllImport =
        info
        |> Option.bind (fun i ->
            i.Attributes
            |> Seq.tryFind (fun a -> a.Entity.FullName = "System.Runtime.InteropServices.DllImportAttribute")
        )

    let unicode =
        match dllImport with
        | Some(:? Fable.Transforms.FSharp2Fable.FsAtt as a) ->
            a.NamedArguments
            |> List.exists (fun (n, v) -> n = "CharSet" && v <> null && System.Convert.ToInt32 v = 3)
        | _ -> false

    let marshalAs (atts: Fable.Attribute seq) =
        atts
        |> Seq.tryPick (fun a ->
            if a.Entity.FullName = "System.Runtime.InteropServices.MarshalAsAttribute" then
                match a.ConstructorArgs with
                | v :: _ when v <> null ->
                    match System.Convert.ToInt32 v with
                    | 2 -> Some "bool4" // UnmanagedType.Bool
                    | 3
                    | 4 -> Some "bool1" // I1, U1
                    | 20
                    | 22
                    | 48 -> Some "utf8" // LPStr, LPTStr, LPUTF8Str
                    | 21 -> Some "utf16" // LPWStr
                    | _ -> None
                | _ -> None
            else
                None
        )

    let rec kindOf (t: Fable.Type) (atts: Fable.Attribute seq) =
        match marshalAs atts with
        | Some k -> k
        | None ->
            match t with
            | Fable.String ->
                if unicode then
                    "utf16"
                else
                    "utf8"
            | Fable.Boolean -> "bool4"
            | Fable.DeclaredType(e, v :: _) when e.FullName = "Microsoft.FSharp.Core.byref`2" -> kindOf v []
            | _ -> "plain"

    let args = m.Args |> List.filter (fun a -> a.Type <> Fable.Unit)

    let parameters =
        info
        |> Option.map (fun i -> i.CurriedParameterGroups |> List.concat)
        |> Option.defaultValue []

    let kinds =
        args
        |> List.mapi (fun i a ->
            let atts =
                if parameters.Length = args.Length then
                    parameters.[i].Attributes
                else
                    Seq.empty

            "." + kindOf a.Type atts
        )
        |> String.concat ", "

    let retKind =
        "."
        + kindOf
            m.Body.Type
            (info
             |> Option.map (fun i -> i.ReturnParameter.Attributes)
             |> Option.defaultValue Seq.empty)

    let holes = args |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "

    Fable.Emit(
        {
            Macro = $"fable_rt.callC($R, \"%s{name}\", .{{ %s{kinds} }}, %s{retKind}, .{{ %s{holes} }})"
            IsStatement = false
            CallInfo = Fable.CallInfo.Create(args = (args |> List.map Fable.IdentExpr))
        },
        m.Body.Type,
        None
    )

let isEntryPoint (info: Fable.MemberFunctionOrValue) =
    info.Attributes
    |> Seq.exists (fun att -> att.Entity.FullName = "Microsoft.FSharp.Core.EntryPointAttribute")

let lowerFile (com: Compiler) (file: Fable.File) : FileState =
    let state = FileState()

    // (the constructors of this file's classes, for `Activator.CreateInstance` of a known type)
    fileCtors().Clear()

    let rec collectCtors (decls: Fable.Declaration list) =
        for d in decls do
            match d with
            | Fable.MemberDeclaration m ->
                match com.TryGetMember m.MemberRef with
                | Some info when info.IsConstructor ->
                    match info.DeclaringEntity with
                    | Some ent ->
                        let ps =
                            m.Args
                            |> List.filter (fun a -> not a.IsThisArgument)
                            |> List.map (fun a -> a.Type)

                        let known =
                            match fileCtors().TryGetValue ent.FullName with
                            | true, l -> l
                            | _ -> []

                        fileCtors().[ent.FullName] <- known @ [ m.Name, m.MemberRef, ps ]
                    | None -> ()
                | _ -> ()
            | Fable.ModuleDeclaration md -> collectCtors md.Members
            | Fable.ClassDeclaration c ->
                match c.Constructor with
                | Some m ->
                    let ps =
                        m.Args
                        |> List.filter (fun a -> not a.IsThisArgument)
                        |> List.map (fun a -> a.Type)

                    let known =
                        match fileCtors().TryGetValue c.Entity.FullName with
                        | true, l -> l
                        | _ -> []

                    fileCtors().[c.Entity.FullName] <- known @ [ m.Name, m.MemberRef, ps ]
                | None -> ()
            | _ -> ()

    collectCtors file.Declarations
    let members = Dictionary<string, MemberKind>()

    let reserved = HashSet<string>()

    let newCtx (fnBase: string) =
        {
            Com = com
            State = state
            Vars = Dictionary()
            Members = members
            LocalFns = Dictionary()
            FnBase = fnBase
            TypeParams = []
            Reserved = reserved
            DecisionTargets = []
            Boxed = HashSet()
            NonNull = HashSet()
            Positive = HashSet()
            NonNeg = HashSet()
            BoundedBelowMax = HashSet()
            Lengths = Dictionary()
            ConstLen = Dictionary()
            KnownTypes = Dictionary()
            InBounds = HashSet()
            Enumerators = Dictionary()
            OutTuples = Dictionary()
            CaughtExn = None
            InCtor = false
            NoTailCalls = state.NoTailCallsFile
        }

    let report (r: SourceLocation option) (msg: string) =
        com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)

    let attached = List<Fable.MemberDecl>()
    let mutable actions = 0
    /// the module value that holds a static field -> its type
    let staticTypes = Dictionary<string, Fable.Type>()

    let rec membersOf (decls: Fable.Declaration list) : Fable.MemberDecl list =
        decls
        |> List.collect (fun d ->
            match d with
            // a secondary or explicit constructor of an object class: takes `self_obj` first, runs
            // any delegating/base constructor on it, writes this class's fields, and runs any `then`
            // block directly against the live object.
            | Fable.MemberDeclaration m when
                (match com.TryGetMember m.MemberRef with
                 | Some info when info.IsConstructor ->
                     match info.DeclaringEntity with
                     | Some cls ->
                         (try
                             (objInfo (newCtx m.Name) None cls).IsSome
                          with ZigError _ ->
                              false)
                     | None -> false
                 | _ -> false)
                ->
                let cls = (com.TryGetMember m.MemberRef).Value.DeclaringEntity.Value
                let o = (objInfo (newCtx m.Name) None cls).Value

                let selfId, args =
                    match m.Args with
                    | first :: _ when first.IsThisArgument -> first, m.Args
                    | _ ->
                        let s = objSelfIdent o
                        s, s :: m.Args

                let ownFields = caseFields (TEnt(o.Part, [])) ""

                let isSysObjCtor (x: Fable.Expr) =
                    match x with
                    | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
                        imp.Selector = ".ctor" && imp.Path = Replacements.DotnetPrefix + "System.Object"
                    | _ -> false

                let rec rewriteSelf (e: Fable.Expr) : Fable.Expr =
                    match e with
                    | Fable.Call(Fable.Import(imp, _, _), _, _, _) when
                        imp.Selector = ".ctor" && imp.Path = Replacements.DotnetPrefix + "System.Object"
                        ->
                        Fable.Value(Fable.UnitConstant, None)
                    | Fable.Value(Fable.ThisValue _, r) -> Fable.IdentExpr { selfId with Range = r }
                    | _ -> e |> AST.visit rewriteSelf

                let rec endsWithIdent (name: string) (e: Fable.Expr) =
                    match e with
                    | Fable.IdentExpr id -> id.Name = name
                    | Fable.Sequential xs when not xs.IsEmpty -> endsWithIdent name (List.last xs)
                    | Fable.Let(_, _, b)
                    | Fable.LetRec(_, b) -> endsWithIdent name b
                    | Fable.TypeCast(x, _) -> endsWithIdent name x
                    | _ -> false

                let rec stripReturnIdent (name: string) (e: Fable.Expr) : Fable.Expr =
                    match e with
                    | Fable.IdentExpr id when id.Name = name -> Fable.Value(Fable.UnitConstant, id.Range)
                    | Fable.Sequential xs when not xs.IsEmpty ->
                        let rev = List.rev xs
                        Fable.Sequential(List.rev (stripReturnIdent name rev.Head :: rev.Tail))
                    | Fable.Let(id, v, b) -> Fable.Let(id, v, stripReturnIdent name b)
                    | Fable.LetRec(bs, b) -> Fable.LetRec(bs, stripReturnIdent name b)
                    | Fable.TypeCast(x, _) -> stripReturnIdent name x
                    | other -> Fable.Sequential [ other; Fable.Value(Fable.UnitConstant, None) ]

                let emitOwnFields (values: Fable.Expr list) (r: SourceLocation option) =
                    let ownValues =
                        if values.Length > ownFields.Length then
                            List.skip (values.Length - ownFields.Length) values
                        else
                            values

                    let sets =
                        List.map2
                            (fun (fname, _) (v: Fable.Expr) ->
                                Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet fname, v.Type, rewriteSelf v, r)
                            )
                            ownFields
                            ownValues

                    Fable.Sequential(sets @ [ Fable.Value(Fable.UnitConstant, r) ])

                let isTypeOfClass (entFullName: string) (t: Fable.Type) =
                    match t with
                    | Fable.DeclaredType(c, _) -> c.FullName = entFullName
                    | _ -> false

                let rec initTail (e: Fable.Expr) : Fable.Expr =
                    match e with
                    // Delegating secondary constructor (`new() = C(args)`)
                    | Fable.Call(callee, call, Fable.DeclaredType(c, cArgs), r) when
                        c.FullName = o.FullName && isConstructorCall com call
                        ->
                        Fable.Call(
                            callee,
                            { call with
                                ThisArg = Some(Fable.IdentExpr selfId)
                                Args = call.Args |> List.map rewriteSelf
                                GenericArgs =
                                    if call.GenericArgs.IsEmpty then
                                        cArgs
                                    else
                                        call.GenericArgs
                            },
                            Fable.Unit,
                            r
                        )
                    // Explicit constructor with `then` (`let this = created in (rest; this)`)
                    | Fable.Let(thisId, created, bodyAfter) when
                        isTypeOfClass o.FullName created.Type && endsWithIdent thisId.Name bodyAfter
                        ->
                        Fable.Sequential
                            [
                                initTail created
                                Fable.Let(
                                    thisId,
                                    Fable.IdentExpr selfId,
                                    rewriteSelf (stripReturnIdent thisId.Name bodyAfter)
                                )
                            ]
                    // Derived explicit constructor with compiler-generated base call:
                    // `let base = Base(args) in { inherited @ own }`
                    | Fable.Let(baseId, Fable.Call(baseCallee, baseCall, Fable.DeclaredType(baseRef, bArgs), cr), inner) when
                        o.Parent.IsSome
                        && baseRef.FullName = o.Parent.Value.FullName
                        && isConstructorCall com baseCall
                        ->
                        let bArgs =
                            if baseCall.GenericArgs.IsEmpty then
                                bArgs
                            else
                                baseCall.GenericArgs

                        Fable.Sequential
                            [
                                Fable.Call(
                                    baseCallee,
                                    { baseCall with
                                        ThisArg = Some(Fable.IdentExpr selfId)
                                        Args = baseCall.Args |> List.map rewriteSelf
                                        GenericArgs = bArgs
                                    },
                                    Fable.Unit,
                                    cr
                                )
                                Fable.Let(baseId, Fable.IdentExpr selfId, initTail inner)
                            ]
                    // Explicit constructor record literal (`{ X = ... }`)
                    | Fable.Value(Fable.NewRecord(values, ent, _), r) when
                        ent.FullName = o.FullName && values.Length >= ownFields.Length
                        ->
                        emitOwnFields values r
                    | Fable.Let(id, v, b) -> Fable.Let(id, rewriteSelf v, initTail b)
                    | Fable.LetRec(bs, b) ->
                        Fable.LetRec(bs |> List.map (fun (id, v) -> id, rewriteSelf v), initTail b)
                    | Fable.Sequential xs ->
                        let xs = xs |> List.filter (not << isSysObjCtor)

                        match List.rev xs, o.Parent with
                        | [ x ], _ -> initTail x
                        // (`{ inherit Base(args); Own = x }` when Base has a primary constructor)
                        | Fable.Value(Fable.NewRecord(values, ent, _), r) :: Fable.Call(callee,
                                                                                        call,
                                                                                        Fable.DeclaredType(baseRef,
                                                                                                           bArgs),
                                                                                        cr) :: before,
                          Some p when
                            ent.FullName = o.FullName
                            && baseRef.FullName = p.FullName
                            && isConstructorCall com call
                            && values.Length >= ownFields.Length
                            ->
                            let bArgs =
                                if call.GenericArgs.IsEmpty then
                                    bArgs
                                else
                                    call.GenericArgs

                            let callExpr =
                                Fable.Call(
                                    callee,
                                    { call with
                                        ThisArg = Some(Fable.IdentExpr selfId)
                                        Args = call.Args |> List.map rewriteSelf
                                        GenericArgs = bArgs
                                    },
                                    Fable.Unit,
                                    cr
                                )

                            let setsExpr = emitOwnFields values r
                            let before = before |> List.rev |> List.map rewriteSelf
                            Fable.Sequential(before @ [ callExpr; setsExpr ])
                        | rev, _ ->
                            let before = rev.Tail |> List.rev |> List.map rewriteSelf
                            Fable.Sequential(before @ [ initTail rev.Head ])
                    | Fable.IfThenElse(c, a, b, r) -> Fable.IfThenElse(rewriteSelf c, initTail a, initTail b, r)
                    | Fable.TypeCast(x, _) -> initTail x
                    | _ ->
                        report
                            e.Range
                            $"the Zig target does not support this secondary constructor of %s{o.FullName} yet"

                        e

                [
                    { m with
                        Args = args
                        Body = initTail m.Body
                    }
                ]
            | Fable.MemberDeclaration m when isExternBody m.Body -> [ { m with Body = externBody com m } ]
            | Fable.MemberDeclaration m -> [ m ]
            | Fable.ModuleDeclaration m -> membersOf m.Members
            // A top-level statement runs when the program starts, in its place among the
            // module-level values. The initializer of a type's static fields (`static let`,
            // `static member val`) gives each its first value.
            | Fable.ActionDeclaration a ->
                let rec flat (e: Fable.Expr) =
                    match e with
                    | Fable.Sequential stmts -> stmts |> List.collect flat
                    | _ -> [ e ]

                let stmts =
                    match a.Body with
                    | Fable.Call(Fable.Delegate(_, body, _, _), _, _, _) -> flat body
                    | body -> flat body

                let value (name: string) (body: Fable.Expr) (isMutable: bool) : Fable.MemberDecl =
                    {
                        Name = name
                        Args = []
                        Body = body
                        MemberRef =
                            Fable.GeneratedMember.Value(name, body.Type, isInstance = false, isMutable = isMutable)
                        IsMangled = false
                        ImplementedSignatureRef = None
                        UsedNames = Set.empty
                        XmlDoc = None
                        Tags = []
                    }

                stmts
                |> List.choose (fun stmt ->
                    match stmt with
                    | Fable.Set(Fable.IdentExpr id, Fable.FieldSet name, _, v, _) when
                        state.StaticFields.ContainsKey(id.Name + "." + name)
                        ->
                        Some(value state.StaticFields[id.Name + "." + name] v true)
                    | Fable.Value(Fable.UnitConstant, _) -> None
                    | _ ->
                        actions <- actions + 1
                        Some(value $"top_level_%d{actions}" stmt false)
                )
            | Fable.ClassDeclaration c ->
                match com.TryGetEntity c.Entity with
                | Some ent ->
                    for f in ent.FSharpFields do
                        if f.IsStatic then
                            let name =
                                c.Name
                                + "__static_"
                                + System.Text.RegularExpressions.Regex.Replace(f.Name, "[^A-Za-z0-9_]", "_")

                            state.StaticFields[c.Name + "." + f.Name] <- name
                            // (a function of several arguments is kept uncurried, as in an
                            // object's field)
                            staticTypes[name] <- FableTransforms.uncurryType f.FieldType
                | None -> ()

                match com.TryGetEntity c.Entity with
                | Some ent when ent.IsInterface ->
                    try
                        entOf (newCtx c.Name) None c.Entity |> ignore
                    with ZigError(msg, r) ->
                        report r msg
                // (an attribute: only the compiler looks at it)
                | Some ent when
                    (match ent.BaseType with
                     | Some bt -> bt.Entity.FullName = "System.Attribute"
                     | None -> false)
                    ->
                    ()
                // a class deriving from System.Exception: its constructor makes the exception,
                // of the message given to the base constructor and its fields
                | Some ent when isExceptionClass ent ->
                    try
                        tryExnEnt (newCtx c.Name) None c.Entity |> ignore

                        let message =
                            match c.BaseCall with
                            | Some(Fable.Call(_, info, _, _)) ->
                                match info.Args with
                                | msg :: _ when msg.Type = Fable.String -> msg
                                | _ ->
                                    Fable.Value(
                                        Fable.StringConstant $"Exception of type '%s{ent.FullName}' was thrown.",
                                        None
                                    )
                            | _ ->
                                Fable.Value(
                                    Fable.StringConstant $"Exception of type '%s{ent.FullName}' was thrown.",
                                    None
                                )

                        let fields =
                            (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                            |> List.map (fun f -> f.Name)

                        match c.Constructor with
                        | Some ctor ->
                            let finish (values: Fable.Expr list) =
                                Fable.Value(Fable.NewRecord(message :: values, c.Entity, []), None)

                            attached.Add
                                { ctor with
                                    Body =
                                        constructorBodyWith fields (fieldDefaults (newCtx c.Name) ent) finish ctor.Body
                                }
                        | None -> report None $"the Zig target needs a primary constructor of %s{c.Name}"

                        for m in c.AttachedMembers do
                            report
                                m.Body.Range
                                $"the Zig target does not support this kind of member of an exception class yet (%s{c.Name}.%s{m.Name})"
                    with ZigError(msg, r) ->
                        report r msg
                // a class deriving from `Dictionary` or `HashSet` with members only: its
                // constructor makes the collection, by the base constructor
                | Some ent when
                    (collectionBase
                        com
                        (Fable.DeclaredType(
                            c.Entity,
                            ent.GenericParameters
                            |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                        )))
                        .IsSome
                    ->
                    let collectionType =
                        (collectionBase
                            com
                            (Fable.DeclaredType(
                                c.Entity,
                                ent.GenericParameters
                                |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                            )))
                            .Value

                    match c.Constructor, c.BaseCall with
                    | Some ctor, Some(Fable.Call(callee, info, _, r)) ->
                        // (Fable types the base constructor's call as unit: it makes the collection)
                        let baseCall = Fable.Call(callee, info, collectionType, r)

                        let body =
                            match ctor.Body with
                            | Fable.Value(Fable.UnitConstant, _) -> baseCall
                            | body -> Fable.Sequential [ body; baseCall ]

                        attached.Add { ctor with Body = body }
                    | _ -> report None $"the Zig target needs a primary constructor of %s{c.Name}"

                    for m in c.AttachedMembers do
                        report
                            m.Body.Range
                            $"the Zig target does not support this kind of member of a collection's subclass yet (%s{c.Name}.%s{m.Name})"
                | Some ent when
                    not (ent.IsFSharpExceptionDeclaration || ent.IsFSharpModule)
                    && (try
                            (objInfo (newCtx c.Name) None c.Entity).IsSome
                        with ZigError(msg, r) ->
                            report r msg
                            false)
                    ->
                    // a class that takes part in inheritance: its constructor computes its
                    // chain of fields; its type and tables of virtual members are emitted
                    let o = (objInfo (newCtx c.Name) None c.Entity).Value

                    try
                        match c.Constructor with
                        | Some ctor ->
                            let selfId, args =
                                match ctor.Args with
                                | first :: _ when first.IsThisArgument -> first, ctor.Args
                                | _ ->
                                    let s = objSelfIdent o
                                    s, s :: ctor.Args

                            attached.Add
                                { ctor with
                                    Args = args
                                    Body =
                                        objConstructorBody
                                            o
                                            selfId
                                            (fieldDefaults (newCtx c.Name) ent)
                                            c.BaseCall
                                            ctor.Body
                                }
                        | None -> ()

                        state.Objs.Add(objDecl (newCtx c.Name) None o (dotnetTypeName com ent))
                    with ZigError(msg, r) ->
                        report r msg

                    // what it overrides, its `default` members, and what it implements
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            let info = com.TryGetMember m.MemberRef

                            let compiled =
                                match info with
                                | Some info -> implFnName com info
                                | None -> m.Name

                            if m.Name = "ToString" then
                                Some { m with Name = c.Name + "__ToString" }
                            elif
                                compiled.Contains "."
                                || (
                                    match info with
                                    | Some info ->
                                        info.IsOverrideOrExplicitInterfaceImplementation || info.IsDispatchSlot
                                    | None -> false
                                )
                            then
                                Some { m with Name = implName c.Name compiled }
                            else
                                report
                                    m.Body.Range
                                    $"the Zig target does not support this kind of member yet (%s{c.Name}.%s{m.Name})"

                                None
                        )
                    )
                | Some ent when not (ent.IsFSharpExceptionDeclaration || ent.IsFSharpModule) ->
                    try
                        entOf (newCtx c.Name) None c.Entity |> ignore

                        // a class: its constructor makes the object
                        match c.Constructor with
                        | Some ctor when not (ent.IsFSharpRecord || ent.IsFSharpUnion) ->
                            let genArgs =
                                ent.GenericParameters
                                |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))

                            let fields =
                                (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                                |> List.map (fun f -> f.Name)

                            attached.Add
                                { ctor with
                                    Body =
                                        constructorBody
                                            c.Entity
                                            genArgs
                                            fields
                                            (fieldDefaults (newCtx c.Name) ent)
                                            ctor.Body
                                }
                        | _ -> ()
                    with ZigError(msg, r) ->
                        report r msg

                    // What a type overrides or implements is a function like its other members:
                    // `ToString`, and the members of the interfaces it implements.
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            let compiled =
                                match com.TryGetMember m.MemberRef with
                                | Some info -> implFnName com info
                                | None -> m.Name

                            if m.Name = "ToString" then
                                Some { m with Name = c.Name + "__ToString" }
                            elif m.Name = "Equals" || m.Name = "GetHashCode" then
                                Some { m with Name = c.Name + "__" + m.Name }
                            elif compiled.Contains "." then
                                Some { m with Name = implName c.Name compiled }
                            else
                                report
                                    m.Body.Range
                                    $"the Zig target does not support this kind of member yet (%s{c.Name}.%s{m.Name})"

                                None
                        )
                    )
                | Some ent when ent.IsFSharpExceptionDeclaration ->
                    try
                        tryExnEnt (newCtx c.Name) None c.Entity |> ignore
                    with ZigError(msg, r) ->
                        report r msg
                | _ -> report None $"the Zig target does not support this kind of type declaration yet (%s{c.Name})"

                []
        )

    let decls = membersOf file.Declarations

    // (a static field that nothing initializes, `[<DefaultValue>] static val mutable`: its
    // default value)
    let decls =
        let given = decls |> List.map (fun d -> d.Name) |> set

        let defaults =
            staticTypes
            |> Seq.filter (fun kv -> not (given.Contains kv.Key))
            |> Seq.map (fun kv ->
                let body =
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
                        Fable.CallInfo.Create(genArgs = [ kv.Value ]),
                        kv.Value,
                        None
                    )

                ({
                    Name = kv.Key
                    Args = []
                    Body = body
                    MemberRef = Fable.GeneratedMember.Value(kv.Key, kv.Value, isInstance = false, isMutable = true)
                    IsMangled = false
                    ImplementedSignatureRef = None
                    UsedNames = Set.empty
                    XmlDoc = None
                    Tags = []
                }
                : Fable.MemberDecl)
            )
            |> List.ofSeq

        defaults @ decls

    let decls = decls @ List.ofSeq attached

    // (for work on the target: what Fable hands over for a file)
    if System.Environment.GetEnvironmentVariable "FABLE_ZIG_DUMP" = "1" then
        for d in file.Declarations do
            eprintfn "DUMP %A" d

    /// the type parameters of the type a member is of
    let typeParamsOfType (info: Fable.MemberFunctionOrValue) : string list =
        match info.DeclaringEntity |> Option.bind com.TryGetEntity with
        | Some ent when not ent.IsFSharpModule -> ent.GenericParameters |> List.map (fun g -> g.Name)
        | _ -> []

    /// (the implementation of a generic method of an interface: its slot has the method's type
    /// parameters erased to `obj`, and so has it)
    let isErasedImpl (info: Fable.MemberFunctionOrValue) =
        info.IsOverrideOrExplicitInterfaceImplementation
        && info.CompiledName.Contains "."
        && not info.GenericParameters.IsEmpty

    /// the type parameters of a function: those of the type it is a member of, then its own
    let typeParamsOf (info: Fable.MemberFunctionOrValue) : string list =
        let ofType = typeParamsOfType info

        if isErasedImpl info then
            ofType
        else
            ofType @ (info.GenericParameters |> List.map (fun g -> g.Name)) |> List.distinct

    let effBodyType (info: Fable.MemberFunctionOrValue) (body: Fable.Expr) =
        match info.ReturnParameter.Type with
        | Fable.Nullable(_, false) as n when unwrapNullness n = unwrapNullness body.Type -> n
        | _ -> body.Type

    // What the file declares is known before any body is lowered: bodies call each other.
    for d in decls do
        let info = com.GetMember d.MemberRef

        try
            reserved.Add d.Name |> ignore

            let retFable = effBodyType info d.Body

            if info.IsValue then
                let ty = mapType (newCtx d.Name) d.Body.Range retFable

                // (a static field can be assigned: it is `static let mutable` or the field
                // behind `static member val`)
                members[d.Name] <-
                    if info.IsMutable || state.StaticFields.ContainsValue d.Name then
                        MValue ty
                    else
                        MConst ty
            else
                members[d.Name] <-
                    MFunction(
                        typeParamsOf info,
                        // (a member without parameters, as `[<CLIEvent>]` makes, takes unit)
                        (if d.Args.IsEmpty && not (isEntryPoint info) then
                             [ Fable.Unit ]
                         else
                             d.Args |> List.map (fun a -> a.Type)),
                        retFable
                    )
        with ZigError(msg, r) ->
            report r msg

    for d in decls do
        let info = com.GetMember d.MemberRef
        let typeParams = typeParamsOf info

        let inObjCtor =
            info.IsConstructor
            && (
                match info.DeclaringEntity with
                | Some cls ->
                    (try
                        (objInfo (newCtx d.Name) None cls).IsSome
                     with ZigError _ ->
                         false)
                | None -> false
            )

        let hasNoTailCallsAtt (atts: Fable.Attribute seq) =
            atts
            |> Seq.exists (fun a -> a.Entity.FullName.EndsWith("NoTailCallsAttribute", System.StringComparison.Ordinal))

        let mutable localNoTailCalls = hasNoTailCallsAtt info.Attributes

        if localNoTailCalls then
            state.NoTailCalls.Add d.Name |> ignore

        let rootModule = com.GetRootModule(com.CurrentFile) |> fst

        let rec checkDeclaringEnt (entRefOpt: Fable.EntityRef option) =
            match entRefOpt |> Option.bind com.TryGetEntity with
            | Some ent ->
                if hasNoTailCallsAtt ent.Attributes then
                    if ent.IsFSharpModule && ent.FullName = rootModule then
                        state.NoTailCallsFile <- true
                    else
                        localNoTailCalls <- true
                        state.NoTailCalls.Add d.Name |> ignore

                checkDeclaringEnt ent.DeclaringEntity
            | None -> ()

        checkDeclaringEnt info.DeclaringEntity

        let ctx =
            { newCtx d.Name with
                TypeParams = typeParams
                InCtor = inObjCtor
                NoTailCalls = state.NoTailCallsFile || localNoTailCalls
            }

        // (an erased implementation: its own type parameters, and those Fable names in its types
        // from the interface's declaration, are `obj` in its body)
        let erasedHere =
            if isErasedImpl info then
                let ofType = set (typeParamsOfType info)

                let rec gens (t: Fable.Type) =
                    match t with
                    | Fable.GenericParam(n, _, _) -> [ n ]
                    | t -> t.Generics |> List.collect gens

                (info.GenericParameters |> List.map (fun g -> g.Name))
                @ (d.Body.Type :: (d.Args |> List.map (fun a -> a.Type)) |> List.collect gens)
                |> List.distinct
                |> List.filter (fun g -> not (ofType.Contains g) && not (state.GenAliases.ContainsKey g))
            else
                []

        for g in erasedHere do
            state.GenAliases[g] <- tAny

        try
            let retFable = effBodyType info d.Body

            if info.IsValue then
                match members.TryGetValue d.Name, lw ctx (wrapNullCast retFable d.Body) with
                | (true, MConst ty), ELit(text, _) -> state.Consts.Add((d.Name, ty, text))
                // A value that is not a literal is computed when the program starts, by a
                // function of its own, and kept until the program ends.
                | (true, (MConst ty | MValue ty)), body ->
                    let body = coerceTy ctx ty body

                    if true then
                        let init = uniqueName ctx (d.Name + "_init")
                        state.Values.Add((d.Name, ty, init))

                        state.Fns.Add
                            {
                                Name = init
                                TypeParams = []
                                Params = []
                                Modes = []
                                Ret = ty
                                Body = body
                                RetFrom = None
                                Raises = RNever
                                Stores = false
                                IsLocal = false
                                IsEntryPoint = false
                                Range = d.Body.Range
                                NoEscape = []
                                BodyK = None
                                StoreFacts = [], false, false
                                AssertedNoRaise = []
                                AssertedStores = []
                                NeedsChain = false
                                PendingChainDeps = []
                                BodyTc = None
                            }
                | _ -> () // its type was rejected above
            else
                let entry = isEntryPoint info

                let args =
                    if d.Args.IsEmpty then
                        [ AST.makeTypedIdent Fable.Unit "unitVar" ]
                    else
                        d.Args

                let ps =
                    if
                        entry
                        && (d.Args.IsEmpty || d.Args |> List.forall (fun a -> a.Type = Fable.Unit))
                    then
                        [] // (`main ()`)
                    else
                        args
                        |> List.map (fun a ->
                            // (the object a member is called on is not null: the call checks)
                            let ty =
                                match mapType ctx a.Range a.Type with
                                | TOpt t when t = tObj && a.IsThisArgument -> tObj
                                | ty -> ty

                            let v = state.NewVar(a.Name, ty, VParam, false)
                            ctx.Vars[a.Name] <- v
                            v
                        )

                let ret = mapType ctx d.Body.Range retFable
                let d = { d with Body = wrapNullCast retFable (typeTaskBuilders d.Body) }

                // `[<StackArena(bytes)>]`: what the function allocates comes from its stack
                match
                    info.Attributes
                    |> Seq.tryFind (fun a ->
                        a.Entity.FullName.EndsWith("StackArenaAttribute", System.StringComparison.Ordinal)
                    )
                with
                | Some att ->
                    let bytes =
                        match att.ConstructorArgs with
                        | [ :? int as n ] -> n
                        | _ -> fail d.Body.Range "[<StackArena>] needs its size in bytes, as a literal"

                    if isManaged ret || ps |> List.exists (fun p -> isManaged p.Ty) then
                        fail
                            d.Body.Range
                            "%s: a [<StackArena>] function cannot take or give values that live on the heap (they would outlive the arena)"
                            d.Name

                    state.Arenas[d.Name] <- bytes
                | None -> ()

                let body =
                    let raw = lw ctx d.Body

                    if ret = tVoid then
                        raw
                    else
                        coerceTy ctx ret raw

                // a test (xUnit's `[<Fact>]`, NUnit's `[<Test>]`): `zig test` runs it
                if
                    info.Attributes
                    |> Seq.exists (fun a ->
                        let n = a.Entity.FullName

                        n.EndsWith("FactAttribute", System.StringComparison.Ordinal)
                        || n.EndsWith(".TestAttribute", System.StringComparison.Ordinal)
                    )
                then
                    state.Tests.Add((info.DisplayName, d.Name))

                // a function given to C (`[<UnmanagedCallersOnly(EntryPoint = "name")>]`): a
                // wrapper of C's calling convention is exported under the name (see Emit)
                if
                    info.Attributes
                    |> Seq.exists (fun a ->
                        a.Entity.FullName = "System.Runtime.InteropServices.UnmanagedCallersOnlyAttribute"
                    )
                then
                    if not typeParams.IsEmpty then
                        fail d.Body.Range "%s: a function given to C cannot be generic" d.Name

                    if isManaged ret || ps |> List.exists (fun p -> isManaged p.Ty && p.Ty <> tStr) then
                        fail
                            d.Body.Range
                            "%s: a function given to C takes numbers, bools and strings and gives numbers, bools or nothing"
                            d.Name

                    let symbol =
                        attEntryPoint "System.Runtime.InteropServices.UnmanagedCallersOnlyAttribute" info
                        |> Option.defaultValue info.CompiledName

                    state.Exports.Add((d.Name, symbol))

                state.Fns.Add
                    {
                        Name = d.Name
                        TypeParams = typeParams
                        Params = ps
                        Modes = ps |> List.map (fun _ -> MPlain)
                        Ret = ret
                        Body = body
                        RetFrom = None
                        Raises = RNever
                        Stores = false
                        IsLocal = false
                        IsEntryPoint = entry
                        Range = d.Body.Range
                        NoEscape = []
                        BodyK = None
                        StoreFacts = [], false, false
                        AssertedNoRaise = []
                        AssertedStores = []
                        NeedsChain = false
                        PendingChainDeps = []
                        BodyTc = None
                    }
        with
        // (an `inline` member: F# puts its body in at each use, which compile on their own; its
        // compiled body, which the target cannot make, is never called)
        | ZigError _ when
            (match d.MemberRef with
             | Fable.MemberRef _ ->
                 match com.TryGetMember d.MemberRef with
                 | Some m -> m.IsInline
                 | None -> false
             | _ -> false)
            ->
            ()
        | ZigError(msg, r) ->
            report
                (match r with
                 | Some _ -> r
                 | None -> d.Body.Range)
                msg
        // (a case the target did not foresee: an error at the declaration, not a crash of the
        // whole file)
        | e when not (e :? System.OutOfMemoryException) ->
            report
                d.Body.Range
                $"internal error of the Zig target while compiling %s{d.Name}: %s{e.GetType().Name}: %s{e.Message}"

        for g in erasedHere do
            state.GenAliases.Remove g |> ignore

    settleCyclic state
    settleCycles state
    state
