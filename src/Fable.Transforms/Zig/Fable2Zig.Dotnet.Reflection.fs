/// .NET Reflection, FSharpReflection, Enum runtime parse/names, and Activator.CreateInstance lowering.
module internal Fable.Transforms.Zig.DotnetReflection

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

/// `Activator.CreateInstance` of a type known here, by one of its constructors (its name, its
/// member and the types of its parameters): the call, with the arguments unboxed to the
/// parameters' types, the object as `t`
let private activatorNew
    (ctx: Ctx)
    (r: SourceLocation option)
    (entRef: Fable.EntityRef)
    (gargs: Fable.Type list)
    (ctorName: string, ctorRef: Fable.MemberRef, ps: Fable.Type list)
    (args: Fable.Expr list)
    (t: Fable.Type)
    : Fable.Expr
    =
    let made = Fable.DeclaredType(entRef, gargs)

    let subst =
        match ctx.Com.TryGetEntity entRef with
        | Some ent when ent.GenericParameters.Length = gargs.Length ->
            List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) gargs
            |> Map.ofList
        | _ -> Map.empty

    let ps = ps |> List.map (substFableType subst)

    // (a constructor of no parameters takes unit)
    let args =
        match ps, args with
        | [ Fable.Unit ], [] -> [ Fable.Value(Fable.UnitConstant, None) ]
        | _ -> args

    let args =
        List.map2
            (fun (p: Fable.Type) (a: Fable.Expr) ->
                match a with
                | Fable.TypeCast(inner, Fable.Any) when inner.Type = p -> inner
                | _ when a.Type = p -> a
                | _ -> Fable.TypeCast(a, p)
            )
            ps
            args

    let ctorType =
        Fable.LambdaType(
            (match ps with
             | [ p ] -> p
             | _ -> Fable.Tuple(ps, false)),
            made
        )

    let call =
        Fable.Call(
            Fable.IdentExpr(AST.makeTypedIdent ctorType ctorName),
            Fable.CallInfo.Create(args = args, sigArgTypes = ps, genArgs = gargs, memberRef = ctorRef),
            made,
            r
        )

    Fable.TypeCast(call, t)

/// How many arguments a constructor of these parameters takes (none for unit)
let private ctorArity (ps: Fable.Type list) =
    match ps with
    | [ Fable.Unit ] -> 0
    | _ -> ps.Length

/// A call of a .NET member of the library, as Fable writes one
let private dotnetMember
    (path: string)
    (selector: string)
    (thisArg: Fable.Expr option)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (r: SourceLocation option)
    =
    Fable.Call(
        Fable.Import(
            {
                Selector = selector
                Path = Replacements.DotnetPrefix + path
                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = thisArg.IsSome))
            },
            Fable.Any,
            None
        ),
        Fable.CallInfo.Create(?thisArg = thisArg, args = args),
        t,
        r
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
    // ---- reflection: the runtime's fable_reflect.zig ----
    // (`FSharpValue.GetUnionFields(v, t, allowAccessToPrivateRepresentation = true)`: an extension
    // of FSharp.Core's, the same member)
    | "Microsoft.FSharp.Reflection.FSharpReflectionExtensions", extName, _ when
        extName.StartsWith("FSharpValue.", System.StringComparison.Ordinal)
        || extName.StartsWith("FSharpType.", System.StringComparison.Ordinal)
        ->
        let owner = extName.Substring(0, extName.IndexOf '.')
        let rest = extName.Substring(extName.IndexOf '.' + 1)

        let memberName =
            if rest.EndsWith ".Static" then
                rest.Substring(0, rest.Length - 7)
            else
                rest

        dotnetCall ctx r ("Microsoft.FSharp.Reflection." + owner) memberName info t
    // (`Enum.Parse<'T>(s)`: of the type's information, as the value)
    | "System.Enum", "Parse", (s :: rest) when info.GenericArgs.Length = 1 && s.Type = Fable.String ->
        let enumT = info.GenericArgs.Head

        let typeOfT =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "TypeOf"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(genArgs = [ enumT ]),
                Fable.MetaType,
                r
            )

        let parsed =
            dotnetCall
                ctx
                r
                "System.Enum"
                "Parse"
                { info with
                    GenericArgs = []
                    ThisArg = None
                    Args = typeOfT :: s :: rest
                }
                Fable.Any

        bindArgs ctx [ parsed ] (fun xs -> ERt("fable_rt.unbox($R, $0)", xs, mapType ctx r enumT))
    // (`Enum.GetNames(t)` and the others of a Type)
    | "System.Enum",
      ("GetUnderlyingType" | "GetNames" | "GetValues" | "GetName" | "IsDefined" | "Parse"),
      (t0 :: _ as args) when t0.Type = Fable.MetaType ->
        ctx.State.UsesRuntime <- true

        match name, args with
        | "GetUnderlyingType", [ x ] ->
            rt "fable_rt.reflect.enumUnderlyingType($0)" [ x ] (TPrim "fable_rt.reflect.Type")
        | "GetNames", [ x ] -> rt "fable_rt.reflect.enumNames($0)" [ x ] (mapType ctx r t)
        | "GetValues", [ x ] -> rt "fable_rt.reflect.enumValues($0)" [ x ] (mapType ctx r t)
        | "GetName", [ x; v ] -> rt "fable_rt.reflect.enumName($0, $1)" [ x; Fable.TypeCast(v, Fable.Any) ] tStr
        | "IsDefined", [ x; v ] -> rt "fable_rt.reflect.enumIsDefined($0, $1)" [ x; Fable.TypeCast(v, Fable.Any) ] tBool
        | "Parse", [ x; v ] -> rt "fable_rt.reflect.enumParse($0, $1, false)" [ x; v ] tAny
        | "Parse", [ x; v; ignoreCase ] -> rt "fable_rt.reflect.enumParse($0, $1, $2)" [ x; v; ignoreCase ] tAny
        | _ -> fail r "the Zig target does not support Enum.%s with these arguments yet" name
    // (Fable.Core.Reflection: of an object, by what its box says of its type)
    | "Fable.Core.Reflection",
      ("isUnion" | "isRecord" | "getCaseTag" | "getCaseName" | "getCaseFields" | "getRecordFields"),
      [ o ] ->
        ctx.State.UsesRuntime <- true
        ctx.State.UsesReflection <- true

        let fn, ty =
            match name with
            | "isUnion" -> "objectIsUnion", tBool
            | "isRecord" -> "objectIsRecord", tBool
            | "getCaseTag" -> "objectCaseTag", tI32
            | "getCaseName" -> "objectCaseName", tStr
            | "getCaseFields" -> "objectCaseFields", mapType ctx r t
            | _ -> "objectRecordFields", mapType ctx r t

        rt $"fable_rt.reflect.%s{fn}($0)" [ Fable.TypeCast(o, Fable.Any) ] ty
    | ("Microsoft.FSharp.Core.Operators" | "System.Type" | "System.Object" | "System.Exception" | "Microsoft.FSharp.Reflection.FSharpType" | "Microsoft.FSharp.Reflection.FSharpValue" | "System.Reflection.PropertyInfo" | "System.Reflection.MemberInfo" | "Microsoft.FSharp.Reflection.UnionCaseInfo"),
      name,
      args when
        (entity <> "System.Exception" || name = "GetType")
        && (entity <> "Microsoft.FSharp.Core.Operators"
            || name = "TypeOf"
            || name = "TypeDefOf"
            || (name = "IsNull" && args |> List.exists (fun a -> a.Type = Fable.MetaType)))
        && (entity <> "System.Object"
            || name = "GetType"
            || (name = "ReferenceEquals"
                && args |> List.forall (fun a -> (let (Unboxed i) = a in i.Type = Fable.MetaType))))
        ->
        ctx.State.UsesRuntime <- true
        let tType = TPrim "fable_rt.reflect.Type"

        // (the information of a type: of a record, a union, a tuple... from its Zig type; a class,
        // an interface or an enum by its .NET name)
        let rec typeExpr (t: Fable.Type) : string =
            let named (ent: Fable.Entity) (kind: string) (genArgs: Fable.Type list) =
                let args =
                    match genArgs with
                    | [] -> ""
                    | gs ->
                        gs
                        |> List.map (fun g -> IR.zigType (mapType ctx r g))
                        |> String.concat ", "
                        |> sprintf ", .args = .{ %s }"

                // (the type's own type parameters, as these arguments)
                let subst (x: Fable.Type) =
                    let pairs =
                        List.zip
                            (ent.GenericParameters |> List.map (fun p -> p.Name))
                            (if genArgs.Length = ent.GenericParameters.Length then
                                 genArgs
                             else
                                 ent.GenericParameters |> List.map (fun _ -> Fable.Any))
                        |> Map.ofList

                    let rec go (x: Fable.Type) =
                        match x with
                        | Fable.GenericParam(n, _, _) when pairs.ContainsKey n -> pairs[n]
                        | Fable.DeclaredType(e, gs) -> Fable.DeclaredType(e, List.map go gs)
                        | other -> other

                    go x

                let parent =
                    match ent.BaseType with
                    | Some b when kind = ".@\"enum\"" -> ""
                    | Some b when b.Entity.FullName = "System.Object" -> ""
                    | Some b ->
                        match b.Entity.Path with
                        | Fable.SourcePath _ ->
                            $", .parent = %s{typeExpr (subst (Fable.DeclaredType(b.Entity, b.GenericArgs)))}"
                        // (a class of .NET's: by its name)
                        | _ ->
                            $", .parent = fable_rt.reflect.named(.{{ .full_name = \"%s{b.Entity.FullName}\", .kind = .class }})"
                    | None -> ""

                let interfaces =
                    match List.ofSeq ent.DeclaredInterfaces with
                    | [] -> ""
                    | ifs ->
                        ifs
                        |> List.map (fun i -> typeExpr (subst (Fable.DeclaredType(i.Entity, i.GenericArgs))))
                        |> String.concat ", "
                        |> sprintf ", .interfaces = .{ %s }"

                let underlying =
                    if kind = ".@\"enum\"" then
                        let numberType =
                            ent.FSharpFields
                            |> List.tryFind (fun f -> f.Name = "value__")
                            |> Option.map (fun f -> IR.zigType (mapType ctx r f.FieldType))
                            |> Option.defaultValue "i32"

                        // (the cases: names and values)
                        let cases =
                            ent.FSharpFields
                            |> List.filter (fun f -> f.Name <> "value__")
                            |> List.choose (fun f ->
                                match f.LiteralValue with
                                | Some v -> Some(f.Name, System.Convert.ToInt64 v)
                                | None -> None
                            )

                        let names = cases |> List.map (fun (n, _) -> $"\"%s{n}\"") |> String.concat ", "
                        let values = cases |> List.map (fun (_, v) -> $"%d{v}") |> String.concat ", "

                        let valueList =
                            if cases.IsEmpty then
                                ""
                            else
                                $"@as(i64, %s{values})"

                        $", .underlying = %s{numberType}, .enum_names = [_][]const u8{{ %s{names} }}, .enum_values = [_]i64{{ %s{values} }}"
                    else
                        ""

                $"fable_rt.reflect.named(.{{ .full_name = \"%s{dotnetTypeName ctx.Com ent}\", .kind = %s{kind}%s{args}%s{parent}%s{interfaces}%s{underlying} }})"

            match t with
            | Fable.Number(_, Fable.NumberInfo.IsEnum entRef) ->
                match ctx.Com.TryGetEntity entRef with
                | Some ent -> named ent ".@\"enum\"" []
                | None -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"
            | Fable.DeclaredType(entRef, genArgs) ->
                match ctx.Com.TryGetEntity entRef with
                // (an erased union of one field: the type it erases to)
                | Some ent when
                    ent.IsFSharpUnion
                    && ent.Attributes
                       |> Seq.exists (fun a -> a.Entity.FullName = "Fable.Core.EraseAttribute")
                    && ent.UnionCases.Length = 1
                    && ent.UnionCases.Head.UnionCaseFields.Length = 1
                    ->
                    let field = ent.UnionCases.Head.UnionCaseFields.Head.FieldType

                    let pairs =
                        List.zip (ent.GenericParameters |> List.map (fun p -> p.Name)) genArgs
                        |> Map.ofList

                    let rec go (x: Fable.Type) =
                        match x with
                        | Fable.GenericParam(n, _, _) when pairs.ContainsKey n -> pairs[n]
                        | Fable.DeclaredType(e, gs) -> Fable.DeclaredType(e, List.map go gs)
                        | other -> other

                    typeExpr (go field)
                | Some ent when ent.IsInterface -> named ent ".interface" genArgs
                | Some ent when
                    not ent.IsFSharpRecord
                    && not ent.IsFSharpUnion
                    && (
                        match entRef.Path with
                        | Fable.SourcePath _ -> true
                        | _ -> false
                    )
                    ->
                    named ent ".class" genArgs
                | _ when libraryValueTypes.ContainsKey entRef.FullName ->
                    $"fable_rt.reflect.named(.{{ .full_name = \"%s{entRef.FullName}\", .kind = .class }})"
                | _ -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"
            | _ -> $"fable_rt.reflect.typeOf(%s{IR.zigType (mapType ctx r t)})"

        let typeOfIr (t: Fable.Type) = EEmit(typeExpr t, [], tType)

        // (a boxed argument: the type it is of, when it is known here)
        let staticTypeOf (x: Fable.Expr) =
            let (Unboxed inner) = x
            inner.Type

        let rfl (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            rt $"fable_rt.reflect.%s{fn}(%s{holes})" xs ty

        let pureRfl (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            pure' $"fable_rt.reflect.%s{fn}(%s{holes})" xs ty

        // (the optional `allowAccessToPrivateRepresentation` and binding flags: nothing here)
        let isFlag (x: Fable.Expr) =
            match x.Type with
            | Fable.Option(Fable.Boolean, _) -> true
            | Fable.Option(Fable.Number(_, Fable.NumberInfo.IsEnum _), _)
            | Fable.Number(_, Fable.NumberInfo.IsEnum _) -> true
            | _ -> false

        let args = args |> List.filter (fun a -> not (isFlag a) && a.Type <> Fable.Unit)
        let resultTy = mapType ctx r t

        // (a value of a type known here: its type's information and the value boxed)
        let withType (o: Fable.Expr) (k: Expr -> Expr -> Expr) =
            let st = staticTypeOf o

            let typeIr =
                if st = Fable.Any then
                    // (an object: what its box says)
                    ctx.State.UsesReflection <- true

                    bindArgs
                        ctx
                        [ lw ctx (Fable.TypeCast(o, Fable.Any)) ]
                        (fun xs -> ERt("fable_rt.reflect.typeOfObject($0)", xs, tType))
                else
                    typeOfIr st

            bindArgs ctx [ typeIr; lw ctx (Fable.TypeCast(o, Fable.Any)) ] (fun xs -> k xs.[0] xs.[1])

        match entity, name, args with
        | _, "TypeOf", [] -> typeOfIr info.GenericArgs.Head
        | _, "TypeDefOf", [] -> EEmit($"fable_rt.reflect.definitionOf(%s{typeExpr info.GenericArgs.Head})", [], tType)
        | "System.Object", "GetType", [ Unboxed inner as x ] when unwrapNullness inner.Type = Fable.Any ->
            ctx.State.UsesReflection <- true
            rfl "typeOfObject" [ x ] tType
        // (an exception: its class, known when the program runs)
        | _, "GetType", [ x ] when mapType ctx r x.Type = TPrim "fable_rt.Exn" ->
            ctx.State.UsesReflection <- true
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.reflect.typeOfExn($0)", xs, tType))
        | "System.Object", "GetType", [ x ] -> bindArgs ctx [ lw ctx x ] (fun _ -> typeOfIr x.Type)
        // (two Type objects: the same type information)
        | "System.Object", "ReferenceEquals", [ Unboxed a; Unboxed b ] -> pure' "($0 == $1)" [ a; b ] tBool
        // System.Type
        | _, ("get_FullName" | "get_Name" | "get_Namespace" | "ToString"), [ x ] when
            unwrapNullness x.Type = Fable.MetaType
            || (
                match unwrapNullness x.Type with
                | Fable.DeclaredType(e, _) -> e.FullName = "System.Type"
                | _ -> false
            )
            ->
            let fn =
                match name with
                | "get_FullName" -> "fullName"
                | "get_Name" -> "name"
                | "get_Namespace" -> "namespace"
                | _ -> "toString"

            pureRfl fn [ x ] tStr
        | _, "get_IsGenericType", [ x ] -> pureRfl "isGenericType" [ x ] tBool
        | _, "get_IsGenericTypeDefinition", [ x ] -> pureRfl "isGenericTypeDefinition" [ x ] tBool
        | _, "get_IsArray", [ x ] -> pureRfl "isArray" [ x ] tBool
        | _, "get_IsEnum", [ x ] -> pureRfl "isEnum" [ x ] tBool
        | _, "get_IsClass", [ x ] -> pureRfl "isClass" [ x ] tBool
        | _, "get_IsInterface", [ x ] -> pureRfl "isInterface" [ x ] tBool
        | _, "GetElementType", [ x ] -> pureRfl "elementOrNull" [ x ] tType
        | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] -> pureRfl "isNullType" [ x ] tBool
        | _, "IsSubclassOf", [ a; b ] -> pureRfl "isSubclassOf" [ a; b ] tBool
        | _, "GetInterface", [ x; n ] ->
            pureRfl "getInterface" [ x; n; Fable.Value(Fable.BoolConstant false, None) ] tType
        | _, "GetInterface", [ x; n; ignoreCase ] -> pureRfl "getInterface" [ x; n; ignoreCase ] tType
        | _, "GetEnumUnderlyingType", [ x ] -> rfl "enumUnderlyingType" [ x ] tType
        | _, "GetEnumNames", [ x ] -> rfl "enumNames" [ x ] resultTy
        | _, "GetEnumValues", [ x ] -> rfl "enumValues" [ x ] resultTy
        | _, "IsAssignableFrom", [ a; b ] -> pureRfl "isAssignableFrom" [ a; b ] tBool
        // (a value whose type cannot hold others (a record, a union, a number...): by that type;
        // an object: by its class)
        | _, "IsInstanceOfType", [ x; o ] ->
            let (Unboxed inner) = o

            let dynamic =
                match inner.Type with
                | Fable.Any -> true
                | Fable.DeclaredType(e, _) ->
                    (objInfo ctx r e).IsSome
                    || (
                        match ctx.Com.TryGetEntity e with
                        | Some ent -> ent.IsInterface
                        | None -> false
                    )
                | _ -> false

            if dynamic then
                ctx.State.UsesReflection <- true
                pureRfl "isInstanceOf" [ x; Fable.TypeCast(inner, Fable.Any) ] tBool
            else
                bindArgs
                    ctx
                    [ lw ctx x; lw ctx inner; typeOfIr inner.Type ]
                    (fun xs -> EEmit("fable_rt.reflect.isAssignableFrom($0, $2)", xs, tBool))
        | _, "GetGenericTypeDefinition", [ x ] -> rfl "genericDefinition" [ x ] tType
        | _, ("get_GenericTypeArguments" | "GetGenericArguments"), [ x ] -> pureRfl "genericArguments" [ x ] resultTy
        | _, "Equals", [ a; b ] -> pureRfl "equals" [ a; b ] tBool
        // FSharpType
        | "Microsoft.FSharp.Reflection.FSharpType", ("IsRecord" | "IsUnion" | "IsTuple" | "IsFunction"), [ x ] ->
            pureRfl (name.Substring(0, 1).ToLowerInvariant() + name.Substring 1) [ x ] tBool
        | "Microsoft.FSharp.Reflection.FSharpType", "GetRecordFields", [ x ] -> rfl "recordFields" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetUnionCases", [ x ] -> rfl "unionCases" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetTupleElements", [ x ] -> rfl "tupleElements" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "GetFunctionElements", [ x ] ->
            rfl "functionElements" [ x ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpType", "MakeTupleType", [ xs ] -> pureRfl "makeTupleType" [ xs ] tType
        // FSharpValue
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetRecordFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getRecordFields($0, $1)", [ t; v ], resultTy))
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetTupleFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getTupleFields($0, $1)", [ t; v ], resultTy))
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetTupleField", [ o; i ] ->
            withType
                o
                (fun t v ->
                    bindArgs
                        ctx
                        [ lw ctx i ]
                        (fun is -> ERt("fable_rt.reflect.getTupleField($0, $1, $2)", [ t; v; is.Head ], resultTy))
                )
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetRecordField", [ o; p ] ->
            rfl "getRecordField" [ o; p ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeRecord", [ ty; vals ] ->
            rfl "makeRecord" [ ty; vals ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeTuple", [ vals; ty ] -> rfl "makeTuple" [ vals; ty ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "MakeUnion", [ c; vals ] -> rfl "makeUnion" [ c; vals ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetUnionFields", [ o; ty ] ->
            rfl "getUnionFields" [ ty; o ] resultTy
        | "Microsoft.FSharp.Reflection.FSharpValue", "GetUnionFields", [ o ] ->
            withType o (fun t v -> ERt("fable_rt.reflect.getUnionFields($0, $1)", [ t; v ], resultTy))
        // PropertyInfo, UnionCaseInfo
        | _, "get_Name", [ x ] when
            (match x.Type with
             | Fable.DeclaredType(e, _) -> e.FullName.EndsWith "PropertyInfo" || e.FullName.EndsWith "MemberInfo"
             | _ -> false)
            ->
            pureRfl "propertyName" [ x ] tStr
        | _, "get_PropertyType", [ x ] -> pureRfl "propertyType" [ x ] tType
        | _, "GetValue", p :: o :: _ -> rfl "propertyValue" [ p; o ] resultTy
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_Name", [ c ] -> pureRfl "caseName" [ c ] tStr
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_Tag", [ c ] -> pureRfl "caseTag" [ c ] tI32
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "GetFields", [ c ] -> pureRfl "caseFieldsOf" [ c ] resultTy
        | "Microsoft.FSharp.Reflection.UnionCaseInfo", "get_DeclaringType", [ c ] ->
            pureRfl "caseDeclaringType" [ c ] tType
        // `def.MakeGenericType(args)`: the type, where its definition and arguments are known
        // here (see staticTypeOf); else made when the program runs
        | _, "MakeGenericType", [ def; typeArgs ] ->
            let items =
                match typeArgs with
                | Fable.Value(Fable.NewArray(Fable.ArrayValues ts, _, _), _) -> Some ts
                | _ -> None

            let known =
                match Fable.Transforms.Zig.LowerHelpers.staticTypeOf ctx def, items with
                | Some(Fable.DeclaredType(ent, gs)), Some ts when gs.Length = ts.Length ->
                    let ks = ts |> List.map (Fable.Transforms.Zig.LowerHelpers.staticTypeOf ctx)

                    if ks |> List.forall Option.isSome then
                        Some(Fable.DeclaredType(ent, ks |> List.map Option.get))
                    else
                        None
                | _ -> None

            match known with
            | Some t -> bindArgs ctx [ lw ctx def; lw ctx typeArgs ] (fun _ -> typeOfIr t)
            | None -> rfl "makeGenericType" [ def; typeArgs ] tType
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet (%A)"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
                (args |> List.map (fun a -> a.Type))
    // (`Activator.CreateInstance(t)` of a number, a char, a bool, without arguments: its default,
    // boxed; of `obj`: a new object)
    | "System.Activator", "CreateInstance", t0 :: rest when
        (match rest with
         | []
         | [ Fable.Value(Fable.NewArray(Fable.ArrayValues [], _, _), _) ] -> true
         | _ -> false)
        && (
            match Fable.Transforms.Zig.LowerHelpers.staticTypeOf ctx t0 with
            | Some(Fable.Number _ | Fable.Char | Fable.Boolean | Fable.Any) -> true
            | _ -> false
        )
        ->
        ctx.State.UsesRuntime <- true

        match Fable.Transforms.Zig.LowerHelpers.staticTypeOf ctx t0 with
        | Some Fable.Any -> pure' "fable_rt.objectNew()" [] tAny
        | Some ty -> EEmit($"fable_rt.box(fable_rt.defaultOf(%s{zigType (mapType ctx r ty)}))", [], tAny)
        | None -> failwith "unreachable"
    // `Activator.CreateInstance(t, args)` of a type known here with the arguments in an array
    // known only when the program runs: the constructor with as many parameters as it has items
    // (.NET's MissingMethodException when there is none)
    | "System.Activator", "CreateInstance", [ t0; arr ] when
        (match staticTypeOf ctx t0 with
         | Some(Fable.DeclaredType(ent, _)) -> fileCtors().ContainsKey ent.FullName
         | _ -> false)
        && (
            match arr with
            | Fable.Value(Fable.NewArray _, _) -> false
            | _ ->
                match arr.Type with
                | Fable.Array(Fable.Any, _) -> true
                | _ -> false
        )
        ->
        let entRef, gargs =
            match staticTypeOf ctx t0 with
            | Some(Fable.DeclaredType(e, gs)) -> e, gs
            | _ -> failwith "unreachable"

        let items = AST.makeTypedIdent arr.Type "ctorArgs"
        let itemsExpr = Fable.IdentExpr items

        let length =
            dotnetMember "System.Array" "get_Length" (Some itemsExpr) [] (Fable.Number(Int32, Fable.NumberInfo.Empty)) r

        let missing =
            let message =
                let name =
                    match ctx.Com.TryGetEntity entRef with
                    | Some ent -> dotnetTypeName ctx.Com ent
                    | None -> entRef.FullName

                Fable.Value(Fable.StringConstant $"Constructor on type '%s{name}' not found.", None)

            Fable.Extended(
                Fable.Throw(
                    Some(
                        dotnetMember
                            "System.MissingMethodException"
                            ".ctor"
                            None
                            [ message ]
                            (Fable.DeclaredType(
                                {
                                    FullName = "System.MissingMethodException"
                                    Path = Fable.CoreAssemblyName "System.Runtime"
                                },
                                []
                            ))
                            r
                    ),
                    t
                ),
                r
            )

        let byCount =
            fileCtors().[entRef.FullName]
            |> List.distinctBy (fun (_, _, ps) -> ctorArity ps)
            |> List.rev
            |> List.fold
                (fun otherwise ((_, _, ps) as ctor) ->
                    let args =
                        List.init
                            (ctorArity ps)
                            (fun i ->
                                dotnetMember
                                    "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
                                    "GetArray"
                                    None
                                    [ itemsExpr; AST.makeIntConst i ]
                                    Fable.Any
                                    r
                            )

                    Fable.IfThenElse(
                        AST.makeEqOp r length (AST.makeIntConst (ctorArity ps)) BinaryEqual,
                        activatorNew ctx r entRef gargs ctor args t,
                        otherwise,
                        r
                    )
                )
                missing

        lw ctx (Fable.Let(items, arr, byCount))
    // `Activator.CreateInstance(t, args)` of a type known here (`MakeGenericType` of known types,
    // see `staticTypeOf`): the constructor of that type with as many parameters, called with the
    // arguments unboxed to their types, the object boxed
    | "System.Activator", "CreateInstance", t0 :: rest when
        (match staticTypeOf ctx t0 with
         | Some(Fable.DeclaredType(ent, _)) -> fileCtors().ContainsKey ent.FullName
         | _ -> false)
        ->
        let entRef, gargs =
            match staticTypeOf ctx t0 with
            | Some(Fable.DeclaredType(e, gs)) -> e, gs
            | _ -> failwith "unreachable"

        let args =
            match rest with
            | [ Fable.Value(Fable.NewArray(Fable.ArrayValues xs, _, _), _) ] -> xs
            | xs -> xs

        match
            fileCtors().[entRef.FullName]
            |> List.tryFind (fun (_, _, ps) -> ctorArity ps = args.Length)
        with
        | Some ctor -> lw ctx (activatorNew ctx r entRef gargs ctor args t)
        | None -> fail r "the Zig target found no constructor of %s with %d parameters" entRef.FullName args.Length
    // `new 'T()` of a type parameter that is not known here: an inline function's own body,
    // which Zig looks at only if something calls it (its callers have it inlined)
    | ("Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions" | "System.Activator"), "CreateInstance", _ when
        info.ThisArg.IsNone
        ->
        EEmit(
            "@compileError(\"fable: new 'T() needs a type known where it is used (an inline function)\")",
            [],
            mapType ctx r t
        )
    | _ -> Unchecked.defaultof<Expr>
