/// System.IO, System.Environment, System.Text.RegularExpressions, System.Guid, and System.Uri lowering.
module internal Fable.Transforms.Zig.DotnetIoRegex

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
    // ---- files, directories, paths, the environment: the library's Path.fs and fable_io.zig ----
    | ("System.IO.Path" | "System.IO.File" | "System.IO.Directory" | "System.IO.DirectoryInfo" | "System.Environment"),
      name,
      args when
        not (
            entity = "System.Environment"
            && name <> "GetEnvironmentVariable"
            && name <> "get_CurrentDirectory"
        )
        ->
        let call fn xs =
            libraryCall
                ctx
                r
                "Path"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let io (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            ctx.State.UsesRuntime <- true
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            rt $"fable_rt.io.%s{fn}(%s{holes})" xs ty

        let pure'' (fn: string) (xs: Fable.Expr list) (ty: Ty) =
            ctx.State.UsesRuntime <- true
            let holes = xs |> List.mapi (fun i _ -> $"${i}") |> String.concat ", "
            pure' $"fable_rt.io.%s{fn}(%s{holes})" xs ty

        let lowerFirst (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        let boolConst (b: bool) = Fable.Value(Fable.BoolConstant b, None)

        // (Path.Combine(a, b, c) and the array form: an array of the parts)
        let partsArray (parts: Fable.Expr list) =
            match parts with
            | [ single ] when
                (match single.Type with
                 | Fable.Array _ -> true
                 | _ -> false)
                ->
                single
            | _ -> Fable.Value(Fable.NewArray(Fable.ArrayValues parts, Fable.String, Fable.MutableArray), None)

        match entity, name, args with
        // Path
        | "System.IO.Path",
          ("GetFileName" | "GetExtension" | "HasExtension" | "GetFileNameWithoutExtension" | "GetDirectoryName" | "IsPathRooted" | "GetPathRoot"),
          [ p ] -> call (lowerFirst name) [ p ]
        | "System.IO.Path", "ChangeExtension", [ p; e ] -> call "changeExtension" [ p; e ]
        | "System.IO.Path", "Combine", parts -> call "combineAll" [ partsArray parts ]
        | "System.IO.Path", "Join", parts -> call "joinAll" [ partsArray parts ]
        | "System.IO.Path", "GetFullPath", [ p ] -> io "fullPath" [ p ] tStr
        | "System.IO.Path", "GetTempPath", [] -> pure'' "tempPath" [] tStr
        | "System.IO.Path", "GetTempFileName", [] -> io "tempFileName" [] tStr
        | "System.IO.Path", "GetRandomFileName", [] -> pure'' "randomFileName" [] tStr
        | "System.IO.Path",
          ("get_DirectorySeparatorChar" | "get_AltDirectorySeparatorChar" | "get_PathSeparator" | "get_VolumeSeparatorChar"),
          [] -> call (lowerFirst (name.Substring 4)) [ Fable.Value(Fable.UnitConstant, None) ]
        | "System.IO.Path", ("GetInvalidFileNameChars" | "GetInvalidPathChars"), [] ->
            call (lowerFirst name) [ Fable.Value(Fable.UnitConstant, None) ]
        // File
        | "System.IO.File", "ReadAllText", p :: _ -> io "readAllText" [ p ] tStr
        | "System.IO.File", "ReadAllBytes", [ p ] -> io "readAllBytes" [ p ] (mapType ctx r t)
        | "System.IO.File", "WriteAllText", p :: text :: _ -> io "writeAllText" [ p; text; boolConst false ] tVoid
        | "System.IO.File", "AppendAllText", p :: text :: _ -> io "writeAllText" [ p; text; boolConst true ] tVoid
        | "System.IO.File", "WriteAllBytes", [ p; bytes ] -> io "writeAllBytes" [ p; bytes ] tVoid
        | "System.IO.File", "ReadAllLines", p :: _ -> call "readAllLines" [ p ]
        | "System.IO.File", "WriteAllLines", p :: lines :: _ when
            (match lines.Type with
             | Fable.Array _ -> true
             | _ -> false)
            ->
            call "writeAllLines" [ p; lines ]
        | "System.IO.File", "AppendAllLines", p :: lines :: _ when
            (match lines.Type with
             | Fable.Array _ -> true
             | _ -> false)
            ->
            call "appendAllLines" [ p; lines ]
        | "System.IO.File", "Exists", [ p ] -> pure'' "fileExists" [ p ] tBool
        | "System.IO.File", "Delete", [ p ] -> io "deleteFile" [ p ] tVoid
        | "System.IO.File", "Copy", [ a; b ] ->
            io "copyFile" [ a; b; Fable.Value(Fable.BoolConstant false, None) ] tVoid
        | "System.IO.File", "Copy", [ a; b; o ] -> io "copyFile" [ a; b; o ] tVoid
        | "System.IO.File", "Move", [ a; b ] ->
            io "moveFile" [ a; b; Fable.Value(Fable.BoolConstant false, None) ] tVoid
        | "System.IO.File", "Move", [ a; b; o ] -> io "moveFile" [ a; b; o ] tVoid
        // Directory
        | "System.IO.Directory", "Exists", [ p ] -> pure'' "dirExists" [ p ] tBool
        | "System.IO.Directory", "CreateDirectory", [ p ] -> call "createDirectory" [ p ]
        | "System.IO.Directory", "Delete", [ p ] -> io "deleteDirectory" [ p ] tVoid
        | "System.IO.Directory", "GetCurrentDirectory", [] -> pure'' "currentDirectory" [] tStr
        | "System.IO.DirectoryInfo", "get_FullName", [ d ] -> call "directoryInfoFullName" [ d ]
        | "System.IO.DirectoryInfo", "get_Name", [ d ] -> call "directoryInfoName" [ d ]
        // Environment
        | "System.Environment", "GetEnvironmentVariable", [ n ] -> pure'' "getEnv" [ n ] tStr
        | "System.Environment", "get_CurrentDirectory", [] -> pure'' "currentDirectory" [] tStr
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
    // ---- regular expressions: the library's Regex.fs ----
    | ("System.Text.RegularExpressions.Regex" | "System.Text.RegularExpressions.Match" | "System.Text.RegularExpressions.Group" | "System.Text.RegularExpressions.Capture" | "System.Text.RegularExpressions.MatchCollection" | "System.Text.RegularExpressions.GroupCollection"),
      name,
      args ->
        let call fn xs =
            libraryCall
                ctx
                r
                "Regex"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                    SignatureArgTypes = []
                }
                xs
                t

        let typeName (x: Fable.Expr) =
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName.Substring(e.FullName.LastIndexOf '.' + 1)
            | _ -> ""

        let regexType =
            Fable.DeclaredType(
                {
                    FullName = "System.Text.RegularExpressions.Regex"
                    Path = Fable.CoreAssemblyName "System.Text.RegularExpressions"
                },
                []
            )

        let int32 (x: Fable.Expr) =
            Fable.TypeCast(x, Fable.Number(Int32, Fable.NumberInfo.Empty))

        let zero =
            Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 0, Fable.NumberInfo.Empty), None)

        // (a static member's regex: a new one of the pattern and the options)
        let made (pattern: Fable.Expr) (options: Fable.Expr option) =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = ".ctor"
                        Path = Replacements.DotnetPrefix + "System.Text.RegularExpressions.Regex"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(
                    args =
                        (match options with
                         | Some o -> [ pattern; o ]
                         | None -> [ pattern ])
                ),
                regexType,
                r
            )

        let isString (x: Fable.Expr) = x.Type = Fable.String

        // (a MatchEvaluator: a function of the match)
        let replaceIn (re: Fable.Expr) (input: Fable.Expr) (rep: Fable.Expr) (rest: Fable.Expr list) =
            let fn, count =
                if isString rep then
                    "replace", "replaceCount"
                else
                    "replaceWith", "replaceWithCount"

            match rest with
            | [] -> call fn [ re; input; rep ]
            | [ c ] -> call count [ re; input; rep; c ]
            | [ c; s ] ->
                call
                    (fn
                     + if isString rep then
                           "From"
                       else
                           "From")
                    [ re; input; rep; c; s ]
            | _ -> fail r "the Zig target does not support this Regex.Replace yet"

        let isRegex (x: Fable.Expr) =
            x.Type = Fable.Regex || typeName x = "Regex"

        let isMatch (x: Fable.Expr) = typeName x = "Match"

        match name, args with
        // Regex
        | ".ctor", [ p ] -> call "ofPattern" [ p ]
        | ".ctor", [ p; o ] -> call "create" [ p; int32 o ]
        | ".ctor", [ p; o; _timeout ] -> call "create" [ p; int32 o ]
        | "Escape", [ s ] -> call "escape" [ s ]
        | "Unescape", [ s ] -> call "unescape" [ s ]
        | "IsMatch", [ re; s ] when isRegex re -> call "isMatch" [ re; s ]
        | "IsMatch", [ re; s; at ] when isRegex re -> call "isMatchFrom" [ re; s; at ]
        | "IsMatch", s :: p :: rest -> call "isMatch" [ made p (List.tryHead rest); s ]
        | "Match", [ re; s ] when isRegex re -> call "matchOf" [ re; s ]
        | "Match", [ re; s; at ] when isRegex re -> call "matchFrom" [ re; s; at ]
        | "Match", s :: p :: rest -> call "matchOf" [ made p (List.tryHead rest); s ]
        | "Matches", [ re; s ] when isRegex re -> call "matches" [ re; s ]
        | "Matches", [ re; s; at ] when isRegex re -> call "matchesFrom" [ re; s; at ]
        | "Matches", s :: p :: rest -> call "matches" [ made p (List.tryHead rest); s ]
        | "Replace", re :: s :: rep :: rest when isRegex re -> replaceIn re s rep rest
        | "Replace", s :: p :: rep :: rest -> replaceIn (made p (List.tryHead rest)) s rep []
        | "Split", [ re; s ] when isRegex re -> call "split" [ re; s ]
        | "Split", [ re; s; c ] when isRegex re -> call "splitCount" [ re; s; c ]
        | "Split", [ re; s; c; at ] when isRegex re -> call "splitFrom" [ re; s; c; at ]
        | "Split", s :: p :: rest -> call "split" [ made p (List.tryHead rest); s ]
        | "get_Options", [ re ] -> call "options" [ re ]
        | "GetGroupNames", [ re ] -> call "getGroupNames" [ re ]
        | "GetGroupNumbers", [ re ] -> call "getGroupNumbers" [ re ]
        | "ToString", [ re ] when isRegex re -> call "toString" [ re ]
        // Match (also a Group), Group
        | "get_Groups", [ m ] -> call "groups" [ m ]
        | "NextMatch", [ m ] -> call "nextMatch" [ m ]
        | ("get_Success" | "get_Index" | "get_Length" | "get_Value" | "get_Name"), [ g ] ->
            let field = name.Substring 4

            call
                ((if isMatch g then
                      "match"
                  else
                      "group")
                 + field)
                [ g ]
        | "ToString", [ g ] ->
            call
                (if isMatch g then
                     "matchValue"
                 else
                     "groupToString")
                [ g ]
        // the collections
        | "get_Count", [ c ] ->
            call
                (if typeName c = "MatchCollection" then
                     "matchesCount"
                 else
                     "groupsCount")
                [ c ]
        | "get_Item", [ c; i ] when typeName c = "MatchCollection" -> call "matchAt" [ c; i ]
        | "get_Item", [ c; key ] when isString key -> call "groupNamed" [ c; key ]
        | "get_Item", [ c; i ] -> call "groupAt" [ c; i ]
        | _ ->
            fail
                r
                "the Zig target does not support %s.%s with these arguments yet"
                (entity.Substring(entity.LastIndexOf '.' + 1))
                name
    // ---- `System.Guid`: the library's Guid.fs ----
    | "System.Guid", name, args when
        (match name with
         | ".ctor"
         | "NewGuid"
         | "CreateVersion7"
         | "get_Empty"
         | "Parse"
         | "TryParse"
         | "ToString"
         | "ToByteArray" -> true
         | _ -> false)
        ->
        let unitArg = [ Fable.Value(Fable.UnitConstant, None) ]

        let call fn xs =
            libraryCall
                ctx
                r
                "Guid"
                fn
                { info with
                    ThisArg = None
                    GenericArgs = []
                }
                xs
                t

        match name, args with
        | (".ctor" | "get_Empty"), [] -> call "create" unitArg
        | ".ctor", [ s ] when unwrapNullness s.Type = Fable.String -> call "parse" [ s ]
        | ".ctor", [ bytes ] -> call "ofBytes" [ bytes ]
        | "NewGuid", [] -> call "newGuid" unitArg
        | "CreateVersion7", [] -> call "createVersion7" unitArg
        | "CreateVersion7", [ d ] -> call "createVersion7Of" [ d ]
        | "Parse", [ s ] -> call "parse" [ s ]
        | "TryParse", [ s ] -> call "tryParse" [ s ]
        // (`Guid.TryParse(s, &g)`: the Guid goes to `g`)
        | "TryParse", [ s; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]

            let pairIr =
                libraryCall
                    ctx
                    r
                    "Guid"
                    "tryParse"
                    { info with ThisArg = None }
                    [ s ]
                    (Fable.Tuple([ Fable.Boolean; out.Type ], false))

            let pair = ctx.State.NewVar("parsed", typeOf pairIr, VLocal, false)

            ELet(
                pair,
                pairIr,
                ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool))
            )
        | "ToString", [ g ] -> call "toString" [ g ]
        | "ToString", [ g; format ] -> call "toStringFormat" [ g; format ]
        | "ToByteArray", [ g ] -> call "toByteArray" [ g ]
        | _ -> fail r "the Zig target does not support Guid.%s with these arguments yet" name
    // ---- `System.Uri`: the library's Uri.fs ----
    | "System.Uri", ".ctor", args ->
        let fn =
            match args with
            | [ _ ] -> "create"
            | [ _; kind ] when
                unwrapNullness kind.Type <> Fable.String
                && (
                    match unwrapNullness kind.Type with
                    | Fable.DeclaredType(e, _) -> e.FullName <> "System.Uri"
                    | _ -> true
                )
                ->
                "createWithKind"
            | [ _; rel ] when unwrapNullness rel.Type = Fable.String -> "createFromBase"
            | _ -> "createFromBaseUri"

        libraryCall ctx r "Uri" fn { info with ThisArg = None } args t
    // (`Uri.TryCreate(s, kind, &uri)`: the URI goes to `uri`)
    | "System.Uri", "TryCreate", [ a; b; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
        ctx.Vars.ContainsKey out.Name
        ->
        let outVar = ctx.Vars[out.Name]

        let fn =
            if unwrapNullness a.Type = Fable.String then
                "tryCreate"
            else
                "tryCreateFromBase"

        let pairT = Fable.Tuple([ Fable.Boolean; out.Type ], false)
        let pairIr = libraryCall ctx r "Uri" fn info [ a; b ] pairT
        let pair = ctx.State.NewVar("created", typeOf pairIr, VLocal, false)

        ELet(pair, pairIr, ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool)))
    | "System.Uri", "TryCreate", [ a; b ] ->
        let fn =
            if unwrapNullness a.Type = Fable.String then
                "tryCreate"
            else
                "tryCreateFromBase"

        libraryCall ctx r "Uri" fn info [ a; b ] t
    | "System.Uri", getter, [ u ] when
        getter.StartsWith("get_", System.StringComparison.Ordinal)
        || getter = "ToString"
        ->
        let fn =
            if getter = "ToString" then
                "toString"
            else
                let n = getter.Substring 4
                n.Substring(0, 1).ToLowerInvariant() + n.Substring 1

        libraryCall ctx r "Uri" fn { info with ThisArg = None } [ u ] t
    | _ -> Unchecked.defaultof<Expr>
