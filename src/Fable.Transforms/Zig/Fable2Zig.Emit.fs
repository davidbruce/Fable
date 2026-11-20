/// Emission: ownership IR -> Zig source text.
module Fable.Transforms.Zig.Emit

open System.Collections.Generic
open System.Text
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.EmitExpr
open Fable.Transforms.Zig.EmitStmt
open Fable.Transforms.Zig.EmitDecls
open Fable.Transforms.Zig.EmitFunction

/// A resource's hooks, as declarations the runtime looks for: `fable_destroy`, `fable_dup`.
/// `fable_rt.Hook(file, "name")` of a function of this file or of another (`alias.name`)
let hookOf (fn: string) =
    match fn.IndexOf '.' with
    | -1 -> $"fable_rt.Hook(@\"$file\", \"%s{topIdent fn}\")"
    | i -> $"fable_rt.Hook(%s{fn.Substring(0, i)}, \"%s{topIdent (fn.Substring(i + 1))}\")"

let hookDecls (e: Ent) (ind: string) : string =
    let overrides =
        e.Overrides
        |> List.map (fun (decl, fn) ->
            if fn = "" then
                $"%s{ind}    pub const %s{decl} = {{}};\n"
            else
                $"%s{ind}    pub const %s{decl} = %s{hookOf fn};\n"
        )
        |> String.concat ""

    overrides
    + match e.Hooks with
      | Some(destroy, dup) ->
          let targs = e.TypeParams |> List.map genName |> String.concat ", "

          let one (name: string) (fn: string) =
              let rhs =
                  if List.isEmpty e.TypeParams then
                      callTarget fn
                  else
                      $"%s{callTarget fn}(%s{targs}).call"

              $"%s{ind}    pub const %s{name} = %s{rhs};\n"

          one "fable_destroy" destroy
          + (
              match dup with
              | Some d -> one "fable_dup" d
              | None -> ""
          )
      | None -> ""

/// The text of one file, without its imports (their paths are only known to the writer).
let emitFile (state: FileState) : string =
    currentArenas.Value.Value <- state.Arenas
    let out = StringBuilder()
    let rootNames = HashSet<string>([ "result"; "hole"; "tail"; "env" ])
    let fableAliases = HashSet<string>(state.Imports.Values)
    let specialNoTc = HashSet<string>()

    for (n, _) in state.Exports do
        specialNoTc.Add n |> ignore

    for (_, n) in state.Tests do
        specialNoTc.Add n |> ignore

    for (_, _, n) in state.Values do
        specialNoTc.Add n |> ignore

    for e in state.Ents.Values do
        match e.Hooks with
        | Some(destroy, dupOpt) ->
            specialNoTc.Add destroy |> ignore
            Option.iter (fun d -> specialNoTc.Add d |> ignore) dupOpt
        | None -> ()

    for fn in state.Fns do
        if fn.IsEntryPoint then
            specialNoTc.Add fn.Name |> ignore

    let noTailCalls =
        if state.NoTailCallsFile then
            let s = HashSet<string>()

            for fn in state.Fns do
                s.Add fn.Name |> ignore

            s
        else
            HashSet<string>(state.NoTailCalls)

    for n in noTailCalls do
        specialNoTc.Add n |> ignore

    for (name, _, _) in state.Consts do
        rootNames.Add(topIdent name) |> ignore

    for (name, _, _) in state.Values do
        rootNames.Add(topIdent name) |> ignore

    for fn in state.Fns do
        rootNames.Add(topIdent fn.Name) |> ignore

    for alias in state.Imports.Values do
        rootNames.Add alias |> ignore

    for alias in state.UserImports.Values do
        rootNames.Add alias |> ignore

    for e in state.LocalEnts do
        rootNames.Add(topIdent e.Name) |> ignore

    // What this file's code does that lets a function value be part of a cycle, joined with
    // what the files it uses say (see `fable_rt.functions_in_cycles`).
    let cyc = state.Cycles

    let used =
        match
            state.Imports.Values
            |> Seq.sort
            |> Seq.map (fun alias -> alias + ".@\"$cycles\"")
            |> List.ofSeq
        with
        | [] -> ".{}"
        | items -> items |> String.concat ", " |> sprintf ".{ %s }"

    let b (x: bool) =
        if x then
            "true"
        else
            "false"

    out
        .AppendLine(
            $"pub const @\"$cycles\" = fable_rt.joinCycles(.{{ .holds = %s{b cyc.Holds}, .generic = %s{b cyc.Generic}, .instantiated = %s{b cyc.Instantiated}, .captures = %s{b cyc.Captures}, .cap_generic = %s{b cyc.CapGeneric}, .cap_instantiated = %s{b cyc.CapInstantiated}, .stack_traces = %s{b state.UsesStackTrace}, .reflection = %s{b state.UsesReflection}, .exn_show = __FABLE_EXN_SHOW__, .oom_catch = %s{b state.CatchesOom}, .uses_arena = %s{b (state.Arenas.Count > 0)} }}, %s{used});"
        )
        .AppendLine()
    |> ignore

    // (what reflection says of a record or a union: `fable_type`, its .NET name and what it is,
    // and its type arguments)
    let netTypeDecl (e: Ent) (ind: string) =
        match state.NetTypes.TryGetValue e.Name with
        | true, (fullName, kind) ->
            let args =
                match e.TypeParams with
                | [] -> ""
                | ps -> ps |> List.map genName |> String.concat ", " |> sprintf ", .args = .{ %s }"

            let kindLit =
                if kind = "union" then
                    ".@\"union\""
                else
                    ".record"

            $"%s{ind}    pub const fable_type = .{{ .full_name = \"%s{fullName}\", .kind = %s{kindLit}%s{args} }};\n"
        | _ -> ""

    for e in state.LocalEnts do
        let fields (fs: (string * Ty) list) =
            fs |> List.map (fun (f, t) -> $"%s{fieldIdent f}: %s{zigType t}")

        // (a type parameter none of the fields mention, a unit of measure, is `_`: Zig refuses
        // an unused parameter)
        let fieldText =
            (e.Cases
             |> List.collect (fun (_, fs) -> fs |> List.map (snd >> zigType))
             |> String.concat " ")
            + hookDecls e ""
            + netTypeDecl e ""

        let comptimeParam (g: string) =
            if fieldText.Contains(genName g) then
                $"comptime %s{genName g}: type"
            else
                "comptime _: type"

        // A generic type is a Zig function from its type arguments to the type.
        let opening, closing, ind =
            match e.TypeParams with
            | [] -> (fun (kind: string) -> $"pub const %s{topIdent e.Name} = %s{kind} {{"), "};", ""
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

                (fun (kind: string) ->
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return %s{kind} {{"
                ),
                "    };\n}",
                "    "

        match e.Kind with
        | KRefRecord ->
            // a pointer to a counted cell that holds the fields
            let decl =
                match cyclicDecl e with
                | Some verdict -> $"pub const fable_cyclic = %s{verdict}; "
                | None -> ""

            let payload =
                decl
                + (hookDecls e "").Replace("\n", " ").Trim()
                + " "
                + (netTypeDecl e "").Replace("\n", " ").Trim()
                + " "
                + (cellHeader e @ fields (snd e.Cases.Head) |> String.concat ", ")

            match e.TypeParams with
            | [] ->
                out.Append($"pub const %s{topIdent e.Name} = *struct {{ %s{payload} }}")
                |> ignore
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

                out.Append(
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return *struct {{ %s{payload} }};\n}}"
                )
                |> ignore
        | KExn ->
            let payload = fields (snd e.Cases.Head) |> String.concat ", "

            out.Append(
                $"pub const %s{topIdent e.Name} = fable_rt.ExnOf(\"%s{e.Ref.DisplayName}\", struct {{ %s{payload} }})"
            )
            |> ignore
        | KIface ->
            let methods = snd e.Cases.Head

            let ifaceFields =
                ("@\"$meta\": *const fable_rt.IfaceMeta" :: fields methods)
                @ (methods
                   |> List.map (fun (m, _) -> $"@\"%s{cleanIdent m}$tc\": ?fable_rt.TailFn = null"))
                |> String.concat ", "

            match e.TypeParams with
            | [] ->
                out.Append($"pub const %s{topIdent e.Name} = fable_rt.Iface(struct {{ %s{ifaceFields} }})")
                |> ignore
            | typeParams ->
                let comptimeParams = typeParams |> List.map comptimeParam |> String.concat ", "

                out.Append(
                    $"pub fn %s{topIdent e.Name}(%s{comptimeParams}) type {{\n    return fable_rt.Iface(struct {{ %s{ifaceFields} }});\n}}"
                )
                |> ignore
        | KRecord ->
            let container =
                match e.Layout with
                | LayoutAuto -> "struct"
                | LayoutExtern _ -> "extern struct"
                | LayoutUnion -> "extern union"

            out.AppendLine(opening container) |> ignore
            out.Append(hookDecls e ind) |> ignore
            out.Append(netTypeDecl e ind) |> ignore

            for (fname, fty) in snd e.Cases.Head do
                let ts = zigType fty

                match e.Layout with
                | LayoutExtern(Some p) when p > 0 ->
                    out.AppendLine($"%s{ind}    %s{fieldIdent fname}: %s{ts} align(@min(%d{p}, @alignOf(%s{ts}))),")
                    |> ignore
                | _ -> out.AppendLine($"%s{ind}    %s{fieldIdent fname}: %s{ts},") |> ignore
        | KValueUnion ->
            out.AppendLine(opening "union(enum)") |> ignore
            out.Append(hookDecls e ind) |> ignore
            out.Append(netTypeDecl e ind) |> ignore

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"%s{ind}    %s{fieldIdent c},") |> ignore
                else
                    let payload = fields fs |> String.concat ", "

                    out.AppendLine($"%s{ind}    %s{fieldIdent c}: struct {{ %s{payload} }},")
                    |> ignore
        | KHeapUnion ->
            // a case with fields points to a reference-counted cell; one without needs none
            out.AppendLine(opening "union(enum)") |> ignore

            match cyclicDecl e with
            | Some verdict -> out.AppendLine($"%s{ind}    pub const fable_cyclic = %s{verdict};") |> ignore
            | None -> ()

            out.Append(hookDecls e ind) |> ignore
            out.Append(netTypeDecl e ind) |> ignore

            // (the trees of `Map` and `Set`: the runtime compares and writes them by what they
            // hold, not by their shape)
            match e.Ref.FullName with
            | "Fable.Library.Zig.Map.MapTree`2" ->
                out.AppendLine($"%s{ind}    pub const fable_collection = .map;") |> ignore
            | "Fable.Library.Zig.Set.SetTree`1" ->
                out.AppendLine($"%s{ind}    pub const fable_collection = .set;") |> ignore
            | _ -> ()

            for (c, fs) in e.Cases do
                if fs.IsEmpty then
                    out.AppendLine($"%s{ind}    %s{fieldIdent c},") |> ignore
                else
                    let payload = cellHeader e @ fields fs |> String.concat ", "

                    out.AppendLine($"%s{ind}    %s{fieldIdent c}: *struct {{ %s{payload} }},")
                    |> ignore

        if e.Kind = KRefRecord || e.Kind = KIface then
            (if e.TypeParams.IsEmpty then
                 out.AppendLine(";")
             else
                 out.AppendLine())
                .AppendLine()
            |> ignore
        elif e.Kind = KExn then
            out.AppendLine(";").AppendLine() |> ignore
        else
            out.AppendLine(closing).AppendLine() |> ignore

    for (name, ty, text) in state.Consts do
        out.AppendLine($"pub const %s{topIdent name}: %s{zigType ty} = %s{text};")
        |> ignore

    if state.Consts.Count > 0 then
        out.AppendLine() |> ignore

    // the anonymous records and `.NET` fat-pointer interfaces the file uses
    let emittedIfaceAliases = HashSet<string>()

    for kv in state.Ents do
        if kv.Key.StartsWith("$anon:", System.StringComparison.Ordinal) then
            let names = kv.Key.Substring(6).Split(',')
            let quoted = names |> Array.map (fun n -> "\"" + n + "\"") |> String.concat ", "

            let alias = "fable_anon_" + String.concat "_" names

            out.AppendLine($"const %s{alias} = fable_rt.Anon%d{names.Length}(.{{ %s{quoted} }});")
            |> ignore
        elif kv.Key.StartsWith("$iface:", System.StringComparison.Ordinal) then
            let rest = kv.Key.Substring(7)

            if rest = "" then
                if emittedIfaceAliases.Add "fable_iface_0" then
                    out.AppendLine("const fable_iface_0 = fable_rt.IfaceAnon0();") |> ignore
            else
                let safe = rest.Split(',') |> Array.map cleanIdent
                let quoted = safe |> Array.map (fun n -> "\"" + n + "\"") |> String.concat ", "
                let alias = "fable_iface_" + String.concat "_" safe

                if emittedIfaceAliases.Add alias then
                    out.AppendLine($"const %s{alias} = fable_rt.IfaceAnon%d{safe.Length}(.{{ %s{quoted} }});")
                    |> ignore

    // Module-level values that are computed: each has a place, filled when the program starts
    // (after the values of the files this one uses) and given up when it ends.
    for (name, ty, _) in state.Values do
        out.AppendLine($"pub var %s{topIdent name}: %s{zigType ty} = undefined;")
        |> ignore

    let aliases = state.Imports.Values |> Seq.sort |> List.ofSeq

    let initCallees =
        (aliases |> List.map (fun alias -> alias + ".@\"$init\""))
        @ (state.Values |> Seq.map (fun (_, _, init) -> topIdent init) |> List.ofSeq)
        |> String.concat ", "

    out
        .AppendLine("var @\"$ready\": bool = false;")
        .AppendLine()
        .AppendLine($"pub fn @\"$init\"() fable_rt.MayRaise(void, .{{ %s{initCallees} }}) {{")
        .AppendLine("    if (@\"$ready\") return;")
        .AppendLine("    @\"$ready\" = true;")
    |> ignore

    for alias in aliases do
        out.AppendLine(
            $"    if (comptime fable_rt.isRaised(@TypeOf(%s{alias}.@\"$init\"()))) try %s{alias}.@\"$init\"() else %s{alias}.@\"$init\"();"
        )
        |> ignore

    for (name, _, init) in state.Values do
        let call = topIdent init + "()"

        out.AppendLine(
            $"    %s{topIdent name} = if (comptime fable_rt.isRaised(@TypeOf(%s{call}))) try %s{call} else %s{call};"
        )
        |> ignore

    out
        .AppendLine("}")
        .AppendLine()
        .AppendLine("pub fn @\"$deinit\"() void {")
        .AppendLine("    if (!@\"$ready\") return;")
        .AppendLine("    @\"$ready\" = false;")
    |> ignore

    for (name, _, _) in Seq.rev state.Values do
        out.AppendLine($"    fable_rt.drop(%s{topIdent name});") |> ignore

    for alias in List.rev aliases do
        out.AppendLine($"    %s{alias}.@\"$deinit\"();") |> ignore

    out.AppendLine("}").AppendLine() |> ignore

    let adapters = Dictionary<string, Adapter>()
    let knowns = Dictionary<string, KnownDecl>()
    let knownIfaces = Dictionary<string, KnownIfaceDecl>()
    let ifaceVts = Dictionary<string, IfaceVt>()
    let fns = Dictionary<string, FnInfo>()

    for fn in state.Fns do
        fns[fn.Name] <- fn

    emitFnsAndSccs out rootNames fableAliases specialNoTc noTailCalls adapters knowns knownIfaces ifaceVts fns state

    // the classes that take part in inheritance: the type of each, with its tables of virtual
    // members (function values of the functions that implement them)
    for d in state.Objs do
        let generic = not d.TypeParams.IsEmpty

        let emitThunk (indent: string) (name, partPtr, parts, field, fnTy) =
            match fnTy with
            | TFn(_ :: args, ret) ->
                let ps =
                    args
                    |> List.mapi (fun i t -> $"a%d{i}: %s{zigType t}")
                    |> List.map (fun p -> ", " + p)
                    |> String.concat ""

                let xs = args |> List.mapi (fun i _ -> $", a%d{i}") |> String.concat ""
                let retZig = zigType ret
                let voidRet = isVoid ret

                out
                    .AppendLine(
                        $"%s{indent}fn %s{topIdent name}(env: ?*fable_rt.Env, this: fable_rt.Obj%s{ps}) fable_rt.Raised!%s{retZig} {{"
                    )
                    .AppendLine($"%s{indent}    _ = env;")
                    .AppendLine(
                        $"%s{indent}    const f = fable_rt.dup(fable_rt.objPart(%s{zigType partPtr}, &[_]type{{ %s{parts} }}, this).%s{fieldIdent field});"
                    )
                    .AppendLine($"%s{indent}    defer fable_rt.drop(f);")
                    .AppendLine($"%s{indent}    return f.code(f.env, fable_rt.dup(this)%s{xs});")
                    .AppendLine($"%s{indent}}}")
                |> ignore

                if not state.NoTailCallsFile then
                    let restTysStr = args |> List.map zigType |> String.concat ", "

                    let callArgTysStr =
                        ("fable_rt.Obj" :: (args |> List.map zigType)) |> String.concat ", "

                    let loadTcaArgs = args |> List.mapi (fun i _ -> $"_tca[%d{i}]")
                    let fallbackArgs = loadTcaArgs |> List.map (fun s -> ", " + s) |> String.concat ""
                    let storeCallArgs = ("this_tc" :: loadTcaArgs) |> String.concat ", "

                    let emitThunkTcBody (bInd: string) =
                        out
                            .AppendLine($"%s{bInd}const _ts = fable_rt.takeSelfBorrowed(ctx);")
                            .AppendLine($"%s{bInd}const this: fable_rt.Obj = @ptrCast(@alignCast(_ts.ptr.?));")
                            .AppendLine(
                                $"%s{bInd}const f = fable_rt.dup(fable_rt.objPart(%s{zigType partPtr}, &[_]type{{ %s{parts} }}, this).%s{fieldIdent field});"
                            )
                            .AppendLine($"%s{bInd}if (comptime fable_rt.fitsTailArgs(&.{{ %s{callArgTysStr} }})) {{")
                            .AppendLine($"%s{bInd}    if (f.tcode) |tcfn| {{")
                            .AppendLine($"%s{bInd}        const this_tc = if (_ts.owned) this else fable_rt.dup(this);")
                            .AppendLine(
                                $"%s{bInd}        fable_rt.tailStore(&.{{ %s{callArgTysStr} }}, ctx, .{{ %s{storeCallArgs} }});"
                            )
                            .AppendLine($"%s{bInd}        ctx.self = f.env;")
                            .AppendLine($"%s{bInd}        ctx.self_owned = true;")
                            .AppendLine($"%s{bInd}        return @call(fable_rt.tail_call, tcfn, .{{ ctx, ret }});")
                            .AppendLine($"%s{bInd}    }}")
                            .AppendLine($"%s{bInd}}}")
                            .AppendLine($"%s{bInd}defer fable_rt.drop(f);")
                            .AppendLine($"%s{bInd}const this_own = if (_ts.owned) this else fable_rt.dup(this);")
                            .AppendLine($"%s{bInd}const raw = f.code(f.env, this_own%s{fallbackArgs});")
                            .AppendLine($"%s{bInd}const r = raw catch {{")
                            .AppendLine($"%s{bInd}    fable_rt.plugRet(%s{retZig}, ret);")
                            .AppendLine($"%s{bInd}    return .raised;")
                            .AppendLine($"%s{bInd}}};")
                        |> ignore

                        if voidRet then
                            out.AppendLine($"%s{bInd}_ = r;").AppendLine($"%s{bInd}return .ok;") |> ignore
                        else
                            out
                                .AppendLine($"%s{bInd}@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = r;")
                                .AppendLine($"%s{bInd}return .ok;")
                            |> ignore

                    out.AppendLine(
                        $"%s{indent}fn @\"%s{topIdent name}$tc\"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{"
                    )
                    |> ignore

                    if args.IsEmpty then
                        emitThunkTcBody (indent + "    ")
                    else
                        out
                            .AppendLine($"%s{indent}    if (comptime fable_rt.fitsTailArgs(&.{{ %s{restTysStr} }})) {{")
                            .AppendLine(
                                $"%s{indent}        const _tca = fable_rt.tailLoad(&.{{ %s{restTysStr} }}, ctx);"
                            )
                        |> ignore

                        emitThunkTcBody (indent + "        ")

                        out
                            .AppendLine($"%s{indent}    }} else {{")
                            .AppendLine($"%s{indent}        unreachable;")
                            .AppendLine($"%s{indent}    }}")
                        |> ignore

                    out.AppendLine($"%s{indent}}}") |> ignore
            | _ -> ()

        // (an object expression's class: each member calls the function value the object holds;
        // a generic one defines its thunks inside its type builder where the type params live)
        if not generic then
            for th in d.Thunks do
                emitThunk "" th

        let decls = System.Collections.Generic.List<string>()

        // (a function as the code of a function value: an adapter, generic in the class's type
        // parameters when the class is; class vtable / ToString adapters borrow `this`)
        let adapterFor (target: string) (typeArgs: Ty list) (fnTy: Ty) =
            let key =
                target
                + "<"
                + (typeArgs |> List.map zigType |> String.concat ",")
                + ">"
                + (if generic then
                       "/" + String.concat "," d.TypeParams
                   else
                       "")
                + "#vt"

            match adapters.TryGetValue key with
            | true, a -> a
            | _ ->
                let a =
                    {
                        Name = $"@\"%s{target}$fn%d{adapters.Count}\""
                        Target = target
                        Target2 = None
                        TypeArgs = typeArgs
                        NCaptures = 0
                        CaptureTys = []
                        FnTy = fnTy
                        BorrowFirst = true
                        NeedsTcode = not state.NoTailCallsFile
                        Gens = d.TypeParams
                    }

                adapters[key] <- a
                a

        let restFits (fnTy: Ty) =
            match fnTy with
            | TFn(_ :: restArgs, _) ->
                let restTys = restArgs |> List.map zigType |> String.concat ", "
                Some $"fable_rt.fitsTailArgs(&.{{ %s{restTys} }})"
            | _ -> None

        let tables =
            d.Tables
            |> List.mapi (fun i t ->
                match t with
                | Some(vtTy, entries) ->
                    let name = topIdent $"%s{d.TypeName}_vt%d{i}"

                    let inits =
                        entries
                        |> List.map (fun (slot, target, typeArgs, fnTy) ->
                            if target.StartsWith("@raw:", System.StringComparison.Ordinal) then
                                // (a function of this file with the calling convention of a function value)
                                let rawName = topIdent (target.Substring 5)

                                if state.NoTailCallsFile then
                                    $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{rawName} }}"
                                else
                                    let tcodeField =
                                        match restFits fnTy with
                                        | Some cond -> $"if (%s{cond}) &@\"%s{rawName}$tc\" else null"
                                        | None -> "null"

                                    $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{rawName}, .tcode = %s{tcodeField} }}"
                            else
                                let adapter = adapterFor target typeArgs fnTy

                                if state.NoTailCallsFile then
                                    $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{adapterRef adapter}.code }}"
                                else
                                    let tcodeField =
                                        match restFits fnTy with
                                        | Some cond -> $"if (%s{cond}) &%s{adapterRef adapter}.tcode else null"
                                        | None -> "null"

                                    $".%s{fieldIdent slot} = %s{zigType fnTy}{{ .env = null, .code = %s{adapterRef adapter}.code, .tcode = %s{tcodeField} }}"
                        )
                        |> String.concat ", "

                    decls.Add($"const %s{name}: %s{zigType vtTy} = .{{ %s{inits} }};")
                    "&" + name
                | None -> "null"
            )
            |> String.concat ", "

        let parent =
            match d.Parent with
            | Some p -> p
            | None -> "null"

        // (the class's ToString, as the code of a function value)
        let toString =
            match d.ToString with
            | Some(target, typeArgs) ->
                if target.StartsWith("@raw:", System.StringComparison.Ordinal) then
                    topIdent (target.Substring 5)
                else
                    let fnTy = TFn([ TPrim "fable_rt.Obj"; tVoid ], tStr)
                    $"%s{adapterRef (adapterFor target typeArgs fnTy)}.code"
            | None -> "null"

        let value =
            if d.Overrides.IsEmpty then
                $"fable_rt.objType(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString})"
            else
                let hook (name: string) (asObj: string) =
                    match d.Overrides |> List.tryFind (fun (h, _) -> h = name) with
                    | Some(_, fn) -> $"%s{hookOf fn}.%s{asObj}"
                    | None -> "null"

                let eq = hook "equals" "objEquals"
                let hs = hook "hash" "objHash"
                let cmp = hook "compare" "objCompare"

                $"fable_rt.objTypeWith(%s{zigType d.Chain}, \"%s{d.DotnetName}\", %s{parent}, &.{{ %s{tables} }}, %s{toString}, %s{eq}, %s{hs}, %s{cmp})"

        // (the interfaces the class implements, with its tables of them: `o :?> I`)
        let value =
            if d.Ifaces.IsEmpty then
                value
            else
                let entries =
                    d.Ifaces
                    |> List.map (fun (ifaceTy, slots) ->
                        let vt = ifaceVtFor ifaceVts ifaceTy IVtObj "obj" [] slots

                        $".{{ .id = fable_rt.ifaceId(%s{zigType ifaceTy}), .vt = @ptrCast(&%s{ifaceVtRef vt}.vt) }}"
                    )
                    |> String.concat ", "

                $"fable_rt.withIfaces(%s{value}, &.{{ %s{entries} }})"

        if generic then
            let comptimeParams =
                d.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            out
                .AppendLine($"pub fn %s{topIdent d.TypeName}(%s{comptimeParams}) *const fable_rt.ObjType {{")
                .AppendLine("    return &struct {")
            |> ignore

            for th in d.Thunks do
                emitThunk "        " th

            for dl in decls do
                out.AppendLine("        " + dl) |> ignore

            out.AppendLine($"        const ty: fable_rt.ObjType = %s{value};").AppendLine("    }.ty;").AppendLine("}")
            |> ignore
        else
            for dl in decls do
                out.AppendLine(dl) |> ignore

            out.AppendLine($"pub const %s{topIdent d.TypeName}: fable_rt.ObjType = %s{value};")
            |> ignore

    for k in knowns.Values do
        emitKnownDecl out fns state.NoTailCallsFile noTailCalls adapters k

    for ki in knownIfaces.Values do
        emitKnownIfaceDecl out fns ifaceVts ki

    for a in adapters.Values do
        emitAdapter out fableAliases specialNoTc fns a

    for vt in ifaceVts.Values do
        emitIfaceVt out fableAliases state.NoTailCallsFile specialNoTc fns vt

    // (a file that uses async: at the end of each test, the work it started and left waiting
    // is run on, so that it finishes within the test)
    let asyncAlias =
        state.Imports
        |> Seq.tryFind (fun kv -> System.IO.Path.GetFileNameWithoutExtension(kv.Key) = "Async")
        |> Option.map (fun kv -> kv.Value)

    for (name, fn) in state.Tests do
        let quoted = name.Replace("\\", "\\\\").Replace("\"", "\\\"")

        out
            .AppendLine("test \"" + quoted + "\" {")
            // (every test is a test of leaks too, where cells are counted: what is alive before the
            // modules' values are made is what is alive after they are given up again, so what
            // a test leaves in a module's state is not taken for a leak; each test starts from
            // the modules' first values)
            .AppendLine("    const fable_live = fable_rt.testLiveBefore();")
            .AppendLine("    try fable_rt.testInit(@\"$init\");")
            .AppendLine($"    try fable_rt.testCase(%s{callTarget fn});")
        |> ignore

        match asyncAlias with
        | Some alias -> out.AppendLine($"    try fable_rt.testCase(%s{alias}.finishPending);") |> ignore
        | None -> ()

        out.AppendLine("    @\"$deinit\"();").AppendLine("    try fable_rt.testNoLeak(fable_live);")
        |> ignore

        out.AppendLine("}") |> ignore

    // The F# entry point returns the process exit code as an int; Zig's `main` returns a u8.
    // In builds that count cells, a program that ends with cells still allocated says so.
    for fn in state.Fns do
        if fn.IsEntryPoint then
            // (`main argv`: the command line's arguments, which the program owns or which
            // are given up after it)
            let takesArgs = not fn.Params.IsEmpty

            let mainCallExpr =
                if takesArgs then
                    $"%s{topIdent fn.Name}(undefined)"
                else
                    $"%s{topIdent fn.Name}()"

            out.AppendLine($"pub const @\"$main_raises\" = fable_rt.isRaised(@TypeOf(%s{mainCallExpr}));")
            |> ignore

            out
                .AppendLine(
                    if takesArgs then
                        "pub fn main(init: @import(\"std\").process.Init.Minimal) u8 {"
                    else
                        "pub fn main() u8 {"
                )
                .AppendLine(
                    "    if (comptime fable_rt.isRaised(@TypeOf(@\"$init\"()))) (@\"$init\"() catch { fable_rt.uncaught(); return 134; }) else @\"$init\"();"
                )
            |> ignore

            if takesArgs then
                out.AppendLine("    const argv = fable_rt.io.programArgs(init.args);") |> ignore

            let call =
                if takesArgs then
                    $"%s{topIdent fn.Name}(argv)"
                else
                    $"%s{topIdent fn.Name}()"

            let argvOwned = takesArgs && (fn.Modes |> List.tryHead = Some MOwned)

            // (an exception that nothing handled ends the program, as on .NET)
            let guarded =
                match fn.Raises with
                | RNever -> call
                | RAlways -> $"%s{call} catch {{ fable_rt.uncaught(); return 134; }}"
                | RDepends _ ->
                    $"if (comptime fable_rt.isRaised(@TypeOf(%s{call}))) (%s{call} catch {{ fable_rt.uncaught(); return 134; }}) else %s{call}"

            if isVoid fn.Ret then
                out.AppendLine($"    %s{guarded};").AppendLine("    const code: i32 = 0;")
                |> ignore
            else
                out.AppendLine($"    const code: i32 = %s{guarded};") |> ignore

            if takesArgs && not argvOwned then
                out.AppendLine("    fable_rt.drop(argv);") |> ignore

            out
                .AppendLine("    @\"$deinit\"();")
                .AppendLine("    if (fable_rt.leaked()) return 70;")
                .AppendLine("    return @truncate(@as(u32, @bitCast(code)));")
                .AppendLine("}")
            |> ignore

    // The functions given to C (`[<UnmanagedCallersOnly(EntryPoint = "name")>]`): a wrapper of
    // C's calling convention, exported under the name. It makes the module values first (as
    // `main` does: once), takes a C string as a string, and ends the program on an exception
    // that nothing handled, as C cannot receive one (as .NET does).
    for (fnName, symbol) in state.Exports do
        let fn = state.Fns |> Seq.find (fun f -> f.Name = fnName)
        let ps = fn.Params |> List.indexed

        let cParams =
            ps
            |> List.filter (fun (_, p) -> not (isVoid p.Ty))
            |> List.map (fun (i, p) ->
                let ty =
                    if p.Ty = tStr then
                        "?[*:0]const u8"
                    else
                        zigType p.Ty

                $"p%d{i}: %s{ty}"
            )
            |> String.concat ", "

        let wrapper = "@\"$export_" + symbol + "\""

        out
            .AppendLine($"fn %s{wrapper}(%s{cParams}) callconv(.c) %s{zigType fn.Ret} {{")
            .AppendLine(
                "    if (comptime fable_rt.isRaised(@TypeOf(@\"$init\"()))) (@\"$init\"() catch { fable_rt.uncaught(); std.process.exit(134); }) else @\"$init\"();"
            )
        |> ignore

        let args =
            ps
            |> List.map (fun (i, p) ->
                if isVoid p.Ty then
                    "{}"
                elif p.Ty = tStr then
                    out.AppendLine($"    const a%d{i} = fable_rt.strFromCStr(p%d{i});") |> ignore

                    if fn.Modes |> List.tryItem i <> Some MOwned then
                        out.AppendLine($"    defer fable_rt.drop(a%d{i});") |> ignore

                    $"a%d{i}"
                else
                    $"p%d{i}"
            )
            |> String.concat ", "

        let call = $"%s{topIdent fn.Name}(%s{args})"

        out
            .AppendLine(
                $"    return if (comptime fable_rt.isRaised(@TypeOf(%s{call}))) (%s{call} catch {{ fable_rt.uncaught(); std.process.exit(134); }}) else %s{call};"
            )
            .AppendLine("}")
            .AppendLine($"comptime {{ @export(&%s{wrapper}, .{{ .name = \"%s{symbol}\" }}); }}")
            .AppendLine()
        |> ignore

    let bodyText = out.ToString()

    let usesExnShow =
        state.Tests.Count > 0
        || bodyText.Contains "fable_rt.anyText"
        || bodyText.Contains "fable_rt.toText"
        || bodyText.Contains "fable_rt.genericText"
        || bodyText.Contains "fable_rt.exnMessage"
        || bodyText.Contains "fable_rt.exnText"
        || bodyText.Contains "fable_rt.toString"
        || bodyText.Contains "fable_rt.writeToString"
        || bodyText.Contains "fable_rt.threadStart"
        || bodyText.Contains ".kind = 'A'"
        || bodyText.Contains ".kind = 'O'"

    bodyText.Replace(
        "__FABLE_EXN_SHOW__",
        if usesExnShow then
            "true"
        else
            "false"
    )
