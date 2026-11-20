/// .NET FFI & low-level memory interop lowering: NativePtr, IntPtr/UIntPtr, Marshal, NativeMemory,
/// MemoryMarshal, Unsafe, NativeLibrary, and `fixed` pinning (`Operators.ToIntPtr`, `String.GetPinnableReference`).
module internal Fable.Transforms.Zig.DotnetInterop

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
    let args =
        match info.ThisArg with
        | Some this -> this :: info.Args
        | None -> info.Args

    let rt = rt ctx
    let pure' = pure' ctx

    let byrefPlace (isConst: bool) (makePtr: Ty -> Expr) : Expr =
        let item =
            match mapType ctx r t with
            | TPtr(item, _) -> item
            | other -> other

        let ptrTy = TPtr(item, isConst)
        bindArgs ctx [ makePtr ptrTy ] (fun xs -> EDeref(xs.Head, item))

    let lwByref (e: Fable.Expr) : Expr =
        let ir = lw ctx e

        match e.Type with
        | Fable.DeclaredType(ent, _) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
            defaultArg (tryAddress ir) ir
        | _ -> ir

    let lwNativePtr (p: Fable.Expr) : Expr =
        let ir = lw ctx p

        match typeOf ir with
        | TPrim "isize" ->
            let targetTy =
                match mapType ctx r p.Type with
                | TPrim s when s.StartsWith("?[*]", System.StringComparison.Ordinal) -> TPrim s
                | _ ->
                    match info.GenericArgs with
                    | g :: _ -> TPrim("?[*]" + zigType (mapType ctx r g))
                    | [] -> TPrim "?*anyopaque"

            coerceTy ctx targetTy ir
        | _ -> ir

    let nativePtrOp (macro: string) (ptrArgs: Expr list) (ty: Ty) : Expr =
        ctx.State.UsesRuntime <- true
        bindArgs ctx ptrArgs (fun xs -> EEmit(macro, xs, ty))

    let isRawPtrTy =
        function
        | TPrim s -> s = "?*anyopaque" || s.StartsWith("?[*]", System.StringComparison.Ordinal)
        | _ -> false

    let toPtrInt (targetPrim: string) (x: Fable.Expr) : Expr =
        let xIr = lw ctx x

        match typeOf xIr with
        | TPrim s when s = targetPrim -> xIr
        | TPtr _ ->
            if targetPrim = "usize" then
                bindArgs ctx [ xIr ] (fun xs -> EEmit("@intFromPtr($0)", xs, TPrim "usize"))
            else
                bindArgs ctx [ xIr ] (fun xs -> EEmit("@as(isize, @bitCast(@intFromPtr($0)))", xs, TPrim "isize"))
        | TPrim s when s = "?*anyopaque" || s.StartsWith("?[*]", System.StringComparison.Ordinal) ->
            if targetPrim = "usize" then
                bindArgs
                    ctx
                    [ xIr ]
                    (fun xs -> EEmit("if ($0) |q| @intFromPtr(q) else @as(usize, 0)", xs, TPrim "usize"))
            else
                bindArgs
                    ctx
                    [ xIr ]
                    (fun xs ->
                        EEmit("if ($0) |q| @as(isize, @bitCast(@intFromPtr(q))) else @as(isize, 0)", xs, TPrim "isize")
                    )
        | TPrim "fable_rt.String" ->
            ctx.State.UsesRuntime <- true

            if targetPrim = "usize" then
                bindArgs
                    ctx
                    [ xIr ]
                    (fun xs ->
                        EEmit(
                            "if ($0 == null) @as(usize, 0) else @intFromPtr(fable_rt.stringPinnableRef($0))",
                            xs,
                            TPrim "usize"
                        )
                    )
            else
                bindArgs
                    ctx
                    [ xIr ]
                    (fun xs ->
                        EEmit(
                            "if ($0 == null) @as(isize, 0) else @as(isize, @bitCast(@intFromPtr(fable_rt.stringPinnableRef($0))))",
                            xs,
                            TPrim "isize"
                        )
                    )
        | TPrim("isize" | "usize") ->
            bindArgs ctx [ xIr ] (fun xs -> EEmit($"@as(%s{targetPrim}, @bitCast($0))", xs, TPrim targetPrim))
        | TPrim "u64" when targetPrim = "isize" ->
            bindArgs ctx [ xIr ] (fun xs -> EEmit("@as(isize, @bitCast($0))", xs, TPrim "isize"))
        | TPrim "i64" when targetPrim = "usize" ->
            bindArgs ctx [ xIr ] (fun xs -> EEmit("@as(usize, @bitCast($0))", xs, TPrim "usize"))
        | _ -> bindArgs ctx [ xIr ] (fun xs -> EEmit($"@as(%s{targetPrim}, @intCast($0))", xs, TPrim targetPrim))

    let tryTypeArg (argOpt: Fable.Expr option) =
        match info.GenericArgs with
        | g :: _ -> Some(mapType ctx r g)
        | [] ->
            match argOpt with
            | Some(Fable.Value(Fable.TypeInfo(ty, _), _)) -> Some(mapType ctx r ty)
            | Some arg -> Some(mapType ctx r arg.Type)
            | None -> None

    match entity, name, args with
    // ---- NativePtr: nullable `?[*]T`, stackalloc (`fable_rt.StackAlloc`), and `&arr.[i]` ----
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", "StackAllocate", [ n ] ->
        let item = mapType ctx r info.GenericArgs.Head
        rt $"fable_stack.alloc(%s{zigType item}, $0)" [ n ] (TPrim("?[*]" + zigType item))
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", "ArrayElemAddress", [ arr; idx ] ->
        rt "fable_rt.arrayElemPtr($0, $1)" [ arr; idx ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", "NullPointer", [] ->
        let outTy = mapType ctx r t
        ELit($"@as(%s{zigType outTy}, null)", outTy)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", "IsNullPointer", [ p ] ->
        nativePtrOp "($0 == null)" [ lwNativePtr p ] tBool
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("OfNativeIntInlined" | "OfNativeInt"), [ addr ] ->
        pure' "@as($R, @ptrFromInt(@as(usize, @bitCast(@as(isize, $0)))))" [ addr ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ToNativeIntInlined" | "ToNativeInt"), [ p ] ->
        nativePtrOp
            "if ($0) |q| @as(isize, @bitCast(@intFromPtr(q))) else @as(isize, 0)"
            [ lwNativePtr p ]
            (TPrim "isize")
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ToVoidPtrInlined" | "ToVoidPtr"), [ p ] ->
        nativePtrOp
            "if ($0) |q| @as(?*anyopaque, @ptrCast(q)) else @as(?*anyopaque, null)"
            [ lwNativePtr p ]
            (TPrim "?*anyopaque")
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("OfVoidPtrInlined" | "OfVoidPtr"), [ p ] ->
        pure' "if ($0) |q| @as($R, @ptrCast(@alignCast(q))) else null" [ p ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("AddPointerInlined" | "Add"), [ p; ofs ] ->
        nativePtrOp "fable_rt.ptrAdd($0, @as(i32, @intCast($1)))" [ lwNativePtr p; lw ctx ofs ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("GetPointerInlined" | "Get"), [ p; i ] ->
        nativePtrOp "fable_rt.ptrGet($0, $1)" [ lwNativePtr p; lw ctx i ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("SetPointerInlined" | "Set"), [ p; i; x ] ->
        nativePtrOp "fable_rt.ptrSet($0, $1, $2)" [ lwNativePtr p; lw ctx i; lw ctx x ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ReadPointerInlined" | "Read"), [ p ] ->
        nativePtrOp "fable_rt.ptrRead($0)" [ lwNativePtr p ] (mapType ctx r t)
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("WritePointerInlined" | "Write"), [ p; x ] ->
        nativePtrOp "fable_rt.ptrWrite($0, $1)" [ lwNativePtr p; lw ctx x ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("CopyPointerInlined" | "Copy"), [ dst; src ] ->
        nativePtrOp "fable_rt.ptrCopy($0, $1, 1)" [ lwNativePtr dst; lwNativePtr src ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule",
      ("CopyPointerInlined" | "Copy" | "CopyBlockInlined" | "CopyBlock"),
      [ dst; src; count ] ->
        nativePtrOp "fable_rt.ptrCopy($0, $1, $2)" [ lwNativePtr dst; lwNativePtr src; lw ctx count ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule",
      ("InitializeBlockInlined" | "InitBlockInlined" | "InitBlock"),
      [ dst; v; count ] ->
        nativePtrOp "fable_rt.ptrInitBlock($0, $1, $2)" [ lwNativePtr dst; lw ctx v; lw ctx count ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ClearPointerInlined" | "Clear"), [ dst ] ->
        nativePtrOp "fable_rt.ptrClear($0, 1)" [ lwNativePtr dst ] tVoid
    | "Microsoft.FSharp.NativeInterop.NativePtrModule", ("ClearPointerInlined" | "Clear"), [ dst; count ] ->
        nativePtrOp "fable_rt.ptrClear($0, $1)" [ lwNativePtr dst; lw ctx count ] tVoid

    // ---- `fixed` string pinning + `Operators.ToIntPtr` / `ToUIntPtr` ----
    | "System.String", "GetPinnableReference", [ s ] -> pure' "fable_rt.stringPinnableRef($0)" [ s ] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators", "ToIntPtr", [ x ] -> toPtrInt "isize" x
    | "Microsoft.FSharp.Core.Operators", "ToUIntPtr", [ x ] -> toPtrInt "usize" x

    // ---- `System.IntPtr` and `System.UIntPtr` ----
    | ("System.IntPtr" | "System.UIntPtr"), ("get_Zero" | "Zero"), [] ->
        ELit(
            "0",
            TPrim(
                if entity = "System.IntPtr" then
                    "isize"
                else
                    "usize"
            )
        )
    | ("System.IntPtr" | "System.UIntPtr"), ("get_Size" | "Size"), [] -> ELit("@as(i32, @sizeOf(isize))", tI32)
    | ("System.IntPtr" | "System.UIntPtr"), ".ctor", [ x ] ->
        toPtrInt
            (if entity = "System.IntPtr" then
                 "isize"
             else
                 "usize")
            x
    | ("System.IntPtr" | "System.UIntPtr"), "ToInt32", [ p ] -> rt "fable_rt.checkedConv(i32, $0)" [ p ] tI32
    | ("System.IntPtr" | "System.UIntPtr"), "ToInt64", [ p ] ->
        if entity = "System.IntPtr" then
            pure' "@as(i64, @intCast($0))" [ p ] (TPrim "i64")
        else
            rt "fable_rt.checkedConv(i64, $0)" [ p ] (TPrim "i64")
    | ("System.IntPtr" | "System.UIntPtr"), "ToUInt32", [ p ] -> rt "fable_rt.checkedConv(u32, $0)" [ p ] (TPrim "u32")
    | ("System.IntPtr" | "System.UIntPtr"), "ToUInt64", [ p ] ->
        if entity = "System.UIntPtr" then
            pure' "@as(u64, @intCast($0))" [ p ] (TPrim "u64")
        else
            rt "fable_rt.checkedConv(u64, $0)" [ p ] (TPrim "u64")
    | "System.IntPtr", "ToPointer", [ p ] ->
        pure' "@as(?*anyopaque, @ptrFromInt(@as(usize, @bitCast($0))))" [ p ] (TPrim "?*anyopaque")
    | "System.UIntPtr", "ToPointer", [ p ] -> pure' "@as(?*anyopaque, @ptrFromInt($0))" [ p ] (TPrim "?*anyopaque")
    | ("System.IntPtr" | "System.UIntPtr"), ("Add" | "op_Addition"), [ p; ofs ] ->
        let outTy = mapType ctx r t
        pure' "($0 +% @as($R, @intCast($1)))" [ p; ofs ] outTy
    | ("System.IntPtr" | "System.UIntPtr"), ("Subtract" | "op_Subtraction"), [ p; ofs ] ->
        let outTy = mapType ctx r t
        pure' "($0 -% @as($R, @intCast($1)))" [ p; ofs ] outTy
    | ("System.IntPtr" | "System.UIntPtr"), "Equals", [ a; b ] -> pure' "($0 == $1)" [ a; b ] tBool
    | ("System.IntPtr" | "System.UIntPtr"), "op_Explicit", [ x ] ->
        let outTy = mapType ctx r t

        if isRawPtrTy outTy then
            let xIr = lw ctx x

            match typeOf xIr with
            | TPrim "usize" -> bindArgs ctx [ xIr ] (fun xs -> EEmit("@as($R, @ptrFromInt($0))", xs, outTy))
            | _ -> bindArgs ctx [ xIr ] (fun xs -> EEmit("@as($R, @ptrFromInt(@as(usize, @bitCast($0))))", xs, outTy))
        elif outTy = TPrim "isize" then
            toPtrInt "isize" x
        elif outTy = TPrim "usize" then
            toPtrInt "usize" x
        else
            rt "fable_rt.checkedConv($R, $0)" [ x ] outTy

    // ---- `System.Runtime.InteropServices.Marshal` ----
    | "System.Runtime.InteropServices.Marshal", "SizeOf", [] ->
        match tryTypeArg None with
        | Some elem -> pure' $"fable_rt.marshalSizeOf(%s{zigType elem})" [] tI32
        | None -> fail r "Marshal.SizeOf requires a known type argument"
    | "System.Runtime.InteropServices.Marshal", "SizeOf", [ x ] ->
        match tryTypeArg (Some x) with
        | Some elem -> pure' $"fable_rt.marshalSizeOf(%s{zigType elem})" [] tI32
        | None -> fail r "Marshal.SizeOf requires a known type"
    | "System.Runtime.InteropServices.Marshal", "OffsetOf", [ fieldName ] ->
        match info.GenericArgs with
        | g :: _ ->
            let elem = mapType ctx r g
            rt $"fable_rt.marshalOffsetOf(%s{zigType elem}, $0)" [ fieldName ] (TPrim "isize")
        | [] -> fail r "Marshal.OffsetOf requires a generic type argument"
    | "System.Runtime.InteropServices.Marshal", "OffsetOf", [ Fable.Value(Fable.TypeInfo(ty, _), _); fieldName ] ->
        let elem = mapType ctx r ty
        rt $"fable_rt.marshalOffsetOf(%s{zigType elem}, $0)" [ fieldName ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", ("AllocHGlobal" | "AllocCoTaskMem"), [ cb ] ->
        rt "fable_rt.marshalAllocHGlobal(@as(isize, @intCast($0)))" [ cb ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "ReAllocHGlobal", [ pv; cb ] ->
        rt "fable_rt.marshalReAllocHGlobal($0, @as(isize, @intCast($1)))" [ pv; cb ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal",
      ("FreeHGlobal" | "FreeCoTaskMem" | "ZeroFreeGlobalAllocUTF8" | "ZeroFreeGlobalAllocAnsi" | "ZeroFreeGlobalAllocUnicode" | "ZeroFreeCoTaskMemUTF8"),
      [ ptr ] -> pure' "fable_rt.marshalFreeHGlobal($0)" [ ptr ] tVoid
    | "System.Runtime.InteropServices.Marshal", ("PtrToStringUTF8" | "PtrToStringAnsi"), [ ptr ] ->
        pure' "fable_rt.marshalPtrToStringUTF8($0)" [ ptr ] tStr
    | "System.Runtime.InteropServices.Marshal", ("PtrToStringUTF8" | "PtrToStringAnsi"), [ ptr; len ] ->
        rt "fable_rt.marshalPtrToStringUTF8Len($0, $1)" [ ptr; len ] tStr
    | "System.Runtime.InteropServices.Marshal", "PtrToStringUni", [ ptr ] ->
        pure' "fable_rt.marshalPtrToStringUni($0)" [ ptr ] tStr
    | "System.Runtime.InteropServices.Marshal", "PtrToStringUni", [ ptr; len ] ->
        rt "fable_rt.marshalPtrToStringUniLen($0, $1)" [ ptr; len ] tStr
    | "System.Runtime.InteropServices.Marshal",
      ("StringToHGlobalUTF8" | "StringToHGlobalAnsi" | "StringToCoTaskMemUTF8"),
      [ s ] -> rt "fable_rt.marshalStringToHGlobalUTF8($0)" [ s ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "StringToHGlobalUni", [ s ] ->
        rt "fable_rt.marshalStringToHGlobalUni($0)" [ s ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "PtrToStructure", [ ptr ] when not info.GenericArgs.IsEmpty ->
        rt "fable_rt.marshalPtrToStructure($R, $0)" [ ptr ] (mapType ctx r t)
    | "System.Runtime.InteropServices.Marshal", "StructureToPtr", [ v; ptr; _fDeleteOld ] ->
        let vUnboxed =
            match v with
            | Fable.TypeCast(inner, tCast) when unwrapNullness tCast = Fable.Any -> inner
            | _ -> v

        rt "fable_rt.marshalStructureToPtr($0, $1)" [ vUnboxed; ptr ] tVoid
    | "System.GC", "KeepAlive", [ x ] -> pure' "fable_rt.keepAlive($0)" [ x ] tVoid
    | "System.Runtime.InteropServices.Marshal", "Copy", [ a; b; c; d ] ->
        match a.Type, b.Type with
        | Fable.Array _, _ -> rt "fable_rt.marshalCopyFromArray($0, $1, $2, $3)" [ a; b; c; d ] tVoid
        | _, Fable.Array _ -> rt "fable_rt.marshalCopyToArray($0, $1, $2, $3)" [ a; b; c; d ] tVoid
        | _ -> Unchecked.defaultof<Expr>
    | "System.Runtime.InteropServices.Marshal", "ReadByte", [ ptr ] ->
        rt "fable_rt.marshalRead(u8, $0, 0)" [ ptr ] (TPrim "u8")
    | "System.Runtime.InteropServices.Marshal", "ReadByte", [ ptr; ofs ] ->
        rt "fable_rt.marshalRead(u8, $0, $1)" [ ptr; ofs ] (TPrim "u8")
    | "System.Runtime.InteropServices.Marshal", "ReadInt16", [ ptr ] ->
        rt "fable_rt.marshalRead(i16, $0, 0)" [ ptr ] (TPrim "i16")
    | "System.Runtime.InteropServices.Marshal", "ReadInt16", [ ptr; ofs ] ->
        rt "fable_rt.marshalRead(i16, $0, $1)" [ ptr; ofs ] (TPrim "i16")
    | "System.Runtime.InteropServices.Marshal", "ReadInt32", [ ptr ] ->
        rt "fable_rt.marshalRead(i32, $0, 0)" [ ptr ] tI32
    | "System.Runtime.InteropServices.Marshal", "ReadInt32", [ ptr; ofs ] ->
        rt "fable_rt.marshalRead(i32, $0, $1)" [ ptr; ofs ] tI32
    | "System.Runtime.InteropServices.Marshal", "ReadInt64", [ ptr ] ->
        rt "fable_rt.marshalRead(i64, $0, 0)" [ ptr ] (TPrim "i64")
    | "System.Runtime.InteropServices.Marshal", "ReadInt64", [ ptr; ofs ] ->
        rt "fable_rt.marshalRead(i64, $0, $1)" [ ptr; ofs ] (TPrim "i64")
    | "System.Runtime.InteropServices.Marshal", "ReadIntPtr", [ ptr ] ->
        rt "fable_rt.marshalRead(isize, $0, 0)" [ ptr ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "ReadIntPtr", [ ptr; ofs ] ->
        rt "fable_rt.marshalRead(isize, $0, $1)" [ ptr; ofs ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "WriteByte", [ ptr; v ] ->
        rt "fable_rt.marshalWrite(u8, $0, 0, $1)" [ ptr; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteByte", [ ptr; ofs; v ] ->
        rt "fable_rt.marshalWrite(u8, $0, $1, $2)" [ ptr; ofs; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt16", [ ptr; v ] ->
        rt "fable_rt.marshalWrite(i16, $0, 0, $1)" [ ptr; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt16", [ ptr; ofs; v ] ->
        rt "fable_rt.marshalWrite(i16, $0, $1, $2)" [ ptr; ofs; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt32", [ ptr; v ] ->
        rt "fable_rt.marshalWrite(i32, $0, 0, $1)" [ ptr; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt32", [ ptr; ofs; v ] ->
        rt "fable_rt.marshalWrite(i32, $0, $1, $2)" [ ptr; ofs; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt64", [ ptr; v ] ->
        rt "fable_rt.marshalWrite(i64, $0, 0, $1)" [ ptr; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteInt64", [ ptr; ofs; v ] ->
        rt "fable_rt.marshalWrite(i64, $0, $1, $2)" [ ptr; ofs; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteIntPtr", [ ptr; v ] ->
        rt "fable_rt.marshalWrite(isize, $0, 0, $1)" [ ptr; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "WriteIntPtr", [ ptr; ofs; v ] ->
        rt "fable_rt.marshalWrite(isize, $0, $1, $2)" [ ptr; ofs; v ] tVoid
    | "System.Runtime.InteropServices.Marshal", "GetFunctionPointerForDelegate", [ del ] ->
        let rec unwrapCast e =
            match e with
            | Fable.TypeCast(x, _) -> unwrapCast x
            | _ -> e

        rt "fable_rt.marshalGetFunctionPointerForDelegate($0)" [ unwrapCast del ] (TPrim "isize")
    | "System.Runtime.InteropServices.Marshal", "GetDelegateForFunctionPointer", ([ ptr ] | [ ptr; _ ]) when
        not info.GenericArgs.IsEmpty
        ->
        rt "fable_rt.marshalGetDelegateForFunctionPointer($R, $0)" [ ptr ] (mapType ctx r t)

    // ---- `System.Runtime.InteropServices.NativeMemory` ----
    | "System.Runtime.InteropServices.NativeMemory", "Alloc", [ byteCount ] ->
        rt "fable_rt.nativeAlloc(@as(usize, @intCast($0)))" [ byteCount ] (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "Alloc", [ elemCount; elemSize ] ->
        rt
            "fable_rt.nativeAllocElem(@as(usize, @intCast($0)), @as(usize, @intCast($1)))"
            [ elemCount; elemSize ]
            (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "AllocZeroed", [ byteCount ] ->
        rt "fable_rt.nativeAllocZeroed(@as(usize, @intCast($0)))" [ byteCount ] (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "AllocZeroed", [ elemCount; elemSize ] ->
        rt
            "fable_rt.nativeAllocZeroedElem(@as(usize, @intCast($0)), @as(usize, @intCast($1)))"
            [ elemCount; elemSize ]
            (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "Realloc", [ ptr; byteCount ] ->
        rt "fable_rt.nativeRealloc($0, @as(usize, @intCast($1)))" [ ptr; byteCount ] (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "Free", [ ptr ] -> pure' "fable_rt.nativeFree($0)" [ ptr ] tVoid
    | "System.Runtime.InteropServices.NativeMemory", "AlignedAlloc", [ byteCount; alignment ] ->
        rt
            "fable_rt.nativeAlignedAlloc(@as(usize, @intCast($0)), @as(usize, @intCast($1)))"
            [ byteCount; alignment ]
            (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "AlignedRealloc", [ ptr; byteCount; alignment ] ->
        rt
            "fable_rt.nativeAlignedRealloc($0, @as(usize, @intCast($1)), @as(usize, @intCast($2)))"
            [ ptr; byteCount; alignment ]
            (TPrim "?*anyopaque")
    | "System.Runtime.InteropServices.NativeMemory", "AlignedFree", [ ptr ] ->
        pure' "fable_rt.nativeAlignedFree($0)" [ ptr ] tVoid
    | "System.Runtime.InteropServices.NativeMemory", "Copy", [ src; dst; byteCount ] ->
        pure' "fable_rt.nativeCopy($0, $1, @as(usize, @intCast($2)))" [ src; dst; byteCount ] tVoid
    | "System.Runtime.InteropServices.NativeMemory", "Fill", [ ptr; byteCount; value ] ->
        pure' "fable_rt.nativeFill($0, @as(usize, @intCast($1)), $2)" [ ptr; byteCount; value ] tVoid
    | "System.Runtime.InteropServices.NativeMemory", "Clear", [ ptr; byteCount ] ->
        pure' "fable_rt.nativeClear($0, @as(usize, @intCast($1)))" [ ptr; byteCount ] tVoid

    // ---- `System.Runtime.InteropServices.MemoryMarshal` ----
    | "System.Runtime.InteropServices.MemoryMarshal", "Cast", [ span ] ->
        pure' "fable_rt.spanCast($R, $0)" [ span ] (mapType ctx r t)
    | "System.Runtime.InteropServices.MemoryMarshal", "AsBytes", [ span ] ->
        pure' "fable_rt.spanAsBytes($R, $0)" [ span ] (mapType ctx r t)
    | "System.Runtime.InteropServices.MemoryMarshal", "GetReference", [ span ] ->
        let spanIr = lw ctx span

        let isConst =
            match typeOf spanIr with
            | TSlice(_, c) -> c
            | _ -> false

        ctx.State.UsesRuntime <- true

        byrefPlace
            isConst
            (fun ptrTy -> bindArgs ctx [ spanIr ] (fun xs -> EEmit("fable_rt.spanGetRef($0)", xs, ptrTy)))
    | "System.Runtime.InteropServices.MemoryMarshal", "GetArrayDataReference", [ arr ] ->
        byrefPlace false (fun ptrTy -> pure' "fable_rt.arrayGetDataRef($0)" [ arr ] ptrTy)
    | "System.Runtime.InteropServices.MemoryMarshal", ("CreateSpan" | "CreateReadOnlySpan"), [ reference; length ] ->
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lwByref reference; lw ctx length ]
            (fun xs -> EEmit("fable_rt.spanCreateFromRef($R, $0, $1)", xs, mapType ctx r t))

    // ---- `System.Runtime.CompilerServices.Unsafe` ----
    | "System.Runtime.CompilerServices.Unsafe", "SizeOf", [] ->
        match info.GenericArgs with
        | g :: _ ->
            let elem = mapType ctx r g
            ELit($"@as(i32, @sizeOf(%s{zigType elem}))", tI32)
        | [] -> fail r "Unsafe.SizeOf requires a generic type argument"
    | "System.Runtime.CompilerServices.Unsafe", "AsPointer", [ ref ] ->
        bindArgs
            ctx
            [ lwByref ref ]
            (fun xs -> EEmit("@as(?*anyopaque, @ptrCast(@constCast($0)))", xs, TPrim "?*anyopaque"))
    | "System.Runtime.CompilerServices.Unsafe", "AsRef", [ src ] ->
        let srcIr = lwByref src

        byrefPlace
            false
            (fun ptrTy ->
                match typeOf srcIr with
                | TPtr _ -> bindArgs ctx [ srcIr ] (fun xs -> EEmit("@constCast($0)", xs, ptrTy))
                | _ -> bindArgs ctx [ srcIr ] (fun xs -> EEmit("@as($R, @ptrCast(@alignCast($0.?)))", xs, ptrTy))
            )
    | "System.Runtime.CompilerServices.Unsafe", "As", [ x ] ->
        let xIr = lwByref x
        let outTy = mapType ctx r t

        match typeOf xIr with
        | TPtr _ ->
            byrefPlace
                false
                (fun ptrTy ->
                    bindArgs ctx [ xIr ] (fun xs -> EEmit("@as($R, @ptrCast(@alignCast(@constCast($0))))", xs, ptrTy))
                )
        | _ ->
            ctx.State.UsesRuntime <- true
            bindArgs ctx [ xIr ] (fun xs -> EEmit($"fable_rt.unsafeAs(%s{zigType outTy}, $0)", xs, outTy))
    | "System.Runtime.CompilerServices.Unsafe", "Add", [ src; ofs ] ->
        let srcIr = lwByref src
        let ofsIr = lw ctx ofs
        let outTy = mapType ctx r t
        ctx.State.UsesRuntime <- true

        match typeOf srcIr with
        | TPtr(_, isConst) ->
            byrefPlace
                isConst
                (fun ptrTy -> bindArgs ctx [ srcIr; ofsIr ] (fun xs -> EEmit("fable_rt.unsafeAdd($0, $1)", xs, ptrTy)))
        | TPrim s when s.StartsWith("?[*]", System.StringComparison.Ordinal) ->
            bindArgs ctx [ srcIr; ofsIr ] (fun xs -> EEmit("fable_rt.ptrAdd($0, @as(i32, @intCast($1)))", xs, outTy))
        | _ ->
            match info.GenericArgs with
            | g :: _ ->
                let elem = zigType (mapType ctx r g)

                bindArgs
                    ctx
                    [ srcIr; ofsIr ]
                    (fun xs ->
                        EEmit(
                            $"@as(?*anyopaque, @ptrCast(fable_rt.ptrAdd(@as(?[*]%s{elem}, @ptrCast(@alignCast($0))), @as(i32, @intCast($1)))))",
                            xs,
                            outTy
                        )
                    )
            | [] -> fail r "Unsafe.Add(voidptr, offset) requires a generic type argument"
    | "System.Runtime.CompilerServices.Unsafe", "ReadUnaligned", [ src ] ->
        let outTy = mapType ctx r t
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lwByref src ]
            (fun xs ->
                EEmit(
                    $"fable_rt.unsafeReadUnaligned(%s{zigType outTy}, @as(?*anyopaque, @ptrCast(@constCast($0))))",
                    xs,
                    outTy
                )
            )
    | "System.Runtime.CompilerServices.Unsafe", "WriteUnaligned", [ dst; v ] ->
        let valTy = mapType ctx r v.Type
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lwByref dst; lw ctx v ]
            (fun xs ->
                EEmit(
                    $"fable_rt.unsafeWriteUnaligned(%s{zigType valTy}, @as(?*anyopaque, @ptrCast(@constCast($0))), $1)",
                    xs,
                    tVoid
                )
            )
    | "System.Runtime.CompilerServices.Unsafe", ("CopyBlock" | "CopyBlockUnaligned"), [ dst; src; byteCount ] ->
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lwByref dst; lwByref src; lw ctx byteCount ]
            (fun xs ->
                EEmit(
                    "fable_rt.nativeCopy(@as(?*anyopaque, @ptrCast(@constCast($1))), @as(?*anyopaque, @ptrCast(@constCast($0))), @as(usize, @intCast($2)))",
                    xs,
                    tVoid
                )
            )
    | "System.Runtime.CompilerServices.Unsafe", ("InitBlock" | "InitBlockUnaligned"), [ dst; value; byteCount ] ->
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lwByref dst; lw ctx value; lw ctx byteCount ]
            (fun xs ->
                EEmit(
                    "fable_rt.nativeFill(@as(?*anyopaque, @ptrCast(@constCast($0))), @as(usize, @intCast($2)), $1)",
                    xs,
                    tVoid
                )
            )

    // ---- `System.Runtime.InteropServices.NativeLibrary` ----
    | "System.Runtime.InteropServices.NativeLibrary", "SetDllImportResolver", _ -> EUnit
    | "System.Runtime.InteropServices.NativeLibrary", "Load", [ path ] ->
        rt "fable_rt.nativeLibLoad($0)" [ path ] (TPrim "isize")
    | "System.Runtime.InteropServices.NativeLibrary", "TryLoad", [ path; handleOut ] ->
        pure' "fable_rt.nativeLibTryLoad($0, $1)" [ path; handleOut ] tBool
    | "System.Runtime.InteropServices.NativeLibrary", "Free", [ handle ] ->
        pure' "fable_rt.nativeLibFree($0)" [ handle ] tVoid
    | "System.Runtime.InteropServices.NativeLibrary", "GetExport", [ handle; symName ] ->
        rt "fable_rt.nativeLibGetExport($0, $1)" [ handle; symName ] (TPrim "isize")
    | "System.Runtime.InteropServices.NativeLibrary", "TryGetExport", [ handle; symName; addrOut ] ->
        pure' "fable_rt.nativeLibTryGetExport($0, $1, $2)" [ handle; symName; addrOut ] tBool

    | _ -> Unchecked.defaultof<Expr>
