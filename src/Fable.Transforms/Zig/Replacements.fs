/// Replacements of the Zig target.
///
/// Operators on numbers, booleans and chars become plain operation nodes. Every other call
/// into .NET or FSharp.Core is kept as what it is: a call to an import named after the
/// declaring type (`dotnet:System.Math` / `Sqrt`), which the lowering resolves, or rejects by
/// its .NET name. Nothing is rewritten in terms of another target's runtime library.
module Fable.Transforms.Zig.Replacements

#nowarn "1182"

open Fable
open Fable.AST
open Fable.AST.Fable
open Fable.Transforms
open Replacements.Util

/// Prefix of the import path that marks a call kept under its .NET name.
[<Literal>]
let DotnetPrefix = "dotnet:"

/// Numbers, booleans and chars: what Zig's own operators work on.
let private isNative (t: Type) =
    match t with
    | Number((BigInt | Decimal), _) -> false
    | Number _
    | Boolean
    | Char -> true
    | _ -> false

/// The .NET name of a native number type, and its zero.
let private numberInfo (kind: NumberKind) : (string * NumberValue) option =
    match kind with
    | Int8 -> Some("System.SByte", NumberValue.Int8 0y)
    | UInt8 -> Some("System.Byte", NumberValue.UInt8 0uy)
    | Int16 -> Some("System.Int16", NumberValue.Int16 0s)
    | UInt16 -> Some("System.UInt16", NumberValue.UInt16 0us)
    | Int32 -> Some("System.Int32", NumberValue.Int32 0)
    | UInt32 -> Some("System.UInt32", NumberValue.UInt32 0u)
    | Int64 -> Some("System.Int64", NumberValue.Int64 0L)
    | UInt64 -> Some("System.UInt64", NumberValue.UInt64 0UL)
    | NativeInt -> Some("System.IntPtr", NumberValue.NativeInt 0n)
    | UNativeInt -> Some("System.UIntPtr", NumberValue.UNativeInt 0un)
    | Float32 -> Some("System.Single", NumberValue.Float32 0.0f)
    | Float64 -> Some("System.Double", NumberValue.Float64 0.0)
    | _ -> None

/// The call, unchanged, under the name of the .NET member it goes to.
let dotnetCall r t (info: CallInfo) (thisArg: Expr option) (args: Expr list) : Expr =
    let callee =
        Import(
            {
                Selector = info.CompiledName
                Path = DotnetPrefix + info.DeclaringEntityFullName
                Kind = LibraryImport(LibraryImportInfo.Create(isInstanceMember = thisArg.IsSome))
            },
            Any,
            None
        )

    let callInfo = makeCallInfo thisArg args info.SignatureArgTypes
    Call(callee, { callInfo with GenericArgs = info.GenericArgs }, t, r)

/// An F# operator on native values is the same operator in Zig; the emitter gives it .NET's
/// semantics (wrapping arithmetic, truncating division, masked shift counts).
let private nativeOp r t (opName: string) (args: Expr list) : Expr option =
    let binOp op left right =
        Operation(Binary(op, left, right), Tags.empty, t, r) |> Some

    let unOp op operand =
        Operation(Unary(op, operand), Tags.empty, t, r) |> Some

    match opName, args with
    | Operators.addition, [ left; right ] -> binOp BinaryPlus left right
    | Operators.subtraction, [ left; right ] -> binOp BinaryMinus left right
    | Operators.multiply, [ left; right ] -> binOp BinaryMultiply left right
    | (Operators.division | Operators.divideByInt), [ left; right ] -> binOp BinaryDivide left right
    | Operators.modulus, [ left; right ] -> binOp BinaryModulus left right
    | Operators.leftShift, [ left; right ] -> binOp BinaryShiftLeft left right
    | Operators.rightShift, [ left; right ] -> binOp BinaryShiftRightSignPropagating left right
    | Operators.bitwiseAnd, [ left; right ] -> binOp BinaryAndBitwise left right
    | Operators.bitwiseOr, [ left; right ] -> binOp BinaryOrBitwise left right
    | Operators.exclusiveOr, [ left; right ] -> binOp BinaryXorBitwise left right
    | Operators.equality, [ left; right ] -> binOp BinaryEqual left right
    | Operators.inequality, [ left; right ] -> binOp BinaryUnequal left right
    | Operators.lessThan, [ left; right ] -> binOp BinaryLess left right
    | Operators.lessThanOrEqual, [ left; right ] -> binOp BinaryLessOrEqual left right
    | Operators.greaterThan, [ left; right ] -> binOp BinaryGreater left right
    | Operators.greaterThanOrEqual, [ left; right ] -> binOp BinaryGreaterOrEqual left right
    | Operators.logicalNot, [ operand ] -> unOp UnaryNotBitwise operand
    | Operators.unaryNegation, [ operand ] -> unOp UnaryMinus operand
    | Operators.unaryPlus, [ operand ] -> unOp UnaryPlus operand
    | "Not", [ operand ] -> unOp UnaryNot operand
    | _ -> None

let tryCall (com: ICompiler) (ctx: Context) r t (info: CallInfo) (thisArg: Expr option) (args: Expr list) =
    let native =
        match thisArg with
        | None when args |> List.forall (fun a -> isNative a.Type) -> nativeOp r t info.CompiledName args
        | _ -> None

    match native with
    | Some _ -> native
    | None -> Some(dotnetCall r t info thisArg args)

/// Static fields of .NET types (`Int32.MaxValue`, ...): none yet.
let tryField (com: ICompiler) (returnTyp: Type) (ownerTyp: Type) (fieldName: string) : Expr option = None

let tryBaseConstructor
    (com: ICompiler)
    (ctx: Context)
    (ent: EntityRef)
    (argTypes: Lazy<Type list>)
    (genArgs: Type list)
    (args: Expr list)
    : (Expr * Expr list) option
    =
    None

/// The .NET type behind a built-in type, for calls the F# compiler resolves by type
/// (statically resolved type parameters).
let tryType (t: Type) =
    match t with
    | Boolean -> Some(Types.bool, tryCall, [])
    | Char -> Some(Types.char, tryCall, [])
    | Number(kind, _) -> numberInfo kind |> Option.map (fun (fullName, _) -> fullName, tryCall, [])
    | _ -> None

/// The value an exception is built from.
let error (com: ICompiler) (msg: Expr) : Expr = msg

let defaultof (com: ICompiler) (ctx: Context) r (t: Type) : Expr =
    match t with
    | Boolean -> makeBoolConst false
    | Number(kind, info) when (numberInfo kind).IsSome -> Value(NumberConstant(snd (numberInfo kind).Value, info), r)
    | _ ->
        dotnetCall
            r
            t
            {
                CompiledName = "DefaultOf"
                OverloadSuffix = ""
                SignatureArgTypes = []
                HasSpread = false
                IsModuleValue = false
                IsInterface = false
                DeclaringEntityFullName = "Microsoft.FSharp.Core.Operators.Unchecked"
                GenericArgs = [ t ]
            }
            None
            []

// Byrefs: the address of a mutable value or field is an address-of operation, reading through
// a byref keeps the variable (its type says it is a pointer), writing through it is a store.
let getRefCell (com: ICompiler) r (t: Type) (expr: Expr) : Expr = expr

let setRefCell (com: ICompiler) r (expr: Expr) (value: Expr) : Expr =
    Set(expr, ValueSet, value.Type, value, r)

let makeRefCellFromValue (com: ICompiler) r (value: Expr) : Expr =
    Operation(Unary(UnaryAddressOf, value), Tags.empty, value.Type, r)

let makeRefFromMutableValue (com: ICompiler) (ctx: Context) r (t: Type) (value: Expr) : Expr =
    Operation(Unary(UnaryAddressOf, value), Tags.empty, t, r)

let makeRefFromMutableField (com: ICompiler) (ctx: Context) r (t: Type) (callee: Expr) (key: string) : Expr =
    let value = Get(callee, FieldInfo.Create(key), t, r)
    Operation(Unary(UnaryAddressOf, value), Tags.empty, t, r)

let makeRefFromMutableFunc (com: ICompiler) (ctx: Context) r (t: Type) (value: Expr) : Expr = value
