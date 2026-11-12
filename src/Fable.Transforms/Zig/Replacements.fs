module Fable.Transforms.Zig.Replacements

#nowarn "1182"

open Fable
open Fable.AST
open Fable.AST.Fable
open Fable.Transforms
open Replacements.Util

/// Numbers, booleans and chars: what Zig's own operators work on.
let private isNative (t: Type) =
    match t with
    | Number((BigInt | Decimal), _) -> false
    | Number _
    | Boolean
    | Char -> true
    | _ -> false

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
    | Operators.logicalNot, [ operand ] -> unOp UnaryNotBitwise operand
    | Operators.unaryNegation, [ operand ] -> unOp UnaryMinus operand
    | Operators.unaryPlus, [ operand ] -> unOp UnaryPlus operand
    | _ -> None

/// Only the operators are the target's own so far; every other call still goes through the
/// JavaScript replacements.
let tryCall (com: ICompiler) (ctx: Context) r t (info: CallInfo) (thisArg: Expr option) (args: Expr list) =
    let own =
        match info.DeclaringEntityFullName, thisArg with
        | "Microsoft.FSharp.Core.Operators", None when args |> List.forall (fun a -> isNative a.Type) ->
            nativeOp r t info.CompiledName args
        | _ -> None

    match own with
    | Some _ -> own
    | None -> JS.Replacements.tryCall com ctx r t info thisArg args
