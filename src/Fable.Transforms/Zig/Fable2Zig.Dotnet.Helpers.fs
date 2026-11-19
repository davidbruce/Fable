/// What the files of .NET members by domain (Fable2Zig.Dotnet.*.fs) share: calls into the
/// runtime library, and tests of the kinds of values.
module Fable.Transforms.Zig.DotnetHelpers

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

/// a call into the runtime library that can raise
let rt (ctx: Ctx) (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
    ctx.State.UsesRuntime <- true
    bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> ERt(macro, irs, ty))

/// a call into the runtime library that cannot
let pure' (ctx: Ctx) (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
    ctx.State.UsesRuntime <- true
    bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> EEmit(macro, irs, ty))

let tChar = TPrim "u16"
let tF64 = TPrim "f64"
let tBig = TPrim "fable_rt.BigInt"
let tDec = TPrim "fable_rt.NetDecimal"

let isNumber (ty: Ty) = intBits ty > 0 || isFloatTy ty

/// the Zig name of a number type
let zigTypeName (r: SourceLocation option) (ty: Ty) =
    match ty with
    | TPrim name -> name
    | _ -> fail r "internal: not a number type"

/// an int argument (an enum's value is not one: `IndexOf(c, StringComparison.Ordinal)`)
let isInt (x: Fable.Expr) =
    match x.Type with
    | Fable.Number(Int32, Fable.NumberInfo.IsEnum _) -> false
    | Fable.Number(Int32, _) -> true
    | _ -> false

let isDec (x: Fable.Expr) =
    match x.Type with
    | Fable.Number(Decimal, _) -> true
    | _ -> false

let isBig (x: Fable.Expr) =
    match x.Type with
    | Fable.Number(BigInt, _) -> true
    | _ -> false

let decLit (ctx: Ctx) (m: string) (scale: int) =
    ctx.State.UsesRuntime <- true
    ELit($"fable_rt.decLit(%s{m}, %d{scale})", tDec)

/// what a ref cell holds
let contents (r: SourceLocation option) (cell: Expr) =
    match typeOf cell with
    | TEnt(_, [ elem ]) -> EGet(cell, PField "contents", elem)
    | _ -> fail r "internal: not a ref cell"
