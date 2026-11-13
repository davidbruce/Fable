/// F#'s `Result` module, written in F# and compiled by the Zig target itself (see List.fs).
module Fable.Library.Zig.Result

let map<'T, 'TError, 'U> (mapping: 'T -> 'U) (result: Result<'T, 'TError>) : Result<'U, 'TError> =
    match result with
    | Ok x -> Ok(mapping x)
    | Error e -> Error e

let mapError<'T, 'TError, 'U> (mapping: 'TError -> 'U) (result: Result<'T, 'TError>) : Result<'T, 'U> =
    match result with
    | Ok x -> Ok x
    | Error e -> Error(mapping e)

let bind<'T, 'TError, 'U> (binder: 'T -> Result<'U, 'TError>) (result: Result<'T, 'TError>) : Result<'U, 'TError> =
    match result with
    | Ok x -> binder x
    | Error e -> Error e
