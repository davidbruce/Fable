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

// (type parameters in the order of their names: the target matches them by name)

let isOk<'Error, 'T> (result: Result<'T, 'Error>) : bool =
    match result with
    | Ok _ -> true
    | Error _ -> false

let isError<'Error, 'T> (result: Result<'T, 'Error>) : bool =
    match result with
    | Ok _ -> false
    | Error _ -> true

let contains<'Error, 'T when 'T: equality> (value: 'T) (result: Result<'T, 'Error>) : bool =
    match result with
    | Ok x -> x = value
    | Error _ -> false

let count<'Error, 'T> (result: Result<'T, 'Error>) : int =
    match result with
    | Ok _ -> 1
    | Error _ -> 0

let defaultValue<'Error, 'T> (value: 'T) (result: Result<'T, 'Error>) : 'T =
    match result with
    | Ok x -> x
    | Error _ -> value

let defaultWith<'Error, 'T> (defThunk: 'Error -> 'T) (result: Result<'T, 'Error>) : 'T =
    match result with
    | Ok x -> x
    | Error e -> defThunk e

let exists<'Error, 'T> (predicate: 'T -> bool) (result: Result<'T, 'Error>) : bool =
    match result with
    | Ok x -> predicate x
    | Error _ -> false

let forAll<'Error, 'T> (predicate: 'T -> bool) (result: Result<'T, 'Error>) : bool =
    match result with
    | Ok x -> predicate x
    | Error _ -> true

let fold<'Error, 'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (result: Result<'T, 'Error>) : 'State =
    match result with
    | Ok x -> folder state x
    | Error _ -> state

let foldBack<'Error, 'State, 'T>
    (folder: 'T -> 'State -> 'State)
    (result: Result<'T, 'Error>)
    (state: 'State)
    : 'State
    =
    match result with
    | Ok x -> folder x state
    | Error _ -> state

let iterate<'Error, 'T> (action: 'T -> unit) (result: Result<'T, 'Error>) : unit =
    match result with
    | Ok x -> action x
    | Error _ -> ()

let toArray<'Error, 'T> (result: Result<'T, 'Error>) : 'T[] =
    match result with
    | Ok x -> [| x |]
    | Error _ -> [||]

let toList<'Error, 'T> (result: Result<'T, 'Error>) : 'T list =
    match result with
    | Ok x -> [ x ]
    | Error _ -> []

let toOption<'Error, 'T> (result: Result<'T, 'Error>) : 'T option =
    match result with
    | Ok x -> Some x
    | Error _ -> None

let toValueOption<'Error, 'T> (result: Result<'T, 'Error>) : 'T option =
    match result with
    | Ok x -> Some x
    | Error _ -> None
