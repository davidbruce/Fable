/// F#'s `Option` module, written in F# and compiled by the Zig target itself (see List.fs).
module Fable.Library.Zig.Option

let map<'T, 'U> (mapping: 'T -> 'U) (option: 'T option) : 'U option =
    match option with
    | Some x -> Some(mapping x)
    | None -> None

let map2<'T1, 'T2, 'U> (mapping: 'T1 -> 'T2 -> 'U) (option1: 'T1 option) (option2: 'T2 option) : 'U option =
    match option1, option2 with
    | Some x, Some y -> Some(mapping x y)
    | _ -> None

let bind<'T, 'U> (binder: 'T -> 'U option) (option: 'T option) : 'U option =
    match option with
    | Some x -> binder x
    | None -> None

let defaultValue<'T> (value: 'T) (option: 'T option) : 'T =
    match option with
    | Some x -> x
    | None -> value

let defaultWith<'T> (defThunk: unit -> 'T) (option: 'T option) : 'T =
    match option with
    | Some x -> x
    | None -> defThunk ()

let orElse<'T> (ifNone: 'T option) (option: 'T option) : 'T option =
    match option with
    | Some _ -> option
    | None -> ifNone

let orElseWith<'T> (ifNoneThunk: unit -> 'T option) (option: 'T option) : 'T option =
    match option with
    | Some _ -> option
    | None -> ifNoneThunk ()

let isSome<'T> (option: 'T option) : bool =
    match option with
    | Some _ -> true
    | None -> false

let isNone<'T> (option: 'T option) : bool =
    match option with
    | Some _ -> false
    | None -> true

let getValue<'T> (option: 'T option) : 'T =
    match option with
    | Some x -> x
    | None -> invalidArg "option" "The option value was None"

let iterate<'T> (action: 'T -> unit) (option: 'T option) : unit =
    match option with
    | Some x -> action x
    | None -> ()

let filter<'T> (predicate: 'T -> bool) (option: 'T option) : 'T option =
    match option with
    | Some x when predicate x -> option
    | _ -> None

let exists<'T> (predicate: 'T -> bool) (option: 'T option) : bool =
    match option with
    | Some x -> predicate x
    | None -> false

let forAll<'T> (predicate: 'T -> bool) (option: 'T option) : bool =
    match option with
    | Some x -> predicate x
    | None -> true

let fold<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (option: 'T option) : 'State =
    match option with
    | Some x -> folder state x
    | None -> state

let count<'T> (option: 'T option) : int =
    match option with
    | Some _ -> 1
    | None -> 0

let contains<'T when 'T: equality> (value: 'T) (option: 'T option) : bool =
    match option with
    | Some x -> x = value
    | None -> false

let flatten<'T> (option: 'T option option) : 'T option =
    match option with
    | Some inner -> inner
    | None -> None

let toList<'T> (option: 'T option) : 'T list =
    match option with
    | Some x -> [ x ]
    | None -> []

let toArray<'T> (option: 'T option) : 'T[] =
    match option with
    | Some x -> [| x |]
    | None -> [||]
