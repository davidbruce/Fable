module Values

// Variables and values that live longer than one call: a `let mutable` that a function
// inside its function uses (F# makes it a ref cell that both share), and module-level values,
// which are computed when the program starts, in the order of the files, and can be assigned
// if they are mutable. `run` returns the number of failed checks.

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

let same (expected: string) (actual: string) : int =
    if actual = expected then
        0
    else
        1

// ---- module-level values ----
let limit = 10
let squares = [ 1; limit - 6; 9 ]
let title = "values " + string limit
let table = Array.init 4 (fun i -> i * limit)
let origin = Helpers.origin ()
let mutable counter = 0
let mutable log = ""
let mutable best: string option = None

type Config =
    {
        Name: string
        mutable Level: int
    }

let config =
    {
        Name = title + "!"
        Level = 1
    }

let note (s: string) : unit =
    counter <- counter + 1
    log <- log + s + ";"

    match best with
    | Some b when b.Length >= s.Length -> ()
    | _ -> best <- Some s

let rec sumOf (xs: int list) : int =
    match xs with
    | [] -> 0
    | h :: t -> h + sumOf t

let moduleValues () : int =
    note "a"
    note "ccc"
    note "bb"
    table.[0] <- 99
    config.Level <- config.Level + 1
    let visits = Helpers.visit "x" + Helpers.visit "yy"
    Helpers.hits <- Helpers.hits + 10

    check (limit = 10 && sumOf squares = 14 && sumOf Helpers.primes = 28)
    + same "values 10|helpers 10" (title + "|" + Helpers.banner)
    + check (table.[0] = 99 && table.[3] = 30 && origin = Helpers.origin ())
    + check (counter = 3 && best = Some "ccc")
    + same "a;ccc;bb;" log
    + same "values 10!" config.Name
    + check (config.Level = 2 && visits = 3 && Helpers.hits = 12)
    + same "yy#2" Helpers.lastSeen

// ---- a `let mutable` that a function inside uses ----
let rec each (f: int -> unit) (xs: int list) : unit =
    match xs with
    | [] -> ()
    | h :: t ->
        f h
        each f t

let counterFrom (start: int) : (unit -> int) =
    let mutable n = start

    fun () ->
        n <- n + 1
        n

let captured () : int =
    let mutable total = 0
    let mutable names = ""
    let mutable last = [ 0 ]
    each (fun x -> total <- total + x) [ 1; 2; 3 ]

    each
        (fun x ->
            names <- names + string x + ","
            last <- x :: last
        )
        [ 7; 8 ]

    total <- total * 2
    let add k = total <- total + k
    add 4
    let next = counterFrom 10
    let other = counterFrom 100
    let a = next ()
    let b = next ()
    let c = other ()

    check (total = 16 && a = 11 && b = 12 && c = 101)
    + same "7,8," names
    + check (last = [ 8; 7; 0 ])

let run () : int =
    // (what the module-level values hold stays alive until the program ends, so only the
    // second part is checked for cells left behind here; the program's end checks the rest)
    let first = moduleValues ()
    let before = liveCells ()
    let failed = first + captured ()
    printfn "values: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
