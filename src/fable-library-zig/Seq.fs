/// F#'s `seq`, written in F# and compiled by the Zig target itself (see List.fs). A sequence is
/// a function that starts a walk; a walk is a function that gives the next item, or None at
/// the end. Nothing is computed before it is asked for, as on .NET. A program's `seq<'T>` is
/// this `SeqOf`; the runtime knows it by its field, to write it with `%A` (`seq [1; 2; ...]`).
module Fable.Library.Zig.Seq

/// A walk: `next` gives the next item, and `close` runs any cleanup if stopped early.
type Walk<'T> =
    {
        next: unit -> 'T option
        close: unit -> unit
    }

type SeqOf<'T> = { fable_seq: unit -> Walk<'T> }

let private make (start: unit -> Walk<'T>) : SeqOf<'T> = { fable_seq = start }

let private noop () = ()

let private walker (next: unit -> 'T option) : Walk<'T> =
    {
        next = next
        close = noop
    }

let private walkerClose (next: unit -> 'T option) (close: unit -> unit) : Walk<'T> =
    {
        next = next
        close = close
    }

let private walk (source: SeqOf<'T>) : Walk<'T> = source.fable_seq ()

let private walking (source: SeqOf<'T>) (useWalk: Walk<'T> -> 'R) : 'R =
    let w = walk source

    try
        useWalk w
    finally
        w.close ()

let private walking2 (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) (useWalks: Walk<'T1> -> Walk<'T2> -> 'R) : 'R =
    walking source1 (fun a -> walking source2 (fun b -> useWalks a b))

let private walkPair (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : Walk<'T1> * Walk<'T2> =
    let a = walk source1

    let b =
        try
            walk source2
        with _ ->
            a.close ()
            reraise ()

    a, b

let private emptyInput () =
    invalidArg "source" "The input sequence was empty."

let private notFound () =
    raise (
        System.Collections.Generic.KeyNotFoundException
            "An index satisfying the predicate was not found in the collection."
    )

let empty<'T> () : SeqOf<'T> =
    make (fun () -> walker (fun () -> None))

let singleton<'T> (value: 'T) : SeqOf<'T> =
    make (fun () ->
        let mutable given = false

        walker
        <| fun () ->
            if given then
                None
            else
                given <- true
                Some value
    )

let delay<'T> (generator: unit -> SeqOf<'T>) : SeqOf<'T> = make (fun () -> walk (generator ()))

let ofList<'T> (source: 'T list) : SeqOf<'T> =
    make (fun () ->
        let mutable rest = source

        walker
        <| fun () ->
            match rest with
            | x :: tail ->
                rest <- tail
                Some x
            | [] -> None
    )

let ofArray<'T> (source: 'T[]) : SeqOf<'T> =
    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            if i < source.Length then
                i <- i + 1
                Some source.[i - 1]
            else
                None
    )

let append<'T> (source1: SeqOf<'T>) (source2: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let mutable stage = 0
        let mutable current: Walk<'T> option = Some(walk source1)

        let closeCurrent () =
            match current with
            | Some w ->
                current <- None
                w.close ()
            | None -> ()

        let close () =
            stage <- 2
            closeCurrent ()

        let rec next () =
            match current with
            | None -> None
            | Some w ->
                match w.next () with
                | Some x -> Some x
                | None ->
                    closeCurrent ()

                    if stage = 0 then
                        stage <- 1
                        current <- Some(walk source2)
                        next ()
                    else
                        stage <- 2
                        None

        walkerClose next close
    )

// ---- what `seq { }` is made of besides `for` and `yield` ----

/// `while guard () do yield! source` in a sequence expression: `source` is walked anew each
/// time round
let enumerateWhile<'T> (guard: unit -> bool) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let mutable current: Walk<'T> option = None
        let mutable closed = false

        let close () =
            closed <- true

            match current with
            | Some w ->
                current <- None
                w.close ()
            | None -> ()

        let rec next () =
            if closed then
                None
            else
                match current with
                | Some w ->
                    match w.next () with
                    | Some x -> Some x
                    | None ->
                        current <- None
                        w.close ()
                        next ()
                | None ->
                    if guard () then
                        current <- Some(walk source)
                        next ()
                    else
                        closed <- true
                        None

        walkerClose next close
    )

/// `try yield! source finally compensation ()`: the compensation runs once, when the walk ends,
/// raises, or is closed early.
let enumerateThenFinally<'T> (source: SeqOf<'T>) (compensation: unit -> unit) : SeqOf<'T> =
    make (fun () ->
        let mutable finished = false
        let mutable current: Walk<'T> option = None

        let finish () =
            if not finished then
                finished <- true
                let wOpt = current
                current <- None

                try
                    match wOpt with
                    | Some w -> w.close ()
                    | None -> ()
                finally
                    compensation ()

        walkerClose
            (fun () ->
                if finished then
                    None
                else
                    let r =
                        try
                            let w =
                                match current with
                                | Some w -> w
                                | None ->
                                    let w = walk source
                                    current <- Some w
                                    w

                            w.next ()
                        with _ ->
                            finish ()
                            reraise ()

                    match r with
                    | Some x -> Some x
                    | None ->
                        finish ()
                        None
            )
            finish
    )

/// `try yield! source with e -> yield! handler e` (F#'s `filter` says whether the handler takes
/// the exception: 1 if it does)
let enumerateTryWith<'T> (source: SeqOf<'T>) (filter: exn -> int) (handler: exn -> SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let mutable current: Walk<'T> option = None
        let mutable handled = false
        let mutable closed = false

        let closeCurrent () =
            match current with
            | Some w ->
                current <- None
                w.close ()
            | None -> ()

        let close () =
            closed <- true
            closeCurrent ()

        let rec next () =
            if closed then
                None
            else
                match current with
                | None when not handled ->
                    let w =
                        try
                            Choice1Of2(walk source)
                        with e ->
                            Choice2Of2 e

                    match w with
                    | Choice1Of2 w -> current <- Some w
                    | Choice2Of2 e ->
                        if filter e = 1 then
                            handled <- true
                            current <- Some(walk (handler e))
                        else
                            raise e

                    next ()
                | None -> None
                | Some w when handled -> w.next ()
                | Some w ->
                    let r =
                        try
                            Choice1Of2(w.next ())
                        with e ->
                            Choice2Of2 e

                    match r with
                    | Choice1Of2 x -> x
                    | Choice2Of2 e ->
                        closeCurrent ()

                        if filter e = 1 then
                            handled <- true
                            current <- Some(walk (handler e))
                            next ()
                        else
                            raise e

        walkerClose next close
    )

let map<'T, 'U> (mapping: 'T -> 'U) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let w = walk source

        walkerClose
            (fun () ->
                match w.next () with
                | Some x -> Some(mapping x)
                | None -> None
            )
            w.close
    )

let mapIndexed<'T, 'U> (mapping: int -> 'T -> 'U) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let w = walk source
        let mutable i = -1

        walkerClose
            (fun () ->
                match w.next () with
                | Some x ->
                    i <- i + 1
                    Some(mapping i x)
                | None -> None
            )
            w.close
    )

let filter<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source

        let rec next () =
            match w.next () with
            | Some x ->
                if predicate x then
                    Some x
                else
                    next ()
            | None -> None

        walkerClose next w.close
    )

let choose<'T, 'U> (chooser: 'T -> 'U option) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let w = walk source

        let rec next () =
            match w.next () with
            | Some x ->
                match chooser x with
                | Some y -> Some y
                | None -> next ()
            | None -> None

        walkerClose next w.close
    )

let collect<'T, 'U> (mapping: 'T -> SeqOf<'U>) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let outer = walk source
        let mutable inner: Walk<'U> option = None
        let mutable closed = false

        let close () =
            if not closed then
                closed <- true

                try
                    match inner with
                    | Some w ->
                        inner <- None
                        w.close ()
                    | None -> ()
                finally
                    outer.close ()

        let rec next () =
            if closed then
                None
            else
                match inner with
                | Some w ->
                    match w.next () with
                    | Some y -> Some y
                    | None ->
                        inner <- None
                        w.close ()
                        next ()
                | None ->
                    match outer.next () with
                    | Some x ->
                        inner <- Some(walk (mapping x))
                        next ()
                    | None ->
                        close ()
                        None

        walkerClose next close
    )

let concat<'T> (sources: SeqOf<SeqOf<'T>>) : SeqOf<'T> = collect id sources

let initialize<'T> (count: int) (initializer: int -> 'T) : SeqOf<'T> =
    if count < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            if i < count then
                i <- i + 1
                Some(initializer (i - 1))
            else
                None
    )

let initializeInfinite<'T> (initializer: int -> 'T) : SeqOf<'T> =
    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            i <- i + 1
            Some(initializer (i - 1))
    )

let unfold<'State, 'T> (generator: 'State -> ('T * 'State) option) (state: 'State) : SeqOf<'T> =
    make (fun () ->
        let mutable s = state

        walker
        <| fun () ->
            match generator s with
            | Some(x, next) ->
                s <- next
                Some x
            | None -> None
    )

let take<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    if count < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

    make (fun () ->
        let w = walk source
        let mutable taken = 0
        let mutable closed = false

        let close () =
            if not closed then
                closed <- true
                w.close ()

        walkerClose
            (fun () ->
                if closed then
                    None
                elif taken = count then
                    close ()
                    None
                else
                    match w.next () with
                    | Some x ->
                        taken <- taken + 1
                        Some x
                    | None ->
                        close ()

                        raise (
                            System.InvalidOperationException(
                                "The input sequence has an insufficient number of elements.\ntried to take "
                                + string (count - taken)
                                + " past the end of the seq. Use Seq.truncate to get "
                                + string taken
                                + " or less elements"
                            )
                        )
            )
            close
    )

let truncate<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    if count <= 0 then
        empty ()
    else
        make (fun () ->
            let w = walk source
            let mutable taken = 0
            let mutable closed = false

            let close () =
                if not closed then
                    closed <- true
                    w.close ()

            walkerClose
                (fun () ->
                    if closed then
                        None
                    elif taken >= count then
                        close ()
                        None
                    else
                        taken <- taken + 1
                        w.next ()
                )
                close
        )

let skip<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable skipped = false

        walkerClose
            (fun () ->
                if not skipped then
                    skipped <- true

                    for i in 1..count do
                        match w.next () with
                        | Some _ -> ()
                        | None ->
                            // (FSharp.Core's message, as it is)
                            raise (
                                System.InvalidOperationException(
                                    "tried to skip The input sequence has an insufficient number of elements. "
                                    + string i
                                    + " past the end of the seq"
                                )
                            )

                w.next ()
            )
            w.close
    )

let takeWhile<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable ended = false

        let close () =
            if not ended then
                ended <- true
                w.close ()

        walkerClose
            (fun () ->
                if ended then
                    None
                else
                    match w.next () with
                    | Some x when predicate x -> Some x
                    | _ ->
                        close ()
                        None
            )
            close
    )

let skipWhile<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable skipping = true

        let rec next () =
            match w.next () with
            | Some x when skipping && predicate x -> next ()
            | other ->
                skipping <- false
                other

        walkerClose next w.close
    )

let zip<'T1, 'T2> (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : SeqOf<'T1 * 'T2> =
    make (fun () ->
        let a, b = walkPair source1 source2
        let mutable closed = false

        let close () =
            if not closed then
                closed <- true

                try
                    a.close ()
                finally
                    b.close ()

        walkerClose
            (fun () ->
                if closed then
                    None
                else
                    match a.next (), b.next () with
                    | Some x, Some y -> Some(x, y)
                    | _ ->
                        close ()
                        None
            )
            close
    )

let indexed<'T> (source: SeqOf<'T>) : SeqOf<int * 'T> = mapIndexed (fun i x -> (i, x)) source

let pairwise<'T> (source: SeqOf<'T>) : SeqOf<'T * 'T> =
    make (fun () ->
        let w = walk source

        let mutable last =
            try
                w.next ()
            with _ ->
                w.close ()
                reraise ()

        walkerClose
            (fun () ->
                match last with
                | Some a ->
                    match w.next () with
                    | Some b ->
                        last <- Some b
                        Some(a, b)
                    | None ->
                        last <- None
                        None
                | None -> None
            )
            w.close
    )

// ---- what walks a sequence to its end ----

let iterate<'T> (action: 'T -> unit) (source: SeqOf<'T>) : unit =
    walking
        source
        (fun w ->
            let mutable go = true

            while go do
                match w.next () with
                | Some x -> action x
                | None -> go <- false
        )

let iterateIndexed<'T> (action: int -> 'T -> unit) (source: SeqOf<'T>) : unit =
    let mutable i = 0

    iterate
        (fun x ->
            action i x
            i <- i + 1
        )
        source

let fold<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (source: SeqOf<'T>) : 'State =
    walking
        source
        (fun w ->
            let mutable acc = state
            let mutable go = true

            while go do
                match w.next () with
                | Some x -> acc <- folder acc x
                | None -> go <- false

            acc
        )

let toList<'T> (source: SeqOf<'T>) : 'T list =
    List.rev (fold (fun acc x -> x :: acc) [] source)

let toArray<'T> (source: SeqOf<'T>) : 'T[] = Array.ofList (toList source)

/// Rows made columns, grouped by index (jagged rows give shorter columns, as FSharp.Core does)
let transpose<'T> (sources: SeqOf<SeqOf<'T>>) : SeqOf<SeqOf<'T>> =
    delay (fun () ->
        let rows = toArray (map toArray sources)

        let width =
            rows
            |> Array.fold
                (fun w (r: 'T[]) ->
                    if r.Length > w then
                        r.Length
                    else
                        w
                )
                0

        ofArray (
            Array.init
                width
                (fun i ->
                    ofArray (
                        rows
                        |> Array.filter (fun (r: 'T[]) -> i < r.Length)
                        |> Array.map (fun r -> r.[i])
                    )
                )
        )
    )

let length<'T> (source: SeqOf<'T>) : int = fold (fun n _ -> n + 1) 0 source

let isEmpty<'T> (source: SeqOf<'T>) : bool =
    walking
        source
        (fun w ->
            match w.next () with
            | Some _ -> false
            | None -> true
        )

let tryHead<'T> (source: SeqOf<'T>) : 'T option = walking source (fun w -> w.next ())

let head<'T> (source: SeqOf<'T>) : 'T =
    match tryHead source with
    | Some x -> x
    | None -> emptyInput ()

let tryLast<'T> (source: SeqOf<'T>) : 'T option = fold (fun _ x -> Some x) None source

let last<'T> (source: SeqOf<'T>) : 'T =
    match tryLast source with
    | Some x -> x
    | None -> emptyInput ()

let tryItem<'T> (index: int) (source: SeqOf<'T>) : 'T option =
    if index < 0 then
        None
    else
        walking
            source
            (fun w ->
                let mutable i = 0
                let mutable result = None
                let mutable go = true

                while go do
                    match w.next () with
                    | Some x ->
                        if i = index then
                            result <- Some x
                            go <- false

                        i <- i + 1
                    | None -> go <- false

                result
            )

let item<'T> (index: int) (source: SeqOf<'T>) : 'T =
    match tryItem index source with
    | Some x -> x
    | None ->
        invalidArg
            "index"
            "The input sequence has an insufficient number of elements.\nThe index is outside the legal range."

let tryFind<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : 'T option = tryHead (filter predicate source)

let find<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : 'T =
    match tryFind predicate source with
    | Some x -> x
    | None -> notFound ()

let tryPick<'T, 'U> (chooser: 'T -> 'U option) (source: SeqOf<'T>) : 'U option = tryHead (choose chooser source)

let pick<'T, 'U> (chooser: 'T -> 'U option) (source: SeqOf<'T>) : 'U =
    match tryPick chooser source with
    | Some x -> x
    | None -> notFound ()

let exists<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : bool = (tryFind predicate source).IsSome

let forAll<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : bool =
    (tryFind (fun x -> not (predicate x)) source).IsNone

let contains<'T when 'T: equality> (value: 'T) (source: SeqOf<'T>) : bool = exists (fun x -> x = value) source

let reduce<'T> (reduction: 'T -> 'T -> 'T) (source: SeqOf<'T>) : 'T =
    match toList source with
    | first :: rest -> List.fold reduction first rest
    | [] -> emptyInput ()

// ---- what needs the whole sequence: by its list ----

let reverse<'T> (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.rev (toList source)))

let sort<'T when 'T: comparison> (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.sort (toList source)))

let sortBy<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.sortBy projection (toList source)))

let sortDescending<'T when 'T: comparison> (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.sortDescending (toList source)))

let sortWith<'T> (comparer: 'T -> 'T -> int) (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.sortWith comparer (toList source)))

let distinct<'T when 'T: equality> (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let seen = System.Collections.Generic.HashSet<'T>()

        let rec next () =
            match w.next () with
            | Some x ->
                if seen.Add x then
                    Some x
                else
                    next ()
            | None -> None

        walkerClose next w.close
    )

let max<'T when 'T: comparison> (source: SeqOf<'T>) : 'T = List.max (toList source)

let min<'T when 'T: comparison> (source: SeqOf<'T>) : 'T = List.min (toList source)

let maxBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (source: SeqOf<'T>) : 'T =
    List.maxBy projection (toList source)

let minBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (source: SeqOf<'T>) : 'T =
    List.minBy projection (toList source)

let groupBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (source: SeqOf<'T>) : SeqOf<'Key * SeqOf<'T>> =
    delay (fun () ->
        ofList (
            List.map (fun (k: 'Key, items: 'T list) -> (k, ofList items)) (List.groupBy projection (toList source))
        )
    )

let countBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (source: SeqOf<'T>) : SeqOf<'Key * int> =
    delay (fun () -> ofList (List.countBy projection (toList source)))

/// `Seq.cache`: one walk of the source, made as far as an enumeration needs it (the source may
/// be infinite), its items kept for the enumerations after
let cache<'T> (source: SeqOf<'T>) : SeqOf<'T> =
    let items = ResizeArray<'T>()
    let mutable shared: Walk<'T> option = None
    let mutable finished = false

    let fill () =
        if finished then
            false
        else
            let w =
                match shared with
                | Some w -> w
                | None ->
                    let w = walk source
                    shared <- Some w
                    w

            match w.next () with
            | Some x ->
                items.Add x
                true
            | None ->
                finished <- true
                shared <- None
                w.close ()
                false

    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            if i < items.Count || fill () then
                i <- i + 1
                Some items.[i - 1]
            else
                None
    )

/// `seq { ... }` and `{ a .. b }`: what is given is the sequence.
let createSequence<'T> (source: SeqOf<'T>) : SeqOf<'T> = source

// ---- ranges: `a .. b` and `a .. step .. b` ----

let rangeInt (start: int) (step: int) (stop: int) : SeqOf<int> =
    if step = 0 then
        invalidArg "step" "The step of a range cannot be zero."

    make (fun () ->
        let mutable next = start

        let mutable ended =
            if step > 0 then
                start > stop
            else
                start < stop

        walker
        <| fun () ->
            if ended then
                None
            else
                let x = next

                if (step > 0 && x > stop - step) || (step < 0 && x < stop - step) then
                    ended <- true
                else
                    next <- x + step

                Some x
    )

let rangeInt64 (start: int64) (step: int64) (stop: int64) : SeqOf<int64> =
    if step = 0L then
        invalidArg "step" "The step of a range cannot be zero."

    make (fun () ->
        let mutable next = start

        let mutable ended =
            if step > 0L then
                start > stop
            else
                start < stop

        walker
        <| fun () ->
            if ended then
                None
            else
                let x = next

                if (step > 0L && x > stop - step) || (step < 0L && x < stop - step) then
                    ended <- true
                else
                    next <- x + step

                Some x
    )

let rangeUInt64 (start: uint64) (step: uint64) (stop: uint64) : SeqOf<uint64> =
    if step = 0UL then
        invalidArg "step" "The step of a range cannot be zero."

    make (fun () ->
        let mutable next = start
        let mutable ended = start > stop

        walker
        <| fun () ->
            if ended then
                None
            else
                let x = next

                // (what is left before the end, so that nothing wraps)
                if stop - x < step then
                    ended <- true
                else
                    next <- x + step

                Some x
    )

/// (decimal and bigint: no wrapping to fear)
let private rangeOf (zero: 'T) (start: 'T) (step: 'T) (stop: 'T) (add: 'T -> 'T -> 'T) : SeqOf<'T> =
    if step = zero then
        invalidArg "step" "The step of a range cannot be zero."

    make (fun () ->
        let mutable next = start

        walker
        <| fun () ->
            let x = next

            if (step > zero && x > stop) || (step < zero && x < stop) then
                None
            else
                next <- add x step
                Some x
    )

let rangeDecimal (start: decimal) (step: decimal) (stop: decimal) : SeqOf<decimal> = rangeOf 0m start step stop (+)

let rangeBigInt (start: bigint) (step: bigint) (stop: bigint) : SeqOf<bigint> = rangeOf 0I start step stop (+)

let rangeChar (start: char) (stop: char) : SeqOf<char> =
    map char (rangeInt (int start) 1 (int stop))

let rangeFloat (start: float) (step: float) (stop: float) : SeqOf<float> =
    if step = 0.0 then
        invalidArg "step" "The step of a range cannot be zero."

    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            let x = start + float i * step

            if (step > 0.0 && x > stop) || (step < 0.0 && x < stop) then
                None
            else
                i <- i + 1
                Some x
    )

let where<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : SeqOf<'T> = filter predicate source

let tail<'T> (source: SeqOf<'T>) : SeqOf<'T> =
    if isEmpty source then
        invalidArg "source" "The input sequence has an insufficient number of elements."

    skip 1 source

// ---- lazy: nothing is computed before it is asked for ----

let map2<'T1, 'T2, 'U> (mapping: 'T1 -> 'T2 -> 'U) (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : SeqOf<'U> =
    make (fun () ->
        let a, b = walkPair source1 source2
        let mutable closed = false

        let close () =
            if not closed then
                closed <- true

                try
                    a.close ()
                finally
                    b.close ()

        walkerClose
            (fun () ->
                if closed then
                    None
                else
                    match a.next () with
                    | Some x ->
                        match b.next () with
                        | Some y -> Some(mapping x y)
                        | None ->
                            close ()
                            None
                    | None ->
                        close ()
                        None
            )
            close
    )

let zip3<'T1, 'T2, 'T3> (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) (source3: SeqOf<'T3>) : SeqOf<'T1 * 'T2 * 'T3> =
    make (fun () ->
        let a, b = walkPair source1 source2

        let c =
            try
                walk source3
            with _ ->
                try
                    a.close ()
                finally
                    b.close ()

                reraise ()

        let mutable closed = false

        let close () =
            if not closed then
                closed <- true

                try
                    a.close ()
                finally
                    try
                        b.close ()
                    finally
                        c.close ()

        walkerClose
            (fun () ->
                if closed then
                    None
                else
                    match a.next (), b.next (), c.next () with
                    | Some x, Some y, Some z -> Some(x, y, z)
                    | _ ->
                        close ()
                        None
            )
            close
    )

let scan<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (source: SeqOf<'T>) : SeqOf<'State> =
    make (fun () ->
        let w = walk source
        let mutable acc = state
        let mutable started = false

        walkerClose
            (fun () ->
                if not started then
                    started <- true
                    Some acc
                else
                    match w.next () with
                    | Some x ->
                        acc <- folder acc x
                        Some acc
                    | None -> None
            )
            w.close
    )

let replicate<'T> (count: int) (initial: 'T) : SeqOf<'T> =
    if count < 0 then
        raise (System.ArgumentOutOfRangeException "count")

    initialize count (fun _ -> initial)

let distinctBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let seen = System.Collections.Generic.HashSet<'Key>()

        let rec next () =
            match w.next () with
            | Some x ->
                if seen.Add(projection x) then
                    Some x
                else
                    next ()
            | None -> None

        walkerClose next w.close
    )

let except<'T when 'T: equality> (itemsToExclude: SeqOf<'T>) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let seen = System.Collections.Generic.HashSet<'T>(toList itemsToExclude)

        let rec next () =
            match w.next () with
            | Some x ->
                if seen.Add x then
                    Some x
                else
                    next ()
            | None -> None

        walkerClose next w.close
    )

let windowed<'T> (windowSize: int) (source: SeqOf<'T>) : SeqOf<'T[]> =
    if windowSize <= 0 then
        invalidArg "windowSize" ("The input must be positive.\nwindowSize = " + string windowSize)

    make (fun () ->
        let w = walk source
        let window = ResizeArray<'T>()

        let rec next () =
            match w.next () with
            | Some x ->
                window.Add x

                if window.Count > windowSize then
                    window.RemoveAt 0

                if window.Count = windowSize then
                    Some(window.ToArray())
                else
                    next ()
            | None -> None

        walkerClose next w.close
    )

let chunkBySize<'T> (chunkSize: int) (source: SeqOf<'T>) : SeqOf<'T[]> =
    if chunkSize <= 0 then
        invalidArg "chunkSize" ("The input must be positive.\nchunkSize = " + string chunkSize)

    make (fun () ->
        let w = walk source
        let mutable finished = false

        walkerClose
            (fun () ->
                if finished then
                    None
                else
                    let chunk = ResizeArray<'T>()
                    let mutable go = true

                    while go && chunk.Count < chunkSize do
                        match w.next () with
                        | Some x -> chunk.Add x
                        | None ->
                            finished <- true
                            go <- false

                    if chunk.Count = 0 then
                        None
                    else
                        Some(chunk.ToArray())
            )
            w.close
    )

let cast<'T> (source: SeqOf<'T>) : SeqOf<'T> = source

let readOnly<'T> (source: SeqOf<'T>) : SeqOf<'T> = source

// ---- walking two at once ----

let iterate2<'T1, 'T2> (action: 'T1 -> 'T2 -> unit) (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : unit =
    walking2
        source1
        source2
        (fun a b ->
            let mutable go = true

            while go do
                match a.next () with
                | Some x ->
                    match b.next () with
                    | Some y -> action x y
                    | None -> go <- false
                | None -> go <- false
        )

let fold2<'State, 'T1, 'T2>
    (folder: 'State -> 'T1 -> 'T2 -> 'State)
    (state: 'State)
    (source1: SeqOf<'T1>)
    (source2: SeqOf<'T2>)
    : 'State
    =
    let mutable acc = state
    iterate2 (fun x y -> acc <- folder acc x y) source1 source2
    acc

let exists2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : bool =
    walking2
        source1
        source2
        (fun a b ->
            let mutable found = false
            let mutable go = true

            while go && not found do
                match a.next () with
                | Some x ->
                    match b.next () with
                    | Some y -> found <- predicate x y
                    | None -> go <- false
                | None -> go <- false

            found
        )

let forAll2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : bool =
    not (exists2 (fun x y -> not (predicate x y)) source1 source2)

let compareWith<'T> (comparer: 'T -> 'T -> int) (source1: SeqOf<'T>) (source2: SeqOf<'T>) : int =
    walking2
        source1
        source2
        (fun a b ->
            let mutable result = 0
            let mutable go = true

            while go do
                match a.next (), b.next () with
                | Some x, Some y ->
                    let c = comparer x y

                    if c <> 0 then
                        result <- c
                        go <- false
                | Some _, None ->
                    result <- 1
                    go <- false
                | None, Some _ ->
                    result <- -1
                    go <- false
                | None, None -> go <- false

            result
        )

// ---- what needs the whole sequence: through a list ----

let tryFindIndex<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : int option =
    walking
        source
        (fun w ->
            let mutable i = 0
            let mutable found = None
            let mutable go = true

            while go && found.IsNone do
                match w.next () with
                | Some x ->
                    if predicate x then
                        found <- Some i

                    i <- i + 1
                | None -> go <- false

            found
        )

let findIndex<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : int =
    match tryFindIndex predicate source with
    | Some i -> i
    | None -> notFound ()

let tryFindBack<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : 'T option =
    List.tryFindBack predicate (toList source)

let findBack<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : 'T =
    match tryFindBack predicate source with
    | Some x -> x
    | None -> notFound ()

let tryFindIndexBack<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : int option =
    List.tryFindIndexBack predicate (toList source)

let findIndexBack<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : int =
    match tryFindIndexBack predicate source with
    | Some i -> i
    | None -> notFound ()

let foldBack<'State, 'T> (folder: 'T -> 'State -> 'State) (source: SeqOf<'T>) (state: 'State) : 'State =
    List.foldBack folder (toList source) state

let foldBack2<'State, 'T1, 'T2>
    (folder: 'T1 -> 'T2 -> 'State -> 'State)
    (source1: SeqOf<'T1>)
    (source2: SeqOf<'T2>)
    (state: 'State)
    : 'State
    =
    List.foldBack (fun (x, y) acc -> folder x y acc) (toList (zip source1 source2)) state

let exactlyOne<'T> (source: SeqOf<'T>) : 'T =
    walking
        source
        (fun w ->
            match w.next () with
            | None -> emptyInput ()
            | Some x ->
                match w.next () with
                | None -> x
                | Some _ -> invalidArg "source" "The input sequence contains more than one element."
        )

let tryExactlyOne<'T> (source: SeqOf<'T>) : 'T option =
    walking
        source
        (fun w ->
            match w.next () with
            | None -> None
            | Some x ->
                match w.next () with
                | None -> Some x
                | Some _ -> None
        )

let reduceBack<'T> (reduction: 'T -> 'T -> 'T) (source: SeqOf<'T>) : 'T =
    match toList source with
    | [] -> emptyInput ()
    | items -> List.reduceBack reduction items

let sortByDescending<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.sortByDescending projection (toList source)))

let splitInto<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T[]> =
    if count <= 0 then
        invalidArg "count" ("The input must be positive.\ncount = " + string count)

    delay (fun () -> ofArray (Array.splitInto count (toArray source)))

let permute<'T> (indexMap: int -> int) (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofArray (Array.permute indexMap (toArray source)))

let mapFold<'Result, 'State, 'T>
    (mapping: 'State -> 'T -> 'Result * 'State)
    (state: 'State)
    (source: SeqOf<'T>)
    : SeqOf<'Result> * 'State
    =
    let results, final = List.mapFold mapping state (toList source)
    ofList results, final

let mapFoldBack<'Result, 'State, 'T>
    (mapping: 'T -> 'State -> 'Result * 'State)
    (source: SeqOf<'T>)
    (state: 'State)
    : SeqOf<'Result> * 'State
    =
    let results, final = List.mapFoldBack mapping (toList source) state
    ofList results, final

/// (as FSharp.Core: the second sequence is walked once, and kept)
let allPairs<'T1, 'T2> (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : SeqOf<'T1 * 'T2> =
    let kept = cache source2
    collect (fun x -> map (fun y -> (x, y)) kept) source1

let private outsideSeq () =
    invalidArg "index" "index must be within bounds of the array"

/// The items of `source` with what `edit` makes of the item at each position, and at the end
/// a check that `index` was inside (`allowEnd`: or just past the last item).
let private edited<'T>
    (index: int)
    (allowEnd: bool)
    (edit: int -> 'T -> 'T list)
    (atEnd: unit -> 'T list)
    (source: SeqOf<'T>)
    : SeqOf<'T>
    =
    if index < 0 then
        outsideSeq ()

    make (fun () ->
        let w = walk source
        let mutable i = 0
        let mutable pending: 'T list = []
        let mutable finished = false

        let rec next () =
            match pending with
            | x :: rest ->
                pending <- rest
                Some x
            | [] ->
                if finished then
                    None
                else
                    match w.next () with
                    | Some x ->
                        let here = i
                        i <- i + 1
                        pending <- edit here x
                        next ()
                    | None ->
                        finished <- true

                        if i < index || (i = index && not allowEnd) then
                            outsideSeq ()

                        pending <-
                            (if i = index then
                                 atEnd ()
                             else
                                 [])

                        next ()

        walkerClose next w.close
    )

let insertAt<'T> (index: int) (value: 'T) (source: SeqOf<'T>) : SeqOf<'T> =
    edited
        index
        true
        (fun i x ->
            if i = index then
                [ value; x ]
            else
                [ x ]
        )
        (fun () -> [ value ])
        source

let insertManyAt<'T> (index: int) (values: SeqOf<'T>) (source: SeqOf<'T>) : SeqOf<'T> =
    edited
        index
        true
        (fun i x ->
            if i = index then
                List.append (toList values) [ x ]
            else
                [ x ]
        )
        (fun () -> toList values)
        source

let removeAt<'T> (index: int) (source: SeqOf<'T>) : SeqOf<'T> =
    edited
        index
        false
        (fun i x ->
            if i = index then
                []
            else
                [ x ]
        )
        (fun () -> [])
        source

let removeManyAt<'T> (index: int) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    edited
        index
        false
        (fun i x ->
            if i >= index && i < index + count then
                []
            else
                [ x ]
        )
        (fun () -> [])
        source

let updateAt<'T> (index: int) (value: 'T) (source: SeqOf<'T>) : SeqOf<'T> =
    edited
        index
        false
        (fun i x ->
            if i = index then
                [ value ]
            else
                [ x ]
        )
        (fun () -> [])
        source

// ---- the random functions (F# 9): through an array, as FSharp.Core does ----

module RandomArray = Fable.Library.Zig.Array

let randomShuffleWith<'T> (random: System.Random) (source: SeqOf<'T>) : SeqOf<'T> =
    ofArray (RandomArray.randomShuffleWith random (toArray source))

let randomShuffleBy<'T> (randomizer: unit -> float) (source: SeqOf<'T>) : SeqOf<'T> =
    ofArray (RandomArray.randomShuffleBy randomizer (toArray source))

let randomShuffle<'T> (source: SeqOf<'T>) : SeqOf<'T> =
    randomShuffleWith System.Random.Shared source

let randomChoiceWith<'T> (random: System.Random) (source: SeqOf<'T>) : 'T =
    let a = toArray source
    a.[RandomArray.randomIndexWith random "The input sequence was empty." a.Length]

let randomChoiceBy<'T> (randomizer: unit -> float) (source: SeqOf<'T>) : 'T =
    let a = toArray source
    a.[RandomArray.randomIndexBy randomizer "The input sequence was empty." a.Length]

let randomChoice<'T> (source: SeqOf<'T>) : 'T =
    randomChoiceWith System.Random.Shared source

/// `count` draws, made anew on each walk (the input is checked at once, as .NET does)
let private choices<'T> (draw: int -> int) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    if count < 0 then
        RandomArray.negativeCount count

    let a = toArray source

    if a.Length = 0 then
        invalidArg "source" "The input sequence was empty."

    make (fun () ->
        let mutable i = 0

        walker
        <| fun () ->
            if i < count then
                i <- i + 1
                Some a.[draw a.Length]
            else
                None
    )

let randomChoicesWith<'T> (random: System.Random) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    choices (fun n -> random.Next n) count source

let randomChoicesBy<'T> (randomizer: unit -> float) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    choices (fun n -> int (float n * RandomArray.randomized randomizer)) count source

let randomChoices<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    randomChoicesWith System.Random.Shared count source

/// A sample drawn on each walk, as FSharp.Core's: the input is read and checked at once, and
/// what the draws keep (the pool they take from, or the indexes taken) is kept from one walk to
/// the next
let private sample<'T> (next: int -> int -> int) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    let a = toArray source
    let n = a.Length

    if count < 0 then
        RandomArray.negativeCount count

    if count > n then
        invalidArg "count" "The input sequence has an insufficient number of elements."

    if n <= RandomArray.sampleSetSize count then
        let pool = Array.copy a

        make (fun () ->
            let mutable i = 0

            walker
            <| fun () ->
                if i < count then
                    let j = next 0 (n - i)
                    let x = pool.[j]
                    pool.[j] <- pool.[n - i - 1]
                    i <- i + 1
                    Some x
                else
                    None
        )
    else
        let selected = System.Collections.Generic.HashSet<int>()

        make (fun () ->
            let mutable i = 0

            walker
            <| fun () ->
                if i < count then
                    let mutable j = next 0 n

                    while not (selected.Add j) do
                        j <- next 0 n

                    i <- i + 1
                    Some a.[j]
                else
                    None
        )

let randomSampleWith<'T> (random: System.Random) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    sample (fun lo hi -> random.Next(lo, hi)) count source

let randomSampleBy<'T> (randomizer: unit -> float) (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    sample (fun lo hi -> int (float (hi - lo) * RandomArray.randomized randomizer + float lo)) count source

let randomSample<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    randomSampleWith System.Random.Shared count source

// ---- enumerators: what a program's own `IEnumerable<'T>` gives, and what `GetEnumerator` of a
// sequence gives ----

/// A sequence that walks what a `GetEnumerator` of the program's gives (each walk asks anew;
/// the enumerator is disposed at the end)
let ofGetEnumerator<'T> (get: unit -> System.Collections.Generic.IEnumerator<'T>) : SeqOf<'T> =
    make (fun () ->
        let e = get ()
        let mutable ended = false

        let close () =
            if not ended then
                ended <- true
                e.Dispose()

        walkerClose
            (fun () ->
                if ended then
                    None
                elif e.MoveNext() then
                    Some e.Current
                else
                    close ()
                    None
            )
            close
    )

/// `(s :> IEnumerable<'T>).GetEnumerator()`: an enumerator over a walk of the sequence.
/// (`Reset` starts a new walk: what .NET's enumerators of arrays, lists and collections do; one of
/// a sequence expression raises NotSupportedException on .NET, here it walks the sequence again)
let getEnumerator<'T> (source: SeqOf<'T>) : System.Collections.Generic.IEnumerator<'T> =
    let mutable w = walk source
    let mutable current: 'T option = None

    let value () =
        match current with
        | Some x -> x
        | None -> invalidOp "Enumeration has either not started or has already finished."

    { new System.Collections.Generic.IEnumerator<'T> with
        member _.Current = value ()
      interface System.Collections.IEnumerator with
          member _.Current = box (value ())

          member _.MoveNext() =
              current <- w.next ()
              current.IsSome

          member _.Reset() =
              w.close ()
              w <- walk source
              current <- None
      interface System.IDisposable with
          member _.Dispose() = w.close ()
    }
