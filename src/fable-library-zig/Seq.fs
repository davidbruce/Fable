/// F#'s `seq`, written in F# and compiled by the Zig target itself (see List.fs). A sequence is
/// a function that starts a walk; a walk is a function that gives the next item, or None at
/// the end. Nothing is computed before it is asked for, as on .NET. A program's `seq<'T>` is
/// this `SeqOf`; the runtime knows it by its field, to write it with `%A` (`seq [1; 2; ...]`).
module Fable.Library.Zig.Seq

/// A walk: the function that gives the next item.
type Walk<'T> = { next: unit -> 'T option }

type SeqOf<'T> = { fable_seq: unit -> Walk<'T> }

let private make (start: unit -> Walk<'T>) : SeqOf<'T> = { fable_seq = start }

let private walker (next: unit -> 'T option) : Walk<'T> = { next = next }

let private walk (source: SeqOf<'T>) : Walk<'T> = source.fable_seq ()

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
        let mutable first = true
        let mutable current = walk source1

        let rec next () =
            match current.next () with
            | Some x -> Some x
            | None ->
                if first then
                    first <- false
                    current <- walk source2
                    next ()
                else
                    None

        walker next
    )

let map<'T, 'U> (mapping: 'T -> 'U) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let w = walk source

        walker
        <| fun () ->
            match w.next () with
            | Some x -> Some(mapping x)
            | None -> None
    )

let mapIndexed<'T, 'U> (mapping: int -> 'T -> 'U) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let w = walk source
        let mutable i = -1

        walker
        <| fun () ->
            match w.next () with
            | Some x ->
                i <- i + 1
                Some(mapping i x)
            | None -> None
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

        walker next
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

        walker next
    )

let collect<'T, 'U> (mapping: 'T -> SeqOf<'U>) (source: SeqOf<'T>) : SeqOf<'U> =
    make (fun () ->
        let outer = walk source
        let mutable inner: Walk<'U> option = None

        let rec next () =
            match inner with
            | Some w ->
                match w.next () with
                | Some y -> Some y
                | None ->
                    inner <- None
                    next ()
            | None ->
                match outer.next () with
                | Some x ->
                    inner <- Some(walk (mapping x))
                    next ()
                | None -> None

        walker next
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

        walker
        <| fun () ->
            if taken = count then
                None
            else
                match w.next () with
                | Some x ->
                    taken <- taken + 1
                    Some x
                | None ->
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

let truncate<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable taken = 0

        walker
        <| fun () ->
            if taken >= count then
                None
            else
                taken <- taken + 1
                w.next ()
    )

let skip<'T> (count: int) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable skipped = false

        walker
        <| fun () ->
            if not skipped then
                skipped <- true

                for i in 1..count do
                    match w.next () with
                    | Some _ -> ()
                    | None ->
                        raise (
                            System.ArgumentException(
                                "The input sequence has an insufficient number of elements.\nnumber of elements: "
                                + string count
                                + " (Parameter 'count')"
                            )
                        )

            w.next ()
    )

let takeWhile<'T> (predicate: 'T -> bool) (source: SeqOf<'T>) : SeqOf<'T> =
    make (fun () ->
        let w = walk source
        let mutable ended = false

        walker
        <| fun () ->
            if ended then
                None
            else
                match w.next () with
                | Some x when predicate x -> Some x
                | _ ->
                    ended <- true
                    None
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

        walker next
    )

let zip<'T1, 'T2> (source1: SeqOf<'T1>) (source2: SeqOf<'T2>) : SeqOf<'T1 * 'T2> =
    make (fun () ->
        let a = walk source1
        let b = walk source2

        walker
        <| fun () ->
            match a.next (), b.next () with
            | Some x, Some y -> Some(x, y)
            | _ -> None
    )

let indexed<'T> (source: SeqOf<'T>) : SeqOf<int * 'T> = mapIndexed (fun i x -> (i, x)) source

let pairwise<'T> (source: SeqOf<'T>) : SeqOf<'T * 'T> =
    make (fun () ->
        let w = walk source
        let mutable last = w.next ()

        walker
        <| fun () ->
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

// ---- what walks a sequence to its end ----

let iterate<'T> (action: 'T -> unit) (source: SeqOf<'T>) : unit =
    let w = walk source
    let mutable go = true

    while go do
        match w.next () with
        | Some x -> action x
        | None -> go <- false

let iterateIndexed<'T> (action: int -> 'T -> unit) (source: SeqOf<'T>) : unit =
    let mutable i = 0

    iterate
        (fun x ->
            action i x
            i <- i + 1
        )
        source

let fold<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (source: SeqOf<'T>) : 'State =
    let w = walk source
    let mutable acc = state
    let mutable go = true

    while go do
        match w.next () with
        | Some x -> acc <- folder acc x
        | None -> go <- false

    acc

let toList<'T> (source: SeqOf<'T>) : 'T list =
    List.rev (fold (fun acc x -> x :: acc) [] source)

let toArray<'T> (source: SeqOf<'T>) : 'T[] = Array.ofList (toList source)

let length<'T> (source: SeqOf<'T>) : int = fold (fun n _ -> n + 1) 0 source

let isEmpty<'T> (source: SeqOf<'T>) : bool =
    match (walk source).next() with
    | Some _ -> false
    | None -> true

let tryHead<'T> (source: SeqOf<'T>) : 'T option = (walk source).next()

let head<'T> (source: SeqOf<'T>) : 'T =
    match (walk source).next() with
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
        let w = walk source
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

let distinct<'T when 'T: equality> (source: SeqOf<'T>) : SeqOf<'T> =
    delay (fun () -> ofList (List.distinct (toList source)))

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

let cache<'T> (source: SeqOf<'T>) : SeqOf<'T> =
    let mutable saved: 'T list option = None

    delay (fun () ->
        match saved with
        | Some items -> ofList items
        | None ->
            let items = toList source
            saved <- Some items
            ofList items
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
