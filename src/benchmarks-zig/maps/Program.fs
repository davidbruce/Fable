module Program

// F#'s Map and Set: insertion, lookup and removal of many keys.

[<EntryPoint>]
let main _ =
    let mutable m = Map.empty
    let n = 200000

    for i in 0 .. n - 1 do
        m <- Map.add ((i * 7919) % n) i m

    let mutable found = 0L

    for i in 0 .. n - 1 do
        match Map.tryFind i m with
        | Some v -> found <- found + int64 v
        | None -> ()

    for i in 0..2 .. n - 1 do
        m <- Map.remove i m

    let s = Set.ofList [ for i in 0 .. n - 1 -> i % 1000 ]
    printfn "%d %d %d" found m.Count s.Count
    0
