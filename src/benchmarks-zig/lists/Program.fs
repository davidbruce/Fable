module Program

// F# lists: building, mapping, filtering, folding and sorting, many times over.

[<EntryPoint>]
let main _ =
    let mutable total = 0L

    for round in 1..40 do
        let xs = List.init 200000 (fun i -> (i * 7919 + round) % 100003)
        let ys = xs |> List.map (fun x -> x * 3) |> List.filter (fun x -> x % 2 = 0)
        let sorted = List.sort ys

        total <-
            total
            + int64 (List.fold (+) 0 ys)
            + int64 (List.head sorted)
            + int64 (List.length sorted)

    printfn "%d" total
    0
