// Message passing: four threads post batches (a ResizeArray, a list) to a MailboxProcessor,
// which changes and sums them; the total comes back with PostAndReply.
open System.Threading

type Msg =
    | Batch of ResizeArray<int>
    | Items of int list
    | Total of AsyncReplyChannel<int64>

let posters = 4
let perPoster = 20000
let size = 64

[<EntryPoint>]
let main _ =
    let mb =
        MailboxProcessor.Start(fun inbox ->
            let rec loop (total: int64) =
                async {
                    match! inbox.Receive() with
                    | Batch b ->
                        b.Add 1
                        let mutable s = 0L

                        for i in 0 .. b.Count - 1 do
                            b.[i] <- b.[i] + 1
                            s <- s + int64 b.[i]

                        return! loop (total + s)
                    | Items xs ->
                        let ys = List.map (fun x -> x * 2) xs
                        return! loop (total + int64 (List.sum ys))
                    | Total ch ->
                        ch.Reply total
                        return! loop total
                }

            loop 0L
        )

    let threads =
        [
            for p in 1..posters ->
                Thread(fun () ->
                    for i in 1..perPoster do
                        if i % 2 = 0 then
                            mb.Post(Batch(ResizeArray [ for k in 1..size -> k + p ]))
                        else
                            mb.Post(Items [ for k in 1..size -> k * p ])
                )
        ]

    for t in threads do
        t.Start()

    for t in threads do
        t.Join()

    printfn "%d" (mb.PostAndReply(fun ch -> Total ch))
    0
