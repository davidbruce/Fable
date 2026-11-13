module Program

// Strings: building with StringBuilder and with +, splitting, joining and searching.

[<EntryPoint>]
let main _ =
    let sb = System.Text.StringBuilder()

    for i in 1..300000 do
        sb.Append(i).Append(',') |> ignore

    let text = sb.ToString()
    let parts = text.Split(',')
    let joined = System.String.Join(";", parts)
    let mutable grown = ""

    for i in 1..100000 do
        grown <- grown + string (i % 10)

    let mutable count = 0

    for p in parts do
        if p.Contains "7" then
            count <- count + 1

    printfn "%d %d %d %d" text.Length joined.Length grown.Length count
    0
