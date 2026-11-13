module Weak

// Weak references: they do not keep their target alive. Here a cell is freed as soon as its
// last reference goes (or, in a cycle, when the collector runs), so a weak reference sees it
// gone at once; on .NET that happens whenever the garbage collector runs, so those checks are
// made on the Zig target only. (So a weak reference sees its target gone right after the last
// use of the last strong reference, which on .NET may be much later.) `run` returns the number of failed checks.

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

type Node(name: string) =
    let mutable next: Node option = None
    member _.Name = name

    member _.Next
        with get () = next
        and set v = next <- v

type Cache() =
    let entries =
        System.Collections.Generic.Dictionary<string, System.WeakReference<Node>>()

    member _.Add(n: Node) =
        entries.[n.Name] <- System.WeakReference<Node>(n)

    member _.TryGet(name: string) : Node option =
        match entries.TryGetValue name with
        | true, w ->
            match w.TryGetTarget() with
            | true, n -> Some n
            | _ -> None
        | _ -> None

let lookup (w: System.WeakReference<Node>) : string =
    match w.TryGetTarget() with
    | true, n -> n.Name
    | _ -> "gone"

let run () : int =
    let before = liveCells ()
    let keep = Node("kept")
    let wKeep = System.WeakReference<Node>(keep)

    let wTemp =
        let temp = Node("temp")
        System.WeakReference<Node>(temp)

    let wCycle =
        let a = Node("a")
        let b = Node("b")
        a.Next <- Some b
        b.Next <- Some a
        System.WeakReference<Node>(a)

    let cache = Cache()
    cache.Add keep
    cache.Add(Node("short-lived"))
    System.GC.Collect()
    let other = Node("other")
    wKeep.SetTarget other

    // (here a value dies at its last use: `keep` and `other` are used below, after the lookups,
    // so they are alive while the weak references are asked)
    let kept = cache.TryGet "kept" |> Option.map (fun n -> n.Name)
    let viaSet = lookup wKeep

    let failed =
        check (kept = Some "kept" && viaSet = "other")
        + (if counting () then
               check (
                   lookup wTemp = "gone"
                   && lookup wCycle = "gone"
                   && cache.TryGet "short-lived" = None
               )
           else
               0)
        + check (keep.Name = "kept" && other.Name = "other")

    printfn "weak: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
