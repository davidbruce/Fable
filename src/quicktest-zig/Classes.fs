module Classes

// Classes, interfaces, object expressions and `use`. A class is a counted cell of its fields;
// an interface value holds a function value for each member. `run` returns the number of
// failed checks.

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

type IShape =
    abstract Area: unit -> float
    abstract Name: string
    abstract Scale: float * float -> float

type Counter(start: int) =
    let mutable n = start
    let label = "c" + string start

    member _.Next() =
        n <- n + 1
        n

    member _.Current = n
    member _.Label = label
    member this.Twice() = this.Next() + this.Next()

    interface IShape with
        member _.Area() = float n
        member _.Name = label
        member _.Scale(a, b) = a * b * float n

type Stack<'T>() =
    let mutable items: 'T list = []
    member _.Push(x: 'T) = items <- x :: items

    member _.Pop() : 'T option =
        match items with
        | x :: rest ->
            items <- rest
            Some x
        | [] -> None

    member _.Count = List.length items

type Account(owner: string, opening: int) =
    let mutable balance = opening
    let history = ResizeArray<int>()
    member _.Owner = owner
    member _.Balance = balance

    member _.Deposit(amount: int) =
        if amount <= 0 then
            invalidArg "amount" "must be positive"

        balance <- balance + amount
        history.Add amount

    member _.History = List.ofSeq history

type Res(name: string, log: ResizeArray<string>) =
    member _.Name = name

    interface System.IDisposable with
        member _.Dispose() = log.Add("closed " + name)

type Person(name: string) =
    let mutable friend: Person option = None
    member _.Name = name

    member _.Friend
        with get () = friend
        and set (v: Person option) = friend <- v

/// `as this`: the object reached through its own self reference
type SelfAware(v: int) as this =
    let mutable n = v
    let next () = this.Value + 1
    member _.Value = n
    member _.Next() = next ()
    member _.Bump() = n <- next ()

let selfAware () : int =
    let s = SelfAware(3)
    s.Bump()
    s.Next()

let total (s: IShape) : float =
    s.Area() + s.Scale(2.0, 3.0) + float s.Name.Length

let run () : int =
    let before = liveCells ()
    let c = Counter(5)
    let a = c.Next() + c.Current
    let b = c.Twice()
    let k = 7.0
    let mutable calls = 0

    let o =
        { new IShape with
            member _.Area() =
                calls <- calls + 1
                k

            member _.Name = "obj"
            member _.Scale(x, y) = x + y + k
        }

    let shapes = [ c :> IShape; o ]
    let sum = List.sumBy total shapes
    let st = Stack<string>()
    st.Push("a")
    st.Push("b" + "c")
    let popped = st.Pop()
    let acct = Account("ann", 10)
    acct.Deposit 5
    acct.Deposit 7

    let refused =
        try
            acct.Deposit -1
            "no"
        with :? System.ArgumentException as e ->
            e.Message

    let log = ResizeArray<string>()

    let used () =
        use r = new Res("a", log)
        use s = new Res("b", log)
        r.Name.Length + s.Name.Length

    let usedN = used ()
    let greeter = Helpers.Greeter "hello" :> Helpers.IGreeter
    let greeting = greeter.Greet "bob" + "|" + greeter.Greet "eve"

    // (two objects that refer to each other: the collector frees them)
    let pairUp () =
        let p = Person("p")
        let q = Person("q")
        p.Friend <- Some q
        q.Friend <- Some p
        (p.Friend |> Option.map (fun f -> f.Name) |> Option.defaultValue "") + q.Name

    let pair = pairUp ()
    Collector.collect () |> ignore

    let failed =
        check (a = 12 && b = 15 && c.Current = 8 && c.Label = "c5")
        + check (total c = 8.0 + 48.0 + 2.0 && sum = 58.0 + 7.0 + 12.0 + 3.0 && calls = 1)
        + same "Some \"bc\"|1" (sprintf "%A" popped + "|" + string st.Count)
        + same "ann|22|[5; 7]" (acct.Owner + "|" + string acct.Balance + "|" + sprintf "%A" acct.History)
        + same "must be positive (Parameter 'amount')" refused
        + same "2|seq [\"closed b\"; \"closed a\"]" (string usedN + "|" + sprintf "%A" log)
        + same "hello, bob|hello, eve|2" (greeting + "|" + string greeter.Count)
        + same "qq" pair
        + check (selfAware () = 5)

    printfn "classes: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
