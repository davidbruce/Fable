module Fable.Tests.Zig.TailCallTests

open Fable.Tests.Util
open Fable.Tests.Util.Testing

module Functions =
    let rec factorial1 aux n =
        if n = 0 then aux
        else factorial1 (aux * n) (n - 1)

    let rec factorial2 n =
        match n with
        | 0 | 1 -> 1
        | _ -> n * factorial2(n-1)

    let factorial3 n =
        let rec loop i acc =
            match i with
            | 0 | 1 -> acc
            | _ -> loop (i-1) (acc * i)
        loop n 1

    let rec sum v m s =
        if v >= m
        then s
        else sum (v + 1L) m (s + v)

    let rec iife a =
        2 * (match id a with
            | []  -> 0
            | [x]  -> x
            | h::t -> iife t)

    type Tree<'Key,'T> =
        | Empty
        | Node of 'Key * 'T * Tree<'Key,'T> *  Tree<'Key,'T> * int

    let One(k,v) = Node(k,v,Empty,Empty,1)

    let rec tryFind k m =
        match m with
        | Empty -> None
        | Node(k2,v2,l,r,_) ->
            let c = compare k k2
            if c < 0 then tryFind k l
            elif c = 0 then Some v2
            else tryFind k r

    let rec functionArguments x f =
        let f2 = f >> ((+) 3)
        match x with
        | [] -> failwith "empty list"
        | [x] -> f x
        | h::t -> functionArguments t f2

    let rec iterate f n x =
        match n with
        | 0 -> x
        | _ -> iterate f (n - 1) (f x)

    let recWithFinally () =
        let mutable log = ""
        let rec test n =
          try
            log <- log + string "abcde".[n]
            if n < 4 then test (n+1)
          finally
            log <- log + string "ABCDE".[n]
        test 0
        log

    let recWithUse () =
        let mutable log = ""
        let disp(n) =
          { new System.IDisposable with
              member x.Dispose() = log <- log + string "ABCDE".[n] }
        let rec test n =
          use _disp = disp(n)
          log <- log + string "abcde".[n]
          if n < 4 then test (n+1) else 0
        test 0 |> ignore
        log

open Functions

module Issue3301 =
    let rec simple x a =
        if x <= 0 then a
        else
            simple (x-1) (a+1)

    let rec binding x a =
        if x <= 0 then a
        else
            let bb = binding (x-1)
            bb (a+1)

    let rec tupleDeconstruction x a =
        if x <= 0 then a
        else
            let (bb, _) = (tupleDeconstruction, 1)
            bb (x-1) (a+1)

type MyTailCall() =
    member x.Sum(v, m, s) =
        if v >= m
        then s
        else x.Sum(v + 1L, m, s + v)

let rec parseNum tokens acc = function
  | x::xs when x >= '0' && x <= '9' ->
      parseNum tokens (x::acc) xs
  | xs -> parseTokens ((List.rev acc)::tokens) xs

and parseTokens tokens = function
  | x::xs when x >= '0' && x <= '9' ->
      parseNum tokens [x] xs
  | x::xs -> parseTokens tokens xs
  | [] -> List.rev tokens

type Element =
    | Element of action: (unit->unit) * children: Element list
    member this.Activate() =
        match this with
        | Element(action, children) ->
            action()
            for child in children do child.Activate()

[<Fact>]
let ``test Tailcall works in tail position`` () =
    Issue3301.simple 100000 1 |> equal 100001

[<Fact>]
let ``test Tailcall works with bindings`` () =
    Issue3301.binding 100000 1 |> equal 100001

[<Fact>]
let ``test Tailcall works with tuple deconstruction`` () =
    Issue3301.tupleDeconstruction 100000 1 |> equal 100001

[<Fact>]
let ``test Recursive functions can be tailcall optimized`` () =
    factorial1 1 10 |> equal 3628800

[<Fact>]
let ``test Non-tailcall recursive functions work`` () =
    factorial2 10 |> equal 3628800

[<Fact>]
let ``test Nested functions can be tailcall optimized`` () =
    factorial3 10 |> equal 3628800

[<Fact>]
let ``test Arguments can be consumed after being passed in tailcall optimizations`` () =
    sum 0L 100000L 0L
    |> equal 4999950000L

[<Fact>]
let ``test Class methods can be tailcall optimized`` () =
    let x = MyTailCall()
    x.Sum(0L, 100000L, 0L)
    |> equal 4999950000L

[<Fact>]
let ``test Mutually recursive functions can be partially optimized`` () =
    let s = "a5b6c"
    s.ToCharArray() |> Seq.toList |> parseTokens []
    |> Seq.concat |> Seq.map string |> String.concat ""
    |> equal "56"

[<Fact>]
let ``test IIFEs prevent tailcall optimization`` () =
    iife [5; 4; 3] |> equal 24

[<Fact>]
let ``test Tailcall optimization doesnt cause endless loops`` () =
    One("a", 42)
    |> tryFind "a"
    |> equal (Some 42)
    Tree.Empty
    |> tryFind "a"
    |> equal None

[<Fact>]
let ``test Recursive functions containing finally work`` () =
    recWithFinally () |> equal "abcdeEDCBA"

[<Fact>]
let ``test Recursive functions containing use work`` () =
    recWithUse () |> equal "abcdeEDCBA"

[<Fact>]
let ``test Function arguments can be optimized`` () =
    functionArguments [1;2;3] ((+) 2) |> equal 11

[<Fact>]
let ``test Function arguments can be optimized II`` () =
    iterate ((*) 2) 5 10 |> equal 320

// See https://github.com/fable-compiler/Fable/issues/1368#issuecomment-434142713
[<Fact>]
let ``test State of internally mutated tail called function parameters is preserved properly`` () =
    let rec loop i lst =
        if i <= 0
        then lst
        else loop (i - 1) ((fun () -> i) :: lst)
    loop 3 [] |> List.map (fun f -> f()) |> equal [1;2;3]

[<Fact>]
let ``test State of internally mutated tail called function parameters is preserved properly II`` () =
    let rec loop lst i =
        if i <= 0
        then lst
        else loop ((fun () -> i) :: lst) (i - 1)
    loop [] 3 |> List.map (fun f -> f()) |> equal [1;2;3]

// See https://github.com/fable-compiler/Fable/issues/1368#issuecomment-434142713
[<Fact>]
let ``test Functions returning unit can be tail called`` () =
    let cmpsts = Array.zeroCreate 16384
    let rec loop x =
        if x > 0 then
            let rec loopi i =
                if i <= 254 then
                    if cmpsts.[i >>> 3] &&& (1uy <<< (i &&& 7)) <> 0uy then loopi (i + 1) else
                    let p = i + i + 3
                    let s0 = 2 * i * (i + 3) + 3
                    let lmt = min 131072 <| s0 + (p <<< 3)
                    let rec loops s =
                        if s < lmt then
                            let msk = 1uy <<< (s &&& 7)
                            let rec loopj j =
                                let cmpsts = cmpsts
                                if j < 16384 then
                                    cmpsts.[j] <- cmpsts.[j] ||| msk
                                    loopj (j + p)
                            loopj (s >>> 3); loops (s + p)
                    loops s0; loopi (i + 1)
            loopi 0; loop (x - 1)
    loop 100
    let oddprms = seq {
        for i in 0 .. 131071 do
            if cmpsts.[i >>> 3] &&& (1uy <<< (i &&& 7)) = 0uy
            then yield i + i + 3 }
    seq { yield 2; yield! oddprms }
    |> Seq.length |> equal 23000

[<Fact>]
let ``test Expressiones captured in a closure don't change after tail-call optimizations`` () =
    let mutable accValue = 0
    let el action children = Element(action, children)

    let init () =
        [|1 .. 4|] |> Array.map (fun i -> i, false) |> Map.ofArray

    let update msg (model: Map<int,bool>) =
        accValue <- accValue + msg
        let b = model.[msg]
        Map.add msg (not b) model

    let view model dispatch =
        let rec looper acc x =
            match x with
            |(i1,b1)::(i2,b2)::rest ->
                let newParent =
                    el ignore [
                        el (fun _ ->
                            // Force the x argument to be captured
                            // by the closure
                            match x with
                            |(i1,_)::_ -> i1 |> dispatch
                            | _ -> ()) []
                        el (fun _ -> i2 |> dispatch) []
                    ]
                looper (newParent::acc) rest
            |(i,b)::rest ->
                let newParent =
                    el (fun _ -> i |> dispatch) []
                looper (newParent::acc) rest
            |[] -> acc

        // Use two looper references to prevent the binding
        // beta reduction and force the tail-call optimization
        model |> Map.toList |> looper [] |> ignore
        model |> Map.toList |> looper [] |> el ignore

    let main init view update =
        let mutable model = init()
        let dispatch m msg =
            model <- update msg m
        let el: Element = view model (dispatch model)
        el.Activate()

    main init view update
    accValue |> equal 10

// See https://github.com/fable-compiler/Fable/issues/3877
[<Fact>]
let ``test Passing a function reference in a TCO context does not capture unneeded outer args`` () =
    let applyFn (f: unit -> int) = f()
    let alwaysFortyTwo () = 42

    // `alwaysFortyTwo` doesn't reference `_unused`, so it should not capture it
    // even though `loop` is tail-call optimised with `_unused` in scope.
    let rec loop (_unused: string) acc n =
        if n <= 0 then acc
        else loop _unused (acc + applyFn alwaysFortyTwo) (n - 1)

    loop "ignored" 0 5 |> equal 210

[<Fact>]
let ``test deep mutual tail recursion over non-scalar and heterogeneous signatures`` () =
    let rec stateA (n: int) (tag: string) (acc: int) =
        if n <= 0 then
            tag + ":" + string acc
        else
            let nextTag = "a" + string (n % 7)
            stateB (n - 1) [ n % 5; acc % 13 ] nextTag (acc + tag.Length)

    and stateB (n: int) (xs: int list) (tag: string) (acc: int) =
        if n <= 0 then
            tag + ":" + string (acc + xs.Length)
        else
            stateA (n - 1) ("b" + string xs.Length) (acc + 1)

    // 120,000 mutual frames would overflow native stack without state-machine fusion.
    stateA 120000 ("init" + string 0) 0 |> equal "b2:180003"

let rec private evenPick<'T> (n: int) (a: 'T) (b: 'T) : 'T =
    if n <= 0 then a
    else oddPick<'T> (n - 1) b a

and private oddPick<'T> (n: int) (a: 'T) (b: 'T) : 'T =
    if n <= 0 then b
    else evenPick<'T> (n - 1) b a

[<Fact>]
let ``test generic and raising mutual tail recursion runs in constant stack`` () =
    evenPick 100000 ("first-" + string 1) ("second-" + string 2) |> equal "first-1"
    evenPick 100001 ("first-" + string 1) ("second-" + string 2) |> equal "first-1"
    evenPick 100000 [ 1; 2 ] [ 3; 4 ] |> equal [ 1; 2 ]
    oddPick 100000 [ 1; 2 ] [ 3; 4 ] |> equal [ 3; 4 ]

    let rec checkedA (n: int) (s: string) =
        if n < 0 then failwith ("neg:" + s)
        elif n = 0 then s
        else checkedB (n - 1) s

    and checkedB (n: int) (s: string) =
        if n = 0 then s + "!"
        else checkedA (n - 1) s

    checkedA 100001 ("ok" + string 1) |> equal "ok1!"
    throwsError "neg:boom" (fun () -> checkedA -1 ("boom" + "") |> ignore)

// ---- ported from tests/Js/Main (2026-11-16) ----

[<Fact>]
let ``test Arguments can be consumed after being "passed" in tailcall optimizations`` () =
    sum 0L 100000L 0L
    |> equal 4999950000L

[<Fact>]
let ``test Tailcall optimization doesn't cause endless loops`` () =
    // See #675
    One("a", 42)
    |> tryFind "a"
    |> equal (Some 42)
    Tree.Empty
    |> tryFind "a"
    |> equal None

type private SccPlugChain =
    | SccEnd of string
    | SccLink of string * SccPlugChain

let rec private sccEvenList (n: int) : string list =
    if n <= 0 then []
    else ("e" + string n) :: sccOddList (n - 1)

and private sccOddList (n: int) : string list =
    if n <= 0 then [ "end" ]
    else ("o" + string n) :: sccEvenList (n - 1)

let rec private sccEvenPlug (failAt: int) (n: int) : SccPlugChain =
    if n = failAt then failwith "scc-plug-boom"
    elif n <= 0 then SccEnd "done"
    else SccLink("e" + string n, sccOddPlug failAt (n - 1))

and private sccOddPlug (failAt: int) (n: int) : SccPlugChain =
    if n = failAt then failwith "scc-odd-boom"
    elif n <= 0 then SccEnd "done-odd"
    else SccLink("o" + string n, sccEvenPlug failAt (n - 1))

[<Fact>]
let ``test mutual TRMC state machine runs in constant stack and cleans up on raise`` () =
#if FABLE_COMPILER
    let depth = 100000
    let failAt = 50000
#else
    let depth = 400
    let failAt = 200
#endif
    let xs = sccEvenList depth
    xs.Length |> equal depth
    xs.Head |> equal ("e" + string depth)

    let chain = sccEvenPlug -1 depth
    let rec countChain acc c =
        match c with
        | SccEnd _ -> acc + 1
        | SccLink(_, rest) -> countChain (acc + 1) rest
    countChain 0 chain |> equal (depth + 1)
    throwsError "scc-plug-boom" (fun () -> sccEvenPlug failAt depth |> ignore)

// ---- Step 9: Uniform `$tc` entries for file functions & lambdas ----

#if FABLE_COMPILER
[<Fable.Core.Emit("@import(\"builtin\").zig_backend == .stage2_llvm")>]
let private isLlvmTc () : bool = false
#else
let private isLlvmTc () : bool = false
#endif

type private TcCpsExpr =
    | TcNum of int
    | TcAdd of TcCpsExpr * TcCpsExpr
    | TcTag of string * TcCpsExpr
    | TcFail of string

let rec private tcEvalK (e: TcCpsExpr) (k: int -> int) : int =
    match e with
    | TcNum n -> k n
    | TcFail msg -> failwith msg
    | TcTag(tag, inner) ->
        let bonus = tag.Length % 2
        tcEvalK inner (fun v -> k (v + bonus))
    | TcAdd(l, r) -> tcEvalK l (fun lv -> tcEvalK r (fun rv -> k (lv + rv)))

let rec private tcFoldk
    (f: 'Acc -> 'T -> ('Acc -> 'R) -> 'R)
    (acc: 'Acc)
    (xs: 'T list)
    (k: 'Acc -> 'R)
    : 'R =
    match xs with
    | [] -> k acc
    | x :: rest -> f acc x (fun acc2 -> tcFoldk f acc2 rest k)

let rec private tcFlipA (n: int) (a: 'A list) (b: 'B list) : int =
    if n <= 0 then a.Length + b.Length
    else tcFlipB (n - 1) b a

and private tcFlipB (n: int) (b: 'B list) (a: 'A list) : int =
    if n <= 0 then a.Length + b.Length + 1
    else tcFlipA (n - 1) a b

[<Struct>]
type private TcBigArgs =
    {
        B0: int64; B1: int64; B2: int64; B3: int64
        B4: int64; B5: int64; B6: int64; B7: int64
        B8: int64; B9: int64; B10: int64; B11: int64
        B12: int64; B13: int64; B14: int64; B15: int64
        B16: int64
    }

[<Fact>]
let ``test Step 9 CPS evalK, foldk, unfused generic cycle, and >128B struct fallback`` () =
    let deep = if isLlvmTc () then 200000 else 500
    let raiseAt = if isLlvmTc () then 100000 else 250

    let mutable expr = TcNum 1
    let mutable expected = 1
    let mutable i = 1
    while i <= deep do
        let tag = "n" + string i
        expected <- expected + 1 + (tag.Length % 2)
        expr <- TcAdd(TcTag(tag, TcNum 1), expr)
        i <- i + 1
    tcEvalK expr id |> equal expected

    let mutable badExpr = TcNum 1
    let mutable j = 1
    while j <= deep do
        if j = deep - raiseAt then
            badExpr <- TcAdd(TcFail("cps-eval-boom:" + string j), badExpr)
        else
            badExpr <- TcAdd(TcTag("m" + string j, TcNum 1), badExpr)
        j <- j + 1
    throwsError ("cps-eval-boom:" + string (deep - raiseAt)) (fun () -> tcEvalK badExpr id |> ignore)

    let mutable xs : string list = []
    let mutable expectedLen = 0
    let mutable k = deep
    while k >= 1 do
        let s = "s" + string k
        expectedLen <- expectedLen + s.Length
        xs <- s :: xs
        k <- k - 1

    tcFoldk (fun acc (s: string) cont -> cont (acc + s.Length)) 0 xs id
    |> equal expectedLen

    throwsError
        ("foldk-boom:s" + string (raiseAt + 1))
        (fun () ->
            tcFoldk
                (fun acc (s: string) cont ->
                    if acc = raiseAt then failwith ("foldk-boom:" + s)
                    else cont (acc + 1))
                0
                xs
                id
            |> ignore)

    tcFlipA deep [ "a" + string 1; "b" + string 2 ] [ 10; 20; 30 ] |> equal 5
    tcFlipA (deep + 1) [ "x" + string 1 ] [ 1; 2 ] |> equal 4

    let big : TcBigArgs =
        {
            B0 = 1L; B1 = 2L; B2 = 3L; B3 = 4L
            B4 = 5L; B5 = 6L; B6 = 7L; B7 = 8L
            B8 = 9L; B9 = 10L; B10 = 11L; B11 = 12L
            B12 = 13L; B13 = 14L; B14 = 15L; B15 = 16L
            B16 = 17L
        }
    let callVal (f: string -> TcBigArgs -> int64) (s: string) (b: TcBigArgs) = f s b
    let callUnit (f: string -> TcBigArgs -> unit) (s: string) (b: TcBigArgs) = f s b
    let mutable unitAcc = 0L
    let sumBig b =
        b.B0 + b.B1 + b.B2 + b.B3 + b.B4 + b.B5 + b.B6 + b.B7 + b.B8 + b.B9 + b.B10 + b.B11 + b.B12 + b.B13 + b.B14 + b.B15 + b.B16
    callVal (fun s b -> sumBig b + int64 s.Length) ("v-" + string 1) big |> equal (153L + 3L)
    callUnit (fun s b -> unitAcc <- sumBig b + int64 s.Length) ("u-" + string 22) big
    unitAcc |> equal (153L + 4L)

let rec private tcCrossPing (n: int) (raiseAt: int) (tag: string) : int =
    if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, tag.Length + n))
    elif n <= 0 then tag.Length + n
    else Fable.Tests.MiscTestsHelper.tcCrossPong tcCrossPing (n - 1) raiseAt tag

let private tcCrossTailLeaf (n: int) (tag: string) : int =
    Fable.Tests.MiscTestsHelper.tcCrossLeaf n tag

let rec private tcCrossGenPing (n: int) (xs: string list) : int =
    if n <= 0 then xs.Length
    else Fable.Tests.MiscTestsHelper.tcCrossPongGen tcCrossGenPing (n - 1) xs

type private TcTestSub(label: string) =
    inherit Fable.Tests.MiscTestsHelper.TcCrossBase(label)

    override this.Step(other, n, raiseAt, tag) =
        if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, this.Label.Length + tag.Length))
        elif n <= 0 then this.Label.Length + tag.Length + n
        else other.Step(this, n - 1, raiseAt, tag)

type private TcSubIfaceTestImpl(prefix: string) =
    interface Fable.Tests.MiscTestsHelper.ITcCrossSubPing with
        member _.Bonus = 7

        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, prefix.Length + tag.Length))
            elif n <= 0 then prefix.Length + tag.Length + n
            else other.Ping(this, n - 1, raiseAt, tag)

type private TcBoxRecordPing =
    {
        TagSalt: string
    }

    interface Fable.Tests.MiscTestsHelper.ITcCrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, this.TagSalt.Length + tag.Length))
            elif n <= 0 then this.TagSalt.Length + tag.Length + n
            else other.Ping(this, n - 1, raiseAt, tag)

[<Struct>]
type private TcValueBoxPing =
    {
        Salt: string
    }

    interface Fable.Tests.MiscTestsHelper.ITcCrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, this.Salt.Length + tag.Length))
            elif n <= 0 then this.Salt.Length + tag.Length + n
            else
                let selfCopy: TcValueBoxPing = { Salt = this.Salt }
                other.Ping(selfCopy, n - 1, raiseAt, tag)

type private ITcMutBox =
    abstract Inc: int -> int

[<Struct>]
type private TcMutBoxStruct =
    val mutable Count: int
    new(c) = { Count = c }

    interface ITcMutBox with
        member this.Inc(d) =
            this.Count <- this.Count + d
            this.Count

let private tcTailMut (b: ITcMutBox) (d: int) : int = b.Inc d

let private tcTailIface (p: Fable.Tests.MiscTestsHelper.ITcCrossPing) (other: Fable.Tests.MiscTestsHelper.ITcCrossPing) (n: int) (raiseAt: int) (tag: string) : int =
    p.Ping(other, n, raiseAt, tag)

[<Fact>]
let ``test Step 10 cross-file, virtual class, object expr, and fat-pointer interface $tc ping-pong`` () =
    let deep = if isLlvmTc () then 200000 else 500
    let raiseAt = if isLlvmTc () then 100000 else 250
    let tag = "tag-" + string 10

    tcCrossPing deep -1 tag |> equal tag.Length
    tcCrossTailLeaf 10 tag |> equal (10 + tag.Length)
    tcCrossGenPing deep [ "a" + string 1; "b" + string 2 ] |> equal 2

    let mutable caughtCross = false
    try
        tcCrossPing deep raiseAt tag |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtCross <- true
    caughtCross |> equal true

    let vtA = TcTestSub("vA") :> Fable.Tests.MiscTestsHelper.TcCrossBase
    let vtB = Fable.Tests.MiscTestsHelper.TcCrossHelperSub("vB-") :> Fable.Tests.MiscTestsHelper.TcCrossBase
    let oePrefix = "oe-" + string 42

    let vtObjExpr =
        { new Fable.Tests.MiscTestsHelper.TcCrossBase("oeBase") with
            override this.Step(other, n, rAt, t) =
                if n = rAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(rAt, oePrefix.Length + t.Length))
                elif n <= 0 then oePrefix.Length + t.Length + n
                else other.Step(this, n - 1, rAt, t)
        }

    vtA.Step(vtB, deep, -1, tag) |> equal ((if deep % 2 = 0 then 2 else 3) + tag.Length)
    vtObjExpr.Step(vtB, deep, -1, tag) |> equal ((if deep % 2 = 0 then oePrefix.Length else 3) + tag.Length)

    let mutable caughtVt = false
    try
        vtObjExpr.Step(vtA, deep, raiseAt, tag) |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtVt <- true
    caughtVt |> equal true

    let ifHelpers = Fable.Tests.MiscTestsHelper.TcHelperObjPing("hi-") :> Fable.Tests.MiscTestsHelper.ITcCrossPing
    let ifUpcast = (TcSubIfaceTestImpl("sub") :> Fable.Tests.MiscTestsHelper.ITcCrossSubPing) :> Fable.Tests.MiscTestsHelper.ITcCrossPing
    let capSalt = "cap-" + string 99

    let ifCaps =
        { new Fable.Tests.MiscTestsHelper.ITcCrossPing with
            member this.Ping(other, n, rAt, t) =
                if n = rAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(rAt, capSalt.Length + t.Length))
                elif n <= 0 then capSalt.Length + t.Length + n
                else other.Ping(this, n - 1, rAt, t)
        }

    let ifRecordBox = { TagSalt = "rec-" + string 7 } :> Fable.Tests.MiscTestsHelper.ITcCrossPing
    let ifStructBox = { Salt = "box-" + string 7 } :> Fable.Tests.MiscTestsHelper.ITcCrossPing

    tcTailIface ifHelpers ifUpcast deep -1 tag |> equal (3 + tag.Length)
    tcTailIface ifCaps ifHelpers deep -1 tag |> equal ((if deep % 2 = 0 then capSalt.Length else 3) + tag.Length)
    tcTailIface ifRecordBox ifCaps deep -1 tag |> equal ((if deep % 2 = 0 then 5 else capSalt.Length) + tag.Length)
    tcTailIface ifStructBox ifCaps 50 -1 tag |> equal (5 + tag.Length)

    let mutable caughtIface = false
    try
        tcTailIface ifUpcast ifCaps deep raiseAt tag |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtIface <- true
    caughtIface |> equal true

    let mutable caughtRecBox = false
    try
        tcTailIface ifRecordBox ifCaps deep raiseAt tag |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtRecBox <- true
    caughtRecBox |> equal true

    let mutable caughtStructBox = false
    try
        tcTailIface ifStructBox ifCaps 50 25 tag |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtStructBox <- true
    caughtStructBox |> equal true

    let mutBox = TcMutBoxStruct(10) :> ITcMutBox
    tcTailMut mutBox 5 |> equal 15
    tcTailMut mutBox 7 |> equal 22

let private tcGoTrmc (next: int -> int -> string list) (n: int) (raiseAt: int) : string list =
    if n = raiseAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(raiseAt, n))
    elif n <= 0 then []
    else ("item-" + string n) :: next (n - 1) raiseAt

let rec private tcGoTie (n: int) (raiseAt: int) : string list =
    if n % 2 = 0 then tcGoTrmc tcGoTie n raiseAt
    else Fable.Tests.MiscTestsHelper.tcTrmcCrossCons tcGoTie n raiseAt

type private ITcTrmcList =
    abstract Build: ITcTrmcList * int * int -> string list

type private TcValWrap =
    | TcWrapItems of label: string * items: string list
    | TcWrapEmpty

let private tcBuildWrap (next: int -> int -> string list) (n: int) (raiseAt: int) : TcValWrap =
    if n <= 0 then TcWrapEmpty
    else TcWrapItems("hdr-" + string n, next n raiseAt)

let private tcWrapViaMaker
    (maker: (int -> int -> string list) -> int -> int -> TcValWrap)
    (next: int -> int -> string list)
    (n: int)
    (raiseAt: int)
    : TcValWrap
    =
    maker next n raiseAt

[<Fact>]
let ``test Step 11 TRMC into unknown callees over KHeapUnion and KValueUnion`` () =
    let deep = if isLlvmTc () then 200000 else 500
    let raiseAt = if isLlvmTc () then 100000 else 250

    let countAndEnds (xs: string list) =
        let mutable len = 0
        let mutable first = ""
        let mutable last = ""
        let mutable cur = xs
        while not (List.isEmpty cur) do
            if len = 0 then first <- cur.Head
            last <- cur.Head
            len <- len + 1
            cur <- cur.Tail
        len, first, last

    let len1, first1, last1 = countAndEnds (tcGoTie deep -1)
    len1 |> equal deep
    first1 |> equal ("item-" + string deep)
    last1 |> equal "h-1"

    let mutable caughtHeap = false
    try
        tcGoTie deep raiseAt |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtHeap <- true
    caughtHeap |> equal true

    let ifPrefix = "if-" + string 3
    let ifBuilder =
        { new ITcTrmcList with
            member this.Build(other, n, rAt) =
                if n = rAt then raise (Fable.Tests.MiscTestsHelper.TcCrossBoom(rAt, n))
                elif n <= 0 then []
                else (ifPrefix + "-" + string n) :: other.Build(this, n - 1, rAt)
        }
    let tailBuild (a: ITcTrmcList) (b: ITcTrmcList) (n: int) (rAt: int) = a.Build(b, n, rAt)
    let len2, first2, last2 = countAndEnds (tailBuild ifBuilder ifBuilder deep -1)
    len2 |> equal deep
    first2 |> equal (ifPrefix + "-" + string deep)
    last2 |> equal (ifPrefix + "-1")

    let mutable caughtIface = false
    try
        tailBuild ifBuilder ifBuilder deep raiseAt |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtIface <- true
    caughtIface |> equal true

    match tcBuildWrap tcGoTie deep -1 with
    | TcWrapItems(lbl, items) ->
        let n, f, l = countAndEnds items
        lbl |> equal ("hdr-" + string deep)
        n |> equal deep
        f |> equal ("item-" + string deep)
        l |> equal "h-1"
    | TcWrapEmpty -> equal true false

    match tcWrapViaMaker tcBuildWrap tcGoTie deep -1 with
    | TcWrapItems(lbl, items) ->
        let n, f, l = countAndEnds items
        lbl |> equal ("hdr-" + string deep)
        n |> equal deep
        f |> equal ("item-" + string deep)
        l |> equal "h-1"
    | TcWrapEmpty -> equal true false

    match tcWrapViaMaker tcBuildWrap tcGoTie 0 -1 with
    | TcWrapEmpty -> ()
    | TcWrapItems _ -> equal true false

    let mutable caughtWrap = false
    try
        tcWrapViaMaker tcBuildWrap tcGoTie deep raiseAt |> ignore
    with :? Fable.Tests.MiscTestsHelper.TcCrossBoom ->
        caughtWrap <- true
    caughtWrap |> equal true

type TcNonNullFuncStream =
    | TcNFStep of System.Func<int, int, int, int, int> * TcNonNullFuncStream
    | TcNFEnd

let private tcPadTouch (n: int) =
    if n = 1 then 1 elif n = 2 then 2 elif n = 3 then 3 elif n = 4 then 4
    elif n = 5 then 5 elif n = 6 then 6 elif n = 7 then 7 elif n = 8 then 8
    elif n = 9 then 9 elif n = 10 then 10 elif n = 11 then 11 elif n = 12 then 12
    elif n = 13 then 13 elif n = 14 then 14 elif n = 15 then 15 elif n = 16 then 16
    elif n = 17 then 17 elif n = 18 then 18 elif n = 19 then 19 elif n = 20 then 20
    elif n = 21 then 21 elif n = 22 then 22 elif n = 23 then 23 elif n = 24 then 24
    elif n = 25 then 25 elif n = 26 then 26 elif n = 27 then 27 elif n = 28 then 28
    elif n = 29 then 29 elif n = 30 then 30 elif n = 31 then 31 elif n = 32 then 32
    else 0

let rec private tcEvenSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let w =
        if n = -9 then tcPadTouch 1 elif n = -8 then tcPadTouch 2 elif n = -7 then tcPadTouch 3
        elif n = -6 then tcPadTouch 4 elif n = -5 then tcPadTouch 5 elif n = -4 then tcPadTouch 6
        elif n = -3 then tcPadTouch 7 elif n = -2 then tcPadTouch 8 elif n = -11 then tcPadTouch 9
        elif n = -12 then tcPadTouch 10 elif n = -13 then tcPadTouch 11 elif n = -14 then tcPadTouch 12
        elif n = -15 then tcPadTouch 13 elif n = -16 then tcPadTouch 14 elif n = -17 then tcPadTouch 15
        elif n = -18 then tcPadTouch 16 elif n = -19 then tcPadTouch 17 elif n = -20 then tcPadTouch 18
        else 0

    if n <= 0 then f (1 + w) else tcOddSwap<'B, 'A> f (n - 1) b a

and private tcOddSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let w =
        if n = -9 then tcPadTouch 1 elif n = -8 then tcPadTouch 2 elif n = -7 then tcPadTouch 3
        elif n = -6 then tcPadTouch 4 elif n = -5 then tcPadTouch 5 elif n = -4 then tcPadTouch 6
        elif n = -3 then tcPadTouch 7 elif n = -2 then tcPadTouch 8 elif n = -11 then tcPadTouch 9
        elif n = -12 then tcPadTouch 10 elif n = -13 then tcPadTouch 11 elif n = -14 then tcPadTouch 12
        elif n = -15 then tcPadTouch 13 elif n = -16 then tcPadTouch 14 elif n = -17 then tcPadTouch 15
        elif n = -18 then tcPadTouch 16 elif n = -19 then tcPadTouch 17 elif n = -20 then tcPadTouch 18
        else 0

    if n <= 0 then f (2 + w) else tcEvenSwap<'B, 'A> f (n - 1) b a

let rec private tcSelfSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let w =
        if n = -9 then tcPadTouch 1 elif n = -8 then tcPadTouch 2 elif n = -7 then tcPadTouch 3
        elif n = -6 then tcPadTouch 4 elif n = -5 then tcPadTouch 5 elif n = -4 then tcPadTouch 6
        else 0

    if n <= 0 then f (3 + w) else tcSelfSwap<'B, 'A> f (n - 1) b a

let rec private tcEvenHofH2 (f: int -> int) (n: int) (acc: int) : int =
    let w =
        if n = -9 then tcPadTouch 1 elif n = -8 then tcPadTouch 2 elif n = -7 then tcPadTouch 3
        elif n = -6 then tcPadTouch 4 elif n = -5 then tcPadTouch 5 elif n = -4 then tcPadTouch 6
        elif n = -3 then tcPadTouch 7 elif n = -2 then tcPadTouch 8 elif n = -11 then tcPadTouch 9
        elif n = -12 then tcPadTouch 10 elif n = -13 then tcPadTouch 11 elif n = -14 then tcPadTouch 12
        elif n = -15 then tcPadTouch 13 elif n = -16 then tcPadTouch 14 elif n = -17 then tcPadTouch 15
        elif n = -18 then tcPadTouch 16 elif n = -19 then tcPadTouch 17 elif n = -20 then tcPadTouch 18
        else 0

    if n <= 0 then acc + w else tcOddHofH2 f (n - 1) (acc + f 1)

and private tcOddHofH2 (f: int -> int) (n: int) (acc: int) : int =
    let w =
        if n = -9 then tcPadTouch 1 elif n = -8 then tcPadTouch 2 elif n = -7 then tcPadTouch 3
        elif n = -6 then tcPadTouch 4 elif n = -5 then tcPadTouch 5 elif n = -4 then tcPadTouch 6
        elif n = -3 then tcPadTouch 7 elif n = -2 then tcPadTouch 8 elif n = -11 then tcPadTouch 9
        elif n = -12 then tcPadTouch 10 elif n = -13 then tcPadTouch 11 elif n = -14 then tcPadTouch 12
        elif n = -15 then tcPadTouch 13 elif n = -16 then tcPadTouch 14 elif n = -17 then tcPadTouch 15
        elif n = -18 then tcPadTouch 16 elif n = -19 then tcPadTouch 17 elif n = -20 then tcPadTouch 18
        else 0

    if n <= 0 then acc + w else tcEvenHofH2 f (n - 1) (acc + f 2)

let rec private tcRaiseGenH1<'T> (f: int -> 'T) (n: int) : 'T =
    if n <= 0 then invalidOp "boom_h1" else f n

let rec private tcBuildNonNullVia (next: int -> TcNonNullFuncStream) (n: int) : TcNonNullFuncStream =
    if n < 0 then
        TcNFEnd
    else
        let fn4 = System.Func<int, int, int, int, int>(fun a b c d -> a + b + c + d)
        TcNFStep(fn4, tcRaiseGenH1 next (n - 1))

let rec private tcDriveNonNull (n: int) : TcNonNullFuncStream = tcBuildNonNullVia tcDriveNonNull n

let private tcApplyThenTail (f: int -> int) (k: int -> int) (x: int) : int = k (f x)

let rec private tcChainTailStep (k: int -> int) (n: int) (acc: int) : int =
    if n <= 0 then acc else tcApplyThenTail (fun v -> v + 1) (fun v -> tcChainTailStep k (n - 1) (k v)) acc

let private tcForwardKToAssumed (pred: string -> bool) (s: string) : int =
    let b1 = Fable.Tests.MiscTestsHelper.tcFindBorrowedOrFallback pred s 3
    let b2 = Fable.Tests.MiscTestsHelper.tcFindBorrowedOrFallbackGen pred s s 4
    b1.Length + b2.Length

[<Fact>]
let ``test Bug C1 forwarding KParam into cross-file assumed-borrowed HOF`` () =
    let pfx = "pre-" + string 9
    let ownedStr = pfx + "-owned"
    let rDirect = Fable.Tests.MiscTestsHelper.tcFindBorrowedOrFallback (fun x -> x.StartsWith pfx) ownedStr 5
    rDirect.Length |> equal ownedStr.Length
    tcForwardKToAssumed (fun x -> x.StartsWith pfx) ownedStr |> equal (ownedStr.Length * 2)

[<Fact>]
let ``test Bug C2 dropping 150k linear multi-capture CPS closure chain in O(1) stack`` () =
    let bonus = 7
    let post = fun (x: int) -> x + bonus
    let mutable k: int -> int = fun x -> x + 1

    for _ = 1 to 150000 do
        let prev = k
        k <- fun x -> if x >= 0 then prev (x + 1) else post x

    k (-1) |> equal 6

[<Fact>]
let ``test Bug C3 type-swapping and polymorphic recursive callK HOFs plus H2 fused SCC`` () =
    let deep = if isLlvmTc () then 200000 else 500
    let cap = 10
    let swapRes = tcEvenSwap<int, string> (fun x -> x + cap) deep 1 "a"
    swapRes |> equal (if deep % 2 = 0 then 1 + cap else 2 + cap)

    tcSelfSwap<int, string> (fun x -> x + cap) deep 1 "a" |> equal (3 + cap)
    tcChainTailStep (fun v -> v + 1) deep 0 |> equal (deep * 2)

    let h2Depth =
#if FABLE_COMPILER
        200000
#else
        500
#endif
    let h2Res = tcEvenHofH2 (fun x -> x + cap) h2Depth 0
    h2Res |> equal ((h2Depth / 2) * (1 + cap + 2 + cap))

[<Fact>]
let ``test Bug H1 generic tc raise into fieldless non-hasNull union`` () =
    let mutable caught = ""

    try
        tcDriveNonNull 12 |> ignore
    with :? System.InvalidOperationException as ex ->
        caught <- ex.Message

    caught |> equal "boom_h1"

[<Fact>]
let ``test Tier 2 pub VGlobal qualification and List Array maxBy minBy groupBy countBy`` () =
    Fable.Tests.MiscTestsHelper.tcTier2GlobalMut <- 10
    let factor = 2
    let r1 = Fable.Tests.MiscTestsHelper.tcApplyWithGlobals (fun v -> v * factor) 5
    let r2 = Fable.Tests.MiscTestsHelper.tcApplyWithGlobals (fun v -> v * factor) 5
    r1 |> equal (((5 + 42 + 5) * 2) + 11)
    r2 |> equal (((5 + 42 + 5) * 2) + 12)

    let scale = 3
    let mutable hits = 0
    [ 7 ] |> List.maxBy (fun x -> hits <- hits + 1; x * scale) |> equal 7
    [| 9 |] |> Array.minBy (fun x -> hits <- hits + 1; x * scale) |> equal 9
    hits |> equal 2

    [ 1; 4; 2 ] |> List.maxBy (fun x -> x * scale) |> equal 4
    [ 3; 1; 4 ] |> List.minBy (fun x -> x * scale) |> equal 1
    [| 2; 8; 5 |] |> Array.maxBy (fun x -> x * scale) |> equal 8
    [| 6; 1; 5 |] |> Array.minBy (fun x -> x * scale) |> equal 1
    ([ 1; 2; 3; 4 ] |> List.groupBy (fun x -> x % scale)).Length |> equal 3
    ([ 1; 2; 3; 4 ] |> List.countBy (fun x -> x % scale)).Length |> equal 3



