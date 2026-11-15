module Fable.Tests.Zig.FnTests

open Fable.Tests.Util
open Fable.Tests.Util.Testing

let add(a, b, cont) =
    cont(a + b)

let square(x, cont) =
    cont(x * x)

let sqrt(x, cont) =
    cont(sqrt(x))

let pythagoras(a, b, cont) =
    square(a, (fun aa ->
        square(b, (fun bb ->
            add(aa, bb, (fun aabb ->
                sqrt(aabb, (fun result ->
                    cont(result)
                ))
            ))
        ))
    ))

[<Fact>]
let ``test pythagoras works`` () =
    let result = pythagoras(10.0, 2.1, id)
    result
    |> equal 10.218121158021175

[<Fact>]
let ``test nonlocal works`` () =
    let mutable value = 0

    let fn () =
        value <- 42

    fn ()

    value |> equal 42

[<Fact>]
let ``test partially apply 1-3`` () =
    let add a b c = a + b + c

    let part = add 1
    part 2 3 |> equal 6


[<Fact>]
let ``test partially apply 2-3`` () =
    let add a b c = a + b + c

    let part = add 1 2
    part 3 |> equal 6

[<Fact>]
let ``test partially apply 1-4`` () =
    let add a b c d = a + b + c + d

    let part = add 1 2 3
    part 4 |> equal 10

[<Fact>]
let ``test partially apply 2-4`` () =
    let add a b c d = a + b + c + d

    let part = add 1 2
    part 3 4 |> equal 10

[<Fact>]
let ``test partially apply 3-4`` () =
    let add a b c d = a + b + c + d

    let part = add 1
    part 2 3 4 |> equal 10

[<Fact>]
let ``test curried 2-arg function values and partial application`` () =
    let sep = "<" + string 9 + ">"
    let known = fun (a: string) (b: string) -> a + sep + b
    known ("x" + string 1) ("y" + string 2) |> equal "x1<9>y2"

    let fns =
        [|
            (fun (a: string) (b: string) -> a + sep + b)
            (fun (a: string) (b: string) -> b + ":" + a)
        |]

    fns[0] ("a" + string 1) ("b" + string 2) |> equal "a1<9>b2"
    fns[1] ("a" + string 1) ("b" + string 2) |> equal "b2:a1"

    let part = fns[0] ("head" + string 1)
    part ("t" + string 1) |> equal "head1<9>t1"
    part ("t" + string 2) |> equal "head1<9>t2"

[<Fact>]
let ``test curried 2-arg and 3-arg mid-call exceptions do not leak arguments`` () =
    let mkF2 (failStage1: bool) : string -> string -> string =
        fun (a: string) ->
            if failStage1 then
                failwith ("stage1:" + a)
            else
                fun (b: string) ->
                    if b = "boom2" then
                        failwith ("stage2:" + a)
                    else
                        a + ":" + b

    let call2 (flag: bool) =
        let f = if flag then mkF2 true else mkF2 false
        f ("arg" + string 1) ("arg" + string 2)

    throwsError "stage1:arg1" (fun () -> call2 true |> ignore)
    call2 false |> equal "arg1:arg2"

    let f2Dyn = if System.DateTime.UtcNow.Ticks >= 0L then mkF2 false else mkF2 true
    throwsError "stage2:arg1" (fun () -> f2Dyn ("arg" + string 1) ("boom" + string 2) |> ignore)

    let mkF3 (failStep: int) : string -> string -> string -> string =
        fun (a: string) ->
            if failStep = 1 then
                failwith ("stage1-3:" + a)
            else
                fun (b: string) ->
                    if failStep = 2 then
                        failwith ("stage2-3:" + a + ":" + b)
                    else
                        fun (c: string) -> a + ":" + b + ":" + c

    let call3 step =
        let f =
            match step with
            | 1 -> mkF3 1
            | 2 -> mkF3 2
            | _ -> mkF3 0

        f ("x" + string 1) ("y" + string 2) ("z" + string 3)

    throwsError "stage1-3:x1" (fun () -> call3 1 |> ignore)
    throwsError "stage2-3:x1:y2" (fun () -> call3 2 |> ignore)
    call3 0 |> equal "x1:y2:z3"

let rec private myMap f xs =
    match xs with
    | [] -> []
    | x :: rest -> f x :: myMap f rest

let rec private myFold f acc xs =
    match xs with
    | [] -> acc
    | x :: rest -> myFold f (f acc x) rest

let private applyWithPrefix prefix f xs =
    myMap (fun x -> f (prefix + ":" + x)) xs

[<Fact>]
let ``test user-defined generic and recursive HOFs specialize cleanly`` () =
    let tag = "t" + string 4
    let input = [ "a" + string 1; "b" + string 2; "c" + string 3 ]
    myMap (fun s -> tag + "-" + s) input |> equal [ "t4-a1"; "t4-b2"; "t4-c3" ]
    myFold (fun acc s -> acc + "/" + tag + ":" + s) "root" input |> equal "root/t4:a1/t4:b2/t4:c3"
    applyWithPrefix tag (fun s -> s + "!") input |> equal [ "t4:a1!"; "t4:b2!"; "t4:c3!" ]

    throwsError "myMap-boom" (fun () ->
        myMap (fun s -> if s = "b2" then failwith "myMap-boom" else tag + "-" + s) input |> ignore
    )
