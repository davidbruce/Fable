module Program

// The n-body simulation of the Computer Language Benchmarks Game: floats in arrays.

let solarMass = 4.0 * System.Math.PI * System.Math.PI
let daysPerYear = 365.24

let advance
    (x: float[])
    (y: float[])
    (z: float[])
    (vx: float[])
    (vy: float[])
    (vz: float[])
    (mass: float[])
    (dt: float)
    =
    let n = x.Length

    for i in 0 .. n - 1 do
        for j in i + 1 .. n - 1 do
            let dx = x.[i] - x.[j]
            let dy = y.[i] - y.[j]
            let dz = z.[i] - z.[j]
            let d2 = dx * dx + dy * dy + dz * dz
            let mag = dt / (d2 * sqrt d2)
            vx.[i] <- vx.[i] - dx * mass.[j] * mag
            vy.[i] <- vy.[i] - dy * mass.[j] * mag
            vz.[i] <- vz.[i] - dz * mass.[j] * mag
            vx.[j] <- vx.[j] + dx * mass.[i] * mag
            vy.[j] <- vy.[j] + dy * mass.[i] * mag
            vz.[j] <- vz.[j] + dz * mass.[i] * mag

    for i in 0 .. n - 1 do
        x.[i] <- x.[i] + dt * vx.[i]
        y.[i] <- y.[i] + dt * vy.[i]
        z.[i] <- z.[i] + dt * vz.[i]

let energy (x: float[]) (y: float[]) (z: float[]) (vx: float[]) (vy: float[]) (vz: float[]) (mass: float[]) =
    let mutable e = 0.0
    let n = x.Length

    for i in 0 .. n - 1 do
        e <- e + 0.5 * mass.[i] * (vx.[i] * vx.[i] + vy.[i] * vy.[i] + vz.[i] * vz.[i])

        for j in i + 1 .. n - 1 do
            let dx = x.[i] - x.[j]
            let dy = y.[i] - y.[j]
            let dz = z.[i] - z.[j]
            e <- e - mass.[i] * mass.[j] / sqrt (dx * dx + dy * dy + dz * dz)

    e

[<EntryPoint>]
let main _ =
    let x =
        [|
            0.0
            4.84143144246472090e+00
            8.34336671824457987e+00
            1.28943695621391310e+01
            1.53796971148509165e+01
        |]

    let y =
        [|
            0.0
            -1.16032004402742839e+00
            4.12479856412430479e+00
            -1.51111514016986312e+01
            -2.59193146099879641e+01
        |]

    let z =
        [|
            0.0
            -1.03622044471123109e-01
            -4.03523417114321381e-01
            -2.23307578892655734e-01
            1.79258772950371181e-01
        |]

    let vx =
        [|
            0.0
            1.66007664274403694e-03 * daysPerYear
            -2.76742510726862411e-03 * daysPerYear
            2.96460137564761618e-03 * daysPerYear
            2.68067772490389322e-03 * daysPerYear
        |]

    let vy =
        [|
            0.0
            7.69901118419740425e-03 * daysPerYear
            4.99852801234917238e-03 * daysPerYear
            2.37847173959480950e-03 * daysPerYear
            1.62824170038242295e-03 * daysPerYear
        |]

    let vz =
        [|
            0.0
            -6.90460016972063023e-05 * daysPerYear
            2.30417297573763929e-05 * daysPerYear
            -2.96589568540237556e-05 * daysPerYear
            -9.51592254519715870e-05 * daysPerYear
        |]

    let mass =
        [|
            solarMass
            9.54791938424326609e-04 * solarMass
            2.85885980666130812e-04 * solarMass
            4.36624404335156298e-05 * solarMass
            5.15138902046611451e-05 * solarMass
        |]

    let mutable px = 0.0
    let mutable py = 0.0
    let mutable pz = 0.0

    for i in 0..4 do
        px <- px + vx.[i] * mass.[i]
        py <- py + vy.[i] * mass.[i]
        pz <- pz + vz.[i] * mass.[i]

    vx.[0] <- -px / solarMass
    vy.[0] <- -py / solarMass
    vz.[0] <- -pz / solarMass
    printfn "%.9f" (energy x y z vx vy vz mass)

    for _ in 1..5000000 do
        advance x y z vx vy vz mass 0.01

    printfn "%.9f" (energy x y z vx vy vz mass)
    0
