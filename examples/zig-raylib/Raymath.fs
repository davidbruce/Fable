module RaylibExamples.Raymath

open System
open RaylibExamples.Raylib

let private deg2Rad = float32 (Math.PI / 180.0)

let vec2 x y : Vector2 =
    {
        x = x
        y = y
    }

let vec3 x y z : Vector3 =
    {
        x = x
        y = y
        z = z
    }

let vec4 x y z w : Vector4 =
    {
        x = x
        y = y
        z = z
        w = w
    }

let vector2Add (v1: Vector2) (v2: Vector2) : Vector2 =
    {
        x = v1.x + v2.x
        y = v1.y + v2.y
    }

let vector2Length (v: Vector2) : float32 = sqrt (v.x * v.x + v.y * v.y)

let vector2Distance (v1: Vector2) (v2: Vector2) : float32 =
    let dx = v1.x - v2.x
    let dy = v1.y - v2.y
    sqrt (dx * dx + dy * dy)

let vector2Lerp (v1: Vector2) (v2: Vector2) (amount: float32) : Vector2 =
    {
        x = v1.x + amount * (v2.x - v1.x)
        y = v1.y + amount * (v2.y - v1.y)
    }

let vector3Add (v1: Vector3) (v2: Vector3) : Vector3 =
    {
        x = v1.x + v2.x
        y = v1.y + v2.y
        z = v1.z + v2.z
    }

let vector3Subtract (v1: Vector3) (v2: Vector3) : Vector3 =
    {
        x = v1.x - v2.x
        y = v1.y - v2.y
        z = v1.z - v2.z
    }

let vector3Scale (v: Vector3) (scalar: float32) : Vector3 =
    {
        x = v.x * scalar
        y = v.y * scalar
        z = v.z * scalar
    }

let vector3Cross (v1: Vector3) (v2: Vector3) : Vector3 =
    {
        x = v1.y * v2.z - v1.z * v2.y
        y = v1.z * v2.x - v1.x * v2.z
        z = v1.x * v2.y - v1.y * v2.x
    }

let vector3Dot (v1: Vector3) (v2: Vector3) : float32 = v1.x * v2.x + v1.y * v2.y + v1.z * v2.z

let vector3Length (v: Vector3) : float32 =
    sqrt (v.x * v.x + v.y * v.y + v.z * v.z)

let vector3Normalize (v: Vector3) : Vector3 =
    let len = vector3Length v

    if len > 0.0f then
        let ilen = 1.0f / len

        {
            x = v.x * ilen
            y = v.y * ilen
            z = v.z * ilen
        }
    else
        v

let matrixIdentity () : Matrix =
    {
        m0 = 1.0f
        m4 = 0.0f
        m8 = 0.0f
        m12 = 0.0f
        m1 = 0.0f
        m5 = 1.0f
        m9 = 0.0f
        m13 = 0.0f
        m2 = 0.0f
        m6 = 0.0f
        m10 = 1.0f
        m14 = 0.0f
        m3 = 0.0f
        m7 = 0.0f
        m11 = 0.0f
        m15 = 1.0f
    }

let matrixMultiply (left: Matrix) (right: Matrix) : Matrix =
    {
        m0 =
            left.m0 * right.m0
            + left.m1 * right.m4
            + left.m2 * right.m8
            + left.m3 * right.m12
        m1 =
            left.m0 * right.m1
            + left.m1 * right.m5
            + left.m2 * right.m9
            + left.m3 * right.m13
        m2 =
            left.m0 * right.m2
            + left.m1 * right.m6
            + left.m2 * right.m10
            + left.m3 * right.m14
        m3 =
            left.m0 * right.m3
            + left.m1 * right.m7
            + left.m2 * right.m11
            + left.m3 * right.m15
        m4 =
            left.m4 * right.m0
            + left.m5 * right.m4
            + left.m6 * right.m8
            + left.m7 * right.m12
        m5 =
            left.m4 * right.m1
            + left.m5 * right.m5
            + left.m6 * right.m9
            + left.m7 * right.m13
        m6 =
            left.m4 * right.m2
            + left.m5 * right.m6
            + left.m6 * right.m10
            + left.m7 * right.m14
        m7 =
            left.m4 * right.m3
            + left.m5 * right.m7
            + left.m6 * right.m11
            + left.m7 * right.m15
        m8 =
            left.m8 * right.m0
            + left.m9 * right.m4
            + left.m10 * right.m8
            + left.m11 * right.m12
        m9 =
            left.m8 * right.m1
            + left.m9 * right.m5
            + left.m10 * right.m9
            + left.m11 * right.m13
        m10 =
            left.m8 * right.m2
            + left.m9 * right.m6
            + left.m10 * right.m10
            + left.m11 * right.m14
        m11 =
            left.m8 * right.m3
            + left.m9 * right.m7
            + left.m10 * right.m11
            + left.m11 * right.m15
        m12 =
            left.m12 * right.m0
            + left.m13 * right.m4
            + left.m14 * right.m8
            + left.m15 * right.m12
        m13 =
            left.m12 * right.m1
            + left.m13 * right.m5
            + left.m14 * right.m9
            + left.m15 * right.m13
        m14 =
            left.m12 * right.m2
            + left.m13 * right.m6
            + left.m14 * right.m10
            + left.m15 * right.m14
        m15 =
            left.m12 * right.m3
            + left.m13 * right.m7
            + left.m14 * right.m11
            + left.m15 * right.m15
    }

let matrixTranslate (x: float32) (y: float32) (z: float32) : Matrix =
    let mutable r = matrixIdentity ()
    r.m12 <- x
    r.m13 <- y
    r.m14 <- z
    r

let matrixRotateY (angleRad: float32) : Matrix =
    let c = cos angleRad
    let s = sin angleRad
    let mutable r = matrixIdentity ()
    r.m0 <- c
    r.m2 <- -s
    r.m8 <- s
    r.m10 <- c
    r

let matrixPerspective (fovYRad: float32) (aspect: float32) (nearPlane: float32) (farPlane: float32) : Matrix =
    let top = nearPlane * tan (fovYRad * 0.5f)
    let bottom = -top
    let right = top * aspect
    let left = -right
    let rl = right - left
    let tb = top - bottom
    let fn = farPlane - nearPlane

    {
        m0 = (nearPlane * 2.0f) / rl
        m4 = 0.0f
        m8 = (right + left) / rl
        m12 = 0.0f
        m1 = 0.0f
        m5 = (nearPlane * 2.0f) / tb
        m9 = (top + bottom) / tb
        m13 = 0.0f
        m2 = 0.0f
        m6 = 0.0f
        m10 = -(farPlane + nearPlane) / fn
        m14 = -(farPlane * nearPlane * 2.0f) / fn
        m3 = 0.0f
        m7 = 0.0f
        m11 = -1.0f
        m15 = 0.0f
    }

let matrixLookAt (eye: Vector3) (target: Vector3) (up: Vector3) : Matrix =
    let vz = vector3Normalize (vector3Subtract eye target)
    let vx = vector3Normalize (vector3Cross up vz)
    let vy = vector3Cross vz vx

    {
        m0 = vx.x
        m4 = vx.y
        m8 = vx.z
        m12 = -(vector3Dot vx eye)
        m1 = vy.x
        m5 = vy.y
        m9 = vy.z
        m13 = -(vector3Dot vy eye)
        m2 = vz.x
        m6 = vz.y
        m10 = vz.z
        m14 = -(vector3Dot vz eye)
        m3 = 0.0f
        m7 = 0.0f
        m11 = 0.0f
        m15 = 1.0f
    }

let vector3Transform (v: Vector3) (mat: Matrix) : Vector3 =
    {
        x = mat.m0 * v.x + mat.m4 * v.y + mat.m8 * v.z + mat.m12
        y = mat.m1 * v.x + mat.m5 * v.y + mat.m9 * v.z + mat.m13
        z = mat.m2 * v.x + mat.m6 * v.y + mat.m10 * v.z + mat.m14
    }

let quaternionFromAxisAngle (axis: Vector3) (angleDeg: float32) : Quaternion =
    let n = vector3Normalize axis
    let half = (angleDeg * deg2Rad) * 0.5f
    let s = sin half

    {
        x = n.x * s
        y = n.y * s
        z = n.z * s
        w = cos half
    }

let quaternionToMatrix (q: Quaternion) : Matrix =
    let a2 = q.x * q.x
    let b2 = q.y * q.y
    let c2 = q.z * q.z
    let ac = q.x * q.z
    let ab = q.x * q.y
    let bc = q.y * q.z
    let ad = q.w * q.x
    let bd = q.w * q.y
    let cd = q.w * q.z
    let mutable r = matrixIdentity ()
    r.m0 <- 1.0f - 2.0f * (b2 + c2)
    r.m1 <- 2.0f * (ab + cd)
    r.m2 <- 2.0f * (ac - bd)
    r.m4 <- 2.0f * (ab - cd)
    r.m5 <- 1.0f - 2.0f * (a2 + c2)
    r.m6 <- 2.0f * (bc + ad)
    r.m8 <- 2.0f * (ac + bd)
    r.m9 <- 2.0f * (bc - ad)
    r.m10 <- 1.0f - 2.0f * (a2 + b2)
    r
