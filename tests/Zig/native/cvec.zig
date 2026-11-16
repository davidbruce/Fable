//! C declarations of functions that take and give structs by value, as a module translated from
//! a header would declare them (InteropTests.fs imports them with `c:`)
pub const Vector2 = extern struct { x: f32, y: f32 };
pub const Rect = extern struct { pos: Vector2, width: f32, height: f32, solid: bool };
pub extern "c" fn fable_test_vadd(a: Vector2, b: Vector2) Vector2;
pub extern "c" fn fable_test_area(r: Rect) f32;
