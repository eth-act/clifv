//! (c) structs, enums, match (incl. niches, C-like discriminants, large returns).
#![no_std]

#[derive(Clone, Copy)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

#[derive(Clone, Copy)]
pub struct Big {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u32,
    pub e: u8,
}

pub enum Shape {
    Circle(u32),
    Rect { w: u32, h: u32 },
    Tri(u16, u16, u16),
    Empty,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Op {
    Add = 1,
    Sub = 2,
    Mul = 5,
    Xor = 9,
}

#[no_mangle]
pub fn point_add(p: Point, q: Point) -> Point {
    Point { x: p.x.wrapping_add(q.x), y: p.y.wrapping_add(q.y) }
}

#[no_mangle]
pub fn manhattan(p: &Point) -> u32 {
    p.x.unsigned_abs() + p.y.unsigned_abs()
}

#[no_mangle]
pub fn big_make(a: u64, e: u8) -> Big {
    Big { a, b: a ^ 1, c: a.rotate_left(7), d: a as u32, e }
}

#[no_mangle]
pub fn big_sum(b: Big) -> u64 {
    b.a ^ b.b ^ b.c ^ b.d as u64 ^ b.e as u64
}

#[no_mangle]
pub fn area(s: &Shape) -> u32 {
    match s {
        Shape::Circle(r) => r.wrapping_mul(*r).wrapping_mul(3),
        Shape::Rect { w, h } => w.wrapping_mul(*h),
        Shape::Tri(a, b, c) => (*a as u32) + (*b as u32) + (*c as u32),
        Shape::Empty => 0,
    }
}

#[no_mangle]
pub fn make_shape(k: u8, v: u32) -> Shape {
    match k {
        0 => Shape::Circle(v),
        1 => Shape::Rect { w: v, h: v + 1 },
        2 => Shape::Tri(v as u16, 1, 2),
        _ => Shape::Empty,
    }
}

#[no_mangle]
pub fn apply(op: Op, a: u32, b: u32) -> u32 {
    match op {
        Op::Add => a.wrapping_add(b),
        Op::Sub => a.wrapping_sub(b),
        Op::Mul => a.wrapping_mul(b),
        Op::Xor => a ^ b,
    }
}

#[no_mangle]
pub fn decode_op(b: u8) -> Option<Op> {
    match b {
        1 => Some(Op::Add),
        2 => Some(Op::Sub),
        5 => Some(Op::Mul),
        9 => Some(Op::Xor),
        _ => None,
    }
}

#[no_mangle]
pub fn classify(x: u32) -> u8 {
    match x {
        0 => 10,
        1..=9 => 20,
        10 | 20 | 30 => 30,
        100..=199 => 40,
        _ => 50,
    }
}

#[no_mangle]
pub fn dense_switch(x: u8) -> u32 {
    match x {
        0 => 7,
        1 => 13,
        2 => 21,
        3 => 34,
        4 => 55,
        5 => 89,
        6 => 144,
        7 => 233,
        _ => 0,
    }
}

#[no_mangle]
pub fn niche_ref(o: Option<&u32>) -> u32 {
    match o {
        Some(v) => *v,
        None => 0,
    }
}

#[no_mangle]
pub fn point_eq(a: &Point, b: &Point) -> bool {
    a.x == b.x && a.y == b.y
}

#[no_mangle]
pub fn nested(o: Option<Option<u8>>) -> u8 {
    match o {
        Some(Some(x)) => x,
        Some(None) => 1,
        None => 2,
    }
}

#[no_mangle]
pub fn char_kind(c: char) -> u32 {
    if c.is_ascii_digit() {
        c as u32 - '0' as u32
    } else if c.is_ascii_alphabetic() {
        100
    } else {
        200
    }
}
