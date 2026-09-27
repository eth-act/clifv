//! (a) integer arithmetic: plain ops (overflow-checked in debug), wrapping/checked/
//! overflowing/saturating forms, division, shifts, bit intrinsics, casts.
#![no_std]

#[no_mangle]
pub fn add_u32(a: u32, b: u32) -> u32 {
    a + b
}

#[no_mangle]
pub fn sub_i64(a: i64, b: i64) -> i64 {
    a - b
}

#[no_mangle]
pub fn mul_i32(a: i32, b: i32) -> i32 {
    a * b
}

#[no_mangle]
pub fn mul_u64(a: u64, b: u64) -> u64 {
    a * b
}

#[no_mangle]
pub fn neg_i16(a: i16) -> i16 {
    -a
}

#[no_mangle]
pub fn wrapping_mix(a: u32, b: u32) -> u32 {
    a.wrapping_add(b).wrapping_mul(0x9e37_79b9).wrapping_sub(a >> 3)
}

#[no_mangle]
pub fn checked_add_u32(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

#[no_mangle]
pub fn checked_mul_i64(a: i64, b: i64) -> Option<i64> {
    a.checked_mul(b)
}

#[no_mangle]
pub fn overflowing_sub_u8(a: u8, b: u8) -> (u8, bool) {
    a.overflowing_sub(b)
}

#[no_mangle]
pub fn saturating_ops(a: u16, b: u16, c: i32, d: i32) -> (u16, i32) {
    (a.saturating_sub(b), c.saturating_add(d))
}

#[no_mangle]
pub fn div_u32(a: u32, b: u32) -> u32 {
    a / b
}

#[no_mangle]
pub fn rem_i32(a: i32, b: i32) -> i32 {
    a % b
}

#[no_mangle]
pub fn div_i64_const(a: i64) -> i64 {
    a / 7
}

#[no_mangle]
pub fn checked_div_i32(a: i32, b: i32) -> Option<i32> {
    a.checked_div(b)
}

#[no_mangle]
pub fn shl_u32(a: u32, s: u32) -> u32 {
    a << s
}

#[no_mangle]
pub fn shr_i64(a: i64, s: u32) -> i64 {
    a >> s
}

#[no_mangle]
pub fn rotl_u64(a: u64, s: u32) -> u64 {
    a.rotate_left(s)
}

#[no_mangle]
pub fn bits(a: u32) -> u32 {
    a.leading_zeros() + a.trailing_zeros() + a.count_ones()
}

#[no_mangle]
pub fn swap_bytes(a: u32) -> u32 {
    a.swap_bytes() ^ a.reverse_bits()
}

#[no_mangle]
pub fn abs_i32(a: i32) -> i32 {
    a.abs()
}

#[no_mangle]
pub fn casts(a: i64, b: u8, c: i8) -> u64 {
    (a as u8 as u64) + (b as i64 as u64) + (c as i64 as u64) + (a as u32 as u64)
}

#[no_mangle]
pub fn minmax(a: i32, b: i32, c: u64, d: u64) -> i64 {
    a.min(b) as i64 + a.max(b) as i64 + c.min(d) as i64
}

#[no_mangle]
pub fn cmp_bool(a: u32, b: u32, c: bool) -> bool {
    (a < b && c) || (a == b) ^ !c
}

#[no_mangle]
pub fn pow_u32(a: u32, e: u32) -> u32 {
    a.pow(e)
}
