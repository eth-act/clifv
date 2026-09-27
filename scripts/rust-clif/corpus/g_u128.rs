//! (g) 128-bit integers: add/mul/shift/compare, widening multiply, division, checked mul.
#![no_std]

#[no_mangle]
pub fn add_u128(a: u128, b: u128) -> u128 {
    a + b
}

#[no_mangle]
pub fn wmul_u128(a: u128, b: u128) -> u128 {
    a.wrapping_mul(b)
}

#[no_mangle]
pub fn widening_mul(a: u64, b: u64) -> (u64, u64) {
    let p = a as u128 * b as u128;
    (p as u64, (p >> 64) as u64)
}

#[no_mangle]
pub fn shl_u128(a: u128, s: u32) -> u128 {
    a << s
}

#[no_mangle]
pub fn sar_i128(a: i128, s: u32) -> i128 {
    a >> s
}

#[no_mangle]
pub fn cmp_i128(a: i128, b: i128) -> bool {
    a < b
}

#[no_mangle]
pub fn div_u128(a: u128, b: u128) -> u128 {
    a / b
}

#[no_mangle]
pub fn rem_i128(a: i128, b: i128) -> i128 {
    a % b
}

#[no_mangle]
pub fn checked_mul_u128(a: u128, b: u128) -> Option<u128> {
    a.checked_mul(b)
}

#[no_mangle]
pub fn from_le(b: &[u8; 16]) -> u128 {
    u128::from_le_bytes(*b)
}

#[no_mangle]
pub fn clz_u128(a: u128) -> u32 {
    a.leading_zeros() + a.count_ones()
}

/// Poly1305-style limb multiply-accumulate.
#[no_mangle]
pub fn mac_limbs(h: &[u64; 3], r: &[u64; 2]) -> [u64; 3] {
    let d0 = h[0] as u128 * r[0] as u128;
    let d1 = h[0] as u128 * r[1] as u128 + h[1] as u128 * r[0] as u128;
    let d2 = h[1] as u128 * r[1] as u128 + h[2] as u128 * r[0] as u128;
    let c0 = (d0 >> 64) as u64;
    let s1 = d1 + c0 as u128;
    let c1 = (s1 >> 64) as u64;
    [d0 as u64, s1 as u64, (d2 as u64).wrapping_add(c1)]
}
