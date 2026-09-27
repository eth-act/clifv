//! (b) slices and arrays with bounds checks, copies, fills, by-value arrays.
#![no_std]

#[no_mangle]
pub fn sum_index(s: &[u32]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < s.len() {
        acc = acc.wrapping_add(s[i]);
        i += 1;
    }
    acc
}

#[no_mangle]
pub fn get_or_zero(s: &[u64], i: usize) -> u64 {
    match s.get(i) {
        Some(v) => *v,
        None => 0,
    }
}

#[no_mangle]
pub fn index_var(s: &[u8], i: usize) -> u8 {
    s[i]
}

#[no_mangle]
pub fn array_index(a: &[u32; 16], i: usize) -> u32 {
    a[i] ^ a[3]
}

#[no_mangle]
pub fn array_by_value(a: [u16; 8]) -> u16 {
    a[0].wrapping_add(a[7])
}

#[no_mangle]
pub fn make_array(x: u8) -> [u8; 64] {
    let mut a = [0u8; 64];
    a[0] = x;
    a[63] = x;
    a
}

#[no_mangle]
pub fn copy_into(dst: &mut [u8], src: &[u8]) {
    dst[..src.len()].copy_from_slice(src);
}

#[no_mangle]
pub fn fill(dst: &mut [u32], v: u32) {
    dst.fill(v);
}

#[no_mangle]
pub fn split_sum(s: &[i32], mid: usize) -> i32 {
    let (a, b) = s.split_at(mid);
    a.len() as i32 - b.len() as i32
}

#[no_mangle]
pub fn swap_ends(s: &mut [u64]) {
    if !s.is_empty() {
        let n = s.len() - 1;
        s.swap(0, n);
    }
}

#[no_mangle]
pub fn insertion_sort(s: &mut [i32]) {
    for i in 1..s.len() {
        let mut j = i;
        while j > 0 && s[j - 1] > s[j] {
            s.swap(j - 1, j);
            j -= 1;
        }
    }
}

#[no_mangle]
pub fn le_u32(b: &[u8]) -> u32 {
    u32::from_le_bytes([b[0], b[1], b[2], b[3]])
}

#[no_mangle]
pub fn be_u64_try(b: &[u8]) -> u64 {
    match <[u8; 8]>::try_from(&b[..8]) {
        Ok(a) => u64::from_be_bytes(a),
        Err(_) => 0,
    }
}

#[no_mangle]
pub fn eq_slices(a: &[u8], b: &[u8]) -> bool {
    a == b
}

pub struct Buf {
    pub data: [u8; 32],
    pub len: usize,
}

#[no_mangle]
pub fn buf_push(b: &mut Buf, x: u8) -> bool {
    if b.len < b.data.len() {
        b.data[b.len] = x;
        b.len += 1;
        true
    } else {
        false
    }
}
