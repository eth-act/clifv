//! (d) loops and iterator chains.
#![no_std]

#[no_mangle]
pub fn sum_range(n: u32) -> u32 {
    let mut s = 0u32;
    for i in 0..n {
        s = s.wrapping_add(i);
    }
    s
}

#[no_mangle]
pub fn while_collatz(mut n: u64) -> u32 {
    let mut steps = 0;
    while n != 1 && n != 0 {
        n = if n % 2 == 0 { n / 2 } else { n.wrapping_mul(3).wrapping_add(1) };
        steps += 1;
    }
    steps
}

#[no_mangle]
pub fn iter_sum(s: &[u32]) -> u32 {
    s.iter().fold(0u32, |a, &x| a.wrapping_add(x))
}

#[no_mangle]
pub fn map_filter_sum(s: &[i64]) -> i64 {
    s.iter().map(|x| x.wrapping_mul(3)).filter(|x| x & 1 == 0).fold(0, |a, x| a.wrapping_add(x))
}

#[no_mangle]
pub fn dot(a: &[u32], b: &[u32]) -> u32 {
    a.iter().zip(b.iter()).map(|(x, y)| x.wrapping_mul(*y)).fold(0, u32::wrapping_add)
}

#[no_mangle]
pub fn enumerate_max(s: &[u16]) -> usize {
    let mut best = 0;
    let mut bi = 0;
    for (i, &x) in s.iter().enumerate() {
        if x > best {
            best = x;
            bi = i;
        }
    }
    bi
}

#[no_mangle]
pub fn rev_step(n: u32) -> u32 {
    (0..n).rev().step_by(3).fold(0, |a, x| a ^ x)
}

#[no_mangle]
pub fn position(s: &[u8], b: u8) -> Option<usize> {
    s.iter().position(|&x| x == b)
}

#[no_mangle]
pub fn any_zero(s: &[u32]) -> bool {
    s.iter().any(|&x| x == 0)
}

#[no_mangle]
pub fn chunks_xor(s: &[u8]) -> u32 {
    let mut h = 0u32;
    for c in s.chunks_exact(4) {
        h ^= u32::from_le_bytes([c[0], c[1], c[2], c[3]]);
    }
    h
}

#[no_mangle]
pub fn nested_loops(n: usize) -> usize {
    let mut c = 0usize;
    'outer: for i in 0..n {
        for j in 0..n {
            if i * j > 1000 {
                break 'outer;
            }
            c = c.wrapping_add(i ^ j);
        }
    }
    c
}

#[no_mangle]
pub fn count_matching(s: &[u8]) -> usize {
    s.iter().filter(|c| c.is_ascii_uppercase()).count()
}
