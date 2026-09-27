//! (i, extra) heap allocation through `alloc`: Vec/Box, to see allocator and memcpy calls.
#![no_std]
extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;

#[no_mangle]
pub fn vec_squares(n: u32) -> Vec<u32> {
    let mut v = Vec::new();
    for i in 0..n {
        v.push(i.wrapping_mul(i));
    }
    v
}

#[no_mangle]
pub fn vec_sum(v: &Vec<u32>) -> u32 {
    v.iter().fold(0, |a, x| a.wrapping_add(*x))
}

#[no_mangle]
pub fn boxed(x: u64) -> Box<[u64; 4]> {
    Box::new([x, x + 1, x + 2, x + 3])
}
