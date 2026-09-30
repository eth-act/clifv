//! The survey crate's functions on fixed inputs; expected values: tests/expected.txt (rustc/LLVM,
//! ../gen-expected.sh). The cases are in cases.rs, shared with the generator.
#![allow(unused_imports)]
use a_arith::*;
use std::hint::black_box as bb;

const EXPECTED: &str = include_str!("expected.txt");
include!("../../harness.rs");
include!("../cases.rs");

#[test]
#[cfg_attr(not(debug_assertions), ignore = "overflow checks are off")]
#[should_panic(expected = "attempt to add with overflow")]
fn add_overflow_panics() {
    add_u32(bb(u32::MAX), bb(1));
}

#[test]
#[should_panic(expected = "attempt to divide by zero")]
fn div_by_zero_panics() {
    div_u32(bb(1), bb(0));
}

#[test]
#[cfg_attr(not(debug_assertions), ignore = "overflow checks are off")]
#[should_panic(expected = "attempt to shift left with overflow")]
fn shift_overflow_panics() {
    shl_u32(bb(1), bb(32));
}
