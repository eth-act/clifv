//! The survey crate's functions on fixed inputs; expected values: tests/expected.txt (rustc/LLVM,
//! ../gen-expected.sh). The cases are in cases.rs, shared with the generator.
#![allow(unused_imports)]
use b_slices::*;
use std::hint::black_box as bb;

const EXPECTED: &str = include_str!("expected.txt");
include!("../../harness.rs");
include!("../cases.rs");

#[test]
#[should_panic(expected = "index out of bounds")]
fn index_out_of_bounds_panics() {
    index_var(bb(b"abc"), bb(3));
}

#[test]
#[should_panic]
fn short_slice_panics() {
    le_u32(bb(&[1, 2, 3]));
}
