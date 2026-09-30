//! The survey crate's functions on fixed inputs; expected values: tests/expected.txt (rustc/LLVM,
//! ../gen-expected.sh). The cases are in cases.rs, shared with the generator.
#![allow(unused_imports)]
use e_option_result::*;
use std::hint::black_box as bb;

const EXPECTED: &str = include_str!("expected.txt");
include!("../../harness.rs");
include!("../cases.rs");

#[test]
#[should_panic(expected = "called `Option::unwrap()` on a `None` value")]
fn unwrap_none_panics() {
    unwrap_it(bb(None));
}

#[test]
#[should_panic(expected = "bad: Empty")]
fn expect_err_panics() {
    expect_it(bb(Err(ParseErr::Empty)));
}
