//! The survey crate's functions on fixed inputs; expected values: tests/expected.txt (rustc/LLVM,
//! ../gen-expected.sh). The cases are in cases.rs, shared with the generator.
#![allow(unused_imports)]
use f_crypto::*;
use std::hint::black_box as bb;

const EXPECTED: &str = include_str!("expected.txt");
include!("../../harness.rs");
include!("../cases.rs");
