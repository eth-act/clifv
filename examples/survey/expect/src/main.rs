//! `survey-expect <crate>`: print `name<TAB>value` for every case of `<crate>/cases.rs`.
#![allow(unused_imports)]
use std::hint::black_box as bb;

macro_rules! cases {
    ($($name:ident { $($e:expr;)* })*) => {
        { $( $( println!("{}\t{:?}", stringify!($name), $e); )* )* }
    };
}

fn main() {
    let which = std::env::args().nth(1).expect("usage: survey-expect <crate>");
    match which.as_str() {
        "a_arith" => { use a_arith::*; include!("../../a_arith/cases.rs") }
        "b_slices" => { use b_slices::*; include!("../../b_slices/cases.rs") }
        "c_structs_enums" => { use c_structs_enums::*; include!("../../c_structs_enums/cases.rs") }
        "d_loops_iters" => { use d_loops_iters::*; include!("../../d_loops_iters/cases.rs") }
        "e_option_result" => { use e_option_result::*; include!("../../e_option_result/cases.rs") }
        "f_crypto" => { use f_crypto::*; include!("../../f_crypto/cases.rs") }
        "g_u128" => { use g_u128::*; include!("../../g_u128/cases.rs") }
        "h_dyn_generic" => { use h_dyn_generic::*; include!("../../h_dyn_generic/cases.rs") }
        "i_alloc" => { use i_alloc::*; include!("../../i_alloc/cases.rs") }
        c => panic!("unknown crate {c}"),
    }
}
