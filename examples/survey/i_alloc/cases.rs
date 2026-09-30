cases! {
    vectors { vec_squares(bb(0)); vec_squares(bb(8)); vec_sum(bb(&vec_squares(bb(1000)))); vec_squares(bb(70000)).len(); }
    boxes { boxed(bb(40)); *boxed(bb(u64::MAX - 3)); }
}
