cases! {
    loops { sum_range(bb(0)); sum_range(bb(100)); sum_range(bb(100_000)); while_collatz(bb(27)); while_collatz(bb(0)); while_collatz(bb(u64::MAX)); rev_step(bb(10)); rev_step(bb(1000)); nested_loops(bb(10)); nested_loops(bb(100)); }
    iterators {
        iter_sum(bb(&[1, 2, 3, u32::MAX])); map_filter_sum(bb(&[1, 2, 3, 4, -6, i64::MAX])); dot(bb(&[1, 2, 3]), bb(&[4, 5, 6, 7]));
        enumerate_max(bb(&[3, 9, 2, 9, 1])); enumerate_max(bb(&[]));
        position(bb(b"hello"), bb(b'l')); position(bb(b"hello"), bb(b'z'));
        any_zero(bb(&[1, 2, 0])); any_zero(bb(&[1, 2, 3]));
        chunks_xor(bb(b"abcdefghij")); count_matching(bb(b"Hello World ABC"));
    }
}
