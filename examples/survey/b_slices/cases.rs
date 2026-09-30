cases! {
    sums { sum_index(bb(&[1, 2, 3, u32::MAX])); sum_index(bb(&[])); split_sum(bb(&[1, 2, 3, 4, 5]), bb(1)); split_sum(bb(&[1, 2]), bb(2)); }
    indexing { get_or_zero(bb(&[5, 6, 7]), bb(2)); get_or_zero(bb(&[5, 6, 7]), bb(3)); index_var(bb(b"hello"), bb(4)); array_index(bb(&[10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]), bb(15)); array_by_value(bb([1, 2, 3, 4, 5, 6, 7, 65535])); }
    arrays { { let a = make_array(bb(9)); (a[0], a[1], a[62], a[63], a.iter().map(|&x| x as u32).sum::<u32>()) }; }
    mutation {
        { let mut d = [0u8; 6]; copy_into(bb(&mut d), bb(b"abc")); d };
        { let mut d = [1u32; 5]; fill(bb(&mut d), bb(0xabcd)); d };
        { let mut d = [1u64, 2, 3, 4]; swap_ends(bb(&mut d)); d };
        { let mut d: [u64; 0] = []; swap_ends(bb(&mut d)); d };
        { let mut d = [5, -1, 3, 3, i32::MIN, 0, 99]; insertion_sort(bb(&mut d)); d };
    }
    bytes { le_u32(bb(&[0x78, 0x56, 0x34, 0x12, 0xff])); be_u64_try(bb(&[1, 2, 3, 4, 5, 6, 7, 8, 9])); eq_slices(bb(b"abc"), bb(b"abc")); eq_slices(bb(b"abc"), bb(b"abd")); eq_slices(bb(b"ab"), bb(b"abc")); }
    buffer {
        {
            let mut b = Buf { data: [0; 32], len: 30 };
            let r = (buf_push(bb(&mut b), 7), buf_push(bb(&mut b), 8), buf_push(bb(&mut b), 9));
            (r, b.len, b.data[30], b.data[31])
        };
    }
}
