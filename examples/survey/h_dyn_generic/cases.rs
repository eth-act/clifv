cases! {
    generics { generic_fnv(bb(&[1, 2, 3])); generic_xor(bb(&[1, 2, 3])); hash_all(bb(&mut Fnv(7)), bb(&[])); hash_all(bb(&mut Xor(7)), bb(&[0xffff_ffff])); }
    dynamic {
        dyn_hash(bb(&mut Fnv(2166136261) as &mut dyn Hasher), bb(&[1, 2, 3]));
        dyn_hash(bb(&mut Xor(0) as &mut dyn Hasher), bb(&[9, 8, 7]));
        dyn_pick(bb(true), bb(&[5, 6])); dyn_pick(bb(false), bb(&[5, 6]));
        total_area(bb(&[&(3u32, 4u32) as &dyn Area, &5u32, &(u32::MAX, 2u32)]));
    }
    functions {
        fn_ptr(bb(|x: u32| x.wrapping_mul(3) + 1), bb(5));
        fn_ptr_table(bb(0), bb(21)); fn_ptr_table(bb(1), bb(21)); fn_ptr_table(bb(3), bb(0x1234));
        closure_dyn(bb(&|x: u64| x * x), bb(12)); closure_dyn(bb(&|x: u64| x.rotate_left(1)), bb(u64::MAX));
        apply_twice(|x: u64| x + 10, bb(1)); closure_generic(bb(3), bb(7)); closure_generic(bb(u64::MAX), bb(u64::MAX));
    }
}
