cases! {
    arith {
        add_u128(bb(u64::MAX as u128), bb(1)); add_u128(bb(1 << 100), bb(1 << 101));
        wmul_u128(bb(u128::MAX), bb(u128::MAX)); wmul_u128(bb(0x1_0000_0001), bb(0xffff_ffff_ffff_ffff_ffff));
        widening_mul(bb(u64::MAX), bb(u64::MAX)); widening_mul(bb(1 << 63), bb(4));
        checked_mul_u128(bb(1 << 64), bb(1 << 63)); checked_mul_u128(bb(1 << 64), bb(1 << 64));
    }
    shifts { shl_u128(bb(1), bb(127)); shl_u128(bb(0xdead_beef), bb(64)); sar_i128(bb(-1 << 100), bb(99)); sar_i128(bb(i128::MIN), bb(127)); sar_i128(bb(i128::MAX), bb(1)); }
    compare { cmp_i128(bb(-1), bb(0)); cmp_i128(bb(i128::MAX), bb(i128::MIN)); cmp_i128(bb(1 << 90), bb(1 << 91)); }
    division {
        div_u128(bb(u128::MAX), bb(10)); div_u128(bb(1 << 127), bb(3 << 64)); div_u128(bb(12345), bb(u128::MAX));
        rem_i128(bb(-(1 << 100) - 7), bb(1 << 61)); rem_i128(bb(i128::MAX), bb(-1_000_000_007));
    }
    bytes_bits {
        from_le(bb(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]));
        clz_u128(bb(0)); clz_u128(bb(1)); clz_u128(bb(u128::MAX));
        mac_limbs(bb(&[u64::MAX, 5, 3]), bb(&[0xffff_ffff_0000_0007, 0x1234_5678_9abc_def0]));
    }
}
