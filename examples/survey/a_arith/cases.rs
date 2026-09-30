cases! {
    add { add_u32(bb(1), bb(2)); add_u32(bb(0x7fff_ffff), bb(0x8000_0000)); sub_i64(bb(5), bb(7)); sub_i64(bb(i64::MIN + 1), bb(1)); }
    mul { mul_i32(bb(3), bb(-4)); mul_i32(bb(46340), bb(46340)); mul_u64(bb(1 << 40), bb(1 << 20)); mul_u64(bb(3), bb(5)); }
    neg { neg_i16(bb(5)); neg_i16(bb(-32767)); neg_i16(bb(0)); }
    wrapping { wrapping_mix(bb(1), bb(2)); wrapping_mix(bb(u32::MAX), bb(1)); wrapping_mix(bb(0x8000_0000), bb(0x8000_0000)); }
    checked { checked_add_u32(bb(u32::MAX), bb(1)); checked_add_u32(bb(7), bb(8)); checked_mul_i64(bb(i64::MAX), bb(2)); checked_mul_i64(bb(-3), bb(1 << 40)); }
    overflowing { overflowing_sub_u8(bb(3), bb(5)); overflowing_sub_u8(bb(200), bb(100)); }
    saturating { saturating_ops(bb(1), bb(2), bb(i32::MAX), bb(1)); saturating_ops(bb(9), bb(2), bb(i32::MIN), bb(-1)); saturating_ops(bb(9), bb(2), bb(-5), bb(3)); }
    division { div_u32(bb(100), bb(7)); div_u32(bb(u32::MAX), bb(3)); rem_i32(bb(-17), bb(5)); rem_i32(bb(17), bb(-5)); div_i64_const(bb(-100)); div_i64_const(bb(i64::MIN)); div_i64_const(bb(5)); }
    checked_div { checked_div_i32(bb(i32::MIN), bb(-1)); checked_div_i32(bb(7), bb(0)); checked_div_i32(bb(-7), bb(2)); }
    shifts { shl_u32(bb(1), bb(31)); shl_u32(bb(0xdead_beef), bb(4)); shr_i64(bb(-256), bb(4)); shr_i64(bb(i64::MIN), bb(63)); rotl_u64(bb(0x8000_0000_0000_0001), bb(1)); rotl_u64(bb(0x1234), bb(100)); }
    bitops { bits(bb(0)); bits(bb(0xf0)); bits(bb(u32::MAX)); swap_bytes(bb(0x1234_5678)); swap_bytes(bb(1)); }
    abs_casts { abs_i32(bb(-5)); abs_i32(bb(i32::MIN + 1)); casts(bb(-1), bb(255), bb(1)); casts(bb(0x1_0000_0101), bb(7), bb(100)); casts(bb(0), bb(0), bb(-128)); }
    compare { minmax(bb(3), bb(-4), bb(10), bb(u64::MAX)); minmax(bb(i32::MIN), bb(i32::MAX), bb(0), bb(1)); cmp_bool(bb(1), bb(2), bb(true)); cmp_bool(bb(2), bb(2), bb(false)); cmp_bool(bb(3), bb(2), bb(true)); cmp_bool(bb(3), bb(2), bb(false)); }
    pow { pow_u32(bb(3), bb(13)); pow_u32(bb(2), bb(31)); pow_u32(bb(7), bb(0)); }
}
