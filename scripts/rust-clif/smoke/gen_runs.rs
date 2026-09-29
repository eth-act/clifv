//! Prints `; run:` lines for scalar corpus functions, with expected values computed by the
//! corpus itself compiled by rustc's LLVM backend (release profile, host target). Consumed by
//! scripts/rust-clif/smoke.sh, which attaches each line to the function it names.
//! Output: `FUNCTION<TAB>; run: %FUNCTION(args) == value` (or `== [a, b]`).

use a_arith as a;
use c_structs_enums as c;
use d_loops_iters as d;
use h_dyn_generic as h;
use g_u128 as g;

macro_rules! run {
    ($f:ident ( $($x:expr),* ) => $r:expr) => {{
        let args: Vec<String> = vec![$(format!("{}", $x)),*];
        println!("{}\t; run: %{}({}) == {}", stringify!($f), stringify!($f), args.join(", "), $r);
    }};
}

fn b(x: bool) -> u8 {
    x as u8
}

fn main() {
    for (x, y) in [(1u32, 2u32), (u32::MAX, 1), (0x8000_0000, 0x8000_0000)] {
        run!(add_u32(x, y) => a::add_u32(x, y));
        run!(wrapping_mix(x, y) => a::wrapping_mix(x, y));
        run!(cmp_bool(x, y, 1) => b(a::cmp_bool(x, y, true)));
        run!(cmp_bool(x, y, 0) => b(a::cmp_bool(x, y, false)));
    }
    for (x, y) in [(5i64, 7i64), (i64::MIN, 1), (0, i64::MIN)] {
        run!(sub_i64(x, y) => a::sub_i64(x, y));
        run!(div_i64_const(x) => a::div_i64_const(x));
    }
    for (x, y) in [(3i32, -4i32), (i32::MAX, 2), (i32::MIN, -1)] {
        run!(mul_i32(x, y) => a::mul_i32(x, y));
        run!(abs_i32(x) => a::abs_i32(x));
    }
    for (x, y) in [(3u64, 5u64), (u64::MAX, u64::MAX), (1 << 40, 1 << 30)] {
        run!(mul_u64(x, y) => a::mul_u64(x, y));
    }
    for x in [0i16, 7, -32768, 32767] {
        run!(neg_i16(x) => a::neg_i16(x));
    }
    for (x, y) in [(0u8, 1u8), (200, 100), (5, 5)] {
        let (r, o) = a::overflowing_sub_u8(x, y);
        run!(overflowing_sub_u8(x, y) => format!("[{}, {}]", r, b(o)));
    }
    for (x, s) in [(1u32, 0u32), (1, 31), (1, 33), (0xdead_beef, 4)] {
        run!(shl_u32(x, s) => a::shl_u32(x, s));
        run!(rotl_u64(x as u64 | 1 << 63, s) => a::rotl_u64(x as u64 | 1 << 63, s));
        run!(shr_i64(-(x as i64), s) => a::shr_i64(-(x as i64), s));
    }
    for x in [0u32, 1, 0x8000_0000, 0x00f0_0f00, u32::MAX] {
        run!(bits(x) => a::bits(x));
    }
    for (x, y, z) in [(-1i64, 200u8, -3i8), (0x1234_5678_9abc, 0, 127)] {
        run!(casts(x, y, z) => a::casts(x, y, z));
    }
    for op in [c::Op::Add, c::Op::Sub, c::Op::Mul, c::Op::Xor] {
        run!(apply(op as u8, 7u32, 9u32) => c::apply(op, 7, 9));
    }
    for x in [0u32, 5, 20, 150, 99, 1000] {
        run!(classify(x) => c::classify(x));
    }
    for x in 0u8..10 {
        run!(dense_switch(x) => c::dense_switch(x));
    }
    for ch in ['7', 'q', ' ', 'é'] {
        run!(char_kind(ch as u32) => c::char_kind(ch));
    }
    for n in [0u32, 1, 10, 1000] {
        run!(sum_range(n) => d::sum_range(n));
    }
    for n in [0u64, 1, 6, 27, 97] {
        run!(while_collatz(n) => d::while_collatz(n));
    }
    for (k, x) in [(3u64, 5u64), (u64::MAX, 2)] {
        run!(closure_generic(k, x) => h::closure_generic(k, x));
    }

    // rust-route step 4/5: fn pointers / closures with scalar args (rustc oracle); the
    // dyn/`&mut dyn` functions take object pointers (data/vtable addresses) — they run in
    // the interpreter fixture `scripts/rust-clif/fixtures/dyn-vtable.clif` instead.
    run!(fn_ptr_table(0, 7) => h::fn_ptr_table(0, 7));
    run!(fn_ptr_table(1, 7) => h::fn_ptr_table(1, 7));

    // rust-route step 5: i128/u128 functions (rustc/LLVM oracle; these run under
    // `Clif.run`, which supports the i128 ops the dumps use, and — once the backend
    // lowers them — natively; until then the native side reports them not-compiled).
    for (x, y) in [(3u128, 4u128), (u128::MAX, 1), (1 << 100, 7), (0xdead_beef_cafe_f000_1234_5678, 0x1111)] {
        run!(add_u128(x, y) => g::add_u128(x, y));
    }
    for x in [7u128, 1 << 70, u128::MAX] {
        run!(shl_u128(x, 3) => g::shl_u128(x, 3));
    }
    for (x, y) in [(i128::MIN, 3), (123456789i128, -98765)] {
        run!(cmp_i128(x, y) => b(g::cmp_i128(x, y)));
        run!(cmp_i128(y, x) => b(g::cmp_i128(y, x)));
    }
    for x in [(1u128 << 80), u128::MAX] {
        run!(clz_u128(x) => g::clz_u128(x));
    }
}
