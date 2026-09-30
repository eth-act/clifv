cases! {
    parsing {
        digit(bb(b'7')); digit(bb(b'x'));
        parse_u32(bb(b"")); parse_u32(bb(b"12345")); parse_u32(bb(b"4294967295")); parse_u32(bb(b"4294967296")); parse_u32(bb(b"12a4"));
        sum_results(bb(b"1234")); sum_results(bb(b"12-4"));
    }
    options {
        first_two(bb(&[1, 2, 3])); first_two(bb(&[1])); first_two(bb(&[u32::MAX, 2]));
        opt_map(bb(Some(u32::MAX))); opt_map(bb(None));
        opt_and_then(bb(Some(1)), bb(Some(2))); opt_and_then(bb(None), bb(Some(2))); opt_and_then(bb(Some(255)), bb(None));
        opt_u64_zip(bb(Some(10)), bb(Some(3))); opt_u64_zip(bb(Some(3)), bb(Some(10))); opt_u64_zip(bb(None), bb(Some(1)));
    }
    results {
        res_map_err(bb(Ok(5))); res_map_err(bb(Err(b'?')));
        unwrap_it(bb(Some(77))); expect_it(bb(Ok(u64::MAX)));
        res_is_ok(bb(&Ok(1))); res_is_ok(bb(&Err(ParseErr::Overflow)));
    }
}
