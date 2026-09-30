cases! {
    points {
        { let p = point_add(bb(Point { x: 1, y: -2 }), bb(Point { x: i32::MAX, y: 5 })); (p.x, p.y) };
        manhattan(bb(&Point { x: -7, y: i32::MIN }));
        point_eq(bb(&Point { x: 1, y: 2 }), bb(&Point { x: 1, y: 2 }));
        point_eq(bb(&Point { x: 1, y: 2 }), bb(&Point { x: 1, y: 3 }));
    }
    big {
        { let b = big_make(bb(0x0123_4567_89ab_cdef), bb(0xee)); (b.a, b.b, b.c, b.d, b.e) };
        big_sum(bb(big_make(bb(u64::MAX), bb(3))));
        big_sum(bb(Big { a: 1, b: 2, c: 4, d: 8, e: 16 }));
    }
    shapes {
        area(bb(&make_shape(bb(0), bb(10))));
        area(bb(&make_shape(bb(1), bb(65536))));
        area(bb(&make_shape(bb(2), bb(70000))));
        area(bb(&make_shape(bb(9), bb(1))));
        area(bb(&Shape::Rect { w: 3, h: 4 }));
    }
    ops {
        apply(bb(Op::Add), bb(u32::MAX), bb(2));
        apply(bb(Op::Sub), bb(1), bb(2));
        apply(bb(Op::Mul), bb(0x10000), bb(0x10001));
        apply(bb(Op::Xor), bb(0xff00), bb(0x0ff0));
        decode_op(bb(5)).map(|o| o as u8);
        decode_op(bb(3)).map(|o| o as u8);
        decode_op(bb(9)).map(|o| apply(o, 6, 3));
    }
    switches {
        classify(bb(0)); classify(bb(5)); classify(bb(20)); classify(bb(150)); classify(bb(200)); classify(bb(u32::MAX));
        dense_switch(bb(0)); dense_switch(bb(7)); dense_switch(bb(8)); dense_switch(bb(255));
    }
    niches {
        niche_ref(bb(Some(&42))); niche_ref(bb(None));
        nested(bb(Some(Some(9)))); nested(bb(Some(None))); nested(bb(None));
        char_kind(bb('7')); char_kind(bb('Q')); char_kind(bb('é')); char_kind(bb(' '));
    }
}
