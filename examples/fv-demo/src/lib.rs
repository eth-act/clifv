//! A small library for `cargo fv test`: each module exercises one kind of Rust code; the tests
//! at the bottom check it (their expected values are the ones `cargo test` computes with LLVM).

pub mod arith {
    pub fn gcd(mut a: u64, mut b: u64) -> u64 {
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        a
    }

    pub fn isqrt(n: u64) -> u64 {
        if n < 2 {
            return n;
        }
        let (mut lo, mut hi) = (1u64, n.min(1 << 32));
        while lo < hi {
            let mid = lo + (hi - lo + 1) / 2;
            if mid.checked_mul(mid).is_some_and(|m| m <= n) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        lo
    }

    pub fn collatz_steps(mut n: u64) -> u32 {
        let mut steps = 0;
        while n != 1 {
            n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
            steps += 1;
        }
        steps
    }

    pub fn mix(a: i32, b: i32) -> i32 {
        a.wrapping_mul(31).wrapping_add(b).rotate_left(7) ^ (a >> 3)
    }

    pub fn checked_ops(a: i64, b: i64) -> (Option<i64>, Option<i64>, Option<i64>) {
        (a.checked_add(b), a.checked_mul(b), a.checked_div(b))
    }

    pub fn saturating(a: u8, b: u8) -> (u8, u8) {
        (a.saturating_add(b), a.saturating_sub(b))
    }
}

pub mod slices {
    pub fn sum(xs: &[i64]) -> i64 {
        xs.iter().sum()
    }

    pub fn reverse_in_place(xs: &mut [u32]) {
        let n = xs.len();
        for i in 0..n / 2 {
            xs.swap(i, n - 1 - i);
        }
    }

    pub fn insertion_sort(xs: &mut [i32]) {
        for i in 1..xs.len() {
            let mut j = i;
            while j > 0 && xs[j - 1] > xs[j] {
                xs.swap(j - 1, j);
                j -= 1;
            }
        }
    }

    pub fn binary_search(xs: &[i32], x: i32) -> Option<usize> {
        let (mut lo, mut hi) = (0usize, xs.len());
        while lo < hi {
            let mid = (lo + hi) / 2;
            match xs[mid].cmp(&x) {
                core::cmp::Ordering::Less => lo = mid + 1,
                core::cmp::Ordering::Greater => hi = mid,
                core::cmp::Ordering::Equal => return Some(mid),
            }
        }
        None
    }

    pub fn nth(xs: &[u8], i: usize) -> u8 {
        xs[i] // panics out of bounds
    }
}

pub mod enums {
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum Shape {
        Circle { r: u32 },
        Rect { w: u32, h: u32 },
        Tri(u32, u32, u32),
        Empty,
    }

    impl Shape {
        /// Area times 100 (integer, π ≈ 3.14).
        pub fn area100(self) -> u64 {
            match self {
                Shape::Circle { r } => 314 * (r as u64) * (r as u64),
                Shape::Rect { w, h } => 100 * w as u64 * h as u64,
                Shape::Tri(a, b, c) => {
                    // Heron, integer approximation via 16 * area^2
                    let (a, b, c) = (a as u64, b as u64, c as u64);
                    let p = (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c);
                    100 * super::arith::isqrt(p) / 4
                }
                Shape::Empty => 0,
            }
        }
        pub fn perimeter(self) -> u32 {
            match self {
                Shape::Circle { r } => 2 * 314 * r / 100,
                Shape::Rect { w, h } => 2 * (w + h),
                Shape::Tri(a, b, c) => a + b + c,
                Shape::Empty => 0,
            }
        }
    }

    #[derive(Debug, PartialEq, Clone, Copy)]
    pub enum Token {
        Num(i64),
        Plus,
        Minus,
        Times,
    }

    /// Evaluate a left-to-right expression (no precedence).
    pub fn eval(tokens: &[Token]) -> Option<i64> {
        let mut it = tokens.iter();
        let mut acc = match it.next()? {
            Token::Num(n) => *n,
            _ => return None,
        };
        while let Some(op) = it.next() {
            let Token::Num(n) = *it.next()? else { return None };
            acc = match op {
                Token::Plus => acc.checked_add(n)?,
                Token::Minus => acc.checked_sub(n)?,
                Token::Times => acc.checked_mul(n)?,
                Token::Num(_) => return None,
            };
        }
        Some(acc)
    }
}

pub mod options {
    #[derive(Debug, PartialEq)]
    pub enum ParseError {
        Empty,
        BadDigit(u8),
        Overflow,
    }

    pub fn parse_u32(s: &[u8]) -> Result<u32, ParseError> {
        if s.is_empty() {
            return Err(ParseError::Empty);
        }
        let mut v: u32 = 0;
        for &c in s {
            if !c.is_ascii_digit() {
                return Err(ParseError::BadDigit(c));
            }
            v = v.checked_mul(10).and_then(|v| v.checked_add((c - b'0') as u32)).ok_or(ParseError::Overflow)?;
        }
        Ok(v)
    }

    pub fn first_even(xs: &[u32]) -> Option<u32> {
        xs.iter().copied().find(|x| x % 2 == 0)
    }

    pub fn div_all(xs: &[i32], d: i32) -> Result<Vec<i32>, &'static str> {
        xs.iter().map(|&x| x.checked_div(d).ok_or("division failed")).collect()
    }

    pub fn or_default(x: Option<u16>) -> u16 {
        x.map(|v| v * 2).unwrap_or(7)
    }
}

pub mod iters {
    pub fn squares_of_odds(n: u32) -> Vec<u32> {
        (0..n).filter(|x| x % 2 == 1).map(|x| x * x).collect()
    }

    pub fn dot(a: &[i32], b: &[i32]) -> i64 {
        a.iter().zip(b).map(|(&x, &y)| x as i64 * y as i64).sum()
    }

    pub fn running_max(xs: &[i32]) -> Vec<i32> {
        xs.iter()
            .scan(i32::MIN, |m, &x| {
                *m = (*m).max(x);
                Some(*m)
            })
            .collect()
    }

    pub fn count_words(s: &str) -> usize {
        s.split_whitespace().count()
    }

    pub fn fold_hash(xs: &[u8]) -> u32 {
        xs.iter().rev().enumerate().fold(17u32, |h, (i, &b)| h.wrapping_mul(31) ^ (b as u32).wrapping_add(i as u32))
    }
}

pub mod wide {
    pub fn mul_full(a: u64, b: u64) -> (u64, u64) {
        let p = a as u128 * b as u128;
        (p as u64, (p >> 64) as u64)
    }

    pub fn fib_u128(n: u32) -> u128 {
        let (mut a, mut b) = (0u128, 1u128);
        for _ in 0..n {
            let t = a.wrapping_add(b);
            a = b;
            b = t;
        }
        a
    }

    pub fn divmod(a: u128, b: u128) -> (u128, u128) {
        (a / b, a % b)
    }

    pub fn signed_ops(a: i128, b: i128) -> (i128, i128, bool) {
        (a.wrapping_sub(b), a.wrapping_mul(3), a < b)
    }
}

pub mod dynamic {
    pub trait Animal {
        fn name(&self) -> &'static str;
        fn legs(&self) -> u32;
        fn speak(&self) -> String {
            format!("{} with {} legs", self.name(), self.legs())
        }
    }

    pub struct Dog;
    pub struct Bird {
        pub flying: bool,
    }

    impl Animal for Dog {
        fn name(&self) -> &'static str {
            "dog"
        }
        fn legs(&self) -> u32 {
            4
        }
    }

    impl Animal for Bird {
        fn name(&self) -> &'static str {
            if self.flying { "flying bird" } else { "bird" }
        }
        fn legs(&self) -> u32 {
            2
        }
        fn speak(&self) -> String {
            format!("tweet from a {}", self.name())
        }
    }

    pub fn zoo() -> Vec<Box<dyn Animal>> {
        vec![Box::new(Dog), Box::new(Bird { flying: true }), Box::new(Bird { flying: false })]
    }

    pub fn total_legs(zoo: &[Box<dyn Animal>]) -> u32 {
        zoo.iter().map(|a| a.legs()).sum()
    }

    pub fn apply(f: &dyn Fn(i32) -> i32, n: u32, x: i32) -> i32 {
        (0..n).fold(x, |acc, _| f(acc))
    }
}

pub mod panics {
    pub fn checked_index(xs: &[u32], i: usize) -> u32 {
        xs[i]
    }

    pub fn must_be_positive(x: i32) -> i32 {
        assert!(x > 0, "x must be positive, got {x}");
        x
    }

    pub fn divide(a: u32, b: u32) -> u32 {
        a / b
    }

    pub fn unwrap_none(x: Option<u8>) -> u8 {
        x.expect("value required")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::hint::black_box as bb;

    #[test]
    fn arithmetic() {
        assert_eq!(arith::gcd(bb(1071), bb(462)), 21);
        assert_eq!(arith::gcd(bb(0), bb(5)), 5);
        assert_eq!(arith::isqrt(bb(1_000_000_007)), 31622);
        assert_eq!(arith::isqrt(bb(u64::MAX)), 4294967295);
        assert_eq!(arith::collatz_steps(bb(27)), 111);
        assert_eq!(arith::mix(bb(123456), bb(-7)), 489_873_608);
        assert_eq!(arith::checked_ops(bb(i64::MAX), bb(1)), (None, Some(i64::MAX), Some(i64::MAX)));
        assert_eq!(arith::checked_ops(bb(-9), bb(0)), (Some(-9), Some(0), None));
        assert_eq!(arith::checked_ops(bb(i64::MIN), bb(-1)), (None, None, None));
        assert_eq!(arith::saturating(bb(200), bb(100)), (255, 100));
        assert_eq!(arith::saturating(bb(3), bb(9)), (12, 0));
    }

    #[test]
    fn slices() {
        let xs = [5i64, -3, 12, 40, -1];
        assert_eq!(slices::sum(bb(&xs)), 53);
        let mut v = [1u32, 2, 3, 4, 5, 6, 7];
        slices::reverse_in_place(bb(&mut v));
        assert_eq!(v, [7, 6, 5, 4, 3, 2, 1]);
        let mut s = [9, -2, 7, 7, 0, 100, -50, 3];
        slices::insertion_sort(bb(&mut s));
        assert_eq!(s, [-50, -2, 0, 3, 7, 7, 9, 100]);
        assert_eq!(slices::binary_search(bb(&s), 9), Some(6));
        assert_eq!(slices::binary_search(bb(&s), 8), None);
        assert_eq!(slices::nth(bb(b"hello"), 1), b'e');
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn slice_out_of_bounds() {
        slices::nth(bb(b"abc"), bb(3));
    }

    #[test]
    fn enums() {
        use enums::{Shape, Token};
        let shapes = [Shape::Circle { r: 10 }, Shape::Rect { w: 3, h: 4 }, Shape::Tri(3, 4, 5), Shape::Empty];
        let areas: Vec<u64> = shapes.iter().map(|s| bb(*s).area100()).collect();
        assert_eq!(areas, [31400, 1200, 600, 0]);
        let per: Vec<u32> = shapes.iter().map(|s| bb(*s).perimeter()).collect();
        assert_eq!(per, [62, 14, 12, 0]);
        use Token::*;
        assert_eq!(enums::eval(bb(&[Num(2), Plus, Num(3), Times, Num(7)])), Some(35));
        assert_eq!(enums::eval(bb(&[Num(i64::MAX), Plus, Num(1)])), None);
        assert_eq!(enums::eval(bb(&[Plus])), None);
        assert_eq!(enums::eval(bb(&[Num(1), Minus])), None);
    }

    #[test]
    fn options_and_results() {
        use options::ParseError;
        assert_eq!(options::parse_u32(bb(b"4294967295")), Ok(u32::MAX));
        assert_eq!(options::parse_u32(bb(b"4294967296")), Err(ParseError::Overflow));
        assert_eq!(options::parse_u32(bb(b"12x")), Err(ParseError::BadDigit(b'x')));
        assert_eq!(options::parse_u32(bb(b"")), Err(ParseError::Empty));
        assert_eq!(options::first_even(bb(&[1, 3, 8, 10])), Some(8));
        assert_eq!(options::first_even(bb(&[1, 3])), None);
        assert_eq!(options::div_all(bb(&[10, -20, 35]), 5), Ok(vec![2, -4, 7]));
        assert_eq!(options::div_all(bb(&[1]), 0), Err("division failed"));
        assert_eq!(options::or_default(bb(Some(21))), 42);
        assert_eq!(options::or_default(bb(None)), 7);
    }

    #[test]
    fn iterators() {
        assert_eq!(iters::squares_of_odds(bb(10)), vec![1, 9, 25, 49, 81]);
        assert_eq!(iters::dot(bb(&[1, 2, 3]), bb(&[4, -5, 6])), 12);
        assert_eq!(iters::running_max(bb(&[3, 1, 4, 1, 5, 9, 2, 6])), vec![3, 3, 4, 4, 5, 9, 9, 9]);
        assert_eq!(iters::count_words(bb("  the quick  brown\tfox ")), 4);
        assert_eq!(iters::fold_hash(bb(b"cargo fv")), 1_031_740_153);
    }

    #[test]
    fn u128_arithmetic() {
        assert_eq!(wide::mul_full(bb(u64::MAX), bb(u64::MAX)), (1, u64::MAX - 1));
        assert_eq!(wide::fib_u128(bb(150)), 9_969_216_677_189_303_386_214_405_760_200);
        let big = 340_282_366_920_938_463_463_374_607_431_768_211_455u128; // u128::MAX
        assert_eq!(wide::divmod(bb(big), bb(1_000_000_007)), (340_282_364_538_961_911_690_641_225_597, 279_632_276));
        assert_eq!(wide::signed_ops(bb(-5), bb(i128::MAX)), (i128::MAX - 3, -15, true));
    }

    #[test]
    fn dyn_traits() {
        let zoo = dynamic::zoo();
        assert_eq!(dynamic::total_legs(bb(&zoo)), 8);
        let said: Vec<String> = zoo.iter().map(|a| a.speak()).collect();
        assert_eq!(said, ["dog with 4 legs", "tweet from a flying bird", "tweet from a bird"]);
        let k = bb(3);
        assert_eq!(dynamic::apply(&|x| x * k + 1, bb(4), bb(1)), 121);
    }

    #[test]
    #[should_panic(expected = "x must be positive, got -3")]
    fn assertion_panics() {
        panics::must_be_positive(bb(-3));
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn division_by_zero_panics() {
        panics::divide(bb(1), bb(0));
    }

    #[test]
    #[should_panic(expected = "value required")]
    fn expect_panics() {
        panics::unwrap_none(bb(None));
    }

    #[test]
    fn no_panic_paths() {
        assert_eq!(panics::checked_index(bb(&[4, 5, 6]), 2), 6);
        assert_eq!(panics::must_be_positive(bb(9)), 9);
        assert_eq!(panics::divide(bb(9), bb(2)), 4);
        assert_eq!(panics::unwrap_none(bb(Some(3))), 3);
    }
}
