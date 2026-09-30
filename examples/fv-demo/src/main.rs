//! `cargo fv run -- 27 1071 462`: a few of the library's functions on command-line numbers.
use fv_demo::{arith, dynamic, iters, wide};

fn main() {
    let args: Vec<u64> = std::env::args().skip(1).filter_map(|a| a.parse().ok()).collect();
    let n = args.first().copied().unwrap_or(27);
    let (a, b) = (args.get(1).copied().unwrap_or(1071), args.get(2).copied().unwrap_or(462));
    println!("collatz_steps({n}) = {}", arith::collatz_steps(n));
    println!("gcd({a}, {b}) = {}", arith::gcd(a, b));
    println!("isqrt({n}) = {}", arith::isqrt(n));
    println!("fib_u128({}) = {}", n.min(186), wide::fib_u128(n.min(186) as u32));
    println!("squares_of_odds({}) = {:?}", n.min(12), iters::squares_of_odds(n.min(12) as u32));
    for animal in dynamic::zoo() {
        println!("{}", animal.speak());
    }
}
