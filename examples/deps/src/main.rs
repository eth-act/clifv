//! `cargo fv run --offline`: JSON, regex, hashes and a big factorial, all through dependencies.
fn main() {
    let order = deps_demo::sample_order();
    let json = serde_json::to_string(&order).unwrap();
    println!("{json}");
    let back: deps_demo::Order = serde_json::from_str(&json).unwrap();
    println!("total {} cents, round trip {}", back.total_cents(), if back == order { "ok" } else { "FAILED" });
    println!("sha256(json) = {}", deps_demo::sha256_hex(json.as_bytes()));
    println!("keccak256(json) = {}", deps_demo::keccak256_hex(json.as_bytes()));
    println!("words: {:?}", deps_demo::word_counts("the quick brown fox jumps over the lazy dog the end"));
    println!("40! = {}", deps_demo::factorial(40));
}
