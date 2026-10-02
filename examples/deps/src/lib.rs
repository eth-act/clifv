//! `cargo fv` example with real crates.io dependencies: every crate compiled for the target
//! (this one and its dependencies) goes through the Lean backend; serde_derive is a proc macro
//! and runs on the host (plain rustc). The tests (tests/crates.rs and below) check reference
//! values: published test vectors, and for `rand` the values of an LLVM build.
use bitflags::bitflags;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Order {
    pub id: u64,
    pub customer: String,
    pub items: Vec<Item>,
    pub note: Option<String>,
    pub status: Status,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Item {
    pub sku: String,
    pub qty: u32,
    pub cents: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Open,
    Shipped { day: u16 },
    Cancelled,
}

impl Order {
    pub fn total_cents(&self) -> i64 {
        self.items.iter().map(|i| i.cents * i.qty as i64).sum()
    }
}

pub fn sample_order() -> Order {
    Order {
        id: 42,
        customer: "Ada \"Countess\" Lovelace".into(),
        items: vec![
            Item { sku: "ENG-1".into(), qty: 2, cents: 1999 },
            Item { sku: "CARD-ß".into(), qty: 100, cents: 5 },
        ],
        note: None,
        status: Status::Shipped { day: 7 },
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Perm: u8 {
        const READ = 0b001;
        const WRITE = 0b010;
        const EXEC = 0b100;
    }
}

/// `rwx`-style rendering of a permission set.
pub fn perm_string(p: Perm) -> String {
    [(Perm::READ, 'r'), (Perm::WRITE, 'w'), (Perm::EXEC, 'x')]
        .iter()
        .map(|(f, c)| if p.contains(*f) { *c } else { '-' })
        .collect()
}

/// n! as a decimal string.
pub fn factorial(n: u32) -> String {
    let mut acc = num_bigint::BigUint::from(1u32);
    for i in 2..=n {
        acc *= i;
    }
    acc.to_string()
}

pub fn sha256_hex(data: &[u8]) -> String {
    use sha2::Digest;
    hex::encode(sha2::Sha256::digest(data))
}

pub fn sha512_hex(data: &[u8]) -> String {
    use sha2::Digest;
    hex::encode(sha2::Sha512::digest(data))
}

pub fn keccak256_hex(data: &[u8]) -> String {
    use tiny_keccak::Hasher;
    let mut h = tiny_keccak::Keccak::v256();
    h.update(data);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    hex::encode(out)
}

pub fn sha3_256_hex(data: &[u8]) -> String {
    use tiny_keccak::Hasher;
    let mut h = tiny_keccak::Sha3::v256();
    h.update(data);
    let mut out = [0u8; 32];
    h.finalize(&mut out);
    hex::encode(out)
}

/// Word frequencies in first-seen order.
pub fn word_counts(text: &str) -> indexmap::IndexMap<String, usize> {
    let re = regex::Regex::new(r"[A-Za-z']+").unwrap();
    let mut m = indexmap::IndexMap::new();
    for w in re.find_iter(text) {
        *m.entry(w.as_str().to_lowercase()).or_insert(0) += 1;
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn total() {
        assert_eq!(sample_order().total_cents(), 2 * 1999 + 100 * 5);
    }

    #[test]
    fn perms() {
        assert_eq!(perm_string(Perm::READ | Perm::EXEC), "r-x");
        assert_eq!(perm_string(Perm::all()), "rwx");
        assert_eq!(perm_string(Perm::empty()), "---");
        assert_eq!(Perm::from_bits(0b1000), None);
        assert_eq!((Perm::all() - Perm::WRITE).bits(), 0b101);
    }

    #[test]
    fn words() {
        let m = word_counts("The cat and the hat. THE END, and the cat's hat");
        let v: Vec<(&str, usize)> = m.iter().map(|(k, v)| (k.as_str(), *v)).collect();
        assert_eq!(v, [("the", 4), ("cat", 1), ("and", 2), ("hat", 2), ("end", 1), ("cat's", 1)]);
    }
}
