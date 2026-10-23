//! Writes `big` (into `OUT_DIR/big.rs`): it keeps `N` `u64` values and 20 `f64` values live
//! across a call that may panic, so the allocator spills them and the frame is larger than
//! 32 KiB (with N = 1600 about 38 KiB; the issue #479 repro).
use std::fmt::Write;

const N: usize = 1600;
const F: usize = 20;

fn main() {
    let mut s = String::new();
    s.push_str("#[inline(never)]\npub fn big(x: u64) -> u64 {\n");
    for i in 0..N {
        writeln!(s, "    let a{i} = black_box(x.wrapping_add({i}));").unwrap();
    }
    for i in 0..F {
        writeln!(s, "    let f{i} = black_box(f64::from_bits(x.wrapping_add({i}) | 0x4000_0000_0000_0000));")
            .unwrap();
    }
    s.push_str("    may_panic(x);\n    let mut s = 0u64;\n");
    for i in 0..N {
        writeln!(s, "    s = s.wrapping_add(a{i});").unwrap();
    }
    for i in 0..F {
        writeln!(s, "    s = s.wrapping_add(f{i}.to_bits());").unwrap();
    }
    s.push_str("    s\n}\n");
    let out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("big.rs");
    std::fs::write(out, s).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
