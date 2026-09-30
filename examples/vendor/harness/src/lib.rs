//! Tests for the vendored crates (crc32fast, hex, itoa, memchr, once_cell,
//! bitflags, cfg-if). The vendored crates' own unit tests also run; this file
//! exercises the public APIs end to end against well-known reference values.

use bitflags::bitflags;
use crc32fast::Hasher;

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct Perms: u8 {
        const READ = 1;
        const WRITE = 2;
        const EXEC = 4;
    }
}

fn lcg(s: &mut u64) -> u32 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (*s >> 33) as u32
}

#[test]
fn crc32_reference_values() {
    // zlib reference checksums
    assert_eq!(crc32fast::hash(b""), 0x00000000);
    assert_eq!(crc32fast::hash(b"foo bar baz"), 0xf262de61);
    assert_eq!(crc32fast::hash(b"The quick brown fox jumps over the lazy dog"), 0x414fa339);

    // chunked update equals one-shot, over pseudo-random chunk sizes
    let mut s = 0xdead_f00du64;
    for len in 0..600u32 {
        let data: Vec<u8> = (0..len).map(|_| lcg(&mut s) as u8).collect();
        let want = crc32fast::hash(&data);
        let mut h = Hasher::new();
        let mut off = 0usize;
        while off < data.len() {
            let n = 1 + (lcg(&mut s) as usize) % 37;
            let end = (off + n).min(data.len());
            h.update(&data[off..end]);
            off = end;
        }
        assert_eq!(h.finalize(), want);
    }
}

#[test]
fn crc32_combine() {
    let mut h1 = Hasher::new();
    h1.update(b"hello, ");
    let mut h2 = Hasher::new();
    h2.update(b"world");
    let combined = {
        let mut c = h1.clone();
        c.combine(&h2);
        c
    };
    let mut direct = Hasher::new();
    direct.update(b"hello, world");
    assert_eq!(combined.finalize(), direct.finalize());
}

#[test]
fn hex_round_trip() {
    let data: Vec<u8> = (0..=255u8).collect();
    let enc = hex::encode(&data);
    assert_eq!(enc.len(), 512);
    assert_eq!(hex::decode(&enc).unwrap(), data);
    assert_eq!(hex::encode("hello world"), "68656c6c6f20776f726c64");
    assert_eq!(hex::decode("48656c6c6f").unwrap(), b"Hello");
    assert!(hex::decode("zz").is_err());
    assert_eq!(hex::encode_upper("hello"), "68656C6C6F");
}

#[test]
fn itoa_formats() {
    let mut buf = itoa::Buffer::new();
    assert_eq!(buf.format(0), "0");
    assert_eq!(buf.format(12345), "12345");
    assert_eq!(buf.format(-98765), "-98765");
    assert_eq!(buf.format(i64::MIN), "-9223372036854775808");
    assert_eq!(buf.format(i64::MAX), "9223372036854775807");
}

#[test]
fn memchr_searches() {
    let hay: Vec<u8> = (0..10_000u32).map(|i| (i % 251) as u8).collect();
    for needle in [b'a', 0u8, 250u8, 42u8] {
        let mut expect = hay.iter().position(|&b| b == needle);
        let mut off = 0;
        while let Some(rel) = memchr::memchr(needle, &hay[off..]) {
            assert_eq!(Some(off + rel), expect);
            off += rel + 1;
            expect = hay[off..].iter().position(|&b| b == needle).map(|p| p + off);
        }
        assert!(expect.is_none());
    }
    assert_eq!(memchr::memchr(b'z', b"hello world"), None);
    assert_eq!(memchr::memchr2(b'w', b'l', b"hello world"), Some(2));
    assert_eq!(memchr::memrchr(b'l', b"hello world"), Some(9));
}

#[test]
fn once_cell_race() {
    use once_cell::sync::Lazy;
    use once_cell::sync::OnceCell;
    static CELL: OnceCell<u32> = OnceCell::new();
    assert_eq!(CELL.get(), None);
    assert_eq!(CELL.set(41), Ok(()));
    assert_eq!(CELL.get_or_init(|| 42), &41);

    static LAZY: Lazy<Vec<u32>> = Lazy::new(|| (0..100).collect());
    assert_eq!(LAZY.len(), 100);
    assert_eq!(LAZY[99], 99);

    let unsync: once_cell::unsync::OnceCell<u32> = once_cell::unsync::OnceCell::new();
    assert_eq!(unsync.get_or_init(|| 7), &7);
}

#[test]
fn bitflags_ops() {
    let rw = Perms::READ | Perms::WRITE;
    assert!(rw.contains(Perms::READ));
    assert!(!rw.contains(Perms::EXEC));
    assert_eq!(rw - Perms::WRITE, Perms::READ);
    assert_eq!(rw.bits(), 3);
    assert_eq!(format!("{:?}", Perms::EXEC), "Perms(EXEC)");
    assert_eq!(Perms::from_bits_truncate(7), Perms::all());
    assert!(Perms::from_bits(3).is_some());
    assert!(Perms::from_bits(8).is_none());
}

#[test]
fn cfg_if_macro() {
    cfg_if::cfg_if! {
        if #[cfg(target_arch = "aarch64")] {
            const ARCH: &str = "aarch64";
        } else {
            const ARCH: &str = "other";
        }
    }
    assert_eq!(ARCH, if cfg!(target_arch = "aarch64") { "aarch64" } else { "other" });
}
#[test]
fn dbg_crc() {
    println!("{:08x}", crc32fast::hash(b"foo bar baz"));
    println!("{:08x}", crc32fast::hash(b""));
}
