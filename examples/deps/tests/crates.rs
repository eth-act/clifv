//! Reference values for the dependencies' code: published test vectors, round trips, and for
//! `rand` (fixed seeds) the values an LLVM build (`cargo test`) computes.
use deps_demo::*;

#[test]
fn serde_json_round_trip() {
    let o = sample_order();
    let s = serde_json::to_string(&o).unwrap();
    assert_eq!(
        s,
        r#"{"id":42,"customer":"Ada \"Countess\" Lovelace","items":[{"sku":"ENG-1","qty":2,"cents":1999},{"sku":"CARD-ß","qty":100,"cents":5}],"note":null,"status":{"shipped":{"day":7}}}"#
    );
    let back: Order = serde_json::from_str(&s).unwrap();
    assert_eq!(back, o);
    let pretty = serde_json::to_string_pretty(&o).unwrap();
    assert_eq!(serde_json::from_str::<Order>(&pretty).unwrap(), o);
}

#[test]
fn serde_json_value() {
    let v: serde_json::Value =
        serde_json::from_str(r#"{"a":[1,-2,3.5,true,null,"x\u00e9\n"],"b":{"c":18446744073709551615}}"#).unwrap();
    assert_eq!(v["a"][1].as_i64(), Some(-2));
    assert_eq!(v["a"][2].as_f64(), Some(3.5));
    assert_eq!(v["a"][5].as_str(), Some("xé\n"));
    assert_eq!(v["b"]["c"].as_u64(), Some(u64::MAX));
    assert_eq!(v.to_string(), r#"{"a":[1,-2,3.5,true,null,"xé\n"],"b":{"c":18446744073709551615}}"#);
    let e = serde_json::from_str::<Order>(r#"{"id":1}"#).unwrap_err();
    assert_eq!(e.to_string(), "missing field `customer` at line 1 column 8");
    let e = serde_json::from_str::<Status>(r#""lost""#).unwrap_err();
    assert!(e.to_string().starts_with("unknown variant `lost`"), "{e}");
}

#[test]
fn regex_matching() {
    let re = regex::Regex::new(r"(?P<y>\d{4})-(?P<m>\d{2})-(?P<d>\d{2})").unwrap();
    let text = "released 2026-09-26, patched 2026-10-02; not 26-9-2026";
    let dates: Vec<String> = re.captures_iter(text).map(|c| format!("{}/{}/{}", &c["d"], &c["m"], &c["y"])).collect();
    assert_eq!(dates, ["26/09/2026", "02/10/2026"]);
    assert_eq!(re.replace_all(text, "$d.$m.$y"), "released 26.09.2026, patched 02.10.2026; not 26-9-2026");
    let ws = regex::Regex::new(r"\s+").unwrap();
    assert_eq!(ws.split("a  b\tc\n d").collect::<Vec<_>>(), ["a", "b", "c", "d"]);
    let alt = regex::Regex::new(r"(?i)\b(foo|bar|baz)+\b").unwrap();
    assert_eq!(alt.find_iter("FooBar x bazfoo foox BAZ").map(|m| m.as_str()).collect::<Vec<_>>(), ["FooBar", "bazfoo", "BAZ"]);
    assert!(!regex::Regex::new(r"^[a-z]+$").unwrap().is_match("abc1"));
    let set = regex::RegexSet::new([r"\d+", r"[aeiou]{2}", r"^x"]).unwrap();
    assert_eq!(set.matches("xoo 12").into_iter().collect::<Vec<_>>(), [0, 1, 2]);
    assert!(regex::Regex::new(r"(unclosed").is_err());
}

#[test]
fn word_frequencies() {
    let m = word_counts("It was the best of times, it was the worst of times");
    assert_eq!(m.get("times"), Some(&2));
    assert_eq!(m.get_index(0), Some((&"it".to_string(), &2)));
    assert_eq!(m.len(), 7);
}

#[test]
fn sha2_vectors() {
    assert_eq!(sha256_hex(b"abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert_eq!(sha256_hex(b""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(
        sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
    assert_eq!(
        sha512_hex(b"abc"),
        "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
    );
    let million_a = vec![b'a'; 1_000_000];
    assert_eq!(sha256_hex(&million_a), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

#[test]
fn keccak_vectors() {
    assert_eq!(keccak256_hex(b""), "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470");
    assert_eq!(sha3_256_hex(b""), "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a");
    assert_eq!(sha3_256_hex(b"abc"), "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532");
}

#[test]
fn bigint_factorials() {
    assert_eq!(factorial(0), "1");
    assert_eq!(factorial(20), "2432902008176640000");
    assert_eq!(factorial(30), "265252859812191058636308480000000");
    assert_eq!(factorial(50), "30414093201713378043612608166064768844377641568960512000000000000");
    let f100 = factorial(100);
    assert_eq!(f100.len(), 158);
    assert!(f100.starts_with("93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864"));
    assert!(f100.ends_with(&"0".repeat(24)));
    use num_bigint::BigInt;
    let a: BigInt = "-123456789012345678901234567890".parse().unwrap();
    let b: BigInt = "987654321098765432109876543210".parse().unwrap();
    assert_eq!((&a * &b).to_string(), "-121932631137021795226185032733622923332237463801111263526900");
    assert_eq!((&b / 7u32).to_string(), "141093474442680776015696649030");
    assert_eq!((&b % 7u32).to_string(), "0");
    assert_eq!(b.pow(3u32).to_str_radix(16).len(), 75);
}

#[test]
fn base64_hex_round_trips() {
    use base64::Engine;
    let e = base64::engine::general_purpose::STANDARD;
    assert_eq!(e.encode(b"hello world"), "aGVsbG8gd29ybGQ=");
    assert_eq!(e.decode("aGVsbG8gd29ybGQ=").unwrap(), b"hello world");
    let all: Vec<u8> = (0..=255u8).collect();
    let enc = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(&all);
    assert_eq!(enc.len(), 342);
    assert_eq!(base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(&enc).unwrap(), all);
    assert!(e.decode("a$==").is_err());
    assert_eq!(hex::encode(b"hello"), "68656c6c6f");
    assert_eq!(hex::decode("DEADbeef").unwrap(), [0xde, 0xad, 0xbe, 0xef]);
    assert_eq!(hex::decode(hex::encode(&all)).unwrap(), all);
    assert!(hex::decode("abc").is_err());
}

#[test]
fn hashbrown_ops() {
    let mut m: hashbrown::HashMap<u64, String> = hashbrown::HashMap::new();
    for i in 0..1000u64 {
        m.insert(i * 7919 % 1009, format!("v{i}"));
    }
    assert_eq!(m.len(), 1000);
    assert_eq!(m.get(&(500 * 7919 % 1009)).map(String::as_str), Some("v500"));
    m.retain(|k, _| k % 3 == 0);
    assert_eq!(m.len(), (0..1009u64).filter(|k| k % 3 == 0 && *k < 1009).filter(|k| (0..1000u64).any(|i| i * 7919 % 1009 == *k)).count());
    let mut s: hashbrown::HashSet<&str> = ["a", "b", "c"].into_iter().collect();
    assert!(s.insert("d"));
    assert!(!s.insert("a"));
    let mut keys: Vec<_> = s.into_iter().collect();
    keys.sort();
    assert_eq!(keys, ["a", "b", "c", "d"]);
}

#[test]
fn indexmap_ops() {
    let mut m = indexmap::IndexMap::new();
    for (i, w) in ["zeta", "alpha", "mu", "alpha", "beta"].iter().enumerate() {
        m.entry(*w).or_insert_with(Vec::new).push(i);
    }
    assert_eq!(m.keys().copied().collect::<Vec<_>>(), ["zeta", "alpha", "mu", "beta"]);
    assert_eq!(m["alpha"], [1, 3]);
    m.shift_remove("alpha");
    assert_eq!(m.get_index_of("beta"), Some(2));
    m.sort_keys();
    assert_eq!(m.keys().copied().collect::<Vec<_>>(), ["beta", "mu", "zeta"]);
    let s: indexmap::IndexSet<u32> = [5, 3, 5, 1, 3].into_iter().collect();
    assert_eq!(s.iter().copied().collect::<Vec<_>>(), [5, 3, 1]);
}

#[test]
fn rand_fixed_seed() {
    use rand::{RngExt, SeedableRng};
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let a: Vec<u32> = (0..8).map(|_| rng.random_range(0..1000)).collect();
    let b: u64 = rng.random();
    let mut v: Vec<u8> = (0..16).collect();
    use rand::seq::SliceRandom;
    v.shuffle(&mut rng);
    let mut bytes = [0u8; 8];
    rand::Rng::fill_bytes(&mut rng, &mut bytes);
    // reference: the LLVM build (`cargo test`, aarch64-unknown-linux-musl)
    assert_eq!(format!("{a:?} {b} {v:?} {}", hex::encode(bytes)), RAND_REFERENCE);
    let mut small = rand::rngs::SmallRng::seed_from_u64(7);
    let c: Vec<i32> = (0..6).map(|_| small.random_range(-50..50)).collect();
    assert_eq!(format!("{c:?}"), SMALL_RAND_REFERENCE);
}

const RAND_REFERENCE: &str =
    "[133, 526, 248, 542, 868, 636, 990, 405] 633513173585076202 [1, 3, 13, 2, 10, 5, 6, 12, 15, 0, 9, 7, 11, 4, 14, 8] fb780859e8d8c7bc";
const SMALL_RAND_REFERENCE: &str = "[-45, -33, 21, -8, 46, -4]";

#[test]
fn small_containers() {
    let mut sv: smallvec::SmallVec<[u32; 4]> = smallvec::SmallVec::new();
    for i in 0..10 {
        sv.push(i * i);
    }
    assert!(sv.spilled());
    sv.retain(|x| *x % 2 == 0);
    assert_eq!(sv.as_slice(), [0, 4, 16, 36, 64]);
    sv.truncate(3);
    assert_eq!(sv.into_vec(), [0, 4, 16]);
    let mut av: arrayvec::ArrayVec<u16, 5> = arrayvec::ArrayVec::new();
    for i in 0..5 {
        av.push(1000 + i);
    }
    assert!(av.try_push(7).is_err());
    assert_eq!(av.remove(1), 1001);
    assert_eq!(av.as_slice(), [1000, 1002, 1003, 1004]);
    let mut s = arrayvec::ArrayString::<16>::new();
    s.push_str("fv-");
    s.push_str("deps");
    assert_eq!(s.as_str(), "fv-deps");
    assert!(s.try_push_str("-overflowing!!").is_err());
}

#[test]
fn numbers_and_bytes() {
    let mut buf = itoa::Buffer::new();
    assert_eq!(buf.format(-9223372036854775808i64), "-9223372036854775808");
    assert_eq!(buf.format(0u8), "0");
    assert_eq!(buf.format(u128::MAX), "340282366920938463463374607431768211455");
    let mut rb = ryu::Buffer::new();
    assert_eq!(rb.format(0.1f64 + 0.2), "0.30000000000000004");
    assert_eq!(rb.format(1e300f64), "1e300");
    assert_eq!(rb.format(-1.5f32), "-1.5");
    use byteorder::{BigEndian, ByteOrder, LittleEndian, ReadBytesExt, WriteBytesExt};
    let mut w = Vec::new();
    w.write_u32::<BigEndian>(0xdeadbeef).unwrap();
    w.write_i16::<LittleEndian>(-2).unwrap();
    w.write_u64::<LittleEndian>(0x0102030405060708).unwrap();
    assert_eq!(hex::encode(&w), "deadbeeffeff0807060504030201");
    let mut r = std::io::Cursor::new(&w);
    assert_eq!(r.read_u32::<BigEndian>().unwrap(), 0xdeadbeef);
    assert_eq!(r.read_i16::<LittleEndian>().unwrap(), -2);
    assert_eq!(LittleEndian::read_u64(&w[6..]), 0x0102030405060708);
    assert_eq!(crc32fast::hash(b"123456789"), 0xcbf43926);
    let mut h = crc32fast::Hasher::new();
    h.update(b"1234");
    h.update(b"56789");
    assert_eq!(h.finalize(), 0xcbf43926);
    assert_eq!(memchr::memchr(b'z', b"abcxyz"), Some(5));
    assert_eq!(memchr::memrchr(b'a', b"banana"), Some(5));
    assert_eq!(memchr::memmem::find_iter(b"abababab", b"aba").collect::<Vec<_>>(), [0, 4]);
    use num_traits::{CheckedMul, Pow, PrimInt};
    assert_eq!(CheckedMul::checked_mul(&250u8, &2), None);
    assert_eq!(Pow::pow(3u64, 5u32), 243);
    assert_eq!(0x00f0u16.leading_zeros(), 8);
    assert_eq!(PrimInt::count_ones(0xffu32), 8);
}
