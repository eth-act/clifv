//! End-to-end checks of `clif-native` (needs clang, rust-lld and qemu-aarch64-static, like
//! the binary itself).

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::{Value, json};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(name)
}

/// Runs clif-native; returns the `actual` outcome of every record, stderr and exit code.
fn native(args: &[&str]) -> (Vec<Value>, String, i32) {
    let out = Command::new(env!("CARGO_BIN_EXE_clif-native")).args(args).output().expect("running clif-native");
    let stdout = String::from_utf8(out.stdout).unwrap();
    let actual = stdout
        .lines()
        .map(|l| serde_json::from_str::<Value>(l).unwrap()["actual"].clone())
        .collect();
    (actual, String::from_utf8_lossy(&out.stderr).into_owned(), out.status.code().unwrap_or(-1))
}

fn ret(values: &[(&str, &str)]) -> Value {
    json!({ "returned": values.iter().map(|(ty, bits)| json!({"ty": ty, "bits": bits})).collect::<Vec<_>>() })
}

fn error_text(v: &Value) -> &str {
    v["error"].as_str().unwrap_or_else(|| panic!("expected an error, got {v}"))
}

#[test]
fn traps_faults_and_hangs() {
    let file = fixture("traps.clif");
    let (actual, _, code) = native(&[file.to_str().unwrap(), "--timeout", "2"]);
    assert_eq!(code, 0);
    assert_eq!(actual.len(), 12);
    assert_eq!(actual[0], ret(&[("i32", "0x00000003")]));
    assert_eq!(actual[1], json!({"trapped": "int_divz"}));
    assert_eq!(actual[2], json!({"trapped": "int_ovf"}));
    assert_eq!(actual[3], ret(&[("i32", "0xfffffffd")]), "runs after a trap still run");
    assert_eq!(actual[4], json!({"trapped": "int_ovf"}));
    assert_eq!(actual[5], ret(&[("i64", "0x000000000000000a")]));
    assert_eq!(actual[6], json!({"trapped": "user7"}));
    assert_eq!(actual[7], json!({"trapped": "heap_oob"}));
    assert!(error_text(&actual[8]).starts_with("SIGSEGV at %ldnotrap+0x"), "{}", actual[8]);
    assert!(error_text(&actual[9]).contains("timed out"), "{}", actual[9]);
    assert_eq!(
        actual[10],
        ret(&[("i8", "0xff"), ("i128", "0x0102030405060708090a0b0c0d0e0f10"), ("i16", "0xfffe")]),
        "the process restarts after a hang"
    );
    assert!(error_text(&actual[11]).starts_with("not compiled: %big: "), "{}", actual[11]);
}

#[test]
fn externs_from_link_objects() {
    let dir = std::env::temp_dir().join(format!("clif-native-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let c = dir.join("bal.c");
    let obj = dir.join("bal.o");
    std::fs::write(&c, "long balance_of(long x) { return x * 2; }\n").unwrap();
    let clang = std::env::var("CLIF_NATIVE_CLANG").unwrap_or_else(|_| "clang".into());
    let st = Command::new(clang)
        .args(["--target=aarch64-linux-gnu", "-ffreestanding", "-nostdlib", "-O1", "-c"])
        .arg(&c)
        .arg("-o")
        .arg(&obj)
        .status()
        .expect("running clang");
    assert!(st.success());
    let file = fixture("externs.clif");

    let (actual, _, code) = native(&[file.to_str().unwrap(), "--link", obj.to_str().unwrap()]);
    assert_eq!(code, 0);
    assert_eq!(
        actual,
        vec![
            ret(&[("i64", "0x000000000000000c")]),
            json!({"trapped": "int_ovf"}),
            ret(&[("i64", "0x0000000000000004")]),
        ]
    );

    let (actual, stderr, code) = native(&[file.to_str().unwrap()]);
    assert_eq!(code, 0);
    assert!(stderr.contains("unresolved external symbol `balance_of`"), "{stderr}");
    for a in &actual[..2] {
        let e = error_text(a);
        assert!(e.contains("calls %sum_balances") && e.contains("unresolved external symbol `balance_of`"), "{e}");
    }
    assert_eq!(actual[2], ret(&[("i64", "0x0000000000000004")]), "functions without the extern still run");
    let _ = std::fs::remove_dir_all(&dir);
}
