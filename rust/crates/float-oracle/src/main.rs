//! Host oracle for the Lean IEEE core (`FV/Float`, `docs/contracts/float.md`).
//!
//! Reads `float-difftest` lines `<class> <mode> <a> <b> <c> <result>` (hex) from stdin,
//! recomputes each case with Rust's `f32`/`f64` operations and compares with the Lean result:
//! bit-for-bit, except that two NaNs agree unless `--exact-nan` is given (the host's NaN
//! payload rules differ from Arm's; on aarch64 the comparison is exact).
//!
//! Rounding modes `p`/`m`/`z` for arithmetic and format conversion are set in the
//! floating-point control register (x86 MXCSR.RC, aarch64 FPCR.RMode) around the operation;
//! `rint`/`tofix` use the mode-independent `round_ties_even`/`ceil`/`floor`/`trunc`/`round`.
//! Prints one summary line per class and exits 1 on any mismatch.

use std::collections::BTreeMap;
use std::hint::black_box;
use std::io::{BufRead, Write};

/// Rounding-control encoding for `mode`: 0 nearest, 1 toward +∞, 2 toward −∞, 3 toward zero.
fn mode_index(mode: char) -> u64 {
    match mode {
        'n' => 0,
        'p' => 1,
        'm' => 2,
        'z' => 3,
        _ => panic!("rounding mode {mode} is not a control-register mode"),
    }
}

#[cfg(target_arch = "x86_64")]
fn set_mode(mode: char) {
    // MXCSR.RC (bits 13-14): 00 nearest, 01 down, 10 up, 11 toward zero.
    let rc: u32 = [0, 2, 1, 3][mode_index(mode) as usize];
    let mut csr: u32 = 0;
    unsafe {
        std::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut csr, options(nostack));
        csr = (csr & !0x6000) | (rc << 13);
        std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &csr, options(nostack));
    }
}

#[cfg(target_arch = "aarch64")]
fn set_mode(mode: char) {
    // FPCR.RMode (bits 22-23): 00 RN, 01 RP, 10 RM, 11 RZ.
    let rm = mode_index(mode);
    unsafe {
        let mut v: u64;
        std::arch::asm!("mrs {v}, fpcr", v = out(reg) v, options(nostack));
        v = (v & !(3 << 22)) | (rm << 22);
        std::arch::asm!("msr fpcr, {v}", v = in(reg) v, options(nostack));
    }
}

/// Run `op` with the control register in `mode`, inputs and output kept opaque so the
/// operation cannot be moved across the mode switches or constant-folded.
#[inline(never)]
fn in_mode<T: Copy, R: Copy>(mode: char, x: T, op: impl Fn(T) -> R) -> R {
    set_mode(mode);
    let r = black_box(op(black_box(x)));
    set_mode('n');
    r
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Res {
    F32(u32),
    F64(u64),
    Int(u64),
}

impl Res {
    fn is_nan(self) -> bool {
        match self {
            Res::F32(b) => f32::from_bits(b).is_nan(),
            Res::F64(b) => f64::from_bits(b).is_nan(),
            Res::Int(_) => false,
        }
    }
    fn bits(self) -> u64 {
        match self {
            Res::F32(b) => b as u64,
            Res::F64(b) | Res::Int(b) => b,
        }
    }
}

fn to_int(mode: char, x: f64) -> f64 {
    match mode {
        'n' => x.round_ties_even(),
        'p' => x.ceil(),
        'm' => x.floor(),
        'z' => x.trunc(),
        'a' => x.round(),
        _ => panic!("mode {mode}"),
    }
}

fn to_int32(mode: char, x: f32) -> f32 {
    match mode {
        'n' => x.round_ties_even(),
        'p' => x.ceil(),
        'm' => x.floor(),
        'z' => x.trunc(),
        'a' => x.round(),
        _ => panic!("mode {mode}"),
    }
}

fn cmp_code(o: Option<std::cmp::Ordering>) -> u64 {
    match o {
        Some(std::cmp::Ordering::Less) => 0,
        Some(std::cmp::Ordering::Equal) => 1,
        Some(std::cmp::Ordering::Greater) => 2,
        None => 3,
    }
}

/// Saturating casts of an integral float (`as` saturates and maps NaN to 0).
fn cast_int(it: &str, x: f64) -> u64 {
    match it {
        "i32" => x as i32 as u32 as u64,
        "u32" => x as u32 as u64,
        "i64" => x as i64 as u64,
        "u64" => x as u64,
        _ => panic!("{it}"),
    }
}

fn cast_int32(it: &str, x: f32) -> u64 {
    match it {
        "i32" => x as i32 as u32 as u64,
        "u32" => x as u32 as u64,
        "i64" => x as i64 as u64,
        "u64" => x as u64,
        _ => panic!("{it}"),
    }
}

fn from_int(it: &str, w: &str, x: u64) -> Res {
    let x = black_box(x);
    match (it, w) {
        ("i32", "32") => Res::F32((x as u32 as i32 as f32).to_bits()),
        ("u32", "32") => Res::F32((x as u32 as f32).to_bits()),
        ("i64", "32") => Res::F32((x as i64 as f32).to_bits()),
        ("u64", "32") => Res::F32((x as f32).to_bits()),
        ("i32", "64") => Res::F64((x as u32 as i32 as f64).to_bits()),
        ("u32", "64") => Res::F64((x as u32 as f64).to_bits()),
        ("i64", "64") => Res::F64((x as i64 as f64).to_bits()),
        ("u64", "64") => Res::F64((x as f64).to_bits()),
        _ => panic!("{it} {w}"),
    }
}

fn eval(class: &str, mode: char, a: u64, b: u64, c: u64) -> Res {
    let parts: Vec<&str> = class.split('.').collect();
    let (fa, fb, fc) = (f32::from_bits(a as u32), f32::from_bits(b as u32), f32::from_bits(c as u32));
    let (da, db, dc) = (f64::from_bits(a), f64::from_bits(b), f64::from_bits(c));
    match parts.as_slice() {
        ["add", "32"] => Res::F32(in_mode(mode, (fa, fb), |(x, y)| x + y).to_bits()),
        ["add", "64"] => Res::F64(in_mode(mode, (da, db), |(x, y)| x + y).to_bits()),
        ["sub", "32"] => Res::F32(in_mode(mode, (fa, fb), |(x, y)| x - y).to_bits()),
        ["sub", "64"] => Res::F64(in_mode(mode, (da, db), |(x, y)| x - y).to_bits()),
        ["mul", "32"] => Res::F32(in_mode(mode, (fa, fb), |(x, y)| x * y).to_bits()),
        ["mul", "64"] => Res::F64(in_mode(mode, (da, db), |(x, y)| x * y).to_bits()),
        ["div", "32"] => Res::F32(in_mode(mode, (fa, fb), |(x, y)| x / y).to_bits()),
        ["div", "64"] => Res::F64(in_mode(mode, (da, db), |(x, y)| x / y).to_bits()),
        ["sqrt", "32"] => Res::F32(in_mode(mode, fa, |x| x.sqrt()).to_bits()),
        ["sqrt", "64"] => Res::F64(in_mode(mode, da, |x| x.sqrt()).to_bits()),
        // Lean `mulAdd addend=c a b` = c + a * b
        ["fma", "32"] => Res::F32(in_mode(mode, (fa, fb, fc), |(x, y, z)| x.mul_add(y, z)).to_bits()),
        ["fma", "64"] => Res::F64(in_mode(mode, (da, db, dc), |(x, y, z)| x.mul_add(y, z)).to_bits()),
        ["cmp", "32"] => Res::Int(cmp_code(black_box(fa).partial_cmp(&black_box(fb)))),
        ["cmp", "64"] => Res::Int(cmp_code(black_box(da).partial_cmp(&black_box(db)))),
        ["rint", "32"] => Res::F32(to_int32(mode, black_box(fa)).to_bits()),
        ["rint", "64"] => Res::F64(to_int(mode, black_box(da)).to_bits()),
        ["cvt", "64", "32"] => Res::F32(in_mode(mode, da, |x| x as f32).to_bits()),
        ["cvt", "32", "64"] => Res::F64(in_mode(mode, fa, |x| x as f64).to_bits()),
        ["tofix", "32", it] => Res::Int(cast_int32(it, to_int32(mode, black_box(fa)))),
        ["tofix", "64", it] => Res::Int(cast_int(it, to_int(mode, black_box(da)))),
        ["fromfix", it, w] => from_int(it, w, a),
        _ => panic!("unknown class {class}"),
    }
}

#[derive(Default)]
struct Count {
    total: u64,
    nan: u64,
    mismatch: u64,
}

fn main() {
    let exact_nan = std::env::args().any(|a| a == "--exact-nan");
    let show: usize = std::env::var("FLOAT_ORACLE_SHOW").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let mut counts: BTreeMap<String, Count> = BTreeMap::new();
    let mut shown = 0;
    let stdin = std::io::stdin();
    for line in stdin.lock().lines() {
        let line = line.expect("read stdin");
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() != 6 {
            panic!("malformed line: {line}");
        }
        let hex = |s: &str| u64::from_str_radix(s, 16).expect("hex");
        let mode = f[1].chars().next().unwrap();
        let (a, b, c, lean) = (hex(f[2]), hex(f[3]), hex(f[4]), hex(f[5]));
        let host = eval(f[0], mode, a, b, c);
        let lean_res = match host {
            Res::F32(_) => Res::F32(lean as u32),
            Res::F64(_) => Res::F64(lean),
            Res::Int(_) => Res::Int(lean),
        };
        let cnt = counts.entry(f[0].to_string()).or_default();
        cnt.total += 1;
        let ok = if host.is_nan() && lean_res.is_nan() {
            cnt.nan += 1;
            !exact_nan || host == lean_res
        } else {
            host.bits() == lean_res.bits() && lean_res.bits() == lean
        };
        if !ok {
            cnt.mismatch += 1;
            if shown < show {
                shown += 1;
                eprintln!("MISMATCH {line}: host {:x}", host.bits());
            }
        }
    }
    let mut out = std::io::stdout().lock();
    let (mut total, mut bad) = (0, 0);
    for (class, c) in &counts {
        writeln!(out, "{class:<16} cases {:>8}  nan-results {:>7}  mismatches {}", c.total, c.nan, c.mismatch).unwrap();
        total += c.total;
        bad += c.mismatch;
    }
    writeln!(out, "TOTAL cases {total} mismatches {bad} ({})", if exact_nan { "NaNs bit-exact" } else { "NaNs: both NaN" }).unwrap();
    if bad > 0 {
        std::process::exit(1);
    }
}
