//! Litmus tests of the instructions Cranelift emits for CLIF atomics (T2c, #301), run natively
//! (aarch64, normally under qemu-aarch64-static). Each test runs many times; every observed outcome
//! must be allowed by the Armv8 model of `FV/Concurrency/Armv8.lean`. The forbidden outcomes
//! below are exactly those proven inconsistent in `FVTest/Concurrency/Litmus.lean` (herd7's
//! `aarch64.cat` verdicts). qemu is not weak-memory faithful, so a missing allowed outcome is not
//! an error; an observed forbidden one is.
//!
//! Usage: litmus [iterations]   (exit 1 if a forbidden outcome was observed)

use std::arch::asm;
use std::cell::UnsafeCell;
use std::collections::BTreeMap;
use std::hint::spin_loop;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[repr(align(128))]
struct Loc(UnsafeCell<u64>);

struct Mem {
    x: Loc,
    y: Loc,
}

unsafe impl Sync for Mem {}

impl Mem {
    fn x(&self) -> *mut u64 {
        self.x.0.get()
    }
    fn y(&self) -> *mut u64 {
        self.y.0.get()
    }
}

/// A sense-reversing spin barrier (the harness's own synchronisation, not under test).
struct Barrier {
    n: usize,
    count: AtomicUsize,
    gen: AtomicUsize,
}

impl Barrier {
    fn wait(&self) {
        let g = self.gen.load(Ordering::Acquire);
        if self.count.fetch_add(1, Ordering::AcqRel) + 1 == self.n {
            self.count.store(0, Ordering::Relaxed);
            self.gen.fetch_add(1, Ordering::Release);
        } else {
            while self.gen.load(Ordering::Acquire) == g {
                spin_loop();
            }
        }
    }
}

type Thread = fn(&Mem, usize) -> Vec<u64>;

struct Test {
    name: &'static str,
    /// The Lean theorem(s) giving the verdict of the forbidden outcomes.
    lean: &'static str,
    threads: Vec<Thread>,
    /// Append the final values of x and y to the outcome.
    finals: bool,
    forbidden: Vec<Vec<u64>>,
}

// --- thread bodies: the exact instructions Cranelift emits ---

fn st_x_st_y(m: &Mem, _: usize) -> Vec<u64> {
    unsafe { asm!("str {v}, [{x}]", "str {v}, [{y}]", v = in(reg) 1u64, x = in(reg) m.x(), y = in(reg) m.y()) };
    vec![]
}
fn st_x_stlr_y(m: &Mem, _: usize) -> Vec<u64> {
    unsafe { asm!("str {v}, [{x}]", "stlr {v}, [{y}]", v = in(reg) 1u64, x = in(reg) m.x(), y = in(reg) m.y()) };
    vec![]
}
fn st_x_dmb_st_y(m: &Mem, _: usize) -> Vec<u64> {
    unsafe {
        asm!("str {v}, [{x}]", "dmb ish", "str {v}, [{y}]", v = in(reg) 1u64, x = in(reg) m.x(), y = in(reg) m.y())
    };
    vec![]
}
fn ldar_y_ld_x(m: &Mem, _: usize) -> Vec<u64> {
    let (a, b): (u64, u64);
    unsafe { asm!("ldar {a}, [{y}]", "ldr {b}, [{x}]", a = out(reg) a, b = out(reg) b, x = in(reg) m.x(), y = in(reg) m.y()) };
    vec![a, b]
}
fn ld_y_ld_x(m: &Mem, _: usize) -> Vec<u64> {
    let (a, b): (u64, u64);
    unsafe { asm!("ldr {a}, [{y}]", "ldr {b}, [{x}]", a = out(reg) a, b = out(reg) b, x = in(reg) m.x(), y = in(reg) m.y()) };
    vec![a, b]
}
fn ld_y_dmb_ld_x(m: &Mem, _: usize) -> Vec<u64> {
    let (a, b): (u64, u64);
    unsafe {
        asm!("ldr {a}, [{y}]", "dmb ish", "ldr {b}, [{x}]", a = out(reg) a, b = out(reg) b, x = in(reg) m.x(), y = in(reg) m.y())
    };
    vec![a, b]
}
fn sb_la(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let r: u64;
    unsafe { asm!("stlr {v}, [{p}]", "ldar {r}, [{q}]", v = in(reg) 1u64, r = out(reg) r, p = in(reg) p, q = in(reg) q) };
    vec![r]
}
fn sb_plain(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let r: u64;
    unsafe { asm!("str {v}, [{p}]", "ldr {r}, [{q}]", v = in(reg) 1u64, r = out(reg) r, p = in(reg) p, q = in(reg) q) };
    vec![r]
}
fn sb_dmb(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let r: u64;
    unsafe {
        asm!("str {v}, [{p}]", "dmb ish", "ldr {r}, [{q}]", v = in(reg) 1u64, r = out(reg) r, p = in(reg) p, q = in(reg) q)
    };
    vec![r]
}
fn lb_al(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let r: u64;
    unsafe { asm!("ldar {r}, [{p}]", "stlr {v}, [{q}]", v = in(reg) 1u64, r = out(reg) r, p = in(reg) p, q = in(reg) q) };
    vec![r]
}
fn lb_plain(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let r: u64;
    unsafe { asm!("ldr {r}, [{p}]", "str {v}, [{q}]", v = in(reg) 1u64, r = out(reg) r, p = in(reg) p, q = in(reg) q) };
    vec![r]
}
fn w22_rel(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    unsafe { asm!("stlr {a}, [{p}]", "stlr {b}, [{q}]", a = in(reg) 1u64, b = in(reg) 2u64, p = in(reg) p, q = in(reg) q) };
    vec![]
}
fn w22_plain(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 0 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    unsafe { asm!("str {a}, [{p}]", "str {b}, [{q}]", a = in(reg) 1u64, b = in(reg) 2u64, p = in(reg) p, q = in(reg) q) };
    vec![]
}
fn iriw_w_rel(m: &Mem, t: usize) -> Vec<u64> {
    let p = if t == 0 { m.x() } else { m.y() };
    unsafe { asm!("stlr {v}, [{p}]", v = in(reg) 1u64, p = in(reg) p) };
    vec![]
}
fn iriw_w_plain(m: &Mem, t: usize) -> Vec<u64> {
    let p = if t == 0 { m.x() } else { m.y() };
    unsafe { asm!("str {v}, [{p}]", v = in(reg) 1u64, p = in(reg) p) };
    vec![]
}
fn iriw_r_acq(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 2 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let (a, b): (u64, u64);
    unsafe { asm!("ldar {a}, [{p}]", "ldar {b}, [{q}]", a = out(reg) a, b = out(reg) b, p = in(reg) p, q = in(reg) q) };
    vec![a, b]
}
fn iriw_r_plain(m: &Mem, t: usize) -> Vec<u64> {
    let (p, q) = if t == 2 { (m.x(), m.y()) } else { (m.y(), m.x()) };
    let (a, b): (u64, u64);
    unsafe { asm!("ldr {a}, [{p}]", "ldr {b}, [{q}]", a = out(reg) a, b = out(reg) b, p = in(reg) p, q = in(reg) q) };
    vec![a, b]
}
fn st_x(m: &Mem, _: usize) -> Vec<u64> {
    unsafe { asm!("str {v}, [{x}]", v = in(reg) 1u64, x = in(reg) m.x()) };
    vec![]
}
fn ld_x_ld_x(m: &Mem, _: usize) -> Vec<u64> {
    let (a, b): (u64, u64);
    unsafe { asm!("ldr {a}, [{x}]", "ldr {b}, [{x}]", a = out(reg) a, b = out(reg) b, x = in(reg) m.x()) };
    vec![a, b]
}
/// `atomic_rmw add` (Cranelift's `AtomicRMWLoop`): returns the old value.
fn rmw_add(m: &Mem, _: usize) -> Vec<u64> {
    let old: u64;
    unsafe {
        asm!(
            "2: ldaxr {old}, [{x}]",
            "add {new}, {old}, {one}",
            "stlxr {st:w}, {new}, [{x}]",
            "cbnz {st:w}, 2b",
            old = out(reg) old, new = out(reg) _, st = out(reg) _, one = in(reg) 1u64, x = in(reg) m.x()
        )
    };
    vec![old]
}
/// `atomic_cas x, 0, t + 1` (Cranelift's `AtomicCASLoop`): returns the old value.
fn cas0(m: &Mem, t: usize) -> Vec<u64> {
    let old: u64;
    unsafe {
        asm!(
            "2: ldaxr {old}, [{x}]",
            "cmp {old}, {e}",
            "b.ne 3f",
            "stlxr {st:w}, {new}, [{x}]",
            "cbnz {st:w}, 2b",
            "3:",
            old = out(reg) old, st = out(reg) _, e = in(reg) 0u64, new = in(reg) (t as u64 + 1), x = in(reg) m.x()
        )
    };
    vec![old]
}

fn tests() -> Vec<Test> {
    vec![
        Test { name: "MP+rel+acq", lean: "mp_rel_acq", threads: vec![st_x_stlr_y, ldar_y_ld_x], finals: false, forbidden: vec![vec![1, 0]] },
        Test { name: "MP", lean: "mp_plain (allowed)", threads: vec![st_x_st_y, ld_y_ld_x], finals: false, forbidden: vec![] },
        Test { name: "MP+rel", lean: "mp_rel (allowed)", threads: vec![st_x_stlr_y, ld_y_ld_x], finals: false, forbidden: vec![] },
        Test { name: "MP+dmbs", lean: "mp_dmbs", threads: vec![st_x_dmb_st_y, ld_y_dmb_ld_x], finals: false, forbidden: vec![vec![1, 0]] },
        Test { name: "SB+rel+acq", lean: "sb_rel_acq", threads: vec![sb_la, sb_la], finals: false, forbidden: vec![vec![0, 0]] },
        Test { name: "SB", lean: "sb_plain (allowed)", threads: vec![sb_plain, sb_plain], finals: false, forbidden: vec![] },
        Test { name: "SB+dmbs", lean: "sb_dmbs", threads: vec![sb_dmb, sb_dmb], finals: false, forbidden: vec![vec![0, 0]] },
        Test { name: "LB+acq+rel", lean: "lb_acq_rel", threads: vec![lb_al, lb_al], finals: false, forbidden: vec![vec![1, 1]] },
        Test { name: "LB", lean: "lb_plain (allowed)", threads: vec![lb_plain, lb_plain], finals: false, forbidden: vec![] },
        Test { name: "2+2W+rels", lean: "w22_rels", threads: vec![w22_rel, w22_rel], finals: true, forbidden: vec![vec![1, 1]] },
        Test { name: "2+2W", lean: "w22_plain (allowed)", threads: vec![w22_plain, w22_plain], finals: true, forbidden: vec![] },
        Test {
            name: "IRIW+acqs",
            lean: "iriw_acqs",
            threads: vec![iriw_w_rel, iriw_w_rel, iriw_r_acq, iriw_r_acq],
            finals: false,
            forbidden: vec![vec![1, 0, 1, 0]],
        },
        Test {
            name: "IRIW",
            lean: "iriw_plain (allowed)",
            threads: vec![iriw_w_plain, iriw_w_plain, iriw_r_plain, iriw_r_plain],
            finals: false,
            forbidden: vec![],
        },
        Test { name: "CoRR", lean: "corr", threads: vec![st_x, ld_x_ld_x], finals: false, forbidden: vec![vec![1, 0]] },
        Test { name: "ATOM-INC", lean: "inc_both0_a, inc_both0_b", threads: vec![rmw_add, rmw_add], finals: false, forbidden: vec![vec![0, 0]] },
        Test { name: "ATOM-CAS", lean: "inc_both0_a, inc_both0_b (same graph)", threads: vec![cas0, cas0], finals: false, forbidden: vec![vec![0, 0]] },
    ]
}

fn run(t: &Test, iters: usize) -> BTreeMap<Vec<u64>, usize> {
    let mem = Arc::new(Mem { x: Loc(UnsafeCell::new(0)), y: Loc(UnsafeCell::new(0)) });
    let n = t.threads.len();
    let bar = Arc::new(Barrier { n: n + 1, count: AtomicUsize::new(0), gen: AtomicUsize::new(0) });
    let results: Arc<Vec<UnsafeCell<Vec<u64>>>> = Arc::new((0..n).map(|_| UnsafeCell::new(vec![])).collect());
    struct Res(Arc<Vec<UnsafeCell<Vec<u64>>>>);
    unsafe impl Send for Res {}
    let mut handles = vec![];
    for (i, f) in t.threads.iter().enumerate() {
        let (mem, bar, f) = (mem.clone(), bar.clone(), *f);
        let res = Res(results.clone());
        handles.push(std::thread::spawn(move || {
            let res = res;
            for _ in 0..iters {
                bar.wait();
                let r = f(&mem, i);
                unsafe { *res.0[i].get() = r };
                bar.wait();
            }
        }));
    }
    let mut hist = BTreeMap::new();
    for _ in 0..iters {
        unsafe {
            *mem.x() = 0;
            *mem.y() = 0;
        }
        bar.wait();
        bar.wait();
        let mut out: Vec<u64> = vec![];
        for i in 0..n {
            out.extend(unsafe { (*results[i].get()).iter().copied() });
        }
        if t.finals {
            unsafe {
                out.push(*mem.x());
                out.push(*mem.y());
            }
        }
        *hist.entry(out).or_insert(0) += 1;
    }
    for h in handles {
        h.join().unwrap();
    }
    hist
}

fn main() {
    let iters: usize = std::env::args().nth(1).map(|s| s.parse().expect("iterations")).unwrap_or(20000);
    let mut bad = 0;
    for t in tests() {
        let hist = run(&t, iters);
        let seen_forbidden: Vec<_> = hist.keys().filter(|k| t.forbidden.contains(k)).collect();
        let status = if seen_forbidden.is_empty() { "ok" } else { "FORBIDDEN OBSERVED" };
        let outs: Vec<String> = hist.iter().map(|(k, v)| format!("{k:?}:{v}")).collect();
        println!("{:<11} {:<19} {}  [{}]", t.name, status, outs.join(" "), t.lean);
        if !seen_forbidden.is_empty() {
            bad += 1;
        }
    }
    println!("litmus: {} tests, {} with a forbidden outcome observed, {} iterations each", tests().len(), bad, iters);
    if bad > 0 {
        std::process::exit(1);
    }
}
