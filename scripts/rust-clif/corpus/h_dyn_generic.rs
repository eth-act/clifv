//! (h) generics (monomorphised), trait objects (`dyn` → vtable call_indirect),
//! function pointers and closures.
#![no_std]

pub trait Hasher {
    fn write(&mut self, x: u32);
    fn finish(&self) -> u32;
}

pub struct Fnv(pub u32);
pub struct Xor(pub u32);

impl Hasher for Fnv {
    fn write(&mut self, x: u32) {
        self.0 = (self.0 ^ x).wrapping_mul(16777619);
    }
    fn finish(&self) -> u32 {
        self.0
    }
}

impl Hasher for Xor {
    fn write(&mut self, x: u32) {
        self.0 ^= x.rotate_left(5);
    }
    fn finish(&self) -> u32 {
        self.0
    }
}

pub fn hash_all<H: Hasher>(h: &mut H, xs: &[u32]) -> u32 {
    for &x in xs {
        h.write(x);
    }
    h.finish()
}

#[no_mangle]
pub fn generic_fnv(xs: &[u32]) -> u32 {
    hash_all(&mut Fnv(2166136261), xs)
}

#[no_mangle]
pub fn generic_xor(xs: &[u32]) -> u32 {
    hash_all(&mut Xor(0), xs)
}

#[no_mangle]
pub fn dyn_hash(h: &mut dyn Hasher, xs: &[u32]) -> u32 {
    for &x in xs {
        h.write(x);
    }
    h.finish()
}

#[no_mangle]
pub fn dyn_pick(which: bool, xs: &[u32]) -> u32 {
    let mut a = Fnv(1);
    let mut b = Xor(1);
    let h: &mut dyn Hasher = if which { &mut a } else { &mut b };
    dyn_hash(h, xs)
}

#[no_mangle]
pub fn fn_ptr(f: fn(u32) -> u32, x: u32) -> u32 {
    f(f(x))
}

fn double(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[no_mangle]
pub fn fn_ptr_table(i: usize, x: u32) -> u32 {
    let table: [fn(u32) -> u32; 2] = [double, |y| y ^ 0xff];
    table[i & 1](x)
}

#[no_mangle]
pub fn closure_dyn(f: &dyn Fn(u64) -> u64, x: u64) -> u64 {
    f(x).wrapping_add(1)
}

pub fn apply_twice<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
    f(f(x))
}

#[no_mangle]
pub fn closure_generic(k: u64, x: u64) -> u64 {
    apply_twice(|y| y.wrapping_mul(k), x)
}

pub trait Area {
    fn area(&self) -> u64;
}
impl Area for (u32, u32) {
    fn area(&self) -> u64 {
        self.0 as u64 * self.1 as u64
    }
}
impl Area for u32 {
    fn area(&self) -> u64 {
        (*self as u64) * (*self as u64)
    }
}

#[no_mangle]
pub fn total_area(xs: &[&dyn Area]) -> u64 {
    xs.iter().map(|a| a.area()).fold(0, u64::wrapping_add)
}
