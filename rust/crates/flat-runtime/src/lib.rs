//! Map runtime for compiled DSL code: the externs of `docs/contracts/compile.md` §4, the
//! native counterpart of the CLIF runtime (`FV/Compile/Runtime.lean`, same algorithm and
//! layout) and of the Lean model `Compile.mapEnv` (the specification: `DSL.Map`, an
//! insertion-ordered association list; insert replaces in place or appends).
//!
//! `#![no_std]`, no global state: every extern takes the runtime context `ctx`, a pointer to
//! an arena provided by the caller (the test wrappers put it in a stack slot).
//!
//! Layout (all words `u64`, naturally aligned):
//! * arena at `ctx`: `used` (bytes in use, counted from `ctx`, header included) at `+0`,
//!   `cap` (arena bytes) at `+8`; bump allocation of multiples of 8 bytes, never freed;
//! * map object (24 bytes): `len`, `cap` (entries), `data` (pointer);
//! * `data`: `cap` entries of (key word, value word); the first `len` are live, in
//!   first-insertion order; a full array is reallocated at twice the capacity (initially 4).
//!
//! Keys and values are the DSL values zero-extended to 64 bits. Arena exhaustion is a
//! resource failure: the process stops with an undefined-instruction trap (the CLIF runtime
//! traps `user1`).
//!
//! Build for the native harness:
//! `cargo rustc --release --manifest-path rust/Cargo.toml -p flat-runtime
//!  --target aarch64-unknown-linux-musl --crate-type staticlib -- -C panic=abort`.

#![cfg_attr(not(test), no_std)]

use core::ptr::{read, write};

/// A map object (`h` points to one).
#[repr(C)]
pub struct MapObj {
    len: u64,
    cap: u64,
    data: *mut u64,
}

/// Arena exhausted: stop (the arena size is a resource precondition of the caller).
#[cold]
fn exhausted() -> ! {
    #[cfg(test)]
    panic!("flat-runtime: arena exhausted");
    #[cfg(all(not(test), target_arch = "aarch64"))]
    unsafe {
        core::arch::asm!("udf #1", options(noreturn))
    }
    #[cfg(all(not(test), target_arch = "x86_64"))]
    unsafe {
        core::arch::asm!("ud2", options(noreturn))
    }
    #[cfg(all(not(test), not(any(target_arch = "aarch64", target_arch = "x86_64"))))]
    loop {}
}

#[cfg(not(test))]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    exhausted()
}

/// Bump-allocate `n` bytes (a multiple of 8) from the arena at `ctx`.
unsafe fn alloc(ctx: *mut u8, n: u64) -> *mut u64 {
    unsafe {
        let hdr = ctx as *mut u64;
        let used = read(hdr);
        let cap = read(hdr.add(1));
        let end = match used.checked_add(n) {
            Some(e) if e <= cap => e,
            _ => exhausted(),
        };
        write(hdr, end);
        ctx.add(used as usize) as *mut u64
    }
}

/// Index of `k` among the live entries, or `len` if absent (first match).
unsafe fn find(h: *const MapObj, k: u64) -> u64 {
    unsafe {
        let m = &*h;
        let mut i = 0;
        while i < m.len {
            if read(m.data.add(2 * i as usize)) == k {
                return i;
            }
            i += 1;
        }
        m.len
    }
}

/// Copy `words` words from `src` to `dst`.
unsafe fn copy_words(dst: *mut u64, src: *const u64, words: u64) {
    unsafe {
        for j in 0..words as usize {
            write(dst.add(j), read(src.add(j)));
        }
    }
}

/// `int64_t flat_map_new(int64_t ctx)`: a new empty map.
///
/// # Safety
/// `ctx` points to an initialised arena.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_new(ctx: *mut u8) -> *mut MapObj {
    unsafe {
        let h = alloc(ctx, 24) as *mut MapObj;
        write(h, MapObj { len: 0, cap: 0, data: core::ptr::null_mut() });
        h
    }
}

/// `void flat_map_insert(int64_t ctx, int64_t h, uint64_t k, uint64_t v)`: replace the value
/// of `k` in place, or append `(k, v)`.
///
/// # Safety
/// `ctx` points to the arena `h` was allocated from; `h` is a live map.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_insert(ctx: *mut u8, h: *mut MapObj, k: u64, v: u64) {
    unsafe {
        let i = find(h, k);
        let m = &mut *h;
        if i < m.len {
            write(m.data.add(2 * i as usize + 1), v);
            return;
        }
        if m.len == m.cap {
            let cap = if m.cap == 0 { 4 } else { 2 * m.cap };
            let data = alloc(ctx, 16 * cap);
            copy_words(data, m.data, 2 * m.len);
            m.data = data;
            m.cap = cap;
        }
        let e = m.data.add(2 * m.len as usize);
        write(e, k);
        write(e.add(1), v);
        m.len += 1;
    }
}

/// `uint8_t flat_map_contains(int64_t ctx, int64_t h, uint64_t k)`.
///
/// # Safety
/// `h` is a live map.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_contains(_ctx: *mut u8, h: *const MapObj, k: u64) -> u8 {
    unsafe { (find(h, k) < (*h).len) as u8 }
}

/// `uint8_t flat_map_get(int64_t ctx, int64_t h, uint64_t k, uint64_t *out)`: 1 and `*out`
/// = value if present, else 0 (`*out` untouched).
///
/// # Safety
/// `h` is a live map, `out` is writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_get(_ctx: *mut u8, h: *const MapObj, k: u64, out: *mut u64) -> u8 {
    unsafe {
        let i = find(h, k);
        let m = &*h;
        if i < m.len {
            write(out, read(m.data.add(2 * i as usize + 1)));
            1
        } else {
            0
        }
    }
}

/// `int64_t flat_map_clone(int64_t ctx, int64_t h)`: an independent copy (capacity = length).
///
/// # Safety
/// `ctx` points to an initialised arena; `h` is a live map.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_clone(ctx: *mut u8, h: *const MapObj) -> *mut MapObj {
    unsafe {
        let m = &*h;
        let data = alloc(ctx, 16 * m.len);
        let c = alloc(ctx, 24) as *mut MapObj;
        write(c, MapObj { len: m.len, cap: m.len, data });
        copy_words(data, m.data, 2 * m.len);
        c
    }
}

/// `uint64_t flat_map_len(int64_t ctx, int64_t h)` (test harness).
///
/// # Safety
/// `h` is a live map.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_len(_ctx: *mut u8, h: *const MapObj) -> u64 {
    unsafe { (*h).len }
}

/// `void flat_map_entry(int64_t ctx, int64_t h, uint64_t i, uint64_t *k, uint64_t *v)`: entry
/// `i` in insertion order; `0, 0` if `i ≥ len` (test harness).
///
/// # Safety
/// `h` is a live map; `k`, `v` are writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn flat_map_entry(_ctx: *mut u8, h: *const MapObj, i: u64, k: *mut u64, v: *mut u64) {
    unsafe {
        let m = &*h;
        if i < m.len {
            write(k, read(m.data.add(2 * i as usize)));
            write(v, read(m.data.add(2 * i as usize + 1)));
        } else {
            write(k, 0);
            write(v, 0);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `DSL.Map` reference: insertion-ordered association list (`upsertL`, `lookupL`).
    #[derive(Clone, Default)]
    struct Model(Vec<(u64, u64)>);

    impl Model {
        fn insert(&mut self, k: u64, v: u64) {
            match self.0.iter_mut().find(|e| e.0 == k) {
                Some(e) => e.1 = v,
                None => self.0.push((k, v)),
            }
        }
        fn get(&self, k: u64) -> Option<u64> {
            self.0.iter().find(|e| e.0 == k).map(|e| e.1)
        }
    }

    struct Arena(Vec<u64>);

    impl Arena {
        fn new(bytes: u64) -> Arena {
            let mut a = vec![0u64; (bytes / 8) as usize];
            a[0] = 16;
            a[1] = bytes;
            Arena(a)
        }
        fn ctx(&mut self) -> *mut u8 {
            self.0.as_mut_ptr() as *mut u8
        }
    }

    unsafe fn entries(ctx: *mut u8, h: *const MapObj) -> Vec<(u64, u64)> {
        unsafe {
            let n = flat_map_len(ctx, h);
            (0..n)
                .map(|i| {
                    let (mut k, mut v) = (7, 7);
                    flat_map_entry(ctx, h, i, &mut k, &mut v);
                    (k, v)
                })
                .collect()
        }
    }

    /// Random insert/get/contains/clone sequences agree with the reference model, including
    /// entry order, growth past the initial capacity, clone independence, and the
    /// out-of-range `flat_map_entry` convention.
    #[test]
    fn agrees_with_dsl_map_model() {
        let mut arena = Arena::new(1 << 20);
        let ctx = arena.ctx();
        let mut seed: u64 = 0x9e3779b97f4a7c15;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        unsafe {
            let mut maps = vec![(flat_map_new(ctx), Model::default())];
            for _ in 0..4000 {
                let r = next();
                let which = (r % maps.len() as u64) as usize;
                let k = (r >> 8) % 23;
                match (r >> 16) % 5 {
                    0 | 1 => {
                        let v = r >> 20;
                        flat_map_insert(ctx, maps[which].0, k, v);
                        maps[which].1.insert(k, v);
                    }
                    2 => {
                        let mut out = 0xdead;
                        let found = flat_map_get(ctx, maps[which].0, k, &mut out);
                        match maps[which].1.get(k) {
                            Some(v) => assert_eq!((found, out), (1, v)),
                            None => assert_eq!((found, out), (0, 0xdead)),
                        }
                        assert_eq!(flat_map_contains(ctx, maps[which].0, k), found);
                    }
                    3 if maps.len() < 8 => {
                        let c = flat_map_clone(ctx, maps[which].0);
                        let m = maps[which].1.clone();
                        maps.push((c, m));
                    }
                    _ => {}
                }
                for (h, m) in &maps {
                    assert_eq!(entries(ctx, *h), m.0);
                }
            }
            let (h, m) = &maps[0];
            let (mut k, mut v) = (1, 1);
            flat_map_entry(ctx, *h, m.0.len() as u64, &mut k, &mut v);
            assert_eq!((k, v), (0, 0));
        }
    }

    #[test]
    #[should_panic(expected = "arena exhausted")]
    fn arena_exhaustion_stops() {
        // `alloc` directly: a panic cannot unwind out of the `extern "C"` functions.
        // 64-byte arena: 16 header + 24 map object = 40 used, so 32 more bytes do not fit.
        let mut arena = Arena::new(64);
        let ctx = arena.ctx();
        unsafe {
            let _ = flat_map_new(ctx);
            alloc(ctx, 32);
        }
    }
}
