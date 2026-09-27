//! (e) Option / Result, `?`, combinators, unwrap/expect.
#![no_std]

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErr {
    Empty,
    BadDigit(u8),
    Overflow,
}

#[no_mangle]
pub fn digit(c: u8) -> Result<u32, ParseErr> {
    if c.is_ascii_digit() {
        Ok((c - b'0') as u32)
    } else {
        Err(ParseErr::BadDigit(c))
    }
}

#[no_mangle]
pub fn parse_u32(s: &[u8]) -> Result<u32, ParseErr> {
    if s.is_empty() {
        return Err(ParseErr::Empty);
    }
    let mut v: u32 = 0;
    for &c in s {
        let d = digit(c)?;
        v = v.checked_mul(10).ok_or(ParseErr::Overflow)?;
        v = v.checked_add(d).ok_or(ParseErr::Overflow)?;
    }
    Ok(v)
}

#[no_mangle]
pub fn first_two(s: &[u32]) -> Option<u32> {
    let a = s.first()?;
    let b = s.get(1)?;
    Some(a.wrapping_add(*b))
}

#[no_mangle]
pub fn opt_map(o: Option<u32>) -> u64 {
    o.map(|x| x as u64 * 2).unwrap_or(7)
}

#[no_mangle]
pub fn opt_and_then(a: Option<u8>, b: Option<u8>) -> Option<u16> {
    a.and_then(|x| b.map(|y| x as u16 * 256 + y as u16))
}

#[no_mangle]
pub fn res_map_err(r: Result<u32, u8>) -> Result<u32, ParseErr> {
    r.map_err(ParseErr::BadDigit)
}

#[no_mangle]
pub fn unwrap_it(o: Option<u32>) -> u32 {
    o.unwrap()
}

#[no_mangle]
pub fn expect_it(r: Result<u64, ParseErr>) -> u64 {
    r.expect("bad")
}

#[no_mangle]
pub fn res_is_ok(r: &Result<u32, ParseErr>) -> bool {
    r.is_ok()
}

#[no_mangle]
pub fn sum_results(s: &[u8]) -> Result<u32, ParseErr> {
    let mut t = 0u32;
    for &c in s {
        t = t.wrapping_add(digit(c)?);
    }
    Ok(t)
}

#[no_mangle]
pub fn opt_u64_zip(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    let (x, y) = a.zip(b)?;
    x.checked_sub(y)
}
