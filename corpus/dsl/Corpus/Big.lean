import FV.DSL

/-! Corpus: the largest function — the ChaCha20 block function (RFC 7539 §2.3),
16 loop-carried `u32` variables, 80 quarter-round steps per iteration. Used to measure
`denote_eq` elaboration time. -/

namespace Corpus
open DSL

set_option flat_def.timing true in
/-- ChaCha20 block function: 10 double rounds, then add the input state. -/
flat def chacha20Block (s : Vector (BitVec 32) 16) : Vector (BitVec 32) 16 := do
  let mut x0 := s[0]!
  let mut x1 := s[1]!
  let mut x2 := s[2]!
  let mut x3 := s[3]!
  let mut x4 := s[4]!
  let mut x5 := s[5]!
  let mut x6 := s[6]!
  let mut x7 := s[7]!
  let mut x8 := s[8]!
  let mut x9 := s[9]!
  let mut x10 := s[10]!
  let mut x11 := s[11]!
  let mut x12 := s[12]!
  let mut x13 := s[13]!
  let mut x14 := s[14]!
  let mut x15 := s[15]!
  for _ in [0:10] do
    x0 := x0 +% x4
    x12 := x12 ^^^ x0
    x12 := (x12 <<< 16) ||| (x12 >>> 16)
    x8 := x8 +% x12
    x4 := x4 ^^^ x8
    x4 := (x4 <<< 12) ||| (x4 >>> 20)
    x0 := x0 +% x4
    x12 := x12 ^^^ x0
    x12 := (x12 <<< 8) ||| (x12 >>> 24)
    x8 := x8 +% x12
    x4 := x4 ^^^ x8
    x4 := (x4 <<< 7) ||| (x4 >>> 25)
    x1 := x1 +% x5
    x13 := x13 ^^^ x1
    x13 := (x13 <<< 16) ||| (x13 >>> 16)
    x9 := x9 +% x13
    x5 := x5 ^^^ x9
    x5 := (x5 <<< 12) ||| (x5 >>> 20)
    x1 := x1 +% x5
    x13 := x13 ^^^ x1
    x13 := (x13 <<< 8) ||| (x13 >>> 24)
    x9 := x9 +% x13
    x5 := x5 ^^^ x9
    x5 := (x5 <<< 7) ||| (x5 >>> 25)
    x2 := x2 +% x6
    x14 := x14 ^^^ x2
    x14 := (x14 <<< 16) ||| (x14 >>> 16)
    x10 := x10 +% x14
    x6 := x6 ^^^ x10
    x6 := (x6 <<< 12) ||| (x6 >>> 20)
    x2 := x2 +% x6
    x14 := x14 ^^^ x2
    x14 := (x14 <<< 8) ||| (x14 >>> 24)
    x10 := x10 +% x14
    x6 := x6 ^^^ x10
    x6 := (x6 <<< 7) ||| (x6 >>> 25)
    x3 := x3 +% x7
    x15 := x15 ^^^ x3
    x15 := (x15 <<< 16) ||| (x15 >>> 16)
    x11 := x11 +% x15
    x7 := x7 ^^^ x11
    x7 := (x7 <<< 12) ||| (x7 >>> 20)
    x3 := x3 +% x7
    x15 := x15 ^^^ x3
    x15 := (x15 <<< 8) ||| (x15 >>> 24)
    x11 := x11 +% x15
    x7 := x7 ^^^ x11
    x7 := (x7 <<< 7) ||| (x7 >>> 25)
    x0 := x0 +% x5
    x15 := x15 ^^^ x0
    x15 := (x15 <<< 16) ||| (x15 >>> 16)
    x10 := x10 +% x15
    x5 := x5 ^^^ x10
    x5 := (x5 <<< 12) ||| (x5 >>> 20)
    x0 := x0 +% x5
    x15 := x15 ^^^ x0
    x15 := (x15 <<< 8) ||| (x15 >>> 24)
    x10 := x10 +% x15
    x5 := x5 ^^^ x10
    x5 := (x5 <<< 7) ||| (x5 >>> 25)
    x1 := x1 +% x6
    x12 := x12 ^^^ x1
    x12 := (x12 <<< 16) ||| (x12 >>> 16)
    x11 := x11 +% x12
    x6 := x6 ^^^ x11
    x6 := (x6 <<< 12) ||| (x6 >>> 20)
    x1 := x1 +% x6
    x12 := x12 ^^^ x1
    x12 := (x12 <<< 8) ||| (x12 >>> 24)
    x11 := x11 +% x12
    x6 := x6 ^^^ x11
    x6 := (x6 <<< 7) ||| (x6 >>> 25)
    x2 := x2 +% x7
    x13 := x13 ^^^ x2
    x13 := (x13 <<< 16) ||| (x13 >>> 16)
    x8 := x8 +% x13
    x7 := x7 ^^^ x8
    x7 := (x7 <<< 12) ||| (x7 >>> 20)
    x2 := x2 +% x7
    x13 := x13 ^^^ x2
    x13 := (x13 <<< 8) ||| (x13 >>> 24)
    x8 := x8 +% x13
    x7 := x7 ^^^ x8
    x7 := (x7 <<< 7) ||| (x7 >>> 25)
    x3 := x3 +% x4
    x14 := x14 ^^^ x3
    x14 := (x14 <<< 16) ||| (x14 >>> 16)
    x9 := x9 +% x14
    x4 := x4 ^^^ x9
    x4 := (x4 <<< 12) ||| (x4 >>> 20)
    x3 := x3 +% x4
    x14 := x14 ^^^ x3
    x14 := (x14 <<< 8) ||| (x14 >>> 24)
    x9 := x9 +% x14
    x4 := x4 ^^^ x9
    x4 := (x4 <<< 7) ||| (x4 >>> 25)
  let mut out := s.clone
  out := out.set! 0 (x0 +% s[0]!)
  out := out.set! 1 (x1 +% s[1]!)
  out := out.set! 2 (x2 +% s[2]!)
  out := out.set! 3 (x3 +% s[3]!)
  out := out.set! 4 (x4 +% s[4]!)
  out := out.set! 5 (x5 +% s[5]!)
  out := out.set! 6 (x6 +% s[6]!)
  out := out.set! 7 (x7 +% s[7]!)
  out := out.set! 8 (x8 +% s[8]!)
  out := out.set! 9 (x9 +% s[9]!)
  out := out.set! 10 (x10 +% s[10]!)
  out := out.set! 11 (x11 +% s[11]!)
  out := out.set! 12 (x12 +% s[12]!)
  out := out.set! 13 (x13 +% s[13]!)
  out := out.set! 14 (x14 +% s[14]!)
  out := out.set! 15 (x15 +% s[15]!)
  return out

/-- RFC 7539 §2.3.2 test vector. -/
def chachaIn : Vector (BitVec 32) 16 :=
  #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000, 0x4a000000, 0x00000000]
def chachaOut : Vector (BitVec 32) 16 :=
  #v[0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3, 0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3, 0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9, 0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2]

#guard chacha20Block chachaIn = .ok chachaOut
#guard DSL.denote chacha20Block.ast (chachaIn, ()) = .ok chachaOut

def bigTests : List DSL.TestCase := [
  .mk' chacha20Block.ast [((chachaIn, ()), .ok chachaOut)]
]

#guard bigTests.all DSL.TestCase.passes

end Corpus
