import FV.DSL

/-! Corpus: scalar arithmetic at all four widths (checked, wrapping, division, casts, bits). -/

namespace Corpus
open DSL

/-- u8 checked add: overflows above 255. -/
flat def addU8 (a : BitVec 8) (b : BitVec 8) : BitVec 8 := do
  return a +? b

/-- u16 checked multiply-accumulate. -/
flat def macU16 (a : BitVec 16) (b : BitVec 16) (c : BitVec 16) : BitVec 16 := do
  let p := a *? b
  return p +? c

/-- u32 absolute difference with a join-point `if`. -/
flat def absDiff (a : BitVec 32) (b : BitVec 32) : BitVec 32 := do
  let mut d : BitVec 32 := 0
  if a ≥ b then
    d := a -% b
  else
    d := b -% a
  return d

/-- u32 unsigned division and remainder; divisor zero throws `divByZero`. -/
flat def divMod (a : BitVec 32) (b : BitVec 32) : BitVec 32 × BitVec 32 := do
  let q := a /? b
  let r := a %? b
  return (q, r)

/-- Width changes: zero/sign extension and truncation. -/
flat def casts (x : BitVec 8) : BitVec 64 := do
  let y := zext 64 x
  let z := sext 32 x
  let w : BitVec 16 := trunc 16 z
  return y +% zext 64 w

/-- u16 bit manipulation: and/or/xor/not, shifts (amount mod 16), comparisons. -/
flat def bits16 (a : BitVec 16) (b : BitVec 16) : BitVec 16 := do
  let c := (a &&& b) ||| (a ^^^ ~~~b)
  let d := (c <<< 3) >>> 1
  let e := ashr d b
  if BitVec.slt a b && a != b then
    return e
  return d -% e

/-- u64 checked subtraction chain; underflow is `overflow`. -/
flat def sub3 (a : BitVec 64) (b : BitVec 64) (c : BitVec 64) : BitVec 64 := do
  let x := a -? b
  return x -? c

/-- Expression-level `if` (pure select), `||`, signed comparison. -/
flat def max3 (a : BitVec 16) (b : BitVec 16) (c : BitVec 16) : BitVec 16 := do
  let m := if a > b then a else b
  let n := if m > c || m == c then m else c
  if BitVec.sle n 0 then
    throw (.user 0)
  return n

/-- No parameters. -/
flat def answer : BitVec 64 := do
  return 42

-- shallow-side tests
#guard addU8 200 55 = .ok 255
#guard addU8 200 56 = .error .overflow
#guard macU16 300 200 5 = .ok 60005
#guard macU16 300 300 0 = .error .overflow
#guard macU16 255 257 1 = .error .overflow
#guard absDiff 3 10 = .ok 7
#guard absDiff 10 3 = .ok 7
#guard divMod 17 5 = .ok (3, 2)
#guard divMod 17 0 = .error .divByZero
#guard casts 0xff = .ok (0xff + 0xffff)
#guard casts 0x7f = .ok (0x7f + 0x7f)
#guard bits16 3 5 = .ok 0x03ff
#guard bits16 5 3 = .ok 0x6fe8
#guard bits16 0x8000 1 = .ok 0x3ffc
#guard sub3 10 3 7 = .ok 0
#guard sub3 10 3 8 = .error .overflow
#guard answer = .ok 42
#guard max3 1 5 3 = .ok 5
#guard max3 1 5 9 = .ok 9
#guard max3 0x8000 0x9000 0x8001 = .error (.user 0)

-- deep-side test vectors (checked against `denote` here; exported via `Corpus.all`)
def arithTests : List DSL.TestCase := [
  .mk' addU8.ast [((200, 55, ()), .ok 255), ((200, 56, ()), .error .overflow), ((0, 0, ()), .ok 0)],
  .mk' macU16.ast [((300, 200, 5, ()), .ok 60005), ((300, 300, 0, ()), .error .overflow),
    ((255, 257, 1, ()), .error .overflow), ((65535, 1, 1, ()), .error .overflow)],
  .mk' absDiff.ast [((3, 10, ()), .ok 7), ((10, 3, ()), .ok 7), ((0, 0xffffffff, ()), .ok 0xffffffff)],
  .mk' divMod.ast [((17, 5, ()), .ok (3, 2)), ((17, 0, ()), .error .divByZero),
    ((0xffffffff, 1, ()), .ok (0xffffffff, 0))],
  .mk' casts.ast [((0xff, ()), .ok (0xff + 0xffff)), ((0x7f, ()), .ok 0xfe), ((0, ()), .ok 0)],
  .mk' bits16.ast [((3, 5, ()), .ok 0x03ff), ((5, 3, ()), .ok 0x6fe8), ((0x8000, 1, ()), .ok 0x3ffc)],
  .mk' sub3.ast [((10, 3, 7, ()), .ok 0), ((10, 3, 8, ()), .error .overflow),
    ((0, 1, 0, ()), .error .overflow)],
  .mk' max3.ast [((1, 5, 3, ()), .ok 5), ((1, 5, 9, ()), .ok 9),
    ((0x8000, 0x9000, 0x8001, ()), .error (.user 0))],
  .mk' answer.ast [((), .ok 42)]
]

#guard arithTests.all DSL.TestCase.passes

end Corpus
