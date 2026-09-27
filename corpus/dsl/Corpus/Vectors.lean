import FV.DSL

/-! Corpus: loops over fixed-size vectors, checked get/set, in-place updates. -/

namespace Corpus
open DSL

/-- The PLAN.md example: u64 checked sum. -/
flat def sumChecked (xs : Vector (BitVec 64) 4) : BitVec 64 := do
  let mut acc : BitVec 64 := 0
  for i in [0:4] do
    acc := acc +? xs[i]!
  return acc

/-- u32 prefix sums, updating a vector in place. -/
flat def prefixSum (xs : Vector (BitVec 32) 4) : Vector (BitVec 32) 4 := do
  let mut ys := xs
  let mut acc : BitVec 32 := 0
  for i in [0:4] do
    acc := acc +? ys[i]!
    ys := ys.set! i acc
  return ys

/-- u16 minimum and maximum (two loop-carried variables, two join-point `if`s). -/
flat def minMax (xs : Vector (BitVec 16) 4) : BitVec 16 × BitVec 16 := do
  let mut lo : BitVec 16 := 65535
  let mut hi : BitVec 16 := 0
  for i in [0:4] do
    let x := xs[i]!
    if x < lo then
      lo := x
    if x > hi then
      hi := x
  return (lo, hi)

/-- u8 reversal into a fresh vector. -/
flat def reverse8 (xs : Vector (BitVec 8) 8) : Vector (BitVec 8) 8 := do
  let mut ys : Vector (BitVec 8) 8 := Vector.replicate 8 0
  for i in [0:8] do
    ys := ys.set! (7 -% i) xs[i]!
  return ys

/-- u64 dot product with checked multiply and add. -/
flat def dot (xs : Vector (BitVec 64) 4) (ys : Vector (BitVec 64) 4) : BitVec 64 := do
  let mut acc : BitVec 64 := 0
  for i in [0:4] do
    let p := xs[i]! *? ys[i]!
    acc := acc +? p
  return acc

/-- Index from the caller: out-of-range reads and writes throw `indexOutOfBounds`. -/
flat def swapAt (xs : Vector (BitVec 32) 4) (i : BitVec 32) (j : BitVec 32) : Vector (BitVec 32) 4 := do
  let mut ys := xs
  let a := ys[i]!
  let b := ys[j]!
  ys := ys.set! i b
  ys := ys.set! j a
  return ys

/-- Nested loops: 4×4 multiplication table sum, the inner loop carries the outer accumulator. -/
flat def tableSum (n : BitVec 64) : BitVec 64 := do
  let mut acc : BitVec 64 := 0
  for i in [0:4] do
    for j in [0:4] do
      let p := i *? j
      let q := p *? n
      acc := acc +? q
  return acc

/-- Explicit `.clone`: keep the original while updating a copy. -/
flat def bumpCopy (xs : Vector (BitVec 16) 2) : Vector (BitVec 16) 2 × Vector (BitVec 16) 2 := do
  let mut ys := xs.clone
  ys := ys.set! 0 (xs[0]! +? 1)
  return (xs, ys)

#guard sumChecked #v[1, 2, 3, 4] = .ok 10
#guard sumChecked #v[1, 2, 3, -1] = .error .overflow
#guard prefixSum #v[1, 2, 3, 4] = .ok #v[1, 3, 6, 10]
#guard prefixSum #v[0xffffffff, 0, 0, 1] = .error .overflow
#guard minMax #v[3, 9, 1, 4] = .ok (1, 9)
#guard reverse8 #v[1, 2, 3, 4, 5, 6, 7, 8] = .ok #v[8, 7, 6, 5, 4, 3, 2, 1]
#guard dot #v[1, 2, 3, 4] #v[5, 6, 7, 8] = .ok 70
#guard dot #v[0x100000000, 0, 0, 0] #v[0x100000000, 0, 0, 0] = .error .overflow
#guard swapAt #v[1, 2, 3, 4] 0 3 = .ok #v[4, 2, 3, 1]
#guard swapAt #v[1, 2, 3, 4] 0 4 = .error .indexOutOfBounds
#guard tableSum 1 = .ok 36
#guard tableSum 0x8000000000000000 = .error .overflow
#guard bumpCopy #v[1, 2] = .ok (#v[1, 2], #v[2, 2])
#guard bumpCopy #v[0xffff, 2] = .error .overflow

def vectorTests : List DSL.TestCase := [
  .mk' sumChecked.ast [((#v[1, 2, 3, 4], ()), .ok 10), ((#v[1, 2, 3, -1], ()), .error .overflow),
    ((#v[0, 0, 0, 0], ()), .ok 0)],
  .mk' prefixSum.ast [((#v[1, 2, 3, 4], ()), .ok #v[1, 3, 6, 10]),
    ((#v[0xffffffff, 0, 0, 1], ()), .error .overflow)],
  .mk' minMax.ast [((#v[3, 9, 1, 4], ()), .ok (1, 9)), ((#v[7, 7, 7, 7], ()), .ok (7, 7))],
  .mk' reverse8.ast [((#v[1, 2, 3, 4, 5, 6, 7, 8], ()), .ok #v[8, 7, 6, 5, 4, 3, 2, 1])],
  .mk' dot.ast [((#v[1, 2, 3, 4], #v[5, 6, 7, 8], ()), .ok 70),
    ((#v[0x100000000, 0, 0, 0], #v[0x100000000, 0, 0, 0], ()), .error .overflow)],
  .mk' swapAt.ast [((#v[1, 2, 3, 4], 0, 3, ()), .ok #v[4, 2, 3, 1]),
    ((#v[1, 2, 3, 4], 0, 4, ()), .error .indexOutOfBounds),
    ((#v[1, 2, 3, 4], 0xffffffff, 0, ()), .error .indexOutOfBounds)],
  .mk' tableSum.ast [((1, ()), .ok 36), ((0x8000000000000000, ()), .error .overflow)],
  .mk' bumpCopy.ast [((#v[1, 2], ()), .ok (#v[1, 2], #v[2, 2])), ((#v[0xffff, 2], ()), .error .overflow)]
]

#guard vectorTests.all DSL.TestCase.passes

end Corpus
