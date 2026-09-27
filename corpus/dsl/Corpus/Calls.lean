import Corpus.Errors

/-! Corpus: calls between `flat def`s (nested, in loops, across modules, with contracts). -/

namespace Corpus
open DSL

flat def square (x : BitVec 32) : BitVec 32 := do
  return x *? x

/-- Calls `square` inside a loop. -/
flat def sumSquares (xs : Vector (BitVec 32) 4) : BitVec 32 := do
  let mut acc : BitVec 32 := 0
  for i in [0:4] do
    let s ← square xs[i]!
    acc := acc +? s
  return acc

/-- Three levels deep: `hypot2 → sumSquares → square`, plus a call across modules (`safeDiv`). -/
flat def meanSquare (xs : Vector (BitVec 32) 4) (n : BitVec 64) : BitVec 64 := do
  let s ← sumSquares xs
  return safeDiv (zext 64 s) n

/-- A function with a contract; it becomes `@[irreducible]` after its proofs. -/
flat def incr (x : BitVec 16) : BitVec 16
  requires x.toNat < 65535
  ensures r, r.toNat = x.toNat + 1
  := do
  return x +? 1
proof by
  intro x hx
  unfold incr
  exact ⟨x + 1, DSL.Ops.addC_ok (by simp; omega), by bv_omega⟩

/-- Calls the irreducible `incr`; `denote_eq` goes through `with_unfolding_all rfl`. -/
flat def incrTwice (x : BitVec 16) : BitVec 16 := do
  let y ← incr x
  return incr y

/-- A call whose result is a vector (moved out of the callee). -/
flat def squares (xs : Vector (BitVec 32) 4) : Vector (BitVec 32) 4 := do
  let mut ys := xs
  for i in [0:4] do
    ys := ys.set! i (square ys[i]!)
  return ys

#guard square 3 = .ok 9
#guard square 0x10000 = .error .overflow
#guard sumSquares #v[1, 2, 3, 4] = .ok 30
#guard sumSquares #v[1, 2, 3, 0x10000] = .error .overflow
#guard meanSquare #v[1, 2, 3, 4] 3 = .ok 10
#guard meanSquare #v[1, 2, 3, 4] 0 = .error (.user 7)
#guard incr 1 = .ok 2
#guard incrTwice 1 = .ok 3
#guard incrTwice 0xfffe = .error .overflow
#guard squares #v[1, 2, 3, 4] = .ok #v[1, 4, 9, 16]
#guard squares #v[1, 2, 0x10000, 4] = .error .overflow

def callTests : List DSL.TestCase := [
  .mk' square.ast [((3, ()), .ok 9), ((0x10000, ()), .error .overflow), ((0xffff, ()), .ok 0xfffe0001)],
  .mk' sumSquares.ast [((#v[1, 2, 3, 4], ()), .ok 30), ((#v[1, 2, 3, 0x10000], ()), .error .overflow)],
  .mk' meanSquare.ast [((#v[1, 2, 3, 4], 3, ()), .ok 10), ((#v[1, 2, 3, 4], 0, ()), .error (.user 7))],
  .mk' incr.ast [((1, ()), .ok 2), ((0xffff, ()), .error .overflow)],
  .mk' incrTwice.ast [((1, ()), .ok 3), ((0xfffe, ()), .error .overflow)],
  .mk' squares.ast [((#v[1, 2, 3, 4], ()), .ok #v[1, 4, 9, 16]),
    ((#v[1, 2, 0x10000, 4], ()), .error .overflow)]
]

#guard callTests.all DSL.TestCase.passes

end Corpus
