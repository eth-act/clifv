import FV.DSL

/-! Negative tests: programs outside the `flat def` fragment are rejected with readable errors,
and hand-written deep ASTs violating the affine/fragment rules fail `FlatFn.checkB`. -/

namespace DSLNegative

/-! ## Frontend rejections -/

/-- error: flat def: bare `+` on machine integers is rejected: write `+%` (wrapping) or `+?` (checked, throws) -/
#guard_msgs in
flat def badPlus (a : BitVec 64) : BitVec 64 := do
  return a + a

/-- error: flat def: bare `*` on machine integers is rejected: write `*%` (wrapping) or `*?` (checked, throws) -/
#guard_msgs in
flat def badMul (a : BitVec 8) : BitVec 8 := do
  let b := a * 2
  return b

/-- error: flat def: bare `/` is rejected: write `/?` (unsigned, throws .divByZero) -/
#guard_msgs in
flat def badDiv (a : BitVec 8) : BitVec 8 := do
  return a / 2

/-- error: flat def: affine rule: `xs` is used after it was moved; write `xs.clone` at the earlier use to keep it -/
#guard_msgs in
flat def affineMove (xs : Vector (BitVec 64) 4) : BitVec 64 := do
  let ys := xs
  let a := ys[0]!
  return a +? xs[1]!

/-- error: flat def: affine rule: `xs` is used after it was moved; write `xs.clone` at the earlier use to keep it -/
#guard_msgs in
flat def affineUpdateAlias (xs : Vector (BitVec 64) 4) : Vector (BitVec 64) 4 := do
  let mut ys := xs
  ys := ys.set! 0 1
  return xs

/-- error: flat def: affine rule: the loop body moves `xs`, which is bound outside the loop; use `xs.clone` -/
#guard_msgs in
flat def affineLoopMove (xs : Vector (BitVec 8) 4) : Vector (BitVec 8) 4 := do
  let mut ys := xs.clone
  for _ in [0:4] do
    let zs := xs
    ys := zs
  return ys

/-- error: flat def: `while`/`repeat` loops are not supported: only bounded `for i in [0:n]` loops (PLAN §3.1) -/
#guard_msgs in
flat def whileLoop (n : BitVec 64) : BitVec 64 := do
  let mut i : BitVec 64 := 0
  while i < n do
    i := i +% 1
  return i

/-- error: flat def: type mismatch: expected `BitVec 64`, got `Bool` -/
#guard_msgs in
flat def illTyped (a : BitVec 64) : BitVec 64 := do
  return a == a

/-- error: flat def: type mismatch: expected `BitVec 64`, got `BitVec 32` -/
#guard_msgs in
flat def mixedWidths (a : BitVec 64) (b : BitVec 32) : BitVec 64 := do
  return a +% b

/-- error: flat def: `return` inside a `for` loop is not supported -/
#guard_msgs in
flat def returnInLoop (xs : Vector (BitVec 8) 4) : BitVec 8 := do
  for i in [0:4] do
    return xs[i]!
  return 0

/-- error: flat def: unchecked indexing is not supported: write `xs[i]!` (throws .indexOutOfBounds) -/
#guard_msgs in
flat def uncheckedIndex (xs : Vector (BitVec 8) 4) (i : BitVec 64) : BitVec 8 := do
  return xs[i]

/-- error: flat def: loop bound must be a numeral -/
#guard_msgs in
flat def dynamicBound (n : BitVec 64) : BitVec 64 := do
  let mut acc : BitVec 64 := 0
  for i in [0:n] do
    acc := acc +% i
  return acc

/-- error: flat def: `a` is not mutable (declare it with `let mut`) -/
#guard_msgs in
flat def notMutable (a : BitVec 64) : BitVec 64 := do
  a := a +% 1
  return a

/-- error: flat def: `BitVec.ofNat` is not a `flat def` (no `BitVec.ofNat.ast`); only flat defs may be called -/
#guard_msgs in
flat def callsNonFlat (a : BitVec 64) : BitVec 64 := do
  return BitVec.ofNat 64 3

/-- error: flat def: machine integers are `BitVec n` (or `DSL.U8 … DSL.U64`), not `UInt64` -/
#guard_msgs in
flat def uintType (a : UInt64) : UInt64 := do
  return a

/-- error: flat def: literal 256 does not fit in `BitVec 8` -/
#guard_msgs in
flat def bigLiteral (a : BitVec 8) : BitVec 8 := do
  return a +% 256

/-! ## Checker rejections on hand-written deep ASTs -/

open _root_.DSL in
/-- The loop body updates a vector bound outside the loop: each iteration would see the
in-place update although `denote` restarts from the outer value. -/
def loopUpdatesOuter : FlatFn [.vec 4 .u8] .unit := ⟨"loopUpdatesOuter",
  .forRange 4 .unit (.vset (.succ (.succ .zero)) (.var (.succ .zero)) (.ilit .w8 0) (.ret .unit))⟩

open _root_.DSL in
/-- `bind s k` where `s` updates `xs` in place and `k` reads `xs` (semantically the old value). -/
def bindUpdateThenRead : FlatFn [.vec 4 .u8] .u8 := ⟨"bindUpdateThenRead",
  .bind (.vset .zero (.ilit .w8 0) (.ilit .w8 7) (.ret .unit))
    (.op (.vget (.succ .zero) (.ilit .w8 0)))⟩

open _root_.DSL in
/-- A move inside one branch of an `ite`, then a use after the join. -/
def moveInBranch : FlatFn [.vec 4 .u8, .bool] (.vec 4 .u8) := ⟨"moveInBranch",
  .bind (.ite (.var (.succ .zero)) (.let_ (.var .zero) (.ret .unit)) (.ret .unit))
    (.ret (.var (.succ .zero)))⟩

open _root_.DSL in
/-- `zext` to a narrower width. -/
def badCast : FlatFn [.u64] .u8 := ⟨"badCast", .ret (.cast .zext .w8 (.var .zero))⟩

open _root_.DSL in
/-- Map with vector keys is outside the fragment. -/
def badMapKey : FlatFn [.map (.vec 2 .u8) .u8] .unit := ⟨"badMapKey", .ret .unit⟩

open _root_.DSL in
/-- A callee that violates the affine rule makes the caller unchecked. -/
def badCaller : FlatFn [.vec 4 .u8, .bool] (.vec 4 .u8) := ⟨"badCaller",
  .call moveInBranch.name moveInBranch.body (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))⟩

#guard !loopUpdatesOuter.checkB
#guard !bindUpdateThenRead.checkB
#guard !moveInBranch.checkB
#guard !badCast.checkB
#guard !badMapKey.checkB
#guard !badCaller.checkB

/-- info: Except.error "bindUpdateThenRead: affine rule: read of variable #1 after it was moved (use `.clone` before the move)" -/
#guard_msgs in
#eval bindUpdateThenRead.check

/-- info: Except.error "loopUpdatesOuter: affine rule: loop body updates variable #2 bound outside the loop" -/
#guard_msgs in
#eval loopUpdatesOuter.check

theorem loopUpdatesOuter_unchecked : ¬ loopUpdatesOuter.checked := by decide

end DSLNegative
