import FV.DSL

/-! Corpus: error paths with distinct tags, early returns. -/

namespace Corpus
open DSL

/-- Division guarded by a user error (tag 56 + 7). -/
flat def safeDiv (a : BitVec 64) (b : BitVec 64) : BitVec 64 := do
  if b == 0 then
    throw (.user 7)
  return a /? b

/-- Validation with three distinct user errors and one built-in. -/
flat def validate (x : BitVec 32) (lo : BitVec 32) (hi : BitVec 32) : BitVec 32 := do
  if lo > hi then
    throw (.user 1)
  else if x < lo then
    throw (.user 2)
  else if x > hi then
    throw (.user 3)
  let span := hi -? lo
  let off := x -? lo
  if off == span then
    throw .overflow
  return off

/-- Linear search with early return; not found throws `notFound`. -/
flat def findIdx (xs : Vector (BitVec 8) 8) (key : BitVec 8) : BitVec 64 := do
  let mut found : Bool := false
  let mut idx : BitVec 64 := 0
  for i in [0:8] do
    if !found && xs[i]! == key then
      found := true
      idx := i
  if found then
    return idx
  throw .notFound

/-- Tail `if` with returns on both sides and a throw in a nested branch. -/
flat def classify (x : BitVec 16) : BitVec 8 := do
  if x == 0 then
    return 0
  else
    if x < 100 then
      return 1
    else if x < 1000 then
      return 2
    else
      throw (.user 199)

#guard safeDiv 7 0 = .error (.user 7)
#guard safeDiv 7 2 = .ok 3
#guard validate 5 1 9 = .ok 4
#guard validate 5 9 1 = .error (.user 1)
#guard validate 0 1 9 = .error (.user 2)
#guard validate 10 1 9 = .error (.user 3)
#guard validate 9 1 9 = .error .overflow
#guard findIdx #v[5, 6, 7, 8, 9, 10, 7, 12] 7 = .ok 2
#guard findIdx #v[5, 6, 7, 8, 9, 10, 7, 12] 1 = .error .notFound
#guard classify 0 = .ok 0
#guard classify 50 = .ok 1
#guard classify 500 = .ok 2
#guard classify 5000 = .error (.user 199)
-- distinct tags on the error-tag ABI
#guard [Err.user 1, .user 2, .user 3, .user 7, .user 199, .overflow, .notFound].map Err.tag
  = [57, 58, 59, 63, 255, 1, 4]

def errorTests : List DSL.TestCase := [
  .mk' safeDiv.ast [((7, 0, ()), .error (.user 7)), ((7, 2, ()), .ok 3)],
  .mk' validate.ast [((5, 1, 9, ()), .ok 4), ((5, 9, 1, ()), .error (.user 1)),
    ((0, 1, 9, ()), .error (.user 2)), ((10, 1, 9, ()), .error (.user 3)),
    ((9, 1, 9, ()), .error .overflow)],
  .mk' findIdx.ast [((#v[5, 6, 7, 8, 9, 10, 7, 12], 7, ()), .ok 2),
    ((#v[5, 6, 7, 8, 9, 10, 7, 12], 1, ()), .error .notFound)],
  .mk' classify.ast [((0, ()), .ok 0), ((50, ()), .ok 1), ((500, ()), .ok 2),
    ((5000, ()), .error (.user 199))]
]

#guard errorTests.all DSL.TestCase.passes

end Corpus
