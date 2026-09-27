import FV.DSL
import Corpus.Vectors

/-! Corpus additions owned by the emitter (M1): constructs the base corpus does not reach —
map clone/growth/results, calls passing the runtime context, result-buffer callees (success
and error), `u8` checked multiply/divide, signed comparisons, sign extension, `ashr`, pure
conditionals, bool vectors, nested vectors. Collected in `Corpus.emitTests` (not part of
`Corpus.all`; the emitter's drivers use `Corpus.all ++ Corpus.emitTests`). -/

namespace Corpus
open DSL

/-- Clone, overwrite and append; returns both maps. -/
flat def mapClone (k : BitVec 32) (v : BitVec 32) :
    DSL.Map (BitVec 32) (BitVec 32) × DSL.Map (BitVec 32) (BitVec 32) := do
  let mut m : DSL.Map (BitVec 32) (BitVec 32) := DSL.Map.empty
  m := m.insert 1 10
  m := m.insert 2 20
  let c := m.clone
  m := m.insert k v
  return (m, c)

/-- Ten inserts (the runtime's entry array grows twice), then checked sum of lookups. -/
flat def mapGrow (base : BitVec 64) (probe : BitVec 64) : BitVec 64 := do
  let mut m : DSL.Map (BitVec 64) (BitVec 64) := DSL.Map.empty
  for i in [0:10] do
    m := m.insert (i *% 3) (base +% i)
  let mut acc : BitVec 64 := 0
  for j in [0:10] do
    let x := m.get! (j *% 3)
    acc := acc +? x
  let y := m.get! probe
  return acc +? y

/-- A map parameter that is only passed through (no runtime context needed). -/
flat def passMap (m : DSL.Map (BitVec 8) Bool) (x : BitVec 8) : DSL.Map (BitVec 8) Bool × BitVec 8 := do
  return (m, x +% 1)

/-- Callee taking a map. -/
flat def countIn (m : DSL.Map (BitVec 8) Bool) (k : BitVec 8) : BitVec 8 := do
  if m.contains k then
    return 1
  else
    return 0

/-- Calls passing the runtime context, a cloned map and a moved map. -/
flat def useCallee (a : BitVec 8) (b : BitVec 8) : BitVec 8 := do
  let mut s : DSL.Map (BitVec 8) Bool := DSL.Map.empty
  s := s.insert a true
  let x ← countIn s.clone b
  let y ← countIn s a
  return x +% y

/-- A result-buffer function (tag + 8 values) that can throw. -/
flat def bumpAll (xs : Vector (BitVec 8) 8) : Vector (BitVec 8) 8 := do
  let mut ys := xs
  for i in [0:8] do
    ys := ys.set! i (ys[i]! +? 1)
  return ys

/-- Calls a result-buffer callee; its error propagates. -/
flat def bumpFirst (xs : Vector (BitVec 8) 8) : BitVec 8 := do
  let ys ← bumpAll xs
  let zs ← reverse8 ys
  return zs[7]! -% zs[0]!

/-- `u8` checked multiply, divide, remainder, subtract. -/
flat def arith8 (a : BitVec 8) (b : BitVec 8) : BitVec 8 := do
  let p := a *? b
  let q := p /? b
  let r := a %? 7
  let d := r -? q
  return d

/-- Signed comparisons, sign extension, `ashr`, pure `if`, a bool vector indexed by `u8`. -/
flat def signedMix (a : BitVec 16) (b : BitVec 16) (i : BitVec 8) : BitVec 32 × Bool := do
  let mut flags : Vector Bool 4 := Vector.replicate 4 false
  flags := flags.set! 1 (BitVec.slt a b)
  flags := flags.set! 2 (BitVec.sle b a && !(a == b))
  flags := flags.set! 3 true
  let f := flags[i]!
  let s := sext 32 a
  let t := (zext 32 b) >>> 1
  let r := ashr s 3
  let q := if f then r +% t else r ^^^ t
  return (q, f)

/-- Nested vectors, truncation, and a `u16` checked multiply. -/
flat def nested (m : Vector (Vector (BitVec 16) 2) 3) (r : BitVec 64) : BitVec 8 := do
  let row := m[r]!
  let x := row[0]!
  let y := row[1]!
  let p := x *? y
  return trunc 8 p

#guard mapClone 3 30 = .ok (⟨[(1, 10), (2, 20), (3, 30)]⟩, ⟨[(1, 10), (2, 20)]⟩)
#guard mapGrow 100 27 = .ok (1045 + 109)
#guard arith8 3 5 = .ok 0
#guard nested #v[#v[1, 2], #v[3, 4], #v[300, 300]] 1 = .ok 12

def emitTests : List DSL.TestCase := [
  .mk' mapClone.ast [((3, 30, ()), .ok (⟨[(1, 10), (2, 20), (3, 30)]⟩, ⟨[(1, 10), (2, 20)]⟩)),
    ((1, 11, ()), .ok (⟨[(1, 11), (2, 20)]⟩, ⟨[(1, 10), (2, 20)]⟩))],
  .mk' mapGrow.ast [((100, 27, ()), .ok 1154), ((100, 28, ()), .error .notFound),
    ((0xfffffffffffffff0, 0, ()), .error .overflow)],
  .mk' passMap.ast [((⟨[(4, true), (9, false)]⟩, 7, ()), .ok (⟨[(4, true), (9, false)]⟩, 8)),
    ((DSL.Map.empty, 255, ()), .ok (DSL.Map.empty, 0))],
  .mk' countIn.ast [((⟨[(4, true)]⟩, 4, ()), .ok 1), ((⟨[(4, true)]⟩, 5, ()), .ok 0)],
  .mk' useCallee.ast [((3, 3, ()), .ok 2), ((3, 4, ()), .ok 1)],
  .mk' bumpAll.ast [((#v[1, 2, 3, 4, 5, 6, 7, 8], ()), .ok #v[2, 3, 4, 5, 6, 7, 8, 9]),
    ((#v[1, 2, 3, 4, 5, 6, 7, 255], ()), .error .overflow)],
  .mk' bumpFirst.ast [((#v[1, 2, 3, 4, 5, 6, 7, 8], ()), .ok 0xf9),
    ((#v[255, 2, 3, 4, 5, 6, 7, 8], ()), .error .overflow)],
  .mk' arith8.ast [((3, 5, ()), .ok 0), ((10, 20, ()), .error .overflow),
    ((16, 16, ()), .error .overflow), ((0, 0, ()), .error .divByZero), ((7, 1, ()), .error .overflow)],
  .mk' signedMix.ast [((0xfff0, 5, 1, ()), .ok (0xfffffffe + 2, true)),
    ((5, 0xfff0, 2, ()), .ok (0 ^^^ 0x7ff8, true)), ((5, 5, 0, ()), .ok (0 ^^^ 2, false)),
    ((5, 5, 3, ()), .ok (0 + 2, true)), ((5, 5, 4, ()), .error .indexOutOfBounds)],
  .mk' nested.ast [((#v[#v[1, 2], #v[3, 4], #v[300, 300]], 1, ()), .ok 12),
    ((#v[#v[1, 2], #v[3, 4], #v[300, 300]], 2, ()), .error .overflow),
    ((#v[#v[1, 2], #v[3, 4], #v[300, 300]], 3, ()), .error .indexOutOfBounds)]
]

#guard emitTests.all DSL.TestCase.passes
#guard emitTests.all fun tc => tc.fn.checkB

end Corpus
