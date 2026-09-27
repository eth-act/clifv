import FV.DSL

/-! Corpus: the abstract map collection (runtime externs). -/

namespace Corpus
open DSL

/-- Histogram of byte values (u8 keys, u32 counts). -/
flat def histogram (xs : Vector (BitVec 8) 8) (probe : BitVec 8) : BitVec 32 := do
  let mut m : DSL.Map (BitVec 8) (BitVec 32) := DSL.Map.empty
  for i in [0:8] do
    let x := xs[i]!
    if m.contains x then
      let c := m.get! x
      m := m.insert x (c +? 1)
    else
      m := m.insert x 1
  return m.get! probe

/-- Lookup table built from parameters; a missing key throws `notFound`. -/
flat def lookup (k : BitVec 32) (a : BitVec 64) (b : BitVec 64) : BitVec 64 := do
  let mut m : DSL.Map (BitVec 32) (BitVec 64) := DSL.Map.empty
  m := m.insert 1 a
  m := m.insert 2 b
  m := m.insert 1 (a +% b)
  return m.get! k

/-- Maps as parameters and results; bool values. -/
flat def markSeen (m : DSL.Map (BitVec 16) Bool) (k : BitVec 16) : DSL.Map (BitVec 16) Bool × Bool := do
  let mut s := m
  let before := s.contains k
  s := s.insert k true
  return (s, before)

#guard histogram #v[1, 2, 1, 3, 1, 2, 9, 9] 1 = .ok 3
#guard histogram #v[1, 2, 1, 3, 1, 2, 9, 9] 9 = .ok 2
#guard histogram #v[1, 2, 1, 3, 1, 2, 9, 9] 4 = .error .notFound
#guard lookup 1 10 20 = .ok 30
#guard lookup 2 10 20 = .ok 20
#guard lookup 3 10 20 = .error .notFound
#guard (markSeen DSL.Map.empty 5).map (·.2) = .ok false
#guard (markSeen ⟨[(5, true)]⟩ 5).map (·.2) = .ok true
#guard (markSeen DSL.Map.empty 5).map (·.1.entries) = .ok [(5, true)]

def mapTests : List DSL.TestCase := [
  .mk' histogram.ast [((#v[1, 2, 1, 3, 1, 2, 9, 9], 1, ()), .ok 3),
    ((#v[1, 2, 1, 3, 1, 2, 9, 9], 9, ()), .ok 2),
    ((#v[1, 2, 1, 3, 1, 2, 9, 9], 4, ()), .error .notFound)],
  .mk' lookup.ast [((1, 10, 20, ()), .ok 30), ((2, 10, 20, ()), .ok 20), ((3, 10, 20, ()), .error .notFound)],
  .mk' markSeen.ast [((DSL.Map.empty, 5, ()), .ok (⟨[(5, true)]⟩, false)),
    ((⟨[(5, true)]⟩, 5, ()), .ok (⟨[(5, true)]⟩, true)),
    ((⟨[(1, false)]⟩, 5, ()), .ok (⟨[(1, false), (5, true)]⟩, false))]
]

#guard mapTests.all DSL.TestCase.passes

end Corpus
