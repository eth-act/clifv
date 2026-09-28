import FV.Opt.Basic

/-!
# DCE: delete removable statements whose results are never used

Liveness is a mark phase from the roots — the operands of every non-removable statement and
of every terminator — through the operands of the definitions of live values. A removable
statement (`Opt.removable`: pure nodes, non-trapping multi-result arithmetic, `nop`) with no
live result is deleted.

**Invariant (for the proof).** A deleted statement defines only values that no remaining
statement or terminator reads, and its evaluation cannot trap or touch memory; so running it
or not changes only the register-file entries of dead values. (Its evaluation could only get
`stuck` on an ill-typed function, and stuck source runs carry no obligation.)
-/

namespace Opt

open Clif

def dce (f : Function) : Function × Nat := Id.run do
  -- definitions of removable statements' results
  let mut defOps : Std.HashMap ValueId (List ValueId) := {}
  let mut work : Array ValueId := #[]
  for b in f.blocks do
    for st in b.body do
      if removable st.inst then
        for r in st.results do defOps := defOps.insert r (operands st.inst)
      else work := work ++ (operands st.inst).toArray
    work := work ++ (termOperands b.term).toArray
  let mut live : Std.HashSet ValueId := {}
  for _ in [0:defOps.size + work.size + 1] do
    if work.isEmpty then break
    let mut next : Array ValueId := #[]
    for v in work do
      if live.contains v then continue
      live := live.insert v
      next := next ++ ((defOps.get? v).getD []).toArray
    work := next
  let mut removed := 0
  let mut blocks : Array Block := #[]
  for b in f.blocks do
    let body := b.body.filter fun st =>
      !removable st.inst || st.results.any live.contains
    removed := removed + (b.body.length - body.length)
    blocks := blocks.push { b with body }
  return ({ f with blocks := blocks.toList }, removed)

end Opt
