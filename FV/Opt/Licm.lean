import FV.Opt.Check

/-!
# LICM: hoist loop-invariant pure nodes to the loop's pre-header position

For each natural loop (`Cfg.loops`, innermost first) with header `h`, the hoist block is
`idom h` (outside the loop, dominating every loop block; Cranelift's elaborator hoists to the
same block, `LoopStackEntry::hoist_block`). A pure statement of a loop block is *invariant*
if every operand is defined outside the loop or by an invariant statement already hoisted;
invariant statements move, in their original relative order (loop blocks in RPO), to the end
of the hoist block's body (before its terminator). The pass iterates until nothing moves, so
code hoisted out of an inner loop can leave the outer one too.

Not hoisted: `symbol_value` (it is `stuck` on a missing symbol, so running it on a path that
did not before is not a refinement), and — with `hoistConst := false` — `iconst`
(rematerialised in place by Cranelift, whose isel folds constants into immediates).

**Invariant (for the proof).** A moved statement is pure and well-typed (cannot trap or get
stuck), its new position dominates its old one (so it dominates every use), and each operand's
definition dominates the new position; by the dominance lemma the most recent value of each
operand at the old and at the new position coincide on every execution that reaches a use,
so every use reads the same value. Executions that reach the new position but not the old one
only gain a dead register entry.
-/

namespace Opt

open Clif

def licmHoistable (hoistConst : Bool) : Inst → Bool
  | .symbolValue .. => false
  | .iconst .. => hoistConst
  | i => isPure i

/-- One round over all loops; returns the new function and the number of moved statements. -/
def licmRound (hoistConst : Bool) (f : Function) (cfg : Cfg) : Function × Nat := Id.run do
  let mut blocks := f.blocks.toArray
  let mut moved := 0
  -- innermost (smallest) loops first
  let loops := cfg.loops.qsort (fun a b => a.body.size < b.body.size)
  for lp in loops do
    let some hb := cfg.idom[lp.header]! | continue
    -- values defined inside the loop (current contents)
    let mut inside : Std.HashSet ValueId := {}
    for bi in lp.body.toList do
      let b := blocks[bi]!
      for (p, _) in b.params do inside := inside.insert p
      for s in b.body do for r in s.results do inside := inside.insert r
    let mut hoisted : Array Stmt := #[]
    for bi in cfg.rpo do
      if !lp.body.contains bi then continue
      let b := blocks[bi]!
      let mut keep : Array Stmt := #[]
      for s in b.body do
        if licmHoistable hoistConst s.inst && s.results.length == 1 &&
            (operands s.inst).all (!inside.contains ·) then
          hoisted := hoisted.push s
          inside := s.results.foldl (·.erase ·) inside
        else keep := keep.push s
      blocks := blocks.set! bi { b with body := keep.toList }
    if !hoisted.isEmpty then
      moved := moved + hoisted.size
      blocks := blocks.modify hb fun b => { b with body := b.body ++ hoisted.toList }
  return ({ f with blocks := blocks.toList }, moved)

/-- LICM to a fixpoint (at most one round per block). -/
def licm (hoistConst : Bool) (f : Function) (info : Info) : Function × Nat := Id.run do
  let mut g := f
  let mut total := 0
  for _ in [0:info.cfg.size + 1] do
    let (g', n) := licmRound hoistConst g info.cfg
    g := g'
    total := total + n
    if n == 0 then break
  return (g, total)

end Opt
