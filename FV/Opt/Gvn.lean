import FV.Opt.Check

/-!
# GVN: dominator-scoped hash-consing of pure nodes

Walk the dominator tree in preorder with a scoped table `node ↦ value` (each block sees the
table of its immediate dominator plus its own earlier entries). A pure statement `v = n`
whose node `n` (operands already renamed) is in the table as `w` is deleted and `v ↦ w` is
added to the substitution; otherwise `n ↦ v` is recorded.

**Invariant (for the proof).** For every `v ↦ w` produced: `w`'s defining statement is the
same pure node over the same (renamed) operands, and it strictly dominates `v`'s. On a
well-formed function (`Opt.check`) the most recent value of `w` therefore equals what `v`
would have computed at every use of `v` (the dominance lemma in `docs/contracts/midend.md`),
and the deleted statement could not trap or get stuck.
-/

namespace Opt

open Clif

/-- One GVN pass. `local?` selects nodes numbered per block only (not across blocks), e.g.
constants when modelling Cranelift's rematerialisation. -/
def gvn (f : Function) (info : Info) (local? : Inst → Bool := fun _ => false) :
    Function × Nat := Id.run do
  let cfg := info.cfg
  let blocks := f.blocks.toArray
  let ch := cfg.domChildren
  let mut subst : Subst := {}
  let mut out := blocks
  let mut removed := 0
  -- stack of (block, table inherited from the immediate dominator)
  let mut stack : Array (Nat × Std.HashMap Inst ValueId) := #[(0, {})]
  for _ in [0:cfg.size + 1] do
    match stack.back? with
    | none => break
    | some (bi, tbl0) =>
      stack := stack.pop
      let b := blocks[bi]!
      let mut tbl := tbl0
      let mut blockTbl : Std.HashMap Inst ValueId := {}
      let mut body : Array Stmt := #[]
      for st in b.body do
        let inst := mapOperands subst.find st.inst
        match st.results, isPure inst with
        | [v], true =>
          let isLocal := local? inst
          match (if isLocal then blockTbl else tbl).get? inst with
          | some w =>
            subst := subst.insert v w
            removed := removed + 1
          | none =>
            if isLocal then blockTbl := blockTbl.insert inst v else tbl := tbl.insert inst v
            body := body.push { st with inst }
        | _, _ => body := body.push { st with inst }
      out := out.set! bi { b with body := body.toList }
      for c in (ch[bi]!).reverse do
        stack := stack.push (c, tbl)
  return (subst.apply { f with blocks := out.toList }, removed)

end Opt
