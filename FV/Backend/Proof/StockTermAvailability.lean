module

public import FV.Backend.Proof.StockDFG
public import FV.Backend.Proof.LowerFix

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false

private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers,usersN,args,view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0,view.valDef,bytes,args]
  simp only [availIn,inFix_eq,users,bytes,work,view.valDef]


/-- Original dominance supplies every terminator operand at the actual Stock
source point. Dense register allocation does not alter the must-availability
fixed point, and no source-availability certificate is added to the input. -/
theorem buildCtx_term_available {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (dominated : Dominated f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ∀ value ∈ Backend.Proof.Driver.termArgs (abiTerm f b.term),value ∈ availOf f (availIn f ctx) bi b.body.length := by
  obtain ⟨original,st0,oldBuild,ctxSpec,view⟩ := buildCtx_source build
  intro value member
  rw [view_avail view f]
  exact (dominated.uses original ranges st0 oldBuild bi b block).2 value member

end Backend.Stock.Proof
