import FV.Backend.Proof.StockAcquireActualBlockColors

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle
set_option autoImplicit false
set_option Elab.async false

/-- Terminator data never becomes an original source statement, including an absent placeholder. -/
theorem termCtx_source_none (ctx : Ctx) (terminal : Nat) (data : V) :
    (Driver.termCtx ctx terminal data).insts[terminal]!.clif = none := by
  simp only [Driver.termCtx,getElem!_def,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self]
  split <;> rfl

/-- The actual retained event's terminator has no original statement payload. -/
theorem stock_lower_event_term_source_none {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) : event.ctx.insts[event.termInst]!.clif = none := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initialState,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  have origin := stock_lowerBlockCore_scanOrigin coreRun
  rw [eventEq,origin.2.1,origin.2.2.2.1]
  exact termCtx_source_none _ _ _

end Backend.Stock.Proof.Acquire810
