import FV.Backend.Proof.StockAcquireActualScanSources

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual complete scan supplies one general source queue, its exact marks, and its assembled chunks. -/
theorem stock_lower_event_source_queue {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState), ∃ pending : List Nat,
      Backend.buildCtx f = .ok (original,ranges,initial) ∧ original.func = f ∧
      event.output.state.sunk = pending.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      (∀ target : Nat,event.input.sunk[target]! = true → event.output.state.sunk[target]! = true) ∧
      (∀ producer ∈ pending,some producer ∈ sourceColorEvents original ranges) ∧
      event.output.code.toList = event.output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,requests,oldBuild,allocation,finished⟩ := buildCtx_allocation build
  obtain ⟨pending,exactSunk,monotone,sources⟩ := stock_lower_event_source_sunk_updates run events
  refine ⟨original,ranges,st0,pending,oldBuild,(ctxSpec_of oldBuild).func,exactSunk,monotone,?_,?_⟩
  · intro producer member
    obtain ⟨other,otherRanges,otherInitial,otherBuild,source⟩ := sources producer member
    have equal := Except.ok.inj (otherBuild.symm.trans oldBuild)
    have fields := Prod.mk.inj equal
    rcases fields with ⟨rfl,tail⟩
    rcases Prod.mk.inj tail with ⟨rfl,rfl⟩
    exact source
  · exact scanBlock_forward_chunks (stock_lower_event_scan_run run events)

end Backend.Stock.Proof.Acquire810
